module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {G : Type} [Group G]

theorem exists_mul_trivial_on_section_of_card_mulAut {K N Y X : Subgroup G} {Q : Type} [Group Q]
    (φ : ↥K →* Q) (hφ : Function.Surjective φ) (hker : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ N)
    (hQ : Nat.card (MulAut Q) = 120)
    (hKz : ∀ k ∈ K, (∀ x ∈ K, k * x * k⁻¹ * x⁻¹ ∈ N) → k ∈ N)
    (hYK : Y ≤ normalizer (K : Set G)) (hYN : Y ≤ normalizer (N : Set G))
    (hY : IsPGroup 3 ↥Y) (hXY : X ≤ Y) (hXK : X ≤ K) (hXN : ¬ X ≤ N) :
    ∀ y ∈ Y, ∃ x ∈ X, ∀ k ∈ K, (x⁻¹ * y) * k * (x⁻¹ * y)⁻¹ * k⁻¹ ∈ N := by
  let cK : ↥Y → ↥K → ↥K := fun y k =>
    ⟨(y : G) * k * (y : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hYK y.2) k).mp k.2⟩
  have cK_coe : ∀ y k, ((cK y k : ↥K) : G) = (y : G) * k * (y : G)⁻¹ := fun _ _ => rfl
  have cK_mul : ∀ y (k k' : ↥K), cK y (k * k') = cK y k * cK y k' := fun y k k' =>
    Subtype.ext (by simp only [cK_coe, Subgroup.coe_mul]; group)
  have cK_one : ∀ y, cK y 1 = 1 := fun y => Subtype.ext (by simp [cK_coe])
  have cK_mul_left : ∀ (y y' : ↥Y) k, cK (y * y') k = cK y (cK y' k) := fun y y' k =>
    Subtype.ext (by simp only [cK_coe, Subgroup.coe_mul]; group)
  have cK_one_left : ∀ k, cK 1 k = k := fun k => Subtype.ext (by simp [cK_coe])
  have cK_inv : ∀ y k, cK y⁻¹ (cK y k) = k := fun y k => by
    rw [← cK_mul_left, inv_mul_cancel, cK_one_left]
  let cH : ↥Y → (↥K →* ↥K) := fun y => { toFun := cK y, map_one' := cK_one y, map_mul' := cK_mul y }
  have hkerle : ∀ y : ↥Y, φ.ker ≤ (φ.comp (cH y)).ker := by
    intro y k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    have hkN : (k : G) ∈ N := (hker k).mp hk
    have : ((cH y k : ↥K) : G) ∈ N := by
      show (y : G) * k * (y : G)⁻¹ ∈ N
      exact (Subgroup.mem_normalizer_iff.mp (hYN y.2) k).mp hkN
    exact (hker (cH y k)).mpr this
  let α₀ : ↥Y → (Q →* Q) := fun y =>
    MonoidHom.liftOfSurjective φ hφ ⟨φ.comp (cH y), hkerle y⟩
  have α₀_apply : ∀ y k, α₀ y (φ k) = φ (cK y k) := fun y k =>
    MonoidHom.liftOfRightInverse_comp_apply φ (Function.surjInv hφ)
      (Function.rightInverse_surjInv hφ) ⟨φ.comp (cH y), hkerle y⟩ k
  have α₀_one : ∀ q, α₀ 1 q = q := by
    intro q
    obtain ⟨k, rfl⟩ := hφ q
    rw [α₀_apply, cK_one_left]
  have α₀_mul : ∀ (y y' : ↥Y) q, α₀ (y * y') q = α₀ y (α₀ y' q) := by
    intro y y' q
    obtain ⟨k, rfl⟩ := hφ q
    rw [α₀_apply, cK_mul_left, α₀_apply, α₀_apply]
  have α₀_inv : ∀ (y : ↥Y) q, α₀ y⁻¹ (α₀ y q) = q := by
    intro y q
    obtain ⟨k, rfl⟩ := hφ q
    rw [α₀_apply, α₀_apply, cK_inv]
  let αe : ↥Y → MulAut Q := fun y =>
    { toFun := α₀ y
      invFun := α₀ y⁻¹
      left_inv := fun q => α₀_inv y q
      right_inv := fun q => by simpa using α₀_inv y⁻¹ q
      map_mul' := (α₀ y).map_mul }
  let α : ↥Y →* MulAut Q :=
    { toFun := αe
      map_one' := MulEquiv.ext fun q => α₀_one q
      map_mul' := fun y y' => MulEquiv.ext fun q => α₀_mul y y' q }
  have α_apply : ∀ y k, α y (φ k) = φ (cK y k) := fun y k => α₀_apply y k
  haveI : Finite (MulAut Q) := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrange3 : IsPGroup 3 ↥α.range :=
    hY.of_surjective α.rangeRestrict (MonoidHom.rangeRestrict_surjective α)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hrange3
  have hdvd : Nat.card ↥α.range ∣ 120 := hQ ▸ Subgroup.card_subgroup_dvd_card _
  have hn1 : n ≤ 1 := by
    by_contra hn2
    have h9 : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    rw [← hn] at h9
    have := h9.trans hdvd
    norm_num at this
  obtain ⟨x₀, hx₀X, hx₀N⟩ : ∃ x ∈ X, x ∉ N := by
    by_contra hall
    apply hXN
    intro x hx
    by_contra hxN
    exact hall ⟨x, hx, hxN⟩
  have hx₀Y : x₀ ∈ Y := hXY hx₀X
  have hα₁ : α ⟨x₀, hx₀Y⟩ ≠ 1 := by
    intro h1
    apply hx₀N
    refine hKz x₀ (hXK hx₀X) fun k hk => ?_
    have h2 : φ (cK ⟨x₀, hx₀Y⟩ ⟨k, hk⟩) = φ ⟨k, hk⟩ := by
      rw [← α_apply, h1]
      rfl
    have h3 : φ (cK ⟨x₀, hx₀Y⟩ ⟨k, hk⟩ * ⟨k, hk⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    exact (hker _).mp h3
  let Xbar : Subgroup (MulAut Q) := (X.subgroupOf Y).map α
  have hXbar_le : Xbar ≤ α.range := Subgroup.map_le_range α _
  have hmem : α ⟨x₀, hx₀Y⟩ ∈ Xbar :=
    Subgroup.mem_map.mpr ⟨⟨x₀, hx₀Y⟩, Subgroup.mem_subgroupOf.mpr hx₀X, rfl⟩
  have hbotne : Xbar ≠ ⊥ := fun hb => hα₁ (Subgroup.mem_bot.mp (hb ▸ hmem))
  have hn1' : n = 1 := by
    by_contra hn0
    have hn0' : n = 0 := by omega
    rw [hn0', pow_zero] at hn
    have hbot : α.range = ⊥ := Subgroup.card_eq_one.mp hn
    rw [hbot] at hXbar_le
    exact hbotne (le_bot_iff.mp hXbar_le)
  rw [hn1', pow_one] at hn
  have hXbar_card : Nat.card ↥Xbar = 3 := by
    have hd : Nat.card ↥Xbar ∣ 3 := hn ▸ Subgroup.card_dvd_of_le hXbar_le
    have h1 : Nat.card ↥Xbar ≠ 1 := fun h1 => hbotne (Subgroup.card_eq_one.mp h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd h h1
    · exact h
  have hXbar_eq : Xbar = α.range :=
    Subgroup.eq_of_le_of_card_ge hXbar_le (by rw [hn, hXbar_card])
  intro y hy
  have hyr : α ⟨y, hy⟩ ∈ α.range := ⟨⟨y, hy⟩, rfl⟩
  rw [← hXbar_eq] at hyr
  obtain ⟨x', hx'X, hx'⟩ := Subgroup.mem_map.mp hyr
  refine ⟨(x' : G), Subgroup.mem_subgroupOf.mp hx'X, fun k hk => ?_⟩
  have h1 : α (x'⁻¹ * ⟨y, hy⟩) = 1 := by rw [map_mul, map_inv, hx', inv_mul_cancel]
  have h2 : φ (cK (x'⁻¹ * ⟨y, hy⟩) ⟨k, hk⟩) = φ ⟨k, hk⟩ := by
    rw [← α_apply, h1]
    rfl
  have h3 : φ (cK (x'⁻¹ * ⟨y, hy⟩) ⟨k, hk⟩ * ⟨k, hk⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h2, mul_inv_cancel]
  exact (hker _).mp h3

end CFSG.LocalAnalysis.WeakClosure81

end
