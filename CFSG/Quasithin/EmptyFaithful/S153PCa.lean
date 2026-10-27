module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin

open scoped MatrixGroups

namespace S153P

namespace PC

theorem card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem words_of_closure {Q : Type*} [Group Q] {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hc : (b * a) * b * (b * a)⁻¹ * a⁻¹ = 1) {q : Q} (hq : q ∈ Subgroup.closure ({a, b} : Set Q)) :
    q = 1 ∨ q = a ∨ q = b ∨ q = a * b ∨ q = b * a ∨ q = a * b * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hba : b * a * b = a * b * a := by
    have h1 : b * a * b * (a * b * a) = 1 := by
      simpa [mul_inv_rev, ha', hb', mul_assoc] using hc
    have h2 : a * b * a = (b * a * b)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    simp [mul_inv_rev, ha', hb', mul_assoc]
  have e3 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e4 : a * (b * a) = a * b * a := (mul_assoc a b a).symm
  have e5 : a * (a * b * a) = b * a := by rw [← mul_assoc, e3]
  have e6 : b * (a * b) = a * b * a := by rw [← mul_assoc, hba]
  have e7 : b * (b * a) = a := by rw [← mul_assoc, hb, one_mul]
  have e8 : b * (a * b * a) = a * b := by rw [← mul_assoc, e6, mul_assoc, ha, mul_one]
  induction hq using Subgroup.closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left x hx y hy ih =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> rcases ih with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [mul_one, ha, hb, e3, e4, e5, e6, e7, e8]
  | inv_mul_cancel x hx y hy ih =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> rcases ih with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [mul_one, ha', hb', ha, hb, e3, e4, e5, e6, e7, e8]

theorem injective_of_dihedral {Q : Type*} [Group Q] {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hc : (b * a) * b * (b * a)⁻¹ * a⁻¹ = 1) (hgen : ∀ q : Q, q ∈ Subgroup.closure ({a, b} : Set Q))
    (φ : Q →* Equiv.Perm (Fin 3)) (hφ : Function.Surjective φ) : Function.Injective φ := by
  let w : Fin 6 → Q := ![1, a, b, a * b, b * a, a * b * a]
  have hw : Function.Surjective w := by
    intro q
    rcases words_of_closure ha hb hc (hgen q) with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]
  have : Finite Q := Finite.of_surjective w hw
  have hcard : Nat.card Q ≤ Nat.card (Equiv.Perm (Fin 3)) := by
    rw [card_perm_three]
    simpa using Nat.card_le_card_of_surjective w hw
  exact (hφ.bijective_of_nat_card_le hcard).1

theorem sl2_pow_six : ∀ c : SL(2, ZMod 2), c ^ 6 = 1 := by decide

theorem sl2_exists_conj :
    ∀ b : SL(2, ZMod 2), b ≠ 1 → ∃ g : SL(2, ZMod 2), (b * (g * b * g⁻¹)) ^ 2 ≠ 1 := by
  decide

theorem sl2_sq_eq_one {c : SL(2, ZMod 2)} {k : ℕ} (h : c ^ 2 ^ k = 1) : c ^ 2 = 1 := by
  have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf c ∣ 6 := orderOf_dvd_of_pow_eq_one (sl2_pow_six c)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hi1 : i ≤ 1 := by
    by_contra hlt
    have h4 : 2 ^ 2 ∣ 2 ^ i := pow_dvd_pow 2 (by omega)
    rw [← hi] at h4
    have := h4.trans h2
    omega
  exact orderOf_dvd_iff_pow_eq_one.1 (hi ▸ pow_dvd_pow 2 hi1)

end PC

section Interface

variable {G : Type} [Group G]

theorem ker_le_of_dihedral {J N : Subgroup G} (hNJ : N ≤ J) (hN : ∀ j ∈ J, ∀ n ∈ N, j * n * j⁻¹ ∈ N)
    (u v : G) (hu : u ∈ J) (hv : v ∈ J)
    (hgen : ∀ x ∈ J, x ∈ N ⊔ Subgroup.closure ({u, v} : Set G))
    (hu2 : u * u ∈ N) (hv2 : v * v ∈ N)
    (hconj : (v * u) * v * (v * u)⁻¹ * u⁻¹ ∈ N)
    (β : ↥J →* Equiv.Perm (Fin 3)) (hβs : Function.Surjective β)
    (hNβ : ∀ x : ↥J, (x : G) ∈ N → β x = 1) :
    ∀ x : ↥J, β x = 1 → (x : G) ∈ N := by
  have hH : (N.subgroupOf J).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hN g g.2 n hn⟩
  let π : ↥J →* ↥J ⧸ N.subgroupOf J := QuotientGroup.mk' (N.subgroupOf J)
  have hπ : ∀ x : ↥J, π x = 1 ↔ (x : G) ∈ N := fun x => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
  let u' : ↥J := ⟨u, hu⟩
  let v' : ↥J := ⟨v, hv⟩
  have ha : π u' * π u' = 1 := by rw [← map_mul, hπ]; exact hu2
  have hb : π v' * π v' = 1 := by rw [← map_mul, hπ]; exact hv2
  have hc : (π v' * π u') * π v' * (π v' * π u')⁻¹ * (π u')⁻¹ = 1 := by
    rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul, hπ]
    exact hconj
  have hQ : ∀ q : ↥J ⧸ N.subgroupOf J,
      q ∈ Subgroup.closure ({π u', π v'} : Set (↥J ⧸ N.subgroupOf J)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    let T : Subgroup G :=
      ((Subgroup.closure ({π u', π v'} : Set (↥J ⧸ N.subgroupOf J))).comap π).map J.subtype
    have hNT : N ≤ T := by
      intro n hn
      refine ⟨⟨n, hNJ hn⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, (hπ ⟨n, hNJ hn⟩).2 hn]
      exact one_mem _
    have hCT : Subgroup.closure ({u, v} : Set G) ≤ T := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨u', Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
      · exact ⟨v', Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
    obtain ⟨t, ht, htx⟩ := sup_le hNT hCT (hgen x x.2)
    have : t = x := Subtype.ext htx
    rw [this] at ht
    exact ht
  have hker : N.subgroupOf J ≤ β.ker := fun x hx => hNβ x (Subgroup.mem_subgroupOf.1 hx)
  let φ : ↥J ⧸ N.subgroupOf J →* Equiv.Perm (Fin 3) := QuotientGroup.lift (N.subgroupOf J) β hker
  have hφ : Function.Surjective φ := by
    intro σ
    obtain ⟨x, rfl⟩ := hβs σ
    exact ⟨x, rfl⟩
  have hinj := PC.injective_of_dihedral ha hb hc hQ φ hφ
  intro x hx
  have h1 : φ (π x) = φ 1 := by
    rw [map_one]; exact hx
  exact (hπ x).1 (hinj h1)

set_option linter.unusedVariables false in
theorem normal_two_sub_trivial {J P : Subgroup G} (β : ↥J →* SL(2, ZMod 2)) (hβs : Function.Surjective β)
    (hPJ : P ≤ J) (hn : ∀ a ∈ J, ∀ b ∈ P, a * b * a⁻¹ ∈ P) (hP2 : IsPGroup 2 P) :
    ∀ x : ↥J, (x : G) ∈ P → β x = 1 := by
  intro x hx
  by_contra hne
  obtain ⟨g, hg⟩ := PC.sl2_exists_conj _ hne
  obtain ⟨y, rfl⟩ := hβs g
  have hy : (y * x * y⁻¹ : ↥J).1 ∈ P := hn y y.2 x hx
  have hz : (x * (y * x * y⁻¹) : ↥J).1 ∈ P := P.mul_mem hx hy
  obtain ⟨k, hk⟩ := hP2 ⟨_, hz⟩
  have hk' : (x * (y * x * y⁻¹) : ↥J) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  apply hg
  apply PC.sl2_sq_eq_one (k := k)
  have hβk : β ((x * (y * x * y⁻¹)) ^ 2 ^ k) = 1 := by rw [hk', map_one]
  simpa only [map_pow, map_mul, map_inv] using hβk

end Interface

end S153P

end CFSG.Quasithin
