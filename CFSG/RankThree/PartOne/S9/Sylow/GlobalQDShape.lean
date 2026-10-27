module

public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne.Sec9B

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_self_le (Y : Subgroup G) : ⁅Y, Y⁆ ≤ Y :=
  (Subgroup.commutator_le_sup Y Y).trans (by simp)

theorem commutator_map_mul_of_central {Y : Subgroup G} {x₁ x₂ y : G} (hx₁ : x₁ ∈ Y)
    (hx₂ : x₂ ∈ Y) (hy : y ∈ Y) (hZ : ∀ z ∈ ⁅Y, Y⁆, ∀ w ∈ Y, w * z = z * w) :
    ⁅x₁ * x₂, y⁆ = ⁅x₁, y⁆ * ⁅x₂, y⁆ := by
  have hz₁ : ⁅x₁, y⁆ ∈ ⁅Y, Y⁆ := Subgroup.commutator_mem_commutator hx₁ hy
  have hz₂ : ⁅x₂, y⁆ ∈ ⁅Y, Y⁆ := Subgroup.commutator_mem_commutator hx₂ hy
  have h1 : x₁ * ⁅x₂, y⁆ = ⁅x₂, y⁆ * x₁ := hZ _ hz₂ x₁ hx₁
  have h2 : ⁅x₁, y⁆ * ⁅x₂, y⁆ = ⁅x₂, y⁆ * ⁅x₁, y⁆ := hZ _ hz₂ _ (commutator_self_le Y hz₁)
  simp only [commutatorElement_def] at h1 h2 ⊢
  calc x₁ * x₂ * y * (x₁ * x₂)⁻¹ * y⁻¹
      = (x₁ * (x₂ * y * x₂⁻¹ * y⁻¹)) * (y * x₁⁻¹ * y⁻¹) := by group
    _ = ((x₂ * y * x₂⁻¹ * y⁻¹) * x₁) * (y * x₁⁻¹ * y⁻¹) := by rw [h1]
    _ = (x₂ * y * x₂⁻¹ * y⁻¹) * (x₁ * y * x₁⁻¹ * y⁻¹) := by group
    _ = _ := h2.symm

theorem false_of_isElementaryAbelian_le_special {q : ℕ} (hq : q.Prime) [Finite G]
    {X Y : Subgroup G} (hXY : X ≤ Y) (hX : IsElementaryAbelian q ↥X) (hXc : Nat.card ↥X = q ^ 4)
    (hYc : Nat.card ↥Y = q ^ 5) (hY' : Nat.card ↥⁅Y, Y⁆ = q)
    (hYZ : Y ⊓ Subgroup.centralizer (Y : Set G) = ⁅Y, Y⁆) : False := by
  have hZ : ∀ z ∈ ⁅Y, Y⁆, ∀ w ∈ Y, w * z = z * w := fun z hz w hw => by
    have hz' : z ∈ Y ⊓ Subgroup.centralizer (Y : Set G) := hYZ ▸ hz
    exact Subgroup.mem_centralizer_iff.mp hz'.2 w hw
  obtain ⟨y, hyY, hyX⟩ : ∃ y ∈ Y, y ∉ X := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hle : Y ≤ X := h
    have := Subgroup.card_le_of_le hle
    rw [hXc, hYc] at this
    have h2 : 1 < q := hq.one_lt
    have : q ^ 4 < q ^ 5 := Nat.pow_lt_pow_right h2 (by norm_num)
    omega
  have hM : X ⊔ Subgroup.zpowers y = Y := by
    have hle : X ⊔ Subgroup.zpowers y ≤ Y := sup_le hXY ((Subgroup.zpowers_le).mpr hyY)
    have h1 : Nat.card ↥X ∣ Nat.card ↥(X ⊔ Subgroup.zpowers y) :=
      Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card ↥(X ⊔ Subgroup.zpowers y) ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hle
    rw [hXc] at h1
    rw [hYc] at h2
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hq).mp h2
    rw [hk'] at h1
    have h4 : 4 ≤ k := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp h1
    have hk5 : k = 4 ∨ k = 5 := by omega
    rcases hk5 with rfl | rfl
    · exfalso
      have hXM : X = X ⊔ Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk', hXc])
      exact hyX (hXM ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hk', hYc])
  let ψ : X →* ↥⁅Y, Y⁆ :=
    { toFun := fun x => ⟨⁅(x : G), y⁆, Subgroup.commutator_mem_commutator (hXY x.2) hyY⟩
      map_one' := by ext; simp
      map_mul' := fun x₁ x₂ => by
        ext
        exact commutator_map_mul_of_central (hXY x₁.2) (hXY x₂.2) hyY hZ }
  have hψker : ∀ x : X, x ∈ ψ.ker → (x : G) * y = y * (x : G) := by
    intro x hx
    have h1 : ⁅(x : G), y⁆ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have hkerZ : ψ.ker.map X.subtype ≤ Y ⊓ Subgroup.centralizer (Y : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hXY x.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    rw [← hM] at hw
    have : X ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
      refine sup_le (fun a ha => ?_) ?_
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        simpa using congrArg Subtype.val ((IsMulCommutative.is_comm (M := X)).comm ⟨a, ha⟩ x)
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hψker x hx).symm
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (this hw)
    exact h2
  have hkerle : Nat.card ψ.ker ≤ q := by
    have := Subgroup.card_le_of_le (hkerZ.trans hYZ.le)
    rwa [Subgroup.card_map_of_injective X.subtype_injective, hY'] at this
  have hrange : Nat.card ψ.range ≤ q := by
    have := Nat.card_le_card_of_injective (fun z : ψ.range => (z : ↥⁅Y, Y⁆))
      Subtype.val_injective
    rw [hY'] at this
    exact this
  have hmul : Nat.card ψ.ker * Nat.card ψ.range = Nat.card X := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hXc] at hmul
  have h2 : 1 < q := hq.one_lt
  have : Nat.card ψ.ker * Nat.card ψ.range ≤ q * q := Nat.mul_le_mul hkerle hrange
  have : q ^ 4 ≤ q * q := hmul ▸ this
  have : q * q < q ^ 4 := by
    calc q * q = q ^ 2 := by ring
      _ < q ^ 4 := Nat.pow_lt_pow_right h2 (by norm_num)
  omega

theorem eq_of_le_of_isQDShape {q : ℕ} (hq : q.Prime) [Finite G] {X D : Subgroup G}
    (hXD : X ≤ D) (hX : IsQDShape q X) (hD : IsQDShape q D) : X = D := by
  have h2 : 1 < q := hq.one_lt
  rcases hX with ⟨hXe, hXc⟩ | ⟨-, hXc, -⟩
  · rcases hD with ⟨-, hDc⟩ | ⟨-, hDc, hD', hDZ, -⟩
    · exact Subgroup.eq_of_le_of_card_ge hXD (by rw [hXc, hDc])
    · exact (false_of_isElementaryAbelian_le_special hq hXD hXe hXc hDc hD' hDZ).elim
  · rcases hD with ⟨-, hDc⟩ | ⟨-, hDc, -⟩
    · exfalso
      have := Subgroup.card_le_of_le hXD
      rw [hXc, hDc] at this
      have := Nat.pow_lt_pow_right h2 (show 4 < 5 by norm_num)
      omega
    · exact Subgroup.eq_of_le_of_card_ge hXD (by rw [hXc, hDc])

end CFSG.RankThree.PartOne.Sec9B
