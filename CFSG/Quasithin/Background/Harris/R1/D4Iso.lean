module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.Background.Harris.R1

variable {K Y : Type*} [Group K] [Group Y]

theorem injective_of_ker_inf_eq_bot {P : Subgroup K} [P.Normal]
    (hC : Subgroup.centralizer (P : Set K) ≤ P) (ψ : K →* Y) (hP : ψ.ker ⊓ P = ⊥) :
    Function.Injective ψ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro n hn
  have hcomm : ∀ p ∈ P, n * p * n⁻¹ * p⁻¹ = 1 := by
    intro p hp
    have h1 : n * p * n⁻¹ * p⁻¹ ∈ ψ.ker := by
      have : n * (p * n⁻¹ * p⁻¹) ∈ ψ.ker :=
        ψ.ker.mul_mem hn (ψ.normal_ker.conj_mem _ (ψ.ker.inv_mem hn) p)
      simpa [mul_assoc] using this
    have h2 : n * p * n⁻¹ * p⁻¹ ∈ P :=
      P.mul_mem (‹P.Normal›.conj_mem p hp n) (P.inv_mem hp)
    have h3 : n * p * n⁻¹ * p⁻¹ ∈ ψ.ker ⊓ P := ⟨h1, h2⟩
    rw [hP] at h3
    exact h3
  have hnC : n ∈ Subgroup.centralizer (P : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h := hcomm p hp
    calc p * n = (n * p * n⁻¹ * p⁻¹)⁻¹ * (n * p) := by group
      _ = n * p := by rw [h, inv_one, one_mul]
  have h3 : n ∈ ψ.ker ⊓ P := ⟨hn, hC hnC⟩
  rw [hP] at h3
  exact h3

theorem injective_of_center_le [Finite K] {P : Subgroup K} [P.Normal] (hP2 : IsPGroup 2 P)
    (hC : Subgroup.centralizer (P : Set K) ≤ P) {z : K}
    (hZ : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x = 1 ∨ x = z) (ψ : K →* Y) (hψz : ψ z ≠ 1) :
    Function.Injective ψ := by
  refine injective_of_ker_inf_eq_bot hC ψ ?_
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥P := hP2.isNilpotent
  set H : Subgroup ↥P := (ψ.ker ⊓ P).subgroupOf P with hH
  have hHn : H.Normal := by
    rw [hH]
    exact Subgroup.normal_subgroupOf
  have hHne : H ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥P) ∈ H := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  obtain ⟨⟨y, hy⟩, hy1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hHne)
  obtain ⟨hyH, hyc⟩ := Subgroup.mem_inf.mp hy
  have hyH' : (y : K) ∈ ψ.ker ⊓ P := Subgroup.mem_subgroupOf.mp hyH
  have hcomm : ∀ w ∈ P, (y : K) * w = w * y := by
    intro w hw
    have := Subgroup.mem_center_iff.mp hyc ⟨w, hw⟩
    exact (congrArg Subtype.val this).symm
  have hy1' : (y : K) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  rcases hZ y y.2 hcomm with h1 | h1
  · exact hy1' h1
  · apply hψz
    rw [← h1]
    exact hyH'.1

end CFSG.Quasithin.Background.Harris.R1
