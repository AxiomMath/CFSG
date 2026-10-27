module

public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

theorem exists_finset_card_four_of_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) : ∃ s : Finset K, s.card = 4 := by
  have := Fintype.ofFinite K
  have hle : 4 ≤ (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
  exact ⟨s, hs⟩

section Inner

variable {Γ : Type} [Group Γ] [Finite Γ] {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite Γ] in
theorem inner_of_blockHom {P : Subgroup Γ} (ρ : ↥P →* Matrix (Fin 2) (Fin 2) K)
    (β : ↥(perfectCore P) →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hβ : ∀ x : ↥(perfectCore P), (β x : Matrix (Fin 2) (Fin 2) K) =
      ρ (Subgroup.inclusion (perfectCore_le P) x))
    (hsurj : Function.Surjective β) (hker : IsPGroup 2 β.ker) :
    ∀ g ∈ P, ∃ y ∈ perfectCore P, ∀ x ∈ perfectCore P,
      ⁅g * y⁻¹, x⁆ ∈ pCoreOf 2 (perfectCore P) := by
  intro g hg
  set gP : ↥P := ⟨g, hg⟩ with hgP
  have hunit : IsUnit (ρ gP).det := by
    refine Matrix.isUnit_det_of_right_inverse (B := ρ gP⁻¹) ?_
    rw [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (ρ gP).det
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hunit.ne_zero (by rw [hc, mul_zero])
  have hdet : (c⁻¹ • ρ gP).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hc]
    field_simp
  obtain ⟨y₀, hy₀⟩ := hsurj ⟨c⁻¹ • ρ gP, hdet⟩
  set yP : ↥P := Subgroup.inclusion (perfectCore_le P) y₀ with hyP
  have hy : ρ yP = c⁻¹ • ρ gP := by
    have := hβ y₀
    rw [hy₀] at this
    exact this.symm
  have hgy : ρ gP = c • ρ yP := by rw [hy, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  refine ⟨(y₀ : Γ), y₀.2, fun x hx => ?_⟩
  set xP : ↥P := ⟨x, perfectCore_le P hx⟩ with hxP
  set hP : ↥P := gP * yP⁻¹ with hhP
  have hρh : ρ hP = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h1 : ρ yP * ρ yP⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [hhP, map_mul, hgy, Matrix.smul_mul, h1]
  have hρh' : ρ hP⁻¹ = c⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have h1 : ρ hP * ρ hP⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [hρh, Matrix.smul_mul, one_mul] at h1
    calc ρ hP⁻¹ = c⁻¹ • (c • ρ hP⁻¹) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • 1 := by rw [h1]
  have hρx : ρ xP * ρ xP⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hρz : ρ ⁅hP, xP⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, hρh, hρh']
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hc0, one_smul]
    exact hρx
  have hxmem : xP ∈ (perfectCore P).subgroupOf P := Subgroup.mem_subgroupOf.2 hx
  have hzcore : (⁅hP, xP⁆ : ↥P) ∈ (perfectCore P).subgroupOf P := by
    rw [commutatorElement_def]
    exact mul_mem ((perfectCore_normal P).conj_mem xP hxmem hP) (inv_mem hxmem)
  set z' : ↥(perfectCore P) := ⟨(⁅hP, xP⁆ : ↥P).1, hzcore⟩ with hz'
  have hβz : β z' = 1 := by
    refine Subtype.ext ?_
    rw [hβ z', Matrix.SpecialLinearGroup.coe_one]
    exact hρz
  have hz'core := le_pCore 2 β.normal_ker hker (MonoidHom.mem_ker.2 hβz)
  refine Subgroup.mem_map.2 ⟨z', hz'core, ?_⟩
  simp [hz', hhP, commutatorElement_def, hgP, hxP, hyP]

end Inner

section Transfer

variable {Γ Y : Type} [Group Γ] [Group Y] [Finite Γ] [Finite Y]

theorem inner_map (π : Γ →* Y) {P : Subgroup Γ}
    (h : ∀ g ∈ P, ∃ y ∈ perfectCore P, ∀ x ∈ perfectCore P,
      ⁅g * y⁻¹, x⁆ ∈ pCoreOf 2 (perfectCore P)) :
    ∀ g ∈ P.map π, ∃ y ∈ perfectCore (P.map π), ∀ x ∈ perfectCore (P.map π),
      ⁅g * y⁻¹, x⁆ ∈ pCoreOf 2 (perfectCore (P.map π)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro _ ⟨g₀, hg₀, rfl⟩
  obtain ⟨y₀, hy₀, hy⟩ := h g₀ hg₀
  refine ⟨π y₀, ?_, fun x hx => ?_⟩
  · rw [← map_perfectCore π P]
    exact ⟨y₀, hy₀, rfl⟩
  · rw [← map_perfectCore π P] at hx ⊢
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    have h1 := map_pCoreOf_le (r := 2) π (perfectCore P) (Subgroup.mem_map_of_mem π (hy x₀ hx₀))
    convert h1 using 1
    simp [commutatorElement_def]

omit [Finite Γ] [Finite Y] in
theorem isSolvable_comap_of_ker (π : Γ →* Y) (hk : Group.IsSolvable ↥π.ker) {X : Subgroup Y}
    (hX : Group.IsSolvable ↥X) : Group.IsSolvable ↥(X.comap π) := by
  have hle : π.ker ≤ X.comap π := Subgroup.ker_le_comap π X
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) (π.subgroupComap X) ?_
  intro z hz
  have hz' : π z.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hz)
  exact ⟨⟨z.1, MonoidHom.mem_ker.2 hz'⟩, Subtype.ext rfl⟩

end Transfer

end CFSG.Quasithin.Rk2
