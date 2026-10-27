module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

private instance sylowMulAction_D11 {Γ : Subgroup (GL ι K)} (S : Sylow 2 ↥Γ) :
    MulAction ↥(S : Subgroup ↥Γ) (ι → K) where
  smul s v := (((s : ↥(S : Subgroup ↥Γ)) : ↥Γ) : GL ι K) *ᵥ v
  one_smul v := by
    show ((((1 : ↥(S : Subgroup ↥Γ)) : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v = v
    simp only [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  mul_smul s t v := by
    show ((((s * t : ↥(S : Subgroup ↥Γ)) : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v
      = ((((s : ↥(S : Subgroup ↥Γ)) : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ
          (((((t : ↥(S : Subgroup ↥Γ)) : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v)
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem sylowFixedLine_mulVec {Γ : Subgroup (GL ι K)} {e : ι → K}
    (h : KTabC.SylowFixedLine Γ e) (g : ↥Γ) :
    KTabC.SylowFixedLine Γ (((g : GL ι K) : Matrix ι ι K) *ᵥ e) := by
  intro S
  obtain ⟨x, hx⟩ := h S
  refine ⟨x * g⁻¹, fun v => ?_⟩
  have hGL : ((x * g⁻¹ : ↥Γ) : GL ι K) * ((g : ↥Γ) : GL ι K) = ((x : ↥Γ) : GL ι K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hmat : (((x * g⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) *
      (((g : ↥Γ) : GL ι K) : Matrix ι ι K) = ((x : ↥Γ) : GL ι K) := by
    rw [← Units.val_mul]
    exact congrArg (fun z : GL ι K => (z : Matrix ι ι K)) hGL
  have hkey : (((x * g⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ
      ((((g : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e)
      = (((x : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ e := by
    rw [Matrix.mulVec_mulVec, hmat]
  rw [hkey]
  exact hx v

private theorem two_dvd_card_D11 [Finite K] [CharP K 2] [Nonempty ι] :
    2 ∣ Nat.card (ι → K) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite ι := Finite.of_fintype ι
  rw [Nat.card_fun]
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  have h2K : 2 ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self 2 n.ne_zero
  exact dvd_pow h2K (Nat.card_pos (α := ι)).ne'

theorem ne_zero_of_sylowFixedLine [Finite K] [CharP K 2] [Nonempty ι] {Γ : Subgroup (GL ι K)}
    {e : ι → K} (h : KTabC.SylowFixedLine Γ e) : e ≠ 0 := by
  intro he
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nonempty (Sylow 2 ↥Γ) := Sylow.nonempty
  obtain ⟨S⟩ := hS
  obtain ⟨x, hx⟩ := h S
  have h0 : (0 : ι → K) ∈ MulAction.fixedPoints ↥(S : Subgroup ↥Γ) (ι → K) := by
    rw [MulAction.mem_fixedPoints]
    intro s
    exact Matrix.mulVec_zero _
  obtain ⟨b, hb, hbne⟩ := IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    S.isPGroup' (α := ι → K) (two_dvd_card_D11 (ι := ι) (K := K)) h0
  have hbfix : ∀ s ∈ (S : Subgroup ↥Γ),
      (((s : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ b = b := by
    intro s hs
    exact (MulAction.mem_fixedPoints.mp hb) ⟨s, hs⟩
  obtain ⟨c, hc⟩ := (hx b).mp hbfix
  have hxe : ((x : GL ι K) : Matrix ι ι K) *ᵥ e = 0 := by
    rw [he, Matrix.mulVec_zero]
  have hb0 : b = 0 := by
    rw [hc, hxe, smul_zero]
  exact hbne hb0.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

end
