module

public import CFSG.GH74.Generic.S3.LyVertSL2
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcInner

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix CFSG.ABGLocalTools CFSG.GorensteinWalter CFSG.GH74.Generic.S3
open scoped MatrixGroups

namespace Item211Res4Proof

variable {F : Type} [Field F] [Finite F]

theorem exists_glConj_eq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p)
    (α : MulAut SL(2, F)) : ∃ G : GL (Fin 2) F, ∀ b : SL(2, F), α b = glConj G b := by
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact hp.odd_of_ne_two (by omega)
  have h3 : 3 < Nat.card F := by omega
  have hK : IsOddPrimePower (Nat.card F) := isOddPrimePower_card_of_odd hodd
  obtain ⟨f, -, hKcard⟩ := card_eq_ringChar_pow (F := F)
  have : Fact (ringChar F).Prime := ⟨ringChar_prime⟩
  obtain ⟨γ, hγ⟩ := pGammaL2ToMulAutPSL2_surjective F hKcard hK h3 (psl2MulAutOf α)
  obtain ⟨G, hG⟩ := ProjGenLinGroup.mk_surjective γ.left
  have hσ : γ.right = 1 := Item211Lie2Proof.ringEquiv_eq_one_of_card_prime hp hF _
  have hu := coe_mulAut_eq_smul_conj hK h3 α γ hγ G hG
  have h4 : 4 ≤ Nat.card F := by omega
  have hcen : ∀ b, (α.toMonoidHom b)⁻¹ * ((glConj G).toMonoidHom b) ∈
      Subgroup.center SL(2, F) := by
    intro b
    obtain ⟨u, hu0, hub⟩ := hu b
    change (α b)⁻¹ * glConj G b ∈ Subgroup.center SL(2, F)
    set X : SL(2, F) := α b with hX
    set Y : SL(2, F) := glConj G b with hY
    have hmap : (b : Matrix (Fin 2) (Fin 2) F).map γ.right = (b : Matrix (Fin 2) (Fin 2) F) := by
      rw [hσ]
      ext i j
      rfl
    have hXY : (X : Matrix (Fin 2) (Fin 2) F) = u • (Y : Matrix (Fin 2) (Fin 2) F) := by
      rw [hY, coe_glConj, ← hmap]
      exact hub
    have hu2 : u ^ 2 = 1 := by
      have h1 := congrArg Matrix.det hXY
      rw [Matrix.SpecialLinearGroup.det_coe, Matrix.det_smul, Matrix.SpecialLinearGroup.det_coe,
        Fintype.card_fin, mul_one] at h1
      exact h1.symm
    have hYX : (Y : Matrix (Fin 2) (Fin 2) F) = u⁻¹ • (X : Matrix (Fin 2) (Fin 2) F) := by
      rw [hXY, smul_smul, inv_mul_cancel₀ hu0, one_smul]
    have hXiX : ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        (X : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨u⁻¹, ?_, ?_⟩
    · rw [Fintype.card_fin, inv_pow, hu2, inv_one]
    · rw [Matrix.SpecialLinearGroup.coe_mul, hYX, Matrix.mul_smul, hXiX, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
  have key := eq_of_inv_mul_mem_center (CFSG.ClassicalInvolution.sl2_isPerfect h4)
    α.toMonoidHom (glConj G).toMonoidHom hcen
  exact ⟨G, fun b => DFunLike.congr_fun key b⟩

theorem commute_of_fix_of_ne_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p)
    {α : MulAut SL(2, F)} (hα : α ≠ 1) {a b : SL(2, F)} (ha : α a = a) (hb : α b = b) :
    a * b = b * a := by
  obtain ⟨G, hG⟩ := exists_glConj_eq hp hp5 hF α
  by_contra hab
  exact hα (eq_one_of_mem_range_of_fix_nonabelian ⟨G, MulEquiv.ext fun c => (hG c).symm⟩
    ⟨a, b, ha, hb, hab⟩)

end Item211Res4Proof

end CFSG.RankThree.PartTwo.Sec21
