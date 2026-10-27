module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergBIPSL2SylowInner

public section

namespace CFSG.Quasithin.He6.Aut

open CFSG.GorensteinWalter CFSG.QuasithinUnique
open scoped MatrixGroups

theorem pgl2Inner_eq_pslConjAut {p : ℕ} [Fact p.Prime] (hK : IsOddPrimePower (Nat.card (ZMod p)))
    (hcard : 3 < Nat.card (ZMod p)) (A : GL (Fin 2) (ZMod p)) :
    pgl2InnerAutPSL2 (ZMod p) hK hcard (Matrix.ProjGenLinGroup.mk A) = pslConjAut A := by
  apply MulEquiv.ext
  intro x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pgl2InnerAutPSL2_apply]
  induction x using QuotientGroup.induction_on with
  | H X =>
    rw [pslConjAut_mk]
    have h1 : (Matrix.SpecialLinearGroup.toGL (slConjAut A X) : GL (Fin 2) (ZMod p)) =
        A * Matrix.SpecialLinearGroup.toGL X * A⁻¹ := by
      apply Units.ext
      simp [coe_slConjAut]
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
      h1, map_mul, map_mul, map_inv]

theorem autInner_psl2_prime {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (α : MulAut PSL(2, ZMod p)) (S : Sylow 2 PSL(2, ZMod p))
    (hα : ∀ s ∈ (S : Subgroup PSL(2, ZMod p)), α s = s) :
    ∃ l : PSL(2, ZMod p), ∀ g, α g = l * g * l⁻¹ := by
  have hodd : Odd p := by
    rcases hp.out.eq_two_or_odd' with h | h
    · omega
    · exact h
  have hKcard : Nat.card (ZMod p) = p ^ 1 := by simp
  have hK : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp.out, hodd, le_refl 1, hKcard⟩
  have hcard : 3 < Nat.card (ZMod p) := by rw [Nat.card_zmod]; omega
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective (ZMod p) hKcard hK hcard α
  have hx1 : x.right = 1 := by
    apply RingEquiv.ext
    intro a
    have := RingHom.ext_zmod x.right.toRingHom (RingHom.id (ZMod p))
    exact congrFun (congrArg DFunLike.coe this) a
  have hxdec : x = SemidirectProduct.inl x.left := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x, hx1]
    simp
  rw [hxdec, pGammaL2ToMulAutPSL2_inl] at hx
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective x.left
  rw [← hA, pgl2Inner_eq_pslConjAut] at hx
  have hfix : ∀ q ∈ S, pslConjAut A q = q := by
    rw [hx]
    exact hα
  have hring : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  obtain ⟨-, c, -, -, hconj⟩ := odd_linear_two_projective_Sylow_centralizer_inner hring S A hfix
  refine ⟨QuotientGroup.mk c, fun g => ?_⟩
  rw [← hx, hconj]
  rfl

end CFSG.Quasithin.He6.Aut
