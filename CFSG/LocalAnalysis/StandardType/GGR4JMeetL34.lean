module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.RankThree.PartTwo.Sec19.Step1918ProofInner
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021RankHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem l34_sl_eq (K : Type) [Field K] :
    LargeEvenSLGroup (Fin 3) K = CFSG.Open.StatedSL 3 K := by
  rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]
  rfl

private noncomputable def l34_slProj_equiv_of_eq (K : Type) [Field K]
    {H : Subgroup (GL (Fin 3) K)} (hH : H = CFSG.Open.StatedSL 3 K) :
    LargeEvenProj H ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) := by
  subst hH
  exact MulEquiv.refl _

private noncomputable def l34_slProj_equiv_projSL (K : Type) [Field K] :
    LargeEvenProj (LargeEvenSLGroup (Fin 3) K) ≃* CFSG.PGLModel.projSL 3 K :=
  (l34_slProj_equiv_of_eq K (l34_sl_eq K)).trans
    (CFSG.PGLModel.projSLEquivStatedProj 3 K).symm

private noncomputable def l34_projSL_fieldEquiv {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) : CFSG.PGLModel.projSL 3 K ≃* CFSG.PGLModel.projSL 3 L :=
  (CFSG.PGLModel.projSLEquivStatedProj 3 K).trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      ((CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) e).trans
        ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 L).trans
          (CFSG.PGLModel.projSLEquivStatedProj 3 L).symm)))

private theorem l34_mapQuotient_center_injective (J : Type) [Group J]
    (hJ : commutator J = ⊤) :
    Function.Injective (MulAut.mapQuotient (Subgroup.center J)) := by
  intro a b hab
  have h1 : MulAut.mapQuotient (Subgroup.center J) (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 : a * b⁻¹ = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.T2021.eq_one_of_mapQuotient_center_eq_one hJ (a * b⁻¹) h1
  exact mul_inv_eq_one.mp h2

theorem ggAut_L34_card_le_nine (J : Type) [Group J] [Finite J] (hJ : commutator J = ⊤)
    (hlab : GGHasLabel ⟨.A, 2, 2⟩ (J ⧸ Subgroup.center J)) (W : Subgroup (MulAut J))
    (hW : IsElemAbelian 3 W) : Nat.card W ≤ 9 := by
  obtain ⟨K, hKfield, hKfinite, hKcard, hiso⟩ := hlab
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  obtain ⟨iso⟩ := hiso
  have hK4 : Nat.card K = 4 := by simpa using hKcard
  have hGF4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hK4' : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK4
  have hGF4' : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hGF4
  let e : K ≃+* GaloisField 2 2 :=
    FiniteField.ringEquivOfCardEq (by rw [hK4', hGF4'])
  let ψ : J ⧸ Subgroup.center J ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 2) :=
    iso.trans ((l34_slProj_equiv_projSL K).trans (l34_projSL_fieldEquiv e))
  let φ : MulAut J →* MulAut (J ⧸ Subgroup.center J) := MulAut.mapQuotient (Subgroup.center J)
  have hφinj : Function.Injective φ := l34_mapQuotient_center_injective J hJ
  let W' : Subgroup (MulAut (J ⧸ Subgroup.center J)) := W.map φ
  have hW'card : Nat.card W' = Nat.card W := Subgroup.card_map_of_injective hφinj
  have hW'ea : IsElemAbelian 3 W' := CFSG.Open.IsElemAbelian.map hW φ
  have hle : Nat.card W' ≤ 9 :=
    CFSG.RankThree.PartTwo.Sec19.Step1918Proof.card_le_nine_of_L34 ψ hW'ea
  rwa [hW'card] at hle

end CFSG.StandardType

end
