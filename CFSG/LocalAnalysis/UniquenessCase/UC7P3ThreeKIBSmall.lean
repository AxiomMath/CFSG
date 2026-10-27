module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIB
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBLinTwo
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBUnitary
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBRee
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBM11
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.FixedFree
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus gammaCore)

namespace ThreeKIB

open CFSG.ComponentClassification.PSL3Four CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.ComponentClassification.PSL3Four.F4 (ω)

private def uMat (v : F4 × F4) : Matrix (Fin 3) (Fin 3) F4 := !![1, 0, v.1; 0, 1, v.2; 0, 0, 1]

private def tMat : Matrix (Fin 3) (Fin 3) F4 := !![0, 1, 0; 1, ω, 0; 0, 0, 1]

private def tAct (v : F4 × F4) : F4 × F4 := (v.2, v.1 + ω * v.2)

private theorem uMat_add (v w : F4 × F4) : uMat (v + w) = uMat v * uMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

private theorem tMat_mul_uMat (v : F4 × F4) : tMat * uMat v = uMat (tAct v) * tMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, tMat, tAct, Matrix.mul_apply, Fin.sum_univ_three]

private def uSL : Multiplicative (F4 × F4) →* SpecialLinearGroup (Fin 3) F4 where
  toFun v := ⟨uMat (Multiplicative.toAdd v), by
    rw [Matrix.det_fin_three]
    simp [uMat]⟩
  map_one' := Subtype.ext (by
    change uMat 0 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl)
  map_mul' v w := Subtype.ext (uMat_add _ _)

private def tSL : SpecialLinearGroup (Fin 3) F4 :=
  ⟨tMat, by rw [Matrix.det_fin_three]; decide⟩

private theorem tSL_conj (v : Multiplicative (F4 × F4)) :
    tSL * uSL v * tSL⁻¹ = uSL (Multiplicative.ofAdd (tAct (Multiplicative.toAdd v))) :=
  mul_inv_eq_of_eq_mul (Subtype.ext (tMat_mul_uMat _))

theorem fixedFreeFive_projectiveSL_three_four :
    SEFive.FixedFreeFive 2 (LinearFlag.projectiveSL 3 F4) := by
  refine fixedFreeFive_of_param (A := Multiplicative (F4 × F4))
    (IsPGroup.of_card (n := 4) (by rw [Nat.card_eq_fintype_card]; rfl))
    (a₀ := Multiplicative.ofAdd (1, 0)) (by decide) ((LinearFlag.proj 3 F4).comp uSL) ?_
    (LinearFlag.proj 3 F4 tSL) (fun v => Multiplicative.ofAdd (tAct (Multiplicative.toAdd v)))
    (fun v => by simp only [MonoidHom.coe_comp, Function.comp_apply, ← map_inv, ← map_mul,
      tSL_conj]) ?_
  · refine (injective_iff_map_eq_one _).2 fun v hv => ?_
    obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 (LinearFlag.proj_eq_one_iff.1 hv)
    have h02 := congrFun (congrFun hc 0) 2
    have h12 := congrFun (congrFun hc 1) 2
    simp only [uSL, MonoidHom.coe_mk, OneHom.coe_mk, uMat] at h02 h12
    simp at h02 h12
    exact toAdd_eq_zero.mp (Prod.ext h02 h12)
  · intro k hk0 hk5 v
    interval_cases k <;> revert v <;> decide

theorem coverActsTriviallyOnSmall_of_isoLie_l34 {L : Type} [Group L] [IsSimpleGroup L]
    (hI : IsoLie L (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩)) : CoverActsTriviallyOnSmall 3 L := by
  obtain ⟨hv, ⟨e⟩⟩ := hI
  have hPSL : CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 3 2 2 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e'⟩⟩ := hPSL
  let E : L ≃* LinearFlag.projectiveSL 3 F4 :=
    e'.trans ((CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 3 2 2 (by norm_num)
      hcard).trans ((CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F4 3 2 2 (by norm_num)
        natCard_F4').symm.trans projectiveSLEquivStated.symm))
  exact SEFive.coverActsTriviallyOnSmall_of_fixedFreeFive (q := 2) (Or.inl rfl)
    (fixedFreeFive_projectiveSL_three_four.of_mulEquiv E.symm)

end ThreeKIB

@[expose] def KIB3Small : Prop :=
  CoverActsTriviallyOnSmall 3 (alternatingGroup (Fin 6)) ∧
    ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid), q.p = 3 →
      q.exponent = 1 → CoverActsTriviallyOnSmall 3 (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group

set_option linter.unusedSectionVars false


theorem StronglyEmbeddedThreeKIB_of_small (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hSmall : KIB3Small) : StronglyEmbeddedThreeKIB := by
  intro X _ _ hX hO h2 N hN
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_three hO hN
  set K := CFSG.generalizedFitting X
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, -⟩ := exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded hO hK1 hN
  have hrk : 2 ≤ CFSG.Open.pRank 3 (P : Subgroup X) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1]
    exact h2
  have hΓX : gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hN.1 (top_le_iff.1 ?_)
    rw [← h]
    exact CFSG.LocalAnalysis.UniquenessCase.UCK.gammaCore_le_of_isStronglyPEmbedded hN P.isPGroup'
      hPN
  obtain ⟨-, -, hrows⟩ := hG3 X hX K hKn hKs hKnab hKC P hrk hΓX
  rcases hrows with ⟨q, hq3, hI, -⟩ | ⟨q, hq3, hI, -⟩ | ⟨m, hI, -⟩ | ⟨hI, -⟩ | ⟨⟨φ, -⟩, -⟩ |
      ⟨hI, -⟩ | ⟨-, hKt, hE, h9, hΓ, S, hS, -, -, hab, hC, hirr⟩
  ·
    exact ThreeKIB.coverActsTriviallyOnSmall_of_isoLie_linTwo hq3 hI
  ·
    by_cases h1 : q.exponent = 1
    · obtain ⟨hv, ⟨e⟩⟩ := hI
      exact ThreeKIB.coverActsTriviallyOnSmall_of_mulEquiv e.symm (hSmall.2 q hv hq3 h1)
    · exact ThreeKIB.coverActsTriviallyOnSmall_of_isoLie_unitary hq3
        (by have := q.exponent_pos; omega) hI
  ·
    exact ThreeKIB.coverActsTriviallyOnSmall_of_isoLie_ree hI
  ·
    exact ThreeKIB.coverActsTriviallyOnSmall_of_isoLie_l28 hI
  ·
    exact ThreeKIB.coverActsTriviallyOnSmall_of_mulEquiv φ.symm hSmall.1
  ·
    exact ThreeKIB.coverActsTriviallyOnSmall_of_isoLie_l34 hI
  ·
    exact ThreeKIB.coverActsTriviallyOnSmall_m11Row hKt hE h9 (hS.trans (hΓ.le.trans inf_le_right))
      hab hC hirr

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
