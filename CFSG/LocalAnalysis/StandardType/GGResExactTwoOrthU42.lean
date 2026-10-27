module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmComp
public import CFSG.Assembly.GL83LieDefs
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthOrthIdent
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoBasic
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightBasic
import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveU52Root
import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.RankThree.PartOne.KC.OrthogonalFactorization
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSmall
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType

open Polynomial Module QuadraticMap CFSG.Assembly CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem ggResX2_isU42_specialBlock (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : primaryMultiplicity x.toLinearMap h = 4) :
    LargeEvenIsU42 ↥((specialBlock Q x h).subgroupOf (orthDerived Q)) := by
  classical
  have hcyc : h = CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 K :=
    (CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.primaryFactor_cases hK hx hh).resolve_left
      hne1
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself : h = reciprocalPolynomial h := by
    rw [hcyc]
    unfold CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3
    exact (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.reciprocalPolynomial_quadratic
      (K := K)).symm
  obtain ⟨hdeg2, b, hb⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_selfDual_matrix_data hx hh
      hne1 hself hm
  obtain ⟨ε, -⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_specialBlock_equiv_SU hx hh b
      hb
  have hcardE : Nat.card (AdjoinRoot h) = (2 ^ 1) ^ 2 := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hdeg2, hK, pow_one]
  have hSB : specialBlock Q x h ≤ orthDerived Q := by
    have hh' := hh
    rw [hcyc] at hh' ⊢
    exact CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.specialBlock_le_orthDerived hK hx hQ hT
      hh'
  have hU := IOneU52.unitarySU_four_isU42 hcardE
  rw [hK] at ε
  exact IOneU52.isU42_of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hSB).trans ε) hU

theorem ggResX2_four_le_primaryMultiplicity (hK : Nat.card K = 2) {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1)
    (hns : ¬ Group.IsSolvable ↥((specialBlock Q x h).subgroupOf (orthDerived Q))) :
    4 ≤ primaryMultiplicity x.toLinearMap h := by
  classical
  by_contra hlt
  have hcyc : h = CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3 K :=
    (CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.primaryFactor_cases hK hx hh).resolve_left
      hne1
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself : h = reciprocalPolynomial h := by
    rw [hcyc]
    unfold CFSG.HardMathSupport.Timmesfeld.CrossChar.cyc3
    exact (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.reciprocalPolynomial_quadratic
      (K := K)).symm
  obtain ⟨hdeg2, b, hb⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_selfDual_matrix_data hx hh
      hne1 hself rfl
  obtain ⟨ε, -⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_specialBlock_equiv_SU hx hh b
      hb
  have hcardE : Nat.card (AdjoinRoot h) = (2 ^ 1) ^ 2 := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hdeg2, hK, pow_one]
  rw [hK] at ε
  have hsol : Group.IsSolvable ↥(CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap h) 2
      (AdjoinRoot h)) :=
    SmallU.isSolvable_unitarySU_small (TableBU.unitaryFieldData_of_card hcardE le_rfl)
      (hx.primaryMultiplicity_pos hh) (by omega)
  have hsolB : Group.IsSolvable ↥(specialBlock Q x h) :=
    solvable_of_solvable_injective (f := ε.toMonoidHom) ε.injective
  let ι : ↥((specialBlock Q x h).subgroupOf (orthDerived Q)) →* ↥(specialBlock Q x h) :=
    { toFun := fun g => ⟨((g : ↥(orthDerived Q)) : V ≃ₗ[K] V), g.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine hns (solvable_of_solvable_injective (f := ι) fun a b hab => ?_)
  have hab' : ((ι a : ↥(specialBlock Q x h)) : V ≃ₗ[K] V) = ι b := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext hab')

theorem ggResX2_isU42_fixed (hK : Nat.card K = 2) {x : V ≃ₗ[K] V} {p : ℕ}
    (hx : OddOrderIsometry Q p x) (hdim : finrank K (fixedSpace x) = 6)
    (hts : ∀ U : Submodule K (fixedSpace x), finrank K U = 3 →
      ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0) :
    LargeEvenIsU42 ↥((supportedFixedDerived Q x).subgroupOf (orthDerived Q)) := by
  have : CharP K 2 := CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.charP_two hK
  obtain ⟨E, _, _, hE, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.OmegaPilot.nonempty_orthDerived_mulEquiv_statedSU_of_six
      (f := 1) (by rw [hK, pow_one]) hx.polarBilin_fixed_nondegenerate hdim hts
  exact IOneU52.isU42_of_mulEquiv ((Subgroup.subgroupOfEquivOfLe
    hx.supportedFixedDerived_le_orthDerived).trans ((supportedFixedDerivedEquiv hx).trans e))
    (IOneU52.unitarySU_four_isU42 hE)

end CFSG.StandardType
