module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonL2Holds
import CFSG.LocalAnalysis.StandardType.GGRawTorusPClassicalTwo
import CFSG.RankThree.PartTwo.KFacts.K72Omega
import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Triple
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.K3Core

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

theorem linShape_rank_pgl2
    {E : Type} [Field E] [Finite E] (hchar : CharP E 2)
    (hE : 4 ≤ Nat.card E) :
    ∀ B : Subgroup (MulAut (PSLg 2 E)),
      B ≤ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) E)) Set.univ →
      IsElemAbelian 3 B → Nat.card B ≤ 3 := by
  haveI : CharP E 2 := hchar
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro B hB hBab
  have hcyc : ∀ S : Sylow 3 (PSLg 2 E), IsCyclic ↥(S : Subgroup (PSLg 2 E)) := by
    intro S
    let e : PSLg 2 E ≃* Matrix.SpecialLinearGroup (Fin 2) E :=
      CFSG.LocalAnalysis.GLTheoremA.projEquiv E
    have hQ : IsPGroup 3 ↥(Subgroup.map e.toMonoidHom (S : Subgroup (PSLg 2 E))) :=
      S.isPGroup'.map e.toMonoidHom
    have hcyc' : IsCyclic ↥(Subgroup.map e.toMonoidHom (S : Subgroup (PSLg 2 E))) :=
      CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic (p := 3) (by norm_num) _ hQ
    haveI : IsCyclic ↥(Subgroup.map e.toMonoidHom (S : Subgroup (PSLg 2 E))) := hcyc'
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (S : Subgroup (PSLg 2 E)) e.toMonoidHom e.injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective (S : Subgroup (PSLg 2 E)) e.toMonoidHom e.injective).symm.surjective
  have hBinner : B ≤ (MulAut.conj : PSLg 2 E →* MulAut (PSLg 2 E)).range := by
    intro φ hφ
    obtain ⟨r, hr⟩ :=
      CFSG.StandardType.RawTorusPClassical.exists_conj_eq_of_mem_two (K := E) (hB hφ)
    exact MonoidHom.mem_range.mpr ⟨r, hr.symm⟩
  have hcycB : IsCyclic ↥B :=
    CFSG.RankThree.PartTwo.KFacts.isCyclic_of_le_range_conj (X := PSLg 2 E) hcyc
      (CFSG.Open.IsElemAbelian.isPGroup hBab) hBinner
  exact CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.l62_card_le_three_of_cyclic hBab hcycB

end CFSG.StandardType.TablePThreeKG

end
