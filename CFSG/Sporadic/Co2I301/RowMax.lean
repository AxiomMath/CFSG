module

import CFSG.Sporadic.Co2I301.RowMaxAux
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Sporadic.Co2I301.Spec

public noncomputable section

namespace CFSG.Sporadic.Co2I301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
  CFSG.HardMathSupport.Dickson.I271 CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301


theorem row_hMax : ∀ (A : Type) [Group A] [Finite A] (ι : ↥co2P →* A), Function.Injective ι →
    ι.range.Normal → Subgroup.centralizer (ι.range : Set A) = ⊥ →
    ∀ R' : Subgroup A, IsPGroup 2 R' →
      (K0.subgroupOf co2P ⊔ B1.subgroupOf co2P).map ι ≤ Subgroup.normalizer (R' : Set A) →
      (locQ.subgroupOf co2P).map ι ≤ R' → R' = (locQ.subgroupOf co2P).map ι := by
  intro A _ _ ι hι hN hC R' hR' hKB hQR'
  have htop := range_eq_top_of_forall_inner CTUC_Co2_full_automorphisms_inner ι hι hN hC
  have hR'eq : R' = (R'.comap ι).map ι := by
    rw [Subgroup.map_comap_eq, htop, top_inf_eq]
  rw [hR'eq, eq_locQ_of_invariant (R'.comap ι) (hR'.comap_of_injective ι hι)
    ((Subgroup.map_le_iff_le_comap.1 hKB).trans (Subgroup.le_normalizer_comap ι))
    (Subgroup.map_le_iff_le_comap.1 hQR')]

end CFSG.Sporadic.Co2I301
