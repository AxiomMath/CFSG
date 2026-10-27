module

public import CFSG.RankThree.PartOne.TAIL.Glue2
public import CFSG.RankThree.PartOne.TAIL.FieldFusion
public import CFSG.RankThree.PartOne.TAIL.KSideData
public import CFSG.RankThree.PartOne.TAIL.KSideModel
public import CFSG.RankThree.PartOne.TAIL.LSideData
public import CFSG.RankThree.PartOne.TAIL.SylMain
public import CFSG.RankThree.PartOne.MB3.FieldReduce
public import CFSG.RankThree.PartOne.MB3.LnSevenFinal
public import CFSG.RankThree.PartOne.FLM.Holds

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)


theorem fieldFusionData_holds (hS : SchreierFor InCatalog) (hPE : FieldFixedPElements)
    (h107 : InSec10Seven) (hKF122 : KF122)
    (hKF1 : KF128Rank1)
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    FieldFusionData := by
  intro G _ _ p A c L B n cfg b S K hW hK hSK hEven hZ a d haA hdA hd1 hAeq hdK hfa hc hcind
  have hp7 : p = 7 := cfg.p_eq
  subst hp7
  have F := MB3.fieldSetting_of_tail hS hPE cfg hW hK hSK hEven hZ
    haA hdA hd1 hAeq hdK hfa hc hcind
  have hc7 : c ^ 7 = 1 := cfg.pow_p_eq_one cfg.c_mem
  have hbB : b ∈ B := hW.b_mem
  have hbL : b ∈ L := cfg.B_le_L hbB
  have hb1 : b ≠ 1 := hW.b_ne_one
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hbord : orderOf b = 7 := orderOf_eq_prime F.b_pow hb1
  have hEV : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)) ≤
      L ⊓ Subgroup.centralizer ({b} : Set G) :=
    le_inf F.E_le_L (F.E_le_K.trans F.K_le_centralizer)
  have hKd : KData G K c := by
    rcases MB3.fieldComponentsLn2_holds G L n cfg.n_mem cfg.model b hbL hbord _ hEV F.E_comp
      with hm | hm
    · have hn3 : (n - 3 = 3 ∨ n - 3 = 4) := by rcases cfg.n_mem with rfl | rfl <;> simp
      obtain ⟨Ff, hFf, hFfin, hcard, ⟨e⟩⟩ := FLM.fieldLmModel_holds hGA G c K (n - 3) hn3 F.K_qs hZ
        hcind hm
      let _ := hFf
      have _ := hFfin
      exact kData_of_model (m := n - 3) (Or.inr ⟨hn3, hcard⟩) e hc7 hcind
    · obtain ⟨Ff, hFf, hFfin, hcard, ⟨e⟩⟩ := fieldL28Model_holds hGA G c K F.K_qs hZ hcind hm
      let _ := hFf
      have _ := hFfin
      exact kData_of_model (m := 2) (Or.inl ⟨rfl, hcard⟩) e hc7 hcind
  have hBcard : Nat.card B = 49 := cfg.B_card
  have hB7 : IsPGroup 7 B := IsPGroup.of_card (n := 2) (by rw [hBcard]; norm_num)
  have hLd : LData G L B := lData_of_model cfg.n_mem cfg.model cfg.B_le_L hB7 hBcard
  have hev : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq cfg.setup).le
  have hC1 := pRank_centralizer_L_le_one hS h107 hKF122 cfg
  have h81 : ∀ x ∈ Subgroup.centralizer (B : Set G), (∃ k : ℕ, orderOf x = 7 ^ k) →
      x ∈ Subgroup.normalizer (K : Set G) := fun x hx hord =>
    mem_normalizer_of_pow_order_thetaComponentsAt (by decide) (by norm_num) hev F.K_mem.2
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx b hbB).symm)
      hord
  have hAsyl := aSylow_of_config cfg hKd hLd h81 F.c_field.2.1 hC1
  exact fusion_of_data F hS hKd hLd hKF1 hAsyl

end CFSG.RankThree.PartOne.TAIL
