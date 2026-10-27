module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H52
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch10SecQ9H50

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_baum_inf
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1)
    (h1022 : Stmt10_2_2) (hE22 : E2.E22StatementC) (he23 : E2.E23Statement)
    (hAS : Ch11.SecH.AS_I_1_3_L2) {T L I H K M₁ J : Subgroup G} {n m : ℕ}
    (cfg : B0KConfig G T L I H K M₁ J n m) : IsSylowTwoOf (baum T ⊓ K) K := by
  have hsyl := isSylowTwoOf_baum_oTwoUpper hF6 h37 h38 h322 h331 h1013 h1021 h1022 hE22 he23
    hAS cfg.hyp cfg.case1 cfg.hH cfg.hn cfg.hZH
  have hKH : K ≤ H := le_of_mem_cComp cfg.hK
  have hKp : ⁅K, K⁆ = K := perfect_of_mem_cComp cfg.hK
  have hKX : K ≤ oTwoUpper H ⊔ baum T :=
    calc K = oTwoUpper K := eq_oTwoUpper_of_perfect hKp
      _ ≤ oTwoUpper H := oTwoUpper_mono hKH
      _ ≤ _ := le_sup_left
  have hXH : oTwoUpper H ⊔ baum T ≤ H :=
    sup_le (oTwoUpper_le H) ((inf_le_left : baum T ≤ T).trans cfg.hH.1.1)
  have hsub := B113.isSubnormal_inf_of_le cfg.hK.2.2.1 hXH
  rw [inf_eq_right.mpr hKX] at hsub
  exact A312.isSylowTwoOf_inf_of_subnormal hsub hsyl

theorem pCoreOf_le_normalizer_K {T L I H K M₁ J : Subgroup G} {n m : ℕ}
    (cfg : B0KConfig G T L I H K M₁ J n m) :
    pCoreOf 2 M₁ ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHM : H ≤ M₁ := le_sup_right.trans cfg.hM₁.2
  have hTM₁ : T ≤ M₁ := (SecE.le_normalizer_baum T).trans (le_sup_left.trans cfg.hM₁.2)
  have hTS : IsSylowTwoOf T M₁ :=
    ⟨hTM₁, cfg.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le cfg.hyp.fsu.sylow hTM₁⟩
  have hQT : pCoreOf 2 M₁ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hTS
  have hQH : pCoreOf 2 M₁ ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans cfg.hH.1.1)
      (hHM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₁))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁)
  exact hQH.trans (P134.pCoreOf_le_normalizer_of_mem_cComp cfg.hK)

end CFSG.Quasithin.Vol2.Ch10.SecB
