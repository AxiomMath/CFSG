module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H60
public import CFSG.Quasithin.Vol2.Ch10SecKIK2h
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar
public import CFSG.Quasithin.Vol2.Ch10SecQ9H58

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRT

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I H K M₁ J : Subgroup G} {n m : ℕ}

theorem localSQTK (cfg : B0KConfig G T L I H K M₁ J n m) : LocalSQTK G := by
  have := cfg.hyp.fsu.simple
  exact (qtkeCore_of_cat cfg.hyp.fsu.nonabelian cfg.hyp.fsu.qtke).1

theorem T_le (cfg : B0KConfig G T L I H K M₁ J n m) : T ≤ M₁ :=
  (SecE.le_normalizer_baum T).trans (le_sup_left.trans cfg.hM₁.2)

theorem sylow (cfg : B0KConfig G T L I H K M₁ J n m) : IsSylowTwoOf T M₁ :=
  ⟨T_le cfg, cfg.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le cfg.hyp.fsu.sylow (T_le cfg)⟩

theorem J_le (cfg : B0KConfig G T L I H K M₁ J n m) : J ≤ M₁ := le_of_mem_cComp cfg.hJ

theorem K_le (cfg : B0KConfig G T L I H K M₁ J n m) : K ≤ M₁ := cfg.hKJ.trans (J_le cfg)

theorem K_mem_lFamily (cfg : B0KConfig G T L I H K M₁ J n m) : K ∈ lFamily T :=
  cComp_subset_lFamily cfg.hH.1.1 cfg.hK

theorem pCoreOf_ne_bot (cfg : B0KConfig G T L I H K M₁ J n m) : pCoreOf 2 M₁ ≠ ⊥ :=
  (inH_of_inM cfg.hM₁).2

theorem K_top_perfect (cfg : B0KConfig G T L I H K M₁ J n m) :
    ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    perfect_of_mem_cComp cfg.hK]

theorem two_le (cfg : B0KConfig G T L I H K M₁ J n m) : 2 ≤ m := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := cfg.hKF
  exact SL2Inv.two_le_of_perfect (K_top_perfect cfg) hF e

theorem barData (cfg : B0KConfig G T L I H K M₁ J n m) :
    Ch11.SecA.BarData (modO2Image M₁ K) m := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := cfg.hKF
  obtain ⟨e'⟩ := SecC.C10KH.lbar_modO2_equiv (K_le cfg)
  exact Ch11.SecA.barData_of_quot_SL2 (two_le cfg) hF (e'.trans e)

theorem sqtkHypCat_bar (cfg : B0KConfig G T L I H K M₁ J n m) :
    Vol2Native.SQTKHypCat (↥M₁ ⧸ CFSG.pCore 2 ↥M₁) :=
  Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot (localSQTK cfg) (pCoreOf_ne_bot cfg)

theorem sylow_bar (cfg : B0KConfig G T L I H K M₁ J n m) :
    IsSylowTwoOf ((T.subgroupOf M₁).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M₁))) ⊤ :=
  isSylowTwoOf_top_map_of_surjective (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf (sylow cfg))
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M₁)) (QuotientGroup.mk'_surjective _)

theorem Kbar_mem_lFamily (cfg : B0KConfig G T L I H K M₁ J n m) :
    modO2Image M₁ K ∈ lFamily ((T.subgroupOf M₁).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M₁))) :=
  modO2Image_mem_lFamily (sylow cfg) (K_le cfg) (K_mem_lFamily cfg)

theorem Jbar_mem_cComp (cfg : B0KConfig G T L I H K M₁ J n m) :
    modO2Image M₁ J ∈ cComp (⊤ : Subgroup (↥M₁ ⧸ CFSG.pCore 2 ↥M₁)) :=
  modO2Image_mem_cComp cfg.hJ

theorem Kbar_le_Jbar (cfg : B0KConfig G T L I H K M₁ J n m) :
    modO2Image M₁ K ≤ modO2Image M₁ J :=
  Subgroup.map_mono fun _ hx => cfg.hKJ hx

theorem list (h312 : Vol2Native.A312ForSQTKCat) (cfg : B0KConfig G T L I H K M₁ J n m) :
    modO2Image M₁ K = modO2Image M₁ J ∨ A312Case (modO2Image M₁ K) (modO2Image M₁ J) ∨
      A312Nonquasi (modO2Image M₁ K) (modO2Image M₁ J) :=
  Vol2Native.lemma_1_2_4_list (localSQTK cfg) h312 (pCoreOf_ne_bot cfg) (sylow cfg) (K_le cfg)
    (K_mem_lFamily cfg) cfg.hJ cfg.hKJ

theorem le_sup_of_modO2Image_eq (cfg : B0KConfig G T L I H K M₁ J n m)
    (h : modO2Image M₁ K = modO2Image M₁ J) : J ≤ K ⊔ pCoreOf 2 M₁ := by
  intro j hj
  have hjM : j ∈ M₁ := J_le cfg hj
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨j, hjM⟩ ∈ modO2Image M₁ K := by
    rw [h]
    exact ⟨⟨j, hjM⟩, hj, rfl⟩
  obtain ⟨k, hk, hkj⟩ := hmem
  have hq : k⁻¹ * ⟨j, hjM⟩ ∈ CFSG.pCore 2 ↥M₁ := QuotientGroup.eq.mp hkj
  have hqG : ((k⁻¹ * ⟨j, hjM⟩ : ↥M₁) : G) ∈ pCoreOf 2 M₁ := by
    exact ⟨_, hq, rfl⟩
  have hkK : (k : G) ∈ K := hk
  have hj' : j = (k : G) * ((k⁻¹ * ⟨j, hjM⟩ : ↥M₁) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [hj']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hkK) (Subgroup.mem_sup_right hqG)

theorem eq_of_modO2Image_eq (cfg : B0KConfig G T L I H K M₁ J n m)
    (h : modO2Image M₁ K = modO2Image M₁ J) : K = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : pCoreOf 2 M₁ ≤ Subgroup.normalizer (K : Set G) := pCoreOf_le_normalizer_K cfg
  have hKn : (K.subgroupOf (K ⊔ pCoreOf 2 M₁)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hKN)
  have hsolv : Group.IsSolvable ↥(pCoreOf 2 M₁) := by
    have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁).isNilpotent
    infer_instance
  have hP : perfectCore (K ⊔ pCoreOf 2 M₁) ≤ K :=
    perfectCore_le_of_sup_solvable le_sup_left hKn rfl hsolv
  have hJ : J ≤ perfectCore (K ⊔ pCoreOf 2 M₁) :=
    le_perfectCore_of_perfect (le_sup_of_modO2Image_eq cfg h) (perfect_of_mem_cComp cfg.hJ)
  exact le_antisymm cfg.hKJ (hJ.trans hP)

end CFSG.Quasithin.Vol2.Ch10.SecB.KRT
