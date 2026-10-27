module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212C

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G}

theorem omegaOneCenterOf_Rp_le (hy : Hyp4_2_3 G T M L Mm I)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ≤ omegaOneCenterOf (pCoreOf 2 I) := by
  have hRp : IsSylowTwoOf (T ⊓ centralizerSection M (conjClosure L T) (pCoreOf 2 (conjClosure L T)))
      (centralizerSection M (conjClosure L T) (pCoreOf 2 (conjClosure L T))) :=
    isSylowTwoOf_inf_centralizerSection (isSylowTwoOf_of_le hy.sylow
      (le_inf hy.T_le (CFSG.Quasithin.le_normalizer_conjClosure L T)))
  have hV := lemma_4_1_5_one (hy.hyp4_1_1 h37 h38 h39) hy.sigma hRp le_rfl hy.gammaStar hy.R_le
  rw [hy.pCoreOf_sup_eq_inf]
  intro z hz
  exact Subgroup.subset_closure ⟨hV hz, sq_eq_one_of_mem_omegaOneCenterOf hz⟩

theorem omegaOneCenter_Rp_inf_centralizer_eq_bot (c : Conf4212 G T M L I H K)
    (hy : Hyp4_2_3 G T M L Mm I) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hLH_C : omegaOneCenterOf (pCoreOf 2 I) ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) ≤
      Subgroup.centralizer (K : Set G)) :
    omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hΩ : omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ≤ omegaOneCenterOf (pCoreOf 2 I) :=
    omegaOneCenterOf_Rp_le hy h37 h38 h39
  have hLHL : perfectCore (L ⊓ H) ≤ L := (perfectCore_le _).trans inf_le_left
  have hZK : omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (K : Set G) := by
    intro z hz
    have hz' : z ∈ omegaOneCenterOf (pCoreOf 2 I) ⊓
        Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) :=
      ⟨hΩ hz.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLHL) hz.2⟩
    exact hLH_C hz'
  have hKc : K ≤ Subgroup.centralizer ((omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓
      Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.mp (hZK hz)) k hk).symm
  have hKN : K ≤ Subgroup.normalizer ((omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓
      Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    hKc.trans (Subgroup.centralizer_le_normalizer _)
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := by
    refine _root_.sup_le Subgroup.le_normalizer ?_
    intro t ht
    exact c.normal (hy.T_le ht)
  have hXN : L ⊔ T ≤ Subgroup.normalizer ((omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓
      Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro x hx
    refine mem_normalizer_inf ?_ ?_
    · exact ((le_normalizer_pCoreOf 2 (L ⊔ T)).trans
        (normalizer_le_normalizer_omegaOneCenterOf _)) hx
    · exact (CFSG.Quasithin.normalizer_le_normalizer_centralizer L) (hLTN hx)
  have hPgrp : IsPGroup 2 ((omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓
      Subgroup.centralizer (L : Set G) : Subgroup G)) :=
    (pCoreOf_isPGroup 2 (L ⊔ T)).to_le (inf_le_left.trans (omegaOneCenterOf_le _))
  have hU := (c.hyp421.isUniqueM_sup h37 h38 h39).1
  by_contra hne
  exact c.K_not_le (hKN.trans (isUniqueM_normalizer_le hU hne hPgrp hXN))

theorem omega_inf_centralizer_eq_bot_of_eq (c : Conf4212 G T M L I H K)
    (hZ0 : omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hR : pCoreOf 2 I = pCoreOf 2 (L ⊔ T)) :
    omegaOneCenterOf (pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  have hΩ : omegaOneCenterOf (pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) ≤
      omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) := by
    rw [hR]
    exact inf_le_left
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
    refine _root_.sup_le (le_normalizer_pCoreOf 2 L) ?_
    intro t ht
    exact normalizer_le_normalizer_pCoreOf 2 L (c.normal (c.hyp421.T_le ht))
  have hO2 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) hLTN
      (pCoreOf_isPGroup 2 L)
  have hZO2 : omegaOneCenterOf (pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.centralizer (pCoreOf 2 L : Set G) :=
    le_centralizer_of_le_omegaOneCenterOf hΩ hO2
  have hZLH : omegaOneCenterOf (pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) := by
    intro z hz
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr c.LH_le) hz.2
  have hZL : omegaOneCenterOf (pCoreOf 2 I) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.centralizer (L : Set G) := by
    intro z hz
    have hLW : L ≤ Subgroup.centralizer ({z} : Set G) := by
      refine c.L_le.trans (_root_.sup_le ?_ ?_)
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hZLH hz) x hx)
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hZO2 hz) x hx)
    exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLW hx)
  exact eq_bot_iff.mpr ((le_inf hΩ hZL).trans hZ0.le)

end CFSG.Quasithin.H13.Ch4.CentK
