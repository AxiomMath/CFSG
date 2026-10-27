module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS17

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

namespace S5Data

variable {T L I H K : Subgroup G} {q t : G} (D : S5Data T L I H K q t)
include D

theorem exists_XJ
    (h311 : Theorem311Stmt) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hshape : Stmt7_0_1_shape) (h113 : ASInputs.AS_C_1_13) :
    ∃ X J : Subgroup G, CFSG.SectionRank.IsSQTKCat ↥X ∧ IsSylowTwoOf (Ch10.T1 T L) X ∧
      J ∈ cComp X ∧ L < J ∧ Ch10.T1 T L ≤ Subgroup.normalizer (J : Set G) ∧
      ∀ E : Subgroup G, E ≤ J → IsElemAbelian 3 E → Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := D.hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat D.hyp.fsu.nonabelian D.hyp.fsu.qtke).1
  have hRT1 := D.R_le_T1 h37 h38
  have hLR := D.L_le_centralizer_R h37 h38
  have hKR := D.K_le_centralizer_R h113 h37
  have hR2 : IsPGroup 2 (CFSG.conjugate (fsuUL T L I ⊓ K) t) :=
    D.hyp.fsu.sylow.1.to_le (hRT1.trans inf_le_left)
  have hXR : L ⊔ K ⊔ Ch10.T1 T L ≤
      Subgroup.normalizer (CFSG.conjugate (fsuUL T L I ⊓ K) t : Set G) :=
    sup_le (sup_le (hLR.trans (Subgroup.centralizer_le_normalizer _))
      (hKR.trans (Subgroup.centralizer_le_normalizer _))) (D.T1_le_normalizer_R h37 h38)
  have hX2 : pCoreOf 2 (L ⊔ K ⊔ Ch10.T1 T L) ≠ ⊥ := by
    intro hb
    have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (hRT1.trans le_sup_right) hXR hR2
    rw [hb] at h1
    exact D.R_ne_bot (le_bot_iff.mp h1)
  have hsyl := D.isSylowTwoOf_of_le_normalizer h311 h331 h37 h38 hshape le_sup_right hXR
  have hLfam : L ∈ lFamily (Ch10.T1 T L) :=
    cComp_mem_of_le (SecE.mem_cComp_L0T D.hyp) le_sup_left
      (sup_le ((SecA.le_fsuL0 T L).trans le_sup_left) (inf_le_left.trans le_sup_right))
  obtain ⟨J, hJ, hLJ⟩ := Vol2Native.lemma_1_2_4_exists hK h37 h39 hX2 hsyl
    (le_sup_left.trans le_sup_left) hLfam
  have hJX := le_of_mem_cComp hJ
  have hXJ : L ⊔ K ⊔ Ch10.T1 T L ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).mp
      (Vol2Native.lemma_1_2_4_normal hK h37 h38 hX2 hsyl hLfam hLJ hJ inf_le_right)
  obtain ⟨αK, hαKs, hαKk, -⟩ := D.hKa
  have hKJ : K ≤ J := le_of_normal_of_not_le (perfect_of_mem_cComp D.hK) hαKs hαKk
    ((le_sup_right.trans le_sup_left).trans hXJ) (hLJ D.hqL) D.hqK
    (alpha_ne_one_of_three hαKk D.hqK D.hq3)
  have hLM : L ≤ fsuM T L := (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_fsuM T L)
  have hT1N : Ch10.T1 T L ≤ Subgroup.normalizer ((L ⊔ K : Subgroup G) : Set G) := by
    intro x hx
    rw [← A38.map_conj_eq_iff, Subgroup.map_sup, A38.map_conj_eq_iff.mpr hx.2,
      A38.map_conj_eq_iff.mpr (D.hT1K hx)]
  have hJLK : J ≤ L ⊔ K := by
    rw [eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hJ)]
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    exact mem_of_mem_sup_of_odd hT1N (D.hyp.fsu.sylow.1.to_le inf_le_left) (hJX hy.1) hy.2
  have hJq2 : J ≤ Subgroup.centralizer ({t⁻¹ * q * t} : Set G) :=
    hJLK.trans (sup_le (D.L_le_centralizer_q2 h113 h37) (D.K_le_centralizer_q2 h113 h37))
  have hq2J : t⁻¹ * q * t ∉ J := by
    obtain ⟨w, hwR, hmov⟩ := D.exists_moved
    intro h
    apply hmov
    have hc := Subgroup.mem_centralizer_iff.mp ((hJLK.trans (sup_le hLR hKR)) h) w hwR
    rw [← hc]
    group
  have hq23 : (t⁻¹ * q * t) ^ 3 = 1 := by rw [← D.orderOf_q2]; exact pow_orderOf_eq_one _
  refine ⟨L ⊔ K ⊔ Ch10.T1 T L, J, hK _ hX2, hsyl, hJ,
    lt_of_le_of_ne hLJ fun h => D.hKM ((hKJ.trans h.symm.le).trans hLM),
    le_sup_right.trans hXJ, fun E hEJ hE => ?_⟩
  exact card_le_three_of_centralizer D.hyp.fsu.qtke D.R_ne_bot hR2 (hJX.trans hXR) hq23
    D.q2_mem_normalizer_R hq2J hJq2 hEJ hE

end S5Data

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
