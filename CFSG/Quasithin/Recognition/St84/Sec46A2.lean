module

public import CFSG.Quasithin.Recognition.St84.Sec46A1
public import CFSG.Quasithin.Recognition.St84.TransportMap
public import CFSG.GroupTheory.Commutator.JoinNormalizer

import CFSG.Quasithin.Recognition.St84.Gen.L2SecDim
import CFSG.Quasithin.Recognition.St84.Gen.NatSecIndex
import CFSG.Quasithin.Recognition.St84.Gen.NatSecLines
import CFSG.Quasithin.Recognition.St84.Gen.NatSecPre
import CFSG.Quasithin.H13.NQS13412A
import CFSG.Quasithin.Vol2.Ch8Sec2L829LNb
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S27Tools
public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

private theorem K_le_normalizer_Z (X : Setup Γ G) (i : ℤ) :
    X.K ≤ Subgroup.normalizer (X.Z i : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact X.Z_normal i k (X.K_le_Gi i hk)

private theorem commutator_eq_one_of_mem_Z_Q (X : Setup Γ G) {i : ℤ} {z q : G}
    (hz : z ∈ X.Z i) (hq : q ∈ X.Q i) : ⁅z, q⁆ = 1 := by
  have hcent : z ∈ Subgroup.centralizer (X.Q i : Set G) := (X.Z_le_center i hz).2
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_centralizer_iff.mp hcent q hq).symm

private theorem caseA_Z_zero_le_Q_inf (X : Setup Γ G)
    (A : X.CaseA) :
    X.Z 0 ≤ X.Q (-1) ⊓ X.Q 1 ∧
      (X.HasB 0 3 ∨ X.HasB 0 2) ∧
      (X.HasB 0 3 → X.Z 0 = centerOf (X.L 0)) := by
  have H := A.hyp
  have hc := H.char
  have hZQ1 : X.Z 0 ≤ X.Q 1 := by
    by_contra hnot
    have hAedge : X.Z 0 ≤ X.edgeSylow 0 := (X.Z_le_Q 0).trans (X.Q_le_edgeSylow_left 0)
    have hsup : X.Z 0 ⊔ X.Q 1 = X.edgeSylow 0 :=
      X.sup_Q_eq_edgeSylow_of_gen 0 (inf_le_left.trans (K_le_normalizer_Z X 0)) hAedge hnot
    have hZneg : X.Z (-1) ≤ X.Z 0 ⊔ X.Q 1 := by
      rw [hsup, X.edgeSylow_zero, ← (X.caseA_pos A).1]
      exact le_sup_left
    have hZ1Q : X.Z 1 ≤ X.Q 0 := X.Z_le_Q_of_lt A.b₁ (by omega)
    have hRbot : ⁅X.Z (-1), X.Z 1⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro a ha b hbm
      have hZc : X.Z 0 ≤ Subgroup.centralizer ({b} : Set G) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact Subgroup.mem_centralizer_iff.mp (X.Z_le_center 0 hz).2 b (hZ1Q hbm)
      have hQc : X.Q 1 ≤ Subgroup.centralizer ({b} : Set G) := by
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (Subgroup.mem_centralizer_iff.mp (X.Z_le_center 1 hbm).2 q hq).symm
      have hcent : a ∈ Subgroup.centralizer ({b} : Set G) := (sup_le hZc hQc) (hZneg ha)
      have hcomm : b * a = a * b := Subgroup.mem_centralizer_iff.mp hcent b (by simp)
      simpa using commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
    exact A.R_ne (le_bot_iff.mp hRbot)
  have hZQm1 : X.Z 0 ≤ X.Q (-1) := by
    obtain ⟨t, ht, htm⟩ := X.exists_reflection H 0
    have ht1 : t • X.vert 1 = X.vert (-1) := by
      have := htm 1
      simpa using this
    have hQ : X.Q (-1) = conjSub t (X.Q 1) := X.Q_smul X ht1
    have hZ : conjSub t (X.Z 0) = X.Z 0 := X.Z_normal 0 t ht.1
    rw [hQ, ← hZ]
    exact conjSub_mono t hZQ1
  obtain ⟨d, hd⟩ := X.exists_hasB H 0
  have hbnd := X.hasB_zero_bounds H hd
  have hG2 : X.Z 0 ≤ X.Gi 2 :=
    hZQ1.trans ((X.Q_le_Gi_adj 1).trans (by simpa using inf_le_right))
  have hGm2 : X.Z 0 ≤ X.Gi (-2) :=
    hZQm1.trans ((X.Q_le_Gi_adj (-1)).trans (by simpa using inf_le_left))
  have hmem2 : (2 : ℤ) ∈ X.fixSet (X.Z 0) := (X.mem_fixSet_iff_le_Gi _ 2).mpr hG2
  have hmemm2 : (-2 : ℤ) ∈ X.fixSet (X.Z 0) := (X.mem_fixSet_iff_le_Gi _ (-2)).mpr hGm2
  rw [X.fixSet_Z 0 hd] at hmem2 hmemm2
  rw [Set.mem_Icc] at hmem2 hmemm2
  have hd2 : 2 ≤ d := by omega
  have hd3 : d ≤ 3 := by omega
  refine ⟨le_inf hZQm1 hZQ1, ?_, ?_⟩
  · rcases (show d = 2 ∨ d = 3 by omega) with rfl | rfl
    · exact Or.inr hd
    · exact Or.inl hd
  · intro h3
    have hfix3 : X.fixSet (X.Z 0) = Set.Icc (-3 : ℤ) 3 := by
      rw [X.fixSet_Z 0 h3]
      norm_num
    have hle : X.Z 0 ≤ X.arcStab (-3) 3 := X.le_arcStab_of_fixSet (by simp [hfix3])
    have hZ2 : IsPGroup 2 (X.Z 0) := (pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)
    have hpc : X.Z 0 ≤ pCoreOf 2 (X.arcStab (-3) 3) :=
      X.le_pCoreOf_arcStab_r H hZ2 hle
    rw [← (X.caseA_3b A).2.2] at hpc
    exact le_antisymm (hpc.trans (X.caseA_3a A).1) (X.centerOf_L_le_Z hc 0)

private theorem pCoreOf_L_eq (X : Setup Γ G) (i : ℤ) : pCoreOf 2 (X.L i) = X.Q i :=
  (X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq

private theorem isL2Quot_L (X : Setup Γ G) (i : ℤ) :
    IsL2Quot (X.n i) (oTwoQuot ↥(X.L i)) :=
  (X.hyp.isLocL2_oTwoPrime (X.vert i)).quot

private theorem relCent_centerOf_L_eq (X : Setup Γ G) (H : X.Sec4Hyp 7 6) :
    relCent (X.Z 0) (centerOf (X.L 0)) (X.L 0) = centerOf (X.L 0) := by
  have hL : X.L 0 = ⁅X.L 0, X.L 0⁆ ⊔ X.Q 0 :=
    X.L_eq_commutator_sup_Q (n := X.n 0) 0 (H.two_le_n 0) (isL2Quot_L X 0)
  have hQE : X.Q 0 ≤ Subgroup.centralizer (X.Z 0 : Set G) :=
    Subgroup.le_centralizer_iff.mp ((X.Z_le_center 0).trans inf_le_right)
  have h := relCent_L_eq (X.Z_le_Q 0) hQE hL
  rwa [inf_eq_left.mpr (X.centerOf_L_le_Z H.char 0)] at h

private theorem K_le_normalizer_commutator_Z (X : Setup Γ G) (i j : ℤ) :
    X.K ≤ Subgroup.normalizer ((⁅X.Z i, X.Z j⁆ : Subgroup G) : Set G) :=
  fun k hk => by
    rw [mem_normalizer_iff_conjSub, ← conjSub_commutator, X.Z_normal i k (X.K_le_Gi i hk),
      X.Z_normal j k (X.K_le_Gi j hk)]

private theorem commutator_Z_zero_Z_neg_two_le (X : Setup Γ G)
    (hb : X.HasB 0 2) : ⁅X.Z 0, X.Z (-2)⁆ ≤ X.Z 0 ⊓ X.Z (-2) := by
  have hb2 : X.HasB (-2) 2 :=
    (X.hasB_iff_of_even (i := (-2)) (j := 0) (by norm_num [Even]) 2).mpr hb
  exact F7.commutator_le_inf_of_normalizes
    (fun x hx => mem_normalizer_iff_conjSub.mpr
      (X.Z_normal (-2) x (hb.Z_le_Gi (j := -2) (by norm_num) hx)))
    (fun y hy => mem_normalizer_iff_conjSub.mpr
      (X.Z_normal 0 y (hb2.Z_le_Gi (j := 0) (by norm_num) hy)))

private theorem commutator_Z_zero_Z_neg_two_le_arc (X : Setup Γ G)
    (hb : X.HasB 0 2) :
    ⁅X.Z 0, X.Z (-2)⁆ ≤ X.arcStab (-4) 2 := by
  have hb2 : X.HasB (-2) 2 :=
    (X.hasB_iff_of_even (i := (-2)) (j := 0) (by norm_num [Even]) 2).mpr hb
  have hle := X.commutator_Z_zero_Z_neg_two_le hb
  refine X.le_arcStab_of_fixSet ?_
  intro j hj
  rw [Set.mem_Icc] at hj
  rw [X.mem_fixSet_iff_le_Gi]
  by_cases h : j ≤ -2
  · exact (hle.trans inf_le_right).trans (hb2.Z_le_Gi (by omega))
  · exact (hle.trans inf_le_left).trans (hb.Z_le_Gi (by omega))

private theorem commutator_Z_zero_Z_neg_two_le_pCore (X : Setup Γ G) (H : X.Sec4Hyp 7 6)
    (hb : X.HasB 0 2) :
    ⁅X.Z 0, X.Z (-2)⁆ ≤ pCoreOf 2 (X.arcStab (-4) 2) := by
  have hle : ⁅X.Z 0, X.Z (-2)⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_neg_two_le hb).trans inf_le_left
  have h2 : IsPGroup 2 ↥(⁅X.Z 0, X.Z (-2)⁆) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le (hle.trans (X.Z_le_Q 0))
  exact X.le_pCoreOf_arcStab_r H h2
    (X.commutator_Z_zero_Z_neg_two_le_arc hb)

private theorem isElemAbelian_commutator_Z_zero (X : Setup Γ G) (H : X.Sec4Hyp 7 6)
    (hb : X.HasB 0 2) : IsElemAbelian 2 ⁅X.Z 0, X.Z (-2)⁆ := by
  have hpc := X.isElemAbelian_pCoreOf_arcStab_r H (-4)
  norm_num at hpc
  exact hpc.mono (X.commutator_Z_zero_Z_neg_two_le_pCore H hb)

private theorem edgeSylow_neg_one_eq_Z_sup_Q (X : Setup Γ G)
    (hb : X.HasB 0 2) : X.edgeSylow (-1) = X.Z (-2) ⊔ X.Q 0 := by
  have hb2 : X.HasB (-2) 2 :=
    (X.hasB_iff_of_even (i := (-2)) (j := 0) (by norm_num [Even]) 2).mpr hb
  have hneg : ¬ X.Z (-2) ≤ X.Q 0 := by
    have := (X.not_Z_le_Q_edge hb2).1
    simpa using this
  have hA : X.Z (-2) ≤ X.edgeSylow (-1) := by
    refine (X.Z_le_Q_of_lt hb2 (j := -1) (by norm_num)).trans ?_
    simpa using X.Q_le_edgeSylow_left (-1)
  have h := X.sup_Q_eq_edgeSylow_of_gen (-1)
    (inf_le_left.trans (K_le_normalizer_Z X (-2))) hA hneg
  simpa using h.symm

private theorem edgeSylow_zero_eq_Z_sup_Q (X : Setup Γ G)
    (hb : X.HasB 0 2) : X.edgeSylow 0 = X.Z 2 ⊔ X.Q 0 := by
  have hb2 : X.HasB 2 2 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num [Even]) 2).mpr hb
  have hneg : ¬ X.Z 2 ≤ X.Q 0 := by
    have := (X.not_Z_le_Q_edge hb2).2
    simpa using this
  have hA : X.Z 2 ≤ X.edgeSylow 0 :=
    (X.Z_le_Q_of_lt hb2 (j := 1) (by norm_num)).trans (X.Q_le_edgeSylow 0)
  have h := X.sup_Q_eq_edgeSylow_of_left_gen 0
    (inf_le_left.trans (K_le_normalizer_Z X 2)) hA hneg
  simpa using h.symm

private theorem commutator_Z_zero_edgeSylow_neg_one (X : Setup Γ G)
    (hb : X.HasB 0 2) :
    ⁅X.Z 0, X.edgeSylow (-1)⁆ = ⁅X.Z 0, X.Z (-2)⁆ := by
  have hb2 : X.HasB (-2) 2 :=
    (X.hasB_iff_of_even (i := (-2)) (j := 0) (by norm_num [Even]) 2).mpr hb
  have hZnegG : X.Z (-2) ≤ X.Gi 0 := hb2.Z_le_Gi (j := 0) (by norm_num)
  have hleA : X.Z (-2) ≤ X.edgeSylow (-1) :=
    (X.Z_le_Q_of_lt hb2 (j := -1) (by norm_num)).trans (X.Q_le_edgeSylow_left (-1))
  refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl hleA)
  rw [X.edgeSylow_neg_one_eq_Z_sup_Q hb, Subgroup.commutator_le]
  intro z hz t ht
  obtain ⟨y, hy, q, hq, rfl⟩ := Set.mem_mul.mp
    ((Subgroup.coe_mul_of_left_le_normalizer_right (X.Z (-2)) (X.Q 0)
      (hZnegG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))).subset ht)
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hq1 : ⁅z, q⁆ = 1 := commutator_eq_one_of_mem_Z_Q X hz hq
  rw [hq1, mul_one]
  simpa using Subgroup.commutator_mem_commutator hz hy

private theorem commutator_Z_zero_edgeSylow_zero (X : Setup Γ G)
    (hb : X.HasB 0 2) :
    ⁅X.Z 0, X.edgeSylow 0⁆ = ⁅X.Z 0, X.Z 2⁆ := by
  have hb2 : X.HasB 2 2 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num [Even]) 2).mpr hb
  have hZ2G : X.Z 2 ≤ X.Gi 0 := hb2.Z_le_Gi (j := 0) (by norm_num)
  have hleA : X.Z 2 ≤ X.edgeSylow 0 :=
    (X.Z_le_Q_of_lt hb2 (j := 1) (by norm_num)).trans (by simpa using X.Q_le_edgeSylow 0)
  refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl hleA)
  rw [X.edgeSylow_zero_eq_Z_sup_Q hb, Subgroup.commutator_le]
  intro z hz t ht
  obtain ⟨y, hy, q, hq, rfl⟩ := Set.mem_mul.mp
    ((Subgroup.coe_mul_of_left_le_normalizer_right (X.Z 2) (X.Q 0)
      (hZ2G.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))).subset ht)
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hq1 : ⁅z, q⁆ = 1 := commutator_eq_one_of_mem_Z_Q X hz hq
  rw [hq1, mul_one]
  simpa using Subgroup.commutator_mem_commutator hz hy

private theorem Z_zero_le_normalizer_centerOf_L (X : Setup Γ G) :
    X.Z 0 ≤ Subgroup.normalizer (centerOf (X.L 0) : Set G) :=
  (X.Z_le_Gi 0).trans (X.Gi_le_normalizer_centerOf_L 0)

private theorem relIndex_inf_le_of_le_edgeSylow {A B S : Subgroup G} {m : ℕ}
    (hA : A ≤ S) (h4 : B.relIndex S = 2 ^ m) : (A ⊓ B).relIndex A ≤ 2 ^ m := by
  rw [Subgroup.inf_relIndex_left]
  exact (Subgroup.relIndex_le_of_le_right hA (by rw [h4]; exact pow_ne_zero _ (by norm_num))).trans
    h4.le

private theorem inf_Q_neg_two_le_relCent (X : Setup Γ G)
    (hb : X.HasB 0 2) :
    X.Z 0 ⊓ X.Q (-2) ≤ relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow (-1)) := by
  intro z hz
  obtain ⟨hzZ, hzQ⟩ := Subgroup.mem_inf.mp hz
  rw [mem_relCent (X.Z_zero_le_normalizer_centerOf_L)]
  refine ⟨hzZ, ?_⟩
  intro a ha
  have hsup := X.edgeSylow_neg_one_eq_Z_sup_Q hb
  have hb2 : X.HasB (-2) 2 :=
    (X.hasB_iff_of_even (i := (-2)) (j := 0) (by norm_num [Even]) 2).mpr hb
  have hZnegG : X.Z (-2) ≤ X.Gi 0 := hb2.Z_le_Gi (j := 0) (by norm_num)
  have ha' : a ∈ X.Z (-2) ⊔ X.Q 0 := hsup ▸ ha
  obtain ⟨y, hy, q, hq, rfl⟩ := Set.mem_mul.mp
    ((Subgroup.coe_mul_of_left_le_normalizer_right (X.Z (-2)) (X.Q 0)
      (hZnegG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))).subset ha')
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hq1 : ⁅z, q⁆ = 1 := commutator_eq_one_of_mem_Z_Q X hzZ hq
  have hy1 : ⁅z, y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp ((X.Z_le_center (-2)) hy).2 z hzQ)
  rw [hq1, hy1]
  simpa using (centerOf (X.L 0)).one_mem

private theorem inf_Q_two_le_relCent (X : Setup Γ G)
    (hb : X.HasB 0 2) :
    X.Z 0 ⊓ X.Q 2 ≤ relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow 0) := by
  intro z hz
  obtain ⟨hzZ, hzQ⟩ := Subgroup.mem_inf.mp hz
  rw [mem_relCent (X.Z_zero_le_normalizer_centerOf_L)]
  refine ⟨hzZ, ?_⟩
  intro a ha
  have hsup := X.edgeSylow_zero_eq_Z_sup_Q hb
  have hb2 : X.HasB 2 2 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num [Even]) 2).mpr hb
  have hZ2G : X.Z 2 ≤ X.Gi 0 := hb2.Z_le_Gi (j := 0) (by norm_num)
  have ha' : a ∈ X.Z 2 ⊔ X.Q 0 := hsup ▸ ha
  obtain ⟨y, hy, q, hq, rfl⟩ := Set.mem_mul.mp
    ((Subgroup.coe_mul_of_left_le_normalizer_right (X.Z 2) (X.Q 0)
      (hZ2G.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))).subset ha')
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hq1 : ⁅z, q⁆ = 1 := commutator_eq_one_of_mem_Z_Q X hzZ hq
  have hy1 : ⁅z, y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp ((X.Z_le_center 2) hy).2 z hzQ)
  rw [hq1, hy1]
  simpa using (centerOf (X.L 0)).one_mem

private theorem relIndex_inf_Q_neg_two_le (X : Setup Γ G)
    (hb : X.HasB 0 2) : (X.Z 0 ⊓ X.Q (-2)).relIndex (X.Z 0) ≤ 2 ^ X.n (-2) := by
  have hA : X.Z 0 ≤ X.edgeSylow (-2) :=
    (X.Z_le_Q_of_lt hb (j := -1) (by norm_num)).trans
      (by simpa using X.Q_le_edgeSylow (-2))
  have h4 : (X.Q (-2)).relIndex (X.edgeSylow (-2)) = 2 ^ X.n (-2) :=
    X.relIndex_Q_edgeSylow (-2)
  exact relIndex_inf_le_of_le_edgeSylow hA h4

private theorem relIndex_inf_Q_two_le (X : Setup Γ G)
    (hb : X.HasB 0 2) : (X.Z 0 ⊓ X.Q 2).relIndex (X.Z 0) ≤ 2 ^ X.n 2 := by
  have hA : X.Z 0 ≤ X.edgeSylow 1 :=
    (X.Z_le_Q_of_lt hb (j := 1) (by norm_num)).trans (X.Q_le_edgeSylow_left 1)
  have h4 : (X.Q 2).relIndex (X.edgeSylow 1) = 2 ^ X.n 2 := by
    simpa using X.relIndex_Q_succ_edgeSylow (1 : ℤ)
  exact relIndex_inf_le_of_le_edgeSylow hA h4

private theorem relCent_neg_one_relIndex_le (X : Setup Γ G)
    (hb : X.HasB 0 2) :
    (relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow (-1))).relIndex (X.Z 0) ≤
      2 ^ X.n (-2) := by
  have hle := X.inf_Q_neg_two_le_relCent hb
  have hdvd : (relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow (-1))).relIndex (X.Z 0) ∣
      (X.Z 0 ⊓ X.Q (-2)).relIndex (X.Z 0) :=
    Subgroup.relIndex_dvd_of_le_left (L := X.Z 0) hle
  haveI hZfin : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (X.Z_le_Gi 0)
  have hpos : 0 < (X.Z 0 ⊓ X.Q (-2)).relIndex (X.Z 0) := Nat.card_pos
  exact (Nat.le_of_dvd hpos hdvd).trans (X.relIndex_inf_Q_neg_two_le hb)

private theorem relCent_zero_relIndex_le (X : Setup Γ G)
    (hb : X.HasB 0 2) :
    (relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow 0)).relIndex (X.Z 0) ≤
      2 ^ X.n 2 := by
  have hle := X.inf_Q_two_le_relCent hb
  have hdvd : (relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow 0)).relIndex (X.Z 0) ∣
      (X.Z 0 ⊓ X.Q 2).relIndex (X.Z 0) :=
    Subgroup.relIndex_dvd_of_le_left (L := X.Z 0) hle
  haveI hZfin : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (X.Z_le_Gi 0)
  have hpos : 0 < (X.Z 0 ⊓ X.Q 2).relIndex (X.Z 0) := Nat.card_pos
  exact (Nat.le_of_dvd hpos hdvd).trans (X.relIndex_inf_Q_two_le hb)

private theorem isElemSec_centerOf_L_Z (X : Setup Γ G) (H : X.Sec4Hyp 7 6)
    (hb : X.HasB 0 2) : IsElemSec (centerOf (X.L 0)) (X.Z 0) := by
  have hP : IsSylowTwoOf (X.Z (-2) ⊔ X.Q 0) (X.L 0) := by
    rw [← X.edgeSylow_neg_one_eq_Z_sup_Q hb]
    exact X.isSylowTwoOf_edgeSylow_L_succ (-1)
  have hRle : ⁅X.Z (-2), X.Z 0⁆ ≤ X.Z 0 := by
    rw [Subgroup.commutator_comm]
    exact (X.commutator_Z_zero_Z_neg_two_le hb).trans inf_le_left
  have hRelem : IsElemAbelian 2 ⁅X.Z (-2), X.Z 0⁆ := by
    rw [Subgroup.commutator_comm]
    exact X.isElemAbelian_commutator_Z_zero H hb
  have hsq : ∀ x ∈ X.Z 0, x ^ 2 ∈ centerOf (X.L 0) :=
    X.sq_le_centerOf_L hP hRle hRelem
  have hZcomm : IsMulCommutative ↥(X.Z 0) :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (X.Z_commute 0 a.1 a.2 b.1 b.2))
  refine ⟨X.centerOf_L_le_Z H.char 0, ?_, hsq⟩
  rw [Subgroup.commutator_self_eq_bot_iff.mpr hZcomm]
  exact bot_le

private theorem commutator_Z_zero_Z_two_le (X : Setup Γ G)
    (hb : X.HasB 0 2) : ⁅X.Z 0, X.Z 2⁆ ≤ X.Z 0 ⊓ X.Z 2 := by
  have hb2 : X.HasB 2 2 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num [Even]) 2).mpr hb
  exact F7.commutator_le_inf_of_normalizes
    (fun x hx => mem_normalizer_iff_conjSub.mpr
      (X.Z_normal 2 x (hb.Z_le_Gi (j := 2) (by norm_num) hx)))
    (fun y hy => mem_normalizer_iff_conjSub.mpr
      (X.Z_normal 0 y (hb2.Z_le_Gi (j := 0) (by norm_num) hy)))

private theorem commutator_Z_zero_Z_two_le_arc (X : Setup Γ G)
    (hb : X.HasB 0 2) :
    ⁅X.Z 0, X.Z 2⁆ ≤ X.arcStab (-2) 4 := by
  have hb2 : X.HasB 2 2 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num [Even]) 2).mpr hb
  have hle := X.commutator_Z_zero_Z_two_le hb
  refine X.le_arcStab_of_fixSet ?_
  intro j hj
  rw [Set.mem_Icc] at hj
  rw [X.mem_fixSet_iff_le_Gi]
  by_cases h : j ≤ 2
  · exact (hle.trans inf_le_left).trans (hb.Z_le_Gi (by omega))
  · exact (hle.trans inf_le_right).trans (hb2.Z_le_Gi (by omega))

private theorem commutator_Z_zero_Z_two_le_pCore (X : Setup Γ G) (H : X.Sec4Hyp 7 6)
    (hb : X.HasB 0 2) :
    ⁅X.Z 0, X.Z 2⁆ ≤ pCoreOf 2 (X.arcStab (-2) 4) := by
  have hle : ⁅X.Z 0, X.Z 2⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_two_le hb).trans inf_le_left
  have h2 : IsPGroup 2 ↥(⁅X.Z 0, X.Z 2⁆) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le (hle.trans (X.Z_le_Q 0))
  exact X.le_pCoreOf_arcStab_r H h2
    (X.commutator_Z_zero_Z_two_le_arc hb)

private theorem centerOf_L_zero_le_Q_neg_two (X : Setup Γ G)
    (hb : X.HasB 0 2) (hXm_ne : ⁅X.Z 0, X.Z (-2)⁆ ≠ ⊥)
    (hCLQm1 : centerOf (X.L 0) ≤ X.Q (-1)) : centerOf (X.L 0) ≤ X.Q (-2) := by
  have hb2 : X.HasB (-2) 2 :=
    (X.hasB_iff_of_even (i := (-2)) (j := 0) (by norm_num [Even]) 2).mpr hb
  have hCLedge : centerOf (X.L 0) ≤ X.edgeSylow (-2) :=
    hCLQm1.trans (by simpa using X.Q_le_edgeSylow (-2))
  by_contra hnot
  have hsup : centerOf (X.L 0) ⊔ X.Q (-2) = X.edgeSylow (-2) :=
    X.sup_Q_eq_edgeSylow_of_left_gen (-2)
      (inf_le_left.trans ((X.K_le_Gi 0).trans (X.Gi_le_normalizer_centerOf_L 0)))
      hCLedge hnot
  have hNe : X.edgeSylow (-2) ≤ Subgroup.normalizer (X.Q (-2) : Set G) :=
    ((X.isSylowTwoOf_edgeSylow (-2)).1.trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-2)))
  have hQm1le : X.Q (-1) ≤ centerOf (X.L 0) ⊔ X.Q (-2) := by
    have h : X.Q (-1) ≤ X.edgeSylow (-2) := by simpa using X.Q_le_edgeSylow (-2)
    rwa [← hsup] at h
  have hXm0 : ⁅X.Z 0, X.Z (-2)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    have hxQ : x ∈ X.Q (-1) := X.Z_le_Q_of_lt hb (j := -1) (by norm_num) hx
    have hxsup : x ∈ centerOf (X.L 0) ⊔ X.Q (-2) := hQm1le hxQ
    obtain ⟨z, hz, b, hb', rfl⟩ := Set.mem_mul.mp
      ((Subgroup.coe_mul_of_left_le_normalizer_right (centerOf (X.L 0)) (X.Q (-2))
        ((le_sup_left.trans hsup.le).trans hNe)).subset hxsup)
    have hyQ : y ∈ X.Q (-1) := X.Z_le_Q_of_lt hb2 (j := -1) (by norm_num) hy
    have hyL : y ∈ X.L 0 :=
      le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi (-1)))
        ((X.Q_le_Gi_adj (-1)).trans inf_le_right) hyQ
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hby : ⁅b, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp ((X.Z_le_center (-2)) hy).2 b hb')
    have hzy : ⁅z, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 y hyL).symm
    rw [hby, hzy]
    simp
  exact hXm_ne hXm0

private theorem centerOf_L_eq_R (X : Setup Γ G)
    (A : X.CaseA) (hb : X.HasB 0 2)
    (hXm_ne : ⁅X.Z 0, X.Z (-2)⁆ ≠ ⊥) :
    centerOf (X.L 0) = ⁅X.Z (-1), X.Z 1⁆ := by
  have H := A.hyp
  have hc := H.char
  have hCLQ1 : centerOf (X.L 0) ≤ X.Q 1 := (X.centerOf_L_le_Q_adj hc 0).2
  have hCLQm1 : centerOf (X.L 0) ≤ X.Q (-1) := by
    obtain ⟨t, ht, htm⟩ := X.exists_reflection H 0
    have ht1 : t • X.vert 1 = X.vert (-1) := by simpa using htm 1
    have hQ : X.Q (-1) = conjSub t (X.Q 1) := X.Q_smul X ht1
    have hC : conjSub t (centerOf (X.L 0)) = centerOf (X.L 0) := by
      rw [← centerOf_conjSub, ← X.L_smul X (MulAction.mem_stabilizer_iff.mp ht.1)]
    rw [hQ, ← hC]
    exact conjSub_mono t hCLQ1
  have hCLQ0 : centerOf (X.L 0) ≤ X.Q 0 := (X.centerOf_L_le_Z hc 0).trans (X.Z_le_Q 0)
  have hCLQm2 : centerOf (X.L 0) ≤ X.Q (-2) :=
    X.centerOf_L_zero_le_Q_neg_two hb hXm_ne hCLQm1
  have hCLQ2 : centerOf (X.L 0) ≤ X.Q 2 := by
    obtain ⟨t, ht, htm⟩ := X.exists_reflection H 0
    have ht2 : t • X.vert (-2) = X.vert 2 := by
      have h := htm (-2)
      simpa using h
    have hQ : X.Q 2 = conjSub t (X.Q (-2)) := X.Q_smul X ht2
    have hC : conjSub t (centerOf (X.L 0)) = centerOf (X.L 0) := by
      rw [← centerOf_conjSub, ← X.L_smul X (MulAction.mem_stabilizer_iff.mp ht.1)]
    rw [hQ, ← hC]
    exact conjSub_mono t hCLQm2
  have hCLarc : centerOf (X.L 0) ≤ X.arcStab (-3) 3 := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    rw [X.mem_fixSet_iff_le_Gi]
    interval_cases j
    · exact hCLQm2.trans (by simpa using (X.Q_le_Gi_adj (-2)).trans inf_le_left)
    · exact hCLQm1.trans (by simpa using (X.Q_le_Gi_adj (-1)).trans inf_le_left)
    · exact hCLQ0.trans (by simpa using (X.Q_le_Gi_adj 0).trans inf_le_left)
    · exact hCLQm1.trans (by simpa using (X.Q_le_Gi_adj (-1)).trans inf_le_right)
    · exact hCLQ0.trans (by simpa using (X.Q_le_Gi_adj 0).trans inf_le_right)
    · exact hCLQ1.trans (by simpa using (X.Q_le_Gi_adj 1).trans inf_le_right)
    · exact hCLQ2.trans (by simpa using (X.Q_le_Gi_adj 2).trans inf_le_right)
  have hCL2 : IsPGroup 2 ↥(centerOf (X.L 0)) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le hCLQ0
  have hCLp : centerOf (X.L 0) ≤ pCoreOf 2 (X.arcStab (-3) 3) :=
    X.le_pCoreOf_arcStab_r H hCL2 hCLarc
  have hR : ⁅X.Z (-1), X.Z 1⁆ = pCoreOf 2 (X.arcStab (-3) 3) := (X.caseA_3b A).2.2
  rw [← hR] at hCLp
  exact le_antisymm hCLp (X.caseA_3a A).1

private theorem commutator_Z_zero_Z_neg_two_ne_bot
    (X : Setup Γ G) (H : X.Sec4Hyp 7 6) (hb : X.HasB 0 2)
    (hntq : NatQuot (X.L 0) (X.Z 0) (centerOf (X.L 0)) (X.n 0)) :
    ⁅X.Z 0, X.Z (-2)⁆ ≠ ⊥ := by
  intro hbot
  have hA : IsSylowTwoOf (X.edgeSylow (-1)) (X.L 0) := by
    simpa using X.isSylowTwoOf_edgeSylow_L_succ (-1)
  have hcomm := hntq.comm_eq (X.edgeSylow (-1)) hA
  rw [X.commutator_Z_zero_edgeSylow_neg_one hb, hbot, bot_sup_eq] at hcomm
  have hl := hntq.line (X.edgeSylow (-1)) hA
  rw [← hcomm] at hl
  rw [Subgroup.relIndex_self] at hl
  exact (Nat.one_lt_two_pow (by have := H.two_le_n 0; omega)).ne' hl.symm

private theorem commutator_Z_zero_Z_two_ne_bot
    (X : Setup Γ G) (H : X.Sec4Hyp 7 6) (hb : X.HasB 0 2)
    (hntq : NatQuot (X.L 0) (X.Z 0) (centerOf (X.L 0)) (X.n 0)) :
    ⁅X.Z 0, X.Z 2⁆ ≠ ⊥ := by
  intro hbot
  have hA : IsSylowTwoOf (X.edgeSylow 0) (X.L 0) := X.isSylowTwoOf_edgeSylow_L 0
  have hcomm := hntq.comm_eq (X.edgeSylow 0) hA
  rw [X.commutator_Z_zero_edgeSylow_zero hb, hbot, bot_sup_eq] at hcomm
  have hl := hntq.line (X.edgeSylow 0) hA
  rw [← hcomm] at hl
  rw [Subgroup.relIndex_self] at hl
  exact (Nat.one_lt_two_pow (by have := H.two_le_n 0; omega)).ne' hl.symm

private theorem commutator_Z_zero_inf (X : Setup Γ G)
    (H : X.Sec4Hyp 7 6) (hb : X.HasB 0 2) :
    ⁅X.Z 0, X.Z (-2)⁆ ⊓ ⁅X.Z 0, X.Z 2⁆ = ⊥ := by
  by_contra hne
  have hU2 : IsPGroup 2 ↥(⁅X.Z 0, X.Z (-2)⁆ ⊓ ⁅X.Z 0, X.Z 2⁆) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le
      ((inf_le_left.trans ((X.commutator_Z_zero_Z_neg_two_le hb).trans inf_le_left)).trans
        (X.Z_le_Q 0))
  have hfix : ⁅X.Z 0, X.Z (-2)⁆ ⊓ ⁅X.Z 0, X.Z 2⁆ ≤
      X.arcStab (-4) ((-4 : ℤ) + (8 : ℕ)) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    rw [X.mem_fixSet_iff_le_Gi]
    by_cases h : j ≤ 2
    · exact (inf_le_left.trans (X.commutator_Z_zero_Z_neg_two_le_arc hb)).trans
        (X.arcStab_le_Gi_of_between (by omega) h)
    · exact (inf_le_right.trans (X.commutator_Z_zero_Z_two_le_arc hb)).trans
        (X.arcStab_le_Gi_of_between (by omega) (by omega : j ≤ 4))
  have := X.le_r_of_fixes H hU2 hne hfix
  norm_num at this

private theorem edgeSylow_one_eq_Z_sup_Q (X : Setup Γ G)
    (hb : X.HasB 0 2) : X.edgeSylow 1 = X.Z 0 ⊔ X.Q 2 := by
  have hneg : ¬ X.Z 0 ≤ X.Q 2 := by
    have := (X.not_Z_le_Q_edge hb).1
    simpa using this
  have hA : X.Z 0 ≤ X.edgeSylow 1 :=
    (X.Z_le_Q_of_lt hb (j := 1) (by norm_num)).trans (X.Q_le_edgeSylow_left 1)
  have h := X.sup_Q_eq_edgeSylow_of_gen 1 (inf_le_left.trans (K_le_normalizer_Z X 0)) hA hneg
  simpa using h.symm

private theorem commutator_Z_zero_Z_two_le_centerOf_L_one (X : Setup Γ G) (H : X.Sec4Hyp 7 6)
    (hb : X.HasB 0 2) : ⁅X.Z 0, X.Z 2⁆ ≤ centerOf (X.L 1) := by
  have hle := X.commutator_Z_zero_Z_two_le hb
  refine X.le_centerOf_L H.char 1 ?_ ?_ ?_
  · exact (hle.trans inf_le_left).trans (hb.Z_le_Gi (j := 1) (by norm_num))
  · have h0 : X.edgeSylow (1 - 1) = X.Z 2 ⊔ X.Q 0 := by
      simpa using X.edgeSylow_zero_eq_Z_sup_Q hb
    rw [h0]
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((X.Z_commute 2) y hy z ((hle.trans inf_le_right) hz)).symm
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp
        ((X.Z_le_center 0) ((hle.trans inf_le_left) hz)).2 q hq).symm
  · rw [X.edgeSylow_one_eq_Z_sup_Q hb]
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((X.Z_commute 0) y hy z ((hle.trans inf_le_left) hz)).symm
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp
        ((X.Z_le_center 2) ((hle.trans inf_le_right) hz)).2 q hq).symm

private theorem commutator_Z_zero_Z_neg_two_le_centerOf_L_neg_one (X : Setup Γ G)
    (H : X.Sec4Hyp 7 6) (hb : X.HasB 0 2) : ⁅X.Z 0, X.Z (-2)⁆ ≤ centerOf (X.L (-1)) := by
  have hb2 : X.HasB (-2) 2 :=
    (X.hasB_iff_of_even (i := (-2)) (j := 0) (by norm_num [Even]) 2).mpr hb
  have hle := X.commutator_Z_zero_Z_neg_two_le hb
  refine X.le_centerOf_L H.char (-1) ?_ ?_ ?_
  · exact (hle.trans inf_le_right).trans (hb2.Z_le_Gi (j := -1) (by norm_num))
  ·
    have hneg : ¬ X.Z 0 ≤ X.Q (-2) := by
      have := (X.not_Z_le_Q_edge hb).2
      simpa using this
    have hA : X.Z 0 ≤ X.edgeSylow (-2) :=
      (X.Z_le_Q_of_lt hb (j := -1) (by norm_num)).trans (by simpa using X.Q_le_edgeSylow (-2))
    have hsup : X.edgeSylow (-1 - 1) = X.Z 0 ⊔ X.Q (-2) := by
      have h := X.sup_Q_eq_edgeSylow_of_left_gen (-2)
        (inf_le_left.trans (K_le_normalizer_Z X 0)) hA hneg
      simpa using h.symm
    rw [hsup]
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((X.Z_commute 0) y hy z ((hle.trans inf_le_left) hz)).symm
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp
        ((X.Z_le_center (-2)) ((hle.trans inf_le_right) hz)).2 q hq).symm
  · rw [X.edgeSylow_neg_one_eq_Z_sup_Q hb]
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((X.Z_commute (-2)) y hy z ((hle.trans inf_le_right) hz)).symm
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp
        ((X.Z_le_center 0) ((hle.trans inf_le_left) hz)).2 q hq).symm

private theorem centerOf_L_one_le_commutator_Z_zero_Z_two (X : Setup Γ G) (A : X.CaseA)
    (hXp_eq : ⁅X.Z 0, X.Z 2⁆ = pCoreOf 2 (X.arcStab (-2) 4)) :
    centerOf (X.L 1) ≤ ⁅X.Z 0, X.Z 2⁆ := by
  have H := A.hyp
  have hc := H.char
  have hb1 : X.HasB (-1) 2 :=
    (X.hasB_iff_of_even (i := (-1)) (j := 1) (by norm_num [Even]) 2).mpr A.b₁
  have hQm1 : centerOf (X.L 1) ≤ X.Q (-1) := by
    by_contra hnot
    have hCLZ : centerOf (X.L 1) ≤ X.Z 1 := X.centerOf_L_le_Z hc 1
    have hCLedge : centerOf (X.L 1) ≤ X.edgeSylow (-1) :=
      (hCLZ.trans (X.Z_le_Q_of_lt A.b₁ (j := 0) (by norm_num))).trans
        (by simpa using X.Q_le_edgeSylow (-1))
    have hsup : centerOf (X.L 1) ⊔ X.Q (-1) = X.edgeSylow (-1) :=
      X.sup_Q_eq_edgeSylow_of_left_gen (-1)
        (inf_le_left.trans ((X.K_le_Gi 1).trans (X.Gi_le_normalizer_centerOf_L 1)))
        hCLedge hnot
    have hNe : X.edgeSylow (-1) ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
      ((X.isSylowTwoOf_edgeSylow (-1)).1.trans inf_le_left).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)))
    have hZ1le : X.Z 1 ≤ centerOf (X.L 1) ⊔ X.Q (-1) := by
      have h := (X.caseA_pos A).2
      exact (le_sup_left.trans (le_of_eq h)).trans (le_of_eq hsup.symm)
    have hR1 : ⁅X.Z (-1), X.Z 1⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro a ha b hb1'
      have hbsup : b ∈ centerOf (X.L 1) ⊔ X.Q (-1) := hZ1le hb1'
      obtain ⟨z, hz, q, hq, rfl⟩ := Set.mem_mul.mp
        ((Subgroup.coe_mul_of_left_le_normalizer_right (centerOf (X.L 1)) (X.Q (-1))
          ((le_sup_left.trans hsup.le).trans hNe)).subset hbsup)
      have haQ : a ∈ X.Q 0 := X.Z_le_Q_of_lt hb1 (j := 0) (by norm_num) ha
      have haL : a ∈ X.L 1 :=
        le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 0))
          ((X.Q_le_Gi_adj 0).trans inf_le_right) haQ
      have h1 : ⁅a, z⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 a haL)
      have h2 : ⁅a, q⁆ = 1 := commutator_eq_one_of_mem_Z_Q X ha hq
      rw [commutatorElement_mul_right_eq_mul_conj, h1, h2]
      simp
    exact A.R_ne (le_bot_iff.mp hR1)
  have hQ3 : centerOf (X.L 1) ≤ X.Q 3 := by
    obtain ⟨t, ht, htm⟩ := X.exists_reflection H 1
    have ht1 : t • X.vert (-1) = X.vert 3 := by
      have h := htm (-2)
      simpa using h
    have hQ : X.Q 3 = conjSub t (X.Q (-1)) := X.Q_smul X ht1
    have hC : centerOf (X.L 1) = conjSub t (centerOf (X.L 1)) := by
      rw [← centerOf_conjSub, ← X.L_smul X (MulAction.mem_stabilizer_iff.mp ht.1)]
    have h := conjSub_mono t hQm1
    rw [← hC] at h
    rw [hQ]
    exact h
  have hCLQ0 : centerOf (X.L 1) ≤ X.Q 0 :=
    (X.centerOf_L_le_Z hc 1).trans (X.Z_le_Q_of_lt A.b₁ (j := 0) (by norm_num))
  have hCLQ2 : centerOf (X.L 1) ≤ X.Q 2 :=
    (X.centerOf_L_le_Z hc 1).trans (X.Z_le_Q_of_lt A.b₁ (j := 2) (by norm_num))
  have harc : centerOf (X.L 1) ≤ X.arcStab (-2) 4 := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    rw [X.mem_fixSet_iff_le_Gi]
    interval_cases j
    · exact hQm1.trans (by simpa using (X.Q_le_Gi_adj (-1)).trans inf_le_left)
    · exact hCLQ0.trans (by simpa using (X.Q_le_Gi_adj 0).trans inf_le_left)
    · exact hQm1.trans (by simpa using (X.Q_le_Gi_adj (-1)).trans inf_le_right)
    · exact hCLQ0.trans (by simpa using (X.Q_le_Gi_adj 0).trans inf_le_right)
    · exact hQ3.trans (by simpa using (X.Q_le_Gi_adj 3).trans inf_le_left)
    · exact hCLQ2.trans (by simpa using (X.Q_le_Gi_adj 2).trans inf_le_right)
    · exact hQ3.trans (by simpa using (X.Q_le_Gi_adj 3).trans inf_le_right)
  have h2 : IsPGroup 2 ↥(centerOf (X.L 1)) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le hCLQ0
  have h := X.le_pCoreOf_arcStab_r H h2 harc
  norm_num at h
  rwa [← hXp_eq] at h

private theorem centerOf_L_neg_one_le_commutator_Z_zero_Z_neg_two (X : Setup Γ G)
    (A : X.CaseA) (hXp_eq : ⁅X.Z 0, X.Z 2⁆ = pCoreOf 2 (X.arcStab (-2) 4)) :
    centerOf (X.L (-1)) ≤ ⁅X.Z 0, X.Z (-2)⁆ := by
  have H := A.hyp
  obtain ⟨t, ht, htm⟩ := X.exists_reflection H 0
  have ht1 : t • X.vert 1 = X.vert (-1) := by simpa using htm 1
  have ht2 : t • X.vert 2 = X.vert (-2) := by
    have h := htm 2
    simpa using h
  have hconj : centerOf (X.L (-1)) = conjSub t (centerOf (X.L 1)) := by
    rw [X.L_smul X ht1, centerOf_conjSub]
  have h := conjSub_mono t (X.centerOf_L_one_le_commutator_Z_zero_Z_two A hXp_eq)
  rw [← hconj] at h
  have hXpconj : conjSub t ⁅X.Z 0, X.Z 2⁆ = ⁅X.Z 0, X.Z (-2)⁆ := by
    rw [← conjSub_commutator, X.Z_normal 0 t ht.1, (X.Z_smul X ht2).symm]
  rwa [hXpconj] at h

private theorem L_eq_oTwoRes_sup (X : Setup Γ G) :
    X.L 0 = oTwoRes (X.L 0) ⊔ X.edgeSylow 0 := by
  haveI : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (X.L_le_Gi 0)
  have hP : IsSylowTwoOf (X.edgeSylow 0) (X.L 0) := X.isSylowTwoOf_edgeSylow_L 0
  have hP' : IsSylowTwoOf ((X.edgeSylow 0).subgroupOf (X.L 0)) ⊤ := by
    refine F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
    · exact hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
    · rw [show (⊤ : Subgroup ↥(X.L 0)) = (X.L 0).subgroupOf (X.L 0) from
        (Subgroup.subgroupOf_self _).symm]
      rw [Subgroup.relIndex_subgroupOf (le_rfl : X.L 0 ≤ X.L 0)]
      exact hP.2.2
  have hmain : (⊤ : Subgroup ↥(X.L 0)) ≤
      oTwoRes (⊤ : Subgroup ↥(X.L 0)) ⊔ (X.edgeSylow 0).subgroupOf (X.L 0) :=
    le_oTwoRes_sup_of_isSylowTwoOf hP'
  have hmap : (oTwoRes (⊤ : Subgroup ↥(X.L 0))).map (X.L 0).subtype = oTwoRes (X.L 0) := by
    rw [← oTwoRes_map (f := (X.L 0).subtype) (X := ⊤) (Subgroup.subtype_injective _),
      Subgroup.map_top, Subgroup.range_subtype]
  have htop : (⊤ : Subgroup ↥(X.L 0)).map (X.L 0).subtype = X.L 0 := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hPmap : ((X.edgeSylow 0).subgroupOf (X.L 0)).map (X.L 0).subtype = X.edgeSylow 0 := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP.1]
  have hmapmain := Subgroup.map_mono (f := (X.L 0).subtype) hmain
  rw [Subgroup.map_sup, hmap, hPmap, htop] at hmapmain
  exact le_antisymm hmapmain (sup_le (oTwoRes_le _) hP.1)

private theorem oTwoRes_commutator_le_Z (X : Setup Γ G)
    (hcon : ∀ y ∈ X.L 0, Odd (orderOf y) → ∀ e ∈ X.Q 0, ⁅e, y⁆ ∈ X.Z 0) :
    ∀ y ∈ oTwoRes (X.L 0), ∀ e ∈ X.Q 0, ⁅e, y⁆ ∈ X.Z 0 := by
  have hD : oTwoRes (X.L 0) ≤
      { carrier := {y : G | y ∈ X.Gi 0 ∧ ∀ e ∈ X.Q 0, ⁅e, y⁆ ∈ X.Z 0}
        one_mem' := ⟨(X.Gi 0).one_mem, fun e _ => by simp⟩
        mul_mem' := by
          rintro y z ⟨hyG, hy⟩ ⟨hzG, hz⟩
          refine ⟨(X.Gi 0).mul_mem hyG hzG, fun e he => ?_⟩
          rw [commutatorElement_mul_right_eq_mul_conj]
          have hz' : y * ⁅e, z⁆ * y⁻¹ ∈ X.Z 0 := by
            have h := mul_mem_conjSub (g := y) (H := X.Z 0) (hz e he)
            rwa [X.Z_normal 0 y hyG] at h
          rw [show ⁅e, y⁆ * y * ⁅e, z⁆ * y⁻¹ = ⁅e, y⁆ * (y * ⁅e, z⁆ * y⁻¹) from by group]
          exact (X.Z 0).mul_mem (hy e he) hz'
        inv_mem' := by
          rintro y ⟨hyG, hy⟩
          refine ⟨(X.Gi 0).inv_mem hyG, fun e he => ?_⟩
          rw [commutatorElement_inv_right]
          have hxe : ⁅y, e⁆ ∈ X.Z 0 := by
            have h := (X.Z 0).inv_mem (hy e he)
            rwa [commutatorElement_inv] at h
          have h := mul_mem_conjSub (g := y⁻¹) (H := X.Z 0) hxe
          rw [X.Z_normal 0 y⁻¹ ((X.Gi 0).inv_mem hyG)] at h
          simpa using h } := by
    rw [oTwoRes]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxL, m, hm, hx1⟩
    refine ⟨X.L_le_Gi 0 hxL, fun e he => hcon x hxL ?_ e he⟩
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hx1)
  intro y hy e he
  exact (hD hy).2 e he

private theorem L_zero_le_normalizer_Z_one_sup (X : Setup Γ G) (A : X.CaseA)
    (hb : X.HasB 0 2)
    (hcon : ∀ y ∈ X.L 0, Odd (orderOf y) → ∀ e ∈ X.Q 0, ⁅e, y⁆ ∈ X.Z 0) :
    X.L 0 ≤ Subgroup.normalizer ((X.Z 1 ⊔ X.Z 0 : Subgroup G) : Set G) := by
  have H := A.hyp
  have hoTwo := X.oTwoRes_commutator_le_Z hcon
  have hb2 : X.HasB 2 2 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num [Even]) 2).mpr hb
  let M : Subgroup G := X.Z 1 ⊔ X.Z 0
  haveI hMfin : Finite ↥M :=
    finite_of_le_stabilizer X.hyp
      (sup_le (X.Z_le_Gi 1) (hb.Z_le_Gi (j := 1) (by norm_num)))
  have hcardM : ∀ g : G, Nat.card ↥(conjSub g M) = Nat.card ↥M := fun g =>
    (Nat.card_congr (Subgroup.equivMapOfInjective M (MulAut.conj g).toMonoidHom
      (MulEquiv.injective _)).toEquiv).symm
  let N : Subgroup G :=
    { carrier := {l : G | conjSub l M ≤ M}
      one_mem' := by
        show conjSub 1 M ≤ M
        rw [conjSub_one]
      mul_mem' := by
        intro x y hx hy
        show conjSub (x * y) M ≤ M
        rw [conjSub_mul]
        exact (conjSub_mono x hy).trans hx
      inv_mem' := by
        intro x hx
        have heq : conjSub x M = M :=
          Subgroup.eq_of_le_of_card_ge hx (by rw [hcardM x])
        have h1 : conjSub x⁻¹ M = M := by
          calc conjSub x⁻¹ M = conjSub x⁻¹ (conjSub x M) := by rw [heq]
            _ = M := by simpa using conjSub_inv_conjSub x⁻¹ M
        exact le_of_eq h1 }
  have hoTwoN : oTwoRes (X.L 0) ≤ N := by
    intro a ha
    have haL : a ∈ X.L 0 := oTwoRes_le _ ha
    have haG : a ∈ X.Gi 0 := X.L_le_Gi 0 haL
    show conjSub a M ≤ M
    have hZ0 : conjSub a (X.Z 0) = X.Z 0 := X.Z_normal 0 a haG
    have hZ1 : conjSub a (X.Z 1) ≤ X.Z 1 ⊔ X.Z 0 := by
      intro x hx
      rw [mem_conjSub] at hx
      have hzQ : a⁻¹ * x * a ∈ X.Q 0 :=
        X.Z_le_Q_of_lt A.b₁ (j := 0) (by norm_num) hx
      have hcomm : ⁅(a⁻¹ * x * a)⁻¹, a⁆ ∈ X.Z 0 :=
        hoTwo a ha _ ((X.Q 0).inv_mem hzQ)
      have e : x = (a⁻¹ * x * a) * ⁅(a⁻¹ * x * a)⁻¹, a⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (X.Z 1 ⊔ X.Z 0).mul_mem (Subgroup.mem_sup_left hx)
        (Subgroup.mem_sup_right hcomm)
    rw [show M = X.Z 1 ⊔ X.Z 0 from rfl, conjSub_sup, hZ0]
    exact sup_le hZ1 le_sup_right
  have hedgeN : X.edgeSylow 0 ≤ N := by
    rw [X.edgeSylow_zero_eq_Z_sup_Q hb]
    refine sup_le ?_ ?_
    · intro z hz
      show conjSub z M ≤ M
      rw [show M = X.Z 1 ⊔ X.Z 0 from rfl, conjSub_sup]
      have hzG0 : z ∈ X.Gi 0 := hb2.Z_le_Gi (j := 0) (by norm_num) hz
      have hzQ1 : z ∈ X.Q 1 := X.Z_le_Q_of_lt hb2 (j := 1) (by norm_num) hz
      have hZ0 : conjSub z (X.Z 0) = X.Z 0 := X.Z_normal 0 z hzG0
      have hZ1 : conjSub z (X.Z 1) = X.Z 1 :=
        F7.conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _
          (Subgroup.le_centralizer_iff.mp ((X.Z_le_center 1).trans inf_le_right) hzQ1))
      rw [hZ0, hZ1]
    · intro q hq
      show conjSub q M ≤ M
      rw [show M = X.Z 1 ⊔ X.Z 0 from rfl, conjSub_sup]
      have hqG1 : q ∈ X.Gi 1 := ((X.Q_le_Gi_adj 0).trans inf_le_right) hq
      rw [X.Z_normal 1 q hqG1, X.Z_normal 0 q (X.Q_le_Gi 0 hq)]
  have hLN : X.L 0 ≤ N := by
    rw [X.L_eq_oTwoRes_sup]
    exact sup_le hoTwoN hedgeN
  intro l hl
  have hlN : conjSub l M ≤ M := hLN hl
  exact mem_normalizer_iff_conjSub.mpr (Subgroup.eq_of_le_of_card_ge hlN (by rw [hcardM l]))

private theorem exists_odd_not_centralize_Q_mod_Z (X : Setup Γ G) (A : X.CaseA)
    (hb : X.HasB 0 2) :
    ∃ y ∈ X.L 0, Odd (orderOf y) ∧ ∃ e ∈ X.Q 0, ⁅e, y⁆ ∉ X.Z 0 := by
  by_contra! hcon'
  have H := A.hyp
  have hLN := X.L_zero_le_normalizer_Z_one_sup A hb hcon'
  obtain ⟨y, hy, hyv⟩ := X.exists_normalizer_Ki_move
  have heqM : conjSub y (X.Z 1 ⊔ X.Z 0) = X.Z 1 ⊔ X.Z 0 :=
    mem_normalizer_iff_conjSub.mp (hLN hy.1)
  have hZ1 : conjSub y (X.Z 1) = X.Z (-1) := (X.Z_smul X hyv).symm
  have hZ0 : conjSub y (X.Z 0) = X.Z 0 := X.Z_normal 0 y (X.L_le_Gi 0 hy.1)
  have heq2 : X.Z (-1) ⊔ X.Z 0 = X.Z 1 ⊔ X.Z 0 := by
    rw [← heqM, conjSub_sup, hZ1, hZ0]
  have hZ1c : X.Z 1 ≤ Subgroup.centralizer (X.Z 1 : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => X.Z_commute 1 b hb a ha
  have hZ0c : X.Z 0 ≤ Subgroup.centralizer (X.Z 0 : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => X.Z_commute 0 b hb a ha
  have hZ01 : X.Z 0 ≤ Subgroup.centralizer (X.Z 1 : Set G) :=
    (X.Z_le_Q_of_lt hb (j := 1) (by norm_num)).trans
      (Subgroup.le_centralizer_iff.mp ((X.Z_le_center 1).trans inf_le_right))
  have hMc : X.Z 1 ⊔ X.Z 0 ≤
      Subgroup.centralizer ((X.Z 1 ⊔ X.Z 0 : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mp (sup_le hZ1c hZ01))
      (Subgroup.le_centralizer_iff.mp (sup_le (Subgroup.le_centralizer_iff.mp hZ01) hZ0c))
  have hRle : ⁅X.Z (-1), X.Z 1⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb1
    have haM : a ∈ X.Z 1 ⊔ X.Z 0 := by
      rw [← heq2]
      exact Subgroup.mem_sup_left ha
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hMc (Subgroup.mem_sup_left hb1)) a haM
  exact A.R_ne (le_bot_iff.mp hRle)

private theorem caseA_natPre_Z_zero (X : Setup Γ G)
    (A : X.CaseA) (hb : X.HasB 0 2) (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    NatPre (X.L 0) (X.L 0) (X.Z 0) (centerOf (X.L 0)) (X.n 0) ∧
      (centerOf (X.L 0)).relIndex
        (relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow (-1))) = 2 ^ X.n 0 := by
  have H := A.hyp
  have hc := H.char
  haveI hLfin : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (X.L_le_Gi 0)
  haveI hZfin : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (X.Z_le_Gi 0)
  have hnormZ : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    fun l hl => mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 l (X.L_le_Gi 0 hl))
  have hnormC : X.L 0 ≤ Subgroup.normalizer (centerOf (X.L 0) : Set G) :=
    (X.L_le_Gi 0).trans (X.Gi_le_normalizer_centerOf_L 0)
  have hcent : relCent (X.Z 0) (centerOf (X.L 0)) (X.L 0) = centerOf (X.L 0) :=
    X.relCent_centerOf_L_eq H
  have hsec : IsElemSec (centerOf (X.L 0)) (X.Z 0) := X.isElemSec_centerOf_L_Z H hb
  have hcore : ⁅X.Z 0, pCoreOf 2 (X.L 0)⁆ ≤ centerOf (X.L 0) := by
    rw [X.pCoreOf_L_eq 0, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((X.Z_le_center 0).trans inf_le_right)]
    exact bot_le
  have hgen : X.L 0 ≤ (X.edgeSylow (-1) ⊔ X.edgeSylow 0) ⊔ pCoreOf 2 (X.L 0) := by
    rw [X.pCoreOf_L_eq 0, ← X.edgeSylow_sup_edgeSylow 0]
    exact le_sup_left
  have hn2 : X.n (-2) = X.n 0 := by simpa using X.n_add (-1) 0
  have hn2' : X.n 2 = X.n 0 := by simpa using X.n_add 1 0
  have h16 := relIndex_eq_two_pow_of_lines (L := X.L 0) (E := X.Z 0)
    (Z := centerOf (X.L 0)) (T := X.edgeSylow (-1)) (T' := X.edgeSylow 0)
    (by have := H.two_le_n 0; omega) (isL2Quot_L X 0) (X.centerOf_L_le_Z hc 0)
    (X.Z_zero_le_normalizer_centerOf_L) hnormZ hnormC
    ((pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)) hcore
    (X.isSylowTwoOf_edgeSylow_L_succ (-1)).1 (X.isSylowTwoOf_edgeSylow_L 0).1 hgen hcent
    hZ.symm
    (by simpa [hn2] using X.relCent_neg_one_relIndex_le hb)
    (by simpa [hn2'] using X.relCent_zero_relIndex_le hb)
  obtain ⟨hidx, hline⟩ := h16
  have hcorePre : ∀ q ∈ pCoreOf 2 (X.L 0), ∀ e ∈ X.Z 0, ⁅q, e⁆ ∈ centerOf (X.L 0) := by
    intro q hq' e he
    rw [X.pCoreOf_L_eq 0] at hq'
    have h1 : ⁅q, e⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp ((X.Z_le_center 0) he).2 q hq')
    rw [h1]
    exact (centerOf (X.L 0)).one_mem
  have hnontriv : ∃ l ∈ X.L 0, ∃ e ∈ X.Z 0, ⁅l, e⁆ ∉ centerOf (X.L 0) := by
    by_contra! hcon'
    have hZle : X.Z 0 ≤ relCent (X.Z 0) (centerOf (X.L 0)) (X.L 0) := by
      intro e he
      rw [mem_relCent (X.Z_zero_le_normalizer_centerOf_L)]
      refine ⟨he, fun l hl => ?_⟩
      have h := hcon' l hl e he
      rw [← commutatorElement_inv l e]
      exact (centerOf (X.L 0)).inv_mem h
    rw [hcent] at hZle
    exact hZ (le_antisymm hZle (X.centerOf_L_le_Z hc 0))
  have hpre : NatPre (X.L 0) (X.L 0) (X.Z 0) (centerOf (X.L 0)) (X.n 0) :=
    ⟨le_rfl, Subgroup.le_normalizer, hnormZ, hnormC, hsec, hidx, hcorePre,
      isL2Quot_L X 0, hnontriv⟩
  exact ⟨hpre, hline⟩

private theorem caseA_natQuot_Z_zero (X : Setup Γ G)
    (A : X.CaseA) (hb : X.HasB 0 2) (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    NatQuot (X.L 0) (X.Z 0) (centerOf (X.L 0)) (X.n 0) := by
  have H := A.hyp
  haveI : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (X.L_le_Gi 0)
  obtain ⟨hpre, hline⟩ := X.caseA_natPre_Z_zero A hb hZ
  exact natQuot_of_two_pow_le (P := X.L 0) (L := X.L 0) (E := X.Z 0)
    (Z := centerOf (X.L 0)) (T := X.edgeSylow (-1)) (H.two_le_n 0) hpre
    ((X.Z_le_Q 0).trans (X.Q_le_L 0))
    (by simpa using X.isSylowTwoOf_edgeSylow_L_succ (-1)) (le_of_eq hline.symm)

private theorem caseA_commutator_Z_zero_eq_pCoreOf
    (X : Setup Γ G) (A : X.CaseA) (hb : X.HasB 0 2)
    (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    NatQuot (X.L 0) (X.Z 0) (centerOf (X.L 0)) (X.n 0) ∧
      ⁅X.Z 0, X.Z (-2)⁆ = pCoreOf 2 (X.arcStab (-4) 2) ∧
      ⁅X.Z 0, X.Z 2⁆ = pCoreOf 2 (X.arcStab (-2) 4) ∧
      ⁅X.Z 0, X.Z (-2)⁆ ⊓ centerOf (X.L 0) = ⊥ := by
  have H := A.hyp
  have hc := H.char
  have hntq := X.caseA_natQuot_Z_zero A hb hZ
  have hXm_ne : ⁅X.Z 0, X.Z (-2)⁆ ≠ ⊥ :=
    X.commutator_Z_zero_Z_neg_two_ne_bot H hb hntq
  have hXp_ne : ⁅X.Z 0, X.Z 2⁆ ≠ ⊥ := X.commutator_Z_zero_Z_two_ne_bot H hb hntq
  have hCR : centerOf (X.L 0) = ⁅X.Z (-1), X.Z 1⁆ := X.centerOf_L_eq_R A hb hXm_ne
  have hR : ⁅X.Z (-1), X.Z 1⁆ = pCoreOf 2 (X.arcStab (-3) 3) := (X.caseA_3b A).2.2
  have hXm_eq : ⁅X.Z 0, X.Z (-2)⁆ = pCoreOf 2 (X.arcStab (-4) 2) := by
    have h := X.eq_of_le_pCoreOf_arcStab_r H (a := -4) (K_le_normalizer_commutator_Z X 0 (-2))
      hXm_ne (X.commutator_Z_zero_Z_neg_two_le_pCore H hb)
    simpa using h
  have hXp_eq : ⁅X.Z 0, X.Z 2⁆ = pCoreOf 2 (X.arcStab (-2) 4) := by
    have h := X.eq_of_le_pCoreOf_arcStab_r H (a := -2) (K_le_normalizer_commutator_Z X 0 2)
      hXp_ne (X.commutator_Z_zero_Z_two_le_pCore H hb)
    simpa using h
  have hXm_arc : ⁅X.Z 0, X.Z (-2)⁆ ≤ X.arcStab (-4) 2 :=
    X.commutator_Z_zero_Z_neg_two_le_arc hb
  have hUle : ⁅X.Z 0, X.Z (-2)⁆ ⊓ centerOf (X.L 0) ≤ X.arcStab (-4) 3 := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    rw [X.mem_fixSet_iff_le_Gi]
    by_cases h : j ≤ 2
    · exact (inf_le_left.trans hXm_arc).trans (X.arcStab_le_Gi_of_between (by omega) h)
    · have hj3 : j = 3 := by omega
      subst hj3
      have hCG : centerOf (X.L 0) ≤ X.Gi 3 := by
        rw [hCR, hR]
        exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
          (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
      exact inf_le_right.trans hCG
  refine ⟨hntq, hXm_eq, hXp_eq, ?_⟩
  by_contra hne
  have hU2 : IsPGroup 2 ↥(⁅X.Z 0, X.Z (-2)⁆ ⊓ centerOf (X.L 0)) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le
      (inf_le_right.trans ((X.centerOf_L_le_Z hc 0).trans (X.Z_le_Q 0)))
  have hfix : ⁅X.Z 0, X.Z (-2)⁆ ⊓ centerOf (X.L 0) ≤
      X.arcStab (-4) ((-4 : ℤ) + (7 : ℕ)) := by
    simpa using hUle
  have := X.le_r_of_fixes H hU2 hne hfix
  norm_num at this

private theorem caseA_card_commutator_Z_zero (X : Setup Γ G)
    (A : X.CaseA) (hb : X.HasB 0 2) (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    Nat.card ↥(⁅X.Z 0, X.Z (-2)⁆) = 2 ^ X.n 0 ∧
      Nat.card ↥(⁅X.Z 0, X.Z 2⁆) = 2 ^ X.n 0 := by
  have H := A.hyp
  obtain ⟨hntq, hXm_eq, hXp_eq, -⟩ := X.caseA_commutator_Z_zero_eq_pCoreOf A hb hZ
  have hneXm : pCoreOf 2 (X.arcStab (-4) 2) ≠ ⊥ := by
    rw [← hXm_eq]
    exact X.commutator_Z_zero_Z_neg_two_ne_bot H hb hntq
  have hneXp : pCoreOf 2 (X.arcStab (-2) 4) ≠ ⊥ := by
    rw [← hXp_eq]
    exact X.commutator_Z_zero_Z_two_ne_bot H hb hntq
  rw [hXm_eq, hXp_eq]
  have hXm : Nat.card (pCoreOf 2 (X.arcStab (-4) 2)) = 2 ^ X.n 0 := by
    have h := (X.pCoreOf_arcStab_r H (-4) hneXm).1
    rwa [show (-4 : ℤ) + ((6 : ℕ) : ℤ) = 2 by norm_num,
      show (-4 : ℤ) = 0 + 2 * (-2) by norm_num, X.n_add (-2) 0] at h
  have hXp : Nat.card (pCoreOf 2 (X.arcStab (-2) 4)) = 2 ^ X.n 0 := by
    have h := (X.pCoreOf_arcStab_r H (-2) hneXp).1
    rwa [show (-2 : ℤ) + ((6 : ℕ) : ℤ) = 4 by norm_num,
      show (-2 : ℤ) = 0 + 2 * (-1) by norm_num, X.n_add (-1) 0] at h
  exact ⟨hXm, hXp⟩

private theorem caseA_not_edgeSylow_neg_one_le
    (X : Setup Γ G) (A : X.CaseA) (hb : X.HasB 0 2) (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    ¬ X.edgeSylow (-1) ≤ X.edgeSylow 0 ⊔ X.Z 0 := by
  have H := A.hyp
  obtain ⟨hcardXm, hcardXp⟩ := X.caseA_card_commutator_Z_zero A hb hZ
  haveI : Finite ↥(⁅X.Z 0, X.Z 2⁆) := finite_of_le_stabilizer X.hyp
    (((X.commutator_Z_zero_Z_two_le hb).trans inf_le_left).trans (X.Z_le_Gi 0))
  intro hle
  rw [sup_eq_left.mpr ((X.Z_le_Q 0).trans (X.Q_le_edgeSylow_left 0))] at hle
  have hXmle : ⁅X.Z 0, X.Z (-2)⁆ ≤ ⁅X.Z 0, X.Z 2⁆ := by
    rw [← X.commutator_Z_zero_edgeSylow_neg_one hb,
      ← X.commutator_Z_zero_edgeSylow_zero hb]
    exact Subgroup.commutator_mono_right hle
  have heq : ⁅X.Z 0, X.Z (-2)⁆ = ⁅X.Z 0, X.Z 2⁆ :=
    Subgroup.eq_of_le_of_card_ge hXmle (by rw [hcardXm, hcardXp])
  have hbot : ⁅X.Z 0, X.Z (-2)⁆ = ⊥ := by
    have h := X.commutator_Z_zero_inf H hb
    rw [heq, inf_idem] at h
    exact heq.trans h
  exact X.commutator_Z_zero_Z_neg_two_ne_bot H hb (X.caseA_natQuot_Z_zero A hb hZ) hbot

private theorem caseA_Z_neg_one_inf_Z_zero (X : Setup Γ G) (A : X.CaseA) (hb : X.HasB 0 2)
    (hcommA : relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow (-1)) =
      ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z (-1), X.Z 1⁆)
    (hZm1le : ⁅X.Z 0, X.Z (-2)⁆ ≤ X.Z (-1)) :
    X.Z (-1) ⊓ X.Z 0 = ⁅X.Z (-1), X.Z 1⁆ ⊔ ⁅X.Z 0, X.Z (-2)⁆ := by
  have H := A.hyp
  have hc := H.char
  have hNe : X.edgeSylow (-1) ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((X.isSylowTwoOf_edgeSylow (-1)).1.trans inf_le_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  refine le_antisymm ?_ ?_
  · intro u hu
    obtain ⟨huZm1, huZ0⟩ := Subgroup.mem_inf.mp hu
    have hmem : u ∈ relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow (-1)) := by
      rw [mem_relCent (X.Z_zero_le_normalizer_centerOf_L)]
      refine ⟨huZ0, fun a ha => ?_⟩
      have hsupA : X.Q (-1) ⊔ X.Q 0 = X.edgeSylow (-1) := X.sup_Q_eq_edgeSylow hc (-1)
      have ha' : a ∈ X.Q (-1) ⊔ X.Q 0 := hsupA.ge ha
      obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_mul.mp
        ((Subgroup.coe_mul_of_left_le_normalizer_right (X.Q (-1)) (X.Q 0)
          ((X.Q_le_edgeSylow_left (-1)).trans hNe)).subset ha')
      have hup : ⁅u, p⁆ = 1 := commutator_eq_one_of_mem_Z_Q X huZm1 hp
      have huq : ⁅u, q⁆ = 1 := commutator_eq_one_of_mem_Z_Q X huZ0 hq
      rw [commutatorElement_mul_right_eq_mul_conj, hup, huq]
      simp
    rw [hcommA, sup_comm] at hmem
    exact hmem
  · refine le_inf (sup_le (A.R_le.trans inf_le_left) hZm1le) ?_
    exact sup_le ((X.caseA_3a A).1.trans (X.centerOf_L_le_Z hc 0))
      ((X.commutator_Z_zero_Z_neg_two_le hb).trans inf_le_left)

private theorem caseA_Z_zero_eq_sup_of_hasB_two
    (X : Setup Γ G) (A : X.CaseA) (hb : X.HasB 0 2)
    (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    centerOf (X.L 1) = ⁅X.Z 0, X.Z 2⁆ ∧
      centerOf (X.L (-1)) = ⁅X.Z 0, X.Z (-2)⁆ ∧
      X.Z 0 =
        (⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆) ⊔ ⁅X.Z (-1), X.Z 1⁆ ∧
      Nat.card (X.Z 0) = 2 ^ (2 * X.n 0 + X.n 1) ∧
      X.Z (-1) ⊓ X.Z 0 =
        ⁅X.Z (-1), X.Z 1⁆ ⊔ ⁅X.Z 0, X.Z (-2)⁆ := by
  have H := A.hyp
  have hc := H.char
  haveI hZfin : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (X.Z_le_Gi 0)
  obtain ⟨hntq, -, hXp_eq, -⟩ := X.caseA_commutator_Z_zero_eq_pCoreOf A hb hZ
  have hXm_ne : ⁅X.Z 0, X.Z (-2)⁆ ≠ ⊥ :=
    X.commutator_Z_zero_Z_neg_two_ne_bot H hb hntq
  have hCR : centerOf (X.L 0) = ⁅X.Z (-1), X.Z 1⁆ := X.centerOf_L_eq_R A hb hXm_ne
  have hAneg : IsSylowTwoOf (X.edgeSylow (-1)) (X.L 0) := by
    simpa using X.isSylowTwoOf_edgeSylow_L_succ (-1)
  have hAzero : IsSylowTwoOf (X.edgeSylow 0) (X.L 0) := X.isSylowTwoOf_edgeSylow_L 0
  have hCL1 : centerOf (X.L 1) = ⁅X.Z 0, X.Z 2⁆ :=
    le_antisymm (X.centerOf_L_one_le_commutator_Z_zero_Z_two A hXp_eq)
      (X.commutator_Z_zero_Z_two_le_centerOf_L_one H hb)
  have hCLm1 : centerOf (X.L (-1)) = ⁅X.Z 0, X.Z (-2)⁆ :=
    le_antisymm (X.centerOf_L_neg_one_le_commutator_Z_zero_Z_neg_two A hXp_eq)
      (X.commutator_Z_zero_Z_neg_two_le_centerOf_L_neg_one H hb)
  have hZm1le : ⁅X.Z 0, X.Z (-2)⁆ ≤ X.Z (-1) := hCLm1 ▸ X.centerOf_L_le_Z hc (-1)
  have hnot := X.caseA_not_edgeSylow_neg_one_le A hb hZ
  have hcommA' : ⁅X.Z 0, X.edgeSylow (-1)⁆ ⊔ centerOf (X.L 0) =
      ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z (-1), X.Z 1⁆ := by
    rw [X.commutator_Z_zero_edgeSylow_neg_one hb, hCR]
  have hcommA : relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow (-1)) =
      ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z (-1), X.Z 1⁆ :=
    (hntq.comm_eq (X.edgeSylow (-1)) hAneg).symm.trans hcommA'
  have hcommB' : ⁅X.Z 0, X.edgeSylow 0⁆ ⊔ centerOf (X.L 0) =
      ⁅X.Z 0, X.Z 2⁆ ⊔ ⁅X.Z (-1), X.Z 1⁆ := by
    rw [X.commutator_Z_zero_edgeSylow_zero hb, hCR]
  have hcommB : relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow 0) =
      ⁅X.Z 0, X.Z 2⁆ ⊔ ⁅X.Z (-1), X.Z 1⁆ :=
    (hntq.comm_eq (X.edgeSylow 0) hAzero).symm.trans hcommB'
  obtain ⟨hinf, hsup⟩ := hntq.lines_inf (X.edgeSylow (-1)) (X.edgeSylow 0) hAneg hAzero hnot
  rw [hcommA, hcommB] at hinf hsup
  have hZ0eq : X.Z 0 =
      (⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆) ⊔ ⁅X.Z (-1), X.Z 1⁆ :=
    hsup.symm.trans (by ac_rfl)
  have hcardR : Nat.card ↥(⁅X.Z (-1), X.Z 1⁆) = 2 ^ X.n 1 := (X.caseA_3b A).2.1
  have hRleZ : ⁅X.Z (-1), X.Z 1⁆ ≤ X.Z 0 :=
    (X.caseA_3a A).1.trans (X.centerOf_L_le_Z hc 0)
  have hcardZ0 : Nat.card (X.Z 0) = 2 ^ (2 * X.n 0 + X.n 1) := by
    have hidx : (⁅X.Z (-1), X.Z 1⁆).relIndex (X.Z 0) = 2 ^ (2 * X.n 0) := by
      have h := hntq.index
      rw [hCR] at h
      simpa using h
    have hm := Subgroup.relIndex_mul_card (H := ⁅X.Z (-1), X.Z 1⁆) (K := X.Z 0)
    rw [inf_eq_left.mpr hRleZ, hidx, hcardR] at hm
    rw [← hm, ← pow_add]
  refine ⟨hCL1, hCLm1, hZ0eq, hcardZ0, ?_⟩
  exact X.caseA_Z_neg_one_inf_Z_zero A hb hcommA hZm1le

private theorem caseA_card_Z_neg_one (X : Setup Γ G)
    (A : X.CaseA) (hb : X.HasB 0 2) (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    Nat.card ↥(X.Z (-1)) = 2 ^ (X.n 0 + 2 * X.n 1) := by
  have hc := A.hyp.char
  obtain ⟨hCL1, -, -, -, -⟩ := X.caseA_Z_zero_eq_sup_of_hasB_two A hb hZ
  have hXpcard := (X.caseA_card_commutator_Z_zero A hb hZ).2
  have hZ1card : Nat.card ↥(X.Z 1) = 2 ^ (X.n 0 + 2 * X.n 1) := by
    have hm := Subgroup.relIndex_mul_card (H := centerOf (X.L 1)) (K := X.Z 1)
    rw [inf_eq_left.mpr (X.centerOf_L_le_Z hc 1)] at hm
    have hidx : (centerOf (X.L 1)).relIndex (X.Z 1) = 2 ^ (2 * X.n 1) := by
      simpa using (X.caseA_3b A).1.index
    rw [hidx, hCL1, hXpcard] at hm
    rw [← hm, ← pow_add]
    congr 1
    ring
  have hconj : X.Z 1 = conjSub X.τ (X.Z (-1)) := by
    simpa using X.Z_add 1 (-1)
  have hcard : Nat.card ↥(X.Z (-1)) = Nat.card ↥(X.Z 1) := by
    rw [hconj, card_conjSub]
  rw [hcard, hZ1card]

private theorem Z_neg_one_le_normalizer_Z_zero (X : Setup Γ G) (hb : X.HasB 0 2) :
    X.Z (-1) ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
  fun z hz => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
    fun x hx => Subgroup.mem_centralizer_iff.mp ((X.Z_le_center (-1)) hz).2 x
      (X.Z_le_Q_of_lt hb (j := -1) (by norm_num) hx))

private theorem caseA_relIndex_Z_zero_sup (X : Setup Γ G)
    (A : X.CaseA) (hb : X.HasB 0 2) (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    (X.Z 0).relIndex (X.Z (-1) ⊔ X.Z 0) = 2 ^ X.n 1 := by
  have H := A.hyp
  have hc := H.char
  obtain ⟨-, -, -, hXm_inf⟩ := X.caseA_commutator_Z_zero_eq_pCoreOf A hb hZ
  obtain ⟨-, -, -, -, hZinf⟩ := X.caseA_Z_zero_eq_sup_of_hasB_two A hb hZ
  have hXmcard := (X.caseA_card_commutator_Z_zero A hb hZ).1
  have hRcard : Nat.card ↥(⁅X.Z (-1), X.Z 1⁆) = 2 ^ X.n 1 := (X.caseA_3b A).2.1
  have hZm1card := X.caseA_card_Z_neg_one A hb hZ
  have hZm1leN := X.Z_neg_one_le_normalizer_Z_zero hb
  have hRleC : ⁅X.Z (-1), X.Z 1⁆ ≤ centerOf (X.L 0) := (X.caseA_3a A).1
  have hRleZ0 : ⁅X.Z (-1), X.Z 1⁆ ≤ X.Z 0 := hRleC.trans (X.centerOf_L_le_Z hc 0)
  have hXmleZ0 : ⁅X.Z 0, X.Z (-2)⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_neg_two_le hb).trans inf_le_left
  have hRXm_disj : ⁅X.Z (-1), X.Z 1⁆ ⊓ ⁅X.Z 0, X.Z (-2)⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    have h1 : u ∈ ⁅X.Z 0, X.Z (-2)⁆ ⊓ centerOf (X.L 0) :=
      Subgroup.mem_inf.mpr ⟨hu2, hRleC hu1⟩
    rwa [hXm_inf] at h1
  have hnormRXm : ⁅X.Z 0, X.Z (-2)⁆ ≤
      Subgroup.normalizer (((⁅X.Z (-1), X.Z 1⁆ : Subgroup G) : Set G)) :=
    fun b hb' => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      fun x hx => X.Z_commute 0 x (hRleZ0 hx) b (hXmleZ0 hb'))
  have hcardRXm : Nat.card ↥(⁅X.Z (-1), X.Z 1⁆ ⊔ ⁅X.Z 0, X.Z (-2)⁆) =
      2 ^ (X.n 0 + X.n 1) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (⁅X.Z (-1), X.Z 1⁆) (⁅X.Z 0, X.Z (-2)⁆) hnormRXm
      (disjoint_iff.mpr hRXm_disj), hRcard, hXmcard, ← pow_add]
    congr 1
    ring
  have hrel : (X.Z 0).relIndex (X.Z (-1)) = 2 ^ X.n 1 := by
    have hm := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Z (-1))
    rw [inf_comm, hZinf, hcardRXm, hZm1card] at hm
    apply Nat.eq_of_mul_eq_mul_right (m := 2 ^ (X.n 0 + X.n 1)) (by positivity)
    rw [hm, ← pow_add]
    congr 1
    ring
  rw [← CFSG.Quasithin.F53.Stellmacher.relIndex_inf_eq_relIndex_sup hZm1leN,
    Subgroup.inf_relIndex_left]
  exact hrel

private theorem caseA_two_pow_le_relIndex_relCent
    (X : Setup Γ G) (A : X.CaseA) (hb : X.HasB 0 2) (hZ : X.Z 0 ≠ centerOf (X.L 0))
    (hQQ : ⁅X.Q 0, X.Q 0⁆ ≤ X.Z 0) :
    2 ^ X.n 1 ≤ (X.Z 0).relIndex (relCent (X.Q 0) (X.Z 0) (X.edgeSylow (-1))) := by
  have H := A.hyp
  have hZm1leN := X.Z_neg_one_le_normalizer_Z_zero hb
  have hsuprel := X.caseA_relIndex_Z_zero_sup A hb hZ
  have hb1 : X.HasB (-1) 2 :=
    (X.hasB_iff_of_even (i := (-1)) (j := 1) (by norm_num [Even]) 2).mpr A.b₁
  have hZm1rel : X.Z (-1) ≤ relCent (X.Q 0) (X.Z 0) (X.edgeSylow (-1)) := by
    intro z hz
    refine ⟨X.Z_le_Q_of_lt hb1 (i := -1) (j := 0) (by norm_num) hz, hZm1leN hz,
      fun a ha => ?_⟩
    have hb2 : X.HasB (-2) 2 :=
      (X.hasB_iff_of_even (i := (-2)) (j := 0) (by norm_num [Even]) 2).mpr hb
    have hZnegG : X.Z (-2) ≤ X.Gi 0 := hb2.Z_le_Gi (j := 0) (by norm_num)
    rw [X.edgeSylow_neg_one_eq_Z_sup_Q hb] at ha
    obtain ⟨y, hy, q, hq, rfl⟩ := Set.mem_mul.mp
      ((Subgroup.coe_mul_of_left_le_normalizer_right (X.Z (-2)) (X.Q 0)
        (hZnegG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))).subset ha)
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hyQ : y ∈ X.Q (-1) := X.Z_le_Q_of_lt hb2 (j := -1) (by norm_num) hy
    have hzy : ⁅z, y⁆ = 1 := commutator_eq_one_of_mem_Z_Q X hz hyQ
    have hzq : ⁅z, q⁆ ∈ X.Z 0 := hQQ (Subgroup.commutator_mem_commutator
      (X.Z_le_Q_of_lt hb1 (i := -1) (j := 0) (by norm_num) hz) hq)
    rw [hzy, one_mul]
    have hm := mul_mem_conjSub (g := y) (H := X.Z 0) hzq
    rwa [X.Z_normal 0 y (hZnegG hy)] at hm
  have hZ0rel : X.Z 0 ≤ relCent (X.Q 0) (X.Z 0) (X.edgeSylow (-1)) := by
    intro z hz
    refine ⟨X.Z_le_Q 0 hz, ?_, fun a ha => ?_⟩
    · exact Subgroup.le_normalizer hz
    · have hmem : ⁅z, a⁆ ∈ ⁅X.Z 0, X.edgeSylow (-1)⁆ :=
        Subgroup.commutator_mem_commutator hz ha
      rw [X.commutator_Z_zero_edgeSylow_neg_one hb] at hmem
      exact (X.commutator_Z_zero_Z_neg_two_le hb).trans inf_le_left hmem
  have hsuprel_le : X.Z (-1) ⊔ X.Z 0 ≤
      relCent (X.Q 0) (X.Z 0) (X.edgeSylow (-1)) := sup_le hZm1rel hZ0rel
  have hrel_le_Gi : relCent (X.Q 0) (X.Z 0) (X.edgeSylow (-1)) ≤ X.Gi 0 :=
    (le_trans (fun g hg => hg.1) (X.Q_le_Gi 0))
  haveI hRelFin : Finite ↥(relCent (X.Q 0) (X.Z 0) (X.edgeSylow (-1))) :=
    finite_of_le_stabilizer X.hyp hrel_le_Gi
  haveI hZfin : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (X.Z_le_Gi 0)
  have hpos : 0 < (X.Z 0).relIndex
      (relCent (X.Q 0) (X.Z 0) (X.edgeSylow (-1))) := Nat.card_pos
  rw [← hsuprel]
  exact Subgroup.relIndex_le_of_le_right hsuprel_le hpos.ne'

private theorem caseA_swap_hasB_zero (X : Setup Γ G) (A : X.CaseA) :
    X.swap.HasB 0 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hj' : (-j).natAbs ≤ 2 := by rwa [Int.natAbs_neg]
    have h := A.b₁.1 (-j) hj'
    have e : (1 : ℤ) + -j = 1 - j := by ring
    simpa [Setup.swap_Z, Setup.swap_Gi, e] using h
  · simpa [Setup.swap_Z, Setup.swap_Gi] using A.b₁.2.2
  · simpa [Setup.swap_Z, Setup.swap_Gi] using A.b₁.2.1

private theorem caseA_swap_hasB_one (X : Setup Γ G) (hb : X.HasB 0 2) :
    X.swap.HasB 1 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hj' : (-j).natAbs ≤ 2 := by rwa [Int.natAbs_neg]
    have h := hb.1 (-j) hj'
    have e : (1 : ℤ) + -j = 1 - j := by ring
    simpa [Setup.swap_Z, Setup.swap_Gi, e] using h
  · simpa [Setup.swap_Z, Setup.swap_Gi] using hb.2.2
  · simpa [Setup.swap_Z, Setup.swap_Gi] using hb.2.1

private theorem caseA_exists_odd_not_centralize_Q_one (X : Setup Γ G) (A : X.CaseA)
    (hb : X.HasB 0 2) (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    ∃ y ∈ X.L 1, Odd (orderOf y) ∧ ∃ e ∈ X.Q 1, ⁅e, y⁆ ∉ X.Z 1 := by
  have hb₁ : X.swap.HasB 1 2 := X.caseA_swap_hasB_one hb
  have hRle : ⁅X.swap.Z (-1), X.swap.Z 1⁆ ≤ X.swap.Z (-1) ⊓ X.swap.Z 1 := by
    have h := X.commutator_Z_zero_Z_two_le hb
    rw [Subgroup.commutator_comm, inf_comm] at h
    simpa [Setup.swap_Z] using h
  have hRne : ⁅X.swap.Z (-1), X.swap.Z 1⁆ ≠ ⊥ := by
    have h := X.commutator_Z_zero_Z_two_ne_bot A.hyp hb (X.caseA_natQuot_Z_zero A hb hZ)
    rw [Subgroup.commutator_comm] at h
    simpa [Setup.swap_Z] using h
  let A' : X.swap.CaseA :=
    { hyp := Sec4Hyp.swap X A.hyp (by norm_num : 6 + 1 = 7)
      b₁ := hb₁
      R_le := hRle
      R_ne := hRne }
  have h := X.swap.exists_odd_not_centralize_Q_mod_Z A' (X.caseA_swap_hasB_zero A)
  simpa [Setup.swap_L, Setup.swap_Q, Setup.swap_Z] using h

private theorem caseA_card_Z_one (X : Setup Γ G)
    (A : X.CaseA) (hb : X.HasB 0 2) (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    Nat.card ↥(X.Z 1) = 2 ^ (X.n 0 + 2 * X.n 1) := by
  have hc := A.hyp.char
  obtain ⟨hCL1, -, -, -, -⟩ := X.caseA_Z_zero_eq_sup_of_hasB_two A hb hZ
  have hXpcard := (X.caseA_card_commutator_Z_zero A hb hZ).2
  have hm := Subgroup.relIndex_mul_card (H := centerOf (X.L 1)) (K := X.Z 1)
  rw [inf_eq_left.mpr (X.centerOf_L_le_Z hc 1)] at hm
  have hidx : (centerOf (X.L 1)).relIndex (X.Z 1) = 2 ^ (2 * X.n 1) := by
    simpa using (X.caseA_3b A).1.index
  rw [hidx, hCL1, hXpcard] at hm
  rw [← hm, ← pow_add]
  congr 1
  ring

private theorem caseA_exists_commutator_not_mem_subgroupOf (X : Setup Γ G) (i : ℤ)
    {y e : G} (hyL : y ∈ X.L i) (heQ : e ∈ X.Q i) (hne : ⁅e, y⁆ ∉ X.Z i) :
    ∃ a ∈ (X.Q i).subgroupOf (X.Gi i),
      (⟨y, X.L_le_Gi i hyL⟩ : ↥(X.Gi i)) * a * ⟨y, X.L_le_Gi i hyL⟩⁻¹ * a⁻¹ ∉
        (X.Z i).subgroupOf (X.Gi i) := by
  let a : (X.Q i).subgroupOf (X.Gi i) :=
    ⟨⟨e, X.Q_le_Gi i heQ⟩, Subgroup.mem_subgroupOf.mpr heQ⟩
  refine ⟨a, a.2, ?_⟩
  intro hmem
  apply hne
  have hcoe : (((⟨y, X.L_le_Gi i hyL⟩ : ↥(X.Gi i)) * (a : ↥(X.Gi i)) *
      (⟨y, X.L_le_Gi i hyL⟩ : ↥(X.Gi i))⁻¹ * (a : ↥(X.Gi i))⁻¹ : ↥(X.Gi i)) : G) =
      y * e * y⁻¹ * e⁻¹ := by
    change (y * (a : G) * y⁻¹ * (a : G)⁻¹) = y * e * y⁻¹ * e⁻¹
    simp [a]
  have hZ : y * e * y⁻¹ * e⁻¹ ∈ X.Z i := by
    have := Subgroup.mem_subgroupOf.mp hmem
    rwa [hcoe] at this
  have hinv := (X.Z i).inv_mem hZ
  show e * y * e⁻¹ * y⁻¹ ∈ X.Z i
  rw [show e * y * e⁻¹ * y⁻¹ = (y * e * y⁻¹ * e⁻¹)⁻¹ by group]
  exact hinv

private theorem caseA_exists_chief_factor (X : Setup Γ G) (i : ℤ)
    (hQ2 : IsPGroup 2 (X.Q i)) (hZQ : X.Z i ≤ X.Q i) (hQL : X.Q i ≤ X.L i)
    (hLQ : X.L i ≤ Subgroup.normalizer (X.Q i : Set G))
    (hLZ : X.L i ≤ Subgroup.normalizer (X.Z i : Set G))
    (hnt : ∃ y ∈ X.L i, Odd (orderOf y) ∧ ∃ e ∈ X.Q i, ⁅e, y⁆ ∉ X.Z i) :
    ∃ A' B' : Subgroup ↥(X.Gi i),
      (X.Z i).subgroupOf (X.Gi i) ≤ B' ∧ B' < A' ∧
        A' ≤ (X.Q i).subgroupOf (X.Gi i) ∧
        (X.L i).subgroupOf (X.Gi i) ≤ Subgroup.normalizer (A' : Set ↥(X.Gi i)) ∧
        (X.L i).subgroupOf (X.Gi i) ≤ Subgroup.normalizer (B' : Set ↥(X.Gi i)) ∧
        (∀ C : Subgroup ↥(X.Gi i), B' ≤ C → C ≤ A' →
          (X.L i).subgroupOf (X.Gi i) ≤ Subgroup.normalizer (C : Set ↥(X.Gi i)) →
          C = B' ∨ C = A') ∧
        ¬ ⁅A', (X.L i).subgroupOf (X.Gi i)⁆ ≤ B' := by
  classical
  haveI hHfin : Finite ↥(X.Gi i) := finite_of_le_stabilizer X.hyp (H := X.Gi i) le_rfl
  let H := ↥(X.Gi i)
  let XH : Subgroup H := (X.L i).subgroupOf (X.Gi i)
  let AH : Subgroup H := (X.Q i).subgroupOf (X.Gi i)
  let BH : Subgroup H := (X.Z i).subgroupOf (X.Gi i)
  have hAHle : AH ≤ XH := fun q hq =>
    Subgroup.mem_subgroupOf.mpr (hQL (Subgroup.mem_subgroupOf.mp hq))
  have hBHle : BH ≤ AH := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (hZQ (Subgroup.mem_subgroupOf.mp hz))
  have hAH2 : IsPGroup 2 AH :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe (X.Q_le_Gi i)).symm
  have hXHA : XH ≤ Subgroup.normalizer (AH : Set H) := by
    intro l hl
    rw [← Subgroup.subgroupOf_normalizer_eq (X.Q_le_Gi i), Subgroup.mem_subgroupOf]
    exact hLQ (Subgroup.mem_subgroupOf.mp hl)
  have hXHB : XH ≤ Subgroup.normalizer (BH : Set H) := by
    intro l hl
    rw [← Subgroup.subgroupOf_normalizer_eq (X.Z_le_Gi i), Subgroup.mem_subgroupOf]
    exact hLZ (Subgroup.mem_subgroupOf.mp hl)
  obtain ⟨y, hyL, hyodd, e, heQ, hne⟩ := hnt
  set x : H := ⟨y, X.L_le_Gi i hyL⟩ with hx
  have hxm : x ^ orderOf y = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa [x] using pow_orderOf_eq_one y
  have hntH : ∃ a ∈ AH, x * a * x⁻¹ * a⁻¹ ∉ BH := by
    simpa [x, AH, BH, H] using
      X.caseA_exists_commutator_not_mem_subgroupOf i hyL heQ hne
  obtain ⟨A', B', hBA', hA'A, hchief, hnc⟩ :=
    CFSG.Quasithin.H13.NQS134.exists_noncentral_chief (G := H) (X := XH) (x := x)
      (by simpa [x] using Subgroup.mem_subgroupOf.mpr hyL) hyodd hxm
      (Nat.card AH - Nat.card BH) AH BH le_rfl
      hAH2 hAHle hBHle hXHA hXHB hntH
  have hsel : ∀ C : Subgroup H, B' ≤ C → C ≤ A' →
      XH ≤ Subgroup.normalizer (C : Set H) → C = B' ∨ C = A' := by
    intro C hB hA hN
    rcases eq_or_lt_of_le hB with h | h
    · exact Or.inl h.symm
    rcases eq_or_lt_of_le hA with h' | h'
    · exact Or.inr h'
    · exact absurd hN (hchief.2.2.2 C h h')
  exact ⟨A', B', hBA', hchief.1, hA'A, hchief.2.1, hchief.2.2.1, hsel, hnc⟩

private theorem caseA_relIndex_chief_le (X : Setup Γ G) (i : ℤ)
    {A' B' : Subgroup ↥(X.Gi i)}
    (hBA : (X.Z i).subgroupOf (X.Gi i) ≤ B') (hlt : B' < A')
    (hA'A : A' ≤ (X.Q i).subgroupOf (X.Gi i)) :
    B'.relIndex A' ≤ (X.Z i).relIndex (X.Q i) := by
  let W : Subgroup G := B'.map (X.Gi i).subtype
  let V : Subgroup G := A'.map (X.Gi i).subtype
  have hrel : B'.relIndex A' = W.relIndex V := by
    simpa [W, V] using
      (Subgroup.relIndex_map_map_of_injective (f := (X.Gi i).subtype) B' A'
        Subtype.coe_injective).symm
  have hBHmap : ((X.Z i).subgroupOf (X.Gi i)).map (X.Gi i).subtype = X.Z i := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (X.Z_le_Gi i)]
  have hAHmap : ((X.Q i).subgroupOf (X.Gi i)).map (X.Gi i).subtype = X.Q i := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (X.Q_le_Gi i)]
  have hZW : X.Z i ≤ W := by
    rw [← hBHmap]
    exact Subgroup.map_mono hBA
  have hWV : W ≤ V := Subgroup.map_mono hlt.le
  have hVQ : V ≤ X.Q i := by
    rw [← hAHmap]
    exact Subgroup.map_mono hA'A
  haveI : Finite ↥(X.Q i) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi i)
  haveI : Finite ↥(X.Z i) := finite_of_le_stabilizer X.hyp (X.Z_le_Gi i)
  haveI : Finite ↥W :=
    finite_of_le_stabilizer X.hyp (H := W) ((hWV.trans hVQ).trans (X.Q_le_Gi i))
  haveI : Finite ↥V := finite_of_le_stabilizer X.hyp (H := V) (hVQ.trans (X.Q_le_Gi i))
  have hposWQ : 0 < W.relIndex (X.Q i) := by
    have hdvd := Subgroup.relIndex_dvd_card (H := W) (K := X.Q i)
    exact Nat.pos_of_dvd_of_pos hdvd Nat.card_pos
  have hposZW : 0 < (X.Z i).relIndex W := by
    have hdvd := Subgroup.relIndex_dvd_card (H := X.Z i) (K := W)
    exact Nat.pos_of_dvd_of_pos hdvd Nat.card_pos
  have hmul : (X.Z i).relIndex W * W.relIndex (X.Q i) = (X.Z i).relIndex (X.Q i) :=
    Subgroup.relIndex_mul_relIndex (H := X.Z i) (K := W) (L := X.Q i) hZW
      (hWV.trans hVQ)
  have hWVle : W.relIndex V ≤ W.relIndex (X.Q i) :=
    Subgroup.relIndex_le_of_le_right hVQ (ne_of_gt hposWQ)
  calc B'.relIndex A' = W.relIndex V := hrel
    _ ≤ W.relIndex (X.Q i) := hWVle
    _ ≤ (X.Z i).relIndex (X.Q i) := by
        rw [← hmul]
        exact Nat.le_mul_of_pos_left _ hposZW

private theorem two_pow_le_relIndex_Z_Q_of_odd (X : Setup Γ G) (i : ℤ) (hn : 2 ≤ X.n i)
    (hQ2 : IsPGroup 2 (X.Q i)) (hZQ : X.Z i ≤ X.Q i) (hQL : X.Q i ≤ X.L i)
    (hLQ : X.L i ≤ Subgroup.normalizer (X.Q i : Set G))
    (hLZ : X.L i ≤ Subgroup.normalizer (X.Z i : Set G))
    (hnt : ∃ y ∈ X.L i, Odd (orderOf y) ∧ ∃ e ∈ X.Q i, ⁅e, y⁆ ∉ X.Z i) :
    2 ^ (2 * X.n i) ≤ (X.Z i).relIndex (X.Q i) := by
  classical
  haveI hHfin : Finite ↥(X.Gi i) := finite_of_le_stabilizer X.hyp (H := X.Gi i) le_rfl
  let H := ↥(X.Gi i)
  let XH : Subgroup H := (X.L i).subgroupOf (X.Gi i)
  let AH : Subgroup H := (X.Q i).subgroupOf (X.Gi i)
  obtain ⟨A', B', hBA', hlt, hA'A, hNA', hNB', hsel, hnc⟩ :=
    X.caseA_exists_chief_factor i hQ2 hZQ hQL hLQ hLZ hnt
  have hAH2 : IsPGroup 2 AH :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe (X.Q_le_Gi i)).symm
  have hp : IsPGroup 2 ↥A' := hAH2.to_le hA'A
  have hsec : IsElemSec B' A' := by
    obtain ⟨hcomm, hsq⟩ := CFSG.Quasithin.H13.L829N.chief_section_elemAb (G := H)
      hlt hp hNB' hNA' hsel
    refine ⟨hlt.le, ?_, ?_⟩
    · rw [Subgroup.commutator_le]
      exact hcomm
    · intro z hz
      simpa [pow_two] using hsq z hz
  have hquotH : IsL2Quot (X.n i) (oTwoQuot ↥XH) := by
    obtain ⟨e₂⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert i)).quot
    exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr
      (Subgroup.subgroupOfEquivOfLe (X.L_le_Gi i))).trans e₂⟩
  have hnt' : ∃ l ∈ XH, ∃ v ∈ A', ⁅l, v⁆ ∉ B' := by
    by_contra! hcon
    apply hnc
    rw [Subgroup.commutator_le]
    intro a ha l hl
    have h := (B').inv_mem (hcon l hl a ha)
    rwa [commutatorElement_inv] at h
  have hF4 := two_pow_le_relIndex_of_irreducible (G := H) (V := A') (Z := B')
    (L := XH) (m := X.n i) (by have := hn; omega) hquotH hlt.le hsec (le_inf hNA' hNB')
    hsel hnt'
  calc 2 ^ (2 * X.n i) ≤ B'.relIndex A' := hF4
    _ ≤ (X.Z i).relIndex (X.Q i) := X.caseA_relIndex_chief_le i hBA' hlt hA'A
private theorem caseA_n_zero_eq_n_one (X : Setup Γ G)
    (A : X.CaseA) (hb : X.HasB 0 2) (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    X.n 0 = X.n 1 := by
  have H := A.hyp
  have hodd0 := X.exists_odd_not_centralize_Q_mod_Z A hb
  have hodd1 := X.caseA_exists_odd_not_centralize_Q_one A hb hZ
  have hLQ0 : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hLZ0 : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := fun l hl =>
    mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 l (X.L_le_Gi 0 hl))
  have hLQ1 : X.L 1 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.L_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hLZ1 : X.L 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := fun l hl =>
    mem_normalizer_iff_conjSub.mpr (X.Z_normal 1 l (X.L_le_Gi 1 hl))
  have hle0 := X.two_pow_le_relIndex_Z_Q_of_odd 0 (H.two_le_n 0)
    (pCoreOf_isPGroup' (X.Gi 0)) (X.Z_le_Q 0) (X.Q_le_L 0) hLQ0 hLZ0 hodd0
  have hle1 := X.two_pow_le_relIndex_Z_Q_of_odd 1 (H.two_le_n 1)
    (pCoreOf_isPGroup' (X.Gi 1)) (X.Z_le_Q 1) (X.Q_le_L 1) hLQ1 hLZ1 hodd1
  obtain ⟨-, -, -, hZ0card, -⟩ := X.caseA_Z_zero_eq_sup_of_hasB_two A hb hZ
  have hZ1card := X.caseA_card_Z_one A hb hZ
  have hq0 : (X.Z 0).relIndex (X.Q 0) = 2 ^ (2 * X.n 1) := by
    have hm := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Q 0)
    rw [inf_eq_left.mpr (X.Z_le_Q 0)] at hm
    have hQ0 := (X.caseA_card A).2 0
    have hn01' : X.n (0 + 1) = X.n 1 := by simpa using X.n_add 0 1
    have hR : Nat.card ↥(X.Q 0) = 2 ^ (2 * X.n 0 + 3 * X.n 1) := by
      rw [hQ0, hn01']
    have hZ : Nat.card ↥(X.Z 0) = 2 ^ (2 * X.n 0 + X.n 1) := hZ0card
    have hm' : (X.Z 0).relIndex (X.Q 0) * 2 ^ (2 * X.n 0 + X.n 1) =
        2 ^ (2 * X.n 0 + 3 * X.n 1) := by
      rw [← hZ, ← hR]
      exact hm
    apply Nat.eq_of_mul_eq_mul_right (m := 2 ^ (2 * X.n 0 + X.n 1)) (by positivity)
    rw [hm', ← pow_add]
    congr 1
    ring
  have hq1 : (X.Z 1).relIndex (X.Q 1) = 2 ^ (2 * X.n 0) := by
    have hm := Subgroup.relIndex_mul_card (H := X.Z 1) (K := X.Q 1)
    rw [inf_eq_left.mpr (X.Z_le_Q 1)] at hm
    have hQ1 := (X.caseA_card A).2 1
    have hn2 : X.n (1 + 1) = X.n 0 := by simpa using X.n_add 1 0
    have hR : Nat.card ↥(X.Q 1) = 2 ^ (2 * X.n 1 + 3 * X.n 0) := by
      rw [hQ1, hn2]
    have hZ : Nat.card ↥(X.Z 1) = 2 ^ (X.n 0 + 2 * X.n 1) := hZ1card
    have hm' : (X.Z 1).relIndex (X.Q 1) * 2 ^ (X.n 0 + 2 * X.n 1) =
        2 ^ (2 * X.n 1 + 3 * X.n 0) := by
      rw [← hZ, ← hR]
      exact hm
    apply Nat.eq_of_mul_eq_mul_right (m := 2 ^ (X.n 0 + 2 * X.n 1)) (by positivity)
    rw [hm', ← pow_add]
    congr 1
    ring
  rw [hq0] at hle0
  rw [hq1] at hle1
  have e0 : 2 * X.n 0 ≤ 2 * X.n 1 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle0
  have e1 : 2 * X.n 1 ≤ 2 * X.n 0 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle1
  omega

private theorem caseA_natQuot_Q_zero_of_hasB_two
    (X : Setup Γ G) (A : X.CaseA) (hb : X.HasB 0 2)
    (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    IsElemSec (X.Z 0) (X.Q 0) ∧ NatQuot (X.L 0) (X.Q 0) (X.Z 0) (X.n 0) := by
  have H := A.hyp
  have hn01 := X.caseA_n_zero_eq_n_one A hb hZ
  haveI hLfin : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (X.L_le_Gi 0)
  haveI hQfin : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi 0)
  haveI hZfin : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (X.Z_le_Gi 0)
  obtain ⟨-, -, -, hZ0card, -⟩ := X.caseA_Z_zero_eq_sup_of_hasB_two A hb hZ
  have h16 : (X.Z 0).relIndex (X.Q 0) = 2 ^ (2 * X.n 0) := by
    have hm := Subgroup.relIndex_mul_card (H := X.Z 0) (K := X.Q 0)
    rw [inf_eq_left.mpr (X.Z_le_Q 0)] at hm
    have hQ0 := (X.caseA_card A).2 0
    have hn01' : X.n (0 + 1) = X.n 1 := by simpa using X.n_add 0 1
    have hR : Nat.card ↥(X.Q 0) = 2 ^ (2 * X.n 1 + 3 * X.n 1) := by
      rw [hQ0, hn01', hn01]
    have hZ : Nat.card ↥(X.Z 0) = 2 ^ (2 * X.n 1 + X.n 1) := by
      rw [hZ0card, hn01]
    have hm' : (X.Z 0).relIndex (X.Q 0) * 2 ^ (2 * X.n 1 + X.n 1) =
        2 ^ (2 * X.n 1 + 3 * X.n 1) := by
      rw [← hZ, ← hR]
      exact hm
    apply Nat.eq_of_mul_eq_mul_right (m := 2 ^ (2 * X.n 1 + X.n 1)) (by positivity)
    rw [hm', ← pow_add, hn01]
    congr 1
    ring
  have hnt := X.exists_odd_not_centralize_Q_mod_Z A hb
  have hEN : X.Q 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    fun q hq => mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 q (X.Q_le_Gi 0 hq))
  have hLN : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    fun l hl => mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 l (X.L_le_Gi 0 hl))
  have hLE : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    fun l hl => mem_normalizer_iff_conjSub.mpr (by
      rw [← X.pCoreOf_L_eq 0, ← pCoreOf_conjSub, conjSub_eq_of_mem hl])
  have hsec : IsElemSec (X.Z 0) (X.Q 0) :=
    isElemSec_of_relIndex_eq_two_pow (n := X.n 0) (by have := H.two_le_n 0; omega)
      (isL2Quot_L X 0) (X.Z_le_Q 0) hEN hLE hLN h16 hnt
  have hQQ : ⁅X.Q 0, X.Q 0⁆ ≤ X.Z 0 := hsec.2.1
  have hC : 2 ^ (X.n 0) ≤
      (X.Z 0).relIndex (relCent (X.Q 0) (X.Z 0) (X.edgeSylow (-1))) := by
    have h := X.caseA_two_pow_le_relIndex_relCent A hb hZ hQQ
    rwa [← hn01] at h
  have hcore : ∀ q ∈ pCoreOf 2 (X.L 0), ∀ e ∈ X.Q 0, ⁅q, e⁆ ∈ X.Z 0 := by
    intro q hq e he
    rw [X.pCoreOf_L_eq 0] at hq
    exact hQQ (Subgroup.commutator_mem_commutator hq he)
  have hnontriv : ∃ l ∈ X.L 0, ∃ e ∈ X.Q 0, ⁅l, e⁆ ∉ X.Z 0 := by
    obtain ⟨y, hyL, -, e, heQ, hne⟩ := hnt
    refine ⟨y, hyL, e, heQ, fun hmem => hne ?_⟩
    have hinv := (X.Z 0).inv_mem hmem
    rwa [commutatorElement_inv] at hinv
  have hpre : NatPre (X.L 0) (X.L 0) (X.Q 0) (X.Z 0) (X.n 0) :=
    ⟨le_rfl, Subgroup.le_normalizer, hLE, hLN, hsec, h16, hcore, isL2Quot_L X 0, hnontriv⟩
  exact ⟨hsec, natQuot_of_two_pow_le (P := X.L 0) (L := X.L 0) (E := X.Q 0)
    (Z := X.Z 0) (T := X.edgeSylow (-1)) (H.two_le_n 0) hpre (X.Q_le_L 0)
    (by simpa using X.isSylowTwoOf_edgeSylow_L_succ (-1)) hC⟩

private theorem caseA_Q_one_le_normalizer_sup (X : Setup Γ G) (A : X.CaseA)
    (hb : X.HasB 0 2) (hCL1 : centerOf (X.L 1) = ⁅X.Z 0, X.Z 2⁆) :
    X.Q 1 ≤ Subgroup.normalizer
      ((⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ : Subgroup G) : Set G) := by
  have H := A.hyp
  have hXmleZ0 : ⁅X.Z 0, X.Z (-2)⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_neg_two_le hb).trans inf_le_left
  have hXpleZ0 : ⁅X.Z 0, X.Z 2⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_two_le hb).trans inf_le_left
  have hNleZ0 : ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ ≤ X.Z 0 :=
    sup_le hXmleZ0 hXpleZ0
  have hXp_of_Q1 : ⁅X.Z 0, X.Q 1⁆ ≤ ⁅X.Z 0, X.Z 2⁆ :=
    (Subgroup.commutator_mono le_rfl (X.Q_le_edgeSylow 0)).trans
      (le_of_eq (X.commutator_Z_zero_edgeSylow_zero hb))
  intro q hq
  rw [mem_normalizer_iff_conjSub]
  have hqL : q ∈ X.L 1 := X.Q_le_L 1 hq
  have hconjL : conjSub q (X.L 1) = X.L 1 := conjSub_eq_of_mem hqL
  have hXpconj : conjSub q (⁅X.Z 0, X.Z 2⁆) = ⁅X.Z 0, X.Z 2⁆ := by
    rw [← hCL1, ← centerOf_conjSub, hconjL]
  have hXmconj : conjSub q (⁅X.Z 0, X.Z (-2)⁆) ≤
      ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ := by
    intro y hy
    rw [mem_conjSub] at hy
    have hyZ : q⁻¹ * y * q ∈ X.Z 0 := hXmleZ0 hy
    have hqy : ⁅q, q⁻¹ * y * q⁆ ∈ ⁅X.Z 0, X.Z 2⁆ := by
      have h := hXp_of_Q1 (Subgroup.commutator_mem_commutator hyZ hq)
      rw [← commutatorElement_inv (q⁻¹ * y * q) q]
      exact (⁅X.Z 0, X.Z 2⁆).inv_mem h
    have e : y = ⁅q, q⁻¹ * y * q⁆ * (q⁻¹ * y * q) := by
      conv_lhs => rw [show y = q * (q⁻¹ * y * q) * q⁻¹ by group]
      exact conj_eq_commutatorElement_mul
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right hqy) (Subgroup.mem_sup_left hy)
  have hle : conjSub q (⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆) ≤
      ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ := by
    rw [conjSub_sup, hXpconj]
    exact sup_le hXmconj le_sup_right
  haveI hNfin : Finite ↥(⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ : Subgroup G) :=
    finite_of_le_stabilizer X.hyp (hNleZ0.trans (X.Z_le_Gi 0))
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_conjSub q _).symm)

private theorem caseA_Q_neg_one_le_normalizer_sup (X : Setup Γ G) (A : X.CaseA)
    (hb : X.HasB 0 2) (hCLm1 : centerOf (X.L (-1)) = ⁅X.Z 0, X.Z (-2)⁆) :
    X.Q (-1) ≤ Subgroup.normalizer
      ((⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ : Subgroup G) : Set G) := by
  have H := A.hyp
  have hXmleZ0 : ⁅X.Z 0, X.Z (-2)⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_neg_two_le hb).trans inf_le_left
  have hXpleZ0 : ⁅X.Z 0, X.Z 2⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_two_le hb).trans inf_le_left
  have hNleZ0 : ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ ≤ X.Z 0 :=
    sup_le hXmleZ0 hXpleZ0
  have hXm_of_Qm1 : ⁅X.Z 0, X.Q (-1)⁆ ≤ ⁅X.Z 0, X.Z (-2)⁆ :=
    (Subgroup.commutator_mono le_rfl (X.Q_le_edgeSylow_left (-1))).trans
      (le_of_eq (X.commutator_Z_zero_edgeSylow_neg_one hb))
  intro q hq
  rw [mem_normalizer_iff_conjSub]
  have hqL : q ∈ X.L (-1) := X.Q_le_L (-1) hq
  have hconjL : conjSub q (X.L (-1)) = X.L (-1) := conjSub_eq_of_mem hqL
  have hXmconj : conjSub q (⁅X.Z 0, X.Z (-2)⁆) = ⁅X.Z 0, X.Z (-2)⁆ := by
    rw [← hCLm1, ← centerOf_conjSub, hconjL]
  have hXpconj : conjSub q (⁅X.Z 0, X.Z 2⁆) ≤
      ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ := by
    intro y hy
    rw [mem_conjSub] at hy
    have hyZ : q⁻¹ * y * q ∈ X.Z 0 := hXpleZ0 hy
    have hqy : ⁅q, q⁻¹ * y * q⁆ ∈ ⁅X.Z 0, X.Z (-2)⁆ := by
      have h := hXm_of_Qm1 (Subgroup.commutator_mem_commutator hyZ hq)
      rw [← commutatorElement_inv (q⁻¹ * y * q) q]
      exact (⁅X.Z 0, X.Z (-2)⁆).inv_mem h
    have e : y = ⁅q, q⁻¹ * y * q⁆ * (q⁻¹ * y * q) := by
      conv_lhs => rw [show y = q * (q⁻¹ * y * q) * q⁻¹ by group]
      exact conj_eq_commutatorElement_mul
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left hqy) (Subgroup.mem_sup_right hy)
  have hle : conjSub q (⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆) ≤
      ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ := by
    rw [conjSub_sup, hXmconj]
    exact sup_le le_sup_left hXpconj
  haveI hNfin : Finite ↥(⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ : Subgroup G) :=
    finite_of_le_stabilizer X.hyp (hNleZ0.trans (X.Z_le_Gi 0))
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_conjSub q _).symm)

private theorem caseA_card_commutator_sup (X : Setup Γ G)
    (A : X.CaseA) (hb : X.HasB 0 2) (hZ : X.Z 0 ≠ centerOf (X.L 0)) :
    Nat.card ↥(⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆) = 2 ^ (2 * X.n 0) := by
  have H := A.hyp
  obtain ⟨hXmcard, hXpcard⟩ := X.caseA_card_commutator_Z_zero A hb hZ
  have hXmleZ0 : ⁅X.Z 0, X.Z (-2)⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_neg_two_le hb).trans inf_le_left
  have hXpleZ0 : ⁅X.Z 0, X.Z 2⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_two_le hb).trans inf_le_left
  have hnorm : ⁅X.Z 0, X.Z 2⁆ ≤ Subgroup.normalizer
      ((⁅X.Z 0, X.Z (-2)⁆ : Subgroup G) : Set G) :=
    fun b hb' => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      fun x hx => X.Z_commute 0 x (hXmleZ0 hx) b (hXpleZ0 hb'))
  have hdisj : Disjoint (⁅X.Z 0, X.Z (-2)⁆) (⁅X.Z 0, X.Z 2⁆) :=
    disjoint_iff.mpr (X.commutator_Z_zero_inf H hb)
  have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (⁅X.Z 0, X.Z (-2)⁆) (⁅X.Z 0, X.Z 2⁆) hnorm hdisj
  rw [h, hXmcard, hXpcard, ← pow_add]
  congr 1
  ring

private theorem caseA_isElemSec_sup_Z_zero (X : Setup Γ G) (A : X.CaseA) (hb : X.HasB 0 2)
    (hZ0eq : X.Z 0 = (⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆) ⊔ ⁅X.Z (-1), X.Z 1⁆) :
    IsElemSec (⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆) (X.Z 0) := by
  have H := A.hyp
  have hc := H.char
  have hXmEA : IsElemAbelian 2 ⁅X.Z 0, X.Z (-2)⁆ := X.isElemAbelian_commutator_Z_zero H hb
  have hXpEA : IsElemAbelian 2 ⁅X.Z 0, X.Z 2⁆ := by
    have hpc := X.isElemAbelian_pCoreOf_arcStab_r H (-2)
    norm_num at hpc
    exact hpc.mono (X.commutator_Z_zero_Z_two_le_pCore H hb)
  have hXmleZ0 : ⁅X.Z 0, X.Z (-2)⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_neg_two_le hb).trans inf_le_left
  have hXpleZ0 : ⁅X.Z 0, X.Z 2⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_two_le hb).trans inf_le_left
  have hNleZ0 : ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ ≤ X.Z 0 :=
    sup_le hXmleZ0 hXpleZ0
  have hRleZ0 : ⁅X.Z (-1), X.Z 1⁆ ≤ X.Z 0 :=
    (X.caseA_3a A).1.trans (X.centerOf_L_le_Z hc 0)
  have hNEA : IsElemAbelian 2 (⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆) := by
    refine IsElemAbelian.sup_of_commute hXmEA hXpEA ?_
    intro a ha b hb'
    exact X.Z_commute 0 a (hXmleZ0 ha) b (hXpleZ0 hb')
  have hZ0EA : IsElemAbelian 2 (X.Z 0) := by
    rw [hZ0eq]
    exact IsElemAbelian.sup_of_commute hNEA (X.caseA_R_elem A).1
      (fun a ha b hb' => X.Z_commute 0 a (hNleZ0 ha) b (hRleZ0 hb'))
  have hZ0comm : IsMulCommutative ↥(X.Z 0) :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (X.Z_commute 0 a.1 a.2 b.1 b.2))
  refine ⟨hNleZ0, ?_, ?_⟩
  · rw [Subgroup.commutator_self_eq_bot_iff.mpr hZ0comm]
    exact bot_le
  · intro z hz
    rw [hZ0EA.2 z hz]
    exact (⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆).one_mem

private theorem caseA_commutator_Z_zero_L_zero_le_sup (X : Setup Γ G) (A : X.CaseA)
    (hb : X.HasB 0 2) (hCL1 : centerOf (X.L 1) = ⁅X.Z 0, X.Z 2⁆)
    (hCLm1 : centerOf (X.L (-1)) = ⁅X.Z 0, X.Z (-2)⁆) :
    ⁅X.Z 0, X.L 0⁆ ≤ ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ := by
  have H := A.hyp
  have hc := H.char
  have hXmleZ0 : ⁅X.Z 0, X.Z (-2)⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_neg_two_le hb).trans inf_le_left
  have hXpleZ0 : ⁅X.Z 0, X.Z 2⁆ ≤ X.Z 0 :=
    (X.commutator_Z_zero_Z_two_le hb).trans inf_le_left
  have hNleZ0 : ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ ≤ X.Z 0 :=
    sup_le hXmleZ0 hXpleZ0
  have hXp_of_Q1 : ⁅X.Z 0, X.Q 1⁆ ≤ ⁅X.Z 0, X.Z 2⁆ :=
    (Subgroup.commutator_mono le_rfl (X.Q_le_edgeSylow 0)).trans
      (le_of_eq (X.commutator_Z_zero_edgeSylow_zero hb))
  have hXm_of_Qm1 : ⁅X.Z 0, X.Q (-1)⁆ ≤ ⁅X.Z 0, X.Z (-2)⁆ :=
    (Subgroup.commutator_mono le_rfl (X.Q_le_edgeSylow_left (-1))).trans
      (le_of_eq (X.commutator_Z_zero_edgeSylow_neg_one hb))
  have hQ0normN : X.Q 0 ≤ Subgroup.normalizer
      ((⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ : Subgroup G) : Set G) :=
    fun q hq => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      fun x hx => (Subgroup.mem_centralizer_iff.mp ((X.Z_le_center 0) (hNleZ0 hx)).2 q hq).symm)
  have hQ1normN := X.caseA_Q_one_le_normalizer_sup A hb hCL1
  have hQm1normN := X.caseA_Q_neg_one_le_normalizer_sup A hb hCLm1
  have hL0 : X.L 0 = (X.Q (-1) ⊔ X.Q 0) ⊔ (X.Q 0 ⊔ X.Q 1) :=
    calc X.L 0 = X.edgeSylow (-1) ⊔ X.edgeSylow 0 := (X.edgeSylow_sup_edgeSylow 0).symm
      _ = (X.Q (-1) ⊔ X.Q 0) ⊔ (X.Q 0 ⊔ X.Q 1) := by
          rw [← X.sup_Q_eq_edgeSylow hc (-1), ← X.sup_Q_eq_edgeSylow hc 0]
          norm_num
  have hZQ0 : ⁅X.Z 0, X.Q 0⁆ ≤ ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((X.Z_le_center 0).trans inf_le_right)]
    exact bot_le
  rw [hL0]
  exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
    (sup_le hQm1normN hQ0normN) (sup_le hQ0normN hQ1normN)
    (CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer hQm1normN hQ0normN
      (hXm_of_Qm1.trans le_sup_left) hZQ0)
    (CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer hQ0normN hQ1normN
      hZQ0 (hXp_of_Q1.trans le_sup_right))
private theorem caseA_false_of_hasB_two
    (X : Setup Γ G) (A : X.CaseA) (hb : X.HasB 0 2)
    (hZ : X.Z 0 ≠ centerOf (X.L 0)) : False := by
  have H := A.hyp
  haveI hLfin : Finite ↥(X.L 0) := finite_of_le_stabilizer X.hyp (X.L_le_Gi 0)
  haveI hQfin : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi 0)
  haveI hZfin : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (X.Z_le_Gi 0)
  obtain ⟨hCL1, hCLm1, hZ0eq, hZ0card, -⟩ := X.caseA_Z_zero_eq_sup_of_hasB_two A hb hZ
  obtain ⟨hsecZQ, hnatZQ⟩ := X.caseA_natQuot_Q_zero_of_hasB_two A hb hZ
  have hcent := X.caseA_commutator_Z_zero_L_zero_le_sup A hb hCL1 hCLm1
  have hNcard := X.caseA_card_commutator_sup A hb hZ
  have hZN := X.caseA_isElemSec_sup_Z_zero A hb hZ0eq
  have hsecNQ : IsElemSec (⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆) (X.Q 0) :=
    isElemSec_of_natQuot_of_comm_le (n := X.n 0) (H.two_le_n 0) (isL2Quot_L X 0)
      (pCoreOf_isPGroup' (X.Gi 0)) hnatZQ hsecZQ hZN hcent
  have hZ1Q0 : X.Z 1 ≤ X.Q 0 := X.Z_le_Q_of_lt A.b₁ (j := 0) (by norm_num)
  have hBm : X.HasB (-1) 2 :=
    (X.hasB_iff_of_even (i := (-1)) (j := 1) (by norm_num) 2).mpr A.b₁
  have hZm1Q0 : X.Z (-1) ≤ X.Q 0 := X.Z_le_Q_of_lt hBm (j := 0) (by norm_num)
  have hRleN : ⁅X.Z (-1), X.Z 1⁆ ≤ ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ :=
    (Subgroup.commutator_mono hZm1Q0 hZ1Q0).trans hsecNQ.2.1
  have hZ0N : X.Z 0 = ⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆ := by
    nth_rewrite 1 [hZ0eq]
    rw [sup_eq_left.mpr hRleN]
  have hcardEq : Nat.card (X.Z 0) =
      Nat.card ↥(⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆) := by
    nth_rewrite 1 [hZ0N]
    rfl
  have hZ0card' : Nat.card (X.Z 0) = 2 ^ (2 * X.n 0 + X.n 1) := hZ0card
  have hNcard' : Nat.card ↥(⁅X.Z 0, X.Z (-2)⁆ ⊔ ⁅X.Z 0, X.Z 2⁆) = 2 ^ (2 * X.n 0) :=
    hNcard
  rw [hZ0card', hNcard'] at hcardEq
  have hexp := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hcardEq
  have := H.two_le_n 1
  omega


private theorem centerOf_L_one_eq_bot_of_Z_zero_eq (X : Setup Γ G) (H : X.Sec4Hyp 7 6)
    (hZ0C : X.Z 0 = centerOf (X.L 0)) : centerOf (X.L 1) = ⊥ := by
  have hc := H.char
  have hZL1Q0 : centerOf (X.L 1) ≤ X.Q 0 := (X.centerOf_L_le_Q_adj hc 0).1
  have hS0Gi0 : IsSylowTwoOf (X.edgeSylow 0) (X.Gi 0) := X.isSylowTwoOf_edgeSylow_Gi 0
  have hZL1leS : centerOf (X.L 1) ≤ X.edgeSylow 0 :=
    hZL1Q0.trans (X.Q_le_edgeSylow_left 0)
  have hZL1C : centerOf (X.L 1) ≤ Subgroup.centralizer (X.edgeSylow 0 : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 s
      ((X.isSylowTwoOf_edgeSylow_L_succ 0).1 hs)
  have hZL1leCenterS : centerOf (X.L 1) ≤ centerOf (X.edgeSylow 0) := le_inf hZL1leS hZL1C
  have hZL1leZ0 : centerOf (X.L 1) ≤ X.Z 0 :=
    hZL1leCenterS.trans (X.centerOf_sylow_le_Z hc 0 hS0Gi0).1
  have h' : centerOf (X.L 0) ⊓ centerOf (X.L 1) = ⊥ := by
    simpa using X.centerOf_L_inf_succ hc 0
  have hle : centerOf (X.L 1) ≤ centerOf (X.L 0) ⊓ centerOf (X.L 1) := by
    refine le_inf ?_ le_rfl
    rw [← hZ0C]
    exact hZL1leZ0
  rw [h'] at hle
  exact le_bot_iff.mp hle

private theorem caseA_Z_zero_eq_R (X : Setup Γ G) (A : X.CaseA)
    (hZ0C : X.Z 0 = centerOf (X.L 0))
    (hrel : relCent (X.Z 1) ⊥ (X.edgeSylow 0) = ⁅X.Z (-1), X.Z 1⁆) :
    X.Z 0 = ⁅X.Z (-1), X.Z 1⁆ := by
  have hc := A.hyp.char
  have hS0Gi1 : IsSylowTwoOf (X.edgeSylow 0) (X.Gi 1) :=
    X.isSylowTwoOf_edgeSylow_Gi_succ 0
  have hZ0leCenterS : X.Z 0 ≤ centerOf (X.edgeSylow 0) := by
    have hZ0leS : X.Z 0 ≤ X.edgeSylow 0 :=
      ((le_of_eq hZ0C).trans (X.centerOf_L_le_Q_adj hc 0).2).trans (X.Q_le_edgeSylow 0)
    refine le_inf hZ0leS ?_
    refine Subgroup.le_centralizer_iff.mpr ?_
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp ((le_of_eq hZ0C) hz)).2 s (X.edgeSylow_le_L 0 hs)).symm
  have hZ0leZ1 : X.Z 0 ≤ X.Z 1 :=
    hZ0leCenterS.trans (X.centerOf_sylow_le_Z hc 1 hS0Gi1).1
  have hZ0rel : X.Z 0 ≤ relCent (X.Z 1) ⊥ (X.edgeSylow 0) := by
    intro z hz
    refine (mem_relCent ?_).mpr ⟨hZ0leZ1 hz, ?_⟩
    · exact fun x _ => mem_normalizer_iff_conjSub.mpr (conjSub_bot x)
    · intro a ha
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp ((le_of_eq hZ0C) hz)).2 a (X.edgeSylow_le_L 0 ha)).symm
  rw [hrel] at hZ0rel
  exact le_antisymm hZ0rel ((X.caseA_3a A).1.trans (le_of_eq hZ0C.symm))

private theorem caseA_not_edgeSylow_zero_le (X : Setup Γ G) (A : X.CaseA) :
    ¬ X.edgeSylow 0 ≤ X.edgeSylow 1 ⊔ X.Z 1 := by
  have H := A.hyp
  have hZ1leS1 : X.Z 1 ≤ X.edgeSylow 1 :=
    (X.Z_le_Q_of_lt A.b₁ (j := 2) (by norm_num)).trans (by simpa using X.Q_le_edgeSylow 1)
  intro hle
  have hsup : X.edgeSylow 1 ⊔ X.Z 1 = X.edgeSylow 1 := sup_eq_left.mpr hZ1leS1
  rw [hsup] at hle
  haveI hS1fin : Finite ↥(X.edgeSylow 1) :=
    finite_of_le_stabilizer X.hyp (H := X.edgeSylow 1)
      ((X.isSylowTwoOf_edgeSylow 1).1.trans inf_le_left)
  have hcard : Nat.card ↥(X.edgeSylow 0) = Nat.card ↥(X.edgeSylow 1) := by
    rw [X.card_edgeSylow_eq 0, X.card_edgeSylow_eq 1]
  have heq : X.edgeSylow 0 = X.edgeSylow 1 :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hL : X.L 1 = X.edgeSylow 0 := by
    rw [← X.edgeSylow_sup_edgeSylow 1]
    show X.edgeSylow 0 ⊔ X.edgeSylow 1 = X.edgeSylow 0
    rw [heq, sup_idem]
  have hpgrp : IsPGroup 2 (X.L 1) := by
    rw [hL]
    exact X.isPGroup_edgeSylow 0
  have hpcL : pCoreOf 2 (X.L 1) = X.L 1 := by
    refine le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl
      Subgroup.le_normalizer hpgrp
  have hQ1eq : X.Q 1 = X.edgeSylow 0 := by
    rw [← X.pCoreOf_L_eq 1, hpcL, hL]
  have hQ1rel : (X.Q 1).relIndex (X.edgeSylow 0) = 1 := by
    rw [hQ1eq, Subgroup.relIndex_self]
  have hrel : (X.Q 1).relIndex (X.edgeSylow 0) = 2 ^ X.n 1 :=
    X.relIndex_Q_succ_edgeSylow 0
  rw [hQ1rel] at hrel
  exact (Nat.one_lt_two_pow (by have := H.two_le_n 1; omega)).ne' hrel.symm

private theorem caseA_commutator_Z_one_edgeSylow_one (X : Setup Γ G) (A : X.CaseA)
    (hZ0R : X.Z 0 = ⁅X.Z (-1), X.Z 1⁆) : ⁅X.Z 1, X.edgeSylow 1⁆ = X.Z 2 := by
  have hedge_conj : conjSub X.τ (X.edgeSylow (-1)) = X.edgeSylow 1 := by
    unfold Setup.edgeSylow
    rw [← pCoreOf_conjSub, conjSub_inf]
    have h1 : conjSub X.τ (X.Gi (-1)) = X.Gi 1 := by
      simpa using (X.Gi_add 1 (-1)).symm
    have h2 : conjSub X.τ (X.Gi ((-1) + 1)) = X.Gi 2 := by
      simpa using (X.Gi_add 1 0).symm
    rw [h1, h2]
    norm_num
  have hS1dec : X.edgeSylow 1 = X.Z 3 ⊔ X.Q 1 := by
    have h := congrArg (conjSub X.τ) (X.caseA_pos A).2
    rw [conjSub_sup] at h
    rw [show conjSub X.τ (X.Z 1) = X.Z 3 from by simpa using (X.Z_add 1 1).symm,
      show conjSub X.τ (X.Q (-1)) = X.Q 1 from by simpa using (X.Q_add 1 (-1)).symm,
      hedge_conj] at h
    exact h.symm
  have hZ3S1 : X.Z 3 ≤ X.edgeSylow 1 := by rw [hS1dec]; exact le_sup_left
  have hQ1normS1 : X.edgeSylow 1 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    ((X.isSylowTwoOf_edgeSylow 1).1.trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hle : ⁅X.Z 1, X.edgeSylow 1⁆ ≤ ⁅X.Z 1, X.Z 3⁆ := by
    rw [hS1dec, Subgroup.commutator_le]
    intro z hz s hs
    obtain ⟨a, ha, b, hb', rfl⟩ := Set.mem_mul.mp
      ((Subgroup.coe_mul_of_left_le_normalizer_right (X.Z 3) (X.Q 1)
        (hZ3S1.trans hQ1normS1)).subset hs)
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hzb : ⁅z, b⁆ = 1 := commutator_eq_one_of_mem_Z_Q X hz hb'
    rw [hzb, mul_one]
    simpa using Subgroup.commutator_mem_commutator hz ha
  have hge : ⁅X.Z 1, X.Z 3⁆ ≤ ⁅X.Z 1, X.edgeSylow 1⁆ :=
    Subgroup.commutator_mono le_rfl hZ3S1
  have heq : ⁅X.Z 1, X.edgeSylow 1⁆ = ⁅X.Z 1, X.Z 3⁆ := le_antisymm hle hge
  rw [heq]
  calc ⁅X.Z 1, X.Z 3⁆ = conjSub X.τ ⁅X.Z (-1), X.Z 1⁆ := by
        have h1 : X.Z 1 = conjSub X.τ (X.Z (-1)) := by
          simpa using X.Z_add 1 (-1)
        have h3 : X.Z 3 = conjSub X.τ (X.Z 1) := by
          simpa using X.Z_add 1 1
        conv_lhs => rw [h1, h3]
        rw [conjSub_commutator]
    _ = conjSub X.τ (X.Z 0) := by rw [← hZ0R]
    _ = X.Z 2 := by simpa using (X.Z_add 1 0).symm

theorem caseA_3 (X : Setup Γ G) (A : X.CaseA) :
    X.HasB 0 3 ∧ X.Z 0 = centerOf (X.L 0) ∧
      X.Z 0 = ⁅X.Z (-1), X.Z 1⁆ ∧
      Nat.card (X.Z 0) = 2 ^ X.n 1 ∧ centerOf (X.L 1) = ⊥ ∧
      NatQuot (X.L 1) (X.Z 1) ⊥ (X.n 1) ∧
      X.Z 1 = X.Z 0 ⊔ X.Z 2 ∧ X.Z 0 ⊓ X.Z 2 = ⊥ := by
  have H := A.hyp
  have hc := H.char
  obtain ⟨_, hBor, h3imp⟩ := X.caseA_Z_zero_le_Q_inf A
  have hZ0C : X.Z 0 = centerOf (X.L 0) := by
    rcases hBor with h3 | h2
    · exact h3imp h3
    · by_contra hne
      exact X.caseA_false_of_hasB_two A h2 hne
  have hZL1bot := X.centerOf_L_one_eq_bot_of_Z_zero_eq H hZ0C
  have hNatZ1 : NatQuot (X.L 1) (X.Z 1) ⊥ (X.n 1) := by
    have h := (X.caseA_3b A).1
    rwa [hZL1bot] at h
  have hS0L1 : IsSylowTwoOf (X.edgeSylow 0) (X.L 1) := X.isSylowTwoOf_edgeSylow_L_succ 0
  have hcommS : relCent (X.Z 1) ⊥ (X.edgeSylow 0) = ⁅X.Z 1, X.edgeSylow 0⁆ := by
    have h := hNatZ1.comm_eq (X.edgeSylow 0) hS0L1
    rw [sup_bot_eq] at h
    exact h.symm
  have hR0eq : ⁅X.Z 1, X.edgeSylow 0⁆ = ⁅X.Z (-1), X.Z 1⁆ := by
    rw [X.edgeSylow_zero]
    exact X.caseA_commutator_Z_one_S A
  have hZ0R := X.caseA_Z_zero_eq_R A hZ0C (hcommS.trans hR0eq)
  have h3 : X.HasB 0 3 := by
    rcases hBor with h3 | h2
    · exact h3
    · exfalso
      have hle : X.Z 0 ≤ X.arcStab (-3) 3 := by
        rw [hZ0R, (X.caseA_3b A).2.2]
        exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
      have hG3 : X.Z 0 ≤ X.Gi 3 :=
        hle.trans (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
      exact h2.2.1 (by simpa using hG3)
  have hS1L1 : IsSylowTwoOf (X.edgeSylow 1) (X.L 1) := X.isSylowTwoOf_edgeSylow_L 1
  have hnot := X.caseA_not_edgeSylow_zero_le A
  have hcommS' : relCent (X.Z 1) ⊥ (X.edgeSylow 1) = ⁅X.Z 1, X.edgeSylow 1⁆ := by
    have h := hNatZ1.comm_eq (X.edgeSylow 1) hS1L1
    rw [sup_bot_eq] at h
    exact h.symm
  have hcommR' := X.caseA_commutator_Z_one_edgeSylow_one A hZ0R
  have hrelS : relCent (X.Z 1) ⊥ (X.edgeSylow 0) = X.Z 0 := by
    rw [hcommS, hR0eq]
    exact hZ0R.symm
  have hrelS' : relCent (X.Z 1) ⊥ (X.edgeSylow 1) = X.Z 2 := by
    rw [hcommS', hcommR']
  obtain ⟨hinf, hsup⟩ := hNatZ1.lines_inf (X.edgeSylow 0) (X.edgeSylow 1)
    hS0L1 hS1L1 hnot
  rw [hrelS, hrelS'] at hinf hsup
  refine ⟨h3, hZ0C, hZ0R, ?_, hZL1bot, hNatZ1, hsup.symm, hinf⟩
  rw [hZ0R]
  exact (X.caseA_3b A).2.1

end Setup

end CFSG.Quasithin.St84
