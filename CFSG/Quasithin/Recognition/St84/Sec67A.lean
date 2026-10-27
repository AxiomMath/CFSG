module

public import CFSG.Quasithin.Recognition.St84.Sec6Z
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuotTransfer
import CFSG.Quasithin.Recognition.St84.Gen.L2SecFaithful

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.QuasithinUnique.Setup.Campbell CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

theorem isElemSec_subgroupOf {G : Type} [Group G] {H Z V : Subgroup G}
    (h : IsElemSec Z V) : IsElemSec (Z.subgroupOf H) (V.subgroupOf H) := by
  refine ⟨fun x hx => h.1 (Subgroup.mem_subgroupOf.mp hx), ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf]
    exact h.2.1 (Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy))
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact h.2.2 _ (Subgroup.mem_subgroupOf.mp hx)

namespace Setup

variable (X : Setup Γ G)

@[expose] def Vone : Subgroup G := ⨆ (g : G) (_ : g ∈ X.Gi 1), conjSub g (X.Z 0)

@[expose] def VnegOne : Subgroup G := ⨆ (g : G) (_ : g ∈ X.Gi (-1)), conjSub g (X.Z 0)

private theorem Vone_eq_iSup_subtype :
    X.Vone = ⨆ g : ↥(X.Gi 1), conjSub (g : G) (X.Z 0) := by
  refine le_antisymm ?_ ?_
  · change (⨆ (g : G) (_ : g ∈ X.Gi 1), conjSub g (X.Z 0)) ≤ _
    refine iSup_le fun g => iSup_le fun hg => ?_
    exact le_iSup (fun g : ↥(X.Gi 1) => conjSub (g : G) (X.Z 0)) ⟨g, hg⟩
  · refine iSup_le fun g => ?_
    change conjSub (g : G) (X.Z 0) ≤
      (⨆ (g : G) (_ : g ∈ X.Gi 1), conjSub g (X.Z 0))
    exact le_iSup₂_of_le (g : G) g.2 le_rfl

theorem Gi_one_le_normalizer_Vone : X.Gi 1 ≤ Subgroup.normalizer (X.Vone : Set G) := by
  rw [X.Vone_eq_iSup_subtype]
  exact CFSG.LocalAnalysis.RankThreeUC.le_normalizer_iSup_conj (X.Gi 1) (X.Z 0)

private theorem reverse_Vone : X.reverse.Vone = X.VnegOne := by
  simp [Setup.Vone, Setup.VnegOne]

theorem Z_le_normalizer_QT (i : ℤ) : X.Z i ≤ M X.QT := by
  intro z hz
  have hzC : z ∈ Subgroup.centralizer (X.Q i : Set G) :=
    (Subgroup.mem_inf.mp (X.Z_le_center i hz)).2
  refine Subgroup.centralizer_le_normalizer (X.QT : Set G) ?_
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro q hq
  exact Subgroup.mem_centralizer_iff.mp hzC q (X.QT_le_Q i hq)

private theorem Q_le_Gi_pred (i : ℤ) : X.Q i ≤ X.Gi (i - 1) :=
  fun _ hx => (X.Q_le_Gi_adj i hx).1

private theorem Q_le_Gi_succ (i : ℤ) : X.Q i ≤ X.Gi (i + 1) :=
  fun _ hx => (X.Q_le_Gi_adj i hx).2

private theorem pCoreOf_L_eq_Q (i : ℤ) : pCoreOf 2 (X.L i) = X.Q i :=
  (X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq

theorem Z_zero_le_E : X.Z 0 ≤ X.E X.QT 0 :=
  le_inf (X.Z_le_Q 0) (X.Z_le_normalizer_QT 0)

private theorem E_QT_le_Q_one (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.E X.QT 0 ≤ X.Q 1 := by
  have hE1 : X.E X.QT 0 ≤ X.Gi 1 :=
    (inf_le_left : X.E X.QT 0 ≤ X.Q 0).trans (by simpa using X.Q_le_Gi_succ 0)
  have hE2 : X.E X.QT 0 ≤ X.Gi 2 :=
    fun _ hx => (X.E_QT_le_Gi_two hGT hs hodd h5 hX hx).1
  have hne : X.vert 0 ≠ X.vert 2 := fun h => by
    have := X.vert_injective h
    omega
  exact le_pCoreOf_of_isPGroup_fixes_two X.hyp
    ((pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left) hE1 (X.adj 0).symm (X.adj 1) hne
    (fun y hy => MulAction.mem_stabilizer_iff.mp (((inf_le_left : X.E X.QT 0 ≤ X.Q 0).trans
      (X.Q_le_Gi 0)) hy))
    (fun y hy => MulAction.mem_stabilizer_iff.mp (hE2 hy))

theorem ZM_le_E_QT (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.ZM ≤ X.E X.QT 0 := by
  obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
  have h3 := X.three_le_m hGT hs hodd h5 hX hreg
  have h4 := X.m_le_four hGT hs hodd h5 hX hreg
  have hm : m = 3 ∨ m = 4 := by omega
  rcases hm with rfl | rfl
  · rw [X.centerOf_eq_QT_of_m_eq_three hGT hs hodd h5 hX hreg rfl]
    exact X.QT_le_E
  · have heq := X.E_minus_inf_E_inf_E_two hGT hs hodd h5 hX hreg rfl
    exact heq ▸ (inf_le_left.trans inf_le_right)

private theorem E_eq_sup_of_not_le_ZM (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)

    (hZ : ¬ X.Z 0 ≤ X.ZM) : X.E X.QT 0 = X.Z 0 ⊔ X.ZM := by
  have hnq := X.natQuot_M hGT hs hodd h5 hX
  have hZ0E : X.Z 0 ≤ X.E X.QT 0 := X.Z_zero_le_E
  have hZME : X.ZM ≤ X.E X.QT 0 := X.ZM_le_E_QT hGT hs hodd h5 hX
  have hL : X.Lst X.QT 0 ≤
      Subgroup.normalizer ((X.Z 0 ⊔ X.ZM : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub l (X.Z 0 ⊔ X.ZM) = X.Z 0 ⊔ X.ZM
    rw [conjSub_sup, X.Z_normal 0 l (X.normGi_le_Gi X.QT 0 (oTwoPrime_le (X.normGi X.QT 0) hl))]
    congr 1
    rw [show X.ZM = centerOf (X.Lst X.QT 0) from rfl]
    exact CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
      (CFSG.Quasithin.E3.normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer hl))
  rcases hnq.irred (X.Z 0 ⊔ X.ZM) le_sup_right (sup_le hZ0E hZME) hL with h | h
  · exact absurd (le_sup_left.trans_eq h) hZ
  · exact h.symm

private theorem Z_zero_le_Etau_one_iff' :
    X.Z 0 ≤ X.Etau 1 ↔ X.Z 0 ≤ X.Gi 3 := by
  constructor
  · intro h
    rw [X.Etau_eq] at h
    exact (h.trans inf_le_left).trans (by simpa using X.Q_le_Gi_succ 2)
  · intro h3
    rw [X.Etau_eq]
    exact le_inf (by simpa using X.Z_le_Q_of_le_Gi 0 3 2 h3 (Or.inr ⟨by norm_num, by norm_num⟩))
      (X.Z_le_normalizer_QT 0)

theorem Z_one_le_E (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Z 1 ≤ X.E X.QT 0 := by
  obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hP : ¬ X.skP X.QT ≤ X.Q 0 ∨ X.n 0 = 2 :=
    Or.inl (X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX)
  have hV : ⁅X.E X.QT 0, X.Yst X.QT 0⁆ ≠ ⊥ :=
    X.commutator_E_Yst_ne_bot hGT hs hodd h5 hX hreg
  have hchar := X.charTwo_Lst hSK (hP.imp_right Eq.ge) hV
  have hZ1L : X.Z 1 ≤ X.Lst X.QT 0 := by
    refine le_oTwoPrime_of_isPGroup
      ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)) ?_
    exact le_inf (X.Z_le_normalizer_QT 1) ((X.Z_le_Q 1).trans (by simpa using X.Q_le_Gi_pred 1))
  have hEQ1 : X.E X.QT 0 ≤ X.Q 1 := X.E_QT_le_Q_one hGT hs hodd h5 hX
  have hpL : pCoreOf 2 (X.Lst X.QT 0) ≤ X.E X.QT 0 :=
    (X.pCoreOf_Lst_eq_E hSK).le
  have hZ1C : X.Z 1 ≤ Subgroup.centralizer (X.E X.QT 0 : Set G) := by
    intro z hz
    refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
    have hzC : z ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2
    exact Subgroup.mem_centralizer_iff.mp hzC e (hEQ1 he)
  have hmem : X.Z 1 ≤ X.Lst X.QT 0 ⊓
      Subgroup.centralizer (pCoreOf 2 (X.Lst X.QT 0) : Set G) :=
    le_inf hZ1L (hZ1C.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hpL)))
  exact (hmem.trans hchar).trans hpL

theorem Z_zero_le_Etau_one_iff (hb : ¬ X.Z 0 ≤ X.Gi 3) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Z 0 ≤ X.Etau 1 ↔ X.Z 0 ≤ X.Gi 3 :=
  X.Z_zero_le_Etau_one_iff'

theorem not_Z_zero_le_Etau_one (hb : ¬ X.Z 0 ≤ X.Gi 3) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ¬ X.Z 0 ≤ X.Etau 1 :=
  fun h => hb ((X.Z_zero_le_Etau_one_iff hb hGT hs hodd h5 hX).mp h)

theorem not_Z_zero_le_ZM (hb : ¬ X.Z 0 ≤ X.Gi 3) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ¬ X.Z 0 ≤ X.ZM :=
  fun hZM => X.not_Z_zero_le_Etau_one hb hGT hs hodd h5 hX
    (hZM.trans (X.ZM_le_Etau_one hGT hs hodd h5 hX))

theorem E_eq_Z_zero_sup_ZM (hb : ¬ X.Z 0 ≤ X.Gi 3) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.E X.QT 0 = X.Z 0 ⊔ X.ZM :=
  X.E_eq_sup_of_not_le_ZM hGT hs hodd h5 hX
    (X.not_Z_zero_le_ZM hb hGT hs hodd h5 hX)

theorem commutator_Lst_E_le (hb : ¬ X.Z 0 ≤ X.Gi 3) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.Lst X.QT 0, X.E X.QT 0⁆ ≤ X.Z 0 := by
  rw [Subgroup.commutator_le]
  intro l hl e he
  rw [X.E_eq_Z_zero_sup_ZM hb hGT hs hodd h5 hX] at he
  have hcommE : ∀ a ∈ X.Z 0, ∀ b ∈ X.ZM, a * b = b * a := by
    have hEA := X.isElemAbelian_E_QT hGT hs hodd h5 hX
    intro a ha b hbm
    haveI : IsMulCommutative ↥(X.E X.QT 0) := hEA.1
    have ha' : a ∈ X.E X.QT 0 := X.Z_zero_le_E ha
    have hb' : b ∈ X.E X.QT 0 := X.ZM_le_E_QT hGT hs hodd h5 hX hbm
    exact congrArg Subtype.val (mul_comm' ⟨a, ha'⟩ ⟨b, hb'⟩)
  rw [CFSG.QuasithinUnique.BenderBranch.mem_sup_iff_of_commute hcommE] at he
  obtain ⟨z, hz, m, hm, rfl⟩ := he
  have hlG0 : l ∈ X.Gi 0 := (X.normGi_le_Gi X.QT 0 (oTwoPrime_le (X.normGi X.QT 0) hl))
  have hmL : m ∈ X.Lst X.QT 0 := (Subgroup.mem_inf.mp hm).1
  have hmC : l * m = m * l :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hm).2 l hl
  have hlz : ⁅l, z⁆ ∈ X.Z 0 := by
    have hZl : conjSub l⁻¹ (X.Z 0) = X.Z 0 := by
      rw [← X.Z_normal 0 l hlG0, conjSub_conjSub_inv, X.Z_normal 0 l hlG0]
    have hmem : z ∈ conjSub l⁻¹ (X.Z 0) := by rw [hZl]; exact hz
    have hz' : l * z * l⁻¹ ∈ X.Z 0 := by simpa using mem_conjSub.mp hmem
    have heq : ⁅l, z⁆ = (l * z * l⁻¹) * z⁻¹ := rfl
    rw [heq]
    exact (X.Z 0).mul_mem hz' ((X.Z 0).inv_mem hz)
  have hcomm : ⁅l, m⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hmC
  have hcalc : ⁅l, z * m⁆ = ⁅l, z⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, hcomm]
    group
  rw [hcalc]
  exact hlz

private theorem Lst_conj_mem_Z_sup (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)

    {l : G} (hl : l ∈ X.Lst X.QT 0) {x : G} (hx : x ∈ X.Z 1 ⊔ X.Z 0) :
    l * x * l⁻¹ ∈ X.Z 1 ⊔ X.Z 0 := by
  have hlG0 : l ∈ X.Gi 0 := (X.normGi_le_Gi X.QT 0 (oTwoPrime_le (X.normGi X.QT 0) hl))
  have hZl : conjSub l⁻¹ (X.Z 0) = X.Z 0 := by
    rw [← X.Z_normal 0 l hlG0, conjSub_conjSub_inv, X.Z_normal 0 l hlG0]
  have hcomm : ∀ a ∈ X.Z 1, ∀ b ∈ X.Z 0, a * b = b * a := by
    have hEA := X.isElemAbelian_E_QT hGT hs hodd h5 hX
    intro a ha b hbm
    haveI : IsMulCommutative ↥(X.E X.QT 0) := hEA.1
    have ha' : a ∈ X.E X.QT 0 := X.Z_one_le_E hGT hs hodd h5 hX ha
    have hb' : b ∈ X.E X.QT 0 := X.Z_zero_le_E hbm
    exact congrArg Subtype.val (mul_comm' ⟨a, ha'⟩ ⟨b, hb'⟩)
  rw [CFSG.QuasithinUnique.BenderBranch.mem_sup_iff_of_commute hcomm] at hx ⊢
  obtain ⟨a, ha, b, hbm, rfl⟩ := hx
  have hcom : ⁅l, a⁆ ∈ X.Z 0 :=
    Subgroup.commutator_le.mp (X.commutator_Lst_E_le hb hGT hs hodd h5 hX) l hl a
      (X.Z_one_le_E hGT hs hodd h5 hX ha)
  have hca : l * a * l⁻¹ = a * ⁅l, a⁆ := by
    have h1 : l * a * l⁻¹ = ⁅l, a⁆ * a := by
      rw [commutatorElement_def]; group
    rw [h1, hcomm a ha ⁅l, a⁆ hcom]
  have hcb : l * b * l⁻¹ ∈ X.Z 0 := by
    have hmem : b ∈ conjSub l⁻¹ (X.Z 0) := by rw [hZl]; exact hbm
    simpa using mem_conjSub.mp hmem
  refine ⟨a, ha, ⁅l, a⁆ * (l * b * l⁻¹), (X.Z 0).mul_mem hcom hcb, ?_⟩
  calc a * (⁅l, a⁆ * (l * b * l⁻¹)) = (a * ⁅l, a⁆) * (l * b * l⁻¹) := by group
    _ = (l * a * l⁻¹) * (l * b * l⁻¹) := by rw [hca]
    _ = l * (a * b) * l⁻¹ := by group

private theorem Lst_le_normalizer_Z_sup (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Lst X.QT 0 ≤ Subgroup.normalizer ((X.Z 1 ⊔ X.Z 0 : Subgroup G) : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact X.Lst_conj_mem_Z_sup hb hGT hs hodd h5 hX hl
  · intro hx
    have h := X.Lst_conj_mem_Z_sup hb hGT hs hodd h5 hX
      ((X.Lst X.QT 0).inv_mem hl) hx
    have heq : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
    rwa [heq] at h

theorem Z_one_sup_Z_zero_normal (hb : ¬ X.Z 0 ≤ X.Gi 3) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Gi 0 ≤ Subgroup.normalizer ((X.Z 1 ⊔ X.Z 0 : Subgroup G) : Set G) := by
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hP : ¬ X.skP X.QT ≤ X.Q 0 ∨ X.n 0 = 2 :=
    Or.inl (X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX)
  rw [X.Gi_eq_L_sup_K 0]
  refine sup_le ?_ ?_
  · rw [X.L_eq_Lst_sup_Q hSK (hP.imp_right Eq.ge)]
    refine sup_le (X.Lst_le_normalizer_Z_sup hb hGT hs hodd h5 hX) ?_
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub q (X.Z 1 ⊔ X.Z 0) = X.Z 1 ⊔ X.Z 0
    rw [conjSub_sup, X.Z_normal 1 q (by simpa using (X.Q_le_Gi_succ 0) hq),
      X.Z_normal 0 q (X.Q_le_Gi 0 hq)]
  · intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k (X.Z 1 ⊔ X.Z 0) = X.Z 1 ⊔ X.Z 0
    rw [conjSub_sup, X.Z_normal 1 k (X.K_le_Gi 1 hk), X.Z_normal 0 k (X.K_le_Gi 0 hk)]

private theorem Z_zero_le_Q_one_aux (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Z 0 ≤ X.Q 1 := by
  have hZ0E : X.Z 0 ≤ X.E X.QT 0 := X.Z_zero_le_E
  exact X.Z_le_Q_of_le_Gi 0 2 1
    (hZ0E.trans fun _ hx => (X.E_QT_le_Gi_two hGT hs hodd h5 hX hx).1)
    (Or.inr ⟨by norm_num, by norm_num⟩)

theorem Z_zero_le_Q_one (hb : ¬ X.Z 0 ≤ X.Gi 3) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1 ∨ X.n 0 = 2) (hn1 : X.n 1 = 1 ∨ X.n 1 = 2) :
    X.Z 0 ≤ X.Q 1 :=
  X.Z_zero_le_Q_one_aux hGT hs hodd h5 hX

theorem Z_zero_le_Q_neg_one (hb : ¬ X.Z 0 ≤ X.Gi 3) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Z 0 ≤ X.Q (-1) := by
  have hZ0E : X.Z 0 ≤ X.E X.QT 0 := X.Z_zero_le_E
  exact X.Z_le_Q_of_le_Gi 0 (-2) (-1)
    (hZ0E.trans fun _ hx => (X.E_QT_le_Gi_two hGT hs hodd h5 hX hx).2)
    (Or.inr ⟨by norm_num, by norm_num⟩)

theorem not_Z_zero_le_Gi_neg_three (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hs : IsSingularity Γ G s) (h5 : 5 ≤ s) : ¬ X.Z 0 ≤ X.Gi (-3) := by
  intro h
  have hfix : X.Z 0 ≤ MulAction.stabilizer G (X.vert (-3)) := by
    rwa [← Setup.Gi]
  have hd3 : Γ.dist (X.vert 0) (X.vert (-3)) = 3 := by
    rw [SimpleGraph.dist_comm]
    have hh := Line.dist_eq X.hyp.isTree X.line (i := (-3 : ℤ)) (j := 0) (by norm_num)
    simpa using hh
  have hfix3 : X.Z 0 ≤ MulAction.stabilizer G (X.vert 3) := by
    refine X.Z_fixes_of_dist 0 hs (by omega) hd3 hfix (X.vert 3) ?_
    rw [Line.dist_eq X.hyp.isTree X.line (i := (0 : ℤ)) (j := 3) (by norm_num)]
    norm_num
  exact hb (by rwa [← Setup.Gi] at hfix3)

theorem Z_two_not_le_Q_zero (hb : ¬ X.Z 0 ≤ X.Gi 3) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ¬ X.Z 2 ≤ X.Q 0 := by
  intro h
  have hZ0Q : X.Z 0 ≤ X.Q (-2) := by
    have hc := conjSub_mono (X.τ ^ (-1 : ℤ)) h
    rw [← X.Z_add (-1) 2, ← X.Q_add (-1) 0] at hc
    simpa using hc
  exact X.not_Z_zero_le_Gi_neg_three hb hs h5
    (hZ0Q.trans (by simpa using X.Q_le_Gi_pred (-2)))

private theorem Q_zero_le_L_one : X.Q 0 ≤ X.L 1 :=
  (X.Q_le_edgeSylow_left 0).trans (X.isSylowTwoOf_edgeSylow_L_succ 0).1

private theorem Q_zero_inf_one_eq_centralizer (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)

    (hC : X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) = X.Q 1) :
    X.Q 0 ⊓ X.Q 1 =
      X.Q 0 ⊓ Subgroup.centralizer ((X.Z 1 ⊔ X.Z 0 : Subgroup G) : Set G) := by
  have hEA := X.isElemAbelian_E_QT hGT hs hodd h5 hX
  have hZ0E : X.Z 0 ≤ X.E X.QT 0 := X.Z_zero_le_E
  have hZ1E : X.Z 1 ≤ X.E X.QT 0 := X.Z_one_le_E hGT hs hodd h5 hX
  have hcomm01 : ∀ a ∈ X.Z 1, ∀ b ∈ X.Z 0, a * b = b * a := by
    intro a ha b hbm
    haveI : IsMulCommutative ↥(X.E X.QT 0) := hEA.1
    exact congrArg Subtype.val (mul_comm' ⟨a, hZ1E ha⟩ ⟨b, hZ0E hbm⟩)
  refine le_antisymm ?_ ?_
  · refine le_inf inf_le_left ?_
    intro q hq
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro x hx
    obtain ⟨a, ha, b, hbm, rfl⟩ :=
      (CFSG.QuasithinUnique.BenderBranch.mem_sup_iff_of_commute hcomm01).mp hx
    have hqa : q * a = a * q := by
      have hmem : a ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
        (Subgroup.mem_inf.mp (X.Z_le_center 1 ha)).2
      exact (Subgroup.mem_centralizer_iff.mp hmem q hq.2)
    have hqb : q * b = b * q := by
      have hmem : b ∈ Subgroup.centralizer (X.Q 0 : Set G) :=
        (Subgroup.mem_inf.mp (X.Z_le_center 0 hbm)).2
      exact (Subgroup.mem_centralizer_iff.mp hmem q hq.1)
    exact (calc q * (a * b) = (q * a) * b := by group
      _ = (a * q) * b := by rw [hqa]
      _ = a * (q * b) := by group
      _ = a * (b * q) := by rw [hqb]
      _ = (a * b) * q := by group).symm
  · refine le_inf inf_le_left ?_
    intro q hq
    have hqC : ∀ x ∈ X.Z 1 ⊔ X.Z 0, x * q = q * x :=
      Subgroup.mem_centralizer_iff.mp hq.2
    have hq1c : q ∈ Subgroup.centralizer (X.Z 1 : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro z hz
      exact hqC z (Subgroup.mem_sup_left hz)
    have hqL : q ∈ X.L 1 := X.Q_zero_le_L_one hq.1
    have hmem : q ∈ X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) := ⟨hqL, hq1c⟩
    rwa [hC] at hmem

private theorem Q_zero_inf_one_normal (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)

    (hC : X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) = X.Q 1) :
    X.Gi 0 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 1 : Subgroup G) : Set G) := by
  have hQ01C := X.Q_zero_inf_one_eq_centralizer hb hGT hs hodd h5 hX hC
  have hZsup : ∀ g ∈ X.Gi 0, conjSub g (X.Z 1 ⊔ X.Z 0) = X.Z 1 ⊔ X.Z 0 := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (X.Z_one_sup_Z_zero_normal hb hGT hs hodd h5 hX hg)
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub g (X.Q 0 ⊓ X.Q 1) = X.Q 0 ⊓ X.Q 1
  rw [hQ01C, conjSub_inf, ← conjSub_centralizer, hZsup g hg]
  have hQ0n : conjSub g (X.Q 0) = X.Q 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)) hg)
  rw [hQ0n]

private theorem Q_zero_inf_one_eq_Q_one_inf_neg_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)

    (hC : X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) = X.Q 1) :
    X.Q 0 ⊓ X.Q 1 = X.Q 1 ⊓ X.Q (-1) := by
  have hQ01_normal := X.Q_zero_inf_one_normal hb hGT hs hodd h5 hX hC
  have hb1 : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    simpa using (X.adj (-1)).symm
  obtain ⟨g0, hg0G0, hg0⟩ := X.hyp.locTrans (X.adj 0) hb1
  have hG1 : conjSub g0 (X.Gi 1) = X.Gi (-1) := by
    rw [← stabilizer_smul_eq_conjSub g0 (X.vert 1)]
    change MulAction.stabilizer G (g0 • X.vert 1) = MulAction.stabilizer G (X.vert (-1))
    rw [show g0 • X.vert 1 = X.vert (-1) by simpa using hg0]
  have hQ0n : conjSub g0 (X.Q 0) = X.Q 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)) hg0G0)
  have hQ1n : conjSub g0 (X.Q 1) = X.Q (-1) := by
    unfold Setup.Q
    rw [← pCoreOf_conjSub, hG1]
  have hconjQ : conjSub g0 (X.Q 0 ⊓ X.Q 1) = X.Q 0 ⊓ X.Q (-1) := by
    rw [conjSub_inf, hQ0n, hQ1n]
  have hQ0m1 : X.Q 0 ⊓ X.Q (-1) = X.Q 0 ⊓ X.Q 1 := by
    rw [← hconjQ]
    simpa [conjSub] using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQ01_normal hg0G0))
  have hQ1m1_le_Q0 : X.Q 1 ⊓ X.Q (-1) ≤ X.Q 0 :=
    (inf_comm (X.Q 1) (X.Q (-1))).le.trans X.Q_neg_one_inf_Q_one_le_Q_zero
  have hQ01_le_Q1m1 : X.Q 0 ⊓ X.Q 1 ≤ X.Q 1 ⊓ X.Q (-1) :=
    le_inf inf_le_right ((le_of_eq hQ0m1.symm).trans inf_le_right)
  exact le_antisymm hQ01_le_Q1m1 (le_inf hQ1m1_le_Q0 inf_le_left)

private theorem sup_le_arcStab_neg_one_two :
    X.K ⊔ (X.Q 0 ⊓ X.Q 1) ≤ X.arcStab (-1) 2 := by
  have hKarc : X.K ≤ X.arcStab (-1) 2 := X.K_le_GT.trans (X.GT_le_arcStab (-1) 2)
  refine sup_le hKarc ?_
  intro q hq
  exact Fan86.mem_fixSet.mpr (by
    rintro v ⟨i, hi, rfl⟩
    rw [Set.mem_Icc] at hi
    have hi' : i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl | rfl | rfl
    · exact MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi_pred 0 hq.1)
    · exact MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi 0 hq.1)
    · exact MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi_succ 0 hq.1)
    · exact MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi_succ 1 hq.2))

private theorem arcStab_neg_one_two_eq_sup :
    X.arcStab (-1) 2 = X.K ⊔ (X.Q 0 ⊓ X.Q 1) := by
  have hKarc : X.K ≤ X.arcStab (-1) 2 := X.K_le_GT.trans (X.GT_le_arcStab (-1) 2)
  have hArc_le : X.arcStab (-1) 2 ≤ X.Gi (-1) ⊓ X.Gi 0 :=
    le_inf (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
      (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
  obtain ⟨-, hsup⟩ := X.pCoreOf_eq_inf_edgeSylow (-1) hKarc hArc_le
  have hR := X.pCoreOf_arcStab_neg_one_two_le_Q_zero_inf_Q_one
  refine le_antisymm ?_ X.sup_le_arcStab_neg_one_two
  rw [← hsup]
  exact sup_le le_sup_left (hR.trans le_sup_right)

theorem centralizer_L_one_Z_one_ne_Q_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) ≠ X.Q 1 := by
  intro hC
  have hQ01_eq := X.Q_zero_inf_one_eq_Q_one_inf_neg_one hb hGT hs hodd h5 hX hC
  have hArc_eq := X.arcStab_neg_one_two_eq_sup
  have hfix2 : X.arcStab (-1) 2 ≤ X.Gi (-2) := by
    rw [hArc_eq]
    refine sup_le ?_ ?_
    · intro k hk
      exact MulAction.mem_stabilizer_iff.mpr (X.K_fix k hk (-2))
    · intro q hq
      have hq1 : q ∈ X.Q 1 ⊓ X.Q (-1) := hQ01_eq ▸ hq
      exact MulAction.mem_stabilizer_iff.mpr (X.Q_le_Gi_pred (-1) hq1.2)
  obtain ⟨hLt, -⟩ := X.trans_of_lt hs (-1) (k := 3) (by norm_num) (by omega)
  have h3 : 3 ≤ (Γ.neighborSet (X.vert (-1))).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact X.hyp.three_le_card (X.vert (-1))
  have hne20 : X.vert (-2) ≠ X.vert 0 := by
    intro h
    have := X.vert_injective h
    omega
  have hpair : ({X.vert (-2), X.vert 0} : Set V).ncard = 2 := Set.ncard_pair hne20
  obtain ⟨b, hbAdj, hbnot⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := ({X.vert (-2), X.vert 0} : Set V))
      (t := Γ.neighborSet (X.vert (-1))) (by rw [hpair]; omega)
  rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hbnot
  obtain ⟨hbne2, hbne0⟩ := hbnot
  have haAdj : Γ.Adj (X.vert (-1)) (X.vert (-2)) := by
    simpa using (X.adj (-2)).symm
  obtain ⟨g, hgArc, hg⟩ := hLt (X.vert (-2)) b haAdj (by simpa using hne20) hbAdj hbne0
  have hgfix : g • X.vert (-2) = X.vert (-2) :=
    MulAction.mem_stabilizer_iff.mp (hfix2 hgArc)
  exact hbne2 (hg.symm.trans hgfix)

private theorem center_le_of_center_quot_eq_bot {H : Type*} [Group H] {N : Subgroup H}
    [N.Normal] (h : Subgroup.center (H ⧸ N) = ⊥) : Subgroup.center H ≤ N := by
  rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff, eq_bot_iff, ← h]
  exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)

private theorem perm3_normal_index_le_two {N : Subgroup (Equiv.Perm (Fin 3))} [N.Normal]
    (hN : N ≠ ⊥) : N.index ≤ 2 := by
  have h := Subgroup.index_dvd_of_le (CFSG.Quasithin.F53.normal_ge_alt3 N hN)
  rw [alternatingGroup.index_eq_two] at h
  exact Nat.le_of_dvd two_pos h

private theorem isL2Quot_one_normal_index_le_two {H : Type*} [Group H] [Finite H]
    (hH : IsL2Quot 1 H) {N : Subgroup H} [N.Normal] (hN : N ≠ ⊥) : N.index ≤ 2 := by
  obtain ⟨e⟩ := CFSG.Quasithin.isL2Quot_one_iff_perm3.mp hH
  haveI hN'map : (N.map (e : H →* Equiv.Perm (Fin 3))).Normal :=
    Subgroup.Normal.map (inferInstance : N.Normal) (e : H →* Equiv.Perm (Fin 3)) e.surjective
  have hN' : N.map (e : H →* Equiv.Perm (Fin 3)) ≠ ⊥ := fun hbot =>
    hN ((Subgroup.map_eq_bot_iff_of_injective (H := N)
      (f := (e : H →* Equiv.Perm (Fin 3))) e.injective).mp hbot)
  have hidx := perm3_normal_index_le_two (N := N.map (e : H →* Equiv.Perm (Fin 3))) hN'
  have hidxeq : (N.map (e : H →* Equiv.Perm (Fin 3))).index = N.index :=
    Subgroup.index_map_equiv (H := N) e
  rwa [hidxeq] at hidx

private theorem Q_one_le_L_one_inf_centralizer :
    X.Q 1 ≤ X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) := by
  have hN : IsLocL2 Γ G (X.vert 1) (X.n 1) (X.L 1) := X.hyp.isLocL2_oTwoPrime (X.vert 1)
  refine le_inf hN.oTwo_le ?_
  intro q hq
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2 q hq).symm

private theorem L_one_le_normalizer_L_one_inf_centralizer :
    X.L 1 ≤ Subgroup.normalizer
      ((X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) : Subgroup G) : Set G) := by
  have hCZ : X.Gi 1 ≤ Subgroup.normalizer (Subgroup.centralizer (X.Z 1 : Set G)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g (Subgroup.centralizer (X.Z 1 : Set G)) =
      Subgroup.centralizer (X.Z 1 : Set G)
    have hconj : conjSub g (X.Z 1) = X.Z 1 := X.Z_normal 1 g hg
    rw [← conjSub_centralizer, hconj]
  exact CFSG.Quasithin.F7.le_normalizer_inf (Subgroup.le_normalizer)
    ((X.L_le_Gi 1).trans hCZ)

private theorem eq_or_relIndex_eq_two_of_le_normalizer {v : V} {n : ℕ} {L C : Subgroup G}
    [Finite ↥L] (hN : IsLocL2 Γ G v n L) (hn : 1 ≤ n) (hCL : C ≤ L)
    (hLC : L ≤ Subgroup.normalizer (C : Set G)) (hPC : pCoreOf 2 L ≤ C)
    (hne : C ≠ pCoreOf 2 L) : C = L ∨ C.relIndex L = 2 := by
  haveI : Finite (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hCsub_normal : (C.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLC
  have hpcore : CFSG.pCore 2 ↥L = (pCoreOf 2 L).subgroupOf L :=
    (CFSG.openPCoreOf_subgroupOf 2 L).symm
  have hker_le : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ≤ C.subgroupOf L := by
    rw [QuotientGroup.ker_mk', hpcore]
    exact Subgroup.subgroupOf_mono L hPC
  set Nim : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (C.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hNimdef
  haveI hNim_normal : Nim.Normal :=
    hCsub_normal.map _ (QuotientGroup.mk'_surjective _)
  have hNim_ne : Nim ≠ ⊥ := by
    intro hbot
    apply hne
    have hle : C.subgroupOf L ≤ CFSG.pCore 2 ↥L := by
      have h := Subgroup.map_le_iff_le_comap.mp (show Nim ≤ ⊥ from le_of_eq hbot)
      rwa [MonoidHom.comap_bot, QuotientGroup.ker_mk'] at h
    refine le_antisymm ?_ hPC
    intro c hc
    have hcL : c ∈ L := hCL hc
    have hcm : (⟨c, hcL⟩ : ↥L) ∈ C.subgroupOf L := Subgroup.mem_subgroupOf.mpr hc
    have hpc : (⟨c, hcL⟩ : ↥L) ∈ (pCoreOf 2 L).subgroupOf L := by
      rw [← hpcore]
      exact hle hcm
    simpa using Subgroup.mem_subgroupOf.mp hpc
  have hidxrel : Nim.index = C.relIndex L := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_map_eq (H := C.subgroupOf L)
      (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _) hker_le
  have hCtop_of_top (htop : Nim = ⊤) : C = L := by
    have htop' : Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (C.subgroupOf L) = ⊤ := by
      rw [← hNimdef]
      exact htop
    have hCsubtop : C.subgroupOf L = ⊤ := by
      have h := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L)) hker_le
      rw [htop', Subgroup.comap_top] at h
      exact h.symm
    refine le_antisymm hCL ?_
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥L) ∈ C.subgroupOf L := by
      rw [hCsubtop]
      exact Subgroup.mem_top _
    simpa [Subgroup.mem_subgroupOf] using hx'
  obtain ⟨e⟩ := hN.quot
  rcases eq_or_lt_of_le hn with h1 | h2
  · have hIsL2 : IsL2Quot 1 (↥L ⧸ CFSG.pCore 2 ↥L) := by
      have hq := hN.quot
      rwa [← h1] at hq
    have hidx := isL2Quot_one_normal_index_le_two hIsL2 hNim_ne
    rcases eq_or_ne Nim ⊤ with htop | hne'
    · exact Or.inl (hCtop_of_top htop)
    · refine Or.inr ?_
      have hidx2 : Nim.index = 2 := by
        have hpos : 0 < Nim.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
        have hne1 : Nim.index ≠ 1 := fun h => hne' (Subgroup.index_eq_one.mp h)
        omega
      rw [← hidxrel]
      exact hidx2
  · have hn2 : 2 ≤ n := by omega
    have hcardF : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [GaloisField.card (p := 2) (n := n) (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcardF
    haveI : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e.isSimpleGroup
    have htop : Nim = ⊤ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top Nim with h | h
      · exact absurd h hNim_ne
      · exact h
    exact Or.inl (hCtop_of_top htop)

theorem centralizer_eq_top_or_index_two_of_ne
    (hne : X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) ≠ X.Q 1) :
    X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) = X.L 1 ∨
      (X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G)).relIndex (X.L 1) = 2 := by
  have hN : IsLocL2 Γ G (X.vert 1) (X.n 1) (X.L 1) := X.hyp.isLocL2_oTwoPrime (X.vert 1)
  haveI : Finite ↥(X.L 1) := finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  have hne' : X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) ≠ pCoreOf 2 (X.L 1) := by
    rw [X.pCoreOf_L_eq_Q 1]
    exact hne
  exact eq_or_relIndex_eq_two_of_le_normalizer hN (X.hyp.valency (X.vert 1)).1 inf_le_left
    X.L_one_le_normalizer_L_one_inf_centralizer
    ((X.pCoreOf_L_eq_Q 1).le.trans X.Q_one_le_L_one_inf_centralizer) hne'

theorem Z_one_le_centerOf_L_one_of_ne
    (hne : X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) ≠ X.Q 1) : X.Z 1 ≤ centerOf (X.L 1) := by
  have hN : IsLocL2 Γ G (X.vert 1) (X.n 1) (X.L 1) := X.hyp.isLocL2_oTwoPrime (X.vert 1)
  set C : Subgroup G := X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) with hCdef
  have hCbig : C = X.L 1 ∨ C.relIndex (X.L 1) = 2 := by
    simpa only [hCdef] using X.centralizer_eq_top_or_index_two_of_ne hne
  have hZ1L : X.Z 1 ≤ X.L 1 := (X.Z_le_Q 1).trans hN.oTwo_le
  refine le_inf hZ1L ?_
  refine iSup_le fun S => iSup_le fun hS => ?_
  intro z hz
  obtain ⟨hzS, hzQ⟩ := Subgroup.mem_inf.mp hz
  have hzZ : z ∈ X.Z 1 :=
    X.le_Z_of_le_centerOf_sylow 1 hS inf_le_left inf_le_right hz
  have hS2 : S ≤ X.L 1 := le_oTwoPrime_of_isPGroup hS.2.1 hS.1
  have hoddS : ¬ 2 ∣ S.relIndex (X.L 1) := by
    intro h2dvd
    have hmul := Subgroup.relIndex_mul_relIndex S (X.L 1) (X.Gi 1) hS2 (X.L_le_Gi 1)
    exact CFSG.Quasithin.F7.isSylowTwoOf_odd_relIndex hS (by
      rw [← hmul]
      exact dvd_mul_of_dvd_left h2dvd _)
  have hCS : C ⊔ S = X.L 1 := by
    rcases hCbig with hCL | hidx2
    · rw [hCL]
      exact sup_eq_left.mpr hS2
    · have hSnotC : ¬ S ≤ C := by
        intro hSC
        apply hoddS
        have hmul := Subgroup.relIndex_mul_relIndex S C (X.L 1) hSC
          (show C ≤ X.L 1 from inf_le_left)
        rw [← hmul, show C.relIndex (X.L 1) = 2 from hidx2]
        exact dvd_mul_left 2 (S.relIndex C)
      have hne1 : C.relIndex (C ⊔ S) ≠ 1 := fun h1 =>
        hSnotC (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1))
      have hmul := Subgroup.relIndex_mul_relIndex C (C ⊔ S) (X.L 1)
        (le_sup_left : C ≤ C ⊔ S) (sup_le (show C ≤ X.L 1 from inf_le_left) hS2)
      have hmul2 : 2 = C.relIndex (C ⊔ S) * (C ⊔ S).relIndex (X.L 1) := by
        rw [hmul, hidx2]
      have hb1 : (C ⊔ S).relIndex (X.L 1) = 1 := by
        have ha_dvd : C.relIndex (C ⊔ S) ∣ 2 := ⟨_, hmul2⟩
        rcases (Nat.dvd_prime Nat.prime_two).mp ha_dvd with ha | ha
        · exact absurd ha hne1
        · rw [ha] at hmul2
          omega
      exact le_antisymm (sup_le inf_le_left hS2) (Subgroup.relIndex_eq_one.mp hb1)
  have hsub : X.L 1 ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← hCS]
    refine sup_le ?_ ?_
    · intro c hcL
      have hcC : c ∈ Subgroup.centralizer (X.Z 1 : Set G) :=
        (Subgroup.mem_inf.mp (show c ∈ X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G)
          from hcL)).2
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst w
      exact Subgroup.mem_centralizer_iff.mp hcC z hzZ
    · intro s hsS
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst w
      exact (Subgroup.mem_centralizer_iff.mp hzS.2 s hsS).symm
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (hsub hl) z rfl).symm

private theorem centerOf_le_pCoreOf_of_isLocL2 {v : V} {n : ℕ} {L : Subgroup G}
    (hN : IsLocL2 Γ G v n L) : centerOf L ≤ pCoreOf 2 L := by
  intro z hz
  obtain ⟨hzL, hzc⟩ := Subgroup.mem_inf.mp hz
  have hcent_quot : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    obtain ⟨e⟩ := hN.quot
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : e x ∈ Subgroup.center
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨w, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg e (hx w)
    rw [CFSG.Quasithin.St84.psl2_center_eq_bot] at hx'
    have h1 : e x = 1 := by simpa using hx'
    exact e.injective (by rw [h1, map_one])
  have hcenter : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzc (y : G) y.2
  have hpc := center_le_of_center_quot_eq_bot hcent_quot hcenter
  rw [← CFSG.openPCoreOf_subgroupOf 2 L] at hpc
  exact Subgroup.mem_subgroupOf.mp hpc

private theorem centerOf_L_one_le_Z_one : centerOf (X.L 1) ≤ X.Z 1 := by
  have hN : IsLocL2 Γ G (X.vert 1) (X.n 1) (X.L 1) := X.hyp.isLocL2_oTwoPrime (X.vert 1)
  have hQeq : X.Q 1 = pCoreOf 2 (X.L 1) := (X.pCoreOf_L_eq_Q 1).symm
  intro z hz
  obtain ⟨-, hzc⟩ := Subgroup.mem_inf.mp hz
  have hzmem : z ∈ pCoreOf 2 (X.L 1) :=
    centerOf_le_pCoreOf_of_isLocL2 (n := X.n 1) (L := X.L 1) hN hz
  have hzQ : z ∈ X.Q 1 := by
    rw [hQeq]
    exact hzmem
  have hS_syl : IsSylowTwoOf (X.edgeSylow 0) (X.Gi 1) :=
    isSylowTwoOf_of_edgeStab X.hyp (α := X.vert 1) (β := X.vert 0) (X.adj 0).symm
      (by simpa [inf_comm] using X.isSylowTwoOf_edgeSylow 0)
  have hzS : z ∈ X.edgeSylow 0 := by
    have h := X.Q_le_edgeSylow (i := 0) hzQ
    simpa using h
  have hzcent : z ∈ centerOf (X.edgeSylow 0) := by
    refine Subgroup.mem_inf.mpr ⟨hzS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hsS
    have hsL : s ∈ X.L 1 :=
      le_oTwoPrime_of_isPGroup hS_syl.2.1 hS_syl.1 hsS
    exact Subgroup.mem_centralizer_iff.mp hzc s hsL
  have hle : centerOf (X.edgeSylow 0) ⊓ X.Q 1 ≤ X.Z 1 :=
    X.le_Z_of_le_centerOf_sylow 1 hS_syl inf_le_left inf_le_right
  exact hle (Subgroup.mem_inf.mpr ⟨hzcent, hzQ⟩)

theorem Z_one_eq_centerOf_L_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Z 1 = centerOf (X.L 1) :=
  le_antisymm
    (X.Z_one_le_centerOf_L_one_of_ne
      (X.centralizer_L_one_Z_one_ne_Q_one hb hc hGT hs hodd h5 hX))
    (X.centerOf_L_one_le_Z_one)

private theorem centerOf_L_zero_le_Z_zero : centerOf (X.L 0) ≤ X.Z 0 := by
  have hN : IsLocL2 Γ G (X.vert 0) (X.n 0) (X.L 0) := X.hyp.isLocL2_oTwoPrime (X.vert 0)
  have hQeq : X.Q 0 = pCoreOf 2 (X.L 0) := (X.pCoreOf_L_eq_Q 0).symm
  intro z hz
  obtain ⟨hzL, hzc⟩ := Subgroup.mem_inf.mp hz
  have hzQ : z ∈ X.Q 0 := by
    rw [hQeq]
    exact centerOf_le_pCoreOf_of_isLocL2 (n := X.n 0) (L := X.L 0) hN hz
  have hS_syl : IsSylowTwoOf (X.edgeSylow 0) (X.Gi 0) :=
    isSylowTwoOf_of_edgeStab X.hyp (X.adj 0) (X.isSylowTwoOf_edgeSylow 0)
  have hzS : z ∈ X.edgeSylow 0 := X.Q_le_edgeSylow_left 0 hzQ
  have hzcent : z ∈ centerOf (X.edgeSylow 0) := by
    refine Subgroup.mem_inf.mpr ⟨hzS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hsS
    have hsL : s ∈ X.L 0 :=
      le_oTwoPrime_of_isPGroup hS_syl.2.1 hS_syl.1 hsS
    exact Subgroup.mem_centralizer_iff.mp hzc s hsL
  have hle : centerOf (X.edgeSylow 0) ⊓ X.Q 0 ≤ X.Z 0 :=
    X.le_Z_of_le_centerOf_sylow 0 hS_syl inf_le_left inf_le_right
  exact hle (Subgroup.mem_inf.mpr ⟨hzcent, hzQ⟩)

private theorem centerOf_L_zero_le_Z_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    centerOf (X.L 0) ≤ X.Z 1 := by
  have hZ0le : centerOf (X.L 0) ≤ X.Z 0 :=
    X.centerOf_L_zero_le_Z_zero
  have hS0_syl : IsSylowTwoOf (X.edgeSylow 0) (X.Gi 0) :=
    isSylowTwoOf_of_edgeStab X.hyp (X.adj 0) (X.isSylowTwoOf_edgeSylow 0)
  have hS_syl : IsSylowTwoOf (X.edgeSylow 0) (X.Gi 1) := by
    have h := isSylowTwoOf_of_edgeStab X.hyp (α := X.vert 1) (β := X.vert 0) (X.adj 0).symm
      (P := X.edgeSylow 0) (by simpa [inf_comm] using X.isSylowTwoOf_edgeSylow 0)
    simpa using h
  intro z hz
  have hzQ1 : z ∈ X.Q 1 :=
    X.Z_zero_le_Q_one_aux hGT hs hodd h5 hX (hZ0le hz)
  have hzS : z ∈ X.edgeSylow 0 := by
    have h := X.Q_le_edgeSylow (i := 0) hzQ1
    simpa using h
  have hzcent : z ∈ centerOf (X.edgeSylow 0) := by
    refine Subgroup.mem_inf.mpr ⟨hzS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hsS
    have hsL : s ∈ X.L 0 :=
      le_oTwoPrime_of_isPGroup hS0_syl.2.1 hS0_syl.1 hsS
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 s hsL
  have hle : centerOf (X.edgeSylow 0) ⊓ X.Q 1 ≤ X.Z 1 :=
    X.le_Z_of_le_centerOf_sylow 1 hS_syl inf_le_left inf_le_right
  exact hle (Subgroup.mem_inf.mpr ⟨hzcent, hzQ1⟩)

private theorem centerOf_L_zero_eq_bot_aux (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    centerOf (X.L 0) = ⊥ := by
  have hZ1eq : X.Z 1 = centerOf (X.L 1) :=
    X.Z_one_eq_centerOf_L_one hb hc hGT hs hodd h5 hX
  have hleZ1 : centerOf (X.L 0) ≤ X.Z 1 :=
    X.centerOf_L_zero_le_Z_one hb hc hGT hs hodd h5 hX
  have hXα : centerOf (X.L 0) ≤ X.L 0 := inf_le_left
  have hnα : ((centerOf (X.L 0)).subgroupOf (X.L 0)).Normal := by
    rw [CFSG.Quasithin.C1GN.centerOf_subgroupOf (X.L 0)]
    infer_instance
  have hXβ : centerOf (X.L 0) ≤ X.L 1 := by
    refine hleZ1.trans ?_
    rw [hZ1eq]
    exact inf_le_left
  have hcle : X.L 1 ≤ Subgroup.centralizer (centerOf (X.L 0) : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haZ : a ∈ centerOf (X.L 1) := by
      rw [← hZ1eq]
      exact hleZ1 ha
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haZ).2 l hl).symm
  have hnβ : ((centerOf (X.L 0)).subgroupOf (X.L 1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hcle.trans (Subgroup.centralizer_le_normalizer _))
  have hbot := eq_bot_of_normal_in_oTwoPrime X.hyp (X.adj 0)
    (X := centerOf (X.L 0)) hXα hnα hXβ hnβ
  simpa [Setup.L, Setup.Gi] using hbot

theorem centerOf_L_zero_eq_bot (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1 ∨ X.n 0 = 2) (hn1 : X.n 1 = 1 ∨ X.n 1 = 2) :
    centerOf (X.L 0) = ⊥ :=
  X.centerOf_L_zero_eq_bot_aux hb hc hGT hs hodd h5 hX

theorem natQuot_Z_zero (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    NatQuot (X.L 0) (X.Z 0) ⊥ (X.n 0) := by
  haveI hfinL : Finite ↥(X.L 0) :=
    finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  have hLst : X.Lst X.QT 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (oTwoPrime_le (X.normGi X.QT 0)).trans
      ((X.normGi_le_Gi X.QT 0).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
  have hP0 : IsPGroup 2 (X.Q 0) :=
    (X.isPGroup_edgeSylow 0).to_le (X.Q_le_edgeSylow_left 0)
  have hQ0L : X.Q 0 ≤ X.L 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).oTwo_le
  have hWZ : X.Z 0 ⊓ X.ZM = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzZ0, hzZM⟩ := Subgroup.mem_inf.mp hz
    have hzQ0 : z ∈ X.Q 0 := X.Z_le_Q 0 hzZ0
    have hzQ0c : z ∈ Subgroup.centralizer (X.Q 0 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 0 hzZ0)).2
    have hzLst : z ∈ X.Lst X.QT 0 := (Subgroup.mem_inf.mp hzZM).1
    have hzLstc : z ∈ Subgroup.centralizer (X.Lst X.QT 0 : Set G) :=
      (Subgroup.mem_inf.mp hzZM).2
    have hzcentL : z ∈ centerOf (X.L 0) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact hQ0L hzQ0
      · rw [Subgroup.mem_centralizer_iff]
        intro l hl
        obtain ⟨a, ha, b, hbQ0, rfl⟩ :=
          (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hLst).mp
            (by rw [X.L_eq_Lst_sup_Q (X.isSK_QT hGT hs hodd h5 hX)
              (Or.inl (X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX))] at hl; exact hl)
        have hza : a * z = z * a := Subgroup.mem_centralizer_iff.mp hzLstc a ha
        have hzb : b * z = z * b := Subgroup.mem_centralizer_iff.mp hzQ0c b hbQ0
        rw [mul_assoc, hzb, ← mul_assoc, hza, mul_assoc]
    have hbot := X.centerOf_L_zero_eq_bot_aux hb hc hGT hs hodd h5 hX
    rw [hbot] at hzcentL
    exact Subgroup.mem_bot.mp hzcentL
  have hWn : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 g (X.L_le_Gi 0 hg)
  have hQW : ∀ q ∈ X.Q 0, ∀ w ∈ X.Z 0, q * w = w * q := by
    intro q hq w hw
    have hwc : w ∈ Subgroup.centralizer (X.Q 0 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 0 hw)).2
    exact Subgroup.mem_centralizer_iff.mp hwc q hq
  have hZ : ∀ z ∈ X.ZM, ∀ l ∈ X.Lst X.QT 0, z * l = l * z := by
    intro z hz l hl
    have hzc : z ∈ Subgroup.centralizer (X.Lst X.QT 0 : Set G) :=
      (Subgroup.mem_inf.mp hz).2
    exact (Subgroup.mem_centralizer_iff.mp hzc l hl).symm
  exact NatQuot.of_complement (L := X.L 0) (L' := X.Lst X.QT 0)
    (E := X.E X.QT 0) (Z := X.ZM) (W := X.Z 0) (Q := X.Q 0) (n := X.n 0)
    (X.natQuot_M hGT hs hodd h5 hX)
    (X.L_eq_Lst_sup_Q (X.isSK_QT hGT hs hodd h5 hX)
      (Or.inl (X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX)))
    hP0 ((X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
    inf_le_left (X.E_eq_Z_zero_sup_ZM hb hGT hs hodd h5 hX).symm hWZ hWn hQW hZ

theorem Z_conj {g : G} {i j : ℤ} (h : g • X.vert i = X.vert j) :
    conjSub g (X.Z i) = X.Z j := by
  have hG : conjSub g (X.Gi i) = X.Gi j := by
    rw [← stabilizer_smul_eq_conjSub g (X.vert i), h]
  have hmain := iSup_sylow_center_conj (H := G) g (X.Gi i)
  rw [hG] at hmain
  simpa [Setup.Z, Setup.Q] using hmain.symm

private theorem Z_one_le_Z_zero (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Z 1 ≤ X.Z 0 := by
  have hZ1E : X.Z 1 ≤ X.E X.QT 0 := X.Z_one_le_E hGT hs hodd h5 hX
  have hZ1Q0 : X.Z 1 ≤ X.Q 0 := hZ1E.trans inf_le_left
  have hZ1cent : X.Z 1 ≤ Subgroup.centralizer (X.L 1 : Set G) := by
    rw [X.Z_one_eq_centerOf_L_one hb hc hGT hs hodd h5 hX]
    exact inf_le_right
  have hS_syl : IsSylowTwoOf (X.edgeSylow 0) (X.Gi 0) :=
    isSylowTwoOf_of_edgeStab X.hyp (X.adj 0) (X.isSylowTwoOf_edgeSylow 0)
  have hSL1 : X.edgeSylow 0 ≤ X.L 1 :=
    le_oTwoPrime_of_isPGroup (X.isSylowTwoOf_edgeSylow 0).2.1
      ((X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_right)
  intro z hz
  have hzQ0 : z ∈ X.Q 0 := hZ1Q0 hz
  have hzS : z ∈ X.edgeSylow 0 := X.Q_le_edgeSylow_left 0 hzQ0
  have hzcent : z ∈ centerOf (X.edgeSylow 0) := by
    refine Subgroup.mem_inf.mpr ⟨hzS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hsS
    exact Subgroup.mem_centralizer_iff.mp (hZ1cent hz) s (hSL1 hsS)
  have hle : centerOf (X.edgeSylow 0) ⊓ X.Q 0 ≤ X.Z 0 :=
    X.le_Z_of_le_centerOf_sylow 0 hS_syl inf_le_left inf_le_right
  exact hle (Subgroup.mem_inf.mpr ⟨hzcent, hzQ0⟩)

private theorem conjSub_relCent (g : G) {E Z A : Subgroup G}
    (hEZ : E ≤ Subgroup.normalizer (Z : Set G)) :
    conjSub g (relCent E Z A) =
      relCent (conjSub g E) (conjSub g Z) (conjSub g A) := by
  have hEZ' : conjSub g E ≤ Subgroup.normalizer (conjSub g Z : Set G) :=
    CFSG.Quasithin.conjSub_le_normalizer hEZ
  ext x
  rw [mem_conjSub, mem_relCent hEZ, mem_relCent hEZ']
  constructor
  · rintro ⟨he, hc⟩
    refine ⟨?_, ?_⟩
    · rwa [mem_conjSub]
    · intro a ha
      rw [mem_conjSub] at ha ⊢
      have hcomm : g⁻¹ * ⁅x, a⁆ * g = ⁅g⁻¹ * x * g, g⁻¹ * a * g⁆ := by
        simp only [commutatorElement_def]; group
      rw [hcomm]
      exact hc (g⁻¹ * a * g) ha
  · rintro ⟨he, hc⟩
    refine ⟨?_, ?_⟩
    · rwa [mem_conjSub] at he
    · intro a ha
      have ha' : g * a * g⁻¹ ∈ conjSub g A := by
        rw [mem_conjSub]
        convert ha using 1 <;> group
      have h := hc (g * a * g⁻¹) ha'
      rw [mem_conjSub] at h
      convert h using 1
      simp only [commutatorElement_def]; group

private theorem Z_neg_one_le_Z_zero (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Z (-1) ≤ X.Z 0 := by
  have hb1 : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    simpa using (X.adj (-1)).symm
  obtain ⟨g0, hg0G0, hg0⟩ := X.hyp.locTrans (X.adj 0) hb1
  have hZ1 : conjSub g0 (X.Z 1) = X.Z (-1) := by
    apply X.Z_conj
    simpa using hg0
  have hZ0 : conjSub g0 (X.Z 0) = X.Z 0 := X.Z_normal 0 g0 hg0G0
  rw [← hZ1, ← hZ0]
  exact conjSub_mono g0 (X.Z_one_le_Z_zero hb hc hGT hs hodd h5 hX)

theorem Z_one_eq_relCent (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Z 1 = relCent (X.Z 0) ⊥ X.S := by
  have hS1 : X.S ≤ X.L 1 := by
    rw [← X.edgeSylow_zero]
    simpa using (X.isSylowTwoOf_edgeSylow_L_succ 0).1
  have hZ0N : X.Z 0 ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hZ1Z0 : X.Z 1 ≤ X.Z 0 := X.Z_one_le_Z_zero hb hc hGT hs hodd h5 hX
  have hZ1S : X.Z 1 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    simpa using (X.Z_le_Q 1).trans (X.Q_le_edgeSylow 0)
  have hZ1cS : X.Z 1 ≤ centerOf X.S := by
    have hZ1cent : X.Z 1 ≤ Subgroup.centralizer (X.L 1 : Set G) := by
      rw [X.Z_one_eq_centerOf_L_one hb hc hGT hs hodd h5 hX]
      exact inf_le_right
    exact le_inf hZ1S (hZ1cent.trans (Subgroup.centralizer_le hS1))
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [mem_relCent hZ0N]
    refine ⟨hZ1Z0 hz, fun s hsS => ?_⟩
    have hcC := (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (hZ1cS hz)).2) s hsS
    rw [Subgroup.mem_bot, commutatorElement_def, ← hcC]
    group
  · have hRQ1 : relCent (X.Z 0) ⊥ X.S ≤ X.Q 1 := fun y hy =>
      X.Z_zero_le_Q_one_aux hGT hs hodd h5 hX ((mem_relCent hZ0N).mp hy).1
    have hRS : relCent (X.Z 0) ⊥ X.S ≤ X.S := by
      refine hRQ1.trans ?_
      rw [← X.edgeSylow_zero]
      exact X.Q_le_edgeSylow 0
    have hRcS : relCent (X.Z 0) ⊥ X.S ≤ centerOf X.S := by
      refine le_inf hRS ?_
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro s hsS
      have hcomm : ⁅z, s⁆ = 1 :=
        Subgroup.mem_bot.mp (((mem_relCent hZ0N).mp hz).2 s hsS)
      rw [commutatorElement_def] at hcomm
      have h1 : z * s = s * z := by
        calc z * s = (z * s * z⁻¹ * s⁻¹) * (s * z) := by group
          _ = 1 * (s * z) := by rw [hcomm]
          _ = s * z := one_mul _
      exact h1.symm
    have hSylS : IsSylowTwoOf X.S (X.Gi 1) := by
      have hh := isSylowTwoOf_of_edgeStab X.hyp (X.adj 0).symm
        (show IsSylowTwoOf X.S (X.Gi 1 ⊓ X.Gi 0) from by
          simpa [X.edgeSylow_zero, inf_comm] using X.isSylowTwoOf_edgeSylow 0)
      simpa using hh
    have hRZ1 : relCent (X.Z 0) ⊥ X.S ≤ X.Z 1 :=
      X.le_Z_of_le_centerOf_sylow 1 hSylS hRcS hRQ1
    exact hRZ1

theorem commutator_Z_zero_S (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.Z 0, X.S⁆ = X.Z 1 := by
  have hS0 : IsSylowTwoOf X.S (X.L 0) := by
    rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L 0
  have h := X.natQuot_Z_zero hb hc hGT hs hodd h5 hX
  have hcomm := h.comm_eq X.S hS0
  rw [sup_bot_eq] at hcomm
  rw [hcomm, X.Z_one_eq_relCent hb hc hGT hs hodd h5 hX]

theorem card_Z_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    Nat.card (X.Z 1) = 2 ^ X.n 0 := by
  have hS0 : IsSylowTwoOf X.S (X.L 0) := by
    rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L 0
  have h := X.natQuot_Z_zero hb hc hGT hs hodd h5 hX
  have hline := h.line X.S hS0
  rw [← X.Z_one_eq_relCent hb hc hGT hs hodd h5 hX,
    Subgroup.relIndex_bot_left] at hline
  exact hline

private theorem not_S_le_Gi_neg_one :
    ¬ X.S ≤ X.Gi (-1) := by
  intro hSS'
  have hn0pos : 0 < X.n 0 := (X.hyp.valency (X.vert 0)).1
  have hSedge : X.S ≤ X.Gi 0 ⊓ X.Gi 1 := by
    rw [← X.edgeSylow_zero]
    exact (X.isSylowTwoOf_edgeSylow 0).1
  have hb1 : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    simpa using (X.adj (-1)).symm
  have hQ0S : X.Q 0 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow_left 0
  have hrel : (X.Q 0).relIndex X.S = 2 ^ X.n 0 := by
    rw [← X.edgeSylow_zero]
    exact X.relIndex_Q_edgeSylow 0
  have hne : X.Q 0 ≠ X.S := by
    intro heq
    rw [heq, Subgroup.relIndex_self] at hrel
    have h2 : 1 < 2 ^ X.n 0 := by
      calc 1 = 2 ^ 0 := (pow_zero 2).symm
        _ < 2 ^ X.n 0 := Nat.pow_lt_pow_right (by norm_num) hn0pos
    omega
  have hlt : X.Q 0 < X.S := lt_of_le_of_ne hQ0S hne
  obtain ⟨-, x, hxS, hxQ⟩ := SetLike.lt_iff_le_and_exists.mp hlt
  have hx1 : x ∈ X.Gi 1 := (inf_le_right : X.Gi 0 ⊓ X.Gi 1 ≤ X.Gi 1) (hSedge hxS)
  have hxm1 : x ∈ X.Gi (-1) := hSS' hxS
  have hxQ' : x ∉ pCoreOf 2 (X.Gi 0) := by
    intro hx
    exact hxQ hx
  have hfix1 : x • X.vert 1 = X.vert 1 := MulAction.mem_stabilizer_iff.mp hx1
  have hfixm1 : x • X.vert (-1) = X.vert (-1) := MulAction.mem_stabilizer_iff.mp hxm1
  have hxVS : x ∈ vertexSylowMap X.hyp
      (X.hyp.isLocL2_oTwoPrime (X.vert 0)) (X.vert 1) := by
    rw [← X.edgeSylow_zero, X.edgeSylow_eq_vertexSylow 0] at hxS
    simpa using hxS
  obtain ⟨a, ⟨haAdj, haFix⟩, huniq⟩ :=
    edgeSylow_fixes_unique_of_not_pcore X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert 0))
      (X.adj 0) hxVS hxQ'
  have heq : X.vert 1 = X.vert (-1) :=
    (huniq (X.vert 1) ⟨X.adj 0, hfix1⟩).trans
      (huniq (X.vert (-1)) ⟨hb1, hfixm1⟩).symm
  have := X.vert_injective heq
  omega

private theorem Z_neg_one_eq_relCent_conjSub (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)

    {g0 : G} (hg0G0 : g0 ∈ X.Gi 0) (hg0 : g0 • X.vert 1 = X.vert (-1)) :
    X.Z (-1) = relCent (X.Z 0) ⊥ (conjSub g0 X.S) := by
  have hZ1conj : conjSub g0 (X.Z 1) = X.Z (-1) := by
    apply X.Z_conj
    simpa using hg0
  have hZ0conj : conjSub g0 (X.Z 0) = X.Z 0 := X.Z_normal 0 g0 hg0G0
  have hZ1rel : X.Z 1 = relCent (X.Z 0) ⊥ X.S :=
    X.Z_one_eq_relCent hb hc hGT hs hodd h5 hX
  have hSrel : conjSub g0 (relCent (X.Z 0) ⊥ X.S) =
      relCent (X.Z 0) ⊥ (conjSub g0 X.S) := by
    have hcR := conjSub_relCent (g := g0) (E := X.Z 0) (Z := ⊥) (A := X.S) (by
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact le_top)
    rwa [hZ0conj, conjSub_bot] at hcR
  rw [← hZ1conj, hZ1rel, hSrel]

theorem Z_zero_eq_Z_one_sup_Z_neg_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Z 0 = X.Z 1 ⊔ X.Z (-1) := by
  have hS0 : IsSylowTwoOf X.S (X.L 0) := by
    rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L 0
  have hSedge : X.S ≤ X.Gi 0 ⊓ X.Gi 1 := by
    rw [← X.edgeSylow_zero]
    exact (X.isSylowTwoOf_edgeSylow 0).1
  have hb1 : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    simpa using (X.adj (-1)).symm
  obtain ⟨g0, hg0G0, hg0⟩ := X.hyp.locTrans (X.adj 0) hb1
  have hG1conj : conjSub g0 (X.Gi 1) = X.Gi (-1) := by
    rw [← stabilizer_smul_eq_conjSub g0 (X.vert 1)]
    change MulAction.stabilizer G (g0 • X.vert 1) = MulAction.stabilizer G (X.vert (-1))
    rw [show g0 • X.vert 1 = X.vert (-1) by simpa using hg0]
  have hL0conj : conjSub g0 (X.L 0) = X.L 0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_oTwoPrime (X.Gi 0) hg0G0)
  have hS' : IsSylowTwoOf (conjSub g0 X.S) (X.L 0) := by
    have h := CFSG.Quasithin.F7.isSylowTwoOf_conj hS0 g0
    rwa [hL0conj] at h
  have hS'Gm1 : conjSub g0 X.S ≤ X.Gi (-1) := by
    rw [← hG1conj]
    exact conjSub_mono g0 (hSedge.trans inf_le_right)
  haveI hfinL0 : Finite ↥(X.L 0) :=
    finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  have hQ0S' : X.Q 0 ≤ conjSub g0 X.S :=
    (X.pCoreOf_L_eq_Q 0).ge.trans (pCoreOf_le_of_isSylowTwoOf hS')
  have hZ0S' : X.Z 0 ≤ conjSub g0 X.S := (X.Z_le_Q 0).trans hQ0S'
  have hsupS' : conjSub g0 X.S ⊔ X.Z 0 = conjSub g0 X.S := sup_eq_left.mpr hZ0S'
  have hnot : ¬ X.S ≤ conjSub g0 X.S ⊔ X.Z 0 := by
    rw [hsupS']
    exact fun h => X.not_S_le_Gi_neg_one (h.trans hS'Gm1)
  have hZ1rel : X.Z 1 = relCent (X.Z 0) ⊥ X.S :=
    X.Z_one_eq_relCent hb hc hGT hs hodd h5 hX
  have hZnegrel : X.Z (-1) = relCent (X.Z 0) ⊥ (conjSub g0 X.S) :=
    X.Z_neg_one_eq_relCent_conjSub hb hc hGT hs hodd h5 hX hg0G0 hg0
  have hl := X.natQuot_Z_zero hb hc hGT hs hodd h5 hX
  have hlines := hl.lines_inf X.S (conjSub g0 X.S) hS0 hS' hnot
  rw [← hZ1rel, ← hZnegrel] at hlines
  exact hlines.2.symm

theorem Vone_le_Q_one (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Vone ≤ X.Q 1 := by
  have hZ0Q1 : X.Z 0 ≤ X.Q 1 := X.Z_le_Q_of_le_Gi 0 2 1
    (X.Z_zero_le_E.trans fun _ hx => (X.E_QT_le_Gi_two hGT hs hodd h5 hX hx).1)
    (Or.inr ⟨by norm_num, by norm_num⟩)
  refine iSup_le fun g => iSup_le fun hg => ?_
  calc conjSub g (X.Z 0) ≤ conjSub g (X.Q 1) := conjSub_mono g hZ0Q1
    _ = X.Q 1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) hg)

theorem VnegOne_le_Q_neg_one (hb : ¬ X.Z 0 ≤ X.Gi 3) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) : X.VnegOne ≤ X.Q (-1) := by
  unfold Setup.VnegOne
  refine iSup_le fun g => iSup_le fun hg => ?_
  calc conjSub g (X.Z 0) ≤ conjSub g (X.Q (-1)) :=
        conjSub_mono g (X.Z_zero_le_Q_neg_one hb hGT hs hodd h5 hX)
    _ = X.Q (-1) := CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1))) hg)

theorem Z_one_le_Gi (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Z 1 ≤ X.Gi (-2) ⊓ X.Gi 4 := by
  have hZ1E : X.Z 1 ≤ X.E X.QT 0 := X.Z_one_le_E hGT hs hodd h5 hX
  refine le_inf ?_ ?_
  · exact hZ1E.trans (fun _ hx => (X.E_QT_le_Gi_two hGT hs hodd h5 hX hx).2)
  · have hZ1Z0 : X.Z 1 ≤ X.Z 0 := X.Z_one_le_Z_zero hb hc hGT hs hodd h5 hX
    have hZ0E : X.Z 0 ≤ X.E X.QT 0 := X.Z_zero_le_E
    have hZ0_2 : X.Z 0 ≤ X.Gi 2 :=
      hZ0E.trans (fun _ hx => (X.E_QT_le_Gi_two hGT hs hodd h5 hX hx).1)
    have hZ2_4 : X.Z 2 ≤ X.Gi 4 := by
      have hZ : conjSub X.τ (X.Z 0) = X.Z 2 := by
        simpa using (X.Z_add 1 0).symm
      have hGi : conjSub X.τ (X.Gi 2) = X.Gi 4 := by
        simpa using (X.Gi_add 1 2).symm
      rw [← hZ, ← hGi]
      exact conjSub_mono X.τ hZ0_2
    obtain ⟨g, hgL1, hg02⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).trans
      (X.vert 0) (X.vert 2) (X.adj 0).symm (X.adj 1)
    have hgG1 : g ∈ X.Gi 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).le hgL1
    have hZ1_eq : conjSub g (X.Z 1) = X.Z 1 := X.Z_normal 1 g hgG1
    have hZ0_eq : conjSub g (X.Z 0) = X.Z 2 := X.Z_conj hg02
    have hZ1Z2 : X.Z 1 ≤ X.Z 2 := by
      rw [← hZ1_eq, ← hZ0_eq]
      exact conjSub_mono g hZ1Z0
    exact hZ1Z2.trans hZ2_4

theorem Z_one_not_le_Gi_five (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ¬ X.Z 1 ≤ X.Gi 5 := by
  intro hZ1_5
  have hZ1m2 : X.Z 1 ≤ X.Gi (-2) := fun z hz =>
    (X.Z_one_le_Gi hb hc hGT hs hodd h5 hX hz).1
  have hZ1_3 : X.Z 1 ≤ X.Gi 3 := fun z hz =>
    X.mem_Gi_of_between (hZ1m2 hz) (hZ1_5 hz) (by omega) (by omega)
  have hZneg_eq : X.Z (-1) = conjSub (X.τ ^ (-1 : ℤ)) (X.Z 1) := by
    have h := X.Z_add (-1) 1
    simpa using h
  have hGi3_eq : X.Gi 3 = conjSub (X.τ ^ (-1 : ℤ)) (X.Gi 5) := by
    have h := X.Gi_add (-1) 5
    simpa using h
  have hZneg_3 : X.Z (-1) ≤ X.Gi 3 := by
    rw [hZneg_eq, hGi3_eq]
    exact conjSub_mono _ hZ1_5
  have hZ0_3 : X.Z 0 ≤ X.Gi 3 := by
    rw [X.Z_zero_eq_Z_one_sup_Z_neg_one hb hc hGT hs hodd h5 hX]
    exact sup_le hZ1_3 hZneg_3
  exact hb hZ0_3

private theorem L_one_le_centralizer_Z_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.L 1 ≤ Subgroup.centralizer (X.Z 1 : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rw [X.Z_one_eq_centerOf_L_one hb hc hGT hs hodd h5 hX] at ha
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 q hq).symm

private theorem commutator_Z_zero_Q_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.Z 0, X.Q 1⁆ = X.Z 1 := by
  have hQ1leS : X.Q 1 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow 0
  have hQ0NQ1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    ((X.Q_le_Gi_adj 0).trans inf_le_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hSleL1 : X.S ≤ X.L 1 := by
    have h := (X.isSylowTwoOf_edgeSylow_L_succ 0).1
    rwa [X.edgeSylow_zero] at h
  have hL1Z1 : X.L 1 ≤ Subgroup.centralizer (X.Z 1 : Set G) :=
    X.L_one_le_centralizer_Z_one hb hc hGT hs hodd h5 hX
  have hQ1Z1 : X.Q 1 ≤ Subgroup.centralizer (X.Z 1 : Set G) := hQ1leS.trans hSleL1 |>.trans hL1Z1
  have hQ0Z1 : X.Q 0 ≤ Subgroup.centralizer (X.Z 1 : Set G) :=
    (X.Q_le_edgeSylow_left 0).trans (by rw [X.edgeSylow_zero]; exact hSleL1) |>.trans hL1Z1
  refine le_antisymm ?_ ?_
  · calc ⁅X.Z 0, X.Q 1⁆ ≤ ⁅X.Z 0, X.S⁆ :=
          Subgroup.commutator_mono (le_refl (X.Z 0)) hQ1leS
      _ = X.Z 1 := X.commutator_Z_zero_S hb hc hGT hs hodd h5 hX
  · rw [← X.commutator_Z_zero_S hb hc hGT hs hodd h5 hX]
    rw [Subgroup.commutator_le]
    intro z hz s hsS
    have hS : X.S = X.Q 0 ⊔ X.Q 1 := (X.sup_Q_eq_edgeSylow hc 0).symm
    rw [hS] at hsS
    obtain ⟨q0, hq0, q1, hq1, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hQ0NQ1).mp hsS
    have hzc : z ∈ Subgroup.centralizer (X.Q 0 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 0 hz)).2
    have hzq0 : z * q0 = q0 * z :=
      (Subgroup.mem_centralizer_iff.mp hzc q0 hq0).symm
    have hcomm : ⁅z, q0 * q1⁆ = q0 * ⁅z, q1⁆ * q0⁻¹ := by
      simp only [commutatorElement_def]
      have h1 : z * (q0 * q1) = q0 * (z * q1) := by
        rw [← mul_assoc, hzq0, mul_assoc]
      rw [h1]
      group
    rw [hcomm]
    have hmem : ⁅z, q1⁆ ∈ ⁅X.Z 0, X.Q 1⁆ :=
      Subgroup.commutator_mem_commutator hz hq1
    have hmemZ1 : ⁅z, q1⁆ ∈ X.Z 1 := by
      have h := (Subgroup.commutator_mono (le_refl (X.Z 0)) hQ1leS) hmem
      rwa [X.commutator_Z_zero_S hb hc hGT hs hodd h5 hX] at h
    have hfix : q0 * ⁅z, q1⁆ * q0⁻¹ = ⁅z, q1⁆ := by
      have h := Subgroup.mem_centralizer_iff.mp (hQ0Z1 hq0) ⁅z, q1⁆ hmemZ1
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hfix]
    exact hmem

private theorem commutator_Vone_Q_one_le (hZ0Q1 : ⁅X.Z 0, X.Q 1⁆ ≤ X.Z 1)
    (hQ1Z1 : X.Q 1 ≤ Subgroup.centralizer (X.Z 1 : Set G)) (hVQ1 : X.Vone ≤ X.Q 1) :
    ⁅X.Vone, X.Q 1⁆ ≤ X.Z 1 := by
  have hVone := X.Vone_eq_iSup_subtype
  rw [Subgroup.commutator_le]
  intro x hx q hq
  have hx' : x ∈ ⨆ g : ↥(X.Gi 1), conjSub (g : G) (X.Z 0) := by rwa [hVone] at hx
  have hres := Subgroup.iSup_induction (fun g : ↥(X.Gi 1) => conjSub (g : G) (X.Z 0))
    (C := fun x => x ∈ X.Vone ∧ ⁅x, q⁆ ∈ X.Z 1) hx'
    (fun g x hx => by
      refine ⟨?_, ?_⟩
      · rw [hVone]
        exact (le_iSup (fun g : ↥(X.Gi 1) => conjSub (g : G) (X.Z 0)) g) hx
      have hz : (g : G)⁻¹ * x * (g : G) ∈ X.Z 0 := mem_conjSub.mp hx
      have hgN : (g : G)⁻¹ ∈ Subgroup.normalizer (X.Q 1 : Set G) :=
        (Subgroup.normalizer (X.Q 1 : Set G)).inv_mem
          ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) g.2)
      have hq' : (g : G)⁻¹ * q * (g : G) ∈ X.Q 1 := by
        have h := (Subgroup.mem_normalizer_iff.mp hgN q).mp hq
        simpa using h
      have hzq' : ⁅(g : G)⁻¹ * x * (g : G), (g : G)⁻¹ * q * (g : G)⁆ ∈ X.Z 1 :=
        hZ0Q1 (Subgroup.commutator_mem_commutator hz hq')
      have hcomm : ⁅x, q⁆ =
          (g : G) * ⁅(g : G)⁻¹ * x * (g : G), (g : G)⁻¹ * q * (g : G)⁆ * (g : G)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [hcomm]
      have hZ1conj : conjSub (g : G) (X.Z 1) = X.Z 1 := X.Z_normal 1 (g : G) g.2
      have hmem := mul_mem_conjSub (g := (g : G)) hzq'
      rwa [hZ1conj] at hmem)
    ⟨(X.Vone).one_mem, by simp⟩
    (fun x y hx hy => by
      refine ⟨(X.Vone).mul_mem hx.1 hy.1, ?_⟩
      have hxQ1 : x ∈ X.Q 1 := hVQ1 hx.1
      have hyZ : ⁅y, q⁆ ∈ X.Z 1 := hy.2
      have hfix : x * ⁅y, q⁆ * x⁻¹ = ⁅y, q⁆ := by
        have h := Subgroup.mem_centralizer_iff.mp (hQ1Z1 hxQ1) ⁅y, q⁆ hyZ
        rw [← h, mul_assoc, mul_inv_cancel, mul_one]
      have hcomm : ⁅x * y, q⁆ = x * ⁅y, q⁆ * x⁻¹ * ⁅x, q⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hcomm, hfix]
      exact (X.Z 1).mul_mem hyZ hx.2)
  exact hres.2

theorem Z_zero_le_Vone : X.Z 0 ≤ X.Vone := by
  rw [X.Vone_eq_iSup_subtype]
  have h := le_iSup (fun g : ↥(X.Gi 1) => conjSub (g : G) (X.Z 0)) ⟨1, (X.Gi 1).one_mem⟩
  simpa [conjSub_one] using h

theorem commutator_Vone_Q_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.Vone, X.Q 1⁆ = X.Z 1 := by
  have hQ1leS : X.Q 1 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow 0
  have hSleL1 : X.S ≤ X.L 1 := by
    have h := (X.isSylowTwoOf_edgeSylow_L_succ 0).1
    rwa [X.edgeSylow_zero] at h
  have hQ1Z1 : X.Q 1 ≤ Subgroup.centralizer (X.Z 1 : Set G) :=
    (hQ1leS.trans hSleL1).trans (X.L_one_le_centralizer_Z_one hb hc hGT hs hodd h5 hX)
  have hZ0Q1 : ⁅X.Z 0, X.Q 1⁆ = X.Z 1 :=
    X.commutator_Z_zero_Q_one hb hc hGT hs hodd h5 hX
  refine le_antisymm
    (X.commutator_Vone_Q_one_le hZ0Q1.le hQ1Z1 (X.Vone_le_Q_one hGT hs hodd h5 hX)) ?_
  rw [← hZ0Q1]
  exact Subgroup.commutator_mono X.Z_zero_le_Vone (le_refl (X.Q 1))

theorem S_eq_Vone_sup_Q_zero (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.S = X.Vone ⊔ X.Q 0 := by
  have hVle : X.Vone ≤ X.Q 1 := X.Vone_le_Q_one hGT hs hodd h5 hX
  have hA : X.Vone ≤ X.edgeSylow 0 := hVle.trans (X.Q_le_edgeSylow 0)
  have hZ2V : X.Z 2 ≤ X.Vone := by
    obtain ⟨g, hgL1, hg02⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).trans
      (X.vert 0) (X.vert 2) (X.adj 0).symm (X.adj 1)
    have hgG1 : g ∈ X.Gi 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).le hgL1
    rw [← X.Z_conj hg02]
    exact le_iSup₂_of_le g hgG1 le_rfl
  have hnot : ¬ X.Vone ≤ X.Q 0 := fun h =>
    X.Z_two_not_le_Q_zero hb hGT hs hodd h5 hX (hZ2V.trans h)
  exact (X.sup_Q_eq_edgeSylow_of_left_gen (A := X.Vone) 0
    (inf_le_left.trans ((X.K_le_Gi 1).trans X.Gi_one_le_normalizer_Vone)) hA hnot).symm

private theorem Q_zero_le_normalizer_Q_one_inf_Q_neg_one :
    X.Q 0 ≤ Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
  have h1' : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    ((X.Q_le_Gi_adj 0).trans inf_le_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have h2' : X.Q 0 ≤ Subgroup.normalizer (X.Q (-1) : Set G) := by
    have h := ((X.Q_le_Gi_adj 0).trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (0 - 1)))
    simpa using h
  exact (le_inf h1' h2').trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem K_le_normalizer_Q_one_inf_Q_neg_one :
    X.K ≤ Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
  have h1' : X.K ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.K_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have h2' : X.K ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
    (X.K_le_Gi (-1)).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)))
  exact (le_inf h1' h2').trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem L_zero_eq_S_sup_S_neg_one_sup_Q_zero :
    X.L 0 = X.S ⊔ pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) ⊔ X.Q 0 := by
  have hQ0S : X.Q 0 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow_left 0
  have hQ0B : X.Q 0 ≤ pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) := by
    have h := X.Q_le_edgeSylow_right 0
    simpa [inf_comm] using h
  have hSedge : X.S ≤ X.L 0 := by
    rw [← X.edgeSylow_zero]
    exact (X.isSylowTwoOf_edgeSylow_L 0).1
  have hBleL : pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) ≤ X.L 0 := by
    have h := (X.isSylowTwoOf_edgeSylow_L_succ (-1)).1
    simpa [Setup.edgeSylow, inf_comm] using h
  have hSb : X.S ≤ MulAction.stabilizer G (X.vert 1) := by
    have h := (X.isSylowTwoOf_edgeSylow 0).1
    rw [X.edgeSylow_zero] at h
    exact fun x hx =>
      MulAction.mem_stabilizer_iff.mp ((inf_le_right : X.Gi 0 ⊓ X.Gi 1 ≤ X.Gi 1) (h hx))
  have hBb : pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) ≤
      MulAction.stabilizer G (X.vert (-1)) := by
    have h := (X.isSylowTwoOf_edgeSylow (-1)).1
    intro x hx
    have hx' : x ∈ X.edgeSylow (-1) := by simpa [Setup.edgeSylow, inf_comm] using hx
    exact MulAction.mem_stabilizer_iff.mp
      ((inf_le_left : X.Gi (-1) ⊓ X.Gi ((-1) + 1) ≤ X.Gi (-1)) (h hx'))
  have hAidx : (X.S ⊓ X.Q 0).relIndex X.S = 2 ^ X.n 0 := by
    rw [inf_eq_right.mpr hQ0S, ← X.edgeSylow_zero]
    exact X.relIndex_Q_edgeSylow 0
  have hBidx : (pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) ⊓ X.Q 0).relIndex
      (pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1))) = 2 ^ X.n 0 := by
    rw [inf_eq_right.mpr hQ0B]
    have h := X.relIndex_Q_succ_edgeSylow (-1)
    simpa [Setup.edgeSylow, inf_comm] using h
  exact X.L_eq_sup_of_fixes 0 (a := X.vert 1) (b := X.vert (-1)) (A := X.S)
    (B := pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)))
    (X.adj 0) (by simpa using (X.adj (-1)).symm)
    (by intro h; have := X.vert_injective h; omega)
    hSedge hBleL hSb hBb hAidx hBidx

theorem Q_one_inf_neg_one_normal (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Gi 0 ≤ Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
  have hZneg : ¬ X.Z 0 ≤ X.Gi (-3) := X.not_Z_zero_le_Gi_neg_three hb hs h5
  have hGTrev : Even (Nat.card (X.reverse).GT) := by simpa using hGT
  have hm := commutator_Vone_Q_one (X := X.reverse) (by simpa using hZneg) hc hGTrev hs
    hodd h5 (X.reverse_hX hs hodd hX)
  rw [X.reverse_Vone] at hm
  have hm' : ⁅X.VnegOne, X.Q (-1)⁆ = X.Z (-1) := by simpa using hm
  have h1 : X.Z 1 ≤ X.Q (-1) :=
    (X.Z_one_le_Z_zero hb hc hGT hs hodd h5 hX).trans
      (X.Z_zero_le_Q_neg_one hb hGT hs hodd h5 hX)
  have hm1 : X.Z (-1) ≤ X.Q 1 :=
    (X.Z_neg_one_le_Z_zero hb hc hGT hs hodd h5 hX).trans
      (X.Z_zero_le_Q_one_aux hGT hs hodd h5 hX)
  have hVn : X.VnegOne ≤
      Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    calc ⁅X.VnegOne, X.Q 1 ⊓ X.Q (-1)⁆ ≤ ⁅X.VnegOne, X.Q (-1)⁆ :=
          Subgroup.commutator_mono (le_refl _) inf_le_right
      _ = X.Z (-1) := hm'
      _ ≤ X.Q 1 ⊓ X.Q (-1) := le_inf hm1 (X.Z_le_Q (-1))
  have hV : X.Vone ≤
      Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    calc ⁅X.Vone, X.Q 1 ⊓ X.Q (-1)⁆ ≤ ⁅X.Vone, X.Q 1⁆ :=
          Subgroup.commutator_mono (le_refl _) inf_le_left
      _ = X.Z 1 := X.commutator_Vone_Q_one hb hc hGT hs hodd h5 hX
      _ ≤ X.Q 1 ⊓ X.Q (-1) := le_inf (X.Z_le_Q 1) h1
  have hQ0 : X.Q 0 ≤
      Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
    X.Q_zero_le_normalizer_Q_one_inf_Q_neg_one
  have hK : X.K ≤
      Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
    X.K_le_normalizer_Q_one_inf_Q_neg_one
  have hS : X.S ≤
      Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
    rw [X.S_eq_Vone_sup_Q_zero hb hc hGT hs hodd h5 hX]
    exact sup_le hV hQ0
  have hSm : pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) =
      X.VnegOne ⊔ X.Q 0 := by
    have h := X.reverse.S_eq_Vone_sup_Q_zero (by simpa using hZneg) hc hGTrev hs hodd h5
      (X.reverse_hX hs hodd hX)
    simpa [Setup.S, Setup.Vone, Setup.VnegOne, Setup.Q, inf_comm] using h
  have hSmN : pCoreOf 2 (X.Gi 0 ⊓ X.Gi (-1)) ≤
      Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
    rw [hSm]
    exact sup_le hVn hQ0
  have hL0 : X.L 0 ≤
      Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
    rw [X.L_zero_eq_S_sup_S_neg_one_sup_Q_zero]
    exact sup_le (sup_le hS hSmN) hQ0
  rw [X.Gi_eq_L_sup_K 0]
  exact sup_le hL0 hK

theorem isElemSec_Q_one_inf_Q_neg_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    IsElemSec (X.Q 1 ⊓ X.Q (-1)) (X.Q 0) := by
  have hAnorm : X.Gi 0 ≤
      Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
    X.Q_one_inf_neg_one_normal hb hc hGT hs hodd h5 hX
  have hKle : X.Q 1 ⊓ X.Q (-1) ≤ X.Q 0 := by
    rw [inf_comm]
    exact X.Q_neg_one_inf_Q_one_le_Q_zero
  have hsq : ∀ q ∈ X.Q 0, q ^ 2 ∈ X.Q 1 ⊓ X.Q (-1) := fun q hq => by
    simpa [inf_comm] using X.sq_mem_Q_neg_one_inf_Q_one hq
  refine ⟨hKle, ?_, hsq⟩
  rw [Subgroup.commutator_le]
  intro a ha b hbm
  have hab2 : (a * b) ^ 2 ∈ X.Q 1 ⊓ X.Q (-1) :=
    hsq (a * b) ((X.Q 0).mul_mem ha hbm)
  have ha2 : a ^ 2 ∈ X.Q 1 ⊓ X.Q (-1) := hsq a ha
  have hb2 : b ^ 2 ∈ X.Q 1 ⊓ X.Q (-1) := hsq b hbm
  have hcA : b⁻¹ * ((a ^ 2)⁻¹) * b * ((b ^ 2)⁻¹) ∈ X.Q 1 ⊓ X.Q (-1) := by
    have hbG0 : b ∈ X.Gi 0 := X.Q_le_Gi 0 hbm
    have hconj : b⁻¹ * ((a ^ 2)⁻¹) * b ∈ X.Q 1 ⊓ X.Q (-1) := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (hAnorm ((X.Gi 0).inv_mem hbG0)) ((a ^ 2)⁻¹)).mp
        ((X.Q 1 ⊓ X.Q (-1)).inv_mem ha2)
    exact (X.Q 1 ⊓ X.Q (-1)).mul_mem hconj ((X.Q 1 ⊓ X.Q (-1)).inv_mem hb2)
  have heq : ⁅a, b⁆ = (a * b) ^ 2 * (b⁻¹ * ((a ^ 2)⁻¹) * b * ((b ^ 2)⁻¹)) := by
    simp only [commutatorElement_def, pow_two]; group
  rw [heq]
  exact (X.Q 1 ⊓ X.Q (-1)).mul_mem hab2 hcA

private theorem Q_one_eq_Vone_sup_inf (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Q 1 = X.Vone ⊔ (X.Q 0 ⊓ X.Q 1) := by
  have hVle : X.Vone ≤ X.Q 1 := X.Vone_le_Q_one hGT hs hodd h5 hX
  have hQ0N : X.Q 0 ≤ Subgroup.normalizer (X.Vone : Set G) :=
    ((X.Q_le_Gi_adj 0).trans inf_le_right).trans X.Gi_one_le_normalizer_Vone
  have hded := Subgroup.inf_sup_assoc_of_le (H := X.Q 0) (K := X.Q 1) (N := X.Vone) hQ0N hVle
  have hS := X.S_eq_Vone_sup_Q_zero hb hc hGT hs hodd h5 hX
  have hQ1S : X.Q 1 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow 0
  rw [show X.Q 0 ⊔ X.Vone = X.S by rw [sup_comm, hS], inf_eq_left.mpr hQ1S,
    inf_comm (X.Q 1) (X.Q 0), sup_comm (X.Q 0 ⊓ X.Q 1) X.Vone] at hded
  exact hded.symm

private theorem commutator_Q_zero_inf_Q_one_Q_zero_inf_Q_neg_one_le :
    ⁅X.Q 0 ⊓ X.Q 1, X.Q 0 ⊓ X.Q (-1)⁆ ≤ X.Q 1 ⊓ X.Q (-1) := by
  have hCQ1 : X.Q 0 ⊓ X.Q (-1) ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (inf_le_left.trans ((X.Q_le_Gi_adj 0).trans inf_le_right)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hQ0Gm1 : X.Q 0 ≤ X.Gi (-1) := by simpa using X.Q_le_Gi_pred 0
  have hHQm1 : X.Q 0 ⊓ X.Q 1 ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
    (inf_le_left.trans hQ0Gm1).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)))
  refine le_inf ?_ ?_
  · rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono_right inf_le_right).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hCQ1)
  · exact (Subgroup.commutator_mono_right inf_le_right).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hHQm1)

private theorem commutator_Q_zero_inf_neg_one_Q_one_le (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ≤ (X.Vone ⊓ X.Q 0) ⊔ (X.Q 1 ⊓ X.Q (-1)) := by
  have hQ1eq := X.Q_one_eq_Vone_sup_inf hb hc hGT hs hodd h5 hX
  have hVle : X.Vone ≤ X.Q 1 := X.Vone_le_Q_one hGT hs hodd h5 hX
  have hCNV : X.Q 0 ⊓ X.Q (-1) ≤ Subgroup.normalizer (X.Vone : Set G) :=
    (inf_le_left.trans ((X.Q_le_Gi_adj 0).trans inf_le_right)).trans X.Gi_one_le_normalizer_Vone
  have hcvV : ⁅X.Q 0 ⊓ X.Q (-1), X.Vone⁆ ≤ X.Vone :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hCNV
  have hVNQ0 : X.Vone ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (hVle.trans ((X.Q_le_Gi_adj 1).trans inf_le_left)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hcvQ0 : ⁅X.Q 0 ⊓ X.Q (-1), X.Vone⁆ ≤ X.Q 0 := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono_right inf_le_left).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hVNQ0)
  have hCV : ⁅X.Q 0 ⊓ X.Q (-1), X.Vone⁆ ≤ X.Vone ⊓ X.Q 0 := le_inf hcvV hcvQ0
  have hCH : ⁅X.Q 0 ⊓ X.Q (-1), X.Q 0 ⊓ X.Q 1⁆ ≤ X.Q 1 ⊓ X.Q (-1) :=
    (Subgroup.commutator_comm _ _).le.trans X.commutator_Q_zero_inf_Q_one_Q_zero_inf_Q_neg_one_le
  have hQ0NV : X.Q 0 ≤ Subgroup.normalizer (X.Vone : Set G) :=
    ((X.Q_le_Gi_adj 0).trans inf_le_right).trans X.Gi_one_le_normalizer_Vone
  have hHnormV : X.Q 0 ⊓ X.Q 1 ≤ Subgroup.normalizer (X.Vone : Set G) :=
    inf_le_left.trans hQ0NV
  have hHA : X.Q 0 ⊓ X.Q 1 ≤
      Subgroup.normalizer ((X.Vone ⊓ X.Q 0 : Subgroup G) : Set G) := by
    refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact hHnormV
    · exact inf_le_left.trans (X.Q 0).le_normalizer
  refine Subgroup.commutator_le.mpr ?_
  intro c hc1 x hx
  have hx' : x ∈ X.Q 0 ⊓ X.Q 1 ⊔ X.Vone := by
    rw [sup_comm, ← hQ1eq]
    exact hx
  obtain ⟨h', hh', v, hv, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hHnormV).mp hx'
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : ⁅c, h'⁆ ∈ X.Q 1 ⊓ X.Q (-1) :=
    hCH (Subgroup.commutator_mem_commutator hc1 hh')
  have h2 : ⁅c, v⁆ ∈ X.Vone ⊓ X.Q 0 :=
    hCV (Subgroup.commutator_mem_commutator hc1 hv)
  have h3 : h' * ⁅c, v⁆ * h'⁻¹ ∈ X.Vone ⊓ X.Q 0 :=
    (Subgroup.mem_normalizer_iff.mp (hHA hh') _).mp h2
  have h4 := Subgroup.mul_mem_sup h1 h3
  rw [sup_comm (X.Q 1 ⊓ X.Q (-1)) (X.Vone ⊓ X.Q 0)] at h4
  simpa [mul_assoc] using h4

private theorem Q_zero_inf_one_le_sup (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Q 0 ⊓ X.Q 1 ≤ (X.Vone ⊓ X.Q 0) ⊔ (X.VnegOne ⊓ X.Q 0) ⊔ (X.Q 1 ⊓ X.Q (-1)) := by
  obtain ⟨-, -, -, -, hcomp5⟩ := X.Q_quot_of_normal_general hc hs (by omega)
  have hcomp5' : X.Q 0 ⊓ X.Q 1 ≤
      ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ⊔ (X.Q 1 ⊓ X.Q (-1)) := by
    simpa [inf_comm] using hcomp5
  have hcomm1 := X.commutator_Q_zero_inf_neg_one_Q_one_le hb hc hGT hs hodd h5 hX
  have hHle : X.Q 0 ⊓ X.Q 1 ≤ (X.Vone ⊓ X.Q 0) ⊔ (X.Q 1 ⊓ X.Q (-1)) :=
    hcomp5'.trans (sup_le hcomm1 le_sup_right)
  exact hHle.trans (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)

private theorem Q_zero_inf_neg_one_le_sup (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Q 0 ⊓ X.Q (-1) ≤ (X.Vone ⊓ X.Q 0) ⊔ (X.VnegOne ⊓ X.Q 0) ⊔ (X.Q 1 ⊓ X.Q (-1)) := by
  have hZneg : ¬ X.Z 0 ≤ X.Gi (-3) := X.not_Z_zero_le_Gi_neg_three hb hs h5
  have hGTrev : Even (Nat.card (X.reverse).GT) := by simpa using hGT
  obtain ⟨-, -, -, -, hcomp5rev⟩ := (X.reverse).Q_quot_of_normal_general hc hs (by omega)
  have hcomm2 := (X.reverse).commutator_Q_zero_inf_neg_one_Q_one_le hZneg hc hGTrev hs hodd h5
    (X.reverse_hX hs hodd hX)
  have hcomm2' : ⁅X.Q 0 ⊓ X.Q 1, X.Q (-1)⁆ ≤
      (X.VnegOne ⊓ X.Q 0) ⊔ (X.Q 1 ⊓ X.Q (-1)) := by
    simpa [X.reverse_Vone, inf_comm] using hcomm2
  have hcomp5rev' : X.Q 0 ⊓ X.Q (-1) ≤
      ⁅X.Q 0 ⊓ X.Q 1, X.Q (-1)⁆ ⊔ (X.Q 1 ⊓ X.Q (-1)) := by
    simpa [inf_comm] using hcomp5rev
  have hCle : X.Q 0 ⊓ X.Q (-1) ≤ (X.VnegOne ⊓ X.Q 0) ⊔ (X.Q 1 ⊓ X.Q (-1)) :=
    hcomp5rev'.trans (sup_le hcomm2' le_sup_right)
  exact hCle.trans (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)

theorem Q_zero_eq_sup (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.Q 0 = (X.Vone ⊓ X.Q 0) ⊔ (X.VnegOne ⊓ X.Q 0) ⊔ (X.Q 1 ⊓ X.Q (-1)) := by
  obtain ⟨hQ0eq, -, -, -, -⟩ := X.Q_quot_of_normal_general hc hs (by omega)
  have hNQ0 : X.Q 1 ⊓ X.Q (-1) ≤ X.Q 0 := by
    rw [inf_comm]
    exact X.Q_neg_one_inf_Q_one_le_Q_zero
  refine le_antisymm ?_ ?_
  · calc X.Q 0 = (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) := hQ0eq
      _ ≤ (X.Vone ⊓ X.Q 0) ⊔ (X.VnegOne ⊓ X.Q 0) ⊔ (X.Q 1 ⊓ X.Q (-1)) :=
          sup_le (X.Q_zero_inf_one_le_sup hb hc hGT hs hodd h5 hX)
            (X.Q_zero_inf_neg_one_le_sup hb hc hGT hs hodd h5 hX)
  · exact sup_le (sup_le inf_le_right inf_le_right) hNQ0

theorem Q_zero_inf_Q_one_le_normalizer_Q_zero_inf_Q_neg_one :
    X.Q 0 ⊓ X.Q 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
  have hQ0Gm1 : X.Q 0 ≤ X.Gi (-1) := by simpa using X.Q_le_Gi_pred 0
  refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
  · exact inf_le_left.trans (X.Q 0).le_normalizer
  · exact (inf_le_left.trans hQ0Gm1).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)))

private theorem relIndex_Q_one_inf_Q_neg_one_Q_zero_inf_Q_neg_one
    (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G s) (h5 : 5 ≤ s) :
    (X.Q 1 ⊓ X.Q (-1)).relIndex (X.Q 0 ⊓ X.Q (-1)) = 2 ^ X.n 1 := by
  obtain ⟨-, -, hrelC, -, -⟩ := (X.reverse).Q_quot_of_normal_general hc hs (by omega)
  rw [show (X.reverse).n 1 = X.n 1 from by simpa [Setup.n] using X.n_neg_one] at hrelC
  simpa [inf_comm] using hrelC

theorem commutator_Q_inf_one_S (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.Q 0 ⊓ X.Q 1, X.S⁆ ≤ X.Q 1 ⊓ X.Q (-1) := by
  haveI hHfin : Finite ↥(X.Q 0 ⊓ X.Q 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 0 ⊓ X.Q 1) (inf_le_left.trans (X.Q_le_Gi 0))
  haveI hCfin : Finite ↥(X.Q 0 ⊓ X.Q (-1)) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 0 ⊓ X.Q (-1)) (inf_le_left.trans (X.Q_le_Gi 0))
  have hNnorm : X.Gi 0 ≤ Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
    X.Q_one_inf_neg_one_normal hb hc hGT hs hodd h5 hX
  have hsec := X.isElemSec_Q_one_inf_Q_neg_one hb hc hGT hs hodd h5 hX
  obtain ⟨hQ0eq, -, -, -, -⟩ := X.Q_quot_of_normal_general hc hs (by omega)
  have hHnorm : X.Q 0 ⊓ X.Q 1 ≤
      Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
    (inf_le_left.trans (X.Q_le_Gi 0)).trans hNnorm
  have hHH : ⁅X.Q 0 ⊓ X.Q 1, X.Q 0 ⊓ X.Q 1⁆ ≤ X.Q 1 ⊓ X.Q (-1) :=
    (Subgroup.commutator_mono inf_le_left inf_le_left).trans hsec.2.1
  have hCnorm : X.Q 0 ⊓ X.Q (-1) ≤
      Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
    (inf_le_left.trans (X.Q_le_Gi 0)).trans hNnorm
  have hCC : ⁅X.Q 0 ⊓ X.Q (-1), X.Q 0 ⊓ X.Q (-1)⁆ ≤ X.Q 1 ⊓ X.Q (-1) :=
    (Subgroup.commutator_mono inf_le_left inf_le_left).trans hsec.2.1
  have hHC : ⁅X.Q 0 ⊓ X.Q 1, X.Q 0 ⊓ X.Q (-1)⁆ ≤ X.Q 1 ⊓ X.Q (-1) :=
    X.commutator_Q_zero_inf_Q_one_Q_zero_inf_Q_neg_one_le
  have hZ1N : X.Z 1 ≤ X.Q 1 ⊓ X.Q (-1) :=
    le_inf (X.Z_le_Q 1) ((X.Z_one_le_Z_zero hb hc hGT hs hodd h5 hX).trans
      (X.Z_zero_le_Q_neg_one hb hGT hs hodd h5 hX))
  have hHV : ⁅X.Q 0 ⊓ X.Q 1, X.Vone⁆ ≤ X.Q 1 ⊓ X.Q (-1) := by
    have h1 : ⁅X.Q 0 ⊓ X.Q 1, X.Vone⁆ ≤ X.Z 1 := by
      calc ⁅X.Q 0 ⊓ X.Q 1, X.Vone⁆ = ⁅X.Vone, X.Q 0 ⊓ X.Q 1⁆ :=
            Subgroup.commutator_comm _ _
        _ ≤ ⁅X.Vone, X.Q 1⁆ := Subgroup.commutator_mono_right inf_le_right
        _ = X.Z 1 := X.commutator_Vone_Q_one hb hc hGT hs hodd h5 hX
    exact h1.trans hZ1N
  have hVnormN : X.Vone ≤ Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
    ((X.Vone_le_Q_one hGT hs hodd h5 hX).trans
      ((X.Q_le_Gi_adj 1).trans inf_le_left)).trans hNnorm
  have hVNQ0 : X.Vone ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((X.Vone_le_Q_one hGT hs hodd h5 hX).trans
      ((X.Q_le_Gi_adj 1).trans inf_le_left)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hHCnorm : X.Q 0 ⊓ X.Q 1 ≤
      Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
    X.Q_zero_inf_Q_one_le_normalizer_Q_zero_inf_Q_neg_one
  refine Subgroup.commutator_le.mpr ?_
  intro h hh s hsS
  have hS := X.S_eq_Vone_sup_Q_zero hb hc hGT hs hodd h5 hX
  have hsS' : s ∈ X.Vone ⊔ X.Q 0 := by rwa [hS] at hsS
  obtain ⟨v, hv, q, hq, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hVNQ0).mp hsS'
  have hq' : q ∈ (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) := by rw [← hQ0eq]; exact hq
  obtain ⟨h', hh', c, hc', rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hHCnorm).mp hq'
  have hqN : ⁅h, h' * c⁆ ∈ X.Q 1 ⊓ X.Q (-1) := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h2 : ⁅h, h'⁆ ∈ X.Q 1 ⊓ X.Q (-1) :=
      hHH (Subgroup.commutator_mem_commutator hh hh')
    have h3 : ⁅h, c⁆ ∈ X.Q 1 ⊓ X.Q (-1) :=
      hHC (Subgroup.commutator_mem_commutator hh hc')
    have h4 : h' * ⁅h, c⁆ * h'⁻¹ ∈ X.Q 1 ⊓ X.Q (-1) :=
      (Subgroup.mem_normalizer_iff.mp (hHnorm hh') _).mp h3
    have h5m := (X.Q 1 ⊓ X.Q (-1)).mul_mem h2 (by simpa [mul_assoc] using h4)
    simpa [mul_assoc] using h5m
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : ⁅h, v⁆ ∈ X.Q 1 ⊓ X.Q (-1) :=
    hHV (Subgroup.commutator_mem_commutator hh hv)
  have h6 : v * ⁅h, h' * c⁆ * v⁻¹ ∈ X.Q 1 ⊓ X.Q (-1) :=
    (Subgroup.mem_normalizer_iff.mp (hVnormN hv) _).mp hqN
  have h7 := (X.Q 1 ⊓ X.Q (-1)).mul_mem h1 h6
  simpa [mul_assoc] using h7

theorem not_normal_Q_zero_inf_one (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (h5 : 5 ≤ s) :
    ¬ (X.Q 0 ⊓ X.Q 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G) ∧
        X.Q 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G)) :=
  (X.Q_quot_of_normal_general hc hs (by omega)).2.2.2.1

private theorem exists_commutator_L_zero_Q_zero_notMem
    (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G s) (h5 : 5 ≤ s) :
    ∃ l ∈ X.L 0, ∃ v ∈ X.Q 0, ⁅l, v⁆ ∉ X.Q 1 ⊓ X.Q (-1) := by
  by_contra h
  push Not at h
  have hcommL : ⁅X.L 0, X.Q 0⁆ ≤ X.Q 1 ⊓ X.Q (-1) := by
    rw [Subgroup.commutator_le]
    exact h
  have hNQ0 : X.Q 1 ⊓ X.Q (-1) ≤ X.Q 0 := by
    rw [inf_comm]
    exact X.Q_neg_one_inf_Q_one_le_Q_zero
  have hQ0L : X.Q 0 ≤ X.L 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).oTwo_le
  have hQ1L : X.Q 1 ≤ X.L 0 := by
    simpa using (X.Q_le_edgeSylow 0).trans (X.edgeSylow_le_L 0)
  have hHnormC : X.Q 0 ⊓ X.Q 1 ≤
      Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    refine Subgroup.commutator_le.mpr ?_
    intro h1 hh c hc'
    exact le_inf hNQ0 inf_le_right
      (hcommL (Subgroup.commutator_mem_commutator (hQ0L (Subgroup.mem_inf.mp hh).1)
        (Subgroup.mem_inf.mp hc').1))
  have hQ1normC : X.Q 1 ≤
      Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    refine Subgroup.commutator_le.mpr ?_
    intro q hq c hc'
    exact le_inf hNQ0 inf_le_right
      (hcommL (Subgroup.commutator_mem_commutator (hQ1L hq) (Subgroup.mem_inf.mp hc').1))
  exact X.not_normal_Q_zero_inf_one hc hs h5 ⟨hHnormC, hQ1normC⟩

private theorem two_pow_le_relIndex_Q_one_inf_Q_neg_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    2 ^ (2 * X.n 0) ≤
      ((X.Q 1 ⊓ X.Q (-1)).subgroupOf (X.L 0)).relIndex ((X.Q 0).subgroupOf (X.L 0)) := by
  classical
  haveI : Finite ↥(X.L 0) :=
    finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  let H : Subgroup G := X.L 0
  let V' : Subgroup ↥H := (X.Q 0).subgroupOf H
  let Z' : Subgroup ↥H := (X.Q 1 ⊓ X.Q (-1)).subgroupOf H
  have hsec0 := X.isElemSec_Q_one_inf_Q_neg_one hb hc hGT hs hodd h5 hX
  have hsec : IsElemSec Z' V' := isElemSec_subgroupOf hsec0
  have hquot : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
  have hquot' : IsL2Quot (X.n 0) (oTwoQuot ↥(⊤ : Subgroup ↥H)) := by
    obtain ⟨e⟩ := hquot
    exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr Subgroup.topEquiv).trans e⟩
  have hQ0L : X.Q 0 ≤ H := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).oTwo_le
  have hZL : X.Q 1 ⊓ X.Q (-1) ≤ H := by
    rw [inf_comm]
    exact X.Q_neg_one_inf_Q_one_le_Q_zero.trans hQ0L
  have hNQ0 : H ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hNZ : H ≤ Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
    (X.L_le_Gi 0).trans (X.Q_one_inf_neg_one_normal hb hc hGT hs hodd h5 hX)
  have hL : (⊤ : Subgroup ↥H) ≤
      Subgroup.normalizer (V' : Set ↥H) ⊓ Subgroup.normalizer (Z' : Set ↥H) :=
    le_inf (le_normalizer_subgroupOf_of_le_normalizer hQ0L hNQ0)
      (le_normalizer_subgroupOf_of_le_normalizer hZL hNZ)
  have hQ0top : pCoreOf 2 (⊤ : Subgroup ↥H) = V' := by
    rw [CFSG.Quasithin.F53Push.pCoreOf_top_eq, ← CFSG.openPCoreOf_subgroupOf 2 H,
      X.pCoreOf_L_eq_Q 0]
  have hQ : ∀ p ∈ pCoreOf 2 (⊤ : Subgroup ↥H), ∀ v ∈ V', ⁅p, v⁆ ∈ Z' := by
    intro p hp v hv
    rw [hQ0top] at hp
    have hpQ : (p : G) ∈ X.Q 0 := Subgroup.mem_subgroupOf.mp hp
    have hvQ : (v : G) ∈ X.Q 0 := Subgroup.mem_subgroupOf.mp hv
    have hcomm : ⁅(p : G), (v : G)⁆ ∈ X.Q 1 ⊓ X.Q (-1) :=
      hsec0.2.1 (Subgroup.commutator_mem_commutator hpQ hvQ)
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hcoe : ((⁅p, v⁆ : ↥H) : G) = ⁅(p : G), (v : G)⁆ :=
      map_commutatorElement (f := Subgroup.subtype H) (g₁ := p) (g₂ := v)
    rwa [hcoe]
  have hnt0 := X.exists_commutator_L_zero_Q_zero_notMem hc hs h5
  obtain ⟨l, hl, v, hv, hne⟩ := hnt0
  have hnt : ∃ l ∈ (⊤ : Subgroup ↥H), ∃ v ∈ V', ⁅l, v⁆ ∉ Z' := by
    refine ⟨⟨l, hl⟩, Subgroup.mem_top _, ⟨v, hQ0L hv⟩,
      Subgroup.mem_subgroupOf.mpr hv, ?_⟩
    intro hmem
    exact hne (by
      have hmem' : ((⁅(⟨l, hl⟩ : ↥H), (⟨v, hQ0L hv⟩ : ↥H)⁆ : ↥H) : G) ∈
          X.Q 1 ⊓ X.Q (-1) := Subgroup.mem_subgroupOf.mp hmem
      have hcoe : ((⁅(⟨l, hl⟩ : ↥H), (⟨v, hQ0L hv⟩ : ↥H)⁆ : ↥H) : G) = ⁅l, v⁆ :=
        map_commutatorElement (f := Subgroup.subtype H) (g₁ := ⟨l, hl⟩)
          (g₂ := ⟨v, hQ0L hv⟩)
      rwa [hcoe] at hmem')
  exact two_pow_le_relIndex_of_nontrivial (G := ↥H) (V := V') (Z := Z') (L := ⊤)
    (X.hyp.valency (X.vert 0)).1 hquot' hsec hL hQ hnt

private theorem relIndex_Q_one_inf_Q_neg_one_Q_zero
    (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G s) (h5 : 5 ≤ s) :
    ((X.Q 1 ⊓ X.Q (-1)).subgroupOf (X.L 0)).relIndex ((X.Q 0).subgroupOf (X.L 0))
      = 2 ^ (2 * X.n 1) := by
  have hQ0L : X.Q 0 ≤ X.L 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).oTwo_le
  rw [Subgroup.relIndex_subgroupOf (H := X.Q 1 ⊓ X.Q (-1)) (K := X.Q 0)
    (L := X.L 0) hQ0L]
  obtain ⟨-, hrel, -⟩ := X.Q_quot_of_normal_general hc hs (by omega)
  simpa [inf_comm] using hrel

theorem n_zero_le_n_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) : X.n 0 ≤ X.n 1 := by
  have hle := X.two_pow_le_relIndex_Q_one_inf_Q_neg_one hb hc hGT hs hodd h5 hX
  rw [X.relIndex_Q_one_inf_Q_neg_one_Q_zero hc hs h5] at hle
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  omega

theorem false_of_n_zero_eq_two_of_n_one_eq_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 2) (hn1 : X.n 1 = 1) : False := by
  have h := X.n_zero_le_n_one hb hc hGT hs hodd h5 hX
  omega

theorem not_Z_le_Gi_three_of_not_le_ZM (hZ : ¬ X.Z 0 ≤ X.ZM)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ¬ X.Z 0 ≤ X.Gi 3 := by
  intro h3
  have hE2 : X.Z 0 ≤ X.Etau 1 :=
    (X.Z_zero_le_Etau_one_iff').mpr h3
  have hEeq : X.E X.QT 0 = X.Z 0 ⊔ X.ZM :=
    X.E_eq_sup_of_not_le_ZM hGT hs hodd h5 hX hZ
  have hE2le : X.E X.QT 0 ≤ X.E X.QT 2 := by
    have h : X.E X.QT 0 ≤ X.Etau 1 := by
      rw [hEeq]
      exact sup_le hE2 (X.ZM_le_Etau_one hGT hs hodd h5 hX)
    rwa [X.Etau_eq] at h
  have hcard : Nat.card ↥(X.E X.QT 0) = Nat.card ↥(X.Etau 1) := by
    rw [X.Etau_eq, show (2 * (1 : ℤ)) = 2 by norm_num, X.E_two_eq]
    exact (card_conjSub X.τ (X.E X.QT 0)).symm
  haveI : Finite ↥(X.Etau 1) := by
    rw [X.Etau_eq]
    exact finite_of_le_stabilizer X.hyp (H := X.E X.QT (2 * 1))
      (inf_le_left.trans (X.Q_le_Gi (2 * 1)))
  have hEq : X.E X.QT 0 = X.Etau 1 := by
    have hE2le' : X.E X.QT 0 ≤ X.Etau 1 := by rwa [X.Etau_eq]
    exact Subgroup.eq_of_le_of_card_ge hE2le' (le_of_eq hcard.symm)
  obtain ⟨t, ht, ht02, -, -⟩ := IsSK.exists_t (X := X) (X.isSK_QT hGT hs hodd h5 hX)
  have hTE : t ∈ Subgroup.normalizer (X.E X.QT 0 : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub t (X.E X.QT 0) = X.E X.QT 0
    rw [IsSK.conjSub_E_zero (X := X) (U := X.QT) ht.1 ht02, hEq, X.Etau_eq]
    norm_num
  have hM : X.normGi X.QT 0 ≤ Subgroup.normalizer (X.E X.QT 0 : Set G) := by
    intro g hg
    obtain ⟨hgM, hgG0⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub g (X.E X.QT 0) = X.E X.QT 0
    have hQ : conjSub g (X.Q 0) = X.Q 0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)) hgG0)
    have hMn : conjSub g (M X.QT) = M X.QT := conjSub_eq_of_mem hgM
    rw [show X.E X.QT 0 = X.Q 0 ⊓ M X.QT from rfl, conjSub_inf, hQ, hMn]
  have hD := X.eq_QT_of_normal (D := X.E X.QT 0) X.QT_le_E (le_inf le_rfl hE2le) hM ht.1 ht02 hTE
  exact X.not_Z_le_GT hc hGT hs hodd h5 hX 0
    (X.Z_zero_le_E.trans ((le_of_eq hD).trans X.QT_le_GT))

end Setup

end CFSG.Quasithin.St84
