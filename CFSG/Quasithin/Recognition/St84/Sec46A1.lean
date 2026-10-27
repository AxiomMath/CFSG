module

public import CFSG.Quasithin.Recognition.St84.Sec46Cases
public import CFSG.Quasithin.Recognition.St84.Sec4Sections
public import CFSG.Quasithin.Recognition.St84.Sec4Local

import CFSG.Quasithin.Recognition.St84.Gen.NatSecLines
import CFSG.Quasithin.Recognition.St84.Gen.NatSecPre
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Recognition.St84.Sec6QQuot

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable (X : Setup Γ G)

theorem caseA_card (X : Setup Γ G) (A : X.CaseA) :
    Nat.card X.S = 2 ^ (3 * X.n 0 + 3 * X.n 1) ∧
      ∀ i : ℤ, Nat.card (X.Q i) = 2 ^ (2 * X.n i + 3 * X.n (i + 1)) := by
  have H := A.hyp
  have hpc : pCoreOf 2 (X.arcStab 0 ((7 : ℕ) : ℤ)) = ⊥ := by
    have hGT : X.arcStab 0 ((7 : ℕ) : ℤ) = X.GT := by
      have h := H.longReg.2 0 7 (by norm_num)
      simpa using h
    rw [hGT, X.GT_eq_K_of_odd H]
    have h := inf_eq_bot_of_odd_of_isPGroup (A := X.K) (B := pCoreOf 2 X.K)
      X.odd_card_K (pCoreOf_isPGroup' X.K)
    rwa [inf_eq_right.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 X.K)] at h
  have hcardS : Nat.card X.S = 2 ^ (3 * X.n 0 + 3 * X.n 1) := by
    have h := X.card_S_eq_pow H.sing H.odd_s
    have hp : Nat.card (pCoreOf 2 (X.arcStab 0 ((7 : ℕ) : ℤ))) = 1 := by
      rw [hpc]
      simp
    rw [hp, Nat.mul_one] at h
    have hpow : (2 ^ X.n 0 * 2 ^ X.n 1) ^ 3 =
        2 ^ (3 * X.n 0 + 3 * X.n 1) := by
      rw [← pow_add, ← pow_mul]
      ring
    calc Nat.card X.S = (2 ^ X.n 0 * 2 ^ X.n 1) ^ ((7 - 1) / 2) := h
      _ = (2 ^ X.n 0 * 2 ^ X.n 1) ^ 3 := by norm_num
      _ = 2 ^ (3 * X.n 0 + 3 * X.n 1) := hpow
  have hQ0 : Nat.card (X.Q 0) = 2 ^ (2 * X.n 0 + 3 * X.n 1) := by
    haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi 0)
    have hrel : (X.Q 0).relIndex X.S = 2 ^ X.n 0 := by
      rw [← X.edgeSylow_zero, X.relIndex_Q_edgeSylow 0]
    have hle : X.Q 0 ≤ X.S := by
      rw [← X.edgeSylow_zero]
      exact X.Q_le_edgeSylow_left 0
    have hcard := Subgroup.relIndex_mul_card (H := X.Q 0) (K := X.S)
    rw [hrel, inf_eq_left.mpr hle] at hcard
    refine Nat.eq_of_mul_eq_mul_left (n := 2 ^ X.n 0)
      (Nat.pow_pos (by norm_num : (0 : ℕ) < 2)) ?_
    rw [hcard, hcardS, ← pow_add]
    congr 1
    ring
  have hQ1 : Nat.card (X.Q 1) = 2 ^ (2 * X.n 1 + 3 * X.n 0) := by
    haveI : Finite ↥(X.Q 1) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi 1)
    have hrel : (X.Q 1).relIndex X.S = 2 ^ X.n 1 := by
      rw [← X.edgeSylow_zero]
      exact X.relIndex_Q_succ_edgeSylow 0
    have hle : X.Q 1 ≤ X.S := by
      rw [← X.edgeSylow_zero]
      exact X.Q_le_edgeSylow 0
    have hcard := Subgroup.relIndex_mul_card (H := X.Q 1) (K := X.S)
    rw [hrel, inf_eq_left.mpr hle] at hcard
    refine Nat.eq_of_mul_eq_mul_left (n := 2 ^ X.n 1)
      (Nat.pow_pos (by norm_num : (0 : ℕ) < 2)) ?_
    rw [hcard, hcardS, ← pow_add]
    congr 1
    ring
  refine ⟨hcardS, ?_⟩
  intro i
  rcases Int.even_or_odd' i with ⟨m, hm | hm⟩
  · have hni : X.n i = X.n 0 := by
      rw [hm, show 2 * m = 0 + 2 * m by ring, X.n_add]
    have hni1 : X.n (i + 1) = X.n 1 := by
      rw [hm, show 2 * m + 1 = 1 + 2 * m by ring, X.n_add]
    have hQi : X.Q i = conjSub (X.τ ^ m) (X.Q 0) := by
      rw [show i = 0 + 2 * m by omega, X.Q_add]
    rw [hQi, card_conjSub, hQ0, hni, hni1]
  · have hni : X.n i = X.n 1 := by
      rw [hm, show 2 * m + 1 = 1 + 2 * m by ring, X.n_add]
    have hni1 : X.n (i + 1) = X.n 0 := by
      rw [hm, show 2 * m + 1 + 1 = 0 + 2 * (m + 1) by ring]
      exact X.n_add (m + 1) 0
    have hQi : X.Q i = conjSub (X.τ ^ m) (X.Q 1) := by
      rw [show i = 1 + 2 * m by omega, X.Q_add]
    rw [hQi, card_conjSub, hQ1, hni, hni1]

theorem caseA_pos (X : Setup Γ G) (A : X.CaseA) :
    X.Z (-1) ⊔ X.Q 1 = X.S ∧ X.Z 1 ⊔ X.Q (-1) = X.edgeSylow (-1) := by
  have H := A.hyp
  have hBm : X.HasB (-1) 2 :=
    (X.hasB_iff_of_even (i := -1) (j := 1) (by norm_num) 2).mpr A.b₁
  have hK : X.K ≤ Subgroup.normalizer (X.Z (-1) : Set G) :=
    fun k hk => mem_normalizer_iff_conjSub.mpr (X.Z_normal (-1) k (X.K_le_Gi (-1) hk))
  have hA : X.Z (-1) ≤ X.edgeSylow 0 := by
    rw [X.edgeSylow_zero]
    exact (X.Z_le_Q_of_lt hBm (j := 0) (by norm_num)).trans (X.Q_le_edgeSylow_left 0)
  have hsup1 : X.Z (-1) ⊔ X.Q 1 = X.S := by
    have hnot : ¬ X.Z (-1) ≤ X.Q 1 := by
      have h := (X.not_Z_le_Q_edge hBm).1
      simpa using h
    have h := X.sup_Q_eq_edgeSylow_of_gen (i := 0) (A := X.Z (-1))
      (inf_le_left.trans hK) hA hnot
    simpa [X.edgeSylow_zero] using h
  refine ⟨hsup1, ?_⟩
  obtain ⟨t, -, htref⟩ := X.exists_reflection H 0
  have htZ : t • X.vert (-1) = X.vert 1 := by
    have h := htref (-1)
    simpa using h
  have htQ : t • X.vert 1 = X.vert (-1) := by
    have h := htref 1
    simpa using h
  have ht0 : t • X.vert 0 = X.vert 0 := by
    have h := htref 0
    simpa using h
  have htedge : conjSub t (X.edgeSylow 0) = X.edgeSylow (-1) :=
    X.conjSub_edgeSylow_swap ht0 htQ
  have h := congrArg (conjSub t) hsup1
  rw [← X.edgeSylow_zero] at h
  rw [conjSub_sup, ← Z_smul X X htZ, ← Q_smul X X htQ, htedge] at h
  exact h

theorem caseA_3a (X : Setup Γ G) (A : X.CaseA) :
    ⁅X.Z (-1), X.Z 1⁆ ≤ centerOf (X.L 0) ∧
      ⁅X.Z (-1), X.Z 1⁆ ⊓ centerOf (X.L 1) = ⊥ ∧
      X.Z 1 ≠ centerOf (X.L 1) := by
  have H := A.hyp
  have hpos := X.caseA_pos A
  have hZ1G0 : X.Z 1 ≤ X.Gi 0 := by
    have h := A.b₁.1 (-1) (by norm_num)
    simpa using h
  have hU : ⁅X.Z (-1), X.Z 1⁆ ≤ X.Gi 0 := (fun r hr => hZ1G0 (Subgroup.mem_inf.mp (A.R_le hr)).2)
  have hcentZ1 : X.Z 1 ≤ Subgroup.centralizer ((⁅X.Z (-1), X.Z 1⁆ : Subgroup G) : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (X.Z_commute 1 z hz r ((Subgroup.mem_inf.mp (A.R_le hr)).2)).symm
  have hcentZm1 : X.Z (-1) ≤ Subgroup.centralizer ((⁅X.Z (-1), X.Z 1⁆ : Subgroup G) : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (X.Z_commute (-1) z hz r ((Subgroup.mem_inf.mp (A.R_le hr)).1)).symm
  have hcentQ1 : X.Q 1 ≤ Subgroup.centralizer ((⁅X.Z (-1), X.Z 1⁆ : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hcr : r ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 1 ((Subgroup.mem_inf.mp (A.R_le hr)).2))).2
    exact (Subgroup.mem_centralizer_iff.mp hcr q hq).symm
  have hcentQm1 : X.Q (-1) ≤ Subgroup.centralizer ((⁅X.Z (-1), X.Z 1⁆ : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hcr : r ∈ Subgroup.centralizer (X.Q (-1) : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center (-1) ((Subgroup.mem_inf.mp (A.R_le hr)).1))).2
    exact (Subgroup.mem_centralizer_iff.mp hcr q hq).symm
  have h1 : X.edgeSylow (-1) ≤ Subgroup.centralizer ((⁅X.Z (-1), X.Z 1⁆ : Subgroup G) : Set G) := by
    rw [← hpos.2]
    exact sup_le hcentZ1 hcentQm1
  have h2 : X.edgeSylow 0 ≤ Subgroup.centralizer ((⁅X.Z (-1), X.Z 1⁆ : Subgroup G) : Set G) := by
    rw [X.edgeSylow_zero, ← hpos.1]
    exact sup_le hcentZm1 hcentQ1
  have hcenter0 : ⁅X.Z (-1), X.Z 1⁆ ≤ centerOf (X.L 0) :=
    X.le_centerOf_L H.char 0 hU h1 h2
  have hdisj : ⁅X.Z (-1), X.Z 1⁆ ⊓ centerOf (X.L 1) = ⊥ := by
    rw [eq_bot_iff]
    calc ⁅X.Z (-1), X.Z 1⁆ ⊓ centerOf (X.L 1)
        ≤ centerOf (X.L 0) ⊓ centerOf (X.L 1) := inf_le_inf hcenter0 le_rfl
      _ = ⊥ := X.centerOf_L_inf_succ H.char 0
  refine ⟨hcenter0, hdisj, ?_⟩
  intro hZeq
  have hRle : ⁅X.Z (-1), X.Z 1⁆ ≤ centerOf (X.L 1) := by
    rw [← hZeq]
    exact fun r hr => (Subgroup.mem_inf.mp (A.R_le hr)).2
  have hle : ⁅X.Z (-1), X.Z 1⁆ ≤
      ⁅X.Z (-1), X.Z 1⁆ ⊓ centerOf (X.L 1) := le_inf le_rfl hRle
  have hbot : ⁅X.Z (-1), X.Z 1⁆ = ⊥ := by
    rw [hdisj] at hle
    exact le_bot_iff.mp hle
  exact A.R_ne hbot

theorem caseA_R_elem (X : Setup Γ G) (A : X.CaseA) :
    IsElemAbelian 2 ⁅X.Z (-1), X.Z 1⁆ ∧
      ⁅X.Z (-1), X.Z 1⁆ ≤ pCoreOf 2 (X.arcStab (-3) 3) := by
  have H := A.hyp
  have hBm : X.HasB (-1) 2 :=
    (X.hasB_iff_of_even (i := -1) (j := 1) (by norm_num) 2).mpr A.b₁
  have hR2 : IsPGroup 2 (⁅X.Z (-1), X.Z 1⁆ : Subgroup G) :=
    (pCoreOf_isPGroup' (X.Gi 1)).to_le
      (fun r hr => X.Z_le_Q 1 ((Subgroup.mem_inf.mp (A.R_le hr)).2))
  have hfix : ⁅X.Z (-1), X.Z 1⁆ ≤ X.arcStab (-3) 3 := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    intro r hr
    have hr1 : r ∈ X.Z 1 := (Subgroup.mem_inf.mp (A.R_le hr)).2
    have hrm : r ∈ X.Z (-1) := (Subgroup.mem_inf.mp (A.R_le hr)).1
    rcases le_total j 1 with hj1 | hj1
    · exact MulAction.mem_stabilizer_iff.mp (hBm.Z_le_Gi (j := j) (by omega) hrm)
    · exact MulAction.mem_stabilizer_iff.mp (A.b₁.Z_le_Gi (j := j) (by omega) hr1)
  have hpc : ⁅X.Z (-1), X.Z 1⁆ ≤
      pCoreOf 2 (X.arcStab (-3) ((-3) + (6 : ℤ))) :=
    X.le_pCoreOf_arcStab_r H hR2 hfix
  have hea : IsElemAbelian 2 (pCoreOf 2 (X.arcStab (-3) ((-3) + (6 : ℤ)))) :=
    X.isElemAbelian_pCoreOf_arcStab_r H (-3)
  exact ⟨hea.mono hpc, by simpa using hpc⟩

private theorem caseA_isElemSec_Z_one (X : Setup Γ G) (A : X.CaseA) :
    IsElemSec (centerOf (X.L 1)) (X.Z 1) := by
  have H := A.hyp
  have hpos := X.caseA_pos A
  have hRelem := X.caseA_R_elem A
  have hZ1comm : IsMulCommutative ↥(X.Z 1) :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (X.Z_commute 1 a.1 a.2 b.1 b.2))
  have hP : IsSylowTwoOf (X.Z (-1) ⊔ X.Q 1) (X.L 1) := by
    rw [hpos.1, ← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L_succ 0
  have hRle : ⁅X.Z (-1), X.Z 1⁆ ≤ X.Z 1 := fun r hr =>
    (Subgroup.mem_inf.mp (A.R_le hr)).2
  have hsq : ∀ x ∈ X.Z 1, x ^ 2 ∈ centerOf (X.L 1) :=
    X.sq_le_centerOf_L hP hRle hRelem.1
  refine ⟨X.centerOf_L_le_Z H.char 1, ?_, hsq⟩
  rw [Subgroup.commutator_self_eq_bot_iff.mpr hZ1comm]
  exact bot_le

private theorem caseA_relIndex_relCent_S_le (X : Setup Γ G) (A : X.CaseA)
    (hEZ : X.Z 1 ≤ Subgroup.normalizer (centerOf (X.L 1) : Set G)) :
    (relCent (X.Z 1) (centerOf (X.L 1)) X.S).relIndex (X.Z 1) ≤ 2 ^ X.n 1 := by
  have hpos := X.caseA_pos A
  have hnneg : X.n (-1) = X.n 1 := by
    rw [show (-1 : ℤ) = 1 + 2 * (-1) by norm_num, X.n_add]
  haveI : Finite ↥(X.Z 1) := finite_of_le_stabilizer X.hyp (X.Z_le_Gi 1)
  have hBrel : X.Z 1 ⊓ X.Q (-1) ≤
      relCent (X.Z 1) (centerOf (X.L 1)) X.S := by
    intro x hx
    rw [mem_relCent hEZ]
    refine ⟨(Subgroup.mem_inf.mp hx).1, ?_⟩
    intro s hs
    have hxQm : x ∈ X.Q (-1) := (Subgroup.mem_inf.mp hx).2
    have hxZ1 : x ∈ X.Z 1 := (Subgroup.mem_inf.mp hx).1
    have hs' : s ∈ X.Z (-1) ⊔ X.Q 1 := by rw [hpos.1]; exact hs
    have hxcentZm : X.Z (-1) ≤ Subgroup.centralizer ({x} : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyx : y = x := by simpa using hy
      rw [hyx]
      have hzc : z ∈ Subgroup.centralizer (X.Q (-1) : Set G) :=
        (Subgroup.mem_inf.mp (X.Z_le_center (-1) hz)).2
      exact Subgroup.mem_centralizer_iff.mp hzc x hxQm
    have hxcentQ : X.Q 1 ≤ Subgroup.centralizer ({x} : Set G) := by
      intro q hq'
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyx : y = x := by simpa using hy
      rw [hyx]
      have hxc : x ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
        (Subgroup.mem_inf.mp (X.Z_le_center 1 hxZ1)).2
      exact (Subgroup.mem_centralizer_iff.mp hxc q hq').symm
    have hsC : s ∈ Subgroup.centralizer ({x} : Set G) :=
      (sup_le hxcentZm hxcentQ) hs'
    have hcomm : s * x = x * s :=
      (Subgroup.mem_centralizer_iff.mp hsC x (by simp)).symm
    have hone : ⁅x, s⁆ = 1 := by
      simp only [commutatorElement_def]
      rw [show x * s = s * x from hcomm.symm]
      group
    rw [hone]
    exact (centerOf (X.L 1)).one_mem
  have hBrelIdx : (X.Z 1 ⊓ X.Q (-1)).relIndex (X.Z 1) ≤ 2 ^ X.n 1 := by
    rw [Subgroup.inf_relIndex_left]
    have hZ1edge : X.Z 1 ≤ X.edgeSylow (-1) := by
      rw [← hpos.2]
      exact le_sup_left
    have hne : (X.Q (-1)).relIndex (X.edgeSylow (-1)) ≠ 0 := by
      rw [X.relIndex_Q_edgeSylow (-1)]
      exact pow_ne_zero _ (by norm_num)
    have h := Subgroup.relIndex_le_of_le_right hZ1edge hne
    rwa [X.relIndex_Q_edgeSylow (-1), hnneg] at h
  have hBne : (X.Z 1 ⊓ X.Q (-1)).relIndex (X.Z 1) ≠ 0 := by
    intro h0
    have hcard := Subgroup.relIndex_mul_card
      (H := X.Z 1 ⊓ X.Q (-1)) (K := X.Z 1)
    rw [h0, zero_mul] at hcard
    exact (Nat.card_pos (α := ↥(X.Z 1))).ne' hcard.symm
  exact (Subgroup.relIndex_le_of_le_left hBrel hBne).trans hBrelIdx

private theorem caseA_relIndex_relCent_edgeSylow_one_le (X : Setup Γ G) (A : X.CaseA)
    (hEZ : X.Z 1 ≤ Subgroup.normalizer (centerOf (X.L 1) : Set G)) :
    (relCent (X.Z 1) (centerOf (X.L 1)) (X.edgeSylow 1)).relIndex (X.Z 1) ≤ 2 ^ X.n 1 := by
  have H := A.hyp
  have hT4 := X.caseA_relIndex_relCent_S_le A hEZ
  obtain ⟨t, ht, htref⟩ := X.exists_reflection H 1
  have ht0 : t • X.vert 0 = X.vert 2 := by
    have h := htref (-1)
    simpa using h
  have ht1 : t • X.vert 1 = X.vert 1 := by
    have h := htref 0
    simpa using h
  have htZ : conjSub t (X.Z 1) = X.Z 1 := X.Z_normal 1 t ht.1
  have htL : conjSub t (X.L 1) = X.L 1 :=
    mem_normalizer_iff_conjSub.mp (le_normalizer_oTwoPrime (X.Gi 1) ht.1)
  have htZL : conjSub t (centerOf (X.L 1)) = centerOf (X.L 1) := by
    rw [← centerOf_conjSub, htL]
  have htS : conjSub t X.S = X.edgeSylow 1 := by
    rw [← X.edgeSylow_zero]
    exact X.conjSub_edgeSylow_swap ht0 ht1
  have hEq : conjSub t (relCent (X.Z 1) (centerOf (X.L 1)) X.S) =
      relCent (X.Z 1) (centerOf (X.L 1)) (X.edgeSylow 1) := by
    rw [conjSub_relCent t hEZ, htZ, htZL, htS]
  have hmap := Subgroup.relIndex_map_map_of_injective
    (H := relCent (X.Z 1) (centerOf (X.L 1)) X.S) (K := X.Z 1)
    (f := (MulAut.conj t).toMonoidHom) (MulEquiv.injective _)
  rw [show (relCent (X.Z 1) (centerOf (X.L 1)) X.S).map
        (MulAut.conj t).toMonoidHom
      = conjSub t (relCent (X.Z 1) (centerOf (X.L 1)) X.S) from rfl,
    show (X.Z 1).map (MulAut.conj t).toMonoidHom = conjSub t (X.Z 1) from rfl,
    hEq, htZ] at hmap
  rw [hmap]
  exact hT4

theorem caseA_commutator_Z_one_S (X : Setup Γ G) (A : X.CaseA) :
    ⁅X.Z 1, X.S⁆ = ⁅X.Z (-1), X.Z 1⁆ := by
  have hpos := X.caseA_pos A
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro z hz s hs
    have hs' : s ∈ X.Z (-1) ⊔ X.Q 1 := by rw [hpos.1]; exact hs
    have hQ1norm : X.S ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
      ((X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_right).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
    have hZnormQ : X.Z (-1) ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
      (le_sup_left.trans hpos.1.le).trans hQ1norm
    have hs'' : s ∈ ((X.Z (-1) : Subgroup G) : Set G) * ((X.Q 1 : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (X.Z (-1)) (X.Q 1) hZnormQ]
      exact hs'
    obtain ⟨z', hz', q, hq', hprod⟩ := Set.mem_mul.mp hs''
    have hzc : z ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2
    have hzq : ⁅z, q⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hzc q hq').symm
    have hmemR : ⁅z, z'⁆ ∈ ⁅X.Z (-1), X.Z 1⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hz hz'
    have h1 : ⁅z, z' * q⁆ = ⁅z, z'⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hzq]
      group
    rw [← hprod, h1]
    exact hmemR
  · calc ⁅X.Z (-1), X.Z 1⁆ ≤ ⁅X.S, X.Z 1⁆ :=
          Subgroup.commutator_mono (by rw [← hpos.1]; exact le_sup_left) le_rfl
      _ = ⁅X.Z 1, X.S⁆ := Subgroup.commutator_comm _ _

private theorem caseA_card_R (X : Setup Γ G) (A : X.CaseA)
    (hNat : NatQuot (X.L 1) (X.Z 1) (centerOf (X.L 1)) (X.n 1)) :
    Nat.card (⁅X.Z (-1), X.Z 1⁆ : Subgroup G) = 2 ^ X.n 1 := by
  have H := A.hyp
  have h3a := X.caseA_3a A
  have hcommRS := X.caseA_commutator_Z_one_S A
  have hlineR : (centerOf (X.L 1)).relIndex
      (⁅X.Z (-1), X.Z 1⁆ ⊔ centerOf (X.L 1)) = 2 ^ X.n 1 := by
    rw [← hcommRS, hNat.comm_eq X.S (X.isSylowTwoOf_edgeSylow_L_succ 0)]
    exact hNat.line X.S (X.isSylowTwoOf_edgeSylow_L_succ 0)
  have hRnormZL : ⁅X.Z (-1), X.Z 1⁆ ≤ Subgroup.normalizer (centerOf (X.L 1) : Set G) :=
    fun r hr => X.Gi_le_normalizer_centerOf_L 1
      (X.Z_le_Gi 1 (Subgroup.mem_inf.mp (A.R_le hr)).2)
  have hcardSup : Nat.card ↥((⁅X.Z (-1), X.Z 1⁆ : Subgroup G) ⊔ centerOf (X.L 1)) =
      Nat.card (⁅X.Z (-1), X.Z 1⁆ : Subgroup G) * Nat.card (centerOf (X.L 1)) := by
    rw [sup_comm]
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (centerOf (X.L 1)) (⁅X.Z (-1), X.Z 1⁆ : Subgroup G) hRnormZL
      (disjoint_iff.mpr (by rw [inf_comm, h3a.2.1]))]
    rw [mul_comm]
  haveI : Finite ↥(centerOf (X.L 1)) :=
    finite_of_le_stabilizer X.hyp (H := centerOf (X.L 1))
      ((X.centerOf_L_le_Z H.char 1).trans (X.Z_le_Gi 1))
  have hrel := Subgroup.relIndex_mul_card
    (H := centerOf (X.L 1))
    (K := (⁅X.Z (-1), X.Z 1⁆ : Subgroup G) ⊔ centerOf (X.L 1))
  rw [inf_eq_left.mpr le_sup_right, hlineR, hcardSup] at hrel
  rw [Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(centerOf (X.L 1)))) hrel]

private theorem caseA_R_eq_pCoreOf (X : Setup Γ G) (A : X.CaseA)
    (hcardR : Nat.card (⁅X.Z (-1), X.Z 1⁆ : Subgroup G) = 2 ^ X.n 1) :
    ⁅X.Z (-1), X.Z 1⁆ = pCoreOf 2 (X.arcStab (-3) 3) := by
  have H := A.hyp
  have hRelem := X.caseA_R_elem A
  have hQgne : pCoreOf 2 (X.arcStab (-3) ((-3) + (6 : ℤ))) ≠ ⊥ := by
    intro hbot
    exact A.R_ne (le_bot_iff.mp (hbot ▸ hRelem.2))
  have hQgcard : Nat.card (pCoreOf 2 (X.arcStab (-3) ((-3) + (6 : ℤ)))) = 2 ^ X.n 1 := by
    have h := (X.pCoreOf_arcStab_r H (-3) hQgne).1
    rwa [show (-3 : ℤ) = 1 + 2 * (-2) by norm_num, X.n_add (-2) 1] at h
  haveI : Finite ↥(pCoreOf 2 (X.arcStab (-3) 3)) :=
    finite_of_le_stabilizer X.hyp (H := pCoreOf 2 (X.arcStab (-3) 3))
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
        (X.arcStab_le_Gi_left (by norm_num : (-3 : ℤ) < 3)))
  exact Subgroup.eq_of_le_of_card_ge hRelem.2
    (by rw [show pCoreOf 2 (X.arcStab (-3) 3) =
          pCoreOf 2 (X.arcStab (-3) ((-3) + (6 : ℤ))) by norm_num, hQgcard, hcardR])

theorem caseA_3b (X : Setup Γ G) (A : X.CaseA) :
    NatQuot (X.L 1) (X.Z 1) (centerOf (X.L 1)) (X.n 1) ∧
      Nat.card (⁅X.Z (-1), X.Z 1⁆ : Subgroup G) = 2 ^ X.n 1 ∧
      ⁅X.Z (-1), X.Z 1⁆ = pCoreOf 2 (X.arcStab (-3) 3) := by
  have H := A.hyp
  have h3a := X.caseA_3a A
  haveI : Finite ↥(X.Gi 1) := X.hyp.finite_stab (X.vert 1)
  haveI : Finite ↥(X.L 1) := finite_of_le_stabilizer X.hyp (X.L_le_Gi 1)
  haveI : Finite ↥(X.Z 1) := finite_of_le_stabilizer X.hyp (H := X.Z 1) (X.Z_le_Gi 1)
  have hNloc := X.hyp.isLocL2_oTwoPrime (X.vert 1)
  have hQeq : pCoreOf 2 (X.L 1) = X.Q 1 := hNloc.pCoreOf_eq
  have hZQ : X.Z 1 ≤ Subgroup.centralizer (X.Q 1 : Set G) :=
    (X.Z_le_center 1).trans inf_le_right
  have hZ1leL : X.Z 1 ≤ X.L 1 := (X.Z_le_Q 1).trans (X.Q_le_L 1)
  have hGiL : X.Gi 1 ≤ Subgroup.normalizer (X.L 1 : Set G) := le_normalizer_oTwoPrime (X.Gi 1)
  have hZLnormL : X.L 1 ≤ Subgroup.normalizer (centerOf (X.L 1) : Set G) :=
    le_normalizer_centerOf_self (X.L 1)
  have hZLnormGi : X.Gi 1 ≤ Subgroup.normalizer (centerOf (X.L 1) : Set G) :=
    X.Gi_le_normalizer_centerOf_L 1
  have hLE : X.L 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := fun l hl =>
    mem_normalizer_iff_conjSub.mpr (X.Z_normal 1 l (X.L_le_Gi 1 hl))
  have hEZ : X.Z 1 ≤ Subgroup.normalizer (centerOf (X.L 1) : Set G) :=
    hZ1leL.trans hZLnormL
  have hq : IsL2Quot (X.n 1) (oTwoQuot ↥(X.L 1)) := hNloc.quot
  have hL : X.L 1 = ⁅X.L 1, X.L 1⁆ ⊔ X.Q 1 :=
    X.L_eq_commutator_sup_Q 1 (H.two_le_n 1) hq
  have hsec := X.caseA_isElemSec_Z_one A
  have hQcent : X.Q 1 ≤ Subgroup.centralizer (X.Z 1 : Set G) :=
    Subgroup.le_centralizer_iff.mp hZQ
  have hcore : ⁅X.Z 1, pCoreOf 2 (X.L 1)⁆ ≤ centerOf (X.L 1) := by
    rw [hQeq, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZQ]
    exact bot_le
  have hcent0 := relCent_L_eq (L := X.L 1) (Q := X.Q 1) (E := X.Z 1)
    (X.Z_le_Q 1) hQcent hL
  have hcent : relCent (X.Z 1) (centerOf (X.L 1)) (X.L 1) = centerOf (X.L 1) := by
    simpa [inf_of_le_left (X.centerOf_L_le_Z H.char 1)] using hcent0
  have hT4 := X.caseA_relIndex_relCent_S_le A hEZ
  have hT4' := X.caseA_relIndex_relCent_edgeSylow_one_le A hEZ
  have hgen : X.L 1 ≤ (X.S ⊔ X.edgeSylow 1) ⊔ pCoreOf 2 (X.L 1) := by
    rw [← X.edgeSylow_sup_edgeSylow 1, ← X.edgeSylow_zero]
    exact le_sup_left
  have hneZL : centerOf (X.L 1) ≠ X.Z 1 := fun h => h3a.2.2 h.symm
  have h16 := relIndex_eq_two_pow_of_lines (L := X.L 1) (E := X.Z 1)
    (Z := centerOf (X.L 1)) (T := X.S) (T' := X.edgeSylow 1)
    (le_trans (by norm_num : 1 ≤ 2) (H.two_le_n 1)) hq
    (X.centerOf_L_le_Z H.char 1) hEZ hLE hZLnormL
      ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)) hcore
    (X.isSylowTwoOf_edgeSylow_L_succ 0).1 (X.isSylowTwoOf_edgeSylow_L 1).1
    hgen hcent hneZL hT4 hT4'
  have hPre : NatPre (X.Gi 1) (X.L 1) (X.Z 1) (centerOf (X.L 1)) (X.n 1) :=
    { le := X.L_le_Gi 1
      norm_L := hGiL
      norm_E := fun g hg => mem_normalizer_iff_conjSub.mpr (X.Z_normal 1 g hg)
      norm_K := hZLnormGi
      sec := hsec
      card := h16.1
      core := fun q hq' z hz => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_iff.mp (hZQ hz) q hq')]
        exact (centerOf (X.L 1)).one_mem
      quot := hq
      nontriv := by
        by_contra! h
        exact h3a.2.2 (le_antisymm (by
          intro z hz
          have hrel : z ∈ relCent (X.Z 1) (centerOf (X.L 1)) (X.L 1) := by
            rw [mem_relCent hEZ]
            exact ⟨hz, fun l hl => by
              rw [← commutatorElement_inv (g₁ := l) (g₂ := z)]
              exact (centerOf (X.L 1)).inv_mem (h l hl z hz)⟩
          rwa [hcent] at hrel) (X.centerOf_L_le_Z H.char 1)) }
  have hC : 2 ^ X.n 1 ≤ (centerOf (X.L 1)).relIndex
      (relCent (X.Z 1) (centerOf (X.L 1)) X.S) := by
    rw [h16.2]
  have hNatGen : NatQuot (X.L 1) (X.Z 1) (centerOf (X.L 1)) (X.n 1) :=
    natQuot_of_two_pow_le (P := X.Gi 1) (H.two_le_n 1) hPre hZ1leL
      (X.isSylowTwoOf_edgeSylow_L_succ 0) hC
  have hcardR := X.caseA_card_R A hNatGen
  exact ⟨hNatGen, hcardR, X.caseA_R_eq_pCoreOf A hcardR⟩

end Setup

end CFSG.Quasithin.St84
