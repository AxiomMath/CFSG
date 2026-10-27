module

public import CFSG.Quasithin.Recognition.St84.Sec5Step13
public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
public import CFSG.Quasithin.Recognition.St84.WeissB
public import CFSG.Quasithin.Recognition.St84.Gen.R1Bridge
import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAmalgam
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2A
public import CFSG.Quasithin.Background.RonanF713Sylow
public import CFSG.Quasithin.Recognition.St84.Gen.Sec6LeafGen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
public import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement MatrixGroups

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

private def Qball2 (Y : Setup Γ G) : Subgroup G :=
  Y.Q 0 ⊓ Gm (Γ := Γ) (G := G) 2 (Y.vert 0)

private theorem sup_perfectCore_pCoreOf_eq {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {m : ℕ} (hm : 2 ≤ m) (h : IsL2Quot m (oTwoQuot ↥H)) :
    perfectCore H ⊔ pCoreOf 2 H = H := by
  haveI hperf : Group.IsPerfect (oTwoQuot ↥H) :=
    CFSG.Quasithin.F112R.isPerfect_of_isL2Quot hm h
  let π : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hKtop : (perfectCore (⊤ : Subgroup ↥H)).map π = ⊤ := by
    rw [map_perfectCore]
    have htop : (⊤ : Subgroup ↥H).map π = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective π hsurj]
    rw [htop]
    exact perfectCore_eq_self_of_perfect (Subgroup.commutator_eq_self (H := ⊤))
  have hsup : perfectCore (⊤ : Subgroup ↥H) ⊔ π.ker = ⊤ := by
    have h := Subgroup.comap_map_eq (f := π) (H := perfectCore (⊤ : Subgroup ↥H))
    rw [hKtop, Subgroup.comap_top] at h
    exact h.symm
  have hker : π.ker = CFSG.Open.pCore 2 ↥H := QuotientGroup.ker_mk' _
  have hmap : (perfectCore (⊤ : Subgroup ↥H) ⊔ CFSG.Open.pCore 2 ↥H).map H.subtype = H := by
    rw [hker] at hsup
    rw [hsup, Subgroup.map_top, Subgroup.range_subtype]
  rw [Subgroup.map_sup, map_perfectCore, Subgroup.map_top, Subgroup.range_subtype] at hmap
  simpa [pCoreOf] using hmap

private theorem Gi_zero_le_normalizer_Qball2 (Y : Setup Γ G) :
    Y.Gi 0 ≤ Subgroup.normalizer (Y.Qball2 : Set G) :=
  (le_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0))
    (stabilizer_le_normalizer_Gm Y.hyp 2 (Y.vert 0))).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem Q_zero_le_normalizer_Qball2 (Y : Setup Γ G) :
    Y.Q 0 ≤ Subgroup.normalizer (Y.Qball2 : Set G) :=
  (Y.Q_le_Gi 0).trans (Gi_zero_le_normalizer_Qball2 Y)

private theorem L_zero_le_normalizer_Qball2 (Y : Setup Γ G) :
    Y.L 0 ≤ Subgroup.normalizer (Y.Qball2 : Set G) :=
  (Y.L_le_Gi 0).trans (Gi_zero_le_normalizer_Qball2 Y)

private theorem exists_pow_two_of_mem {P : Subgroup G} (hP : IsPGroup 2 P) {z : G}
    (hz : z ∈ P) : ∃ m : ℕ, z ^ 2 ^ m = 1 := by
  obtain ⟨m, hm⟩ := hP.exists_pow_pow_eq_one (⟨z, hz⟩ : ↥P)
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

private theorem exists_mem_Q_zero_inf_Q_one_notMem_Q_neg_one (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀) : ∃ x ∈ Y.Q 0 ⊓ Y.Q 1, x ∉ Y.Q (-1) := by
  haveI : Finite ↥(Y.Q 0) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 0)
  by_contra hcon
  push Not at hcon
  have hle : Y.Q 0 ⊓ Y.Q 1 ≤ Y.Q (-1) ⊓ Y.Q 1 :=
    le_inf (fun x hx => hcon x hx) inf_le_right
  have hrel : (Y.Q (-1) ⊓ Y.Q 1).relIndex (Y.Q 0) = 4 := by
    have h := Y.relIndex_inf_Q H 0
    rw [show (0 : ℤ) + 1 = 1 by norm_num, H.n_one] at h
    simpa using h
  have hQS : (Y.Q 1).relIndex Y.S = 2 := by
    have h := Y.relIndex_Q_succ_edgeSylow 0
    rw [show (0 : ℤ) + 1 = 1 by norm_num, H.n_one] at h
    simpa [Y.edgeSylow_zero] using h
  have h2 : (Y.Q 0 ⊓ Y.Q 1).relIndex (Y.Q 0) ≤ 2 := by
    rw [Subgroup.inf_relIndex_left]
    have hne : (Y.Q 1).relIndex Y.S ≠ 0 := by rw [hQS]; norm_num
    calc (Y.Q 1).relIndex (Y.Q 0) ≤ (Y.Q 1).relIndex Y.S :=
          Subgroup.relIndex_le_of_le_right (Y.Q_le_edgeSylow_left 0) hne
      _ = 2 := hQS
  have hne : (Y.Q 0 ⊓ Y.Q 1).relIndex (Y.Q 0) ≠ 0 := by
    intro h0
    have hd := Subgroup.relIndex_dvd_card (Y.Q 0 ⊓ Y.Q 1) (Y.Q 0)
    rw [h0] at hd
    have hcard0 : Nat.card ↥(Y.Q 0) = 0 := Nat.eq_zero_of_zero_dvd hd
    haveI : Nonempty ↥(Y.Q 0) := ⟨1⟩
    have hpos : 0 < Nat.card ↥(Y.Q 0) := Nat.card_pos
    omega
  have h3 : (Y.Q (-1) ⊓ Y.Q 1).relIndex (Y.Q 0) ≤
      (Y.Q 0 ⊓ Y.Q 1).relIndex (Y.Q 0) :=
    Subgroup.relIndex_le_of_le_left hle hne
  omega

private theorem exists_adj_smul_ne_of_notMem_Q (Y : Setup Γ G) {x : G} (hxQ0 : x ∈ Y.Q 0)
    (hxQm1 : x ∉ Y.Q (-1)) :
    ∃ w : V, Γ.Adj (Y.vert (-1)) w ∧ x • w ≠ w ∧ Γ.dist (Y.vert 0) w ≤ 2 := by
  have hxGi0 : x ∈ Y.Gi 0 := Y.Q_le_Gi 0 hxQ0
  have hxGm1 : x ∈ Y.Gi (-1) := by
    simpa using (Y.Q_le_Gi_adj (0 : ℤ)).trans inf_le_left hxQ0
  have hpow := exists_pow_two_of_mem (pCoreOf_isPGroup' (Y.Gi 0)) hxQ0
  have hexw : ∃ w : V, Γ.Adj (Y.vert (-1)) w ∧ x • w ≠ w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hbadj, hbne⟩ := Y.hyp.exists_adj_ne (Y.vert (-1)) (Y.vert 0)
    have hxQ : x ∈ Y.Q (-1) :=
      mem_pCoreOf_of_fixes_two Y.hyp hxGm1 hpow (by simpa using (Y.adj (-1)))
        hbadj (Ne.symm hbne) (MulAction.mem_stabilizer_iff.mp hxGi0) (hcon b hbadj)
    exact hxQm1 hxQ
  obtain ⟨w, hwadj, hwmove⟩ := hexw
  have hwball : Γ.dist (Y.vert 0) w ≤ 2 := by
    have h01 : Γ.dist (Y.vert 0) (Y.vert (-1)) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (by simpa using (Y.adj (-1)).symm)
    have h1w : Γ.dist (Y.vert (-1)) w = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hwadj
    have htri := Y.hyp.isTree.connected.dist_triangle
      (u := Y.vert 0) (v := Y.vert (-1)) (w := w)
    omega
  exact ⟨w, hwadj, hwmove, hwball⟩

private theorem perfectCore_sup_Q_zero_eq_L_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    perfectCore ((Y.L 0).subgroupOf (Y.Gi 0)) ⊔ (Y.Q 0).subgroupOf (Y.Gi 0) =
      (Y.L 0).subgroupOf (Y.Gi 0) := by
  haveI : Finite ↥(Y.Gi 0) := Y.hyp.finite_stab (Y.vert 0)
  have hpc : pCoreOf 2 ((Y.L 0).subgroupOf (Y.Gi 0)) = (Y.Q 0).subgroupOf (Y.Gi 0) := by
    apply Subgroup.map_injective (Y.Gi 0).subtype_injective
    rw [CFSG.Quasithin.F6.map_pCoreOf_subgroupOf (Y.L_le_Gi 0),
      (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).pCoreOf_eq,
      Subgroup.map_subgroupOf_eq_of_le (Y.Q_le_Gi 0)]
  have hloc : IsL2Quot n₀ (oTwoQuot ↥(Y.L 0)) := Y.isL2Quot_L_zero H
  have hloc' : IsL2Quot n₀ (oTwoQuot ↥((Y.L 0).subgroupOf (Y.Gi 0))) := by
    obtain ⟨e⟩ := hloc
    exact ⟨(CFSG.Quasithin.Fan86.Univ.oTwoQuotMulEquiv
      (Subgroup.subgroupOfEquivOfLe (Y.L_le_Gi 0))).trans e⟩
  have h := sup_perfectCore_pCoreOf_eq H.two_le hloc'
  rwa [hpc] at h

private theorem conj_smul_eq_of_mem_Q_one (Y : Setup Γ G) {x l : G} (hxQ1 : x ∈ Y.Q 1)
    (hl1 : l • Y.vert 1 = Y.vert (-1)) :
    ∀ v : V, Γ.Adj (Y.vert (-1)) v → (l * x * l⁻¹) • v = v := by
  intro v hv
  have hlv : Γ.Adj (Y.vert 1) (l⁻¹ • v) := by
    have h1 : Γ.Adj (l • Y.vert 1) (l • (l⁻¹ • v)) := by
      rw [hl1, smul_inv_smul]
      exact hv
    exact (Y.hyp.adj_smul l (Y.vert 1) (l⁻¹ • v)).mp h1
  have hxfix : x • (l⁻¹ • v) = l⁻¹ • v :=
    Y.Q_fixes_neighbors_vert 1 (l⁻¹ • v) hlv x hxQ1
  calc (l * x * l⁻¹) • v
      = l • (x • (l⁻¹ • v)) := by simp [mul_smul]
    _ = l • (l⁻¹ • v) := by rw [hxfix]
    _ = v := smul_inv_smul _ _

private theorem exists_commutator_notMem_Qball2 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    ∃ n : ↥(Y.Gi 0), n ∈ (Y.Q 0).subgroupOf (Y.Gi 0) ∧
      ∃ l : ↥(Y.Gi 0), l ∈ perfectCore ((Y.L 0).subgroupOf (Y.Gi 0)) ∧
        ⁅l, n⁻¹⁆ ∉ Y.Qball2.subgroupOf (Y.Gi 0) := by
  obtain ⟨x, hx01, hxQm1⟩ := exists_mem_Q_zero_inf_Q_one_notMem_Q_neg_one Y H
  have hxQ0 : x ∈ Y.Q 0 := hx01.1
  have hxQ1 : x ∈ Y.Q 1 := hx01.2
  have hxGi0 : x ∈ Y.Gi 0 := Y.Q_le_Gi 0 hxQ0
  obtain ⟨w, hwadj, hwmove, hwball⟩ := exists_adj_smul_ne_of_notMem_Q Y hxQ0 hxQm1
  obtain ⟨g, hgL0, hg1⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).trans
    (Y.vert 1) (Y.vert (-1)) (by simpa using Y.adj 0) (by simpa using (Y.adj (-1)).symm)
  haveI hQ0norm : ((Y.Q 0).subgroupOf (Y.Gi 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0))
  have hsup := perfectCore_sup_Q_zero_eq_L_zero Y H
  let g' : ↥(Y.Gi 0) := ⟨g, Y.L_le_Gi 0 hgL0⟩
  have hg'L0 : g' ∈ (Y.L 0).subgroupOf (Y.Gi 0) := by
    rw [Subgroup.mem_subgroupOf]
    exact hgL0
  have hg'sup : g' ∈ perfectCore ((Y.L 0).subgroupOf (Y.Gi 0)) ⊔
      (Y.Q 0).subgroupOf (Y.Gi 0) := by
    rw [hsup]
    exact hg'L0
  obtain ⟨l, hl, q, hq, hglq⟩ := Subgroup.mem_sup_of_normal_right.mp hg'sup
  have hl1 : (l : G) • Y.vert 1 = Y.vert (-1) := by
    have hq1 : (q : G) • Y.vert 1 = Y.vert 1 :=
      Y.Q_fixes_neighbors_vert 0 (Y.vert 1) (by simpa using Y.adj 0) (q : G)
        (Subgroup.mem_subgroupOf.mp hq)
    have h := congrArg (fun z : ↥(Y.Gi 0) => (z : G) • Y.vert 1) hglq
    simp only [Subgroup.coe_mul, mul_smul] at h
    rw [hq1] at h
    have hg1' : (g' : G) • Y.vert 1 = Y.vert (-1) := hg1
    rw [hg1'] at h
    exact h
  have hu_fix := conj_smul_eq_of_mem_Q_one Y hxQ1 hl1
  let n : ↥(Y.Gi 0) := ⟨x, hxGi0⟩
  let l' : ↥(Y.Gi 0) := l
  let y : ↥(Y.Gi 0) := ⁅l', n⁻¹⁆
  refine ⟨n, ?_, l', ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact hxQ0
  · exact hl
  · intro hyN
    have hyball : (y : G) ∈ Y.Qball2 := Subgroup.mem_subgroupOf.mp hyN
    have hyval : (y : G) = (l : G) * x⁻¹ * (l : G)⁻¹ * x := by
      simp only [y, l', n, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
        inv_inv]
    have hyw : (y : G) • w = ((l : G) * x * (l : G)⁻¹)⁻¹ • (x • w) := by
      rw [hyval, ← mul_smul]
      congr 1
      group
    have hyw_ne : (y : G) • w ≠ w := by
      intro h
      have h2 : x • w = ((l : G) * x * (l : G)⁻¹) • w := by
        have h3 := congrArg (fun z => ((l : G) * x * (l : G)⁻¹) • z) h
        rw [hyw] at h3
        simpa [mul_smul, smul_inv_smul] using h3
      rw [hu_fix w hwadj] at h2
      exact hwmove h2
    have hfix := (mem_Gm (Γ := Γ) (G := G)).mp (Subgroup.mem_inf.mp hyball).2 w hwball
    exact hyw_ne hfix

private theorem pow_le_relIndex_Qball2 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    2 ^ (2 * n₀) ≤ Y.Qball2.relIndex (Y.Q 0) := by
  haveI : Finite ↥(Y.Gi 0) := Y.hyp.finite_stab (Y.vert 0)
  let G0 := ↥(Y.Gi 0)
  haveI : Finite G0 := ‹Finite ↥(Y.Gi 0)›
  let L0' : Subgroup G0 := (Y.L 0).subgroupOf (Y.Gi 0)
  let Q0' : Subgroup G0 := (Y.Q 0).subgroupOf (Y.Gi 0)
  let N2' : Subgroup G0 := Y.Qball2.subgroupOf (Y.Gi 0)
  let L' : Subgroup G0 := perfectCore L0'
  haveI hQ0normal : Q0'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0))
  have hWN : N2' ≤ Q0' := Subgroup.subgroupOf_mono (Y.Gi 0) inf_le_left
  have hQ0W : Q0' ≤ Subgroup.normalizer (N2' : Set G0) :=
    (Subgroup.comap_mono (Q_zero_le_normalizer_Qball2 Y)).trans
      (Subgroup.le_normalizer_comap _)
  haveI hWnormal : (N2'.subgroupOf Q0').Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hQ0W
  have hL'L0 : L' ≤ L0' := perfectCore_le L0'
  have hL'N : L' ≤ Subgroup.normalizer (Q0' : Set G0) :=
    hL'L0.trans ((Subgroup.comap_mono ((Y.L_le_Gi 0).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0)))).trans
      (Subgroup.le_normalizer_comap _))
  have hL'W : L' ≤ Subgroup.normalizer (N2' : Set G0) :=
    hL'L0.trans ((Subgroup.comap_mono (L_zero_le_normalizer_Qball2 Y)).trans
      (Subgroup.le_normalizer_comap _))
  have hloc : IsL2Quot n₀ (oTwoQuot ↥(Y.L 0)) := Y.isL2Quot_L_zero H
  have hloc' : IsL2Quot n₀ (oTwoQuot ↥L0') := by
    obtain ⟨e⟩ := hloc
    exact ⟨(CFSG.Quasithin.Fan86.Univ.oTwoQuotMulEquiv
      (Subgroup.subgroupOfEquivOfLe (Y.L_le_Gi 0))).trans e⟩
  have hL'2 : IsL2Quot n₀ (oTwoQuot ↥L') :=
    CFSG.Quasithin.F112R.isL2Quot_perfectCore H.two_le hloc'
  have hL'perf : Group.IsPerfect ↥L' :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect L0')
  have hQ0p : IsPGroup 2 ↥Q0' :=
    (pCoreOf_isPGroup' (Y.Gi 0)).of_equiv (Subgroup.subgroupOfEquivOfLe (Y.Q_le_Gi 0)).symm
  have hquotp : IsPGroup 2 (↥Q0' ⧸ N2'.subgroupOf Q0') :=
    hQ0p.to_quotient (N2'.subgroupOf Q0')
  obtain ⟨f, hf⟩ := IsPGroup.iff_card.mp hquotp
  have hrel : N2'.relIndex Q0' = 2 ^ f := by
    have heq : N2'.relIndex Q0' = (N2'.subgroupOf Q0').index := by
      have h := Subgroup.relIndex_subgroupOf (H := N2') (K := Q0') (L := Q0') le_rfl
      rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h
      exact h.symm
    rw [heq, Subgroup.index_eq_card, hf]
  have hcard : Nat.card ↥Q0' = 2 ^ f * Nat.card ↥N2' := by
    have h := Subgroup.relIndex_mul_card (H := N2') (K := Q0')
    rw [inf_eq_left.mpr hWN, hrel] at h
    exact h.symm
  have hrelG : Y.Qball2.relIndex (Y.Q 0) = 2 ^ f := by
    rw [← Subgroup.relIndex_subgroupOf (H := Y.Qball2) (K := Y.Q 0) (L := Y.Gi 0)
      (Y.Q_le_Gi 0)]
    exact hrel
  by_contra hcon
  push Not at hcon
  have hflt : f < 2 * n₀ := by
    have h : 2 ^ f < 2 ^ (2 * n₀) := by
      rw [← hrelG]
      exact hcon
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hcomm := CFSG.Quasithin.H13.Sec526.commutator_le_of_isL2Quot
    (L := L') (N := Q0') (W := N2') H.two_le hflt hL'perf hL'2 hL'N hL'W hWN hcard
  obtain ⟨n, hnN, l, hlL, hynot⟩ := exists_commutator_notMem_Qball2 Y H
  have hycomm : ⁅l, n⁻¹⁆ ∈ ⁅Q0', L'⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hlL (Q0'.inv_mem hnN)
  exact hynot (hcomm hycomm)

private theorem eq_bot_of_le_GT (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {U : Subgroup G}
    (hU : IsPGroup 2 U) (hle : U ≤ Y.GT) : U = ⊥ := by
  have h := inf_eq_bot_of_odd_of_isPGroup (A := Y.GT) (B := U) H.odd_GT hU
  rwa [inf_eq_right.mpr hle] at h

private theorem le_Gm_three_of_normal_fixes_dist_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {U : Subgroup G} {j : ℤ} (hUj : U ≤ Y.Gi j)
    (hUnorm : Y.Gi j ≤ Subgroup.normalizer (U : Set G)) {a : V}
    (ha : Γ.dist (Y.vert j) a = 3) (hUa : U ≤ MulAction.stabilizer G a) :
    U ≤ Gm (Γ := Γ) (G := G) 3 (Y.vert j) := by
  have hfix3 : ∀ v : V, Γ.dist (Y.vert j) v = 3 → U ≤ MulAction.stabilizer G v := by
    intro v hv u hu
    obtain ⟨P, hP0, hP3⟩ : ∃ P : Arc Γ 3, P.vert 0 = Y.vert j ∧ P.vert 3 = a := by
      have h := IsTree.exists_arc_between Y.hyp.isTree (Y.vert j) a
      rwa [ha] at h
    obtain ⟨Q, hQ0, hQ3⟩ : ∃ Q : Arc Γ 3, Q.vert 0 = Y.vert j ∧ Q.vert 3 = v := by
      have h := IsTree.exists_arc_between Y.hyp.isTree (Y.vert j) v
      rwa [hv] at h
    have hs3 : 3 ≤ s := le_trans (by norm_num) H.five_le
    obtain ⟨g, hg⟩ := arc_conj_of_le Y.hyp.adj_smul
      (fun a b c ha hb => Y.hyp.locTrans ha hb) H.sing (m := 3) hs3 P Q 1
      (by rw [hP0, hQ0]; exact one_smul G (Y.vert j))
    have hgj : g • Y.vert j = Y.vert j := by
      have h := hg 0 (by norm_num)
      rw [hP0] at h
      rwa [hQ0] at h
    have hga : g • a = v := by
      have h := hg 3 (by norm_num)
      rw [hP3] at h
      rwa [hQ3] at h
    have hgGj : g ∈ Y.Gi j := MulAction.mem_stabilizer_iff.mpr hgj
    have hu' : g⁻¹ * u * g ∈ U := by
      have h := (Subgroup.mem_normalizer_iff.mp (hUnorm ((Y.Gi j).inv_mem hgGj)) u).mp hu
      simpa using h
    have hfixa : (g⁻¹ * u * g) • a = a := hUa hu'
    calc u • v = u • (g • a) := by rw [hga]
      _ = (u * g) • a := (mul_smul u g a).symm
      _ = (g * (g⁻¹ * u * g)) • a := by rw [show u * g = g * (g⁻¹ * u * g) by group]
      _ = g • ((g⁻¹ * u * g) • a) := mul_smul g _ a
      _ = g • a := by rw [hfixa]
      _ = v := hga
  intro u hu
  rw [mem_Gm (Γ := Γ) (G := G)]
  intro v hv
  obtain ⟨P, hP0, hPd⟩ := IsTree.exists_arc_between Y.hyp.isTree (Y.vert j) v
  obtain ⟨Q, hQ⟩ := exists_arc_extend
    (fun u v huv => Y.hyp.exists_adj_ne u v) (fun u => Y.hyp.exists_adj u) P 3 hv
  have hQ0 : Q.vert 0 = Y.vert j := by rw [hQ 0 (by omega), hP0]
  have hQd : Q.vert (Γ.dist (Y.vert j) v) = v := by
    rw [hQ (Γ.dist (Y.vert j) v) le_rfl, hPd]
  have hq3 : Γ.dist (Y.vert j) (Q.vert 3) = 3 := by
    have h := Arc.dist_eq Y.hyp.isTree Q 3 le_rfl
    rwa [hQ0] at h
  have hfixj : u • Q.vert 0 = Q.vert 0 := by
    rw [hQ0]
    exact MulAction.mem_stabilizer_iff.mp (hUj hu)
  have hfix3' : u • Q.vert 3 = Q.vert 3 := (hfix3 (Q.vert 3) hq3) hu
  have hfixd := Arc.fixes_of_ends Y.hyp.isTree Y.hyp.adj_smul Q hfixj hfix3'
    (Γ.dist (Y.vert j) v) hv
  rwa [hQd] at hfixd

private theorem dist_one_neg_two (Y : Setup Γ G) :
    Γ.dist (Y.vert 1) (Y.vert (-2)) = 3 := by
  have h := Line.dist_eq Y.hyp.isTree Y.line (i := (-2 : ℤ)) (j := 1) (by norm_num)
  rw [SimpleGraph.dist_comm]
  simpa using h

private theorem Zt_one_fixes_neg_two (Y : Setup Γ G)
    (he : Y.ZtExt 0 2 2) (hW : Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2) :
    Y.Zt 1 ≤ MulAction.stabilizer G (Y.vert (-2)) := by
  obtain ⟨he1, -, -⟩ := he
  have h1 : (-(2 : ℤ)) ≤ (-2 : ℤ) := by norm_num
  have h2 : (-2 : ℤ) ≤ (2 : ℤ) := by norm_num
  intro w hw
  exact he1 (-2) h1 h2 ((hW.trans inf_le_left) hw)

private theorem Zt_one_le_Gm (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (he : Y.ZtExt 0 2 2) (hW : Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2) :
    Y.Zt 1 ≤ Gm (Γ := Γ) (G := G) 3 (Y.vert 1) := by
  have hUj : Y.Zt 1 ≤ Y.Gi 1 :=
    (Zt_le_Z Y 1).trans ((Y.Z_le_Q 1).trans (Y.Q_le_Gi 1))
  have hUnorm : Y.Gi 1 ≤ Subgroup.normalizer (Y.Zt 1 : Set G) :=
    Gi_one_le_normalizer_Zt_one Y H
  exact le_Gm_three_of_normal_fixes_dist_three (Y := Y) (H := H)
    (U := Y.Zt 1) (j := 1) (a := Y.vert (-2)) hUj hUnorm
    (dist_one_neg_two Y) (Zt_one_fixes_neg_two Y he hW)

private theorem le_Qball2_of_le_Gm_three (Y : Setup Γ G) {U : Subgroup G} {j : ℤ}
    (hadj : Γ.Adj (Y.vert 0) (Y.vert j)) (hU0 : U ≤ Y.Q 0)
    (hU : U ≤ Gm (Γ := Γ) (G := G) 3 (Y.vert j)) : U ≤ Y.Qball2 := by
  have hball : {v : V | Γ.dist (Y.vert 0) v ≤ 2} ⊆
      {v : V | Γ.dist (Y.vert j) v ≤ 3} := by
    intro v hv
    have htri := Y.hyp.isTree.connected.dist_triangle
      (u := Y.vert j) (v := Y.vert 0) (w := v)
    have h10 : Γ.dist (Y.vert j) (Y.vert 0) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (by simpa using hadj.symm)
    calc Γ.dist (Y.vert j) v ≤ Γ.dist (Y.vert j) (Y.vert 0) + Γ.dist (Y.vert 0) v := htri
      _ ≤ 1 + 2 := Nat.add_le_add (le_of_eq h10) hv
      _ = 3 := by norm_num
  refine le_inf hU0 ?_
  intro u hu
  rw [mem_Gm]
  intro v hv
  exact (mem_Gm (Γ := Γ) (G := G)).mp (hU hu) v (hball hv)

private theorem Zt_one_le_Qball2 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (he : Y.ZtExt 0 2 2) (hW : Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2) : Y.Zt 1 ≤ Y.Qball2 :=
  le_Qball2_of_le_Gm_three Y (by simpa using Y.adj 0)
    ((hW.trans inf_le_left).trans ((Zt_le_Z Y 0).trans (Y.Z_le_Q 0)))
    (Zt_one_le_Gm Y H he hW)

private theorem Gi_neg_one_le_normalizer_Zt_neg_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.Gi (-1) ≤ Subgroup.normalizer (Y.Zt (-1) : Set G) := by
  intro x hx
  have hx' : Y.τ * x * Y.τ⁻¹ ∈ Y.Gi 1 := by
    have h := Y.Gi_add (m := 1) (i := -1)
    rw [show (-1 : ℤ) + 2 * 1 = 1 by norm_num] at h
    rw [h]
    simpa using mul_mem_conjSub (g := Y.τ) hx
  have hnorm := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Gi_one_le_normalizer_Zt_one Y H hx')
  have hZtm1 : Y.Zt (-1) = conjSub (Y.τ ^ (-1 : ℤ)) (Y.Zt 1) := by
    simpa using Y.Zt_add (-1) 1
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub x (Y.Zt (-1)) = Y.Zt (-1)
  rw [hZtm1]
  simp only [zpow_neg_one]
  calc conjSub x (conjSub (Y.τ⁻¹) (Y.Zt 1))
      = conjSub (x * Y.τ⁻¹) (Y.Zt 1) := (conjSub_mul x (Y.τ⁻¹) (Y.Zt 1)).symm
    _ = conjSub (Y.τ⁻¹ * (Y.τ * x * Y.τ⁻¹)) (Y.Zt 1) := by
          rw [show x * Y.τ⁻¹ = Y.τ⁻¹ * (Y.τ * x * Y.τ⁻¹) by group]
    _ = conjSub (Y.τ⁻¹) (conjSub (Y.τ * x * Y.τ⁻¹) (Y.Zt 1)) :=
          conjSub_mul (Y.τ⁻¹) (Y.τ * x * Y.τ⁻¹) (Y.Zt 1)
    _ = conjSub (Y.τ⁻¹) (Y.Zt 1) := congrArg (conjSub (Y.τ⁻¹)) hnorm

private theorem Zt_neg_one_le_Qball2 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (he : Y.ZtExt 0 2 2) (hW : Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2) : Y.Zt (-1) ≤ Y.Qball2 := by
  obtain ⟨he1, -, -⟩ := he
  have h1 : (-(2 : ℤ)) ≤ (-2 : ℤ) := by norm_num
  have h2 : (-2 : ℤ) ≤ (2 : ℤ) := by norm_num
  have hZtm1 : Y.Zt (-1) = conjSub (Y.τ ^ (-1 : ℤ)) (Y.Zt 1) := by
    simpa using Y.Zt_add (-1) 1
  have hZtm2 : Y.Zt (-2) = conjSub (Y.τ ^ (-1 : ℤ)) (Y.Zt 0) := by
    simpa using Y.Zt_add (-1) 0
  have hZt0 : Y.Zt 0 = conjSub (Y.τ ^ (-1 : ℤ)) (Y.Zt 2) := by
    simpa using Y.Zt_add (-1) 2
  have hle0 : Y.Zt (-1) ≤ Y.Zt 0 := by
    rw [hZtm1, hZt0]
    exact conjSub_mono _ (hW.trans inf_le_right)
  have hle_m2 : Y.Zt (-1) ≤ Y.Zt (-2) := by
    rw [hZtm1, hZtm2]
    exact conjSub_mono _ (hW.trans inf_le_left)
  have hGim4 : Y.Zt (-2) ≤ Y.Gi (-4) := by
    rw [hZtm2]
    simp only [zpow_neg_one]
    calc conjSub (Y.τ⁻¹) (Y.Zt 0) ≤ conjSub (Y.τ⁻¹) (Y.Gi (-2)) :=
          conjSub_mono _ (he1 (-2) h1 h2)
      _ = Y.Gi (-4) := by
          have h := Y.Gi_add (m := -1) (i := -2)
          rw [show (-2 : ℤ) + 2 * (-1) = -4 by norm_num, zpow_neg_one] at h
          exact h.symm
  have hUj : Y.Zt (-1) ≤ Y.Gi (-1) :=
    (Zt_le_Z Y (-1)).trans ((Y.Z_le_Q (-1)).trans (Y.Q_le_Gi (-1)))
  have hUnorm : Y.Gi (-1) ≤ Subgroup.normalizer (Y.Zt (-1) : Set G) :=
    Gi_neg_one_le_normalizer_Zt_neg_one Y H
  have hdist : Γ.dist (Y.vert (-1)) (Y.vert (-4)) = 3 := by
    have h := Line.dist_eq Y.hyp.isTree Y.line (i := (-4 : ℤ)) (j := -1) (by norm_num)
    rw [SimpleGraph.dist_comm]
    simpa using h
  have hUa : Y.Zt (-1) ≤ MulAction.stabilizer G (Y.vert (-4)) :=
    fun w hw => hGim4 (hle_m2 hw)
  have hGm := le_Gm_three_of_normal_fixes_dist_three (Y := Y) (H := H)
    (U := Y.Zt (-1)) (j := -1) (a := Y.vert (-4)) hUj hUnorm hdist hUa
  exact le_Qball2_of_le_Gm_three Y (by simpa using (Y.adj (-1)).symm)
    (hle0.trans ((Zt_le_Z Y 0).trans (Y.Z_le_Q 0))) hGm


private theorem card_S_le_eight_q0_cube (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) :
    Nat.card Y.S ≤ 2 ^ (3 * n₀ + 3) := by
  have hs7 : s ≤ 7 := by
    have := s_sub_one_le_of_isMaxRegLen Y H hr
    omega
  have hs5 : 5 ≤ s := H.five_le
  have hs : s = 5 ∨ s = 7 := by
    interval_cases s
    · exact Or.inl rfl
    · exfalso
      obtain ⟨k, hk⟩ := H.odd_s
      omega
    · exact Or.inr rfl
  rcases hs with h5 | h7
  · by_cases h06 : Y.LeftTransAt 0 6 ∧ Y.RightTransAt 0 6
    · have h := card_S_of_isMaxRegLen_six_reg Y H hr h5 h06
      calc Nat.card Y.S = 4 * 2 ^ (3 * n₀) := h
        _ = 2 ^ (3 * n₀ + 2) := by
              rw [show (4 : ℕ) = 2 ^ 2 by norm_num, mul_comm, ← pow_add]
        _ ≤ 2 ^ (3 * n₀ + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · have h17 : Y.LeftTransAt 1 7 ∧ Y.RightTransAt 1 7 := by
        rcases regular_at_zero_or_one Y hr with h | h
        · exact absurd h h06
        · exact h
      have hc : Y.J2Arc := ⟨h17, h06⟩
      have h := card_S_of_isMaxRegLen_six_J2Arc Y H hr hc h5
      calc Nat.card Y.S = 8 * 2 ^ (2 * n₀) := h
        _ = 2 ^ (2 * n₀ + 3) := by
              rw [show (8 : ℕ) = 2 ^ 3 by norm_num, mul_comm, ← pow_add]
        _ ≤ 2 ^ (3 * n₀ + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h := card_S_of_isMaxRegLen_six_sub Y H hr h7
    exact le_of_eq h

private theorem card_Q_zero_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hS : Nat.card Y.S ≤ 2 ^ (3 * n₀ + 3)) :
    Nat.card (Y.Q 0) ≤ 2 ^ (2 * n₀ + 3) := by
  have hQS : Y.Q 0 ≤ Y.S := by
    rw [← Y.edgeSylow_zero]
    exact Y.Q_le_edgeSylow_left 0
  have hrel : (Y.Q 0).relIndex Y.S = 2 ^ n₀ := by
    rw [← Y.edgeSylow_zero, Y.relIndex_Q_edgeSylow 0, H.n_zero]
  have h := Subgroup.relIndex_mul_card (H := Y.Q 0) (K := Y.S)
  rw [inf_eq_left.mpr hQS] at h
  have hle : Nat.card (Y.Q 0) * 2 ^ n₀ ≤ 2 ^ (2 * n₀ + 3) * 2 ^ n₀ := by
    have hEq : Nat.card (Y.Q 0) * 2 ^ n₀ = Nat.card Y.S := by
      calc Nat.card (Y.Q 0) * 2 ^ n₀ = 2 ^ n₀ * Nat.card (Y.Q 0) := by ring
        _ = (Y.Q 0).relIndex Y.S * Nat.card (Y.Q 0) := by rw [hrel]
        _ = Nat.card Y.S := h
    rw [hEq]
    have h2 : 2 ^ (3 * n₀ + 3) = 2 ^ (2 * n₀ + 3) * 2 ^ n₀ := by
      rw [← pow_add]
      congr 1
      ring
    rwa [h2] at hS
  exact Nat.le_of_mul_le_mul_right hle (by positivity)

private theorem card_Qball2_le_eight (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hQ0 : Nat.card (Y.Q 0) ≤ 2 ^ (2 * n₀ + 3)) : Nat.card ↥Y.Qball2 ≤ 8 := by
  have hrel := pow_le_relIndex_Qball2 Y H
  have hN2Q0 : Y.Qball2 ≤ Y.Q 0 := inf_le_left
  have h := Subgroup.relIndex_mul_card (H := Y.Qball2) (K := Y.Q 0)
  rw [inf_eq_left.mpr hN2Q0] at h
  have hle : Nat.card ↥Y.Qball2 * 2 ^ (2 * n₀) ≤ 8 * 2 ^ (2 * n₀) := by
    calc Nat.card ↥Y.Qball2 * 2 ^ (2 * n₀)
        ≤ Nat.card ↥Y.Qball2 * Y.Qball2.relIndex (Y.Q 0) :=
          Nat.mul_le_mul_left _ hrel
      _ = Y.Qball2.relIndex (Y.Q 0) * Nat.card ↥Y.Qball2 := by ring
      _ = Nat.card (Y.Q 0) := h
      _ ≤ 2 ^ (2 * n₀ + 3) := hQ0
      _ = 8 * 2 ^ (2 * n₀) := by
          rw [show (8 : ℕ) = 2 ^ 3 by norm_num, mul_comm, ← pow_add]
          congr 1
          ring
  exact Nat.le_of_mul_le_mul_right hle (by positivity)

private theorem Zt_neg_one_le_Zt_zero (Y : Setup Γ G)
    (hW : Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2) : Y.Zt (-1) ≤ Y.Zt 0 := by
  have hZtm1 : Y.Zt (-1) = conjSub (Y.τ ^ (-1 : ℤ)) (Y.Zt 1) := by
    simpa using Y.Zt_add (-1) 1
  have hZt0 : Y.Zt 0 = conjSub (Y.τ ^ (-1 : ℤ)) (Y.Zt 2) := by
    simpa using Y.Zt_add (-1) 2
  rw [hZtm1, hZt0]
  exact conjSub_mono _ (hW.trans inf_le_right)

private theorem Zt_neg_one_le_Zt_neg_two (Y : Setup Γ G)
    (hW : Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2) : Y.Zt (-1) ≤ Y.Zt (-2) := by
  have hZtm1 : Y.Zt (-1) = conjSub (Y.τ ^ (-1 : ℤ)) (Y.Zt 1) := by
    simpa using Y.Zt_add (-1) 1
  have hZtm2 : Y.Zt (-2) = conjSub (Y.τ ^ (-1 : ℤ)) (Y.Zt 0) := by
    simpa using Y.Zt_add (-1) 0
  rw [hZtm1, hZtm2]
  exact conjSub_mono _ (hW.trans inf_le_left)

private theorem Zt_two_le_Gi_four (Y : Setup Γ G)
    (he : Y.ZtExt 0 2 2) : Y.Zt 2 ≤ Y.Gi 4 := by
  obtain ⟨he1, -, -⟩ := he
  have h1 : (-(2 : ℤ)) ≤ (2 : ℤ) := by norm_num
  have h2 : (2 : ℤ) ≤ (2 : ℤ) := le_rfl
  have hZeq : Y.Zt 2 = conjSub Y.τ (Y.Zt 0) := by
    simpa using Y.Zt_add 1 0
  rw [hZeq]
  calc conjSub Y.τ (Y.Zt 0) ≤ conjSub Y.τ (Y.Gi 2) := conjSub_mono _ (he1 2 h1 h2)
    _ = Y.Gi 4 := by
        have h := Y.Gi_add (m := 1) (i := 2)
        rw [show (2 : ℤ) + 2 * 1 = 4 by norm_num, zpow_one] at h
        exact h.symm

private theorem Zt_neg_two_le_Gi_neg_four (Y : Setup Γ G)
    (he : Y.ZtExt 0 2 2) : Y.Zt (-2) ≤ Y.Gi (-4) := by
  obtain ⟨he1, -, -⟩ := he
  have h1 : (-(2 : ℤ)) ≤ (-2 : ℤ) := by norm_num
  have h2 : (-2 : ℤ) ≤ (2 : ℤ) := by norm_num
  have hZtm2 : Y.Zt (-2) = conjSub (Y.τ ^ (-1 : ℤ)) (Y.Zt 0) := by
    simpa using Y.Zt_add (-1) 0
  rw [hZtm2]
  simp only [zpow_neg_one]
  calc conjSub (Y.τ⁻¹) (Y.Zt 0) ≤ conjSub (Y.τ⁻¹) (Y.Gi (-2)) :=
        conjSub_mono _ (he1 (-2) h1 h2)
    _ = Y.Gi (-4) := by
        have h := Y.Gi_add (m := -1) (i := -2)
        rw [show (-2 : ℤ) + 2 * (-1) = -4 by norm_num, zpow_neg_one] at h
        exact h.symm

private theorem Zt_one_inf_Zt_neg_one_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) (he : Y.ZtExt 0 2 2)
    (hW : Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2) : Y.Zt 1 ⊓ Y.Zt (-1) = ⊥ := by
  have hX2 : IsPGroup 2 ↥(Y.Zt 1 ⊓ Y.Zt (-1)) := (isPGroup_Zt Y 1).to_le inf_le_left
  have hle_arc : Y.Zt 1 ⊓ Y.Zt (-1) ≤ Y.arcStab (-4) 4 := by
    rw [Y.arcStab_eq_inf (by norm_num)]
    refine le_inf ?_ ?_
    · exact (inf_le_right.trans (Zt_neg_one_le_Zt_neg_two Y hW)).trans
        (Zt_neg_two_le_Gi_neg_four Y he)
    · exact (inf_le_left.trans (hW.trans inf_le_right)).trans (Zt_two_le_Gi_four Y he)
  have hGT : Y.arcStab (-4) 4 = Y.GT := by
    simpa using hr.2 (-4) 8 (by norm_num)
  have hXGT : Y.Zt 1 ⊓ Y.Zt (-1) ≤ Y.GT := hGT ▸ hle_arc
  exact eq_bot_of_le_GT Y H hX2 hXGT

private theorem conjSub_Zt_zero_eq_Zt_two (Y : Setup Γ G) {h : G}
    (hN : h ∈ Subgroup.normalizer (Y.K : Set G)) (h02 : h • Y.vert 0 = Y.vert 2) :
    conjSub h (Y.Zt 0) = Y.Zt 2 := by
  have hKn : conjSub h (Y.K : Subgroup G) = Y.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hN
  have hZ0n : conjSub h (Y.Z 0) = Y.Z 2 := (Y.Z_smul Y h02).symm
  rw [Setup.Zt, Setup.Zt, conjSub, Subgroup.map_commutator]
  rw [← conjSub, ← conjSub, hZ0n, hKn]

private theorem Zt_one_le_inf_Zt_zero_Zt_two_of_le_center (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (hc : Y.Zt 1 ≤ centerOf (Y.L 1)) :
    Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2 := by
  have hSleL : Y.S ≤ Y.L 1 := Y.S_le_L_one
  have hWcentS : Y.Zt 1 ≤ Subgroup.centralizer (Y.S : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hc hw)).2 s (hSleL hs)
  have hleZ0 : Y.Zt 1 ≤ Y.Zt 0 := by
    have h := Zt_one_inf_centralizer_S_le Y H hZ
    rwa [inf_eq_left.mpr hWcentS] at h
  obtain ⟨h, hh, hh02⟩ := Y.exists_normalizer_K_one H (a := Y.vert 0) (b := Y.vert 2)
    (by simpa using (Y.adj 0).symm) (Y.adj 1)
  obtain ⟨hhN, hhG1⟩ := Subgroup.mem_inf.mp hh
  have hZt1n : conjSub h (Y.Zt 1) = Y.Zt 1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Gi_one_le_normalizer_Zt_one Y H) hhG1)
  have hZtn : conjSub h (Y.Zt 0) = Y.Zt 2 := conjSub_Zt_zero_eq_Zt_two Y hhN hh02
  refine le_inf hleZ0 ?_
  calc Y.Zt 1 = conjSub h (Y.Zt 1) := hZt1n.symm
    _ ≤ conjSub h (Y.Zt 0) := conjSub_mono _ hleZ0
    _ = Y.Zt 2 := hZtn

private theorem four_le_card_Zt_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hne : Y.Zt 1 ≠ ⊥) : 4 ≤ Nat.card ↥(Y.Zt 1) := by
  haveI hZt1fin : Finite ↥(Y.Zt 1) :=
    finite_of_le_stabilizer Y.hyp
      ((Zt_le_Z Y 1).trans ((Y.Z_le_Q 1).trans (Y.Q_le_Gi 1)))
  by_contra hlt
  push Not at hlt
  have hW2 : IsPGroup 2 ↥(Y.Zt 1) := isPGroup_Zt Y 1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW2
  have hne1 : Nat.card ↥(Y.Zt 1) ≠ 1 := by
    intro h1
    exact hne (Subgroup.eq_bot_of_card_eq _ h1)
  have hk1 : k = 1 := by
    have hk0 : k ≠ 0 := by rintro rfl; exact hne1 (by rw [hk, pow_zero])
    have hk2 : k < 2 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by rw [← hk]; simpa using hlt)
    omega
  have hcard2 : Nat.card ↥(Y.Zt 1) = 2 := by rw [hk, hk1]; norm_num
  have hnormK : Y.K ≤ Subgroup.normalizer (Y.Zt 1 : Set G) := K_le_normalizer_Zt Y 1
  have hcentK : Y.K ≤ Subgroup.centralizer (Y.Zt 1 : Set G) := by
    rw [← normalizer_eq_centralizer_of_card_eq_two hcard2]
    exact hnormK
  have hWcent : Y.Zt 1 ≤ Subgroup.centralizer (Y.K : Set G) :=
    Subgroup.le_centralizer_iff.mpr hcentK
  have hbot := (Y.Zt_eq H 1).2.1
  have hle : Y.Zt 1 ≤ Y.Zt 1 ⊓ Subgroup.centralizer (Y.K : Set G) :=
    le_inf le_rfl hWcent
  rw [hbot] at hle
  exact hne (le_bot_iff.mp hle)

private theorem Zt_one_eq_bot_of_ZtExt_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) (he : Y.ZtExt 0 2 2) (hW : Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2) :
    Y.Zt 1 = ⊥ := by
  by_contra hne
  haveI hZt1fin : Finite ↥(Y.Zt 1) :=
    finite_of_le_stabilizer Y.hyp
      ((Zt_le_Z Y 1).trans ((Y.Z_le_Q 1).trans (Y.Q_le_Gi 1)))
  haveI hZtm1fin : Finite ↥(Y.Zt (-1)) :=
    finite_of_le_stabilizer Y.hyp
      ((Zt_le_Z Y (-1)).trans ((Y.Z_le_Q (-1)).trans (Y.Q_le_Gi (-1))))
  haveI hQball2fin : Finite ↥Y.Qball2 :=
    finite_of_le_stabilizer Y.hyp (inf_le_left.trans (Y.Q_le_Gi 0))
  have hWZ0 : Y.Zt 1 ≤ Y.Zt 0 := hW.trans inf_le_left
  have hWmZ0 : Y.Zt (-1) ≤ Y.Zt 0 := Zt_neg_one_le_Zt_zero Y hW
  have hWle : Y.Zt 1 ≤ Y.Qball2 := Zt_one_le_Qball2 Y H he hW
  have hWmle : Y.Zt (-1) ≤ Y.Qball2 := Zt_neg_one_le_Qball2 Y H he hW
  have hcardN : Nat.card ↥Y.Qball2 ≤ 8 :=
    card_Qball2_le_eight Y H (card_Q_zero_le Y H (card_S_le_eight_q0_cube Y H hr))
  have hdisj : Y.Zt 1 ⊓ Y.Zt (-1) = ⊥ := Zt_one_inf_Zt_neg_one_eq_bot Y H hr he hW
  have hcomm0 : ∀ a ∈ Y.Zt 0, ∀ b ∈ Y.Zt 0, a * b = b * a :=
    fun a ha b hb => Y.Z_commute 0 a (Zt_le_Z Y 0 ha) b (Zt_le_Z Y 0 hb)
  have hcomm : Y.Zt (-1) ≤ Subgroup.normalizer (Y.Zt 1 : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hcomm0 y (hWZ0 hy) x (hWmZ0 hx))
  have hcardsup : Nat.card ↥(Y.Zt 1 ⊔ Y.Zt (-1)) =
      Nat.card ↥(Y.Zt 1) * Nat.card ↥(Y.Zt (-1)) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Y.Zt 1) (Y.Zt (-1)) hcomm (disjoint_iff.mpr hdisj)
  have hcardm : Nat.card ↥(Y.Zt (-1)) = Nat.card ↥(Y.Zt 1) := by
    have hZeq : Y.Zt (-1) = conjSub (Y.τ ^ (-1 : ℤ)) (Y.Zt 1) := by
      simpa using Y.Zt_add (-1) 1
    rw [hZeq, conjSub]
    exact Subgroup.card_map_of_injective (MulAut.conj (Y.τ ^ (-1 : ℤ))).injective
  have hWcard : 4 ≤ Nat.card ↥(Y.Zt 1) := four_le_card_Zt_one Y H hne
  have hsuple : Y.Zt 1 ⊔ Y.Zt (-1) ≤ Y.Qball2 := sup_le hWle hWmle
  have hcard16 : 16 ≤ Nat.card ↥(Y.Zt 1 ⊔ Y.Zt (-1)) := by
    rw [hcardsup, hcardm]
    nlinarith
  have hcard8 : Nat.card ↥(Y.Zt 1 ⊔ Y.Zt (-1)) ≤ 8 :=
    (Subgroup.card_le_of_le hsuple).trans hcardN
  omega

@[instance_reducible] private def conjActionOfLeNormalizer (K X : Subgroup G)
    (h : K ≤ Subgroup.normalizer (X : Set G)) : MulDistribMulAction ↥K ↥X where
  smul k x :=
    ⟨(k : G) * (x : G) * (k : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (h k.2) x.1).mp x.2⟩
  one_smul x := by
    ext
    change (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
    simp
  mul_smul a b x := by
    ext
    change ((a : G) * (b : G)) * (x : G) * ((a : G) * (b : G))⁻¹ =
      (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹
    group
  smul_mul a x y := by
    ext
    change (a : G) * ((x : G) * (y : G)) * (a : G)⁻¹ =
      ((a : G) * (x : G) * (a : G)⁻¹) * ((a : G) * (y : G) * (a : G)⁻¹)
    group
  smul_one a := by
    ext
    change (a : G) * 1 * (a : G)⁻¹ = 1
    simp

private theorem commutator_eq_self_of_isPGroup_two_of_inf_centralizer {K X : Subgroup G}
    [Finite ↥K] [Finite ↥X] (hX : IsPGroup 2 X) (hXab : IsMulCommutative ↥X)
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) (hodd : Odd (Nat.card ↥K))
    (hC : X ⊓ Subgroup.centralizer (K : Set G) = ⊥) : ⁅X, K⁆ = X := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulDistribMulAction ↥K ↥X := conjActionOfLeNormalizer K X hKX
  obtain ⟨m, hm⟩ := hX.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥X) := by
    rw [hm]
    exact (Nat.coprime_two_right.mpr hodd).pow_right m
  haveI : Group.IsNilpotent ↥X := IsPGroup.isNilpotent hX
  have hsolv : Group.IsSolvable ↥X := inferInstance
  have hfix : fixedPointSubgroup ↥K ↥X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    ext
    have hx' : ∀ k : ↥K, ((k : G) * (x : G) * (k : G)⁻¹) = (x : G) :=
      fun k => congrArg Subtype.val (hx k)
    have hmem : (x : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := hx' ⟨k, hk⟩
      calc k * (x : G) = (k * (x : G) * k⁻¹) * k := by
            rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
        _ = (x : G) * k := by rw [h1]
    have hxbot : (x : G) ∈ X ⊓ Subgroup.centralizer (K : Set G) := ⟨x.2, hmem⟩
    rw [hC, Subgroup.mem_bot] at hxbot
    exact hxbot
  have hcompl :=
    CFSG.isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := ↥X) (A := ↥K) hsolv hcop hXab
  have htop : commutatorAction ↥K ↥X = ⊤ := by
    simpa [hfix] using hcompl.codisjoint
  have hle : (⊤ : Subgroup ↥X) ≤ (⁅X, K⁆).subgroupOf X := by
    rw [← htop, CFSG.commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := (⁅X, K⁆).subgroupOf X)).mpr ?_
    rintro x ⟨k, h, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    change (h : G)⁻¹ * ((k : G) * (h : G) * (k : G)⁻¹) ∈ ⁅X, K⁆
    rw [show (h : G)⁻¹ * ((k : G) * (h : G) * (k : G)⁻¹) = ⁅(h : G)⁻¹, (k : G)⁆ by
      rw [commutatorElement_def]; group]
    exact Subgroup.commutator_mem_commutator (X.inv_mem h.2) k.2
  have hXle : X ≤ ⁅X, K⁆ := by
    intro x hx
    have h := hle (Subgroup.mem_top (⟨x, hx⟩ : ↥X))
    exact Subgroup.mem_subgroupOf.mp h
  refine le_antisymm ?_ hXle
  rw [Subgroup.commutator_comm]
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp hKX

private theorem commutator_Zt_inf_Zt_zero_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r r₀ : ℕ} (hr : Y.IsMaxRegLen r) (he : Y.ZtExt 0 r₀ r₀) (h4 : 4 ≤ r₀)
    (hne : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≠ ⊥) (hrr : r ≤ 2 * r₀ + 2)
    (hZtrGi : ∀ j : ℤ, (0 : ℤ) ≤ j → j ≤ 2 * (r₀ : ℤ) → Y.Zt (r₀ : ℤ) ≤ Y.Gi j)
    (hRZ0 : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z 0)
    (hRZr : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z (r₀ : ℤ))
    (hKR : Y.K ≤ Subgroup.normalizer ((⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ : Subgroup G) : Set G)) :
    ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ⊓ Y.Zt 0 = ⊥ := by
  by_contra hne
  set X : Subgroup G := ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ⊓ Y.Zt 0 with hX
  have hXZ0 : X ≤ Y.Z 0 := inf_le_left.trans hRZ0
  have hXZr : X ≤ Y.Z (r₀ : ℤ) := inf_le_left.trans hRZr
  have hXZt : X ≤ Y.Zt 0 := inf_le_right
  have hX2 : IsPGroup 2 X :=
    (pCoreOf_isPGroup' (Y.Gi 0)).to_le (hXZt.trans ((Y.Zt_le_Z 0).trans (Y.Z_le_Q 0)))
  haveI : Finite ↥Y.K := finite_of_le_stabilizer Y.hyp (Y.K_le_Gi 0)
  haveI : Finite ↥X :=
    finite_of_le_stabilizer Y.hyp (hXZ0.trans ((Y.Z_le_Q 0).trans (Y.Q_le_Gi 0)))
  have hXab : IsMulCommutative ↥X := by
    rw [isMulCommutative_iff]
    intro a b
    exact Subtype.ext (Y.Z_commute 0 (a : G) (hXZ0 a.2) (b : G) (hXZ0 b.2))
  have hXK : Y.K ≤ Subgroup.normalizer (X : Set G) := by
    rw [hX]
    exact CFSG.Quasithin.F7.le_normalizer_inf hKR (Y.K_le_normalizer_Zt 0)
  have hXC : X ⊓ Subgroup.centralizer (Y.K : Set G) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro y hy
    obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyZt : y ∈ Y.Zt 0 := hXZt hyX
    have hmem : y ∈ Y.Zt 0 ⊓ Subgroup.centralizer (Y.K : Set G) := ⟨hyZt, hyC⟩
    rw [(Zt_eq Y H 0).2.1, Subgroup.mem_bot] at hmem
    exact hmem
  have hcommX := commutator_eq_self_of_isPGroup_two_of_inf_centralizer hX2 hXab hXK
    Y.odd_card_K hXC
  have hXZtr : X ≤ Y.Zt (r₀ : ℤ) := by
    rw [← hcommX]
    exact Subgroup.commutator_mono hXZr le_rfl
  have hfixL : X ≤ Y.Gi (-(r₀ : ℤ)) := by
    refine hXZt.trans ?_
    simpa using he.1 (-(r₀ : ℤ)) (by omega) (by omega)
  have hfixR : X ≤ Y.Gi (2 * (r₀ : ℤ)) :=
    hXZtr.trans (hZtrGi (2 * (r₀ : ℤ)) (by positivity) le_rfl)
  have hXarc : X ≤ Y.arcStab (-(r₀ : ℤ)) (2 * (r₀ : ℤ)) := by
    rw [Y.arcStab_eq_inf (by omega)]
    exact le_inf hfixL hfixR
  have hk : r < 3 * r₀ := by omega
  have hEqGT : Y.arcStab (-(r₀ : ℤ)) (2 * (r₀ : ℤ)) = Y.GT := by
    have h := hr.2 (-(r₀ : ℤ)) (3 * r₀) hk
    rwa [show -(r₀ : ℤ) + ((3 * r₀ : ℕ) : ℤ) = 2 * (r₀ : ℤ) by push_cast; ring] at h
  have hXKsub : X ≤ Y.K := by
    rw [← Y.GT_eq_K_of_sec5Hyp H, ← hEqGT]
    exact hXarc
  have hbot : Y.K ⊓ X = ⊥ := inf_eq_bot_of_odd_of_isPGroup Y.odd_card_K hX2
  have hXbot : X = ⊥ := by
    have h : X ≤ Y.K ⊓ X := le_inf hXKsub le_rfl
    rw [hbot] at h
    exact le_bot_iff.mp h
  exact hne hXbot

private theorem commutator_Zt_le_centralizer_K (Y : Setup Γ G) {r₀ : ℕ}
    (hRZ0 : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z 0)
    (hKR : Y.K ≤ Subgroup.normalizer ((⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ : Subgroup G) : Set G))
    (hRinfZt : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ⊓ Y.Zt 0 = ⊥) :
    ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Subgroup.centralizer (Y.K : Set G) := by
  have hRK : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ = ⊥ := by
    have hleR : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hKR
    have hleZt : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤ Y.Zt 0 := Subgroup.commutator_mono hRZ0 le_rfl
    have h : ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ ≤
        ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ⊓ Y.Zt 0 := le_inf hleR hleZt
    rw [hRinfZt] at h
    exact le_bot_iff.mp h
  have hRcent : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Subgroup.centralizer (Y.K : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hcomm : ⁅r, k⁆ ∈ ⁅⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆, Y.K⁆ := Subgroup.commutator_mem_commutator hr hk
    rw [hRK, Subgroup.mem_bot, commutatorElement_def] at hcomm
    have hrk : r * k = k * r := by
      calc r * k = (r * k * r⁻¹ * k⁻¹) * (k * r) := by group
        _ = k * r := by rw [hcomm]; group
    exact hrk.symm
  exact hRcent

private theorem Z_zero_inf_centralizer_le_Gi_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZQ : Y.Z 0 ≤ Y.Q 1) : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Gi 3 := by
  set U : Subgroup G := Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) with hU
  have hUQ0 : U ≤ Y.Q 0 := inf_le_left.trans (Y.Z_le_Q 0)
  have hU2 : IsPGroup 2 U := (pCoreOf_isPGroup' (Y.Gi 0)).to_le hUQ0
  have hUC : U ≤ Subgroup.centralizer (Y.K : Set G) := inf_le_right
  have hUcomm : ⁅U, Y.K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUC
  have hUQ1 : U ≤ Y.Q 1 := inf_le_left.trans hZQ
  have hU2Gi : U ≤ Y.Gi 2 := hUQ1.trans ((Y.Q_le_Gi_adj 1).trans inf_le_right)
  have hUQ2 : U ≤ Y.Q 2 :=
    Y.le_Q_of_comm_K_eq_bot H (by norm_num : Even (2 : ℤ)) hU2Gi hU2 hUcomm
  exact hUQ2.trans ((Y.Q_le_Gi_adj 2).trans inf_le_right)

private theorem Z_zero_inf_centralizer_le_Gi_neg_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZQ : Y.Z 0 ≤ Y.Q 1) : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Gi (-3) := by
  set U : Subgroup G := Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) with hU
  have hUQ0 : U ≤ Y.Q 0 := inf_le_left.trans (Y.Z_le_Q 0)
  have hU2 : IsPGroup 2 U := (pCoreOf_isPGroup' (Y.Gi 0)).to_le hUQ0
  have hUC : U ≤ Subgroup.centralizer (Y.K : Set G) := inf_le_right
  have hUcomm : ⁅U, Y.K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUC
  have hUQ1 : U ≤ Y.Q 1 := inf_le_left.trans hZQ
  obtain ⟨h, hh, hh1⟩ := Y.exists_normalizer_K_move 0 (Y.K_le_Gi 0) le_rfl
    (fun a b ha hb => Y.hyp.locTrans ha hb) (Y.adj 0) (by
      have := Y.adj (-1); simpa using this.symm)
    (fun k hk => Y.K_fix k hk 1) (fun k hk => Y.K_fix k hk (-1))
  obtain ⟨hhG, hhN⟩ := Subgroup.mem_inf.mp hh
  have hKinv : conjSub h (Y.K : Subgroup G) = Y.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hhN
  have hUinv : conjSub h U = U := by
    rw [hU, conjSub_inf, Y.Z_normal 0 h hhG, ← conjSub_centralizer, hKinv]
  have hUinv' : conjSub h⁻¹ U = U := by
    have hh := congrArg (conjSub h⁻¹) hUinv
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at hh
    exact hh.symm
  have hsm : h⁻¹ • Y.vert 1 = Y.vert (-1) := by
    have h' : h • Y.vert (-1) = Y.vert 1 := by simpa using hh1
    calc h⁻¹ • Y.vert 1 = h⁻¹ • (h • Y.vert (-1)) := by rw [h']
      _ = Y.vert (-1) := by rw [smul_smul, inv_mul_cancel, one_smul]
  have hQconj : Y.Q (-1) = conjSub h⁻¹ (Y.Q 1) := Q_smul Y Y hsm
  have hUQm1 : U ≤ Y.Q (-1) := by
    rw [hQconj, ← hUinv']
    exact conjSub_mono h⁻¹ hUQ1
  have hU2' : U ≤ Y.Gi (-2) := hUQm1.trans ((Y.Q_le_Gi_adj (-1)).trans inf_le_left)
  have hUQm2 : U ≤ Y.Q (-2) :=
    Y.le_Q_of_comm_K_eq_bot H (by norm_num : Even (-2 : ℤ)) hU2' hU2 hUcomm
  exact hUQm2.trans ((Y.Q_le_Gi_adj (-2)).trans inf_le_left)

private theorem commutator_Zt_le_Gi_of_between (Y : Setup Γ G) {r₀ : ℕ}
    (hrdiv : (r₀ : ℤ) = 2 * ((r₀ / 2 : ℕ) : ℤ))
    (hRZ0 : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z 0)
    (hRZr : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Z (r₀ : ℤ))
    (hRcent : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Subgroup.centralizer (Y.K : Set G))
    (hU3 : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Gi 3)
    (hUm3 : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Gi (-3)) :
    ∀ j : ℤ, -3 ≤ j → j ≤ (r₀ : ℤ) + 3 → ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Gi j := by
  intro j hj1 hj2 x hx
  have hxZ : x ∈ Y.Z (r₀ : ℤ) := hRZr hx
  have hxC : x ∈ Subgroup.centralizer (Y.K : Set G) := hRcent hx
  set m : ℤ := ((r₀ / 2 : ℕ) : ℤ) with hm
  have hmr : 2 * m = (r₀ : ℤ) := by
    rw [hm]; exact hrdiv.symm
  have hyZ0 : (Y.τ ^ m)⁻¹ * x * (Y.τ ^ m) ∈ Y.Z 0 := by
    have hZ := Y.Z_add m 0
    rw [show (0 : ℤ) + 2 * m = (r₀ : ℤ) by omega] at hZ
    rw [hZ] at hxZ
    exact mem_conjSub.mp hxZ
  have hyC : (Y.τ ^ m)⁻¹ * x * (Y.τ ^ m) ∈ Subgroup.centralizer (Y.K : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro k hk
    have hk' : (Y.τ ^ m) * k * (Y.τ ^ m)⁻¹ ∈ Y.K := by
      have hτN : Y.τ ^ m ∈ Subgroup.normalizer (Y.K : Set G) :=
        Subgroup.zpow_mem (K := Subgroup.normalizer (Y.K : Set G)) Y.τ_norm m
      exact (Subgroup.mem_normalizer_iff.mp hτN k).mp hk
    have hcomm := hxC ((Y.τ ^ m) * k * (Y.τ ^ m)⁻¹) hk'
    calc k * ((Y.τ ^ m)⁻¹ * x * (Y.τ ^ m))
        = (Y.τ ^ m)⁻¹ * (((Y.τ ^ m) * k * (Y.τ ^ m)⁻¹) * x) * (Y.τ ^ m) := by group
      _ = (Y.τ ^ m)⁻¹ * (x * ((Y.τ ^ m) * k * (Y.τ ^ m)⁻¹)) * (Y.τ ^ m) := by rw [hcomm]
      _ = ((Y.τ ^ m)⁻¹ * x * (Y.τ ^ m)) * k := by group
  have hyU : (Y.τ ^ m)⁻¹ * x * (Y.τ ^ m) ∈
      Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) := Subgroup.mem_inf.mpr ⟨hyZ0, hyC⟩
  have hx2 : x ∈ Y.Gi (3 + 2 * m) := by
    have hmem := mul_mem_conjSub (g := Y.τ ^ m) (hU3 hyU)
    rw [← Y.Gi_add m 3] at hmem
    rwa [show Y.τ ^ m * ((Y.τ ^ m)⁻¹ * x * (Y.τ ^ m)) * (Y.τ ^ m)⁻¹ = x by group] at hmem
  have hx2' : x ∈ Y.Gi ((r₀ : ℤ) + 3) := by
    rwa [show 3 + 2 * m = (r₀ : ℤ) + 3 by omega] at hx2
  have hxU : x ∈ Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) := le_inf hRZ0 hRcent hx
  have hxL : x ∈ Y.Gi (-3) := hUm3 hxU
  exact Y.mem_Gi_of_between hxL hx2' hj1 hj2

private theorem commutator_Zt_le_K (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (h4 : 4 ≤ r₀)
    (hRcent : ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Subgroup.centralizer (Y.K : Set G))
    (hRfix : ∀ j : ℤ, -3 ≤ j → j ≤ (r₀ : ℤ) + 3 → ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.Gi j) :
    ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ ≤ Y.K := by
  intro x hx
  refine Y.mem_K_of_fixes_odd_vert H ?_ (by norm_num : Odd (-3)) ?_
  · exact Subgroup.centralizer_le_normalizer (Y.K : Set G) (hRcent hx)
  · intro j hj
    have h1 : -3 ≤ -3 + 2 * (j : ℤ) := by
      have : (0 : ℤ) ≤ (j : ℤ) := by positivity
      linarith
    have h2 : -3 + 2 * (j : ℤ) ≤ (r₀ : ℤ) + 3 := by
      have hj5 : (j : ℤ) ≤ 5 := by exact_mod_cast hj
      have h4' : (4 : ℤ) ≤ (r₀ : ℤ) := by exact_mod_cast h4
      linarith
    exact MulAction.mem_stabilizer_iff.mp (hRfix (-3 + 2 * (j : ℤ)) h1 h2 hx)

private theorem not_Z_zero_le_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 ≠ ⊥)
    {r r₀ : ℕ} (hr : Y.IsMaxRegLen r) (he : Y.ZtExt 0 r₀ r₀) (h4 : 4 ≤ r₀)
    (hrr : r ≤ 2 * r₀ + 2) : ¬ Y.Z 0 ≤ Y.Q 1 := by
  intro hZQ
  have hEven : Even r₀ := (s52_step1 Y H hZ he).2
  have hrdiv : (r₀ : ℤ) = 2 * ((r₀ / 2 : ℕ) : ℤ) := by
    have h2 : r₀ = 2 * (r₀ / 2) := by
      rw [eq_comm]
      exact Nat.mul_div_cancel' (even_iff_two_dvd.mp hEven)
    exact_mod_cast h2
  have hZtrGi : ∀ j : ℤ, (0 : ℤ) ≤ j → j ≤ 2 * (r₀ : ℤ) → Y.Zt (r₀ : ℤ) ≤ Y.Gi j := by
    intro j hj0 hj2
    have hm : (r₀ : ℤ) = 0 + 2 * ((r₀ / 2 : ℕ) : ℤ) := by simpa using hrdiv
    have hidx : j - 2 * ((r₀ / 2 : ℕ) : ℤ) = j - (r₀ : ℤ) := by rw [hrdiv]
    have hle : Y.Zt 0 ≤ Y.Gi (j - 2 * ((r₀ / 2 : ℕ) : ℤ)) := by
      rw [hidx]
      simpa using he.1 (j - (r₀ : ℤ)) (by linarith) (by linarith)
    have hmap := Y.Zt_add_two (0 : ℤ) ((r₀ / 2 : ℕ) : ℤ)
    have hGi := Y.Gi_add ((r₀ / 2 : ℕ) : ℤ) (j - 2 * ((r₀ / 2 : ℕ) : ℤ))
    rw [show j - 2 * ((r₀ / 2 : ℕ) : ℤ) + 2 * ((r₀ / 2 : ℕ) : ℤ) = j by ring] at hGi
    rw [hm, hmap, hGi]
    exact Subgroup.map_mono hle
  have hGiN : ∀ i : ℤ, Y.Gi i ≤ Subgroup.normalizer (Y.Z i : Set G) :=
    fun i => Y.Gi_le_normalizer_Z i
  set R : Subgroup G := ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ with hR
  have hRne : R ≠ ⊥ := comm_Zt_ne_bot_of_ZtExt Y H hZ he
  have hRZ0 : R ≤ Y.Z 0 := by
    rw [hR]
    refine Subgroup.commutator_le.mpr ?_
    intro a ha b hb
    have hbGi : b ∈ Y.Gi 0 := (hZtrGi 0 le_rfl (by positivity)) hb
    have hconj : b * a⁻¹ * b⁻¹ ∈ Y.Z 0 :=
      (Subgroup.mem_normalizer_iff.mp (hGiN 0 hbGi) a⁻¹).mp ((Y.Z 0).inv_mem (Y.Zt_le_Z 0 ha))
    rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact (Y.Z 0).mul_mem (Y.Zt_le_Z 0 ha) hconj
  have hRZr : R ≤ Y.Z (r₀ : ℤ) := by
    rw [hR]
    refine Subgroup.commutator_le.mpr ?_
    intro a ha b hb
    have haGi : a ∈ Y.Gi (r₀ : ℤ) := by
      simpa using (he.1 (r₀ : ℤ) (by omega) (by omega)) ha
    have hconj : a * b * a⁻¹ ∈ Y.Z (r₀ : ℤ) :=
      (Subgroup.mem_normalizer_iff.mp (hGiN (r₀ : ℤ) haGi) b).mp (Y.Zt_le_Z (r₀ : ℤ) hb)
    rw [commutatorElement_def]
    exact (Y.Z (r₀ : ℤ)).mul_mem hconj ((Y.Z (r₀ : ℤ)).inv_mem (Y.Zt_le_Z (r₀ : ℤ) hb))
  have hKR : Y.K ≤ Subgroup.normalizer (R : Set G) := by
    rw [hR]
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆ = ⁅Y.Zt 0, Y.Zt (r₀ : ℤ)⁆
    have h1 : conjSub k (Y.Zt 0) = Y.Zt 0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Y.K_le_normalizer_Zt 0) hk)
    have h2 : conjSub k (Y.Zt (r₀ : ℤ)) = Y.Zt (r₀ : ℤ) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Y.K_le_normalizer_Zt (r₀ : ℤ)) hk)
    rw [← conjSub_commutator, h1, h2]
  have hRinfZt : R ⊓ Y.Zt 0 = ⊥ :=
    commutator_Zt_inf_Zt_zero_eq_bot Y H hr he h4 hRne hrr hZtrGi hRZ0 hRZr hKR
  have hRcent : R ≤ Subgroup.centralizer (Y.K : Set G) :=
    commutator_Zt_le_centralizer_K Y hRZ0 hKR hRinfZt
  have hU3 : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Gi 3 :=
    Z_zero_inf_centralizer_le_Gi_three Y H hZQ
  have hUm3 : Y.Z 0 ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Gi (-3) :=
    Z_zero_inf_centralizer_le_Gi_neg_three Y H hZQ
  have hRfix : ∀ j : ℤ, -3 ≤ j → j ≤ (r₀ : ℤ) + 3 → R ≤ Y.Gi j :=
    commutator_Zt_le_Gi_of_between Y hrdiv hRZ0 hRZr hRcent hU3 hUm3
  have hRKsub : R ≤ Y.K := commutator_Zt_le_K Y H h4 hRcent hRfix
  exact hRne (by
    have h : R ≤ Y.K ⊓ R := le_inf hRKsub le_rfl
    have h2 : Y.K ⊓ R = ⊥ :=
      inf_eq_bot_of_odd_of_isPGroup Y.odd_card_K
        ((pCoreOf_isPGroup' (Y.Gi 0)).to_le (hRZ0.trans (Y.Z_le_Q 0)))
    rw [h2] at h
    exact le_bot_iff.mp h)

private theorem Z_zero_le_Gi_one (Y : Setup Γ G) : Y.Z 0 ≤ Y.Gi 1 := by
  simpa using (Y.Z_le_Q 0).trans ((Y.Q_le_Gi_adj 0).trans inf_le_right)

private theorem eq_third_of_adj_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {a b c d : V} (ha : Γ.Adj (Y.vert 1) a) (hb : Γ.Adj (Y.vert 1) b) (hab : a ≠ b)
    (hc : Γ.Adj (Y.vert 1) c) (hca : c ≠ a) (hcb : c ≠ b)
    (hd : Γ.Adj (Y.vert 1) d) (hda : d ≠ a) (hdb : d ≠ b) : c = d := by
  by_contra hcd
  have hcard : Nat.card (Γ.neighborSet (Y.vert 1)) = 3 := by
    have h := (Y.hyp.valency (Y.vert 1)).2
    rw [show nOf Γ (Y.vert 1) = 1 from H.n_one] at h
    norm_num at h
    exact h
  have hsub : ({a, b, c, d} : Set V) ⊆ Γ.neighborSet (Y.vert 1) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have h4 : ({a, b, c, d} : Set V).ncard = 4 := by
    have h1 : a ∉ ({b, c, d} : Set V) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, hca.symm, hda.symm⟩
    have h2 : b ∉ ({c, d} : Set V) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hcb.symm, hdb.symm⟩
    have h3 : c ∉ ({d} : Set V) := by
      simp only [Set.mem_singleton_iff]
      exact hcd
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_insert_of_notMem h3, Set.ncard_singleton]
  haveI : Finite (Γ.neighborSet (Y.vert 1)) := Y.hyp.finite_neighborSet (Y.vert 1)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h4, ← Nat.card_coe_set_eq, hcard] at hle
  omega

private theorem Z_zero_le_L_one (Y : Setup Γ G) : Y.Z 0 ≤ Y.L 1 :=
  le_oTwoPrime_of_isPGroup ((pCoreOf_isPGroup' (Y.Gi 0)).to_le (Y.Z_le_Q 0))
    (Z_zero_le_Gi_one Y)

private theorem Z_two_le_Gi_one (Y : Setup Γ G) : Y.Z 2 ≤ Y.Gi 1 := by
  simpa using (Y.Z_le_Q 2).trans ((Y.Q_le_Gi_adj 2).trans inf_le_left)

private theorem Z_two_le_L_one (Y : Setup Γ G) : Y.Z 2 ≤ Y.L 1 :=
  le_oTwoPrime_of_isPGroup ((pCoreOf_isPGroup' (Y.Gi 2)).to_le (Y.Z_le_Q 2))
    (Z_two_le_Gi_one Y)

private theorem card_map_eq_two_of_isPGroup {L : Type*} [Group L] [Finite L] {n : ℕ}
    (φ : L →* PSL(2, GaloisField 2 n)) (hcard6 : Nat.card (PSL(2, GaloisField 2 n)) = 6)
    {K : Subgroup L} (hP : IsPGroup 2 ↥K) (hne : K.map φ ≠ ⊥) :
    Nat.card ↥(K.map φ) = 2 := by
  have h2 : IsPGroup 2 ↥(K.map φ) := hP.map φ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  have hdvd : Nat.card ↥(K.map φ) ∣ 6 := by
    rw [← hcard6]
    exact Subgroup.card_subgroup_dvd_card _
  have hle : 2 ^ n ≤ 6 := by
    have h := Nat.le_of_dvd (by norm_num) (hn ▸ hdvd)
    simpa using h
  have hnlt : n < 3 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (hle.trans_lt (by norm_num))
  interval_cases n
  · exfalso
    apply hne
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hn]; norm_num)
  · rw [hn]; norm_num
  · exfalso
    rw [hn] at hdvd
    norm_num at hdvd

theorem relIndex_Z_zero_inf_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hb : ¬ Y.Z 0 ≤ Y.Q 1) : (Y.Z 0 ⊓ Y.Q 1).relIndex (Y.Z 0) = 2 := by
  let hN := Y.hyp.isLocL2_oTwoPrime (Y.vert 1)
  haveI : Finite ↥(Y.L 1) := finite_of_le_stabilizer Y.hyp (Y.L_le_Gi 1)
  have hZ0L : Y.Z 0 ≤ Y.L 1 := Z_zero_le_L_one Y
  have hker : hN.phi.ker = (Y.Q 1).subgroupOf (Y.L 1) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hN.phi_ker x
  have hP : IsPGroup 2 ↥((Y.Z 0).subgroupOf (Y.L 1)) :=
    ((pCoreOf_isPGroup' (Y.Gi 0)).to_le (Y.Z_le_Q 0)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hZ0L).symm
  have hne : ((Y.Z 0).subgroupOf (Y.L 1)).map hN.phi ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff] at hbot
    apply hb
    intro z hz
    have hz' : (⟨z, hZ0L hz⟩ : ↥(Y.L 1)) ∈ (Y.Z 0).subgroupOf (Y.L 1) := by
      rw [Subgroup.mem_subgroupOf]
      exact hz
    have hmem := hbot hz'
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hcard6 : Nat.card (PSL(2, GaloisField 2 (Y.n 1))) = 6 := by
    rw [H.n_one]
    simpa using CFSG.Walter.psl2_even_card (f := 1) (by norm_num)
  have hcard := card_map_eq_two_of_isPGroup (L := ↥(Y.L 1)) (φ := hN.phi) hcard6
    (K := (Y.Z 0).subgroupOf (Y.L 1)) hP hne
  have h1 : (Y.Q 1).relIndex (Y.Z 0) = 2 := by
    rw [← Subgroup.relIndex_subgroupOf (H := Y.Q 1) (K := Y.Z 0) (L := Y.L 1) hZ0L]
    rw [← hker, Subgroup.relIndex_ker]
    exact hcard
  rw [Subgroup.inf_relIndex_left]
  exact h1

private theorem not_Z_two_le_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hb : ¬ Y.Z 0 ≤ Y.Q 1) : ¬ Y.Z 2 ≤ Y.Q 1 := by
  intro h2Q
  obtain ⟨g, hg, hg02⟩ := Y.exists_normalizer_K_one H (a := Y.vert 0) (b := Y.vert 2)
    (by simpa using (Y.adj 0).symm) (Y.adj 1)
  obtain ⟨-, hgG1⟩ := Subgroup.mem_inf.mp hg
  have hZeq : Y.Z 2 = conjSub g (Y.Z 0) := Setup.Z_smul Y Y hg02
  have hQeq : conjSub g (Y.Q 1) = Y.Q 1 := by
    rw [show Y.Q 1 = pCoreOf 2 (Y.Gi 1) from rfl, ← pCoreOf_conjSub,
      conjSub_eq_of_mem hgG1]
  have hQeq' : conjSub g⁻¹ (Y.Q 1) = Y.Q 1 := by
    have h := congrArg (conjSub g⁻¹) hQeq
    rw [conjSub_conjSub_inv] at h
    exact h.symm
  apply hb
  intro x hx
  have hmem : g * x * g⁻¹ ∈ Y.Z 2 := by
    rw [hZeq]
    exact mul_mem_conjSub hx
  have hQ : g * x * g⁻¹ ∈ Y.Q 1 := h2Q hmem
  have hx' : g⁻¹ * (g * x * g⁻¹) * g ∈ Y.Q 1 := by
    have h := mul_mem_conjSub (g := g⁻¹) hQ
    rw [hQeq'] at h
    simpa using h
  have hxe : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rwa [hxe] at hx'

private theorem relIndex_Z_two_inf_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hb : ¬ Y.Z 0 ≤ Y.Q 1) : (Y.Z 2 ⊓ Y.Q 1).relIndex (Y.Z 2) = 2 := by
  obtain ⟨g, hg, hg02⟩ := Y.exists_normalizer_K_one H (a := Y.vert 0) (b := Y.vert 2)
    (by simpa using (Y.adj 0).symm) (Y.adj 1)
  obtain ⟨-, hgG1⟩ := Subgroup.mem_inf.mp hg
  have hZeq : Y.Z 2 = conjSub g (Y.Z 0) := Setup.Z_smul Y Y hg02
  have hQeq : conjSub g (Y.Q 1) = Y.Q 1 := by
    rw [show Y.Q 1 = pCoreOf 2 (Y.Gi 1) from rfl, ← pCoreOf_conjSub,
      conjSub_eq_of_mem hgG1]
  have h := relIndex_Z_zero_inf_Q_one Y H hb
  rw [hZeq, ← hQeq, ← conjSub_inf]
  simp only [conjSub]
  rw [Subgroup.relIndex_map_map_of_injective (H := Y.Z 0 ⊓ Y.Q 1) (K := Y.Z 0)
    (MulAut.conj g).injective]
  exact h

theorem L_one_le_sup_of_not_Z_zero_le_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hb : ¬ Y.Z 0 ≤ Y.Q 1) : Y.L 1 ≤ Y.Z 0 ⊔ Y.Z 2 ⊔ Y.Q 1 := by
  have h := L_eq_sup_of_fixes Y 1 (A := Y.Z 0) (B := Y.Z 2) (a := Y.vert 0) (b := Y.vert 2)
    (by simpa using (Y.adj 0).symm) (Y.adj 1)
    (by intro h; have := Y.vert_injective h; omega)
    (Z_zero_le_L_one Y) (Z_two_le_L_one Y)
    (fun x hx => MulAction.mem_stabilizer_iff.mp (Y.Z_le_Gi 0 hx))
    (fun x hx => MulAction.mem_stabilizer_iff.mp (Y.Z_le_Gi 2 hx))
    (by rw [H.n_one]; simpa using relIndex_Z_zero_inf_Q_one Y H hb)
    (by rw [H.n_one]; simpa using relIndex_Z_two_inf_Q_one Y H hb)
  exact h.le

theorem Z_zero_inf_Z_two_le_centerOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.Z 0 ⊓ Y.Z 2 ≤ centerOf (Y.L 1) := by
  set U : Subgroup G := Y.Z 0 ⊓ Y.Z 2 with hU
  have hUleL : U ≤ Y.L 1 := inf_le_left.trans (Z_zero_le_L_one Y)
  have hQ0c : U ≤ Subgroup.centralizer (Y.Q 0 : Set G) := by
    intro u hu
    exact (Subgroup.mem_inf.mp (Y.Z_le_center 0 hu.1)).2
  have hQ2c : U ≤ Subgroup.centralizer (Y.Q 2 : Set G) := by
    intro u hu
    exact (Subgroup.mem_inf.mp (Y.Z_le_center 2 hu.2)).2
  have hA : U ≤ Subgroup.centralizer ((Y.Q 0 ⊓ Y.Q 1) : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp
      ((Subgroup.mem_inf.mp (Y.Z_le_center 0 hu.1)).2) a ha.1
  have hB : U ≤ Subgroup.centralizer ((Y.Q 2 ⊓ Y.Q 1) : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_iff.mp
      ((Subgroup.mem_inf.mp (Y.Z_le_center 2 hu.2)).2) b hb.1
  have hQ1c : U ≤ Subgroup.centralizer (Y.Q 1 : Set G) := by
    rw [Y.Q_eq_sup_inf H 1]
    exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hA hB
  have hSc : U ≤ Subgroup.centralizer (Y.S : Set G) := by
    have hSeq : Y.S = Y.Q 0 ⊔ Y.Q 1 := (Y.sup_Q_eq_edgeSylow H.char 0).symm
    rw [hSeq]
    exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hQ0c hQ1c
  have hS2c : U ≤ Subgroup.centralizer (Y.edgeSylow 1 : Set G) := by
    have hS2eq : Y.edgeSylow 1 = Y.Q 1 ⊔ Y.Q 2 := (Y.sup_Q_eq_edgeSylow H.char 1).symm
    rw [hS2eq]
    exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hQ1c hQ2c
  have hLc : Y.L 1 ≤ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    have hLsup : Y.S ⊔ Y.edgeSylow 1 = Y.L 1 := by
      rw [← Y.edgeSylow_zero]
      exact Y.edgeSylow_sup_edgeSylow 1
    rw [← hLsup]
    exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hSc hS2c
  rw [centerOf]
  exact le_inf hUleL (Subgroup.le_centralizer_iff.mpr hLc)

private theorem mul_smul_vert_zero_eq_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {z0 z2 : G}
    (h01 : z0 • Y.vert 0 = Y.vert 0) (h11 : z0 • Y.vert 1 = Y.vert 1)
    (h12 : z2 • Y.vert 1 = Y.vert 1) (h22 : z2 • Y.vert 2 = Y.vert 2)
    (h0 : z0 • Y.vert 2 ≠ Y.vert 2) (h2 : z2 • Y.vert 0 ≠ Y.vert 0) :
    (z0 * z2) • Y.vert 0 = Y.vert 2 := by
  have h02 : Y.vert 0 ≠ Y.vert 2 := by
    intro h
    have := Y.vert_injective h
    omega
  set c : V := z2 • Y.vert 0 with hcdef
  have hcadj : Γ.Adj (Y.vert 1) c := by
    have h := (Y.hyp.adj_smul z2 (Y.vert 0) (Y.vert 1)).mpr (Y.adj 0)
    rw [h12] at h
    exact h.symm
  have hcne0 : c ≠ Y.vert 0 := h2
  have hcne2 : c ≠ Y.vert 2 := by
    intro h
    have h2 : z2 • Y.vert 0 = z2 • Y.vert 2 := by rw [← hcdef, h, h22]
    exact h02 (MulAction.injective z2 h2)
  have hz0_2_adj : Γ.Adj (Y.vert 1) (z0 • Y.vert 2) := by
    have h := (Y.hyp.adj_smul z0 (Y.vert 2) (Y.vert 1)).mpr (Y.adj 1).symm
    rw [h11] at h
    exact h.symm
  have hz0_2_ne0 : z0 • Y.vert 2 ≠ Y.vert 0 := by
    intro h
    have h2 : z0 • Y.vert 2 = z0 • Y.vert 0 := by rw [h, h01]
    have h3 := MulAction.injective z0 h2
    have := Y.vert_injective h3
    omega
  have hz0_2_eq_c : z0 • Y.vert 2 = c :=
    eq_third_of_adj_three Y H (a := Y.vert 0) (b := Y.vert 2)
      (c := z0 • Y.vert 2) (d := c)
      (by simpa using (Y.adj 0).symm) (Y.adj 1) h02
      hz0_2_adj hz0_2_ne0 h0
      hcadj hcne0 hcne2
  have hcadj0 : Γ.Adj (Y.vert 1) (z0 • c) := by
    have h := (Y.hyp.adj_smul z0 c (Y.vert 1)).mpr hcadj.symm
    rw [h11] at h
    exact h.symm
  have hz0c_ne0 : z0 • c ≠ Y.vert 0 := by
    intro h
    have h2 : z0 • c = z0 • Y.vert 0 := by rw [h, h01]
    exact hcne0 (MulAction.injective z0 h2)
  have hz0c_nec : z0 • c ≠ c := by
    intro h
    have h2 : z0 • c = z0 • Y.vert 2 := by rw [h, hz0_2_eq_c]
    have := MulAction.injective z0 h2
    exact hcne2 this
  have hz0c : z0 • c = Y.vert 2 :=
    (eq_third_of_adj_three Y H (a := Y.vert 0) (b := c)
      (c := Y.vert 2) (d := z0 • c)
      (by simpa using (Y.adj 0).symm) hcadj (Ne.symm hcne0)
      (Y.adj 1) (Ne.symm h02) hcne2.symm
      hcadj0 hz0c_ne0 hz0c_nec).symm
  rw [mul_smul, show z2 • Y.vert 0 = c from rfl, hz0c]

theorem Z_zero_inf_Q_two_le_Z_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hb : ¬ Y.Z 0 ≤ Y.Q 1) : Y.Z 0 ⊓ Y.Q 2 ≤ Y.Z 2 := by
  obtain ⟨z0, hz0Z, hz0Q⟩ := Set.not_subset.mp hb
  obtain ⟨z2, hz2Z, hz2Q⟩ := Set.not_subset.mp (not_Z_two_le_Q_one Y H hb)
  have hz0G0 : z0 ∈ Y.Gi 0 := Y.Z_le_Gi 0 hz0Z
  have hz0G1 : z0 ∈ Y.Gi 1 := Z_zero_le_Gi_one Y hz0Z
  have hz0pow := exists_pow_two_of_mem (pCoreOf_isPGroup' (Y.Gi 0)) (Y.Z_le_Q 0 hz0Z)
  have hz2G1 : z2 ∈ Y.Gi 1 := Z_two_le_Gi_one Y hz2Z
  have hz2G2 : z2 ∈ Y.Gi 2 := Y.Z_le_Gi 2 hz2Z
  have hz2pow := exists_pow_two_of_mem (pCoreOf_isPGroup' (Y.Gi 2)) (Y.Z_le_Q 2 hz2Z)
  have hfix01 : z0 • Y.vert 0 = Y.vert 0 := MulAction.mem_stabilizer_iff.mp hz0G0
  have hfix11 : z0 • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp hz0G1
  have hfix12 : z2 • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp hz2G1
  have hfix22 : z2 • Y.vert 2 = Y.vert 2 := MulAction.mem_stabilizer_iff.mp hz2G2
  have h02 : Y.vert 0 ≠ Y.vert 2 := by
    intro h; have := Y.vert_injective h; omega
  have hz0move2 : z0 • Y.vert 2 ≠ Y.vert 2 := by
    intro h
    exact hz0Q (mem_pCoreOf_of_fixes_two Y.hyp hz0G1 hz0pow
      (by simpa using (Y.adj 0).symm) (Y.adj 1) h02 hfix01 h)
  have hz2move0 : z2 • Y.vert 0 ≠ Y.vert 0 := by
    intro h
    exact hz2Q (mem_pCoreOf_of_fixes_two Y.hyp hz2G1 hz2pow
      (by simpa using (Y.adj 0).symm) (Y.adj 1) h02 h hfix22)
  have hd0 : (z0 * z2) • Y.vert 0 = Y.vert 2 :=
    mul_smul_vert_zero_eq_two Y H hfix01 hfix11 hfix12 hfix22 hz0move2 hz2move0
  have hdcent : ∀ x ∈ (Y.Z 0 ⊓ Y.Q 2 : Subgroup G), (z0 * z2) * x = x * (z0 * z2) := by
    intro x hx
    obtain ⟨hxZ, hxQ2⟩ := Subgroup.mem_inf.mp hx
    have hxQ0 : x ∈ Y.Q 0 := Y.Z_le_Q 0 hxZ
    have hz0x : z0 * x = x * z0 :=
      (Subgroup.mem_centralizer_iff.mp (Y.Z_le_center 0 hz0Z).2 x hxQ0).symm
    have hz2x : z2 * x = x * z2 :=
      (Subgroup.mem_centralizer_iff.mp (Y.Z_le_center 2 hz2Z).2 x hxQ2).symm
    calc (z0 * z2) * x = z0 * (z2 * x) := by group
      _ = z0 * (x * z2) := by rw [hz2x]
      _ = (z0 * x) * z2 := by group
      _ = (x * z0) * z2 := by rw [hz0x]
      _ = x * (z0 * z2) := by group
  intro x hx
  have hxZ : x ∈ Y.Z 0 := hx.1
  have hxconj : z0 * z2 * x * (z0 * z2)⁻¹ ∈ Y.Z 2 := by
    rw [Y.Z_smul Y hd0]
    exact mul_mem_conjSub hxZ
  have hxe : x = z0 * z2 * x * (z0 * z2)⁻¹ := by
    rw [hdcent x hx]
    group
  rwa [hxe]

private theorem Zt_zero_le_Q_two (Y : Setup Γ G)
    (h3 : Y.Zt 0 ≤ Y.Gi 3) : Y.Zt 0 ≤ Y.Q 2 := by
  intro x hx
  have hxZ : x ∈ Y.Z 0 := Zt_le_Z Y 0 hx
  have hxQ0 : x ∈ Y.Q 0 := Y.Z_le_Q 0 hxZ
  have hxG1 : x ∈ Y.Gi 1 := Z_zero_le_Gi_one Y hxZ
  have hxG2 : x ∈ Y.Gi 2 :=
    Y.mem_Gi_of_between hxG1 (h3 hx) (by norm_num) (by norm_num)
  have hpow := exists_pow_two_of_mem (pCoreOf_isPGroup' (Y.Gi 0)) hxQ0
  exact mem_pCoreOf_of_fixes_two Y.hyp hxG2 hpow (by simpa using (Y.adj 1).symm)
    (Y.adj 2) (by intro h; have := Y.vert_injective h; omega)
    (MulAction.mem_stabilizer_iff.mp hxG1) (MulAction.mem_stabilizer_iff.mp (h3 hx))

private theorem Zt_zero_le_Zt_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hb : ¬ Y.Z 0 ≤ Y.Q 1)
    (h3 : Y.Zt 0 ≤ Y.Gi 3) : Y.Zt 0 ≤ Y.Zt 1 := by
  have hZtQ2 : Y.Zt 0 ≤ Y.Q 2 := Zt_zero_le_Q_two Y h3
  have hZtZ0 : Y.Zt 0 ≤ Y.Z 0 := Zt_le_Z Y 0
  have hZInQ : Y.Z 0 ⊓ Y.Q 2 ≤ Y.Z 2 := Z_zero_inf_Q_two_le_Z_two Y H hb
  have hZinfZ : Y.Z 0 ⊓ Y.Z 2 ≤ centerOf (Y.L 1) := Z_zero_inf_Z_two_le_centerOf Y H
  have hZtZ1 : Y.Zt 0 ≤ Y.Z 1 := by
    intro x hx
    have hxZ : x ∈ Y.Z 0 := hZtZ0 hx
    have hxQ : x ∈ Y.Q 2 := hZtQ2 hx
    have hxZ2 : x ∈ Y.Z 2 := hZInQ (Subgroup.mem_inf.mpr ⟨hxZ, hxQ⟩)
    exact Y.centerOf_L_le_Z H.char 1 (hZinfZ (Subgroup.mem_inf.mpr ⟨hxZ, hxZ2⟩))
  have hZtEq : ⁅Y.Zt 0, Y.K⁆ = Y.Zt 0 := (Y.Zt_eq H 0).2.2
  show Y.Zt 0 ≤ ⁅Y.Z 1, Y.K⁆
  rw [← hZtEq]
  exact Subgroup.commutator_mono hZtZ1 le_rfl

private theorem exists_even_ZtExt_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) : ∃ r₀ : ℕ, 1 ≤ r₀ ∧ Even r₀ ∧ Y.ZtExt 0 r₀ r₀ := by
  obtain ⟨l, r0, hl1, hr01, he0⟩ := exists_ZtExt Y H hZ
  obtain ⟨hlr, hEven⟩ := s52_step1 Y H hZ he0
  exact ⟨r0, hr01, hEven, by simpa [hlr] using he0⟩

private theorem two_mul_add_two_of_Zt_one_le_arcStab (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀) {r r₀ : ℕ} (hr : Y.IsMaxRegLen r) (hne : Y.Zt 1 ≠ ⊥)
    (hfix : Y.Zt 1 ≤ Y.arcStab (-(r₀ : ℤ)) ((r₀ : ℤ) + 2)) : 2 * r₀ + 2 ≤ r := by
  by_contra hcon
  have hlt : r < 2 * r₀ + 2 := by omega
  have hGT : Y.arcStab (-(r₀ : ℤ)) ((r₀ : ℤ) + 2) = Y.GT := by
    have h := hr.2 (-(r₀ : ℤ)) (2 * r₀ + 2) (by omega)
    have harg : (-(r₀ : ℤ)) + ((2 * r₀ + 2 : ℕ) : ℤ) = (r₀ : ℤ) + 2 := by
      push_cast
      ring
    rwa [harg] at h
  have hWGT : Y.Zt 1 ≤ Y.GT := by rw [← hGT]; exact hfix
  exact hne (eq_bot_of_le_GT Y H (isPGroup_Zt Y 1) hWGT)

private theorem step2_and_le_of_Zt_one_le_inf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r0 : ℕ} {r : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r0 r0) (hr : Y.IsMaxRegLen r)
    (hW : Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2) (hne : Y.Zt 1 ≠ ⊥) :
    Y.Step2Conclusion s r r0 ∧ 2 * r0 + 2 ≤ r := by
  have harc : Y.Zt 1 ≤ Y.arcStab (-(r0 : ℤ)) ((r0 : ℤ) + 2) := by
    rw [Y.arcStab_eq_inf (by omega)]
    refine le_inf ?_ ?_
    · intro w hw
      have h := he.1 (-(r0 : ℤ)) (by omega) (by omega) (hW.trans inf_le_left hw)
      exact MulAction.mem_stabilizer_iff.mp (by simpa using h)
    · intro w hw
      have h : w ∈ Y.Gi ((r0 : ℤ) + 2) := by
        have h0 := he.Zt_two_mul_le_Gi 1 ((r0 : ℤ) + 2 - 2) (by omega) (by omega)
          (hW.trans inf_le_right hw)
        rwa [show 2 * (1 : ℤ) + ((r0 : ℤ) + 2 - 2) = (r0 : ℤ) + 2 by ring] at h0
      exact MulAction.mem_stabilizer_iff.mp h
  have hbound : 2 * r0 + 2 ≤ r :=
    two_mul_add_two_of_Zt_one_le_arcStab Y H hr hne harc
  exact ⟨s52_step2 Y H hZ hr he, hbound⟩

private theorem Zt_one_eq_bot_of_le_center (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 ≠ ⊥)
    (hc : Y.Zt 1 ≤ centerOf (Y.L 1)) : Y.Zt 1 = ⊥ := by
  by_contra hne
  obtain ⟨r0, hr01, hEven, he⟩ := exists_even_ZtExt_zero Y H hZ
  obtain ⟨r, -, -, hr⟩ := exists_isMaxRegLen Y H
  have hW : Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2 :=
    Zt_one_le_inf_Zt_zero_Zt_two_of_le_center Y H hZ hc
  obtain ⟨h2, hbound⟩ := step2_and_le_of_Zt_one_le_inf Y H hZ he hr hW hne
  rcases h2 with h2a | ⟨h2b, -, -⟩ | ⟨hr6, -, hr02, -⟩
  · omega
  · have h2r0 : 2 ≤ r0 := by
      obtain ⟨k, hk⟩ := hEven
      omega
    rcases Nat.eq_or_lt_of_le h2r0 with hr02' | hr04
    · have h6 : r = 6 := by rw [← h2b]; omega
      have hr6' : Y.IsMaxRegLen 6 := by rwa [h6] at hr
      have he2 : Y.ZtExt 0 2 2 := by simpa [hr02'] using he
      exact hne (Zt_one_eq_bot_of_ZtExt_two Y H hr6' he2 hW)
    · have h4 : 4 ≤ r0 := by
        obtain ⟨k, hk⟩ := hEven
        omega
      have hrr : r ≤ 2 * r0 + 2 := by omega
      have hb := not_Z_zero_le_Q_one Y H hZ hr he h4 hrr
      have h3 : Y.Zt 0 ≤ Y.Gi 3 := by
        have h := he.1 3 (by omega) (by omega)
        simpa using h
      have hZtW : Y.Zt 0 ≤ Y.Zt 1 := Zt_zero_le_Zt_one Y H hb h3
      have hW2 : Y.Zt 1 ≤ Y.Zt 2 := hW.trans inf_le_right
      have h : Y.Zt 2 ≤ Y.Gi ((r0 : ℤ) + 1) := by
        simpa using he.Zt_two_mul_le_Gi 1 ((r0 : ℤ) + 1 - 2) (by omega) (by omega)
      have hZtGi : Y.Zt 0 ≤ Y.Gi ((r0 : ℤ) + 1) := hZtW.trans (hW2.trans h)
      exact he.2.1 (by simpa using hZtGi)
  · have hr6' : Y.IsMaxRegLen 6 := by rwa [hr6] at hr
    have he2 : Y.ZtExt 0 2 2 := by simpa [hr02] using he
    exact hne (Zt_one_eq_bot_of_ZtExt_two Y H hr6' he2 hW)

private theorem Zt_one_inf_centralizer_S_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) :
    Y.Zt 1 ⊓ Subgroup.centralizer (Y.S : Set G) = Y.Zt 0 ⊓ Y.Zt 1 := by
  refine le_antisymm (le_inf (Zt_one_inf_centralizer_S_le Y H hZ) inf_le_left) ?_
  intro x hx
  obtain ⟨hx0, hx1⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨hx1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hS : Y.S = Y.Q 0 ⊔ Y.Q 1 := (Y.sup_Q_eq_edgeSylow H.char 0).symm
  have hxZ0 : x ∈ Y.Z 0 := Zt_le_Z Y 0 hx0
  have hxZ1 : x ∈ Y.Z 1 := Zt_le_Z Y 1 hx1
  have hcomm0 : ∀ q ∈ Y.Q 0, x * q = q * x := by
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (Y.Z_le_center 0 hxZ0)).2 q hq).symm
  have hcomm1 : ∀ q ∈ Y.Q 1, x * q = q * x := by
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (Y.Z_le_center 1 hxZ1)).2 q hq).symm
  have hle : Y.Q 0 ⊔ Y.Q 1 ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_
    · intro q hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm0 q hq).symm
    · intro q hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm1 q hq).symm
  rw [← hS] at hle
  exact (Subgroup.mem_centralizer_iff.mp (hle hs) x (by simp)).symm

private theorem Zt_two_inf_centralizer_edgeSylow_one_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) :
    Y.Zt 1 ⊓ Subgroup.centralizer (Y.edgeSylow 1 : Set G) = Y.Zt 2 ⊓ Y.Zt 1 := by
  obtain ⟨g, hg, hg02⟩ := Y.exists_normalizer_K_one H (a := Y.vert 0) (b := Y.vert 2)
    (by simpa using (Y.adj 0).symm) (Y.adj 1)
  obtain ⟨hgN, hgG1⟩ := Subgroup.mem_inf.mp hg
  have hZt1n : conjSub g (Y.Zt 1) = Y.Zt 1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Gi_one_le_normalizer_Zt_one Y H) hgG1)
  have hZtn : conjSub g (Y.Zt 0) = Y.Zt 2 := conjSub_Zt_zero_eq_Zt_two Y hgN hg02
  have hG0n : conjSub g (Y.Gi 0) = Y.Gi 2 := by
    rw [← stabilizer_smul_eq_conjSub, hg02]
  have hS_edge : conjSub g (Y.S) = Y.edgeSylow 1 := by
    rw [← Y.edgeSylow_zero]
    unfold Setup.edgeSylow
    rw [show (0 : ℤ) + 1 = 1 by norm_num, ← pCoreOf_conjSub, conjSub_inf,
      conjSub_eq_of_mem hgG1, hG0n, inf_comm]
    congr 1
  calc Y.Zt 1 ⊓ Subgroup.centralizer (Y.edgeSylow 1 : Set G)
      = conjSub g (Y.Zt 1 ⊓ Subgroup.centralizer (Y.S : Set G)) := by
        rw [conjSub_inf, hZt1n, ← conjSub_centralizer, hS_edge]
    _ = conjSub g (Y.Zt 0 ⊓ Y.Zt 1) := by rw [Zt_one_inf_centralizer_S_eq Y H hZ]
    _ = Y.Zt 2 ⊓ Y.Zt 1 := by rw [conjSub_inf, hZtn, hZt1n]

private theorem commutator_sup_three_le {G : Type*} [Group G] {Z A B C K W : Subgroup G}
    (hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (hAZ : A ≤ Z) (hBZ : B ≤ Z) (hCZ : C ≤ Z) (hWZ : W ≤ Z)
    (hAK : ⁅A, K⁆ ≤ W) (hBK : ⁅B, K⁆ ≤ W) (hCK : ⁅C, K⁆ ≤ W) :
    ⁅A ⊔ B ⊔ C, K⁆ ≤ W := by
  classical
  let T : Subgroup G :=
    { carrier := {g | g ∈ Z ∧ ∀ k ∈ K, ⁅g, k⁆ ∈ W}
      one_mem' := ⟨Z.one_mem, fun k _ => by simp⟩
      mul_mem' := by
        rintro g h ⟨hgZ, hg⟩ ⟨hhZ, hh⟩
        refine ⟨Z.mul_mem hgZ hhZ, fun k hk => ?_⟩
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hgW : ⁅g, k⁆ ∈ W := hg k hk
        have hhW : ⁅h, k⁆ ∈ W := hh k hk
        have hconj : g * ⁅h, k⁆ * g⁻¹ = ⁅h, k⁆ := by
          rw [hZab g hgZ ⁅h, k⁆ (hWZ hhW)]
          group
        rw [hconj]
        exact W.mul_mem hhW hgW
      inv_mem' := by
        rintro g ⟨hgZ, hg⟩
        refine ⟨Z.inv_mem hgZ, fun k hk => ?_⟩
        have hgW : ⁅g, k⁆ ∈ W := hg k hk
        have e : ⁅g⁻¹, k⁆ = g⁻¹ * ⁅g, k⁆⁻¹ * g := by
          simp only [commutatorElement_def]; group
        rw [e]
        have hconj : g⁻¹ * ⁅g, k⁆⁻¹ * g = ⁅g, k⁆⁻¹ := by
          rw [hZab g⁻¹ (Z.inv_mem hgZ) ⁅g, k⁆⁻¹ (hWZ (W.inv_mem hgW))]
          group
        rw [hconj]
        exact W.inv_mem hgW }
  have hle : A ⊔ B ⊔ C ≤ T := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      exact ⟨hAZ ha, fun k hk => hAK (Subgroup.commutator_mem_commutator ha hk)⟩
    · intro b hb
      exact ⟨hBZ hb, fun k hk => hBK (Subgroup.commutator_mem_commutator hb hk)⟩
    · intro c hc
      exact ⟨hCZ hc, fun k hk => hCK (Subgroup.commutator_mem_commutator hc hk)⟩
  rw [Subgroup.commutator_le]
  intro x hx k hk
  exact (hle hx).2 k hk

private theorem conjSub_S_eq_or_of_mem_Gi_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {p : V} (hp : Γ.Adj (Y.vert 1) p) (hp0 : p ≠ Y.vert 0) (hp2 : p ≠ Y.vert 2)
    {g : G} (hg : g ∈ Y.Gi 1) (hgp : g • Y.vert 0 = p) {c : G} (hc : c ∈ Y.Gi 1) :
    conjSub c Y.S = Y.S ∨ conjSub c Y.S = Y.edgeSylow 1 ∨ conjSub c Y.S = conjSub g Y.S := by
  have hcardN : (Γ.neighborSet (Y.vert 1)).ncard = 3 := by
    rw [← Nat.card_coe_set_eq, (Y.hyp.valency (Y.vert 1)).2]
    change 2 ^ Y.n 1 + 1 = 3
    rw [H.n_one]
    norm_num
  have hsub : ({Y.vert 0, Y.vert 2, p} : Set V) ⊆ Γ.neighborSet (Y.vert 1) := by
    intro x hx
    rw [SimpleGraph.mem_neighborSet]
    rcases hx with rfl | rfl | rfl
    · simpa using (Y.adj 0).symm
    · exact Y.adj 1
    · exact hp
  have hne02 : Y.vert 0 ≠ Y.vert 2 := by
    intro h
    have := Y.vert_injective h
    omega
  have hnp : ({Y.vert 0, Y.vert 2, p} : Set V).ncard = 3 := by
    refine Set.ncard_eq_three.mpr ⟨Y.vert 0, Y.vert 2, p, hne02, ?_, ?_, rfl⟩
    · exact Ne.symm hp0
    · exact Ne.symm hp2
  have hset : ({Y.vert 0, Y.vert 2, p} : Set V) = Γ.neighborSet (Y.vert 1) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Y.hyp.finite_neighborSet (Y.vert 1))
    rw [hcardN, hnp]
  have hmem : ∀ v : V, Γ.Adj (Y.vert 1) v → v = Y.vert 0 ∨ v = Y.vert 2 ∨ v = p := by
    intro v hv
    have hv' : v ∈ ({Y.vert 0, Y.vert 2, p} : Set V) := by
      rw [hset]
      simpa using hv
    simpa using hv'
  have hadj : Γ.Adj (Y.vert 1) (c • Y.vert 0) := by
    have h := (Y.hyp.adj_smul c (Y.vert 1) (Y.vert 0)).mpr (by simpa using (Y.adj 0).symm)
    rwa [MulAction.mem_stabilizer_iff.mp (by simpa [Setup.Gi] using hc)] at h
  rcases hmem (c • Y.vert 0) hadj with hc0 | hc0 | hc0
  · left
    have hSconj : conjSub c Y.S = Y.S := by
      rw [← Y.edgeSylow_zero]
      unfold Setup.edgeSylow
      rw [show (0 : ℤ) + 1 = 1 by norm_num, ← pCoreOf_conjSub, conjSub_inf,
        conjSub_eq_of_mem hc, ← stabilizer_smul_eq_conjSub, hc0, inf_comm]
    exact hSconj
  · right; left
    have hSconj : conjSub c Y.S = Y.edgeSylow 1 := by
      rw [← Y.edgeSylow_zero]
      unfold Setup.edgeSylow
      rw [show (0 : ℤ) + 1 = 1 by norm_num, ← pCoreOf_conjSub, conjSub_inf,
        conjSub_eq_of_mem hc, ← stabilizer_smul_eq_conjSub, hc0, inf_comm]
      rw [show (1 : ℤ) + 1 = 2 by norm_num]
    exact hSconj
  · right; right
    have hSconj : conjSub c Y.S = conjSub g Y.S := by
      have h1 : conjSub c Y.S = pCoreOf 2 (Y.Gi 1 ⊓ MulAction.stabilizer G p) := by
        rw [← Y.edgeSylow_zero]
        unfold Setup.edgeSylow
        rw [show (0 : ℤ) + 1 = 1 by norm_num, ← pCoreOf_conjSub, conjSub_inf,
          conjSub_eq_of_mem hc, ← stabilizer_smul_eq_conjSub, hc0, inf_comm]
      have h2 : conjSub g Y.S = pCoreOf 2 (Y.Gi 1 ⊓ MulAction.stabilizer G p) := by
        rw [← Y.edgeSylow_zero]
        unfold Setup.edgeSylow
        rw [show (0 : ℤ) + 1 = 1 by norm_num, ← pCoreOf_conjSub, conjSub_inf,
          conjSub_eq_of_mem hg, ← stabilizer_smul_eq_conjSub, hgp, inf_comm]
      rw [h1, h2]
    exact hSconj

private theorem Z_one_le_sup_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {p : V} (hp : Γ.Adj (Y.vert 1) p) (hp0 : p ≠ Y.vert 0) (hp2 : p ≠ Y.vert 2)
    {g : G} (hg : g ∈ Y.Gi 1) (hgp : g • Y.vert 0 = p) :
    Y.Z 1 ≤ (centerOf Y.S ⊓ Y.Q 1) ⊔ (centerOf (Y.edgeSylow 1) ⊓ Y.Q 1) ⊔
      (centerOf (conjSub g Y.S) ⊓ Y.Q 1) := by
  have hSylS : IsSylowTwoOf Y.S (Y.Gi 1) := by
    simpa [Y.edgeSylow_zero] using Y.isSylowTwoOf_edgeSylow_Gi_succ 0
  rw [Setup.Z]
  refine iSup_le fun P => iSup_le fun hP => ?_
  intro x hx
  obtain ⟨hxP, hxQ⟩ := Subgroup.mem_inf.mp hx
  haveI hfinGi1 : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  obtain ⟨c, hcG1, hcP⟩ :=
    CFSG.Quasithin.RonanF713.isSylowTwoOf_exists_conj_le_loc hSylS hP.1 hP.2.1
  have hcPsyl : IsSylowTwoOf (conjSub c Y.S) (Y.Gi 1) := by
    have h := CFSG.Quasithin.F7.isSylowTwoOf_conj hSylS c
    rwa [conjSub_eq_of_mem hcG1] at h
  have hPeq : P = conjSub c Y.S := by
    haveI : Finite ↥(conjSub c Y.S) := finite_of_le_stabilizer Y.hyp hcPsyl.1
    exact (CFSG.GroupTheory.eq_of_isSylowTwoOf_of_le hP hcPsyl.2.1 hcPsyl.1 hcP).symm
  rw [hPeq] at hxP
  have hxQ1 : x ∈ Y.Q 1 := hxQ
  have hxcen : x ∈ conjSub c (centerOf Y.S) := by
    rw [centerOf_conjSub] at hxP
    exact hxP
  have hQn : conjSub c (Y.Q 1) = Y.Q 1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1) hcG1)
  have hxcone : x ∈ conjSub c (centerOf Y.S ⊓ Y.Q 1) := by
    rw [conjSub_inf]
    exact Subgroup.mem_inf.mpr ⟨hxcen, by rw [hQn]; exact hxQ1⟩
  rcases conjSub_S_eq_or_of_mem_Gi_one Y H hp hp0 hp2 hg hgp hcG1 with hS | hS | hS
  ·
    have hx0 : x ∈ centerOf Y.S ⊓ Y.Q 1 := by
      rw [conjSub_inf, hQn, ← centerOf_conjSub] at hxcone
      rwa [hS] at hxcone
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hx0)
  ·
    have hx2 : x ∈ centerOf (Y.edgeSylow 1) ⊓ Y.Q 1 := by
      rw [conjSub_inf, hQn, ← centerOf_conjSub] at hxcone
      rwa [hS] at hxcone
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hx2)
  ·
    have hxp : x ∈ centerOf (conjSub g Y.S) ⊓ Y.Q 1 := by
      rw [conjSub_inf, hQn, ← centerOf_conjSub] at hxcone
      rwa [hS] at hxcone
    exact Subgroup.mem_sup_right hxp

private theorem ZtExt_one_lower (Y : Setup Γ G) {r₀ l r : ℕ}
    (hU : Y.ZtExt 1 l r)
    (hfix : Y.Zt 1 ≤ Y.arcStab (2 - (r₀ : ℤ)) (r₀ : ℤ)) :
    r₀ - 1 ≤ l ∧ r₀ - 1 ≤ r := by
  constructor
  · by_contra hlt
    push Not at hlt
    have hj1 : 2 - (r₀ : ℤ) ≤ 1 - (l : ℤ) - 1 := by omega
    have hj2 : 1 - (l : ℤ) - 1 ≤ (r₀ : ℤ) := by omega
    have hle : Y.Zt 1 ≤ Y.Gi (1 - (l : ℤ) - 1) :=
      hfix.trans (Y.arcStab_le_Gi_of_between (m := 2 - (r₀ : ℤ)) (r := (r₀ : ℤ))
        (k := 1 - (l : ℤ) - 1) hj1 hj2)
    exact hU.2.2 hle
  · by_contra hlt
    push Not at hlt
    have hj1 : 2 - (r₀ : ℤ) ≤ (r : ℤ) + 2 := by omega
    have hj2 : (r : ℤ) + 2 ≤ (r₀ : ℤ) := by omega
    have hle : Y.Zt 1 ≤ Y.Gi ((r : ℤ) + 2) :=
      hfix.trans (Y.arcStab_le_Gi_of_between (m := 2 - (r₀ : ℤ)) (r := (r₀ : ℤ))
        (k := (r : ℤ) + 2) hj1 hj2)
    exact hU.2.1 (by simpa [show (1 : ℤ) + (r : ℤ) + 1 = (r : ℤ) + 2 by ring] using hle)

private theorem sup_Q_eq_pCoreOf_of_K_invariant (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {j : ℤ} (hj : Even j) {U : Subgroup G} (h2 : IsPGroup 2 U) (hU : U ≤ Y.Gi j)
    (hKU : Y.K ≤ Subgroup.normalizer (U : Set G)) (hQ : ¬ U ≤ Y.Q j)
    (hω : U ≤ Y.Gi (j - 1)) : U ⊔ Y.Q j = pCoreOf 2 (Y.Gi j ⊓ Y.Gi (j - 1)) := by
  have h := (gen_of_K_invariant Y.reverse H.reverse (j := -j) (U := U) hj.neg h2
    (by rw [Setup.reverse_Gi]; simpa using hU)
    (by simpa only [Setup.reverse_K] using hKU)
    (by rw [Setup.reverse_Q]; simpa using hQ)
    (by
      rw [Setup.reverse_Gi]
      rwa [show -(-j + 1) = j - 1 by ring])).1
  rw [Setup.reverse_Q, Setup.reverse_Gi, Setup.reverse_Gi] at h
  rwa [show -(-j) = j by ring, show -(-j + 1) = j - 1 by ring] at h

private theorem Zt_le_Q_one_of_ZtExt (Y : Setup Γ G) {r₀ : ℕ} (he : Y.ZtExt 0 r₀ r₀)
    (heven : Even r₀) (hr1 : 1 ≤ r₀) : Y.Zt (r₀ : ℤ) ≤ Y.Q 1 := by
  have hZt2 : ∀ i : ℤ, IsPGroup 2 (Y.Zt i) := fun i => isPGroup_Zt Y i
  obtain ⟨k, hk⟩ := heven
  have hkZ : (r₀ : ℤ) = 2 * (k : ℤ) := by
    have h : (r₀ : ℤ) = (k : ℤ) + (k : ℤ) := by exact_mod_cast hk
    linarith
  have hB_le_Gi : ∀ j : ℤ, -(r₀ : ℤ) ≤ j → j ≤ (r₀ : ℤ) →
      Y.Zt (r₀ : ℤ) ≤ Y.Gi ((r₀ : ℤ) + j) := by
    intro j h1 h2
    have h := he.Zt_two_mul_le_Gi (k : ℤ) j h1 h2
    rwa [show 2 * (k : ℤ) = (r₀ : ℤ) by rw [hkZ]] at h
  have hB_le_Gi_zero : Y.Zt (r₀ : ℤ) ≤ Y.Gi 0 := by
    have h := hB_le_Gi (-(r₀ : ℤ)) (by omega) (by omega)
    rwa [show (r₀ : ℤ) + -(r₀ : ℤ) = 0 by ring] at h
  have hB_le_Gi_one : Y.Zt (r₀ : ℤ) ≤ Y.Gi 1 := by
    have h := hB_le_Gi (1 - (r₀ : ℤ)) (by omega) (by omega)
    rwa [show (r₀ : ℤ) + (1 - (r₀ : ℤ)) = 1 by ring] at h
  have hB_le_Gi_two : Y.Zt (r₀ : ℤ) ≤ Y.Gi 2 := by
    have h := hB_le_Gi (2 - (r₀ : ℤ)) (by omega) (by omega)
    rwa [show (r₀ : ℤ) + (2 - (r₀ : ℤ)) = 2 by ring] at h
  have h02 : Y.vert 0 ≠ Y.vert 2 := by
    intro h
    have h' := Y.vert_injective h
    norm_num at h'
  exact le_pCoreOf_of_isPGroup_fixes_two Y.hyp (hZt2 (r₀ : ℤ)) hB_le_Gi_one
    (by simpa using (Y.adj 0).symm) (Y.adj 1) h02
    (fun y hy => MulAction.mem_stabilizer_iff.mp (hB_le_Gi_zero hy))
    (fun y hy => MulAction.mem_stabilizer_iff.mp (hB_le_Gi_two hy))

private theorem not_right_len_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ l r : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) (hU : Y.ZtExt 1 l r)
    (hr : r = r₀ - 1) (hfixm1 : Y.Zt 1 ≤ Y.Gi ((r₀ : ℤ) - 1)) : False := by
  have hZt_le_Z : ∀ i : ℤ, Y.Zt i ≤ Y.Z i := fun i => Zt_le_Z Y i
  have hZt2 : ∀ i : ℤ, IsPGroup 2 (Y.Zt i) := fun i => isPGroup_Zt Y i
  have heven : Even r₀ := (s52_step1 Y H hZ he).2
  have hevenZ : Even (r₀ : ℤ) := by
    obtain ⟨d, hd⟩ := heven
    exact ⟨(d : ℤ), by rw [hd]; push_cast; ring⟩
  have hr1 : 1 ≤ r₀ := by
    rcases Nat.eq_zero_or_pos r₀ with h | h
    · exfalso
      apply he.2.1
      rw [h]
      have hZtQ : Y.Zt 0 ≤ Y.Q 0 := (hZt_le_Z 0).trans (Y.Z_le_Q 0)
      refine hZtQ.trans (fun q hq => MulAction.mem_stabilizer_iff.mpr ?_)
      exact Y.Q_fixes_neighbors_vert 0 (Y.vert 1) (Y.adj 0) q hq
    · exact h
  have hrZ : (r : ℤ) = (r₀ : ℤ) - 1 := by omega
  have hU_le : Y.Zt 1 ≤ Y.Gi (r₀ : ℤ) := by
    have h := hU.1 ((r₀ : ℤ) - 1) (by omega) (by omega)
    rwa [show (1 : ℤ) + ((r₀ : ℤ) - 1) = (r₀ : ℤ) by ring] at h
  have hnotUQ : ¬ Y.Zt 1 ≤ Y.Q (r₀ : ℤ) := by
    intro hQ
    have hcon : ¬ Y.Zt 1 ≤ Y.Gi ((r₀ : ℤ) + 1) := by
      have h := hU.2.1
      rwa [show (1 : ℤ) + (r : ℤ) + 1 = (r₀ : ℤ) + 1 by rw [hrZ]; ring] at h
    exact hcon (hQ.trans ((Y.Q_le_Gi_adj (r₀ : ℤ)).trans inf_le_right))
  have hV_le : Y.Zt 0 ≤ Y.Gi (r₀ : ℤ) := by
    simpa using he.1 (r₀ : ℤ) (by omega) le_rfl
  have hV_fix : Y.Zt 0 ≤ Y.Gi ((r₀ : ℤ) - 1) := by
    simpa using he.1 ((r₀ : ℤ) - 1) (by omega) (by omega)
  have hnotVQ : ¬ Y.Zt 0 ≤ Y.Q (r₀ : ℤ) := by
    intro hQ
    have hcon : ¬ Y.Zt 0 ≤ Y.Gi ((r₀ : ℤ) + 1) := by simpa using he.2.1
    exact hcon (hQ.trans ((Y.Q_le_Gi_adj (r₀ : ℤ)).trans inf_le_right))
  have hKU : Y.K ≤ Subgroup.normalizer (Y.Zt 1 : Set G) := K_le_normalizer_Zt Y 1
  have hKV : Y.K ≤ Subgroup.normalizer (Y.Zt 0 : Set G) := K_le_normalizer_Zt Y 0
  have hGU' : Y.Zt 1 ⊔ Y.Q (r₀ : ℤ) =
      pCoreOf 2 (Y.Gi (r₀ : ℤ) ⊓ Y.Gi ((r₀ : ℤ) - 1)) :=
    sup_Q_eq_pCoreOf_of_K_invariant Y H hevenZ (hZt2 1) hU_le hKU hnotUQ hfixm1
  have hGV' : Y.Zt 0 ⊔ Y.Q (r₀ : ℤ) =
      pCoreOf 2 (Y.Gi (r₀ : ℤ) ⊓ Y.Gi ((r₀ : ℤ) - 1)) :=
    sup_Q_eq_pCoreOf_of_K_invariant Y H hevenZ (hZt2 0) hV_le hKV hnotVQ hV_fix
  have hsup_eq : Y.Zt 1 ⊔ Y.Q (r₀ : ℤ) = Y.Zt 0 ⊔ Y.Q (r₀ : ℤ) := hGU'.trans hGV'.symm
  have hV_le_sup : Y.Zt 0 ≤ Y.Zt 1 ⊔ Y.Q (r₀ : ℤ) := by
    rw [hsup_eq]
    exact le_sup_left
  have hB_le_Q1 := Zt_le_Q_one_of_ZtExt Y he heven hr1
  have hU_cent : Y.Zt 1 ≤ Subgroup.centralizer (Y.Zt (r₀ : ℤ) : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have huc : u ∈ Subgroup.centralizer (Y.Q 1 : Set G) :=
      (Y.Z_le_center 1 (hZt_le_Z 1 hu)).2
    exact Subgroup.mem_centralizer_iff.mp huc b (hB_le_Q1 hb)
  have hQ_cent : Y.Q (r₀ : ℤ) ≤ Subgroup.centralizer (Y.Zt (r₀ : ℤ) : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbc : b ∈ Subgroup.centralizer (Y.Q (r₀ : ℤ) : Set G) :=
      (Y.Z_le_center (r₀ : ℤ) (hZt_le_Z (r₀ : ℤ) hb)).2
    exact (Subgroup.mem_centralizer_iff.mp hbc q hq).symm
  have hV_cent : Y.Zt 0 ≤ Subgroup.centralizer (Y.Zt (r₀ : ℤ) : Set G) :=
    hV_le_sup.trans (sup_le hU_cent hQ_cent)
  exact comm_Zt_ne_bot_of_ZtExt Y H hZ he
    ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hV_cent)

private theorem ZtExt_one_ge (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ l r : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (he : Y.ZtExt 0 r₀ r₀) (hU : Y.ZtExt 1 l r)
    (hfix : Y.Zt 1 ≤ Y.arcStab (2 - (r₀ : ℤ)) (r₀ : ℤ)) :
    r₀ + 1 ≤ l ∧ r₀ + 1 ≤ r := by
  have hr0 : 1 ≤ r₀ := by
    rcases Nat.eq_zero_or_pos r₀ with h0 | hpos
    · exfalso
      have hZtQ : Y.Zt 0 ≤ Y.Q 0 := (Zt_le_Z Y 0).trans (Y.Z_le_Q 0)
      have hle1 : Y.Zt 0 ≤ Y.Gi 1 := hZtQ.trans (by
        intro q hq
        exact MulAction.mem_stabilizer_iff.mpr
          (Y.Q_fixes_neighbors_vert 0 (Y.vert 1) (Y.adj 0) q hq))
      apply he.2.1
      simpa [h0] using hle1
    · exact hpos
  have hEven : Even r₀ := (s52_step1 Y H hZ he).2
  have hr02 : 2 ≤ r₀ := by
    obtain ⟨k, hk⟩ := hEven
    omega
  have hEvenU := even_of_ZtExt Y H hU
  have hoddl : Odd l := by
    have h1 : Even ((l : ℤ) - 1) := by
      have h := hEvenU.1.neg
      rwa [show -(1 - (l : ℤ)) = (l : ℤ) - 1 by ring] at h
    exact (Int.odd_coe_nat l).mp (even_sub_one.mp h1)
  have hoddR : Odd r := by
    have h1 : Even ((r : ℤ) + 1) := by
      simpa [add_comm] using hEvenU.2
    exact (Int.odd_coe_nat r).mp (even_add_one.mp h1)
  obtain ⟨hlow, hrlow⟩ := ZtExt_one_lower Y hU hfix
  have hfixm1 : Y.Zt 1 ≤ Y.Gi ((r₀ : ℤ) - 1) :=
    hfix.trans (Y.arcStab_le_Gi_of_between (m := 2 - (r₀ : ℤ)) (r := (r₀ : ℤ))
      (k := (r₀ : ℤ) - 1) (by omega) (by omega))
  have hnr : ¬ r = r₀ - 1 := fun h => not_right_len_eq Y H hZ he hU h hfixm1
  have hnl : ¬ l = r₀ - 1 := by
    intro hl
    have hUmir : Y.mirror1.ZtExt 1 r l := by simpa using hU.mirror1
    have hemir : Y.mirror1.ZtExt 0 r₀ r₀ := by simpa using (he.add_two_mul 1).mirror1
    have hZmir : Y.mirror1.Zt 0 ≠ ⊥ := by
      rw [mirror1_Zt]
      simpa using Y.Zt_ne_bot_of_even even_two hZ
    have hfixmir : Y.mirror1.Zt 1 ≤ Y.mirror1.Gi ((r₀ : ℤ) - 1) := by
      rw [Setup.mirror1_Zt]
      norm_num
      have hlcast : (l : ℤ) = (r₀ : ℤ) - 1 := by
        rw [hl]
        omega
      have hrcast : (r₀ : ℤ) - 1 ≤ (r : ℤ) := by exact_mod_cast hrlow
      have hleft : -(l : ℤ) ≤ 2 - (r₀ : ℤ) := by omega
      have hright : 2 - (r₀ : ℤ) ≤ (r : ℤ) := by omega
      have h := hU.1 (2 - (r₀ : ℤ)) hleft hright
      have h' : Y.Zt 1 ≤ Y.Gi (1 + (2 - (r₀ : ℤ))) := h
      simpa [Setup.mirror1_Gi, show (2 : ℤ) - ((r₀ : ℤ) - 1) = 1 + (2 - (r₀ : ℤ)) by ring] using h'
    exact not_right_len_eq Y.mirror1 H.mirror1 hZmir hemir hUmir hl hfixmir
  constructor
  · obtain ⟨k, hk⟩ := hoddl
    obtain ⟨m, hm⟩ := hEven
    have hlgt : r₀ - 1 < l := lt_of_le_of_ne hlow (by intro h; exact hnl h.symm)
    have hlne : l ≠ r₀ := by
      intro h
      rw [h] at hk
      omega
    have hle : r₀ ≤ l := by omega
    have : r₀ < l := lt_of_le_of_ne hle (Ne.symm hlne)
    omega
  · obtain ⟨k, hk⟩ := hoddR
    obtain ⟨m, hm⟩ := hEven
    have hrgt : r₀ - 1 < r := lt_of_le_of_ne hrlow (by intro h; exact hnr h.symm)
    have hrne : r ≠ r₀ := by
      intro h
      rw [h] at hk
      omega
    have hle : r₀ ≤ r := by omega
    have : r₀ < r := lt_of_le_of_ne hle (Ne.symm hrne)
    omega

private theorem eq_of_mem_Zt_one_of_smul_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hfix : Y.Zt 1 ≤ Y.arcStab (-(r₀ : ℤ)) ((r₀ : ℤ) + 2))
    (hmax : Y.arcStab (-(r₀ : ℤ)) ((r₀ : ℤ) + 3) = Y.GT) {x y : G}
    (hx : x ∈ Y.Zt 1) (hy : y ∈ Y.Zt 1)
    (hxy : x • Y.vert ((r₀ : ℤ) + 3) = y • Y.vert ((r₀ : ℤ) + 3)) : x = y := by
  have hxy' : (x⁻¹ * y) • Y.vert ((r₀ : ℤ) + 3) = Y.vert ((r₀ : ℤ) + 3) := by
    rw [mul_smul, ← hxy]
    simp
  have hmem : x⁻¹ * y ∈ Y.Zt 1 := (Y.Zt 1).mul_mem ((Y.Zt 1).inv_mem hx) hy
  have hGT : x⁻¹ * y ∈ Y.GT := by
    rw [← hmax]
    rw [Y.arcStab_eq_inf (by omega)]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := hfix hmem
      exact (Y.arcStab_le_Gi_of_between (m := -(r₀ : ℤ)) (r := (r₀ : ℤ) + 2)
        (k := -(r₀ : ℤ)) le_rfl (by omega)) this
    · exact hxy'
  have hbot : Y.Zt 1 ⊓ Y.GT = ⊥ :=
    eq_bot_of_le_GT Y H ((isPGroup_Zt Y 1).to_le inf_le_left) inf_le_right
  have hmeminf : x⁻¹ * y ∈ Y.Zt 1 ⊓ Y.GT := Subgroup.mem_inf.mpr ⟨hmem, hGT⟩
  rw [hbot] at hmeminf
  have h1 : x⁻¹ * y = 1 := Subgroup.mem_bot.mp hmeminf
  exact inv_mul_eq_one.mp h1

private theorem K_transitive_on_Zt_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hfix : Y.Zt 1 ≤ Y.arcStab (-(r₀ : ℤ)) ((r₀ : ℤ) + 2))
    (hmax : Y.arcStab (-(r₀ : ℤ)) ((r₀ : ℤ) + 3) = Y.GT) :
    ∀ x ∈ Y.Zt 1, x ≠ 1 → ∀ y ∈ Y.Zt 1, y ≠ 1 → ∃ k ∈ Y.K, k * x * k⁻¹ = y := by
  set v : ℤ := (r₀ : ℤ) + 2 with hv
  have hvadj : Γ.Adj (Y.vert v) (Y.vert (v + 1)) := Y.adj v
  have hVv : Y.Zt 1 ≤ Y.Gi v := by
    have hle : -(r₀ : ℤ) ≤ v := by omega
    have hle' : v ≤ (r₀ : ℤ) + 2 := by omega
    exact hfix.trans (Y.arcStab_le_Gi_of_between hle hle')
  have hVpred : Y.Zt 1 ≤ Y.Gi (v - 1) := by
    have hle : -(r₀ : ℤ) ≤ v - 1 := by omega
    have hle' : v - 1 ≤ (r₀ : ℤ) + 2 := by omega
    exact hfix.trans (Y.arcStab_le_Gi_of_between hle hle')
  have hinj : ∀ x ∈ Y.Zt 1, ∀ y ∈ Y.Zt 1,
      x • Y.vert (v + 1) = y • Y.vert (v + 1) → x = y := by
    intro x hx y hy hxy
    refine eq_of_mem_Zt_one_of_smul_eq Y H hfix hmax hx hy ?_
    rw [show (r₀ : ℤ) + 3 = v + 1 by omega]
    exact hxy
  intro x hx hx1 y hy hy1
  have hxadj : Γ.Adj (Y.vert v) (x • Y.vert (v + 1)) := by
    have hxfix : x • Y.vert v = Y.vert v := MulAction.mem_stabilizer_iff.mp (hVv hx)
    have h := (Y.hyp.adj_smul x (Y.vert v) (Y.vert (v + 1))).mpr hvadj
    rwa [hxfix] at h
  have hyadj : Γ.Adj (Y.vert v) (y • Y.vert (v + 1)) := by
    have hyfix : y • Y.vert v = Y.vert v := MulAction.mem_stabilizer_iff.mp (hVv hy)
    have h := (Y.hyp.adj_smul y (Y.vert v) (Y.vert (v + 1))).mpr hvadj
    rwa [hyfix] at h
  have hx1' : x • Y.vert (v + 1) ≠ Y.vert (v + 1) := by
    intro h
    exact hx1 (hinj x hx 1 (Y.Zt 1).one_mem (by simpa using h))
  have hy1' : y • Y.vert (v + 1) ≠ Y.vert (v + 1) := by
    intro h
    exact hy1 (hinj y hy 1 (Y.Zt 1).one_mem (by simpa using h))
  have hpred : ∀ z ∈ Y.Zt 1, z • Y.vert (v + 1) ≠ Y.vert (v - 1) := by
    intro z hz hzpred
    have hzinv : z⁻¹ • Y.vert (v - 1) = Y.vert (v - 1) :=
      MulAction.mem_stabilizer_iff.mp (hVpred ((Y.Zt 1).inv_mem hz))
    have := congrArg (fun w => z⁻¹ • w) hzpred
    rw [inv_smul_smul, hzinv] at this
    have hne : Y.vert (v + 1) ≠ Y.vert (v - 1) := by
      intro heq
      have := Y.vert_injective heq
      omega
    exact hne this
  obtain ⟨k, hkKi, hkab⟩ :=
    Y.Ki_transitive_gen v hxadj hyadj (hpred x hx) hx1' (hpred y hy) hy1'
  have hkK : k ∈ Y.K := hkKi.1
  have hkfixsucc : k • Y.vert (v + 1) = Y.vert (v + 1) := Y.K_fix k hkK _
  have hkfixinv : k⁻¹ • Y.vert (v + 1) = Y.vert (v + 1) := by
    conv_lhs => rw [← hkfixsucc]
    rw [inv_smul_smul]
  have hxn : k * x * k⁻¹ ∈ Y.Zt 1 := by
    have hkn : k ∈ Subgroup.normalizer (Y.Zt 1 : Set G) := K_le_normalizer_Zt Y 1 hkK
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hkn
    have := mul_mem_conjSub (g := k) hx
    rwa [show conjSub k (Y.Zt 1) = Y.Zt 1 from hkn] at this
  have heq : (k * x * k⁻¹) • Y.vert (v + 1) = y • Y.vert (v + 1) := by
    calc (k * x * k⁻¹) • Y.vert (v + 1)
        = k • (x • (k⁻¹ • Y.vert (v + 1))) := by simp [mul_smul]
      _ = k • (x • Y.vert (v + 1)) := by rw [hkfixinv]
      _ = y • Y.vert (v + 1) := hkab
  exact ⟨k, hkK, hinj (k * x * k⁻¹) hxn y hy heq⟩

private theorem commutator_centerOf_inf_Q_one_le (Y : Setup Γ G) {P : Subgroup G}
    (hPZ : centerOf P ⊓ Y.Q 1 ≤ Y.Z 1) (hKP : Y.K ≤ Subgroup.normalizer (P : Set G)) :
    ⁅centerOf P ⊓ Y.Q 1, Y.K⁆ ≤ centerOf P ⊓ Y.Zt 1 := by
  refine Subgroup.commutator_le.mpr ?_
  intro a ha k hk
  obtain ⟨haC, haQ⟩ := Subgroup.mem_inf.mp ha
  have hkP : conjSub k P = P := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKP hk)
  have hkC : k * a * k⁻¹ ∈ centerOf P := by
    have h := mul_mem_conjSub (g := k) haC
    rwa [← centerOf_conjSub, hkP] at h
  have hkQ : k * a * k⁻¹ ∈ Y.Q 1 := by
    have hq : conjSub k (Y.Q 1) = Y.Q 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1) (Y.K_le_Gi 1 hk))
    have h := mul_mem_conjSub (g := k) haQ
    rwa [hq] at h
  have hkA : k * a * k⁻¹ ∈ centerOf P ⊓ Y.Q 1 := Subgroup.mem_inf.mpr ⟨hkC, hkQ⟩
  have hmem : ⁅a, k⁆ ∈ centerOf P ⊓ Y.Q 1 := by
    rw [commutatorElement_def]
    have heq : a * k * a⁻¹ * k⁻¹ = a * (k * a⁻¹ * k⁻¹) := by group
    rw [heq]
    have hkA' : k * a⁻¹ * k⁻¹ ∈ centerOf P ⊓ Y.Q 1 := by
      have h := (centerOf P ⊓ Y.Q 1).inv_mem hkA
      rwa [show (k * a * k⁻¹)⁻¹ = k * a⁻¹ * k⁻¹ by group] at h
    exact (centerOf P ⊓ Y.Q 1).mul_mem ha hkA'
  have hmemZt : ⁅a, k⁆ ∈ Y.Zt 1 := by
    have h := Subgroup.commutator_mem_commutator (hPZ ha) hk
    simpa [Setup.Zt] using h
  exact Subgroup.mem_inf.mpr ⟨hmem.1, hmemZt⟩

private theorem Zt_one_le_sup_inf_centerOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 ≠ ⊥)
    {p : V} (hp : Γ.Adj (Y.vert 1) p) (hp0 : p ≠ Y.vert 0) (hp2 : p ≠ Y.vert 2)
    {g : G} (hg : g ∈ Y.Gi 1) (hgp : g • Y.vert 0 = p) :
    Y.Zt 1 ≤ (Y.Zt 0 ⊓ Y.Zt 1) ⊔ (Y.Zt 2 ⊓ Y.Zt 1) ⊔
      (centerOf (conjSub g Y.S) ⊓ Y.Zt 1) := by
  set A : Subgroup G := centerOf Y.S ⊓ Y.Q 1 with hA
  set B : Subgroup G := centerOf (Y.edgeSylow 1) ⊓ Y.Q 1 with hB
  set C : Subgroup G := centerOf (conjSub g Y.S) ⊓ Y.Q 1 with hC
  set W : Subgroup G := (Y.Zt 0 ⊓ Y.Zt 1) ⊔ (Y.Zt 2 ⊓ Y.Zt 1) ⊔
      (centerOf (conjSub g Y.S) ⊓ Y.Zt 1) with hW
  have hSylS : IsSylowTwoOf Y.S (Y.Gi 1) := by
    simpa [Y.edgeSylow_zero] using Y.isSylowTwoOf_edgeSylow_Gi_succ 0
  have hSylB : IsSylowTwoOf (Y.edgeSylow 1) (Y.Gi 1) :=
    Y.isSylowTwoOf_edgeSylow_Gi 1
  have hSylC : IsSylowTwoOf (conjSub g Y.S) (Y.Gi 1) := by
    have h := CFSG.Quasithin.F7.isSylowTwoOf_conj hSylS g
    rwa [conjSub_eq_of_mem hg] at h
  have hAZ : A ≤ Y.Z 1 :=
    le_iSup₂_of_le (f := fun P (_ : IsSylowTwoOf P (Y.Gi 1)) => centerOf P ⊓ Y.Q 1)
      (a := A) Y.S hSylS (by simp [hA])
  have hBZ : B ≤ Y.Z 1 :=
    le_iSup₂_of_le (f := fun P (_ : IsSylowTwoOf P (Y.Gi 1)) => centerOf P ⊓ Y.Q 1)
      (a := B) (Y.edgeSylow 1) hSylB (by simp [hB])
  have hCZ : C ≤ Y.Z 1 :=
    le_iSup₂_of_le (f := fun P (_ : IsSylowTwoOf P (Y.Gi 1)) => centerOf P ⊓ Y.Q 1)
      (a := C) (conjSub g Y.S) hSylC (by simp [hC])
  have hWZ : W ≤ Y.Z 1 := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (inf_le_right : Y.Zt 0 ⊓ Y.Zt 1 ≤ Y.Zt 1).trans (Zt_le_Z Y 1)
    · exact (inf_le_right : Y.Zt 2 ⊓ Y.Zt 1 ≤ Y.Zt 1).trans (Zt_le_Z Y 1)
    · exact (inf_le_right : centerOf (conjSub g Y.S) ⊓ Y.Zt 1 ≤ Y.Zt 1).trans (Zt_le_Z Y 1)
  have hKnS : Y.K ≤ Subgroup.normalizer (Y.S : Set G) := by
    rw [← Y.edgeSylow_zero]
    exact (le_inf (Y.K_le_Gi 0) (Y.K_le_Gi 1)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0 ⊓ Y.Gi 1))
  have hKnB : Y.K ≤ Subgroup.normalizer (Y.edgeSylow 1 : Set G) := by
    exact (le_inf (Y.K_le_Gi 1) (Y.K_le_Gi 2)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1 ⊓ Y.Gi 2))
  have hSconj : conjSub g Y.S = pCoreOf 2 (Y.Gi 1 ⊓ MulAction.stabilizer G p) := by
    rw [← Y.edgeSylow_zero]
    unfold Setup.edgeSylow
    rw [show (0 : ℤ) + 1 = 1 by norm_num, ← pCoreOf_conjSub, conjSub_inf,
      conjSub_eq_of_mem hg, ← stabilizer_smul_eq_conjSub, hgp, inf_comm]
  have hKnC : Y.K ≤ Subgroup.normalizer (conjSub g Y.S : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hSconj]
    change conjSub k (pCoreOf 2 (Y.Gi 1 ⊓ MulAction.stabilizer G p)) =
      pCoreOf 2 (Y.Gi 1 ⊓ MulAction.stabilizer G p)
    have hkp : k • p = p := Y.K_fixes_nbr_one H hp k hk
    have hkG : k ∈ Y.Gi 1 := Y.K_le_Gi 1 hk
    have hconjGi : conjSub k (Y.Gi 1 ⊓ MulAction.stabilizer G p) =
        Y.Gi 1 ⊓ MulAction.stabilizer G p := by
      rw [conjSub_inf, conjSub_eq_of_mem hkG, conjSub_eq_of_mem hkp]
    rw [← pCoreOf_conjSub, hconjGi]
  have hCs : ∀ k ∈ Y.K, conjSub k (centerOf Y.S) = centerOf Y.S := by
    intro k hk
    have h : conjSub k Y.S = Y.S := by
      simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKnS hk)
    rw [← centerOf_conjSub, h]
  have hCb : ∀ k ∈ Y.K, conjSub k (centerOf (Y.edgeSylow 1)) = centerOf (Y.edgeSylow 1) := by
    intro k hk
    have h : conjSub k (Y.edgeSylow 1) = Y.edgeSylow 1 := by
      simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKnB hk)
    rw [← centerOf_conjSub, h]
  have hCc : ∀ k ∈ Y.K, conjSub k (centerOf (conjSub g Y.S)) = centerOf (conjSub g Y.S) := by
    intro k hk
    have h : conjSub k (conjSub g Y.S) = conjSub g Y.S := by
      simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKnC hk)
    rw [← centerOf_conjSub, h]
  have hCq : ∀ k ∈ Y.K, conjSub k (Y.Q 1) = Y.Q 1 := by
    intro k hk
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1) (Y.K_le_Gi 1 hk))
  have hAK : ⁅A, Y.K⁆ ≤ W := by
    refine (commutator_centerOf_inf_Q_one_le Y (P := Y.S) hAZ hKnS).trans ?_
    have hle : centerOf Y.S ⊓ Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 1 := by
      rw [← Zt_one_inf_centralizer_S_eq Y H hZ]
      intro x hx
      exact ⟨hx.2, (Subgroup.mem_inf.mp hx.1).2⟩
    exact hle.trans (le_sup_left.trans le_sup_left)
  have hBK : ⁅B, Y.K⁆ ≤ W := by
    refine (commutator_centerOf_inf_Q_one_le Y (P := Y.edgeSylow 1) hBZ hKnB).trans ?_
    have hle : centerOf (Y.edgeSylow 1) ⊓ Y.Zt 1 ≤ Y.Zt 2 ⊓ Y.Zt 1 := by
      rw [← Zt_two_inf_centralizer_edgeSylow_one_eq Y H hZ]
      intro x hx
      exact ⟨hx.2, (Subgroup.mem_inf.mp hx.1).2⟩
    exact hle.trans (le_sup_right.trans le_sup_left)
  have hCK : ⁅C, Y.K⁆ ≤ W :=
    (commutator_centerOf_inf_Q_one_le Y (P := conjSub g Y.S) hCZ hKnC).trans le_sup_right
  have hcomm : ⁅Y.Z 1, Y.K⁆ ≤ W := by
    have hgen : Y.Z 1 ≤ A ⊔ B ⊔ C := Z_one_le_sup_three Y H hp hp0 hp2 hg hgp
    exact (Subgroup.commutator_mono hgen le_rfl).trans
      (commutator_sup_three_le (Z := Y.Z 1) (A := A) (B := B) (C := C) (K := Y.K) (W := W)
        (Y.Z_commute 1) hAZ hBZ hCZ hWZ hAK hBK hCK)
  simpa [Setup.Zt, hW] using hcomm

private theorem smul_neighbors_one_of_mem_S_of_notMem_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {p : V} (hp : Γ.Adj (Y.vert 1) p) (hp0 : p ≠ Y.vert 0) (hp2 : p ≠ Y.vert 2)
    {s : G} (hs : s ∈ Y.S) (hsQ : s ∉ Y.Q 1) :
    s • Y.vert 0 = Y.vert 0 ∧ s • Y.vert 2 = p ∧ s • p = Y.vert 2 := by
  have hNeigh := Y.neighborSet_one_eq H hp hp0 hp2
  have hne02 : Y.vert 0 ≠ Y.vert 2 := by
    intro h
    have h' := Y.vert_injective h
    norm_num at h'
  have hne2p : Y.vert 2 ≠ p := fun h => hp2 h.symm
  have hsE : s ∈ Y.edgeSylow 0 := by simpa [Y.edgeSylow_zero] using hs
  have hpow := exists_pow_two_of_mem (Y.isPGroup_edgeSylow 0) hsE
  have hs0 : s • Y.vert 0 = Y.vert 0 :=
    MulAction.mem_stabilizer_iff.mp ((Y.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left hsE)
  have hs1 : s ∈ Y.Gi 1 := (Y.isSylowTwoOf_edgeSylow 0).1.trans inf_le_right hsE
  have hinj : Function.Injective (fun v : V => s • v) := fun x y h => by
    simpa using congrArg (fun w => s⁻¹ • w) h
  have hclass : ∀ w : V, Γ.Adj (Y.vert 1) w →
      s • w = Y.vert 0 ∨ s • w = Y.vert 2 ∨ s • w = p := by
    intro w hw
    have hmem : s • w ∈ Γ.neighborSet (Y.vert 1) := by
      rw [SimpleGraph.mem_neighborSet]
      have h1 : Γ.Adj (s • Y.vert 1) (s • w) := (Y.hyp.adj_smul s (Y.vert 1) w).2 hw
      rwa [MulAction.mem_stabilizer_iff.mp hs1] at h1
    rw [hNeigh] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hs2ne : s • Y.vert 2 ≠ Y.vert 2 := by
    intro h2
    exact hsQ (mem_pCoreOf_of_fixes_two Y.hyp hs1 hpow (by simpa using (Y.adj 0).symm)
      (Y.adj 1) hne02 hs0 h2)
  have hs2 : s • Y.vert 2 = p := by
    rcases hclass (Y.vert 2) (Y.adj 1) with h | h | h
    · exact absurd (hinj (h.trans hs0.symm)) hne02.symm
    · exact absurd h hs2ne
    · exact h
  have hspne : s • p ≠ p := fun hp' => hp2 (hinj (hs2.trans hp'.symm)).symm
  have hsp : s • p = Y.vert 2 := by
    rcases hclass p hp with h | h | h
    · exact absurd (hinj (h.trans hs0.symm)) hp0
    · exact h
    · exact absurd h hspne
  exact ⟨hs0, hs2, hsp⟩

private theorem conj_mem_Zt_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {a : G} (haL : a ∈ Y.L 1) {u : G} (hu : u ∈ Y.Zt 1) :
    a * u * a⁻¹ ∈ Y.Zt 1 := by
  have haGi : a ∈ Y.Gi 1 := Y.L_le_Gi 1 haL
  have hZa : conjSub a (Y.Zt 1) = Y.Zt 1 := by
    simpa [conjSub] using
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Gi_one_le_normalizer_Zt_one Y H haGi)
  rw [← hZa, mem_conjSub]
  have h : a⁻¹ * (a * u * a⁻¹) * a = u := by group
  rwa [h]

private theorem conj_mem_Zt_two_inf_Zt_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) {a : G} (haL : a ∈ Y.L 1) (ha0 : a • Y.vert 0 = Y.vert 2)
    {u : G} (hu : u ∈ Y.Zt 0 ⊓ Y.Zt 1) :
    a * u * a⁻¹ ∈ Y.Zt 2 ⊓ Y.Zt 1 := by
  have hW0eq := Zt_one_inf_centralizer_S_eq Y H hZ
  have hW2eq := Zt_two_inf_centralizer_edgeSylow_one_eq Y H hZ
  have huZt1 : u ∈ Y.Zt 1 := hu.2
  have huC : u ∈ Subgroup.centralizer (Y.S : Set G) := by
    have h : u ∈ Y.Zt 1 ⊓ Subgroup.centralizer (Y.S : Set G) := by
      rw [hW0eq]; exact hu
    exact h.2
  have hxZt1 : a * u * a⁻¹ ∈ Y.Zt 1 := conj_mem_Zt_one Y H haL huZt1
  have haGi : a ∈ Y.Gi 1 := Y.L_le_Gi 1 haL
  have hGi0a : conjSub a (Y.Gi 0) = Y.Gi 2 := by
    rw [← stabilizer_smul_eq_conjSub, ha0]
  have hGi1a : conjSub a (Y.Gi 1) = Y.Gi 1 := by
    rw [← stabilizer_smul_eq_conjSub, MulAction.mem_stabilizer_iff.mp haGi]
  have hSa : conjSub a (Y.S) = Y.edgeSylow 1 := by
    unfold Setup.S Setup.edgeSylow
    rw [← pCoreOf_conjSub, conjSub_inf, hGi0a, hGi1a]
    rw [show (1 : ℤ) + 1 = 2 by norm_num, inf_comm]
  have hxC : a * u * a⁻¹ ∈ Subgroup.centralizer (Y.edgeSylow 1 : Set G) := by
    rw [← hSa, conjSub_centralizer, mem_conjSub]
    have h : a⁻¹ * (a * u * a⁻¹) * a = u := by group
    rwa [h]
  rw [← hW2eq]
  exact Subgroup.mem_inf.mpr ⟨hxZt1, hxC⟩

private theorem conj_conj_eq_of_smul_vert_zero_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {s a b u : G} (hs : s ∈ Y.L 1) (ha : a ∈ Y.L 1) (hb : b ∈ Y.L 1)
    (hab : (s * a) • Y.vert 0 = b • Y.vert 0)
    (hu : u ∈ Subgroup.centralizer (Y.S : Set G)) :
    s * (a * u * a⁻¹) * s⁻¹ = b * u * b⁻¹ := by
  have hc : (s * a)⁻¹ * b ∈ Y.S := by
    have hcL : (s * a)⁻¹ * b ∈ Y.L 1 :=
      (Y.L 1).mul_mem ((Y.L 1).inv_mem ((Y.L 1).mul_mem hs ha)) hb
    have hc0 : ((s * a)⁻¹ * b) • Y.vert 0 = Y.vert 0 := by
      rw [mul_smul, ← hab, inv_smul_smul]
    exact Y.L_one_inf_Gi_zero_le_S H
      (Subgroup.mem_inf.mpr ⟨hcL, MulAction.mem_stabilizer_iff.mpr hc0⟩)
  have hcu : ((s * a)⁻¹ * b) * u * ((s * a)⁻¹ * b)⁻¹ = u := by
    have hcomm : ((s * a)⁻¹ * b) * u = u * ((s * a)⁻¹ * b) :=
      Subgroup.mem_centralizer_iff.mp hu _ hc
    rw [hcomm]; group
  calc s * (a * u * a⁻¹) * s⁻¹
      = (s * a) * u * (s * a)⁻¹ := by group
    _ = (s * a) * (((s * a)⁻¹ * b) * u * ((s * a)⁻¹ * b)⁻¹) *
          (s * a)⁻¹ := by rw [hcu]
    _ = (s * a * ((s * a)⁻¹ * b)) * u *
          (s * a * ((s * a)⁻¹ * b))⁻¹ := by group
    _ = b * u * b⁻¹ := by
          conv_rhs => rw [show b = s * a * ((s * a)⁻¹ * b) by group]

private theorem S_fixes_prod_conj (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) {p : V} (hp : Γ.Adj (Y.vert 1) p)
    (hp0 : p ≠ Y.vert 0) (hp2 : p ≠ Y.vert 2)
    {a b : G} (haL : a ∈ Y.L 1) (ha0 : a • Y.vert 0 = Y.vert 2)
    (hbL : b ∈ Y.L 1) (hb0 : b • Y.vert 0 = p)
    {u x y : G} (hu : u ∈ Y.Zt 0 ⊓ Y.Zt 1)
    (hx : x = a * u * a⁻¹) (hy : y = b * u * b⁻¹)
    {s : G} (hs : s ∈ Y.S) :
    s * (u * x * y) * s⁻¹ = u * x * y := by
  have hW0eq := Zt_one_inf_centralizer_S_eq Y H hZ
  have huZt1 : u ∈ Y.Zt 1 := hu.2
  have huC : u ∈ Subgroup.centralizer (Y.S : Set G) := by
    have h : u ∈ Y.Zt 1 ⊓ Subgroup.centralizer (Y.S : Set G) := by
      rw [hW0eq]; exact hu
    exact h.2
  have hxZt1 : x ∈ Y.Zt 1 := by rw [hx]; exact conj_mem_Zt_one Y H haL huZt1
  have hyZt1 : y ∈ Y.Zt 1 := by rw [hy]; exact conj_mem_Zt_one Y H hbL huZt1
  by_cases hsQ : s ∈ Y.Q 1
  · have hcent : ∀ v ∈ Y.Zt 1, s * v * s⁻¹ = v := by
      intro v hv
      have hcomm : s * v = v * s :=
        Subgroup.mem_centralizer_iff.mp
          (Subgroup.mem_inf.mp (Y.Z_le_center 1 (Zt_le_Z Y 1 hv))).2 s hsQ
      rw [hcomm]; group
    calc s * (u * x * y) * s⁻¹
        = (s * u * s⁻¹) * (s * x * s⁻¹) * (s * y * s⁻¹) := by group
      _ = u * x * y := by rw [hcent u huZt1, hcent x hxZt1, hcent y hyZt1]
  · obtain ⟨hs0, hs2, hsp⟩ := smul_neighbors_one_of_mem_S_of_notMem_Q Y H hp hp0 hp2 hs hsQ
    have hsL1 : s ∈ Y.L 1 :=
      le_oTwoPrime_of_isPGroup (Y.isPGroup_edgeSylow 0)
        ((Y.isSylowTwoOf_edgeSylow 0).1.trans inf_le_right)
        (by simpa [Y.edgeSylow_zero] using hs)
    have hsu : s * u * s⁻¹ = u := by
      have hcomm : s * u = u * s := Subgroup.mem_centralizer_iff.mp huC s hs
      rw [hcomm]; group
    have hxsy : s * x * s⁻¹ = y := by
      rw [hx, hy]
      exact conj_conj_eq_of_smul_vert_zero_eq Y H hsL1 haL hbL
        (by rw [mul_smul, ha0, hs2, hb0]) huC
    have hysx : s * y * s⁻¹ = x := by
      rw [hx, hy]
      exact conj_conj_eq_of_smul_vert_zero_eq Y H hsL1 hbL haL
        (by rw [mul_smul, hb0, hsp, ha0]) huC
    have hxy : x * y = y * x :=
      Z_commute Y 1 x (Zt_le_Z Y 1 hxZt1) y (Zt_le_Z Y 1 hyZt1)
    calc s * (u * x * y) * s⁻¹
        = (s * u * s⁻¹) * (s * x * s⁻¹) * (s * y * s⁻¹) := by group
      _ = u * y * x := by rw [hsu, hxsy, hysx]
      _ = u * x * y := by
            rw [show u * y * x = u * (y * x) by group, ← hxy]
            group

private theorem conjSub_Zt_zero_inf_Zt_one_le_sup (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) {p : V} (hp : Γ.Adj (Y.vert 1) p) (hp0 : p ≠ Y.vert 0)
    (hp2 : p ≠ Y.vert 2)
    {a b : G} (haL : a ∈ Y.L 1) (ha0 : a • Y.vert 0 = Y.vert 2)
    (hbL : b ∈ Y.L 1) (hb0 : b • Y.vert 0 = p) :
    conjSub b (Y.Zt 0 ⊓ Y.Zt 1) ≤ (Y.Zt 0 ⊓ Y.Zt 1) ⊔ (Y.Zt 2 ⊓ Y.Zt 1) := by
  intro z hz
  rw [mem_conjSub] at hz
  set u : G := b⁻¹ * z * b with hu
  have huW0 : u ∈ Y.Zt 0 ⊓ Y.Zt 1 := by rw [hu]; exact hz
  have hz_eq : z = b * u * b⁻¹ := by rw [hu]; group
  rw [hz_eq]
  set x : G := a * u * a⁻¹ with hx
  set y : G := b * u * b⁻¹ with hy
  set σ : G := u * x * y with hσ
  have hfixS : ∀ s ∈ Y.S, s * σ * s⁻¹ = σ := by
    intro s hs
    have := S_fixes_prod_conj Y H hZ hp hp0 hp2 haL ha0 hbL hb0 huW0 hx hy hs
    simpa [hσ] using this
  have hσC_S : σ ∈ Subgroup.centralizer (Y.S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    calc s * σ = (s * σ * s⁻¹) * s := by group
      _ = σ * s := by rw [hfixS s hs]
  have huZt1 : u ∈ Y.Zt 1 := huW0.2
  have hxW2 : x ∈ Y.Zt 2 ⊓ Y.Zt 1 := by
    rw [hx]; exact conj_mem_Zt_two_inf_Zt_one Y H hZ haL ha0 huW0
  have hxZt1 : x ∈ Y.Zt 1 := hxW2.2
  have hyZt1 : y ∈ Y.Zt 1 := by
    rw [hy]; exact conj_mem_Zt_one Y H hbL huZt1
  have hσZt1 : σ ∈ Y.Zt 1 := by
    rw [hσ]
    exact (Y.Zt 1).mul_mem ((Y.Zt 1).mul_mem huZt1 hxZt1) hyZt1
  have hσW0 : σ ∈ Y.Zt 0 ⊓ Y.Zt 1 := by
    rw [← Zt_one_inf_centralizer_S_eq Y H hZ]
    exact Subgroup.mem_inf.mpr ⟨hσZt1, hσC_S⟩
  have hux : u * x = x * u :=
    Z_commute Y 1 u (Zt_le_Z Y 1 huZt1) x (Zt_le_Z Y 1 hxZt1)
  have hinv : x⁻¹ * u⁻¹ = u⁻¹ * x⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hux]
  have hy_eq : y = u⁻¹ * x⁻¹ * σ := by
    rw [hσ]
    calc y = (u * x)⁻¹ * (u * x * y) := by group
      _ = u⁻¹ * x⁻¹ * (u * x * y) := by rw [mul_inv_rev, hinv]
  rw [hy_eq]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.inv_mem _ huW0))
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ hxW2)))
    (Subgroup.mem_sup_left hσW0)

private theorem Zt_one_le_center_of_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hVZ0 : Y.Zt 1 ≤ Y.Zt 0) (hVZ2 : Y.Zt 1 ≤ Y.Zt 2) :
    Y.Zt 1 ≤ centerOf (Y.L 1) := by
  have hZ1 : Y.Zt 1 ≤ Y.Z 1 := Zt_le_Z Y 1
  have hZ0 : Y.Zt 1 ≤ Y.Z 0 := hVZ0.trans (Zt_le_Z Y 0)
  have hZ2 : Y.Zt 1 ≤ Y.Z 2 := hVZ2.trans (Zt_le_Z Y 2)
  have hQ0c : Y.Zt 1 ≤ Subgroup.centralizer (Y.Q 0 : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (Y.Z_le_center 0 (hZ0 hv))).2 q hq
  have hQ1c : Y.Zt 1 ≤ Subgroup.centralizer (Y.Q 1 : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (Y.Z_le_center 1 (hZ1 hv))).2 q hq
  have hQ2c : Y.Zt 1 ≤ Subgroup.centralizer (Y.Q 2 : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (Y.Z_le_center 2 (hZ2 hv))).2 q hq
  have hSc : Y.Zt 1 ≤ Subgroup.centralizer (Y.S : Set G) := by
    have hSeq : Y.S = Y.Q 0 ⊔ Y.Q 1 := (Y.sup_Q_eq_edgeSylow H.char 0).symm
    rw [hSeq]
    exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hQ0c hQ1c
  have hS2c : Y.Zt 1 ≤ Subgroup.centralizer (Y.edgeSylow 1 : Set G) := by
    have hS2eq : Y.edgeSylow 1 = Y.Q 1 ⊔ Y.Q 2 := (Y.sup_Q_eq_edgeSylow H.char 1).symm
    rw [hS2eq]
    exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hQ1c hQ2c
  have hLsup : Y.S ⊔ Y.edgeSylow 1 = Y.L 1 := by
    rw [← Y.edgeSylow_zero]
    exact Y.edgeSylow_sup_edgeSylow 1
  have hLc : Y.Zt 1 ≤ Subgroup.centralizer (Y.L 1 : Set G) := by
    rw [← hLsup]
    exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hSc hS2c
  exact le_inf (hZ1.trans ((Y.Z_le_Q 1).trans
    ((Y.Q_le_edgeSylow_left 1).trans (Y.edgeSylow_le_L 1)))) hLc

private theorem Zt_one_le_sup_inf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 ≠ ⊥) :
    Y.Zt 1 ≤ (Y.Zt 0 ⊓ Y.Zt 1) ⊔ (Y.Zt 2 ⊓ Y.Zt 1) := by
  have hcardN : Nat.card (Γ.neighborSet (Y.vert 1)) = 3 := by
    rw [(Y.hyp.valency (Y.vert 1)).2]
    change 2 ^ Y.n 1 + 1 = 3
    rw [H.n_one]
    norm_num
  have hcard1 : 3 ≤ Nat.card (Γ.neighborSet (Y.vert 1)) := by omega
  obtain ⟨p, hp, hp0, hp2⟩ :=
    exists_adj_ne_ne (Γ := Γ) (v := Y.vert 1) (a := Y.vert 0) (b := Y.vert 2) hcard1
  let hL : IsLocL2 Γ G (Y.vert 1) (Y.n 1) (Y.L 1) := Y.hyp.isLocL2_oTwoPrime (Y.vert 1)
  obtain ⟨b, hbL, hb0⟩ := hL.trans (Y.vert 0) p
    (by simpa using (Y.adj 0).symm) hp
  obtain ⟨a, haL, ha0⟩ := hL.trans (Y.vert 0) (Y.vert 2)
    (by simpa using (Y.adj 0).symm) (Y.adj 1)
  have hbG1 : b ∈ Y.Gi 1 := Y.L_le_Gi 1 hbL
  set W0 : Subgroup G := Y.Zt 0 ⊓ Y.Zt 1 with hW0def
  set W2 : Subgroup G := Y.Zt 2 ⊓ Y.Zt 1 with hW2def
  set Wp : Subgroup G := centerOf (conjSub b Y.S) ⊓ Y.Zt 1 with hWpdef
  have hgen : Y.Zt 1 ≤ W0 ⊔ W2 ⊔ Wp := by
    simpa [hW0def, hW2def, hWpdef] using Zt_one_le_sup_inf_centerOf Y H hZ hp hp0 hp2 hbG1 hb0
  have hWp_eq : Wp = conjSub b W0 := by
    have hZt1n : conjSub b (Y.Zt 1) = Y.Zt 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Gi_one_le_normalizer_Zt_one Y H hbG1)
    have hZt1S : Y.Zt 1 ≤ Y.S := by
      rw [← Y.edgeSylow_zero]
      exact (Zt_le_Z Y 1).trans ((Y.Z_le_Q 1).trans
        (by simpa [Y.edgeSylow_zero] using Y.Q_le_edgeSylow_right 1))
    have hcenter : centerOf Y.S ⊓ Y.Zt 1 =
        Subgroup.centralizer (Y.S : Set G) ⊓ Y.Zt 1 := by
      ext x
      constructor
      · rintro ⟨⟨-, hxC⟩, hxZt⟩
        exact ⟨hxC, hxZt⟩
      · rintro ⟨hxC, hxZt⟩
        exact ⟨⟨hZt1S hxZt, hxC⟩, hxZt⟩
    rw [hWpdef]
    calc centerOf (conjSub b Y.S) ⊓ Y.Zt 1
        = conjSub b (centerOf Y.S) ⊓ Y.Zt 1 := by rw [centerOf_conjSub]
      _ = conjSub b (centerOf Y.S ⊓ Y.Zt 1) := by rw [conjSub_inf, hZt1n]
      _ = conjSub b (Subgroup.centralizer (Y.S : Set G) ⊓ Y.Zt 1) := by rw [hcenter]
      _ = conjSub b (Y.Zt 1 ⊓ Subgroup.centralizer (Y.S : Set G)) := by rw [inf_comm]
      _ = conjSub b (Y.Zt 0 ⊓ Y.Zt 1) := by rw [Zt_one_inf_centralizer_S_eq Y H hZ]
      _ = conjSub b W0 := by rw [hW0def]
  have hML : conjSub b W0 ≤ W0 ⊔ W2 := by
    simpa [hW0def, hW2def] using
      conjSub_Zt_zero_inf_Zt_one_le_sup Y H hZ hp hp0 hp2 haL ha0 hbL hb0
  refine hgen.trans ?_
  rw [hWp_eq]
  exact sup_le le_rfl hML

private theorem Zt_one_le_arcStab_of_le_sup (Y : Setup Γ G) {r₀ : ℕ} (he : Y.ZtExt 0 r₀ r₀)
    (hr01 : 1 ≤ r₀) (hsup : Y.Zt 1 ≤ (Y.Zt 0 ⊓ Y.Zt 1) ⊔ (Y.Zt 2 ⊓ Y.Zt 1)) :
    Y.Zt 1 ≤ Y.arcStab (2 - (r₀ : ℤ)) (r₀ : ℤ) := by
  set W0 : Subgroup G := Y.Zt 0 ⊓ Y.Zt 1 with hW0def
  set W2 : Subgroup G := Y.Zt 2 ⊓ Y.Zt 1 with hW2def
  have hW0fix : W0 ≤ Y.arcStab (2 - (r₀ : ℤ)) (r₀ : ℤ) := by
    rw [Y.arcStab_eq_inf (by omega)]
    refine le_inf ?_ ?_
    · refine (hW0def ▸ inf_le_left).trans ?_
      have h := he.1 (2 - (r₀ : ℤ)) (by omega) (by omega)
      simpa using h
    · refine (hW0def ▸ inf_le_left).trans ?_
      have h := he.1 (r₀ : ℤ) (by omega) le_rfl
      simpa using h
  have hW2fix : W2 ≤ Y.arcStab (2 - (r₀ : ℤ)) (r₀ : ℤ) := by
    rw [Y.arcStab_eq_inf (by omega)]
    refine le_inf ?_ ?_
    · refine (hW2def ▸ inf_le_left).trans ?_
      have h := he.Zt_two_mul_le_Gi 1 (2 - (r₀ : ℤ) - 2) (by omega) (by omega)
      rwa [show 2 * (1 : ℤ) + (2 - (r₀ : ℤ) - 2) = 2 - (r₀ : ℤ) by ring] at h
    · refine (hW2def ▸ inf_le_left).trans ?_
      have h := he.Zt_two_mul_le_Gi 1 ((r₀ : ℤ) - 2) (by omega) (by omega)
      rwa [show 2 * (1 : ℤ) + ((r₀ : ℤ) - 2) = (r₀ : ℤ) by ring] at h
  exact hsup.trans (sup_le hW0fix hW2fix)

private theorem Zt_one_le_arcStab_of_ZtExt_one (Y : Setup Γ G) {r₀ l rr : ℕ}
    (hU : Y.ZtExt 1 l rr) (hlge : r₀ + 1 ≤ l) (hrge : r₀ + 1 ≤ rr) :
    Y.Zt 1 ≤ Y.arcStab (-(r₀ : ℤ)) ((r₀ : ℤ) + 2) := by
  rw [Y.arcStab_eq_inf (by omega)]
  refine le_inf ?_ ?_
  · have hleft : -(l : ℤ) ≤ -(r₀ : ℤ) - 1 := by
      have : (r₀ : ℤ) + 1 ≤ (l : ℤ) := by exact_mod_cast hlge
      omega
    have hright : -(r₀ : ℤ) - 1 ≤ (rr : ℤ) := by
      have : (0 : ℤ) ≤ (rr : ℤ) := by positivity
      omega
    have h := hU.1 (-(r₀ : ℤ) - 1) hleft hright
    have h1 : (1 : ℤ) + (-(r₀ : ℤ) - 1) = -(r₀ : ℤ) := by ring
    simpa [h1] using h
  · have hleft : -(l : ℤ) ≤ (r₀ : ℤ) + 1 := by
      have : (0 : ℤ) ≤ (r₀ : ℤ) := by positivity
      omega
    have hright : (r₀ : ℤ) + 1 ≤ (rr : ℤ) := by exact_mod_cast hrge
    have h := hU.1 ((r₀ : ℤ) + 1) hleft hright
    simpa [show (1 : ℤ) + ((r₀ : ℤ) + 1) = (r₀ : ℤ) + 2 by ring] using h

private theorem Zt_zero_inf_Zt_one_eq_bot_or_eq (Y : Setup Γ G)
    (hKtrans : ∀ x ∈ Y.Zt 1, x ≠ 1 → ∀ y ∈ Y.Zt 1, y ≠ 1 → ∃ k ∈ Y.K, k * x * k⁻¹ = y) :
    Y.Zt 0 ⊓ Y.Zt 1 = ⊥ ∨ Y.Zt 0 ⊓ Y.Zt 1 = Y.Zt 1 := by
  set W0 : Subgroup G := Y.Zt 0 ⊓ Y.Zt 1 with hW0def
  have hKnZ0 : Y.K ≤ Subgroup.normalizer (Y.Zt 0 : Set G) := K_le_normalizer_Zt Y 0
  have hKnZ1 : Y.K ≤ Subgroup.normalizer (Y.Zt 1 : Set G) := K_le_normalizer_Zt Y 1
  have hKnW0 : Y.K ≤ Subgroup.normalizer (W0 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h0 : conjSub k (Y.Zt 0) = Y.Zt 0 := by
      simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKnZ0 hk)
    have h1 : conjSub k (Y.Zt 1) = Y.Zt 1 := by
      simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKnZ1 hk)
    change conjSub k (Y.Zt 0 ⊓ Y.Zt 1) = Y.Zt 0 ⊓ Y.Zt 1
    rw [conjSub_inf, h0, h1]
  have hcases : W0 = ⊥ ∨ W0 = Y.Zt 1 := by
    by_cases hbot : W0 = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨u, huW0, hu1⟩ := (Subgroup.bot_or_exists_ne_one W0).resolve_left hbot
      have huV : u ∈ Y.Zt 1 := (hW0def ▸ inf_le_right) huW0
      refine le_antisymm (hW0def ▸ inf_le_right) ?_
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1]; exact W0.one_mem
      · obtain ⟨k, hkK, hkuv⟩ := hKtrans u huV hu1 v hv hv1
        have hkuW0 : k * u * k⁻¹ ∈ W0 := by
          have hmap : conjSub k W0 = W0 := by
            simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKnW0 hkK)
          have := mul_mem_conjSub (g := k) huW0
          rwa [hmap] at this
        rwa [hkuv] at hkuW0
  exact hcases

theorem s52_step3 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (hr : Y.IsMaxRegLen r)
    (he : Y.ZtExt 0 r₀ r₀) (h2 : Y.Step2Conclusion s r r₀) : Y.Zt 1 = ⊥ := by
  by_contra hne
  have hr01 : 1 ≤ r₀ := by
    rcases Nat.eq_zero_or_pos r₀ with h0 | hpos
    · exfalso
      apply he.2.1
      rw [h0]
      have hZtQ : Y.Zt 0 ≤ Y.Q 0 := (Zt_le_Z Y 0).trans (Y.Z_le_Q 0)
      refine hZtQ.trans (fun q hq => MulAction.mem_stabilizer_iff.mpr ?_)
      exact Y.Q_fixes_neighbors_vert 0 (Y.vert 1) (Y.adj 0) q hq
    · exact hpos
  set W0 : Subgroup G := Y.Zt 0 ⊓ Y.Zt 1 with hW0def
  set W2 : Subgroup G := Y.Zt 2 ⊓ Y.Zt 1 with hW2def
  have hsup : Y.Zt 1 ≤ W0 ⊔ W2 := by
    simpa [hW0def, hW2def] using Zt_one_le_sup_inf Y H hZ
  obtain ⟨aN, haNmem, haN0⟩ := Y.exists_normalizer_K_one H (a := Y.vert 0) (b := Y.vert 2)
    (by simpa using (Y.adj 0).symm) (Y.adj 1)
  obtain ⟨haN, haNG1⟩ := Subgroup.mem_inf.mp haNmem
  have hfixint := Zt_one_le_arcStab_of_le_sup Y he hr01 hsup
  obtain ⟨l, rr, hl1, hr1, hU⟩ := exists_ZtExt Y H hne
  obtain ⟨hlge, hrge⟩ := ZtExt_one_ge Y H hZ he hU hfixint
  have hfixδ := Zt_one_le_arcStab_of_ZtExt_one Y hU hlge hrge
  have hbound : 2 * r₀ + 2 ≤ r :=
    two_mul_add_two_of_Zt_one_le_arcStab Y H hr hne hfixδ
  have hrEq : r = 2 * r₀ + 2 := by
    rcases h2 with h2a | ⟨h2b, -, -⟩ | ⟨h2c, -, h2r0, -, -, -, -, -⟩
    · omega
    · omega
    · omega
  have hmax : Y.arcStab (-(r₀ : ℤ)) ((r₀ : ℤ) + 3) = Y.GT := by
    have h := hr.2 (-(r₀ : ℤ)) (r + 1) (by omega)
    have harg : (-(r₀ : ℤ)) + ((r + 1 : ℕ) : ℤ) = (r₀ : ℤ) + 3 := by
      push_cast [hrEq]
      ring
    rwa [harg] at h
  have hKtrans := K_transitive_on_Zt_one Y H hfixδ hmax
  have hcases : W0 = ⊥ ∨ W0 = Y.Zt 1 := by
    simpa [hW0def] using Zt_zero_inf_Zt_one_eq_bot_or_eq Y hKtrans
  have hZt2n : conjSub aN (Y.Zt 0) = Y.Zt 2 := conjSub_Zt_zero_eq_Zt_two Y haN haN0
  have hZt1nN : conjSub aN (Y.Zt 1) = Y.Zt 1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Gi_one_le_normalizer_Zt_one Y H haNG1)
  have hconjW0 : conjSub aN W0 = W2 := by
    rw [hW0def, hW2def, conjSub_inf, hZt2n, hZt1nN]
  rcases hcases with h0 | hV
  ·
    have hW2bot : W2 = ⊥ := by
      rw [← hconjW0, h0]
      simpa [conjSub]
    have : Y.Zt 1 ≤ ⊥ := by simpa [h0, hW2bot] using hsup
    exact hne (le_antisymm this bot_le)
  ·
    have hVZ0 : Y.Zt 1 ≤ Y.Zt 0 := by
      rw [← hV]
      exact hW0def ▸ inf_le_left
    have hW2eq : W2 = Y.Zt 1 := by
      rw [← hconjW0, hV]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Gi_one_le_normalizer_Zt_one Y H haNG1)
    have hVZ2 : Y.Zt 1 ≤ Y.Zt 2 := by
      rw [← hW2eq]
      exact hW2def ▸ inf_le_left
    have hW : Y.Zt 1 ≤ Y.Zt 0 ⊓ Y.Zt 2 := le_inf hVZ0 hVZ2
    exact hne (Zt_one_eq_bot_of_le_center Y H hZ
      (Zt_one_le_center_of_le Y H hVZ0 hVZ2))

end Setup
end CFSG.Quasithin.St84
