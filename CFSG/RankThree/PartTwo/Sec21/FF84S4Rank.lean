module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankP1
public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankP2
public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankQ
public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankQnc
public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankDec
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
public import CFSG.RankThree.PartTwo.Sec21.FF84S411TransvStmt

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)
open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

@[expose] def SylP1 : Subgroup P8 := tabSub rankP1 P1_mul P1_one P1_inv
@[expose] def SylP2 : Subgroup P8 := tabSub rankP2 P2_mul P2_one P2_inv
@[expose] def Qsub : Subgroup P8 := tabSub rankQ Q_mul Q_one Q_inv

theorem P1_card : Nat.card SylP1 = 64 := by
  rw [SylP1, natCard_tabSub _ _ _ _ P1_nodup]
  rfl
theorem P2_card : Nat.card SylP2 = 64 := by
  rw [SylP2, natCard_tabSub _ _ _ _ P2_nodup]
  rfl
theorem Qsub_card : Nat.card Qsub = 32 := by
  rw [Qsub, natCard_tabSub _ _ _ _ Q_nodup]
  rfl

theorem P1_le : SylP1 ≤ Subgroup.centralizer ({rep4} : Set P8) ⊓ A8s := by
  intro g hg
  have hg' : FF84.tab g ∈ rankP1.map FF84.tab := hg
  obtain ⟨c, hc, hceq⟩ := List.mem_map.1 hg'
  have hcg : c = g := FF84.tab_inj hceq
  rw [← hcg]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply FF84.tab_inj
    rw [FF84.tab_mul, FF84.tab_mul]
    exact P1_comm c hc
  · exact mem_alternatingGroup.2 (P1_sign c hc)

theorem P2_le : SylP2 ≤ Subgroup.centralizer ({rep4} : Set P8) ⊓ A8s := by
  intro g hg
  have hg' : FF84.tab g ∈ rankP2.map FF84.tab := hg
  obtain ⟨c, hc, hceq⟩ := List.mem_map.1 hg'
  have hcg : c = g := FF84.tab_inj hceq
  rw [← hcg]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply FF84.tab_inj
    rw [FF84.tab_mul, FF84.tab_mul]
    exact P2_comm c hc
  · exact mem_alternatingGroup.2 (P2_sign c hc)

theorem mem_Qsub_of_P12 {b : P8} (h1 : b ∈ SylP1) (h2 : b ∈ SylP2) : b ∈ Qsub := by
  have h1' : FF84.tab b ∈ rankP1.map FF84.tab := h1
  have h2' : FF84.tab b ∈ rankP2.map FF84.tab := h2
  show FF84.tab b ∈ rankQ.map FF84.tab
  obtain ⟨c, hc, hceq⟩ := List.mem_map.1 h1'
  rw [← hceq] at h2' ⊢
  exact Q_of_P12 c hc h2'

theorem comm_of_EA {B : Subgroup P8} [IsElementaryAbelian 2 B] {x y : P8} (hx : x ∈ B)
    (hy : y ∈ B) : x * y = y * x := by
  have h : ∀ a b : B, a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  exact congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩)

theorem natCard_cenQ (a : P8) : Nat.card ↥(Subgroup.centralizer ({a} : Set P8) ⊓ Qsub) =
    (rankQ.filter (fun d => decide (FF84.comp (FF84.tab d) (FF84.tab a) =
      FF84.comp (FF84.tab a) (FF84.tab d)))).length := by
  have hnd : rankQ.Nodup := List.Nodup.of_map _ Q_nodup
  have key : ∀ g : P8, g ∈ Subgroup.centralizer ({a} : Set P8) ⊓ Qsub ↔ g ∈ (rankQ.filter (fun d => decide
      (FF84.comp (FF84.tab d) (FF84.tab a) = FF84.comp (FF84.tab a) (FF84.tab d)))).toFinset := by
    intro g
    rw [List.mem_toFinset, List.mem_filter, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hc, hq⟩
      exact ⟨(mem_tab_iff rankQ g).1 hq, decide_eq_true ((tab_mul_eq_iff g a).1 hc)⟩
    · rintro ⟨hq, hdec⟩
      exact ⟨(tab_mul_eq_iff g a).2 (of_decide_eq_true hdec), (mem_tab_iff rankQ g).2 hq⟩
  rw [natCard_of_iff_finset' _ _ key, List.toFinset_card_of_nodup (hnd.filter _)]

theorem EA16_false (B : Subgroup P8) (hB : B ≤ Qsub) [IsElementaryAbelian 2 B]
    (h : Nat.card B = 16) : False := by
  by_cases hcen : ∀ a ∈ B, ∀ g ∈ Qsub, a * g = g * a
  ·
    have hsub : B ≤ Subgroup.zpowers rep4 := by
      intro a ha
      have haQ : FF84.tab a ∈ rankQ.map FF84.tab := hB ha
      have hcen' : ∀ y ∈ rankQ.map FF84.tab, FF84.comp (FF84.tab a) y = FF84.comp y (FF84.tab a) := by
        intro y hy
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
        have hdQ : FF84.tab d ∈ rankQ.map FF84.tab := (mem_tab_iff rankQ d).2 hd
        exact (tab_mul_eq_iff a d).1 (hcen a ha d hdQ)
      rcases Q_center (FF84.tab a) haQ hcen' with h1 | h1
      · have ha1 : a = 1 := FF84.tab_inj h1
        rw [ha1]
        exact one_mem _
      · have har : a = rep4 := FF84.tab_inj h1
        rw [har]
        exact Subgroup.mem_zpowers rep4
    have h2 := Subgroup.card_le_of_le hsub
    rw [Nat.card_zpowers] at h2
    have h4 : rep4 ^ 2 = 1 := by decide +kernel
    have hord : orderOf rep4 ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h4)
    omega
  ·
    push_neg at hcen
    obtain ⟨a, ha, g, hgQ, hag⟩ := hcen
    have haQ : FF84.tab a ∈ rankQ.map FF84.tab := hB ha
    obtain ⟨c, hc, hca⟩ := List.mem_map.1 haQ
    obtain ⟨d, hd, hdg⟩ := List.mem_map.1 hgQ
    have hnc : ∃ d' ∈ rankQ, FF84.comp (FF84.tab c) (FF84.tab d') ≠
        FF84.comp (FF84.tab d') (FF84.tab c) := by
      refine ⟨d, hd, ?_⟩
      rw [hca, hdg]
      intro hh
      apply hag
      exact (tab_mul_eq_iff a g).2 hh
    obtain ⟨hlen, y, hy, w, hw, hyc, hwc, hyw⟩ := Q_noncentral c hc hnc
    rw [hca] at hlen hyc hwc
    have hcard : Nat.card ↥(Subgroup.centralizer ({a} : Set P8) ⊓ Qsub) = 16 := by
      rw [natCard_cenQ a]
      exact hlen
    have hBC : B ≤ Subgroup.centralizer ({a} : Set P8) ⊓ Qsub := by
      intro b hb
      refine Subgroup.mem_inf.2 ⟨?_, hB hb⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact comm_of_EA hb ha
    have hBeq : B = Subgroup.centralizer ({a} : Set P8) ⊓ Qsub :=
      Subgroup.eq_of_le_of_card_ge hBC (by omega)
    have hyB : y ∈ B := by
      rw [hBeq]
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
        ((tab_mul_eq_iff y a).2 hyc), (mem_tab_iff rankQ y).2 hy⟩
    have hwB : w ∈ B := by
      rw [hBeq]
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
        ((tab_mul_eq_iff w a).2 hwc), (mem_tab_iff rankQ w).2 hw⟩
    apply hyw
    rw [← FF84.tab_mul, ← FF84.tab_mul, comm_of_EA hyB hwB]

theorem EA32_false (B : Subgroup P8) (hB : B ≤ Qsub) [IsElementaryAbelian 2 B]
    (h : Nat.card B = 32) : False := by
  have hQc := Qsub_card
  have hBQ : B = Qsub := Subgroup.eq_of_le_of_card_ge hB (by omega)
  obtain ⟨c, hc, d, hd, hne⟩ := Q_nonab
  have hcB : c ∈ B := by
    rw [hBQ]
    exact (mem_tab_iff rankQ c).2 hc
  have hdB : d ∈ B := by
    rw [hBQ]
    exact (mem_tab_iff rankQ d).2 hd
  apply hne
  rw [← FF84.tab_mul, ← FF84.tab_mul, comm_of_EA hcB hdB]

theorem EA_Q (B : Subgroup P8) (hB : B ≤ Qsub) [IsElementaryAbelian 2 B] :
    Nat.card B ≤ 8 := by
  by_contra hcon
  push_neg at hcon
  have hdvd : Nat.card B ∣ 2 ^ 5 := by
    have h1 := Subgroup.card_dvd_of_le hB
    rw [Qsub_card] at h1
    norm_num
    exact h1
  have hdvd32 : Nat.card B ∣ 32 := by
    norm_num at hdvd
    exact hdvd
  have key : ∀ k ≤ 32, 8 < k → k ∣ 32 → k = 16 ∨ k = 32 := by decide
  have hle : Nat.card B ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd32
  have h16 : Nat.card B = 16 ∨ Nat.card B = 32 := key (Nat.card B) hle hcon hdvd32
  rcases h16 with h16 | h32
  · exact EA16_false B hB h16
  · exact EA32_false B hB h32

theorem bound_of_conj (x g : P8) (hg : g ∈ A8s) (hgx : g * rep4 * g⁻¹ = x) (A : Subgroup P8)
    (hA : A ≤ Op 2 (Subgroup.centralizer ({x} : Set P8) ⊓ A8s)) (hEA : IsElementaryAbelian 2 A) : Nat.card A ≤ 8 := by
  subst hgx
  haveI := hEA
  have hgs : Equiv.Perm.sign g = 1 := mem_alternatingGroup.1 hg
  have hφinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hψinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hP1' : SylP1.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({g * rep4 * g⁻¹} : Set P8) ⊓ A8s := by
    rintro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨hzc, hzA⟩ := Subgroup.mem_inf.1 (P1_le hz)
    have hzr : z * rep4 = rep4 * z := Subgroup.mem_centralizer_singleton_iff.1 hzc
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      show g * z * g⁻¹ * (g * rep4 * g⁻¹) = g * rep4 * g⁻¹ * (g * z * g⁻¹)
      calc g * z * g⁻¹ * (g * rep4 * g⁻¹) = g * (z * rep4) * g⁻¹ := by group
        _ = g * (rep4 * z) * g⁻¹ := by rw [hzr]
        _ = g * rep4 * g⁻¹ * (g * z * g⁻¹) := by group
    · have hzs : Equiv.Perm.sign z = 1 := mem_alternatingGroup.1 hzA
      exact mem_alternatingGroup.2 (by simp [map_mul, map_inv, hgs, hzs])
  have hP2' : SylP2.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({g * rep4 * g⁻¹} : Set P8) ⊓ A8s := by
    rintro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨hzc, hzA⟩ := Subgroup.mem_inf.1 (P2_le hz)
    have hzr : z * rep4 = rep4 * z := Subgroup.mem_centralizer_singleton_iff.1 hzc
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      show g * z * g⁻¹ * (g * rep4 * g⁻¹) = g * rep4 * g⁻¹ * (g * z * g⁻¹)
      calc g * z * g⁻¹ * (g * rep4 * g⁻¹) = g * (z * rep4) * g⁻¹ := by group
        _ = g * (rep4 * z) * g⁻¹ := by rw [hzr]
        _ = g * rep4 * g⁻¹ * (g * z * g⁻¹) := by group
    · have hzs : Equiv.Perm.sign z = 1 := mem_alternatingGroup.1 hzA
      exact mem_alternatingGroup.2 (by simp [map_mul, map_inv, hgs, hzs])
  have hc1 : Nat.card (SylP1.map (MulAut.conj g).toMonoidHom) = 64 := by
    rw [Subgroup.card_map_of_injective hφinj, P1_card]
  have hc2 : Nat.card (SylP2.map (MulAut.conj g).toMonoidHom) = 64 := by
    rw [Subgroup.card_map_of_injective hφinj, P2_card]
  have S1 : Op 2 (Subgroup.centralizer ({g * rep4 * g⁻¹} : Set P8) ⊓ A8s) ≤ SylP1.map (MulAut.conj g).toMonoidHom :=
    sylow_contains (H := Subgroup.centralizer ({g * rep4 * g⁻¹} : Set P8) ⊓ A8s) inf_le_right
      (FF79.L41.Op_le _) (fun h hh r hr => FF79.L41.Op_conj_mem hh hr)
      (FF79.L41.Op_isPGroup _) hP1' hc1
  have S2 : Op 2 (Subgroup.centralizer ({g * rep4 * g⁻¹} : Set P8) ⊓ A8s) ≤ SylP2.map (MulAut.conj g).toMonoidHom :=
    sylow_contains (H := Subgroup.centralizer ({g * rep4 * g⁻¹} : Set P8) ⊓ A8s) inf_le_right
      (FF79.L41.Op_le _) (fun h hh r hr => FF79.L41.Op_conj_mem hh hr)
      (FF79.L41.Op_isPGroup _) hP2' hc2
  have hBQ : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ Qsub := by
    rintro b hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨z1, hz1, hz1a⟩ := Subgroup.mem_map.1 (S1 (hA ha))
    obtain ⟨z2, hz2, hz2a⟩ := Subgroup.mem_map.1 (S2 (hA ha))
    have e1 : (MulAut.conj g⁻¹).toMonoidHom a = z1 := by
      rw [← hz1a]
      show g⁻¹ * (g * z1 * g⁻¹) * g⁻¹⁻¹ = z1
      group
    have e2 : (MulAut.conj g⁻¹).toMonoidHom a = z2 := by
      rw [← hz2a]
      show g⁻¹ * (g * z2 * g⁻¹) * g⁻¹⁻¹ = z2
      group
    have hz12 : z1 = z2 := e1.symm.trans e2
    have hz1P2 : z1 ∈ SylP2 := by
      rw [hz12]
      exact hz2
    rw [e1]
    exact mem_Qsub_of_P12 hz1 hz1P2
  haveI : IsElementaryAbelian 2 (A.map (MulAut.conj g⁻¹).toMonoidHom) :=
    IsElementaryAbelian.map (p := 2) (A := A) (MulAut.conj g⁻¹).toMonoidHom
  have hcardB : Nat.card (A.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective hψinj
  have := EA_Q (A.map (MulAut.conj g⁻¹).toMonoidHom) hBQ
  omega

theorem A_transvRank_holds : A_transvRank_stmt := by
  intro Y hY x hx hne h1 h2 A hA hEA
  rcases hY with rfl | rfl
  · obtain ⟨t, rfl⟩ := (mem_Ua_iff x).1 hx
    rcases transvRank_dec_Ua t hne with hC | ⟨s, hs⟩ | ⟨g, -, hsign, hconj⟩
    · exact absurd (Subgroup.mem_inf.2 ⟨(mem_Ua_iff _).2 ⟨t, rfl⟩,
        mem_centralizer_singleton_iff.2 hC⟩) h2
    · have hmem : tup4 pa pb pc pd t ∈ ⁅Ua, Subgroup.zpowers cc⁆ := by
        have := commutator_mem_commutator ((mem_Ua_iff _).2 ⟨s, rfl⟩)
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers cc))
        rw [commutatorElement_def, hs] at this
        exact this
      exact absurd hmem h1
    · exact bound_of_conj _ g (mem_alternatingGroup.2 hsign) hconj A hA hEA
  · obtain ⟨t, rfl⟩ := (mem_Ub_iff x).1 hx
    rcases transvRank_dec_Ub t hne with hC | ⟨s, hs⟩ | ⟨g, -, hsign, hconj⟩
    · exact absurd (Subgroup.mem_inf.2 ⟨(mem_Ub_iff _).2 ⟨t, rfl⟩,
        mem_centralizer_singleton_iff.2 hC⟩) h2
    · have hmem : tup4 qa qb qc qd t ∈ ⁅Ub, Subgroup.zpowers cc⁆ := by
        have := commutator_mem_commutator ((mem_Ub_iff _).2 ⟨s, rfl⟩)
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers cc))
        rw [commutatorElement_def, hs] at this
        exact this
      exact absurd hmem h1
    · exact bound_of_conj _ g (mem_alternatingGroup.2 hsign) hconj A hA hEA

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
