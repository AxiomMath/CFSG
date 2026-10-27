module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3Check
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint
open scoped Matrix

section Push

theorem push_getElem!_lt {α : Type} [Inhabited α] (A : Array α) (x : α) {i : Nat}
    (h : i < A.size) : (A.push x)[i]! = A[i]! := by
  rw [getElem!_pos (A.push x) i (by simpa using Nat.lt_succ_of_lt h), getElem!_pos A i h,
    Array.getElem_push_lt]

theorem push_getElem!_size {α : Type} [Inhabited α] (A : Array α) (x : α) :
    (A.push x)[A.size]! = x := by
  rw [getElem!_pos (A.push x) A.size (by simp), Array.getElem_push_eq]

theorem xor_one_eq (c : Nat) : c ^^^ 1 = if c % 2 = 0 then c + 1 else c - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · simp [Nat.testBit_zero]
    split <;> simp_all <;> omega
  · simp [Nat.testBit_succ]
    split_ifs with h
    · have : (c + 1) / 2 = c / 2 := by omega
      rw [this]
    · have : (c - 1) / 2 = c / 2 := by omega
      rw [this]

theorem invCodes_lt {w : List Nat} {n : Nat} (h : ∀ c ∈ w, c < n) (hn : n % 2 = 0) :
    ∀ c ∈ invCodes w, c < n := by
  intro c hc
  simp only [invCodes, List.mem_map, List.mem_reverse] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  have := h c' hc'
  rw [xor_one_eq]
  split <;> omega

end Push

section Spec

variable {M V : Type} [Inhabited M] {O : Ops M V} {p d : Nat} (Sp : OpsSpec O p d)
  (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p)))

include Sp

theorem evalLetters_spec {L : Array M} (hL : ∀ c < L.size, Sp.WF L[c]! ∧ Sp.toMat L[c]! ∈ S) :
    ∀ {w : List Nat}, (∀ c ∈ w, c < L.size) →
      Sp.WF (evalLetters O L w) ∧ Sp.toMat (evalLetters O L w) ∈ S
  | [], _ => ⟨Sp.one_wf, by
    show Sp.toMat O.one ∈ S
    rw [Sp.toMat_one]; exact S.one_mem⟩
  | c :: w, hw => by
    obtain ⟨wi, mi⟩ := hL c (hw c List.mem_cons_self)
    obtain ⟨w2, m2⟩ := evalLetters_spec hL (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))
    exact ⟨Sp.mul_wf wi w2, by
      show Sp.toMat (O.mul L[c]! (evalLetters O L w)) ∈ S
      rw [Sp.toMat_mul wi w2]; exact S.mul_mem mi m2⟩

set_option linter.unusedVariables false in
theorem extendLetters_spec : ∀ (ds : List (List Nat)) {L : Array M}
    (hL : ∀ c < L.size, Sp.WF L[c]! ∧ Sp.toMat L[c]! ∈ S) (hsz : L.size % 2 = 0)
    (hd : defsOK L.size ds = true),
    (extendLetters O L ds).size = L.size + 2 * ds.length ∧
      ∀ c < (extendLetters O L ds).size,
        Sp.WF (extendLetters O L ds)[c]! ∧ Sp.toMat (extendLetters O L ds)[c]! ∈ S
  | [], L, hL, _, _ => ⟨by simp [extendLetters], hL⟩
  | w :: ws, L, hL, hsz, hd => by
    simp only [defsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hd
    obtain ⟨hw, hws⟩ := hd
    have h1 := evalLetters_spec Sp S hL hw
    have h2 := evalLetters_spec Sp S hL (invCodes_lt hw hsz)
    have hsz' : (((L.push (evalLetters O L w)).push (evalLetters O L (invCodes w)))).size =
        L.size + 2 := by simp
    have hL' : ∀ c < ((L.push (evalLetters O L w)).push (evalLetters O L (invCodes w))).size,
        Sp.WF ((L.push (evalLetters O L w)).push (evalLetters O L (invCodes w)))[c]! ∧
        Sp.toMat ((L.push (evalLetters O L w)).push (evalLetters O L (invCodes w)))[c]! ∈ S := by
      intro c hc
      rw [hsz'] at hc
      by_cases hc0 : c < L.size
      · rw [push_getElem!_lt _ _ (by simp; omega), push_getElem!_lt _ _ hc0]
        exact hL c hc0
      · by_cases hc1 : c = L.size
        · subst hc1
          rw [push_getElem!_lt _ _ (by simp), push_getElem!_size]
          exact h1
        · have : c = L.size + 1 := by omega
          subst this
          have := push_getElem!_size (L.push (evalLetters O L w)) (evalLetters O L (invCodes w))
          simp only [Array.size_push] at this
          rw [this]
          exact h2
    obtain ⟨hs, hall⟩ := extendLetters_spec ws hL' (by rw [hsz']; omega) (by rw [hsz']; exact hws)
    exact ⟨by rw [extendLetters, hs, hsz']; simp; omega, hall⟩

end Spec

section Words

variable {M V : Type} [Inhabited M] {O : Ops M V} {p d : Nat} (Sp : OpsSpec O p d)
  {G : Type*} [Group G] (φ : G →* Matrix (Fin d) (Fin d) (ZMod p))

include Sp

theorem evalGen_spec {m : Nat} {x : Fin m → G} {Gs Gi : Array M}
    (hG : ∀ i : Fin m, Sp.WF Gs[i.val]! ∧ Sp.toMat Gs[i.val]! = φ (x i))
    (hGi : ∀ i : Fin m, Sp.WF Gi[i.val]! ∧ Sp.toMat Gi[i.val]! = φ (x i)⁻¹)
    (w : List (Fin m × Bool)) :
    Sp.WF (evalGen O Gs Gi w) ∧
      Sp.toMat (evalGen O Gs Gi w) = φ (FreeGroup.lift x (FreeGroup.mk w)) := by
  induction w with
  | nil =>
    refine ⟨Sp.one_wf, ?_⟩
    simp [evalGen, Sp.toMat_one]
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have e : FreeGroup.lift x (FreeGroup.mk ((i, b) :: w)) =
        (if b then x i else (x i)⁻¹) * FreeGroup.lift x (FreeGroup.mk w) := by
      rw [FreeGroup.lift_mk, FreeGroup.lift_mk, List.map_cons, List.prod_cons]
      cases b <;> rfl
    cases b
    · obtain ⟨w1, m1⟩ := hGi i
      refine ⟨Sp.mul_wf w1 ih.1, ?_⟩
      rw [e, ite_eq_right (by simp), map_mul, ← m1, ← ih.2]
      exact Sp.toMat_mul w1 ih.1
    · obtain ⟨w1, m1⟩ := hG i
      refine ⟨Sp.mul_wf w1 ih.1, ?_⟩
      rw [e, ite_eq_left rfl, map_mul, ← m1, ← ih.2]
      exact Sp.toMat_mul w1 ih.1

end Words

section Orbit

variable {M V : Type} [Inhabited M] [Inhabited V] {O : Ops M V}

theorem strictInc_nodup {l : List Nat} (h : strictInc l = true) : l.Nodup := by
  have hc : List.IsChain (· < ·) l := by
    induction l with
    | nil => exact List.isChain_nil
    | cons a l ih =>
      cases l with
      | nil => exact List.isChain_singleton a
      | cons b l =>
        simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
        exact List.IsChain.cons_cons h.1 (ih h.2)
  exact (List.isChain_iff_pairwise.1 hc).imp (fun h => h.ne)

theorem orbVecs_spec (gens : Array M) (w0 : V) (par lab : Array Nat) :
    ∀ n : Nat, (orbVecs O gens w0 par lab n).size = n ∧
      (∀ i < n, i = 0 → (orbVecs O gens w0 par lab n)[i]! = w0) ∧
      (∀ i < n, 0 < i → par[i]! < i → (orbVecs O gens w0 par lab n)[i]! =
        O.vmul (orbVecs O gens w0 par lab n)[par[i]!]! gens[lab[i]!]!) := by
  intro n
  induction n with
  | zero => simp [orbVecs]
  | succ n ih =>
    obtain ⟨hs, h0, hst⟩ := ih
    have e : orbVecs O gens w0 par lab (n + 1) =
        (orbVecs O gens w0 par lab n).push (if n = 0 then w0 else
          O.vmul (orbVecs O gens w0 par lab n)[par[n]!]! gens[lab[n]!]!) := by
      simp only [orbVecs, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    rw [e]
    set A := orbVecs O gens w0 par lab n with hA
    refine ⟨by simp [hs], fun i hi hi0 => ?_, fun i hi hpos hp => ?_⟩
    · subst hi0
      by_cases hn : n = 0
      · subst hn
        rw [show (0 : Nat) = A.size by rw [hs]]
        simp
      · rw [push_getElem!_lt A _ (by rw [hs]; omega)]
        exact h0 0 (by omega) rfl
    · by_cases hin : i < n
      · have hpn : par[i]! < A.size := by rw [hs]; omega
        rw [push_getElem!_lt A _ (by rw [hs]; exact hin), push_getElem!_lt A _ hpn]
        exact hst i hin hpos hp
      · have hi' : i = n := by omega
        subst hi'
        have hpn : par[i]! < A.size := by rw [hs]; exact hp
        have e1 := push_getElem!_size A
          (if i = 0 then w0 else O.vmul A[par[i]!]! gens[lab[i]!]!)
        rw [hs] at e1
        rw [e1, push_getElem!_lt A _ hpn, ite_eq_right hpos.ne']

variable {p d : Nat} (Sp : OpsSpec O p d)
  {G : Type*} [Group G] [Finite G] (φ : G →* Matrix (Fin d) (Fin d) (ZMod p))

include Sp

theorem orbit_card_ge {m : Nat} {gs : Fin m → G} {gens : Array M} (hsz : gens.size = m)
    (hX : ∀ k : Fin m, Sp.WF gens[k.val]! ∧ Sp.toMat gens[k.val]! = φ (gs k)) {w0 : V}
    (hw0 : Sp.VWF w0) {key : V → Nat}
    (hkey : ∀ u w, Sp.toVec u = Sp.toVec w → key u = key w) {par lab : Array Nat} {n : Nat}
    (h : orbitOK O key gens w0 par lab n = true) :
    n ≤ Nat.card (Subgroup.closure (Set.range gs)) := by
  classical
  unfold orbitOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hn, hpar⟩, hlab⟩, hkeys⟩ := h
  obtain ⟨hsize, hroot, hstep⟩ := orbVecs_spec gens w0 par lab n
  generalize orbVecs O gens w0 par lab n = ws at hsize hroot hstep hkeys
  have hsem : ∀ i, i < n → ∃ g ∈ Subgroup.closure (Set.range gs), Sp.VWF ws[i]! ∧
      Sp.toVec ws[i]! = Sp.toVec w0 ᵥ* φ g := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨1, Subgroup.one_mem _, by rw [hroot 0 hi rfl]; exact hw0,
          by rw [hroot 0 hi rfl, map_one, Matrix.vecMul_one]⟩
      · have hp := (hpar i hi).resolve_left hpos.ne'
        obtain ⟨g', hg', hvw, hv⟩ := ih (par[i]!) hp (hp.trans hi)
        have hl : lab[i]! < m := by have := hlab i hi; rwa [hsz] at this
        have hst := hstep i hi hpos hp
        obtain ⟨hXw, hXm⟩ := hX ⟨lab[i]!, hl⟩
        refine ⟨g' * gs ⟨lab[i]!, hl⟩, Subgroup.mul_mem _ hg'
          (Subgroup.subset_closure ⟨_, rfl⟩), ?_, ?_⟩
        · rw [hst]; exact Sp.vmul_wf hvw hXw
        · rw [hst, Sp.toVec_vmul hvw hXw, hv, hXm, Matrix.vecMul_vecMul, map_mul]
  have hnd : (ws.toList.map key).Nodup := by
    have h1 := strictInc_nodup hkeys
    exact (List.mergeSort_perm _ _).nodup_iff.1 h1
  choose! g hg hvw hv using hsem
  let F : Fin n → Subgroup.closure (Set.range gs) := fun i => ⟨g i, hg i i.2⟩
  have hF : Function.Injective F := by
    intro i j hij
    have hgij : g i = g j := congrArg Subtype.val hij
    have hveq : Sp.toVec ws[i.val]! = Sp.toVec ws[j.val]! := by
      rw [hv i i.2, hv j j.2, hgij]
    have hk := hkey _ _ hveq
    have hlen : ∀ k : Fin n, k.val < (ws.toList.map key).length := fun k => by
      simp [hsize]
    have hel : ∀ k : Fin n, (ws.toList.map key)[k.val]'(hlen k) = key ws[k.val]! := fun k => by
      rw [List.getElem_map, getElem!_pos ws k.val (by rw [hsize]; exact k.2)]
      rfl
    have := (hnd.getElem_inj_iff (hi := hlen i) (hj := hlen j)).1 (by rw [hel, hel]; exact hk)
    exact Fin.ext this
  calc n = Nat.card (Fin n) := by simp
    _ ≤ Nat.card (Subgroup.closure (Set.range gs)) := Nat.card_le_card_of_injective F hF

end Orbit

section Main

variable {M V : Type} [Inhabited M] [Inhabited V] {O : Ops M V} {p d : Nat} [NeZero p]
  (Sp : OpsSpec O p d)

include Sp

theorem exists_local3_of_check {m : Nat} (D : Local3Data m) {key : V → Nat} {root : V}
    (hroot : Sp.VWF root) (hkey : ∀ u w, Sp.toVec u = Sp.toVec w → key u = key w)
    (h : local3Check O key D root = true) :
    ∃ x : Fin m → (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      (∀ r ∈ D.rels, FreeGroup.lift x (FreeGroup.mk r) = 1) ∧
      (∀ i : Fin m, x i ^ D.ords.getD i 0 = 1) ∧
      (∀ i : Fin m, D.ords.getD i 0 ≠ 0 ∧ Nat.gcd (D.ords.getD i 0) 3 = 1) ∧
      D.n ≤ Nat.card (Subgroup.closure (Set.range x)) := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB with hS
  unfold local3Check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hlen, hdefs⟩, hlet⟩, hord⟩, hrels⟩, horb⟩ := h
  have hA : Sp.WF (O.decode D.seedA) ∧ Sp.toMat (O.decode D.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.seedB) ∧ Sp.toMat (O.decode D.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  set L0 := seedLetters O (O.decode D.seedA) (O.decode D.seedB) D.oA D.oB with hL0def
  have hL0sz : L0.size = 4 := by simp [hL0def, seedLetters]
  have hL0 : ∀ c < L0.size, Sp.WF L0[c]! ∧ Sp.toMat L0[c]! ∈ S := by
    intro c hc
    rw [hL0sz] at hc
    obtain ⟨wA, mA⟩ := hA
    obtain ⟨wB, mB⟩ := hB
    interval_cases c
    · exact ⟨wA, mA⟩
    · obtain ⟨w, e⟩ := Sp.pow_spec wA (D.oA - 1)
      exact ⟨w, by
        show Sp.toMat (O.pow (O.decode D.seedA) (D.oA - 1)) ∈ S
        rw [e]; exact S.pow_mem mA _⟩
    · exact ⟨wB, mB⟩
    · obtain ⟨w, e⟩ := Sp.pow_spec wB (D.oB - 1)
      exact ⟨w, by
        show Sp.toMat (O.pow (O.decode D.seedB) (D.oB - 1)) ∈ S
        rw [e]; exact S.pow_mem mB _⟩
  obtain ⟨hLsz, hL⟩ := extendLetters_spec Sp S D.defs hL0 (by rw [hL0sz])
    (by rw [hL0sz]; exact hdefs)
  set L := extendLetters O L0 D.defs with hLdef
  set Gs : Array M := (D.gens.map (evalLetters O L)).toArray with hGs
  have hGsz : Gs.size = m := by simp [hGs, hlen]
  have hGi_get : ∀ i : Fin m, Gs[i.val]! = evalLetters O L (D.gens[i.val]'(by omega)) := by
    intro i
    have hi : i.val < Gs.size := by rw [hGsz]; exact i.isLt
    rw [getElem!_pos Gs i.val hi]
    simp [hGs]
  have hGmem : ∀ i : Fin m, Sp.WF Gs[i.val]! ∧ Sp.toMat Gs[i.val]! ∈ S := by
    intro i
    rw [hGi_get]
    exact evalLetters_spec Sp S hL (fun c hc => by
      have := hlet (D.gens[i.val]'(by omega)) (List.getElem_mem _) c hc
      rw [hLsz, hL0sz]
      exact this)
  have hordi : ∀ i : Fin m, D.ords.getD i 0 ≠ 0 ∧ Nat.gcd (D.ords.getD i 0) 3 = 1 ∧
      O.eq (O.pow Gs[i.val]! (D.ords.getD i 0)) O.one = true := by
    intro i
    have := hord i i.2
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hpowM : ∀ i : Fin m, Sp.toMat Gs[i.val]! ^ D.ords.getD i 0 = 1 := fun i =>
    Sp.pow_eq_one_of_check (hGmem i).1 (hordi i).2.2
  let x : Fin m → Sˣ := fun i => unitOf S (hGmem i).2 (hordi i).1 (hpowM i)
  have hxval : ∀ i : Fin m, valHom S (x i) = Sp.toMat Gs[i.val]! := fun i =>
    valHom_unitOf S _ _ _
  have hxpow : ∀ i : Fin m, x i ^ D.ords.getD i 0 = 1 := fun i => unitOf_pow S _ _ _
  set Gi : Array M := (List.range m).toArray.map fun i => O.pow Gs[i]! (D.ords.getD i 0 - 1)
    with hGi
  have hGisz : Gi.size = m := by simp [hGi]
  have hGi_get' : ∀ i : Fin m, Gi[i.val]! = O.pow Gs[i.val]! (D.ords.getD i 0 - 1) := by
    intro i
    have hi : i.val < Gi.size := by rw [hGisz]; exact i.isLt
    rw [getElem!_pos Gi i.val hi]
    simp [hGi]
  have hGirep : ∀ i : Fin m, Sp.WF Gi[i.val]! ∧ Sp.toMat Gi[i.val]! = valHom S (x i)⁻¹ := by
    intro i
    rw [hGi_get', valHom_inv_of_pow S (hordi i).1 (hxpow i), hxval]
    exact ⟨(Sp.pow_spec (hGmem i).1 _).1, (Sp.pow_spec (hGmem i).1 _).2⟩
  have hGrep : ∀ i : Fin m, Sp.WF Gs[i.val]! ∧ Sp.toMat Gs[i.val]! = valHom S (x i) := fun i =>
    ⟨(hGmem i).1, (hxval i).symm⟩
  have : Finite Sˣ := Finite.of_injective (valHom S) (valHom_injective S)
  refine ⟨x, fun r hr => ?_, hxpow, fun i => ⟨(hordi i).1, (hordi i).2.1⟩, ?_⟩
  · obtain ⟨hw, hm⟩ := evalGen_spec Sp (valHom S) hGrep hGirep r
    have := Sp.toMat_eq hw Sp.one_wf (hrels r hr)
    rw [Sp.toMat_one, hm] at this
    apply valHom_injective S
    rw [this, map_one]
  · exact orbit_card_ge Sp (valHom S) (gens := Gs) hGsz hGrep hroot hkey horb

end Main

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
