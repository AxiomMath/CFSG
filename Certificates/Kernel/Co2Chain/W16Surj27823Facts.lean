module

public import Certificates.Kernel.Co2Chain.W16Surj27823
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.J2CoverSnd.Packed

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Chain.W16

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.J2VertK
open CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.Monster.B.Co2.Native

theorem testBit_maskL : ∀ (l : List Nat) (x : Nat), (maskL l).testBit x = decide (x ∈ l)
  | [], x => by simp [maskL]
  | y :: l, x => by
    have e : maskL (y :: l) = (1 <<< y) ||| maskL l := rfl
    rw [e, Nat.testBit_or, testBit_maskL l x, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : y = x
    · subst h
      simp
    · simp [h, List.mem_cons, Ne.symm h]

theorem lt_of_blt' {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa using h

theorem sameSet_of_mask {S T : Array Nat} (h : maskL S.toList = maskL T.toList)
    (hs : S.size = T.size) : sameSet S T = true := by
  have hm : ∀ x, x ∈ S.toList ↔ x ∈ T.toList := fun x => by
    have := congrArg (fun m => m.testBit x) h
    simpa [testBit_maskL] using this
  unfold sameSet
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, Array.contains_iff_mem,
    Array.mem_def, beq_iff_eq]
  exact ⟨⟨fun x hx => (hm x).1 hx, fun x hx => (hm x).2 hx⟩, hs⟩

theorem imgL_list (G : Nat) : ∀ l : List Nat, (∀ x ∈ l, x < 128) →
    maskL (l.map fun x => (unpack 128 8 G)[x]!) = imgL G l
  | [], _ => rfl
  | x :: l, h => by
    change Nat.lor (Nat.shiftLeft 1 ((unpack 128 8 G)[x]!)) (maskL (l.map fun x =>
      (unpack 128 8 G)[x]!)) = Nat.lor (Nat.shiftLeft 1 (pg 8 (mask 8) G x)) (imgL G l)
    rw [unpack_get' (h x List.mem_cons_self),
      imgL_list G l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem om_eq {j : Nat} (hj : j < 216) : OM j = maskL omegaSets[j]!.toList :=
  Nat.eq_of_beq_eq_true (allN_spec kOM j hj)

theorem same_of {G j j' : Nat} (hj : j < 216) (hj' : j' < 216)
    (h : Nat.beq (imgL G omegaSets[j]!.toList) (OM j') = true) :
    sameSet (imgSet (unpack 128 8 G) omegaSets[j]!) omegaSets[j']! = true := by
  refine sameSet_of_mask ?_ ?_
  · unfold imgSet
    rw [Array.toList_map, imgL_list G _ (kSz j hj).2, Nat.eq_of_beq_eq_true h, om_eq hj']
  · rw [imgSet, Array.size_map, (kSz j hj).1, (kSz j' hj').1]

theorem binds : Binds 128 8 W16C.S 36 6 W16C.BP sgsArr baseArr :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel,
    fun j hj => unpack_eq_of_bindArrK (allN_spec kStrong j hj), by decide +kernel,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec kBase t ht)⟩

theorem inPg_of {G : Nat} (c : cn G = true) (s : sk G = true) : inPg (unpack 128 8 G) = true := by
  unfold inPg levelsPg
  rw [CFSG.KC.J2Cover.Snd.siftK_eq' binds kPerm W16C.hl c]
  exact s

theorem inv_of {G GI : Nat} (h : invEqK 128 8 (mask 8) (128 * 8) G GI = true) :
    isInvA 128 (unpack 128 8 G) (invCand 128 (unpack 128 8 G)) = true := by
  rw [(invEqK_sound h).1]
  exact (invEqK_sound h).2

theorem g0_eq {k : Nat} (hk : k < 3) : g0Gens[k]! = unpack 128 8 (G0 k) := by
  have h := allN_spec kG0 k hk
  simp only [bAnd_iff] at h
  exact unpack_eq_of_bindArrK h.1

theorem gr_eq {r : Nat} (hr : r < 10) : gamReps[r]! = unpack 128 8 (GR r) := by
  have h := allN_spec kGR r hr
  simp only [bAnd_iff] at h
  exact unpack_eq_of_bindArrK h.1

theorem gens_eq {r i : Nat} (hr : r < 10) (hi : i < 4) :
    (g0Gens.push gamReps[r]!)[i]! = unpack 128 8 (GG r i) := by
  have h3 : g0Gens.size = 3 := kSizes.2.2.2.1
  have hlt : ∀ k < 3, (g0Gens.push gamReps[r]!)[k]! = g0Gens[k]! := fun k hk => by
    rw [getElem!_pos _ k (by rw [Array.size_push, h3]; omega), getElem!_pos g0Gens k (by omega),
      Array.getElem_push_lt]
  have hlast : (g0Gens.push gamReps[r]!)[g0Gens.size]! = gamReps[r]! := by
    rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]
  rw [h3] at hlast
  interval_cases i
  · rw [hlt 0 (by omega), g0_eq (by omega)]
    rfl
  · rw [hlt 1 (by omega), g0_eq (by omega)]
    rfl
  · rw [hlt 2 (by omega), g0_eq (by omega)]
    rfl
  · rw [hlast, gr_eq hr]
    rfl

theorem treeOK_of {r : Nat} (hr : r < 10) (h : treeK' r = true) : treeOK r = true := by
  unfold treeK' at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  unfold treeOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro k' hk'
    have hrow := allN_spec h3 k' (List.mem_range.1 hk')
    unfold rowK at hrow
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow ⊢
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := hrow
    refine ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, ?_⟩
    rw [gens_eq hr a3]
    exact same_of a5 a4 a6
  · rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    have hw := allN_spec h4 j hj'
    simp only [Bool.and_eq_true] at hw
    rw [List.any_eq_true]
    exact ⟨_, List.mem_range.2 (lt_of_blt' hw.1), hw.2⟩

theorem omega_ok : omegaClosed = true := by
  unfold omegaClosed
  rw [Bool.and_eq_true]
  refine ⟨kSmall, ?_⟩
  rw [List.all_eq_true]
  intro gi hgi
  have hgi' := List.mem_range.1 hgi
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.1 hj
  have hc := allN_spec (allN_spec kClosed gi hgi') j hj'
  rw [bAnd_iff] at hc
  rw [List.any_eq_true]
  refine ⟨_, List.mem_range.2 (lt_of_blt' hc.1), ?_⟩
  rw [unpack_eq_of_bindArrK (allN_spec kStrong gi hgi')]
  exact same_of hj' (lt_of_blt' hc.1) hc.2

theorem g0_ok : g0Check = true := by
  unfold g0Check
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨kSizes.2.2.2.1, ?_⟩, kSizes.2.2.2.2.1⟩, ?_⟩, kRoots⟩
  · rw [List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    have h := allN_spec kG0 k hk'
    simp only [bAnd_iff] at h
    obtain ⟨-, hi, hc, hs, hm⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [g0_eq hk']
    exact ⟨⟨⟨by rw [← g0_eq hk']; exact kSizes.2.2.2.2.2 k hk', inv_of hi⟩, inPg_of hc hs⟩,
      same_of (by decide) (by decide) hm⟩
  · rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    have h := allN_spec kPar j hj'
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    cases hb : Nat.beq g0Par[j]!.1 j
    · rw [hb] at h
      have h' : bAnd(Nat.blt g0Par[j]!.1 j, bAnd(Nat.blt g0Par[j]!.2 3,
          Nat.beq (imgL (G0 g0Par[j]!.2) omegaSets[g0Par[j]!.1]!.toList) (OM j))) = true := h
      simp only [bAnd_iff] at h'
      obtain ⟨p1, p2, p3⟩ := h'
      have p1' := lt_of_blt' p1
      have p2' := lt_of_blt' p2
      right
      refine ⟨⟨p1', p2'⟩, ?_⟩
      rw [g0_eq p2']
      exact same_of (by omega) hj' p3
    · left
      exact Nat.eq_of_beq_eq_true hb

theorem roots_ok : ((List.range 10).all rootCheck) = true := by
  rw [List.all_eq_true]
  intro r hr
  have hr' := List.mem_range.1 hr
  have h := allN_spec kGR r hr'
  simp only [bAnd_iff] at h
  obtain ⟨-, hi, hc, hs, hm⟩ := h
  unfold rootCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  have ht := allN_spec kTree r hr'
  rw [Bool.or_eq_true] at ht
  rw [gr_eq hr']
  refine ⟨⟨⟨⟨⟨by rw [← gr_eq hr']; exact (kRootSmall r hr').1, inv_of hi⟩, inPg_of hc hs⟩,
    (kRootSmall r hr').2⟩, same_of (by decide) (kRootSmall r hr').2 hm⟩, ?_⟩
  rcases ht with ht | ht
  · left
    rw [← gr_eq hr']
    exact ht
  · right
    exact treeOK_of hr' ht

theorem check : surjCheck = true := by
  unfold surjCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨omega_ok, g0_ok⟩, kSizes.1⟩, kSizes.2.1⟩, kSizes.2.2.1⟩, roots_ok⟩

end CertificateChecks.KernelCo2Chain.W16

end
