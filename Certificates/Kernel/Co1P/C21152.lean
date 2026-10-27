module

public import Certificates.Kernel.Co1P.C21158
public import Certificates.Kernel.Co1P.Chk21152
public import Certificates.Kernel.Co1P.Chk21152L
public import Certificates.Kernel.Co1P.PinEGlue

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native CertificateChecks.KernelCo1B

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem lenL_eq' : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (lenL L) = _
    rw [lenL_eq' L]
    rfl

theorem getL_eq' (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L[i]?.getD x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => by
    change getL x L i = _
    rw [getL_eq' x L i]
    rfl

theorem bitsOf_testBit (k : Nat) : ∀ ns : List Nat, (bitsOf ns).testBit k = ns.contains k
  | [] => Nat.zero_testBit k
  | n :: ns => by
    change ((1 <<< n) ||| bitsOf ns).testBit k = _
    rw [List.contains_cons, ← bitsOf_testBit k ns, Nat.testBit_or, Nat.one_shiftLeft,
      Nat.testBit_two_pow]
    by_cases h : n = k
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem bit_bitsOf (ns : List Nat) (k : Nat) : bit (bitsOf ns) k = ns.contains k := by
  unfold bit
  rw [bit_eq, bitsOf_testBit]

theorem xeK_eq {n : Nat} (hn : n < 12600) : xeK orbE n = unpackR 24 (xeP n) := by
  rw [xeK, orbE_hs' hn, repX_eq, CFSG.KC.F2W.mul_unpackW]
  rfl

theorem xeiK_eq {n : Nat} (hn : n < 12600) : xeiK orbE n = unpackR 24 (xeiP n) := by
  rw [xeiK, orbE_his' hn, repXi_eq, CFSG.KC.F2W.mul_unpackW]
  rfl

theorem adjC_eq' (X Xi V : Nat) :
    adjC (ptSet orbE) (unpackR 24 X) (unpackR 24 Xi) (unpackR 24 V) = adjP X Xi V := by
  rw [adjC, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, orbE_mem]
  rfl

theorem adjK_eq {k : Nat} (hk : k < 12600) (B : Nat) :
    adjK orbE (ptSet orbE) (unpackR 24 B) k = adjP (xeP k) (xeiP k) B := by
  rw [adjK, xeK_eq hk, xeiK_eq hk, adjC_eq']

theorem treeIn_of {ns ps : List Nat} {P Q PK : Nat → Bool} (hP : ∀ n < 12600, P n = PK n)
    (ht : treeK ns ps PK = true) (hQ : ∀ k < 12600, (!(Q k) || ns.contains k) = true) :
    treeIn orbE (ptSet orbE) ns ps P Q = true := by
  unfold treeK at ht
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true ht
  obtain ⟨h3, h4⟩ := CFSG.KC.TreeK.andB_true h1
  have h0 : 0 < ns.length := by
    have := lt_of_blt' h3
    rwa [lenL_eq'] at this
  have hl : ps.length = ns.length := by
    have := Nat.eq_of_beq_eq_true h4
    rwa [lenL_eq', lenL_eq'] at this
  have hr := allN_true h2
  rw [lenL_eq'] at hr
  have hnode : ∀ r < ns.length, ns[r]?.getD 0 < 12600 ∧ PK (ns[r]?.getD 0) = true ∧
      (r = 0 ∨ (ps[r]?.getD 0 < r ∧ adjP (xeP (ns[r]?.getD 0)) (xeiP (ns[r]?.getD 0))
        (ptPE (ns[ps[r]?.getD 0]?.getD 0)) = true)) := by
    intro r hr'
    have e := hr r hr'
    simp only [getL_eq'] at e
    obtain ⟨e1, e2⟩ := CFSG.KC.TreeK.andB_true e
    obtain ⟨e3, e4⟩ := CFSG.KC.TreeK.andB_true e1
    refine ⟨lt_of_blt' e3, e4, ?_⟩
    rcases orB_true e2 with e5 | e5
    · exact Or.inl (Nat.eq_of_beq_eq_true e5)
    · obtain ⟨e6, e7⟩ := CFSG.KC.TreeK.andB_true e5
      exact Or.inr ⟨lt_of_blt' e6, e7⟩
  have hget : ∀ (L : List Nat) (r : Nat) (hr : r < L.length), L.toArray[r]! = L[r]?.getD 0 := by
    intro L r hr
    rw [getElem!_pos L.toArray r (by simpa using hr), List.getElem_toArray,
      List.getElem?_eq_getElem hr]
    rfl
  unfold treeIn
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.size_toArray]
  refine ⟨⟨⟨h0, hl⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro r hr'
    have hr2 := List.mem_range.1 hr'
    obtain ⟨n1, n2, n3⟩ := hnode r hr2
    rw [hget ns r hr2, orbE_size', hP _ n1]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
    refine ⟨⟨n1, n2⟩, ?_⟩
    rcases n3 with n3 | ⟨n4, n5⟩
    · exact Or.inl n3
    · have hp : ps[r]?.getD 0 < ns.length := by omega
      obtain ⟨m1, -, -⟩ := hnode _ hp
      refine Or.inr ⟨?_, ?_⟩
      · rw [hget ps r (by omega)]
        exact n4
      · rw [hget ps r (by omega), hget ns _ hp, xeK_eq n1, xeiK_eq n1, orbE_pt' m1, adjC_eq']
        exact n5
  · rw [orbE_size', List.all_eq_true]
    intro k hk
    rw [Std.HashSet.contains_ofList]
    exact hQ k (List.mem_range.1 hk)

theorem ronan_all {k : Nat} (hk : k < 12600) :
    (∀ t < 7, orB (notB (adjP (xeP k) (xeiP k) (RB t))) (bit (maskL2 t) k) = true) ∧
      ∀ t < 2, notB (adjP (xeP k) (xeiP k) (RF t)) = true := by
  have hc : ∀ c < 197, chunkK 12600 (ronanAtW fun t => getL 0 [maskL2 0, maskL2 1, maskL2 2,
      maskL2 3, maskL2 4, maskL2 5, maskL2 6] t) c = true := by
    intro c hc
    have h := RonanE.all c hc
    unfold ronanChunk at h
    simp only [strictB_eq'] at h
    exact h
  have h := chunks_all (by decide) hc k hk
  unfold ronanAtW at h
  rw [strictB_eq', strictB_eq'] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  refine ⟨fun t ht => ?_, allN_true h2⟩
  have e := allN_true h1 t ht
  interval_cases t <;> exact e

theorem not_eqK {A B : Nat} (h : notB (eqK A B) = true) : (unpackR 24 A != unpackR 24 B) = true := by
  rw [bne, beq_unpack]
  rw [notB_eq] at h
  exact h

theorem lvl2 : ((List.range 7).all fun t => lvl2Check orbE (ptSet orbE) t) = true := by
  rw [List.all_eq_true]
  intro t ht
  have ht' := List.mem_range.1 ht
  have h := allN_true lvl2_ok t ht'
  unfold lvl2K at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  obtain ⟨h3, h4⟩ := CFSG.KC.TreeK.andB_true h1
  unfold lvl2Check
  simp only [Bool.and_eq_true]
  rw [repRows_eq, iotaA_K, orbE_mem]
  refine ⟨⟨not_eqK h3, by rw [notB_eq] at h4; exact h4⟩, ?_⟩
  refine treeIn_of (PK := fun n => adjP (xeP n) (xeiP n) (RB t)) (fun n hn => adjK_eq hn _) h2
    fun k hk => ?_
  rw [adjK_eq hk]
  have e := (ronan_all hk).1 t ht'
  rw [orB_eq, notB_eq, maskL2, bit_bitsOf] at e
  exact e

theorem far : ((List.range 2).all fun t => farCheck orbE (ptSet orbE) t) = true := by
  rw [List.all_eq_true]
  intro t ht
  have ht' := List.mem_range.1 ht
  have h := allN_true far_ok t ht'
  unfold farK at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  obtain ⟨h3, h4⟩ := CFSG.KC.TreeK.andB_true h1
  obtain ⟨h5, h6⟩ := CFSG.KC.TreeK.andB_true h2
  obtain ⟨h7, h8⟩ := CFSG.KC.TreeK.andB_true h5
  have hc := lt_of_blt' h7
  have hm := lt_of_blt' h8
  unfold farCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [repRows_eq, iotaA_K, orbE_mem, orbE_size', nbrX, xeK_eq hc, xeiK_eq hc, xeK_eq hm, xeiK_eq hm,
    CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, adjC_eq']
  refine ⟨⟨⟨⟨⟨not_eqK h3, by rw [notB_eq] at h4; exact h4⟩, ?_⟩, hc⟩, hm⟩, h6⟩
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.1 hk
  rw [adjK_eq hk']
  have e := (ronan_all hk').2 t ht'
  rw [notB_eq] at e
  exact e

theorem ae : aeCheck = true := by
  have h := ae_ok
  unfold aeK at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  unfold aeCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  have hi : aeIdx = 190 := rfl
  rw [hi, conjA, gEl_eq, gElInv_eq, iotaA_K, repRows_eq, repXi_eq, repX_eq, CFSG.KC.F2W.mul_unpackW,
    CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW,
    CFSG.KC.F2W.mul_unpackW, qPts_contains]
  refine ⟨⟨⟨by decide, by decide⟩, unpack_eq h1⟩, ?_⟩
  rw [notB_eq] at h2
  exact h2

theorem ronan1 : ronanCheck1 = true := by
  unfold ronanCheck1
  simp only [Bool.and_eq_true]
  exact ⟨⟨ae, lvl2⟩, far⟩

open Certificates in
theorem c21152 : CFSG.Sporadic.Co1Patterson.Native.ronanCheck1 = true := ronan1

end CertificateChecks.KernelCo1P

end
