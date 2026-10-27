module

public import Certificates.Kernel.Co1P.C21152
public import Certificates.Kernel.Co1P.Chk21153
public import Certificates.Kernel.Co1P.Chk21153T
public import Certificates.Kernel.Co1P.Chk21153L0
public import Certificates.Kernel.Co1P.Chk21153L1
public import CFSG.Certificates.Kernel.Co1PTextSound

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native CertificateChecks.KernelCo1B

theorem ord6_eq (M : Nat) : ord6 (unpackR 24 M) = ord6K M := by
  unfold ord6 ord6K
  simp only [CFSG.KC.F2W.mul_unpackW, CFSG.KC.Co1B.one_eq, beq_unpack]
  rfl

theorem dcls_eq (X : Nat) : dcls (ptSet orbE) (unpackR 24 X) = dclsK X := by
  unfold dcls dclsK
  simp only [iotaA_K, beq_unpack, orbE_mem, CFSG.KC.F2W.mul_unpackW, ord6_eq]
  rfl

theorem atK_eq {k : Nat} (hk : k < 12600) (B : Nat) :
    atK orbE k (unpackR 24 B) = unpackR 24 (atP k B) := by
  rw [atK, xeK_eq hk, xeiK_eq hk, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
  rfl

theorem nodesL_ne (t : Nat) : nodesL t ≠ [] := by
  unfold nodesL nT
  split <;> simp

theorem parsL_ne (t : Nat) : parsL t ≠ [] := by
  unfold parsL nT
  split <;> simp

theorem nodesL_get {t r : Nat} (hr : r < nT t) : (nodesL t)[r]?.getD 0 = NT t r := by
  rw [nodesL, List.getElem?_map, List.getElem?_range hr]
  rfl

theorem parsL_get {t r : Nat} (hr : r < nT t) : (parsL t)[r]?.getD 0 = PT t r := by
  rw [parsL, List.getElem?_map, List.getElem?_range hr]
  rfl

theorem tree_eq {t : Nat} (ht : t < 2) : lvl3Tree t = (nodesL t, parsL t) := by
  interval_cases t
  · unfold lvl3Tree
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [text0n, text0p, parseNats_natsC (nodesL_ne 0), parseNats_natsC (parsL_ne 0)]
  · unfold lvl3Tree
    simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    rw [text1n, text1p, parseNats_natsC (nodesL_ne 1), parseNats_natsC (parsL_ne 1)]

theorem witL_mem {t : Nat} {p : Nat × Nat} :
    p ∈ witL t ↔ p.1 < 12600 ∧ WTt t p.1 ≠ 0 ∧ p.2 = WTt t p.1 - 1 := by
  unfold witL
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨m, hm, e⟩
    rw [List.mem_range] at hm
    by_cases hw : WTt t m = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hw)] at e
      exact absurd e (by simp)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hw)] at e
      cases e
      exact ⟨hm, hw, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p.1, List.mem_range.2 h1, ?_⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ← h3]

theorem witL_pairwise (t : Nat) : (witL t).Pairwise fun a b => (a.1 == b.1) = false := by
  unfold witL
  rw [List.pairwise_filterMap]
  refine (List.pairwise_lt_range (n := 12600)).imp fun {a a'} h b hb b' hb' => ?_
  by_cases hw : WTt t a = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hw)] at hb
    exact absurd hb (by simp)
  · by_cases hw' : WTt t a' = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hw')] at hb'
      exact absurd hb' (by simp)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hw), Option.some.injEq] at hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false hw'), Option.some.injEq] at hb'
      rw [← hb, ← hb']
      simpa using Nat.ne_of_lt h

theorem witL_ne {t : Nat} (ht : t < 2) : witL t ≠ [] := by
  intro e
  interval_cases t
  · have h : WTt 0 2 = 2 := by decide +kernel
    have hm : ((2, 1) : Nat × Nat) ∈ witL 0 := witL_mem.2 ⟨by decide, by rw [h]; decide, by rw [h]⟩
    rw [e] at hm
    exact List.not_mem_nil hm
  · have h : (witL 1).length ≠ 0 := by decide +kernel
    rw [e] at h
    exact h rfl

theorem wit_eq {t : Nat} (ht : t < 2) : lvl3Wit t = Std.HashMap.ofList (witL t) := by
  interval_cases t
  · unfold lvl3Wit
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [wit0_text, parsePairs_pairsC (witL_ne (by decide))]
  · unfold lvl3Wit
    simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    rw [wit1_text, parsePairs_pairsC (witL_ne (by decide))]

theorem wit_get {t m : Nat} (hm : m < 12600) :
    (Std.HashMap.ofList (witL t))[m]? = if WTt t m = 0 then none else some (WTt t m - 1) := by
  by_cases hw : WTt t m = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hw)]
    apply Std.HashMap.getElem?_ofList_of_contains_eq_false
    rw [Bool.eq_false_iff]
    intro hc
    rw [List.contains_iff_mem, List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    exact (witL_mem.1 hp).2.1 hw
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hw)]
    exact Std.HashMap.getElem?_ofList_of_mem (k := m) (by simp) (witL_pairwise t)
      (witL_mem.2 ⟨hm, hw, rfl⟩)

theorem treeIn_of_nodes {ns ps : List Nat} {P Q PK : Nat → Bool} (hP : ∀ n < 12600, P n = PK n)
    (h0 : 0 < ns.length) (hl : ps.length = ns.length)
    (hnode : ∀ r < ns.length, ns[r]?.getD 0 < 12600 ∧ PK (ns[r]?.getD 0) = true ∧
      (r = 0 ∨ (ps[r]?.getD 0 < r ∧ adjP (xeP (ns[r]?.getD 0)) (xeiP (ns[r]?.getD 0))
        (ptPE (ns[ps[r]?.getD 0]?.getD 0)) = true)))
    (hQ : ∀ k < 12600, (!(Q k) || ns.contains k) = true) :
    treeIn orbE (ptSet orbE) ns ps P Q = true := by
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

theorem tree_all {t : Nat} (ht : t < 2) : ∀ r < nT t, treeAtK t r = true := by
  interval_cases t
  · exact chunks_all (f := treeAtK 0) (N := 10710) (nc := 168) (by decide) fun c hc => Tree0.all c hc
  · exact chunks_all (f := treeAtK 1) (N := 7950) (nc := 125) (by decide) fun c hc => Tree1.all c hc

theorem far_all {t : Nat} (ht : t < 2) : ∀ k < 12600, farAtK t (MSt t) k = true := by
  have hc : ∀ c < 197, chunkK 12600 (farAtK t (MSt t)) c = true := by
    intro c hc
    have h : farChunk t c = true := by
      interval_cases t
      · exact Far0.all c hc
      · exact Far1.all c hc
    unfold farChunk at h
    rw [strictB_eq'] at h
    exact h
  exact chunks_all (by decide) hc

theorem masks_eq {t : Nat} (ht : t < 2) : MSt t = bitsOf (nodesL t) := by
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true masks_ok
  interval_cases t
  · exact (Nat.eq_of_beq_eq_true h1).symm
  · exact (Nat.eq_of_beq_eq_true h2).symm

theorem far_parts {t k : Nat} (ht : t < 2) (hk : k < 12600) :
    (dclsK (atP k (RF t)) = 3 ∨ (nodesL t).contains k = true) ∧
      (fun d => orB (orB (Nat.beq d 1) (Nat.beq d 2)) (andB (Nat.beq d 3)
          ((fun w => andB (notB (Nat.beq w 0)) ((fun kk => andB (Nat.blt kk 12600)
            (andB (Nat.beq (dclsK (atP kk (RF t))) 2)
              (Nat.beq (dclsK (atP kk (mulWK (mulWK (mulWK (RFX t) (xeP k)) AL)
                (mulWK (xeiP k) (RFXi t))))) 2))) (w - 1))) (WTt t k))))
        (dclsK (mulWK (mulWK (mulWK (RFX t) (xeP k)) AL) (mulWK (xeiP k) (RFXi t)))) = true := by
  have h := far_all ht k hk
  unfold farAtK at h
  rw [strictB_eq', strictB_eq', strictB_eq'] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
  refine ⟨?_, h2⟩
  rcases orB_true h1 with e | e
  · exact Or.inl (Nat.eq_of_beq_eq_true e)
  · refine Or.inr ?_
    rw [masks_eq ht, bit_bitsOf] at e
    exact e

theorem ronan2 {t : Nat} (ht : t < 2) : ronanCheck2 t = true := by
  unfold ronanCheck2
  simp only [Bool.and_eq_true]
  rw [tree_eq ht, wit_eq ht]
  dsimp only
  refine ⟨?_, ?_⟩
  · refine treeIn_of_nodes (PK := fun n => Nat.beq (dclsK (atP n (RF t))) 2) (fun n hn => ?_)
      (by rw [nodesL, List.length_map, List.length_range]; interval_cases t <;> decide)
      (by rw [parsL, nodesL, List.length_map, List.length_map]) (fun r hr => ?_) (fun k hk => ?_)
    · rw [repRows_eq, atK_eq hn, dcls_eq]
      rfl
    · have hr' : r < nT t := by rw [nodesL, List.length_map, List.length_range] at hr; exact hr
      have h := tree_all ht r hr'
      unfold treeAtK at h
      obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true h
      obtain ⟨h3, h4⟩ := CFSG.KC.TreeK.andB_true h1
      rw [nodesL_get hr', parsL_get hr']
      refine ⟨lt_of_blt' h3, h4, ?_⟩
      rcases orB_true h2 with e | e
      · exact Or.inl (Nat.eq_of_beq_eq_true e)
      · obtain ⟨e1, e2⟩ := CFSG.KC.TreeK.andB_true e
        have hp := lt_of_blt' e1
        refine Or.inr ⟨hp, ?_⟩
        rw [nodesL_get (by omega)]
        exact e2
    · rw [repRows_eq, atK_eq hk, dcls_eq]
      rcases (far_parts ht hk).1 with e | e
      · unfold RF at e
        rw [e]
        rfl
      · rw [e, Bool.or_true]
  · rw [orbE_size', List.all_eq_true]
    intro m hm
    have hm' := List.mem_range.1 hm
    have h := (far_parts ht hm').2
    simp only [nbrX, repP, vtxR, conjA, xeK_eq hm', xeiK_eq hm', repX_eq, repXi_eq, iotaA_K, repRows_eq,
      CFSG.KC.F2W.mul_unpackW, dcls_eq, wit_get hm']
    simp only [RF, RFX, RFXi, mulWK, orB_eq, andB_eq, notB_eq] at h
    by_cases hw : WTt t m = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hw)]
      rw [hw] at h
      simpa using h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hw)]
      dsimp only
      rw [← Nat.beq_eq, Bool.not_eq_true] at hw
      rw [hw] at h
      by_cases hkk : WTt t m - 1 < 12600
      · rw [atK_eq hkk, atK_eq hkk, dcls_eq, dcls_eq]
        have e : Nat.blt (WTt t m - 1) 12600 = true := by rw [Nat.blt_eq]; exact hkk
        rw [e] at h
        simpa [decide_eq_true hkk] using h
      · have e : Nat.blt (WTt t m - 1) 12600 = false := by
          rw [← Bool.not_eq_true, Nat.blt_eq]; exact hkk
        rw [e] at h
        simpa [hkk] using h

open Certificates in
theorem c21153 : CFSG.Sporadic.Co1Patterson.Native.ronanCheck2 0 = true ∧
    CFSG.Sporadic.Co1Patterson.Native.ronanCheck2 1 = true := ⟨ronan2 (by decide), ronan2 (by decide)⟩

end CertificateChecks.KernelCo1P

end
