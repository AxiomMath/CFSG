module

public import Certificates.Kernel.Co1P.C21157
public import Certificates.Kernel.Co1P.Chk21158

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KD.Co1B CFSG.KLie.CT
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native
  CFSG.Sporadic.Co1Patterson.TwistNative CertificateChecks.KernelCo1B

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem allN_iff (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i h => absurd h (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (by omega)⟩

theorem QG_eq : QG = IQK := rfl

theorem twoAQ_get {l : Nat} (hl : l < 8) :
    CFSG.Sporadic.Co1Block.twoAQRows.toArray[l]! = unpackR 24 (getL 0 QG l) := by
  have hl' : l < IQK.length := by rw [show IQK.length = 8 from rfl]; exact hl
  rw [twoAQ_eq, getElem!_pos _ l (by simpa using hl'), List.getElem_toArray,
    List.getElem_map, QG_eq, CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem hl']
  rfl

theorem qPts_contains (X : Nat) : qPts.contains (unpackR 24 X) = memQ X := by
  have hT : CFSG.Sporadic.Co1Block.twoAQTree = CFSG.Sporadic.Co1Block.gtOfMasks
      CFSG.Sporadic.Co1Block.twoAQRows.toArray (treeArr (recsT CFSG.Sporadic.Co1Block.twoAQMasks)) := by
    rw [CFSG.Sporadic.Co1Block.twoAQTree, treeOfMasks_eq]
    rfl
  obtain ⟨hs, hg⟩ := gtOfMasks_get (fun l hl => twoAQ_get hl) treeAQ_ok
  have hl := walk_length treeAQ_ok
  rw [qPts, Std.HashSet.contains_ofList, hT, toList_eq_map (L := QL) (by rw [hs]; exact hl.symm)
    (fun j hj => by rw [hg j (by rw [← hl]; exact hj)]; rfl), contains_map_unpack]
  rfl

theorem qwW_eq (e : Nat) : qwW e = qwK e := by
  unfold qwW qwK
  simp only [mulWK, CFSG.KC.F2W.mulW_eq, mulK]

theorem ypW_eq (c : Nat) : ypW c = ypK c := by
  unfold ypW ypK
  simp only [qwW_eq, mulWK, CFSG.KC.F2W.mulW_eq, mulK]

theorem yprodRow_W (c : Nat) : yprodRow c = unpackR 24 (ypW c) := by
  rw [yprodRow_q, ypW_eq]

theorem yRow_W (i : Nat) : yRow i = unpackR 24 (qwW (yBits.getD i 0)) := by
  rw [yRow_q, qwW_eq]

theorem qRows_eq : qRows = unpackR 24 (wK 64) := wRows_eq (by decide)

theorem pRows_eq : pRows = unpackR 24 (wK 128) := wRows_eq (by decide)

theorem qae_at (y : Nat) :
    (!qPts.contains (mul (mul (repXi 1) (unpackR 24 y)) (repX 1)) || unpackR 24 y == one ||
      unpackR 24 y == qRows || unpackR 24 y == pRows || unpackR 24 y == mul qRows pRows) =
      qaeAt (wK 64) (wK 128) y := by
  rw [repXi_eq, repX_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, qPts_contains, CFSG.KC.Co1B.one_eq,
    qRows_eq, pRows_eq, CFSG.KC.F2W.mul_unpackW, beq_unpack, beq_unpack, beq_unpack, beq_unpack]
  simp only [qaeAt, orB_eq, notB_eq, Bool.or_assoc]
  rfl

theorem qae : qaeOK = true := by
  have h := (allN_iff _ _).1 qae_chk
  unfold qaeOK
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true (h c (List.mem_range.1 hc))
  rw [yprodRow_W, iotaA_K, CFSG.KC.F2W.mul_unpackW]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨(qae_at _).trans h1, (qae_at _).trans h2⟩

theorem eqK_refl (A : Nat) : eqK A A = true := Nat.beq_refl _

theorem unpack_eq {A B : Nat} (h : eqK A B = true) : unpackR 24 A = unpackR 24 B :=
  eq_of_beq ((beq_unpack A B).trans h)

theorem edge : edgeElemOK = true := by
  have hk : edgeK (getL oneK GDS 94) (getL oneK GDIS 94) (getL oneK GDS 92) (getL oneK GDIS 92) =
      true := edge_chk
  unfold edgeK at hk
  simp only [andB_eq, Bool.and_eq_true] at hk
  obtain ⟨e1, e2, e3, e4, e5, hcj, hu⟩ := hk
  unfold conjEK at hcj
  simp only [andB_eq, Bool.and_eq_true] at hcj
  obtain ⟨⟨⟨hc1, hc2⟩, hsq⟩, hconj⟩ := hcj
  have hinv : inv (unpackR 24 (repK 1)) = unpackR 24 (repK 1) := by
    apply inv_sound'
    rw [andB_eq, andB_eq, hc1, hsq]
    rfl
  have hs := edge_small
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩ := hs
  unfold edgeElemOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨s1, s2⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, s3⟩, ?_⟩, by simpa using s4⟩,
    by simpa using s5⟩
  · rw [gEl_eq, gElInv_eq, pRows_eq, qRows_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW,
      CFSG.KC.F2W.mul_unpackW]
    exact unpack_eq e1
  · rw [y0Idx, gEl_eq, gElInv_eq, qRows_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
    exact unpack_eq e2
  · rw [y0Idx, gEl_eq, gElInv_eq, pRows_eq, qRows_eq, CFSG.KC.F2W.mul_unpackW,
      CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
    exact unpack_eq e3
  · rw [qRows_eq, yprodRow_W, iotaA_K, CFSG.KC.F2W.mul_unpackW]
    exact unpack_eq e4
  · rw [pRows_eq, yprodRow_W]
    exact unpack_eq e5
  · unfold CFSG.Sporadic.Co1Patterson.TwistNative.conjOK
    rw [repRows_eq, hinv, CFSG.KC.F2W.mul_unpackW, CFSG.KC.Co1B.one_eq, beq_unpack]
    have hc := (allN_iff _ _).1 hconj
    refine Bool.and_eq_true_iff.2 ⟨?_, List.all_eq_true.2 fun k hk => ?_⟩
    · have : mulK (repK 1) (repK 1) = oneK := Nat.eq_of_beq_eq_true hsq
      rw [show CFSG.KC.F2W.mulW 24 (repK 1) (repK 1) = mulK (repK 1) (repK 1) from
        CFSG.KC.F2W.mulW_eq _ _ _, this]
      exact (eqK_refl oneK)
    · have h1 := hc k (List.mem_range.1 hk)
      rw [yRow_W, yprodRow_W, iotaA_K]
      simp only [CFSG.KC.F2W.mul_unpackW, beq_unpack, orB_eq] at h1 ⊢
      exact h1
  · rw [List.all_eq_true]
    intro c hc
    have h1 := List.all_eq_true.1 hu c hc
    rw [yprodRow_W, repRows_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW, beq_unpack]
    exact h1

open CFSG.EvenSmallLie.OmegaEight (bNat) in
theorem stabCond_eq (y₁ y₂ : Nat) :
    stabCond y₁ y₂ = (stabA y₁ && stabB y₂ && bNat y₁ y₂ == bNat 1 16) := by
  unfold stabCond stabA stabB
  have : (uBasis.all fun c => bNat y₁ c == bNat 1 c && bNat y₂ c == bNat 16 c) =
      ((uBasis.all fun c => bNat y₁ c == bNat 1 c) && uBasis.all fun c => bNat y₂ c == bNat 16 c) := by
    simp only [uBasis, List.all_cons, List.all_nil, Bool.and_true]
    cases bNat y₁ 2 == bNat 1 2 <;> cases bNat y₁ 5 == bNat 1 5 <;> cases bNat y₁ 9 == bNat 1 9 <;>
      cases bNat y₁ 32 == bNat 1 32 <;> cases bNat y₁ 64 == bNat 1 64 <;>
      cases bNat y₁ 144 == bNat 1 144 <;> simp
  rw [this]
  cases (uBasis.all fun c => bNat y₁ c == bNat 1 c) <;>
    cases (uBasis.all fun c => bNat y₂ c == bNat 16 c) <;>
    cases CFSG.EvenSmallLie.OmegaEight.qNat y₁ == CFSG.EvenSmallLie.OmegaEight.qNat 1 <;>
    cases CFSG.EvenSmallLie.OmegaEight.qNat y₂ == CFSG.EvenSmallLie.OmegaEight.qNat 16 <;> simp

theorem stab : stabOK = true := by
  have h := stab_chk
  unfold stabF at h
  unfold stabOK
  rw [List.all_eq_true]
  intro y₁ hy₁
  rw [List.all_eq_true]
  intro y₂ hy₂
  rw [stabCond_eq]
  by_cases hA : stabA y₁ = true
  · by_cases hB : stabB y₂ = true
    · have h1 := List.all_eq_true.1 h y₁ (List.mem_filter.2 ⟨hy₁, hA⟩)
      have h2 := List.all_eq_true.1 h1 y₂ (List.mem_filter.2 ⟨hy₂, hB⟩)
      rw [hA, hB]
      simpa using h2
    · rw [Bool.eq_false_iff.2 hB]
      simp
  · rw [Bool.eq_false_iff.2 hA]
    simp

open Certificates in
theorem c21158 : CFSG.Sporadic.Co1Patterson.Native.qaeOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.edgeElemOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.stabOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.perpOK = true := ⟨qae, edge, stab, perp_chk⟩

end CertificateChecks.KernelCo1P

end
