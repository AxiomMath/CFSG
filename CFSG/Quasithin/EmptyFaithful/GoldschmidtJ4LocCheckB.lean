module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import Certificates.Certificate4177

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4.QT

theorem mem_stepW {ℓ : Int} {W : List Nat} {c : Nat} : c ∈ stepW ℓ W ↔ ∃ x ∈ W, act ℓ x = c := by
  simp [stepW, mem_srt]

@[expose] def trioL : Set (List ℕ) := {W | W.Pairwise (· < ·) ∧ W.toFinset ∈ TrioOct}

theorem pairwise_srt (L : List ℕ) : (srt L).Pairwise (· ≤ ·) := by
  have hs := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) L
  exact hs.imp (fun h => by simpa using h)

theorem toFinset_srt (L : List ℕ) : (srt L).toFinset = L.toFinset := by
  ext x
  simp only [List.mem_toFinset, mem_srt]

theorem V0L_toFinset : V0L.toFinset = V0F := by
  ext x
  simp [V0L, V0F]

theorem V0L_mem_trioL : V0L ∈ trioL :=
  ⟨by decide, by rw [V0L_toFinset]; exact V0F_mem_TrioOct⟩

theorem trioL_ext {A B : List ℕ} (hA : A ∈ trioL) (hB : B ∈ trioL)
    (h : A.toFinset = B.toFinset) : A = B :=
  List.Perm.eq_of_pairwise (le := (· < ·)) (fun a b _ _ h1 h2 => absurd (h1.trans h2) (lt_irrefl a))
    hA.1 hB.1 ((List.perm_ext_iff_of_nodup (hA.1.imp ne_of_lt) (hB.1.imp ne_of_lt)).2
      (fun x => by rw [← List.mem_toFinset, h, List.mem_toFinset]))

theorem trioL_eq_V0L {W : List ℕ} (hW : W ∈ trioL) (h : W.toFinset = V0F) : W = V0L :=
  trioL_ext hW V0L_mem_trioL (h.trans V0L_toFinset.symm)

theorem trioL_props {W : List ℕ} (hW : W ∈ trioL) :
    W.length = 8 ∧ (∀ c ∈ W, c < 2048) ∧ W.Nodup ∧ 0 ∈ W ∧ ∀ x ∈ W, ∀ y ∈ W, x ^^^ y ∈ W := by
  obtain ⟨h8, h0, hlt, hx⟩ := Certificates.certificate4174.2.2.2.2.2.1 _ hW.2
  have hnd : W.Nodup := hW.1.imp ne_of_lt
  refine ⟨?_, fun c hc => hlt c (List.mem_toFinset.2 hc), hnd, List.mem_toFinset.1 h0,
    fun x hx' y hy => List.mem_toFinset.1 (hx x (List.mem_toFinset.2 hx') y
      (List.mem_toFinset.2 hy))⟩
  rw [← List.toFinset_card_of_nodup hnd, h8]

theorem srt_mem_trioL {L : List ℕ} (hlen : L.length = 8)
    (h : L.toFinset ∈ TrioOct) : srt L ∈ trioL := by
  have h8 := (Certificates.certificate4174.2.2.2.2.2.1 _ h).1
  have hl : (srt L).length = L.length := (List.mergeSort_perm L _).length_eq
  have hc : (srt L).toFinset.card = (srt L).length := by
    rw [toFinset_srt, h8, hl, hlen]
  have hnd : (srt L).Nodup :=
    Multiset.coe_nodup.1 (Multiset.toFinset_card_eq_card_iff_nodup.1 (by
      rw [Multiset.coe_card]
      exact hc))
  refine ⟨((pairwise_srt L).and hnd).imp fun h => lt_of_le_of_ne h.1 h.2, ?_⟩
  rw [toFinset_srt]
  exact h

theorem trio_prop :
    V0L ∈ trioL ∧ ∀ W ∈ trioL, W.length = 8 ∧ (∀ c ∈ W, c < 2048) ∧ W.Nodup ∧
      ∀ ℓ ∈ letters, stepW ℓ W ∈ trioL := by
  refine ⟨V0L_mem_trioL, fun W hW => ?_⟩
  obtain ⟨h8, hlt, hnd, -⟩ := trioL_props hW
  refine ⟨h8, hlt, hnd, fun ℓ hℓ => srt_mem_trioL (by rw [List.length_map, h8]) ?_⟩
  have e : (W.map (act ℓ)).toFinset = W.toFinset.image (act ℓ) := by
    ext x
    simp
  rw [e]
  exact image_mem_TrioOct hW.2 hℓ

theorem trioL_finite_ncard : trioL.Finite ∧ trioL.ncard ≤ 3795 := by
  have hT : TrioOct.Finite := Set.finite_of_ncard_ne_zero (by
    rw [Certificates.certificate4174.2.2.2.2.1]
    decide)
  have hinj : Set.InjOn List.toFinset trioL := fun A hA B hB h => trioL_ext hA hB h
  have himg : List.toFinset '' trioL ⊆ TrioOct := by
    rintro _ ⟨W, hW, rfl⟩
    exact hW.2
  refine ⟨Set.Finite.of_finite_image (hT.subset himg) hinj, ?_⟩
  rw [← Certificates.certificate4174.2.2.2.2.1]
  exact Set.ncard_le_ncard_of_injOn List.toFinset (fun W hW => hW.2) hinj hT

theorem mem_xset {B t : List Nat} : t ∈ xset B ↔ t ∈ tabL ∧ compT t t = idT ∧
    (∀ c ∈ B, actT t c = c) ∧ ∀ c < 2048, (actT t c ^^^ c) ∈ B := by
  simp only [xset, List.mem_filter, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, List.contains_iff_mem, and_assoc]

theorem x_bound {B : List Nat} (hB : B ∈ subs)
    (h16 : 16 ≤ B.length) : 8 * xcnt B ≤ B.length ∧
    (8 * xcnt B = B.length → ∀ W ∈ trioL, (∀ w ∈ W, w ∈ B) → W = V0L) := by
  have h := Certificates.certificate4174.2.2.2.2.2.2.1 B hB h16
  exact ⟨h.1, fun heq W hW hWB => trioL_eq_V0L hW
    (h.2 heq _ hW.2 fun w hw => hWB w (List.mem_toFinset.1 hw))⟩

theorem small_sub {B : List Nat} (hB : B ∈ subs)
    (h : B.length ≤ 2) : B = [0] ∨ B = z0L :=
  Certificates.certificate4174.2.2.2.2.2.2.2.1.2.2 B hB h

theorem above {B : List Nat} (hB : B ∈ subs) (h : 3 ≤ B.length)
    {W : List Nat} (hW : W ∈ trioL) (hsub : ∀ b ∈ B, b ∈ W) : W = V0L :=
  trioL_eq_V0L hW (Certificates.certificate4174.2.2.2.2.2.2.2.2 B hB h _ hW.2
    fun c hc => List.mem_toFinset.2 (hsub c hc))

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2 in
theorem i5_prop :
    (∀ p ∈ ([(965, 1243), (1979, 1979), (165, 165)] : List (ℕ × ℕ)),
      mulRows (mulRows (pathRows (repPaths.getD 5 []))
        (etaRows (uTab (locMats ()) (locInvs ())) 11 p.1))
        (invRows (pathRows (repPaths.getD 5 []))) =
        etaRows (uTab (locMats ()) (locInvs ())) 11 p.2) ∧ i5Masks ∈ trioL := by
  refine ⟨Certificates.certificate4177.1, ?_⟩
  have h := Certificates.certificate4177.2
  rw [i5Masks, toFinset_srt] at h
  exact srt_mem_trioL (by simp [i5Pairs]) h

end CFSG.Quasithin.J4Loc
