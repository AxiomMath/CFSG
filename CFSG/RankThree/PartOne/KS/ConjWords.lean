module

public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.RankThree.PartOne

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

variable {n : ℕ}

@[expose] def conjSel (n : ℕ) (c : ArrCert) (k : ℕ) (sel : List ℕ) : Array (Array ℕ) :=
  (sel.map fun j => conjA n c.pts[j]! c.pts[k]!).toArray

@[expose] def conjSelInv (n : ℕ) (c : ArrCert) (k : ℕ) (sel : List ℕ) : Array (Array ℕ) :=
  (sel.map fun j => conjA n c.pts[j]! (invCand n c.pts[k]!)).toArray

@[expose] def conjWordsOK (n : ℕ) (c : ArrCert) (gs : Array (Array ℕ)) (sel : ℕ → List ℕ)
    (W : ℕ → List (List ℤ)) : Bool :=
  allLt c.pts.size fun k => eqA n c.pts[k]! (idA n) ||
    ((sel k).all (fun j => decide (j < c.pts.size)) && (W k).length == gs.size &&
      allLt gs.size fun l => lettersOK (sel k).length (W k)[l]! &&
        eqA n gs[l]! (wordA n (conjSel n c k (sel k)) (conjSelInv n c k (sel k)) (W k)[l]!))

theorem isSimpleGroup_of_conjWordsOK {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (hc : enumOK n gs ps c = true) (hnt : 1 < c.pts.size)
    {sel : ℕ → List ℕ} {W : ℕ → List (List ℤ)} (h : conjWordsOK n c gs sel W = true) :
    IsSimpleGroup (Subgroup.closure (permsA n gs)) := by
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps hc
  set D := Subgroup.closure (permsA n gs)
  apply isSimpleGroup_of_conj_closure
  · by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hsub : (D : Set (Equiv.Perm (Fin n))) ⊆ {1} := fun g hg => hall g hg
    have h1 : Nat.card D ≤ 1 := by
      calc Nat.card D = (D : Set (Equiv.Perm (Fin n))).ncard := (Nat.card_coe_set_eq _).symm
        _ ≤ ({1} : Set (Equiv.Perm (Fin n))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 1 := Set.ncard_singleton _
    omega
  · intro e he he1
    obtain ⟨k, hk, rfl⟩ := (hmem e).1 he
    have hck := allLt_spec h hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      decide_eq_true_eq] at hck
    rcases hck with hid | ⟨⟨hsel, hlen⟩, hw⟩
    · exact absurd ((eqA_iff (rep_of_validA (hval k hk)) rep_idA).1 hid) he1
    set m := (sel k).length
    let f : ℕ → Equiv.Perm (Fin n) := fun h =>
      permOfArr n c.pts[(sel k).getD h 0]! * permOfArr n c.pts[k]! *
        (permOfArr n c.pts[(sel k).getD h 0]!)⁻¹
    have hget : ∀ h (hh : h < m), (sel k).getD h 0 = (sel k)[h] := fun h hh => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh]
    have hj : ∀ h < m, (sel k).getD h 0 < c.pts.size := fun h hh =>
      hsel _ (by rw [hget h hh]; exact List.getElem_mem hh)
    have hS : ∀ h < m, Rep n (conjSel n c k (sel k))[h]! (f h) := by
      intro h hh
      have e : (conjSel n c k (sel k))[h]! = conjA n c.pts[(sel k).getD h 0]! c.pts[k]! := by
        rw [getElem!_pos _ h (by simpa [conjSel] using hh)]
        simp [conjSel, hget h hh, List.getElem?_eq_getElem hh]
      rw [e]
      exact rep_conjA (hval _ (hj h hh)) (rep_of_validA (hval k hk))
    have hSinv : ∀ h < m, Rep n (conjSelInv n c k (sel k))[h]! (f h)⁻¹ := by
      intro h hh
      have e : (conjSelInv n c k (sel k))[h]! =
          conjA n c.pts[(sel k).getD h 0]! (invCand n c.pts[k]!) := by
        rw [getElem!_pos _ h (by simpa [conjSelInv] using hh)]
        simp [conjSelInv, hget h hh, List.getElem?_eq_getElem hh]
      rw [e]
      have hr := rep_conjA (hval _ (hj h hh)) (rep_inv_of_validA (hval k hk))
      have e2 : (f h)⁻¹ = permOfArr n c.pts[(sel k).getD h 0]! * (permOfArr n c.pts[k]!)⁻¹ *
          (permOfArr n c.pts[(sel k).getD h 0]!)⁻¹ := by
        simp only [f]
        group
      rw [e2]
      exact hr
    have hfD : ∀ h < m, f h ∈ Subgroup.closure
        {y | ∃ g ∈ D, g * permOfArr n c.pts[k]! * g⁻¹ = y} := fun h hh =>
      Subgroup.subset_closure ⟨_, (hmem _).2 ⟨_, hj h hh, rfl⟩, rfl⟩
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hwl := allLt_spec hw hl
    rw [Bool.and_eq_true] at hwl
    obtain ⟨hlet, heq⟩ := hwl
    have hrep := rep_wordA (n := n) (gs := f) hS hSinv _ hlet
    have hg : permOfArr n gs[l]! = Quiver.SchreierGraph.evalWord (fun h : Fin m => f h)
        (toLetters m (W k)[l]!) :=
      (eqA_iff (rep_of_validA (enumOK_gens_valid hc hl)) hrep).1 heq
    change permOfArr n gs[l]! ∈ _
    rw [hg]
    refine (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
    rintro _ ⟨h, rfl⟩
    exact hfD h h.2

end CFSG.RankThree.PartOne

end
