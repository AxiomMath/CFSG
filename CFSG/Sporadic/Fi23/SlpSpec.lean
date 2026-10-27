module

public import Certificates.Data.CFSGNative.Fi23.Slp
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

@[expose] noncomputable def slpG (gensG : ℤ → G) (words : Array (List ℤ)) (j : ℕ) : G :=
  wordG (fun z => if z.natAbs ≤ 2 then gensG z
    else if _h : z.natAbs - 3 < j then
      (if 0 < z then slpG gensG words (z.natAbs - 3) else (slpG gensG words (z.natAbs - 3))⁻¹)
    else 1) words[j]!
termination_by j

theorem slpG_eq (gensG : ℤ → G) (words : Array (List ℤ)) (j : ℕ) :
    slpG gensG words j = wordG (fun z => if z.natAbs ≤ 2 then gensG z
      else if z.natAbs - 3 < j then
        (if 0 < z then slpG gensG words (z.natAbs - 3) else (slpG gensG words (z.natAbs - 3))⁻¹)
      else 1) words[j]! := by
  rw [slpG]
  simp only [dite_eq_ite]

private def SlpInv (n : ℕ) (gens : ℤ → Table) (words : Array (List ℤ)) (m : ℕ) (L : Array Table) :
    Prop :=
  L.size = 2 * m ∧ ∀ j < m, L[2 * j]! = wordT n (slpLetterT gens L) words[j]! ∧
    L[2 * j + 1]! = invT n L[2 * j]!

theorem wordT_congr {n : ℕ} {f g : ℤ → Table} {w : List ℤ} (h : ∀ z ∈ w, f z = g z) :
    wordT n f w = wordT n g w := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    simp only [wordT, List.foldr_cons] at ih ⊢
    rw [h z List.mem_cons_self, ih fun z' hz' => h z' (List.mem_cons_of_mem _ hz')]

private theorem getElem!_push {α : Type*} [Inhabited α] (L : Array α) (x : α) {i : ℕ}
    (hi : i < L.size) : (L.push x)[i]! = L[i]! := by
  rw [getElem!_pos _ i (by simp; omega), Array.getElem_push_lt hi, getElem!_pos L i hi]

private theorem slpLetterT_extend {gens : ℤ → Table} {L L' : Array Table}
    (hext : ∀ i < L.size, L'[i]! = L[i]!) {z : ℤ}
    (hz : z.natAbs ≤ 2 ∨ 2 * (z.natAbs - 3) + 1 < L.size) :
    slpLetterT gens L' z = slpLetterT gens L z := by
  unfold slpLetterT
  split_ifs with h1 h2
  · rfl
  · exact hext _ (by omega)
  · exact hext _ (by omega)

theorem slpInv_full {n : ℕ} {gens : ℤ → Table} {words : Array (List ℤ)}
    (hok : slpOK words = true) :
    (slpLetters n gens words).size = 2 * words.size ∧
      ∀ j < words.size, (slpLetters n gens words)[2 * j]! =
        wordT n (slpLetterT gens (slpLetters n gens words)) words[j]! ∧
        (slpLetters n gens words)[2 * j + 1]! = invT n (slpLetters n gens words)[2 * j]! := by
  have hw : ∀ j < words.size, ∀ z ∈ words[j]!, z.natAbs ≤ 2 ∨ z.natAbs < j + 3 := by
    intro j hj z hz
    unfold slpOK at hok
    have := (allIn_eq_true.1 hok) j (Nat.zero_le _) hj
    rw [List.all_eq_true] at this
    have := this z hz
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at this
    exact this.2
  unfold slpLetters
  apply Array.foldl_induction (SlpInv n gens words)
  · exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · intro i L hL
    obtain ⟨hsz, hent⟩ := hL
    dsimp only
    generalize hTdef : wordT n (slpLetterT gens L) words[i] = T
    have hwi : words[i.1]! = words[i] := by
      rw [getElem!_pos words i.1 i.2]; rfl
    have hsz' : ((L.push T).push (invT n T)).size = 2 * (i.1 + 1) := by simp [hsz]; ring
    have hext : ∀ k < L.size, ((L.push T).push (invT n T))[k]! = L[k]! := by
      intro k hk
      rw [getElem!_push _ _ (by simp; omega), getElem!_push _ _ hk]
    have hT : ((L.push T).push (invT n T))[2 * i.1]! = T := by
      rw [getElem!_push _ _ (by simp; omega), getElem!_pos _ _ (by simp; omega)]
      simp [Array.getElem_push, hsz]
    have hTi : ((L.push T).push (invT n T))[2 * i.1 + 1]! = invT n T := by
      rw [getElem!_pos _ _ (by simp; omega)]
      simp [Array.getElem_push, hsz]
    refine ⟨hsz', fun j hj => ?_⟩
    by_cases hji : j < i.1
    · obtain ⟨h1, h2⟩ := hent j hji
      refine ⟨?_, ?_⟩
      · rw [hext _ (by omega), h1]
        apply wordT_congr
        intro z hz
        refine (slpLetterT_extend hext ?_).symm
        rcases hw j (by omega) z hz with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      · rw [hext _ (by omega), hext _ (by omega), h2]
    · obtain rfl : j = i.1 := by omega
      refine ⟨?_, ?_⟩
      · rw [hT, hwi]
        nth_rewrite 1 [← hTdef]
        apply wordT_congr
        intro z hz
        refine (slpLetterT_extend hext ?_).symm
        by_cases h2 : z.natAbs ≤ 2
        · exact Or.inl h2
        · rcases hw i.1 i.2 z (by rw [hwi]; exact hz) with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
      · rw [hTi, hT]

theorem rep_slpLetters (hn : n < 2 ^ 32) {gens : ℤ → Table} {gensG : ℤ → G}
    {words : Array (List ℤ)} (hgens : ∀ z, Rep n (gens z) (gensG z)) (hok : slpOK words = true)
    (hinv : ∀ j < words.size, invOK n (slpLetters n gens words)[2 * j]!
      (slpLetters n gens words)[2 * j + 1]! = true) :
    ∀ j < words.size, Rep n (slpLetters n gens words)[2 * j]! (slpG gensG words j) := by
  obtain ⟨-, hent⟩ := slpInv_full (n := n) (gens := gens) hok
  have hw : ∀ j < words.size, ∀ z ∈ words[j]!, z.natAbs ≤ 2 ∨ z.natAbs < j + 3 := by
    intro j hj z hz
    unfold slpOK at hok
    have := (allIn_eq_true.1 hok) j (Nat.zero_le _) hj
    rw [List.all_eq_true] at this
    have := this z hz
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at this
    exact this.2
  intro j hj
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [(hent j hj).1, slpG_eq]
    refine Rep.wordT hn _ fun z hz => ?_
    unfold slpLetterT
    by_cases h2 : z.natAbs ≤ 2
    · rw [ite_eq_left h2, ite_eq_left h2]
      exact hgens z
    · have hi : z.natAbs - 3 < j := by
        rcases hw j hj z hz with h | h
        · exact absurd h h2
        · omega
      rw [ite_eq_right h2, ite_eq_right h2, ite_eq_left hi]
      have hR := ih _ hi (by omega)
      by_cases hz0 : 0 < z
      · rw [ite_eq_left hz0, ite_eq_left hz0]
        exact hR
      · rw [ite_eq_right hz0, ite_eq_right hz0]
        exact Rep.inv_of_invOK hR (hinv _ (by omega))

theorem slpG_mem_closure {gensG : ℤ → G} {words : Array (List ℤ)} (hok : slpOK words = true)
    (hpure : slpPure words = true) :
    ∀ j < words.size, slpG gensG words j ∈
      Subgroup.closure ({slpG gensG words 0, slpG gensG words 1} : Set G) := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.lt_or_ge j 2 with h2 | h2
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [slpG_eq gensG words j]
      unfold wordG
      apply Subgroup.list_prod_mem
      intro x hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      have hz3 : 3 ≤ z.natAbs := by
        unfold slpPure at hpure
        have := (allIn_eq_true.1 hpure) j h2 hj
        rw [List.all_eq_true] at this
        simpa using this z hz
      have hzj : z.natAbs - 3 < j := by
        unfold slpOK at hok
        have := (allIn_eq_true.1 hok) j (Nat.zero_le _) hj
        rw [List.all_eq_true] at this
        have := this z hz
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
          at this
        omega
      rw [ite_eq_right (by omega), ite_eq_left hzj]
      have hm := ih _ hzj (by omega)
      split_ifs
      · exact hm
      · exact Subgroup.inv_mem _ hm

end CFSG.Sporadic.Fi23
