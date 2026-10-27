module

public import CFSG.Quasithin.H13.U3S1347P
public import CFSG.Quasithin.H13.A6Model4
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Quasithin.H13.U3S1347QK

public section

namespace CFSG.Quasithin.H13.U3

namespace S6Out

open Equiv CFSG.Quasithin.H13.A6

@[expose] def d6 : Fin 16 → Perm (Fin 6) := ![1, swap 4 5, swap 2 3, swap 2 3 * swap 4 5,
  swap 0 1, swap 0 1 * swap 4 5, swap 0 1 * swap 2 3, swap 0 1 * swap 2 3 * swap 4 5,
  swap 0 2 * swap 1 3, swap 0 2 * swap 1 3 * swap 4 5, swap 0 3 * swap 0 1 * swap 0 2,
  swap 0 3 * swap 0 1 * swap 0 2 * swap 4 5, swap 0 2 * swap 0 1 * swap 0 3,
  swap 0 2 * swap 0 1 * swap 0 3 * swap 4 5, swap 0 3 * swap 1 2,
  swap 0 3 * swap 1 2 * swap 4 5]

@[expose] def tw : Fin 16 → Perm (Fin 6) := ![1, swap 0 1 * swap 2 3 * swap 4 5,
  swap 0 2 * swap 1 3 * swap 4 5, swap 0 3 * swap 1 2, swap 0 3 * swap 1 2 * swap 4 5,
  swap 0 2 * swap 1 3, swap 0 1 * swap 2 3, swap 4 5, swap 2 3 * swap 4 5, swap 0 1,
  swap 0 2 * swap 0 1 * swap 0 3, swap 0 3 * swap 0 1 * swap 0 2 * swap 4 5,
  swap 0 3 * swap 0 1 * swap 0 2, swap 0 2 * swap 0 1 * swap 0 3 * swap 4 5,
  swap 0 1 * swap 4 5, swap 2 3]

theorem mem_d6 : ∀ σ : Perm (Fin 6), InD6 σ → ∃ i, d6 i = σ := by
  decide +kernel

theorem phi_inv_d6 : ∀ i : Fin 16, phi (cc⁻¹ * d6 i * cc) = tw i := by
  decide +kernel

@[expose] def w4List : List P6 := [
  Multiplicative.ofAdd ![0, 0, 0, 0, 0, 0],
  Multiplicative.ofAdd ![0, 0, 0, 1, 1, 0],
  Multiplicative.ofAdd ![0, 0, 1, 0, 1, 0],
  Multiplicative.ofAdd ![0, 0, 1, 1, 0, 0],
  Multiplicative.ofAdd ![0, 1, 0, 0, 1, 0],
  Multiplicative.ofAdd ![0, 1, 0, 1, 0, 0],
  Multiplicative.ofAdd ![0, 1, 1, 0, 0, 0],
  Multiplicative.ofAdd ![0, 1, 1, 1, 1, 0],
  Multiplicative.ofAdd ![1, 0, 0, 0, 1, 0],
  Multiplicative.ofAdd ![1, 0, 0, 1, 0, 0],
  Multiplicative.ofAdd ![1, 0, 1, 0, 0, 0],
  Multiplicative.ofAdd ![1, 0, 1, 1, 1, 0],
  Multiplicative.ofAdd ![1, 1, 0, 0, 0, 0],
  Multiplicative.ofAdd ![1, 1, 0, 1, 1, 0],
  Multiplicative.ofAdd ![1, 1, 1, 0, 1, 0],
  Multiplicative.ofAdd ![1, 1, 1, 1, 0, 0]]

theorem mem_w4List : ∀ x : P6, InW4 x ↔ x ∈ w4List := by
  decide +kernel

@[expose] def fixCount (S : List (Perm (Fin 6))) : ℕ :=
  (w4List.filter fun x => decide (∀ s ∈ S, act4f s x = x)).length

theorem fix_one : ∀ i : Fin 16, d6 i * d6 i = 1 → d6 i ≠ 1 →
    fixCount [d6 i] * fixCount [tw i] ≤ 32 := by
  have hp : ∀ i : Fin 16, S6OutK.DTC.getD i 0 =
      S6OutK.pk (CFSG.Permutation.FinPack.enc (d6 i)) (CFSG.Permutation.FinPack.enc (tw i)) := by
    decide +kernel
  have hW : (w4List.map A6L76EK.vc6 == S6OutK.W4Q) = true := by decide +kernel
  intro i h1 h2
  unfold fixCount
  exact S6OutK.fix1_of hW hp i h1 h2

@[expose] def InvPair (i j : Fin 16) : Prop :=
  d6 i * d6 i = 1 ∧ d6 i ≠ 1 ∧ d6 j * d6 j = 1 ∧ d6 j ≠ 1 ∧ d6 i ≠ d6 j ∧
    d6 i * d6 j = d6 j * d6 i

instance (i j : Fin 16) : Decidable (InvPair i j) := by unfold InvPair; infer_instance

theorem fix_two : ∀ i j : Fin 16, InvPair i j →
    fixCount [d6 i, d6 j] * fixCount [tw i, tw j] ≤ 16 := by
  have hp : ∀ i : Fin 16, S6OutK.DTC.getD i 0 =
      S6OutK.pk (CFSG.Permutation.FinPack.enc (d6 i)) (CFSG.Permutation.FinPack.enc (tw i)) := by
    decide +kernel
  have hW : (w4List.map A6L76EK.vc6 == S6OutK.W4Q) = true := by decide +kernel
  intro i j h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold fixCount
  exact S6OutK.fix2_of hW hp i j h1 h2 h3 h4 h5 h6

@[expose] def cl : Fin 16 → List (Fin 16) := ![[], [2, 3, 4, 5, 6, 7, 8, 9, 14, 15],
  [1, 3, 4, 5, 6, 7], [1, 2, 4, 5, 6, 7], [1, 2, 3, 5, 6, 7], [1, 2, 3, 4, 6, 7],
  [1, 2, 3, 4, 5, 7, 8, 9, 14, 15], [1, 2, 3, 4, 5, 6, 8, 9, 14, 15], [1, 6, 7, 9, 14, 15],
  [1, 6, 7, 8, 14, 15], [], [], [], [], [1, 6, 7, 8, 9, 15], [1, 6, 7, 8, 9, 14]]

theorem mem_cl : ∀ i j : Fin 16, InvPair i j → j ∈ cl i := by
  decide +kernel

@[expose] def InvTriple (i j k : Fin 16) : Prop :=
  InvPair i j ∧ d6 k * d6 k = 1 ∧ d6 k * d6 i = d6 i * d6 k ∧ d6 k * d6 j = d6 j * d6 k ∧
    d6 k ≠ 1 ∧ d6 k ≠ d6 i ∧ d6 k ≠ d6 j ∧ d6 k ≠ d6 i * d6 j

instance (i j k : Fin 16) : Decidable (InvTriple i j k) := by unfold InvTriple; infer_instance

@[expose] def span3 (i j k : Fin 16) : List (Perm (Fin 6)) :=
  [1, d6 i, d6 j, d6 k, d6 i * d6 j, d6 i * d6 k, d6 j * d6 k, d6 i * d6 j * d6 k]

theorem e8_cases : ∀ i : Fin 16, ∀ j ∈ cl i, ∀ k ∈ cl i, InvTriple i j k →
    (d6 4 ∈ span3 i j k ∧ d6 2 ∈ span3 i j k ∧ d6 1 ∈ span3 i j k) ∨
      (d6 8 ∈ span3 i j k ∧ d6 6 ∈ span3 i j k ∧ d6 1 ∈ span3 i j k) := by
  decide +kernel

@[expose] def CommInv (i j k l : Fin 16) : Prop :=
  d6 l * d6 l = 1 ∧ d6 l * d6 i = d6 i * d6 l ∧ d6 l * d6 j = d6 j * d6 l ∧
    d6 l * d6 k = d6 k * d6 l

instance (i j k l : Fin 16) : Decidable (CommInv i j k l) := by unfold CommInv; infer_instance

theorem e8_max : (∀ l : Fin 16, CommInv 4 2 1 l → d6 l ∈ span3 4 2 1) ∧
    ∀ l : Fin 16, CommInv 8 6 1 l → d6 l ∈ span3 8 6 1 := by
  decide +kernel

theorem fix_E8 : fixCount [d6 4, d6 2, d6 1] * fixCount [tw 4, tw 2, tw 1] ≤ 8 ∧
    fixCount [d6 8, d6 6, d6 1] * fixCount [tw 8, tw 6, tw 1] ≤ 8 := by
  decide +kernel

theorem w4List_nodup : w4List.Nodup := by
  decide +kernel

theorem card_le_length {A : Subgroup (Perm (Fin 6))} {L : List (Perm (Fin 6))}
    (h : ∀ a ∈ A, a ∈ L) : Nat.card A ≤ L.length := by
  calc Nat.card A = (A : Set (Perm (Fin 6))).ncard := Nat.card_coe_set_eq _
    _ ≤ ((L.toFinset : Finset (Perm (Fin 6))) : Set (Perm (Fin 6))).ncard :=
      Set.ncard_le_ncard (fun a ha => List.mem_toFinset.2 (h a ha)) (Finset.finite_toSet _)
    _ = L.toFinset.card := Set.ncard_coe_finset _
    _ ≤ L.length := List.toFinset_card_le L

theorem card_fix_le {S : Set (Perm (Fin 6))} {L : List (Perm (Fin 6))} (hL : ∀ s ∈ L, s ∈ S) :
    Nat.card {x : ↥W4 // ∀ s ∈ S, act4 s x = x} ≤ fixCount L := by
  set l' := w4List.filter fun x => decide (∀ s ∈ L, act4f s x = x) with hl'
  have hnd : l'.Nodup := w4List_nodup.filter _
  have hle : Nat.card {x : ↥W4 // ∀ s ∈ S, act4 s x = x} ≤ Nat.card {y : P6 // y ∈ l'} := by
    refine Nat.card_le_card_of_injective (fun x => ⟨(x.1 : P6), List.mem_filter.2
      ⟨(mem_w4List _).1 x.1.2, decide_eq_true fun s hs => ?_⟩⟩) fun x y hxy => ?_
    · show ((act4 s x.1 : ↥W4) : P6) = (x.1 : P6)
      exact congrArg Subtype.val (x.2 s (hL s hs))
    · have h1 := congrArg (fun z : {y : P6 // y ∈ l'} => (z : P6)) hxy
      exact Subtype.ext (Subtype.ext h1)
  have hcard : Nat.card {y : P6 // y ∈ l'} = l'.length := by
    rw [← List.toFinset_card_of_nodup hnd, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => List.mem_toFinset.symm)
  rw [hcard] at hle
  exact hle

theorem card_fix_mul_le {A : Subgroup (Perm (Fin 6))} (hAD : ∀ a ∈ A, InD6 a) (hA : A ≠ ⊥)
    (hA2 : ∀ a ∈ A, a * a = 1) :
    Nat.card A * Nat.card {x : ↥W4 // ∀ a ∈ A, act4 a x = x} *
      Nat.card {x : ↥W4 // ∀ a ∈ phiEquiv.symm '' (A : Set (Perm (Fin 6))), act4 a x = x} ≤
        64 := by
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hA2 x hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hA2 y hy)
    have h3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hA2 _ (A.mul_mem hx hy))
    rw [mul_inv_rev, hxi, hyi] at h3
    exact h3.symm
  have htw : ∀ i : Fin 16, d6 i ∈ A → tw i ∈ phiEquiv.symm '' (A : Set (Perm (Fin 6))) :=
    fun i hi => ⟨d6 i, hi, by rw [phi_inv_eq, phi_inv_d6]⟩
  have hfix : ∀ L L' : List (Perm (Fin 6)), (∀ s ∈ L, s ∈ A) →
      (∀ s ∈ L', s ∈ phiEquiv.symm '' (A : Set (Perm (Fin 6)))) →
      Nat.card {x : ↥W4 // ∀ a ∈ A, act4 a x = x} *
        Nat.card {x : ↥W4 // ∀ a ∈ phiEquiv.symm '' (A : Set (Perm (Fin 6))), act4 a x = x} ≤
          fixCount L * fixCount L' := fun L L' hL hL' =>
    Nat.mul_le_mul (card_fix_le (S := (A : Set (Perm (Fin 6)))) hL) (card_fix_le hL')
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨i, rfl⟩ := mem_d6 a (hAD a haA)
  by_cases hb : ∃ b ∈ A, b ≠ 1 ∧ b ≠ d6 i
  · obtain ⟨b, hbA, hb1, hba⟩ := hb
    obtain ⟨j, rfl⟩ := mem_d6 b (hAD b hbA)
    have hij : InvPair i j := ⟨hA2 _ haA, ha1', hA2 _ hbA, hb1, fun h => hba h.symm,
      hcomm _ haA _ hbA⟩
    by_cases hc : ∃ c ∈ A, c ≠ 1 ∧ c ≠ d6 i ∧ c ≠ d6 j ∧ c ≠ d6 i * d6 j
    · obtain ⟨c, hcA, hc1, hci, hcj, hcij⟩ := hc
      obtain ⟨k, rfl⟩ := mem_d6 c (hAD c hcA)
      have hijk : InvTriple i j k := ⟨hij, hA2 _ hcA, hcomm _ hcA _ haA, hcomm _ hcA _ hbA, hc1,
        hci, hcj, hcij⟩
      have hj := mem_cl i j hij
      have hk := mem_cl i k ⟨hA2 _ haA, ha1', hA2 _ hcA, hc1, fun h => hci h.symm,
        hcomm _ haA _ hcA⟩
      have hspan : ∀ x ∈ span3 i j k, x ∈ A := by
        intro x hx
        simp only [span3, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact A.one_mem
        · exact haA
        · exact hbA
        · exact hcA
        · exact A.mul_mem haA hbA
        · exact A.mul_mem haA hcA
        · exact A.mul_mem hbA hcA
        · exact A.mul_mem (A.mul_mem haA hbA) hcA
      rcases e8_cases i j hj k hk hijk with ⟨h4, h2, h1⟩ | ⟨h8, h6, h1⟩
      · have hsub : ∀ x ∈ A, x ∈ span3 4 2 1 := by
          intro x hx
          obtain ⟨l, rfl⟩ := mem_d6 x (hAD x hx)
          exact e8_max.1 l ⟨hA2 _ hx, hcomm _ hx _ (hspan _ h4), hcomm _ hx _ (hspan _ h2),
            hcomm _ hx _ (hspan _ h1)⟩
        have h1' := hfix [d6 4, d6 2, d6 1] [tw 4, tw 2, tw 1]
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro s (rfl | rfl | rfl) <;>
            exact hspan _ ‹_›)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro s (rfl | rfl | rfl) <;>
            exact htw _ (hspan _ ‹_›))
        have hA8 := card_le_length hsub
        rw [mul_assoc]
        calc Nat.card A * _ ≤ 8 * 8 := Nat.mul_le_mul hA8 (h1'.trans fix_E8.1)
          _ = 64 := by norm_num
      · have hsub : ∀ x ∈ A, x ∈ span3 8 6 1 := by
          intro x hx
          obtain ⟨l, rfl⟩ := mem_d6 x (hAD x hx)
          exact e8_max.2 l ⟨hA2 _ hx, hcomm _ hx _ (hspan _ h8), hcomm _ hx _ (hspan _ h6),
            hcomm _ hx _ (hspan _ h1)⟩
        have h1' := hfix [d6 8, d6 6, d6 1] [tw 8, tw 6, tw 1]
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro s (rfl | rfl | rfl) <;>
            exact hspan _ ‹_›)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro s (rfl | rfl | rfl) <;>
            exact htw _ (hspan _ ‹_›))
        have hA8 := card_le_length hsub
        rw [mul_assoc]
        calc Nat.card A * _ ≤ 8 * 8 := Nat.mul_le_mul hA8 (h1'.trans fix_E8.2)
          _ = 64 := by norm_num
    · push Not at hc
      have hsub : ∀ x ∈ A, x ∈ [1, d6 i, d6 j, d6 i * d6 j] := by
        intro x hx
        by_cases h1 : x = 1
        · simp [h1]
        by_cases h2 : x = d6 i
        · simp [h2]
        by_cases h3 : x = d6 j
        · simp [h3]
        simp [hc x hx h1 h2 h3]
      have h1' := hfix [d6 i, d6 j] [tw i, tw j]
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro s (rfl | rfl) <;>
          assumption)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro s (rfl | rfl)
            · exact htw i haA
            · exact htw j hbA)
      have hA4 := card_le_length hsub
      rw [mul_assoc]
      calc Nat.card A * _ ≤ 4 * 16 := Nat.mul_le_mul hA4 (h1'.trans (fix_two i j hij))
        _ = 64 := by norm_num
  · push Not at hb
    have hsub : ∀ x ∈ A, x ∈ [1, d6 i] := by
      intro x hx
      by_cases h1 : x = 1
      · simp [h1]
      simp [hb x hx h1]
    have h1' := hfix [d6 i] [tw i]
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro s rfl; exact haA)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro s rfl; exact htw i haA)
    have hA2' := card_le_length hsub
    rw [mul_assoc]
    calc Nat.card A * _ ≤ 2 * 32 := Nat.mul_le_mul hA2' (h1'.trans (fix_one i (hA2 _ haA) ha1'))
      _ = 64 := by norm_num

end S6Out

end CFSG.Quasithin.H13.U3
