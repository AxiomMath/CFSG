module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Sec

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def Row1Ineq (L : Subgroup (MulAut W)) (U Z : Subgroup W) (m : ℕ) : Prop :=
  ∃ n a : ℕ, 2 ≤ a ∧ a ≤ m ∧
    ((IsSLn ↥L n a ∧ BinaryNaturalSL L U Z n a) ∨ (IsSpn ↥L n a ∧ NatSpn L U Z n a) ∨
      (IsOmegaPlus ↥L n a ∧ NatOmegaPlus L U Z n a) ∨
      (IsOmegaMinus ↥L n a ∧ NatOmegaMinus L U Z n a))

private theorem w1369_card_field_ne_one (K : Type) [Field K] [Finite K] : Nat.card K ≠ 1 := by
  intro h
  have := Finite.one_lt_card (α := K)
  omega

private theorem w1369_isSLn_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSLn X n a) : IsSLn Y n a := by
  obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

private theorem w1369_isSpn_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSpn X n a) : IsSpn Y n a := by
  obtain ⟨hn, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

private theorem w1369_isOmegaPlus_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n a : ℕ} (h : IsOmegaPlus X n a) : IsOmegaPlus Y n a := by
  obtain ⟨hn, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

private theorem w1369_isOmegaMinus_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n a : ℕ} (h : IsOmegaMinus X n a) : IsOmegaMinus Y n a := by
  obtain ⟨hn, K, hK, hKf, b, c, hcard, hq, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hK, hKf, b, c, hcard, hq, ⟨e.symm.trans e'⟩⟩

private theorem w1369_isSUn_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSUn X n a) : IsSUn Y n a := by
  obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

private theorem w1369_isAlt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : IsAlt X n) : IsAlt Y n := by
  obtain ⟨e'⟩ := h
  exact ⟨e.symm.trans e'⟩

private theorem w1369_binaryNaturalSL_sec {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) (hZU : Z ≤ U) (hf : FaithOn A U Z) {n a : ℕ}
    (h : BinaryNaturalSL (secSub U Z A) ⊤ ⊥ n a) : BinaryNaturalSL A U Z n a := by
  obtain ⟨K, hK, hKf, hcard, hreal⟩ := h
  exact ⟨K, hK, hKf, hcard,
    (realizes_secSub_iff (FFModel.nat (StatedSL n K)) hA hZU hf).1 hreal⟩

private theorem w1369_natSpn_sec {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) (hZU : Z ≤ U) (hf : FaithOn A U Z) {n a : ℕ}
    (h : NatSpn (secSub U Z A) ⊤ ⊥ n a) : NatSpn A U Z n a := by
  obtain ⟨hn, K, hK, hKf, hcard, hreal⟩ := h
  exact ⟨hn, K, hK, hKf, hcard,
    (realizes_secSub_iff (FFModel.nat (StatedSp (n / 2) K)) hA hZU hf).1 hreal⟩

private theorem w1369_natOmegaPlus_sec {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) (hZU : Z ≤ U) (hf : FaithOn A U Z) {n a : ℕ}
    (h : NatOmegaPlus (secSub U Z A) ⊤ ⊥ n a) : NatOmegaPlus A U Z n a := by
  obtain ⟨hn, K, hK, hKf, hcard, hreal⟩ := h
  exact ⟨hn, K, hK, hKf, hcard,
    (realizes_secSub_iff (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K)))
      hA hZU hf).1 hreal⟩

private theorem w1369_natOmegaMinus_sec {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) (hZU : Z ≤ U) (hf : FaithOn A U Z) {n a : ℕ}
    (h : NatOmegaMinus (secSub U Z A) ⊤ ⊥ n a) : NatOmegaMinus A U Z n a := by
  obtain ⟨hn, K, hK, hKf, b, c, hcard, hirr, hreal⟩ := h
  exact ⟨hn, K, hK, hKf, b, c, hcard, hirr,
    (realizes_secSub_iff (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K b c)))
      hA hZU hf).1 hreal⟩

private theorem w1369_natSUn_sec {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) (hZU : Z ≤ U) (hf : FaithOn A U Z) {n a : ℕ}
    (h : NatSUn (secSub U Z A) ⊤ ⊥ n a) : NatSUn A U Z n a := by
  obtain ⟨K, hK, hKf, hcard, hreal⟩ := h
  exact ⟨K, hK, hKf, hcard,
    (realizes_secSub_iff (FFModel.nat (StatedSU n (2 ^ a) K)) hA hZU hf).1 hreal⟩

private theorem w1369_g2NaturalDerived_sec {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) (hZU : Z ≤ U) (hf : FaithOn A U Z) {a : ℕ}
    (h : G2NaturalDerived (secSub U Z A) ⊤ ⊥ a) : G2NaturalDerived A U Z a := by
  obtain ⟨K, hK, hKf, hcard, hreal⟩ := h
  exact ⟨K, hK, hKf, hcard,
    (realizes_secSub_iff (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) hA hZU hf).1 hreal⟩

private theorem w1369_alternatingNatural_sec {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) (hZU : Z ≤ U) (hf : FaithOn A U Z) {n : ℕ}
    (h : AlternatingNatural (secSub U Z A) ⊤ ⊥ n) : AlternatingNatural A U Z n :=
  (realizes_secSub_iff (FFModel.altDn n) hA hZU hf).1 h

private theorem w1369_conc_four_exp1 {L : Subgroup (MulAut W)} {U Z : Subgroup W} {m n : ℕ}
    (h : (IsSLn ↥L n 1 ∧ BinaryNaturalSL L U Z n 1) ∨
      (IsSpn ↥L n 1 ∧ NatSpn L U Z n 1) ∨
      (IsOmegaPlus ↥L n 1 ∧ NatOmegaPlus L U Z n 1) ∨
      (IsOmegaMinus ↥L n 1 ∧ NatOmegaMinus L U Z n 1)) : Conc4_135 L U Z m := by
  unfold Conc4_135
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr (Or.inl ⟨n, Or.inl ⟨h1, h2⟩⟩)
  · exact Or.inr (Or.inl ⟨n, Or.inr (Or.inl ⟨h1, h2⟩)⟩)
  · exact Or.inr (Or.inl ⟨n, Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))⟩)
  · exact Or.inr (Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))⟩)

private theorem w1369_conc_alt {L : Subgroup (MulAut W)} {U Z : Subgroup W} {m n : ℕ}
    (h : IsAlt ↥L n ∧ AlternatingNatural L U Z n) : Conc4_135 L U Z m := by
  unfold Conc4_135
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h.1, h.2⟩)))))

private theorem w1369_first_block {L : Subgroup (MulAut W)} {U Z : Subgroup W} {m n a : ℕ}
    (e : ↥(secSub U Z L) ≃* ↥L) (hL : StabPair L U Z) (hZU : Z ≤ U) (hf : FaithOn L U Z)
    (ha : a ≤ m)
    (h : (IsSLn ↥(secSub U Z L) n a ∧ BinaryNaturalSL (secSub U Z L) ⊤ ⊥ n a) ∨
      (IsSpn ↥(secSub U Z L) n a ∧ NatSpn (secSub U Z L) ⊤ ⊥ n a) ∨
      (IsOmegaPlus ↥(secSub U Z L) n a ∧ NatOmegaPlus (secSub U Z L) ⊤ ⊥ n a) ∨
      (IsOmegaMinus ↥(secSub U Z L) n a ∧ NatOmegaMinus (secSub U Z L) ⊤ ⊥ n a)) :
    Conc4_135 L U Z m ∨ Row1Ineq L U Z m := by
  have htrans : (IsSLn ↥L n a ∧ BinaryNaturalSL L U Z n a) ∨
      (IsSpn ↥L n a ∧ NatSpn L U Z n a) ∨
      (IsOmegaPlus ↥L n a ∧ NatOmegaPlus L U Z n a) ∨
      (IsOmegaMinus ↥L n a ∧ NatOmegaMinus L U Z n a) := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨w1369_isSLn_of_mulEquiv e h1, w1369_binaryNaturalSL_sec hL hZU hf h2⟩
    · exact Or.inr (Or.inl ⟨w1369_isSpn_of_mulEquiv e h1, w1369_natSpn_sec hL hZU hf h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨w1369_isOmegaPlus_of_mulEquiv e h1,
        w1369_natOmegaPlus_sec hL hZU hf h2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨w1369_isOmegaMinus_of_mulEquiv e h1,
        w1369_natOmegaMinus_sec hL hZU hf h2⟩))
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · exfalso
    rw [ha0] at h
    rcases h with ⟨hSL, _⟩ | ⟨hSp, _⟩ | ⟨hOp, _⟩ | ⟨hOm, _⟩
    · obtain ⟨K, hK, hKf, hcard, _⟩ := hSL
      exact w1369_card_field_ne_one K (by simpa using hcard)
    · obtain ⟨_, K, hK, hKf, hcard, _⟩ := hSp
      exact w1369_card_field_ne_one K (by simpa using hcard)
    · obtain ⟨_, K, hK, hKf, hcard, _⟩ := hOp
      exact w1369_card_field_ne_one K (by simpa using hcard)
    · obtain ⟨_, K, hK, hKf, b, c, hcard, _, _⟩ := hOm
      exact w1369_card_field_ne_one K (by simpa using hcard)
  · rcases Nat.eq_or_lt_of_le (show 1 ≤ a from hapos) with h1 | h1
    · have ha1 : a = 1 := h1.symm
      rw [ha1] at htrans
      exact Or.inl (w1369_conc_four_exp1 htrans)
    · exact Or.inr ⟨n, a, h1, ha, htrans⟩

private theorem w1369_second_block {L : Subgroup (MulAut W)} {U Z : Subgroup W} {m n : ℕ}
    (e : ↥(secSub U Z L) ≃* ↥L) (hL : StabPair L U Z) (hZU : Z ≤ U) (hf : FaithOn L U Z)
    (h : (IsSLn ↥(secSub U Z L) n 1 ∧ BinaryNaturalSL (secSub U Z L) ⊤ ⊥ n 1) ∨
      (IsSpn ↥(secSub U Z L) n 1 ∧ NatSpn (secSub U Z L) ⊤ ⊥ n 1) ∨
      (IsOmegaPlus ↥(secSub U Z L) n 1 ∧ NatOmegaPlus (secSub U Z L) ⊤ ⊥ n 1) ∨
      (IsOmegaMinus ↥(secSub U Z L) n 1 ∧ NatOmegaMinus (secSub U Z L) ⊤ ⊥ n 1) ∨
      (IsSUn ↥(secSub U Z L) n 1 ∧ NatSUn (secSub U Z L) ⊤ ⊥ n 1) ∨
      (LieModel ↥(secSub U Z L) .PSU 3 3 1 ∧ G2NaturalDerived (secSub U Z L) ⊤ ⊥ 1)) :
    Conc4_135 L U Z m := by
  unfold Conc4_135
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨_, h2⟩
  · refine Or.inr (Or.inl ⟨n, Or.inl ?_⟩)
    exact ⟨w1369_isSLn_of_mulEquiv e h1, w1369_binaryNaturalSL_sec hL hZU hf h2⟩
  · refine Or.inr (Or.inl ⟨n, Or.inr (Or.inl ?_)⟩)
    exact ⟨w1369_isSpn_of_mulEquiv e h1, w1369_natSpn_sec hL hZU hf h2⟩
  · refine Or.inr (Or.inl ⟨n, Or.inr (Or.inr (Or.inl ?_))⟩)
    exact ⟨w1369_isOmegaPlus_of_mulEquiv e h1, w1369_natOmegaPlus_sec hL hZU hf h2⟩
  · refine Or.inr (Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩)
    exact ⟨w1369_isOmegaMinus_of_mulEquiv e h1, w1369_natOmegaMinus_sec hL hZU hf h2⟩
  · refine Or.inr (Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩)
    exact ⟨w1369_isSUn_of_mulEquiv e h1, w1369_natSUn_sec hL hZU hf h2⟩
  · exact Or.inr (Or.inr (Or.inl (w1369_g2NaturalDerived_sec hL hZU hf h2)))

theorem bridge_rows_nat {U Z : Subgroup W} {L : Subgroup (MulAut W)} {m : ℕ} (hZU : Z ≤ U)
    (hL : StabPair L U Z) (hf : FaithOn L U Z)
    (h : (∃ n a : ℕ, a ≤ m ∧
        ((IsSLn ↥(secSub U Z L) n a ∧ BinaryNaturalSL (secSub U Z L) ⊤ ⊥ n a) ∨
          (IsSpn ↥(secSub U Z L) n a ∧ NatSpn (secSub U Z L) ⊤ ⊥ n a) ∨
          (IsOmegaPlus ↥(secSub U Z L) n a ∧ NatOmegaPlus (secSub U Z L) ⊤ ⊥ n a) ∨
          (IsOmegaMinus ↥(secSub U Z L) n a ∧ NatOmegaMinus (secSub U Z L) ⊤ ⊥ n a))) ∨
      (∃ n : ℕ,
        (IsSLn ↥(secSub U Z L) n 1 ∧ BinaryNaturalSL (secSub U Z L) ⊤ ⊥ n 1) ∨
        (IsSpn ↥(secSub U Z L) n 1 ∧ NatSpn (secSub U Z L) ⊤ ⊥ n 1) ∨
        (IsOmegaPlus ↥(secSub U Z L) n 1 ∧ NatOmegaPlus (secSub U Z L) ⊤ ⊥ n 1) ∨
        (IsOmegaMinus ↥(secSub U Z L) n 1 ∧ NatOmegaMinus (secSub U Z L) ⊤ ⊥ n 1) ∨
        (IsSUn ↥(secSub U Z L) n 1 ∧ NatSUn (secSub U Z L) ⊤ ⊥ n 1) ∨
        (LieModel ↥(secSub U Z L) .PSU 3 3 1 ∧ G2NaturalDerived (secSub U Z L) ⊤ ⊥ 1)) ∨
      (∃ n : ℕ, IsAlt ↥(secSub U Z L) n ∧ AlternatingNatural (secSub U Z L) ⊤ ⊥ n)) :
    Conc4_135 L U Z m ∨ Row1Ineq L U Z m := by
  obtain ⟨e⟩ := mulEquiv_secSub hL hf
  rcases h with h1 | h2 | h3
  · obtain ⟨n, a, ha, hrow⟩ := h1
    exact w1369_first_block e.symm hL hZU hf ha hrow
  · obtain ⟨n, hrow⟩ := h2
    exact Or.inl (w1369_second_block e.symm hL hZU hf hrow)
  · obtain ⟨n, hAlt, hMod⟩ := h3
    exact Or.inl (w1369_conc_alt ⟨w1369_isAlt_of_mulEquiv e.symm hAlt,
      w1369_alternatingNatural_sec hL hZU hf hMod⟩)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
