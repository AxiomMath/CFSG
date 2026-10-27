module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocDef
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheckB

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

@[expose] def Img (h : J) (W W' : List ℕ) : Prop :=
  (∀ c ∈ W, ∃ c' ∈ W', h * eta uJ 11 c * h⁻¹ = eta uJ 11 c') ∧
    ∀ c' ∈ W', ∃ c ∈ W, h * eta uJ 11 c * h⁻¹ = eta uJ 11 c'

theorem Img_one (W : List ℕ) : Img 1 W W := by
  refine ⟨fun c hc => ⟨c, hc, by simp⟩, fun c hc => ⟨c, hc, by simp⟩⟩

theorem Img_mul {h1 h2 : J} {W W2 W3 : List ℕ} (h : Img h2 W W2) (h' : Img h1 W2 W3) :
    Img (h1 * h2) W W3 := by
  refine ⟨fun c hc => ?_, fun c' hc' => ?_⟩
  · obtain ⟨c2, hc2, e2⟩ := h.1 c hc
    obtain ⟨c3, hc3, e3⟩ := h'.1 c2 hc2
    refine ⟨c3, hc3, ?_⟩
    rw [← e3, ← e2]
    group
  · obtain ⟨c2, hc2, e2⟩ := h'.2 c' hc'
    obtain ⟨c, hc, e⟩ := h.2 c2 hc2
    refine ⟨c, hc, ?_⟩
    rw [← e2, ← e]
    group

theorem Img_iff (hM : MatFacts)
    {h : J} {W W' : List ℕ} (hW' : W' ∈ trioL) (hi : Img h W W') {c' : ℕ} (hc' : c' < 2048) :
    c' ∈ W' ↔ ∃ c ∈ W, h * eta uJ 11 c * h⁻¹ = eta uJ 11 c' := by
  constructor
  · intro h1
    exact hi.2 c' h1
  · rintro ⟨c, hc, e⟩
    obtain ⟨c'', hc'', e''⟩ := hi.1 c hc
    have : c'' = c' := by
      refine eta_inj' hM ((trio_prop.2 W' hW').2.1 c'' hc'') hc' ?_
      rw [← e'', ← e]
    rw [← this]
    exact hc''

theorem trio_conj
    (hM : MatFacts) {h : J} (hh : h ∈ Hj) :
    (∀ W ∈ trioL, ∃ W' ∈ trioL, Img h W W') ∧ ∀ W ∈ trioL, ∃ W' ∈ trioL, Img h⁻¹ W W' := by
  have hmem : ∀ h ∈ Subgroup.closure (XJ '' {ℓ | ℓ ∈ letters}),
      (∀ W ∈ trioL, ∃ W' ∈ trioL, Img h W W') ∧ ∀ W ∈ trioL, ∃ W' ∈ trioL, Img h⁻¹ W W' := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨ℓ, hℓ, rfl⟩ := hy
      have key : ∀ ℓ ∈ letters, ∀ W ∈ trioL, ∃ W' ∈ trioL, Img (XJ ℓ) W W' := by
        intro ℓ hℓ W hW
        refine ⟨stepW ℓ W, (trio_prop.2 W hW).2.2.2 ℓ hℓ, ?_, ?_⟩
        · intro c hc
          exact ⟨act ℓ c, mem_stepW.2 ⟨c, hc, rfl⟩, hX_all hM hℓ c⟩
        · intro c' hc'
          obtain ⟨c, hc, rfl⟩ := mem_stepW.1 hc'
          exact ⟨c, hc, hX_all hM hℓ c⟩
      refine ⟨key ℓ hℓ, ?_⟩
      obtain ⟨hℓ', hinv⟩ := XJ_inv hℓ
      rw [← hinv]
      exact key (-ℓ) hℓ'
    | one =>
      exact ⟨fun W hW => ⟨W, hW, Img_one W⟩, fun W hW => ⟨W, hW, by simpa using Img_one W⟩⟩
    | mul y z _ _ hy hz =>
      refine ⟨fun W hW => ?_, fun W hW => ?_⟩
      · obtain ⟨W2, hW2, e2⟩ := hz.1 W hW
        obtain ⟨W3, hW3, e3⟩ := hy.1 W2 hW2
        exact ⟨W3, hW3, Img_mul e2 e3⟩
      · obtain ⟨W2, hW2, e2⟩ := hy.2 W hW
        obtain ⟨W3, hW3, e3⟩ := hz.2 W2 hW2
        refine ⟨W3, hW3, ?_⟩
        rw [mul_inv_rev]
        exact Img_mul e2 e3
    | inv y _ hy =>
      refine ⟨hy.2, fun W hW => ?_⟩
      simpa using hy.1 W hW
  exact hmem h (Hj_le_closure hh)

end CFSG.Quasithin.J4Loc
