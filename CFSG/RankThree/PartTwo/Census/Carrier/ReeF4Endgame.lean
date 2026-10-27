module

public import CFSG.Adapters.TauCetiExceptional.EvenTail

public section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti
  BigCell

section Powers

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem exponent_mul_exponent_perm (i : Fin ReeTag.F4.tag.rank) :
    ReeTag.F4.exponent i * ReeTag.F4.exponent (ReeTag.F4.perm i) = 2 := by
  fin_cases i <;> decide

theorem perm_perm (i : Fin ReeTag.F4.tag.rank) : ReeTag.F4.perm (ReeTag.F4.perm i) = i := by
  fin_cases i <;> decide

theorem finiteExceptionalAut_pow_xElement (a : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : K) :
    (ReeTag.F4.finiteExceptionalAut K ^ (2 * a)) (xElement i c) = xElement i (c ^ 2 ^ a) ∧
      (ReeTag.F4.finiteExceptionalAut K ^ (2 * a + 1)) (xElement i c) =
        xElement (ReeTag.F4.perm i) (c ^ (2 ^ a * ReeTag.F4.exponent i)) := by
  induction a generalizing c with
  | zero => simp [ReeTag.finiteExceptionalAut_xElement]
  | succ a ih =>
    have h2 : (ReeTag.F4.finiteExceptionalAut K ^ (2 * (a + 1))) (xElement i c) =
        xElement i (c ^ 2 ^ (a + 1)) := by
      rw [show 2 * (a + 1) = 2 * a + 1 + 1 by ring, pow_succ', MulAut.mul_apply, (ih c).2,
        ReeTag.finiteExceptionalAut_xElement, perm_perm, ← pow_mul, mul_assoc,
        exponent_mul_exponent_perm, pow_succ]
    refine ⟨h2, ?_⟩
    rw [pow_succ', MulAut.mul_apply, h2, ReeTag.finiteExceptionalAut_xElement, ← pow_mul]

theorem finiteExceptionalAut_pow_yElement (a : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : K) :
    (ReeTag.F4.finiteExceptionalAut K ^ (2 * a)) (yElement i c) = yElement i (c ^ 2 ^ a) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [show 2 * (a + 1) = 2 * a + 1 + 1 by ring, pow_succ', pow_succ', MulAut.mul_apply,
      MulAut.mul_apply, ih, ReeTag.finiteExceptionalAut_yElement,
      ReeTag.finiteExceptionalAut_yElement, perm_perm, ← pow_mul, ← pow_mul,
      exponent_mul_exponent_perm, pow_succ]

theorem finiteExceptionalAut_pow_even (a : ℕ) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ a)
    (x : adjointGroup ReeTag.F4.tag K) :
    ((ReeTag.F4.finiteExceptionalAut K ^ (2 * a)) x : ModGL ReeTag.F4.tag K) =
      Units.map (entrywiseHom σ.toRingHom) (x : ModGL ReeTag.F4.tag K) := by
  have h := adjointGroup_hom_ext
    (f := (ReeTag.F4.finiteExceptionalAut K ^ (2 * a)).toMonoidHom)
    (g := frobeniusTwist ReeTag.F4.tag K σ.toRingHom)
    (fun i c => by
      change (ReeTag.F4.finiteExceptionalAut K ^ (2 * a)) (xElement i c) = _
      rw [(finiteExceptionalAut_pow_xElement a i c).1, frobeniusTwist_xElement]
      exact congrArg (xElement i) (hσ c).symm)
    (fun i c => by
      change (ReeTag.F4.finiteExceptionalAut K ^ (2 * a)) (yElement i c) = _
      rw [finiteExceptionalAut_pow_yElement a i c, frobeniusTwist_yElement]
      exact congrArg (yElement i) (hσ c).symm)
  exact congrArg Subtype.val (DFunLike.congr_fun h x)

end Powers

section Odd

variable {L : Type} [Field L] (E : Subfield L) [Finite E] [CharP E ReeTag.F4.prime]

theorem conj_xUnit_of_odd (h : ModGL ReeTag.F4.tag L) (α : MulAut (adjointGroup ReeTag.F4.tag E))
    (hα : ∀ x : adjointGroup ReeTag.F4.tag E, baseChangeGL E.subtype (α x : ModGL ReeTag.F4.tag E) =
      h * baseChangeGL E.subtype (x : ModGL ReeTag.F4.tag E) * h⁻¹)
    (g : adjointGroup ReeTag.F4.tag E) (a : ℕ)
    (hαx : ∀ x : adjointGroup ReeTag.F4.tag E, (α x : ModGL ReeTag.F4.tag E) =
      (g : ModGL ReeTag.F4.tag E) *
        ((ReeTag.F4.finiteExceptionalAut E ^ (2 * a + 1)) x : ModGL ReeTag.F4.tag E) *
        (g : ModGL ReeTag.F4.tag E)⁻¹)
    (i : Fin ReeTag.F4.tag.rank) (c : E) :
    (baseChangeGL E.subtype (g : ModGL ReeTag.F4.tag E))⁻¹ * h * xUnit ReeTag.F4.tag L i (c : L) *
        ((baseChangeGL E.subtype (g : ModGL ReeTag.F4.tag E))⁻¹ * h)⁻¹ =
      xUnit ReeTag.F4.tag L (ReeTag.F4.perm i) ((c : L) ^ (2 ^ a * ReeTag.F4.exponent i)) := by
  set G := baseChangeGL E.subtype (g : ModGL ReeTag.F4.tag E) with hG
  have e := hα (xElement i c)
  rw [hαx, (finiteExceptionalAut_pow_xElement a i c).2] at e
  simp only [map_mul, map_inv] at e
  have ex : ((xElement i c : adjointGroup ReeTag.F4.tag E) : ModGL ReeTag.F4.tag E) =
      xUnit ReeTag.F4.tag E i c := rfl
  have ex' : ((xElement (ReeTag.F4.perm i) (c ^ (2 ^ a * ReeTag.F4.exponent i)) :
      adjointGroup ReeTag.F4.tag E) : ModGL ReeTag.F4.tag E) =
      xUnit ReeTag.F4.tag E (ReeTag.F4.perm i) (c ^ (2 ^ a * ReeTag.F4.exponent i)) := rfl
  rw [ex, ex', baseChangeGL_xUnit, baseChangeGL_xUnit, ← hG] at e
  have e2 : h * xUnit ReeTag.F4.tag L i (E.subtype c) * h⁻¹ =
      G * xUnit ReeTag.F4.tag L (ReeTag.F4.perm i)
        (E.subtype (c ^ (2 ^ a * ReeTag.F4.exponent i))) * G⁻¹ := e.symm
  rw [mul_inv_rev, inv_inv]
  calc G⁻¹ * h * xUnit ReeTag.F4.tag L i (c : L) * (h⁻¹ * G) =
      G⁻¹ * (h * xUnit ReeTag.F4.tag L i (E.subtype c) * h⁻¹) * G := by
        simp only [mul_assoc]
        rfl
    _ = _ := by
        rw [e2]
        simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, map_pow]
        rfl

omit [CharP E ReeTag.F4.prime] in
theorem false_of_conj_odd {k : ℕ} (hE : Nat.card E = 2 ^ k) (hk : 3 ≤ k) {a : ℕ}
    (hak : a + 1 ≤ k) (h' : ModGL ReeTag.F4.tag L)
    (hconj : ∀ (i : Fin ReeTag.F4.tag.rank) (c : E),
      h' * xUnit ReeTag.F4.tag L i (c : L) * h'⁻¹ =
        xUnit ReeTag.F4.tag L (ReeTag.F4.perm i) ((c : L) ^ (2 ^ a * ReeTag.F4.exponent i))) :
    False := by
  have hA3 : ∀ i : Fin ReeTag.F4.tag.rank, xCoeff ReeTag.F4.tag L i 3 = 0 := fun i =>
    xCoeff_three_eq_zero (by decide) i
  by_cases hak' : a + 1 < k
  ·
    have hm : 2 ^ a * ReeTag.F4.exponent (⟨2, by decide⟩ : Fin ReeTag.F4.tag.rank) =
        2 ^ (a + 1) := by
      rw [pow_succ]
      rfl
    refine false_of_conj_xUnit_pow E h' (hA3 ⟨2, by decide⟩)
      (i' := ReeTag.F4.perm ⟨2, by decide⟩) (m := 2 ^ (a + 1)) ?_ ?_ ?_ fun c => ?_
    · calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [hE]
      exact Nat.pow_lt_pow_right (by norm_num) hak'
    · by_cases ha0 : a = 0
      · refine Or.inr ?_
        rw [ha0, hE]
        calc 2 * 2 ^ (0 + 1) < 2 ^ 3 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      · refine Or.inl ?_
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [hconj, hm]
  ·
    have hm : 2 ^ a * ReeTag.F4.exponent (⟨0, by decide⟩ : Fin ReeTag.F4.tag.rank) = 2 ^ a := by
      rw [mul_eq_left₀ (by positivity)]
      rfl
    refine false_of_conj_xUnit_pow E h' (hA3 ⟨0, by decide⟩)
      (i' := ReeTag.F4.perm ⟨0, by decide⟩) (m := 2 ^ a) ?_ ?_ ?_ fun c => ?_
    · calc 2 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [hE]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · refine Or.inl ?_
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [hconj, hm]

end Odd

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L p]
  [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L]

theorem le_adjointGroup_reeF4_tag_two (hp : p = 2) (H : Subgroup (ModGL ReeTag.F4.tag L))
    (hCH : adjointGroup ReeTag.F4.tag L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat ReeTag.F4.tag P →
      evalMat (natMat ReeTag.F4.tag L (h : Module.End L (RootModule ReeTag.F4.tag L))) P = 0) :
    H ≤ adjointGroup ReeTag.F4.tag L := by
  subst hp
  intro h hh
  obtain ⟨k, hk, ⟨t, ht⟩, α, hα⟩ := exists_conj_mulAut_of_three_le (p := 2) H hCH hH hh
  have : Finite (frobeniusFixedSubfield L 2 k) := finite_frobeniusFixedSubfield L 2 k (by omega)
  have hE : Nat.card (frobeniusFixedSubfield L 2 k) = 2 ^ k :=
    card_frobeniusFixedSubfield L 2 k (by omega)
  have : CharP (frobeniusFixedSubfield L 2 k) 2 := Subfield.charP _ 2
  have : CharP (frobeniusFixedSubfield L 2 k) ReeTag.F4.prime := ‹CharP _ 2›
  obtain ⟨⟨g, j⟩, hgj, -⟩ := (even_F4_exact_automorphism_normal_form (f := k) (by omega)
    (frobeniusFixedSubfield L 2 k) hE).2.1 α
  have hαx : ∀ x : adjointGroup ReeTag.F4.tag (frobeniusFixedSubfield L 2 k),
      (α x : ModGL ReeTag.F4.tag (frobeniusFixedSubfield L 2 k)) =
      (g : ModGL ReeTag.F4.tag (frobeniusFixedSubfield L 2 k)) *
        ((ReeTag.F4.finiteExceptionalAut (frobeniusFixedSubfield L 2 k) ^ (j : ℕ)) x :
          ModGL ReeTag.F4.tag (frobeniusFixedSubfield L 2 k)) *
        (g : ModGL ReeTag.F4.tag (frobeniusFixedSubfield L 2 k))⁻¹ := fun x => by
    rw [hgj]
    rfl
  obtain ⟨a, ha | ha⟩ := Nat.even_or_odd' (j : ℕ)
  ·
    refine mem_adjointGroup_of_inner_entrywise_two (hasQuadraticNode_of_ne_G2 (by decide))
      (frobeniusFixedSubfield L 2 k) hE hk (iterateFrobeniusEquiv _ 2 a) t ht hCH hH hh g α hα
      fun x => ?_
    rw [hαx, ha, finiteExceptionalAut_pow_even a _ (iterateFrobeniusEquiv_def _ 2 a)]
  ·
    exfalso
    have hj : (j : ℕ) < 2 * k := j.2
    rw [ha] at hαx
    exact false_of_conj_odd (frobeniusFixedSubfield L 2 k) hE hk (a := a) (by omega) _
      (conj_xUnit_of_odd (frobeniusFixedSubfield L 2 k) h α hα g a hαx)

theorem le_adjointGroup_F4_two_rankThree (hp : p = 2) (H : Subgroup (ModGL .F4 L))
    (hCH : adjointGroup .F4 L ≤ H)
    (hH : ∀ h ∈ H, ∀ P, VanishesOnRat .F4 P →
      evalMat (natMat .F4 L (h : Module.End L (RootModule .F4 L))) P = 0) :
    H ≤ adjointGroup .F4 L :=
  le_adjointGroup_reeF4_tag_two hp H hCH hH

end CFSG.TauCetiBridge.Even
