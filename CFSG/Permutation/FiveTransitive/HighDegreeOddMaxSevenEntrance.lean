module

public import CFSG.Permutation.FiveTransitive.OddOriginalChosenDescent
public import CFSG.Permutation.FiveTransitive.OddSemiregularExclusion
public import CFSG.Permutation.FiveTransitive.TupleMinimalOrbitFixerSylow
public import CFSG.Permutation.FiveTransitive.SylowFullFixedSet
public import CFSG.Permutation.FiveTransitive.BoundedInvolutionFixedSet
public import CFSG.Permutation.FiveTransitive.SevenNontrivialFiveFixer

public section

namespace CFSG

namespace FiveTransitive.HighDegreeOddMaxSevenEntrance

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem exists_entrance
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X))
    (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7)
    (a : Fin 5 ↪ X) (P : Sylow 2 (stabilizer G a)) :
    ∃ (x : X) (Q : Subgroup G),
      x ∉ Set.range a ∧
      Q = (stabilizer (ambientSylow a P) x).map (ambientSylow a P).subtype ∧
      (∀ y : X, y ∉ Set.range a →
        Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) ∧
      Q < ambientSylow a P ∧ IsPGroup 2 Q ∧ Q ≠ ⊥ ∧
      Nat.card (fixedPoints Q X) = 7 ∧ Nat.card (Fixed (X := X) Q) = 7 ∧
      Nat.card (Fixed (X := X) Q) < Nat.card X ∧
      Nat.card (Fixed (X := X) Q) ≤ Fintype.card X / 2 ∧
      Image (X := X) Q = ⊤ ∧ Nat.card (Image (X := X) Q) = 5040 ∧
      (∃ T : Sylow 2 (fixingSubgroup G (insert x (Set.range a))),
        (T : Subgroup (fixingSubgroup G (insert x (Set.range a)))).map
          (fixingSubgroup G (insert x (Set.range a))).subtype = Q) ∧
      (∃ S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)),
        (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
          (fixingSubgroup G (fixedPoints Q X)).subtype = Q) ∧
      (∀ t : G, t ∈ Q → orderOf t = 2 → fixedBy X t = fixedPoints Q X) ∧
      (∃ t : G, t ∈ Q ∧ orderOf t = 2 ∧ fixedBy X t = fixedPoints Q X ∧
        (fixedBy X t).ncard = 7 ∧
        ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ (fixedBy X t).ncard) ∧
      ∀ q : G, q ∈ Q → q ≠ 1 → ∀ z : X, z ∉ fixedPoints Q X → q • z ≠ z := by
  classical
  obtain ⟨hP, hfixed, x, hx, hmin, hQA, hstrict, hlarge, hoddQ, hJ5,
    hfaithful, hlocal, hcases⟩ :=
    OddOriginalChosenDescent.exists_descent X G hcard h5 hnotAlt hodd a P
  rcases hcases with ⟨hbot, _, hfree⟩ | ⟨hne, hlt, hhalf⟩
  · exact (OddSemiregularExclusion.contradiction X G hcard h5 hnotAlt hodd a P hfree).elim
  · let Q := (stabilizer (ambientSylow a P) x).map (ambientSylow a P).subtype
    obtain ⟨T, hT⟩ := TupleMinimalOrbitFixerSylow.exists_sylow a P hfixed x hx hmin
    change GenericSylowFixedAction.sylowImage G X (insert x (Set.range a)) T = Q at hT
    have hQp : IsPGroup 2 Q := by
      rw [←hT]
      exact T.isPGroup'.map _
    have hlarge' : 7 ≤ Nat.card (fixedPoints Q X) := by
      simpa only [fixed_eq] using hlarge
    obtain ⟨h7, hall, ht, hsemi⟩ :=
      BoundedInvolutionFixedSet.exact_and_semiregular 7 hmax Q hQp hne hlarge'
    have h7' : Nat.card (Fixed (X := X) Q) = 7 := by
      simpa only [fixed_eq] using h7
    let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
    obtain ⟨b⟩ : Nonempty (Fin 5 ↪ Fixed (X := X) Q) :=
      Function.Embedding.nonempty_of_card_le (by
        simpa only [Fintype.card_fin, ←Nat.card_eq_fintype_card, Nat.card_fin, h7'] using
          (show 5 ≤ 7 by omega))
    let S := Classical.arbitrary (Sylow 2 (stabilizer (Image (X := X) Q) b))
    have hS : (S : Subgroup (stabilizer (Image (X := X) Q) b)) ≠ ⊥ := by
      intro he
      have hh := (hlocal b S).1
      simp only [he, Subgroup.map_bot] at hh
      exact hh rfl
    obtain ⟨htop, horder⟩ := SevenNontrivialFiveFixer.eq_top (Image (X := X) Q) h7' hJ5 b S hS
    obtain ⟨U, hU⟩ := SylowFullFixedSet.exists_full_fixer (insert x (Set.range a)) T Q hT
    exact ⟨x, Q, hx, rfl, hmin, hQA, hQp, hne, h7, h7', hlt, hhalf,
      htop, horder, ⟨T, hT⟩, ⟨U, hU⟩, hall, ht, hsemi⟩

end FiveTransitive.HighDegreeOddMaxSevenEntrance

end CFSG
