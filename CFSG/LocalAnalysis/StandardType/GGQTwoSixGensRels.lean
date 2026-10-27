module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointSu

public section

namespace CFSG.StandardType.QTwo.SixPoint

@[expose] def qTwoSixRelsInWindow (inWindow : Fin 3 → Fin 18 → Prop) (s : Fin 3)
    (w : List (Fin 18 × Bool)) : Prop :=
  ∀ p ∈ w, inWindow s p.1

instance qTwoSixRelsInWindow_decidable (inWindow : Fin 3 → Fin 18 → Prop)
    [DecidableRel inWindow] (s : Fin 3) (w : List (Fin 18 × Bool)) :
    Decidable (qTwoSixRelsInWindow inWindow s w) :=
  inferInstanceAs (Decidable (∀ p ∈ w, inWindow s p.1))

@[expose] def qTwoSixRelsSplitSupport (inWindow : Fin 3 → Fin 18 → Prop)
    (support : Fin 18 → Finset (Fin 6)) : Prop :=
  ∀ w ∈ relsP,
    (∃ s : Fin 3, qTwoSixRelsInWindow inWindow s w) ∨
      ∃ a b : Fin 18, Disjoint (support a) (support b) ∧
        (support a ∪ support b).card ≤ 5 ∧
          w = [(a, true), (b, true), (a, false), (b, false)]

theorem qTwoSixRels_evalG_congr {X : Type} [Group X] {g h : Fin 18 → X}
    {w : List (Fin 18 × Bool)} (hgh : ∀ p ∈ w, g p.1 = h p.1) : evalG g w = evalG h w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    obtain ⟨i, b⟩ := p
    have hhead : g i = h i := hgh (i, b) (by simp)
    have htail : ∀ q ∈ w, g q.1 = h q.1 := fun q hq => hgh q (by simp [hq])
    change (cond b (g i) ((g i)⁻¹)) * evalG g w =
      (cond b (h i) ((h i)⁻¹)) * evalG h w
    rw [hhead, ih htail]

theorem qTwoSixRels_evalG_map {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (g : Fin 18 → X) (w : List (Fin 18 × Bool)) :
    evalG (fun i => f (g i)) w = f (evalG g w) := by
  induction w with
  | nil => simp [evalG]
  | cons p w ih =>
    obtain ⟨i, b⟩ := p
    simp only [evalG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, map_mul]
    cases b <;> simp

theorem qTwoSixRels_evalG_commutator {X : Type} [Group X] (g : Fin 18 → X) (a b : Fin 18) :
    evalG g [(a, true), (b, true), (a, false), (b, false)] =
      g a * g b * (g a)⁻¹ * (g b)⁻¹ := by
  simp only [evalG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    cond_true, cond_false]
  group

theorem qTwoSixRels_commutator_eq_one {G : Type} [Group G] {x y : G} (h : Commute x y) :
    x * y * x⁻¹ * y⁻¹ = 1 := by
  calc x * y * x⁻¹ * y⁻¹ = x * y * (x⁻¹ * y⁻¹) := by group
    _ = x * y * (y⁻¹ * x⁻¹) := by rw [h.inv_inv.eq]
    _ = 1 := by group

theorem qTwoSixRels_evalG_eq_one {X Y G : Type} [Group X] [Group Y] [Group G]
    (emb : Fin 3 → Y →* X) (hemb : ∀ s, Function.Injective (emb s))
    (native : Fin 18 → X) (hnative : ∀ w ∈ relsP, evalG native w = 1)
    (inWindow : Fin 3 → Fin 18 → Prop) (support : Fin 18 → Finset (Fin 6))
    (lift : Fin 3 → Fin 18 → Y)
    (hlift : ∀ s i, inWindow s i → emb s (lift s i) = native i)
    (g : Fin 18 → G) (φ : Fin 3 → Y →* G)
    (hφ : ∀ s i, inWindow s i → g i = φ s (lift s i))
    (hsplit : qTwoSixRelsSplitSupport inWindow support)
    (hcomm : ∀ a b : Fin 18, Disjoint (support a) (support b) →
      (support a ∪ support b).card ≤ 5 → Commute (g a) (g b)) :
    ∀ w ∈ relsP, evalG g w = 1 := by
  intro w hw
  rcases hsplit w hw with ⟨s, hs⟩ | ⟨a, b, hdisj, hcard, rfl⟩
  · have hcongr : evalG g w = evalG (fun i => φ s (lift s i)) w :=
      qTwoSixRels_evalG_congr fun p hp => hφ s p.1 (hs p hp)
    have hmap : evalG (fun i => φ s (lift s i)) w = φ s (evalG (lift s) w) :=
      qTwoSixRels_evalG_map (φ s) (lift s) w
    have hlift_eval : evalG (fun i => emb s (lift s i)) w = evalG native w :=
      qTwoSixRels_evalG_congr fun p hp => hlift s p.1 (hs p hp)
    have hone : evalG (lift s) w = 1 := by
      apply hemb s
      calc emb s (evalG (lift s) w)
          = evalG (fun i => emb s (lift s i)) w :=
            (qTwoSixRels_evalG_map (emb s) (lift s) w).symm
        _ = evalG native w := hlift_eval
        _ = 1 := hnative w hw
        _ = emb s 1 := (map_one (emb s)).symm
    rw [hcongr, hmap, hone, map_one]
  · rw [qTwoSixRels_evalG_commutator]
    exact qTwoSixRels_commutator_eq_one (hcomm a b hdisj hcard)

end CFSG.StandardType.QTwo.SixPoint

end
