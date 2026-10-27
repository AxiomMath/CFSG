module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Root
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6A5Std
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6FrameK

public section

namespace CFSG.StandardType.TableCRes

@[expose] def tcAddL (a b : List ℤ) : List ℤ := List.zipWith (· + ·) a b

@[expose] def tcNegL (a : List ℤ) : List ℤ := a.map fun x => -x

@[expose] def tcA2L (a b : List ℤ) : List (List ℤ) :=
  [a, b, tcAddL a b, tcNegL a, tcNegL b, tcNegL (tcAddL a b)]

@[expose] def tcCompL (X : List (List ℤ)) : List (List ℤ) :=
  e6RootList.filter fun g => X.all fun m => e6ip g m == 0

@[expose] def tab12 : List (ℤ × ℤ) :=
  [(2, -1), (-1, 2), (1, 1), (-2, 1), (1, -2), (-1, -1), (1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1),
    (1, -1)]

@[expose] def tcRootTab : List (ℤ × ℤ) := [(2, -1), (-1, 2), (1, 1), (-2, 1), (1, -2), (-1, -1)]

@[expose] def wtTab : List (ℤ × ℤ) := [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]

@[expose] def e6CanonIdx : List (ℕ × ℕ) :=
  [(0, 46), (0, 47), (0, 48), (0, 49), (0, 50), (0, 51), (0, 52), (0, 53), (0, 54), (0, 55),
   (1, 39), (1, 40), (1, 41), (1, 43), (1, 44), (1, 45), (1, 53), (1, 54), (1, 55), (2, 37),
   (2, 38), (2, 42), (2, 44), (2, 45), (2, 51), (2, 52), (2, 55), (3, 36), (3, 42), (3, 43),
   (3, 45), (3, 50), (3, 52), (3, 54), (4, 42), (4, 43), (4, 44), (4, 50), (4, 51), (4, 53),
   (5, 37), (5, 38), (5, 40), (5, 41), (5, 48), (5, 49), (5, 55), (6, 36), (6, 39), (6, 41),
   (6, 47), (6, 49), (6, 54), (7, 39), (7, 40), (7, 47), (7, 48), (7, 53), (8, 36), (8, 38),
   (8, 46), (8, 49), (8, 52), (9, 37), (9, 46), (9, 48), (9, 51), (10, 46), (10, 47), (10, 50),
   (11, 36), (11, 38), (11, 41), (11, 45), (12, 37), (12, 40), (12, 44), (13, 39), (13, 43),
   (14, 42), (16, 37), (16, 38), (16, 40), (16, 41), (16, 44), (16, 45), (17, 36), (17, 39),
   (17, 41), (17, 43), (17, 45), (18, 39), (18, 40), (18, 43), (18, 44), (19, 36), (19, 38),
   (19, 42), (19, 45), (20, 37), (20, 42), (20, 44), (21, 42), (21, 43), (22, 36), (22, 38),
   (22, 41), (23, 37), (23, 40), (24, 39), (26, 36), (26, 38), (26, 41), (27, 37), (27, 40),
   (28, 39), (30, 36), (30, 38), (31, 37), (33, 36)]

@[expose] def e6CanonBases : List (List ℤ × List ℤ) :=
  e6CanonIdx.map fun ij => (e6RootList[ij.1]!, e6RootList[ij.2]!)

@[expose] def smulL (k : ℤ) (a : List ℤ) : List ℤ := a.map fun x => k * x

@[expose] def tcComb5 (c : List ℤ) (d₀ d₁ d₂ d₃ d₄ : List ℤ) : List ℤ :=
  match c with
  | [c0, c1, c2, c3, c4] =>
    tcAddL (tcAddL (tcAddL (tcAddL (smulL c0 d₀) (smulL c1 d₁)) (smulL c2 d₂)) (smulL c3 d₃))
      (smulL c4 d₄)
  | _ => []

@[expose] def chainRootsL (d₀ d₁ d₂ d₃ d₄ : List ℤ) : List (List ℤ) :=
  std30.map fun c => tcComb5 c d₀ d₁ d₂ d₃ d₄

@[expose] def tcLineL (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) : List (List ℤ) :=
  e6RootList.filter fun g =>
    !(decide (g ∈ tcA2L c₁ d₁ ++ tcA2L c₂ d₂)) &&
      (decide ((e6ip g c₃, e6ip g d₃) = u₀) || decide ((e6ip g c₃, e6ip g d₃) = (-u₀.1, -u₀.2)))

@[expose] def A5Last (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ δ₂ δ₃ δ₄ : List ℤ) : Prop :=
  (∀ g ∈ tcA2L c₁ d₁ ++ tcA2L c₂ d₂ ++ tcLineL c₁ d₁ c₂ d₂ c₃ d₃ u₀,
    g ∈ chainRootsL δ₀ δ₁ δ₂ δ₃ δ₄) ∧
  (∀ g ∈ chainRootsL δ₀ δ₁ δ₂ δ₃ δ₄, g ∈ tcA2L c₁ d₁ ++ tcA2L c₂ d₂ ++ tcLineL c₁ d₁ c₂ d₂ c₃ d₃ u₀)

instance (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ δ₂ δ₃ δ₄ : List ℤ) :
    Decidable (A5Last c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁ δ₂ δ₃ δ₄) := by
  unfold A5Last
  infer_instance

@[expose] def A5L4 (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ δ₂ δ₃ : List ℤ) : Prop :=
  ∃ δ₄ ∈ tcA2L c₂ d₂, e6ip δ₃ δ₄ = -1 ∧ e6ip δ₂ δ₄ = 0 ∧ e6ip δ₁ δ₄ = 0 ∧ e6ip δ₀ δ₄ = 0 ∧
    A5Last c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁ δ₂ δ₃ δ₄

instance (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ δ₂ δ₃ : List ℤ) :
    Decidable (A5L4 c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁ δ₂ δ₃) := by
  unfold A5L4
  infer_instance

@[expose] def A5L3 (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ δ₂ : List ℤ) : Prop :=
  ∃ δ₃ ∈ tcA2L c₂ d₂, e6ip δ₂ δ₃ = -1 ∧ e6ip δ₁ δ₃ = 0 ∧ e6ip δ₀ δ₃ = 0 ∧
    A5L4 c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁ δ₂ δ₃

instance (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ δ₂ : List ℤ) :
    Decidable (A5L3 c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁ δ₂) := by
  unfold A5L3
  infer_instance

@[expose] def A5L2 (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ : List ℤ) : Prop :=
  ∃ δ₂ ∈ tcLineL c₁ d₁ c₂ d₂ c₃ d₃ u₀, e6ip δ₁ δ₂ = -1 ∧ e6ip δ₀ δ₂ = 0 ∧
    A5L3 c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁ δ₂

instance (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) (δ₀ δ₁ : List ℤ) :
    Decidable (A5L2 c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁) := by
  unfold A5L2
  infer_instance

@[expose] def tcA5L (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) : Prop :=
  ∃ δ₀ ∈ tcA2L c₁ d₁, ∃ δ₁ ∈ tcA2L c₁ d₁, e6ip δ₀ δ₁ = -1 ∧ A5L2 c₁ d₁ c₂ d₂ c₃ d₃ u₀ δ₀ δ₁

instance (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) (u₀ : ℤ × ℤ) : Decidable (tcA5L c₁ d₁ c₂ d₂ c₃ d₃ u₀) := by
  unfold tcA5L
  infer_instance

@[expose] def wtRep : List (ℤ × ℤ) := [(1, 0), (0, 1), (1, -1)]

abbrev FrameL (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) : Prop :=
  e6ip c₃ d₃ = -1 ∧
  (∀ g ∈ e6RootList, (g ∈ tcA2L c₁ d₁ ++ tcA2L c₂ d₂ ↔ (e6ip g c₃ = 0 ∧ e6ip g d₃ = 0))) ∧
  (∀ g ∈ e6RootList, g ∉ tcA2L c₁ d₁ ++ tcA2L c₂ d₂ → (e6ip g c₃, e6ip g d₃) ∈ tab12) ∧
  (∀ g ∈ e6RootList, g ∉ tcA2L c₁ d₁ ++ tcA2L c₂ d₂ → (e6ip g c₃, e6ip g d₃) ∈ tcRootTab →
    ∀ m ∈ tcA2L c₁ d₁ ++ tcA2L c₂ d₂, e6ip g m = 0) ∧
  (∀ g ∈ e6RootList, g ∉ tcA2L c₁ d₁ ++ tcA2L c₂ d₂ → (e6ip g c₃, e6ip g d₃) ∈ wtTab →
    (∃ m ∈ tcA2L c₁ d₁, e6ip g m ≠ 0) ∧ (∃ m ∈ tcA2L c₂ d₂, e6ip g m ≠ 0)) ∧
  (∀ u₀ ∈ wtRep, tcA5L c₁ d₁ c₂ d₂ c₃ d₃ u₀)

instance (c₁ d₁ c₂ d₂ c₃ d₃ : List ℤ) : Decidable (FrameL c₁ d₁ c₂ d₂ c₃ d₃) := by
  unfold FrameL
  infer_instance

theorem e6_canon_frames_1 :
    ∀ p₁ ∈ e6CanonBases.take 30, ∀ p₂ ∈ e6CanonBases,
      (e6ip p₁.1 p₂.1 = 0 ∧ e6ip p₁.1 p₂.2 = 0 ∧ e6ip p₁.2 p₂.1 = 0 ∧ e6ip p₁.2 p₂.2 = 0) →
      ∃ c₃ ∈ tcCompL (tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2),
        ∃ d₃ ∈ tcCompL (tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2),
        FrameL p₁.1 p₁.2 p₂.1 p₂.2 c₃ d₃ := by
  intro p₁ hp₁
  rw [e6CanonBases, ← List.map_take] at hp₁
  have h : FrameK.sliceI (e6CanonIdx.take 30) e6CanonIdx FrameK.framesData1 = true := by
    decide +kernel
  exact FrameK.frames_of _ _ _ h p₁ hp₁

theorem e6_canon_frames_2 :
    ∀ p₁ ∈ (e6CanonBases.drop 30).take 30, ∀ p₂ ∈ e6CanonBases,
      (e6ip p₁.1 p₂.1 = 0 ∧ e6ip p₁.1 p₂.2 = 0 ∧ e6ip p₁.2 p₂.1 = 0 ∧ e6ip p₁.2 p₂.2 = 0) →
      ∃ c₃ ∈ tcCompL (tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2),
        ∃ d₃ ∈ tcCompL (tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2),
        FrameL p₁.1 p₁.2 p₂.1 p₂.2 c₃ d₃ := by
  intro p₁ hp₁
  rw [e6CanonBases, ← List.map_drop, ← List.map_take] at hp₁
  have h :
      FrameK.sliceI ((e6CanonIdx.drop 30).take 30) e6CanonIdx FrameK.framesData2 = true := by
    decide +kernel
  exact FrameK.frames_of _ _ _ h p₁ hp₁

theorem e6_canon_frames_3 :
    ∀ p₁ ∈ (e6CanonBases.drop 60).take 30, ∀ p₂ ∈ e6CanonBases,
      (e6ip p₁.1 p₂.1 = 0 ∧ e6ip p₁.1 p₂.2 = 0 ∧ e6ip p₁.2 p₂.1 = 0 ∧ e6ip p₁.2 p₂.2 = 0) →
      ∃ c₃ ∈ tcCompL (tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2),
        ∃ d₃ ∈ tcCompL (tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2),
        FrameL p₁.1 p₁.2 p₂.1 p₂.2 c₃ d₃ := by
  intro p₁ hp₁
  rw [e6CanonBases, ← List.map_drop, ← List.map_take] at hp₁
  have h :
      FrameK.sliceI ((e6CanonIdx.drop 60).take 30) e6CanonIdx FrameK.framesData3 = true := by
    decide +kernel
  exact FrameK.frames_of _ _ _ h p₁ hp₁

theorem e6_canon_frames_4 :
    ∀ p₁ ∈ e6CanonBases.drop 90, ∀ p₂ ∈ e6CanonBases,
      (e6ip p₁.1 p₂.1 = 0 ∧ e6ip p₁.1 p₂.2 = 0 ∧ e6ip p₁.2 p₂.1 = 0 ∧ e6ip p₁.2 p₂.2 = 0) →
      ∃ c₃ ∈ tcCompL (tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2),
        ∃ d₃ ∈ tcCompL (tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2),
        FrameL p₁.1 p₁.2 p₂.1 p₂.2 c₃ d₃ := by
  intro p₁ hp₁
  rw [e6CanonBases, ← List.map_drop] at hp₁
  have h : FrameK.sliceI (e6CanonIdx.drop 90) e6CanonIdx FrameK.framesData4 = true := by
    decide +kernel
  exact FrameK.frames_of _ _ _ h p₁ hp₁

theorem e6_canon_slices : ∀ p ∈ e6CanonBases, p ∈ e6CanonBases.take 30 ∨
    p ∈ (e6CanonBases.drop 30).take 30 ∨ p ∈ (e6CanonBases.drop 60).take 30 ∨
    p ∈ e6CanonBases.drop 90 := by
  decide +kernel

theorem e6_canon_frames :
    ∀ p₁ ∈ e6CanonBases, ∀ p₂ ∈ e6CanonBases,
      (e6ip p₁.1 p₂.1 = 0 ∧ e6ip p₁.1 p₂.2 = 0 ∧ e6ip p₁.2 p₂.1 = 0 ∧ e6ip p₁.2 p₂.2 = 0) →
      ∃ c₃ ∈ tcCompL (tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2),
        ∃ d₃ ∈ tcCompL (tcA2L p₁.1 p₁.2 ++ tcA2L p₂.1 p₂.2),
        FrameL p₁.1 p₁.2 p₂.1 p₂.2 c₃ d₃ := by
  intro p₁ hp₁
  rcases e6_canon_slices p₁ hp₁ with h | h | h | h
  · exact e6_canon_frames_1 p₁ h
  · exact e6_canon_frames_2 p₁ h
  · exact e6_canon_frames_3 p₁ h
  · exact e6_canon_frames_4 p₁ h

theorem e6_canon_cover :
    ∀ a ∈ e6RootList, ∀ b ∈ e6RootList, e6ip a b = -1 →
      ∃ p ∈ e6CanonBases, p.1 ∈ tcA2L a b ∧ p.2 ∈ tcA2L a b := by
  have h : FrameK.coverI e6CanonIdx FrameK.coverData = true := by
    decide +kernel
  exact FrameK.cover_of _ _ h

theorem e6_canon_length : ∀ p ∈ e6CanonBases, p.1.length = 6 ∧ p.2.length = 6 := by
  decide +kernel

theorem e6_canon_roots : ∀ p ∈ e6CanonBases, p.1 ∈ e6RootList ∧ p.2 ∈ e6RootList ∧
    e6ip p.1 p.2 = -1 := by
  decide +kernel

end CFSG.StandardType.TableCRes

end
