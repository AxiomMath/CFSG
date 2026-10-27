module

public import Certificates.Data.B3Spor3Checks

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3S3

@[expose] def m11S3A : Array ℕ := #[0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3]

@[expose] def m11S3B : Array ℕ := #[3, 4, 7, 2, 5, 8, 6, 0, 1, 9, 10]

@[expose] def m11S3QGens : Array (Array ℕ) :=
  #[#[1, 2, 0, 5, 9, 7, 6, 3, 8, 10, 4],
  #[10, 4, 9, 0, 5, 1, 6, 2, 8, 7, 3]]

@[expose] def m11S3Lines : Array (Array ℕ) :=
  #[#[1, 2, 0, 5, 9, 7, 6, 3, 8, 10, 4],
  #[10, 4, 9, 0, 5, 1, 6, 2, 8, 7, 3],
  #[4, 9, 10, 1, 7, 2, 6, 0, 8, 3, 5],
  #[9, 10, 4, 2, 3, 0, 6, 1, 8, 5, 7]]

@[expose] def m11S3Trans : Array (Array ℕ) :=
  #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
  #[3, 0, 10, 5, 2, 1, 6, 4, 8, 9, 7],
  #[1, 9, 3, 10, 0, 5, 6, 2, 8, 4, 7],
  #[5, 0, 9, 4, 10, 3, 8, 2, 6, 7, 1]]

@[expose] def m11S3Rec : List ℕ := [0, 0, 0, 0]

@[expose] def m11S3CaseX : Array (Array ℕ) :=
  #[#[1, 2, 0, 5, 9, 7, 6, 3, 8, 10, 4]]

@[expose] def m11S3C0S : Array (Array ℕ) :=
  #[#[0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3],
  #[3, 4, 7, 2, 5, 8, 6, 0, 1, 9, 10],
  #[3, 7, 5, 0, 9, 2, 6, 1, 8, 4, 10],
  #[4, 3, 2, 0, 1, 9, 6, 5, 8, 10, 7],
  #[0, 9, 5, 7, 3, 1, 6, 10, 8, 2, 4],
  #[0, 3, 10, 2, 5, 7, 6, 9, 8, 4, 1]]

@[expose] def m11S3C0W : Array (List ℤ) :=
  #[[], [], [-1, -2, 1, 2, 1], [-2, -1, -3, 2, 3, 1], [-3, -4], [-4, 5, -2, -1, -3, 4, 2, 1]]

@[expose] def m11S3C0Base : Array ℕ := #[6, 8, 0, 1, 2, 3, 5, 7, 4, 9, 10]

@[expose] def m11S3C0Rels : List (ℕ × ℕ × ℕ) := [(0, 0, 0), (0, 0, 1), (0, 0, 2), (1, 1, 0), (1, 1, 1), (1, 1, 2), (2, 2, 0), (2, 3, 1), (2, 4, 2), (3, 3, 0), (3, 4, 1), (3, 2, 2), (4, 4, 0), (4, 2, 1), (4, 3, 2), (5, 5, 0), (5, 6, 1), (5, 7, 2), (6, 6, 0), (6, 7, 1), (6, 5, 2), (7, 7, 0), (7, 5, 1), (7, 6, 2), (8, 8, 0), (8, 9, 1), (8, 10, 2), (9, 9, 0), (9, 10, 1), (9, 8, 2), (10, 10, 0), (10, 8, 1), (10, 9, 2)]

@[expose] def m11S3C0Gens : Array (Array ℕ) :=
  #[#[1, 2, 0, 5, 9, 7, 6, 3, 8, 10, 4],
  #[5, 7, 3, 4, 2, 9, 6, 10, 8, 0, 1],
  #[0, 1, 2, 4, 3, 9, 8, 10, 6, 5, 7]]

@[expose] def m11S3Data : Data where
  n := 11
  A := m11S3A
  B := m11S3B
  QGens := m11S3QGens
  ord := 7920
  k3 := 2
  m3 := 880
  N3 := 9
  lines := m11S3Lines
  trans := m11S3Trans
  recs := m11S3Rec
  caseX := m11S3CaseX
  cases := #[{ S := m11S3C0S, W := m11S3C0W, base := m11S3C0Base, rels := m11S3C0Rels, gens := m11S3C0Gens, card := 18, crit := ⟨0, 1, 2, [], []⟩ }]

end CFSG.HardMathSupport.Solomon.Coordinator.B3S3
