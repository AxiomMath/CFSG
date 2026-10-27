module

public import Certificates.Data.B3Spor3.M11

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3S3

@[expose] def m11S3DataO : Data where
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
  cases := #[{ S := m11S3C0S, W := m11S3C0W, base := m11S3C0Base, rels := m11S3C0Rels, gens := m11S3C0Gens, card := 18, crit := ⟨1, 0, 0, [2], [1]⟩ }]

end CFSG.HardMathSupport.Solomon.Coordinator.B3S3
