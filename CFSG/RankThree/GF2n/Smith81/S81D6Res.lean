module

public import CFSG.RankThree.GF2n.Smith81.S81D6Ops
public import CFSG.RankThree.GF2n.Smith81.S81E7Cent2

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.GF2n.Smith81.E7Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem resV0_injective : Function.Injective (resV0 K) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  apply Subtype.ext
  apply Lam_faithful_V0 (K := K) l.2
  intro v hv
  obtain ⟨w, rfl⟩ := exists_emb_eq hv
  have h := resV0_induces l w
  rw [hl] at h
  simpa using h.symm

end CFSG.RankThree.GF2n.Smith81.D6Spin
