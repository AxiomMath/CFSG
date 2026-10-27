module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open CFSG.QuasithinUnique

theorem un5te_relIndex_le {A : Type*} [Group A] [Finite A] {N R T : Subgroup A}
    (h : R ≤ T) : N.relIndex R ≤ N.relIndex T :=
  Subgroup.relIndex_le_of_le_right h Subgroup.index_ne_zero_of_finite

theorem un5te_card_le {A : Type*} [Group A] [Finite A] {N K₀ T R : Subgroup A} [N.Normal]
    (hS : IsSylowTwoOf T K₀) (hR : IsPGroup 2 R) (hRK : R ≤ K₀) :
    Nat.card R * Nat.card ↥(T ⊓ N) ≤ Nat.card ↥(R ⊓ N) * Nat.card T := by
  obtain ⟨S, hRS, hS'⟩ := exists_isSylowTwoOf_of_le hRK hR
  obtain ⟨g, -, hg⟩ := hS.exists_conj hS'
  have hN : N.map (MulAut.conj g).toMonoidHom = N := Subgroup.Normal.map_conj_eq N g
  have hrel : N.relIndex S = N.relIndex T := by
    have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) N T
      (MulAut.conj g).injective
    rwa [hN, ← hg] at h
  have h1 : N.relIndex R ≤ N.relIndex T := hrel ▸ un5te_relIndex_le hRS
  have hR' := Subgroup.relIndex_mul_card N R
  have hT' := Subgroup.relIndex_mul_card N T
  rw [inf_comm] at hR' hT'
  rw [← hR', ← hT']
  calc N.relIndex R * Nat.card ↥(R ⊓ N) * Nat.card ↥(T ⊓ N)
      = N.relIndex R * (Nat.card ↥(R ⊓ N) * Nat.card ↥(T ⊓ N)) := by ring
    _ ≤ N.relIndex T * (Nat.card ↥(R ⊓ N) * Nat.card ↥(T ⊓ N)) := Nat.mul_le_mul_right _ h1
    _ = Nat.card ↥(R ⊓ N) * (N.relIndex T * Nat.card ↥(T ⊓ N)) := by ring

end CFSG.Quasithin.H13.F431.Un.OL5
