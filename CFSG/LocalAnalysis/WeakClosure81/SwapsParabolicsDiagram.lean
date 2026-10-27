module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsMaxParabolicOver SwapsParabolics)

variable {G : Type} [Group G]

private theorem isMaxParabolicOver_conj {X S P : Subgroup G} {g : G}
    (hP : IsMaxParabolicOver X S P) :
    IsMaxParabolicOver (X.map (MulAut.conj g).toMonoidHom)
      (S.map (MulAut.conj g).toMonoidHom) (P.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hPX, hN, hPne, hmax⟩ := hP
  set f : G →* G := (MulAut.conj g).toMonoidHom
  have hsurj : Function.Surjective f := (MulAut.conj g).surjective
  refine ⟨Subgroup.map_mono hPX, ?_, fun h =>
    hPne (Subgroup.map_injective (MulAut.conj g).injective h), fun Q hPQ hQX => ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq S (MulAut.conj g),
      ← Subgroup.map_inf X _ _ (MulAut.conj g).injective]
    exact Subgroup.map_mono hN
  · have hPle : P ≤ Q.comap f := fun p hp => hPQ (Subgroup.mem_map_of_mem f hp)
    have hle : Q.comap f ≤ X := fun y hy => by
      obtain ⟨x, hx, hxy⟩ := hQX hy
      rw [(MulAut.conj g).injective hxy] at hx
      exact hx
    rcases hmax _ hPle hle with h | h
    · exact Or.inl (by rw [← Subgroup.map_comap_eq_self_of_surjective hsurj Q, h])
    · exact Or.inr (by rw [← Subgroup.map_comap_eq_self_of_surjective hsurj Q, h])

theorem isDiagramNontrivial_of_swapsParabolics {L T : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) (hU : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L)
    (hpair : ∃ P₀ P₁ : Subgroup G, ∀ P : Subgroup G,
      IsMaxParabolicOver L (T ⊓ L) P → P = P₀ ∨ P = P₁)
    (hsw : SwapsParabolics T L) :
    E2.IsDiagramNontrivial T L (T ⊓ L) := by
  intro P' hP' hBP' hTP'
  obtain ⟨t, ht, P, hP, hPt⟩ := hsw
  obtain ⟨P₀, P₁, h01⟩ := hpair
  set f : G →* G := (MulAut.conj t).toMonoidHom
  have hLt : L.map f = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTL ht)
  have hTt : T.map f = T := Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ht)
  have hUt : (T ⊓ L).map f = T ⊓ L := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hTt, hLt]
  have hP'over : IsMaxParabolicOver L (T ⊓ L) P' := by
    obtain ⟨⟨hP'L, -⟩, hne, hmax⟩ := hP'
    refine ⟨hP'L, hBP', hne, fun Q hPQ hQL => ?_⟩
    by_cases hQ : Q = L
    · exact Or.inr hQ
    · exact Or.inl (hmax Q ⟨hQL, T ⊓ L, hU, hBP'.trans hPQ⟩ hQ hPQ)
  have hP't : P'.map f = P' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTP' ht)
  have hPt' : IsMaxParabolicOver L (T ⊓ L) (P.map f) := by
    have h := isMaxParabolicOver_conj (g := t) hP
    rwa [hLt, hUt] at h
  have hPP' : P ≠ P' := fun h => hPt (by rw [h, hP't])
  have hcover : ∀ M : Subgroup G, IsMaxParabolicOver L (T ⊓ L) M → M = P ∨ M = P' := by
    intro M hM
    rcases h01 M hM with hM | hM <;> rcases h01 P hP with hP0 | hP0 <;>
      rcases h01 P' hP'over with hP'0 | hP'0
    all_goals
      first
        | exact Or.inl (hM.trans hP0.symm)
        | exact Or.inr (hM.trans hP'0.symm)
        | exact absurd (hP0.trans hP'0.symm) hPP'
  rcases hcover _ hPt' with h | h
  · exact hPt h
  · exact hPP' (Subgroup.map_injective (MulAut.conj t).injective (h.trans hP't.symm))

end CFSG.LocalAnalysis.WeakClosure81
