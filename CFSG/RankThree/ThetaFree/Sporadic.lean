module

public import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.RankThree.Native.MathieuRealThree
public import CFSG.RankThree.Native.FiveTwoSporadic
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KS.FischerSections
public import CFSG.RankThree.GroupTheory.SteinbergBYHighTwoRankCover
public import CFSG.Sporadic.J4

public section

namespace CFSG.RankThree.ThetaFree

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
open CFSG.Blueprint
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Assembly.RankThreeEven (localRank)

theorem quotient_witness_of_mathieu {S : Type} [Group S]
    (hS : Nonempty (S ≃* NativeSporadic.M11) ∨ Nonempty (S ≃* NativeSporadic.M12) ∨
      Nonempty (S ≃* NativeSporadic.M22) ∨ Nonempty (S ≃* NativeSporadic.M23) ∨
      Nonempty (S ≃* NativeSporadic.M24)) :
    ∃ V : Subgroup S, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ((∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Nat.card (normalizer (V : Set S))) ∨
        ∃ t ∈ normalizer (V : Set S), orderOf t = 3 ∧ IsConj t t⁻¹) := by
  obtain ⟨x, z, b, hx, hz, hxz, hb⟩ :=
    Native.five_mathieu_real_three_elements_centralizing_involutions hS
  obtain ⟨hV, hV2⟩ := zpowers_ne_bot_and_isPGroup_two hz
  exact ⟨zpowers z, hV, hV2, Or.inr ⟨x,
    centralizer_le_normalizer _ (Native.mem_centralizer_zpowers_of_commute hxz.symm), hx,
    isConj_iff.2 ⟨b, hb⟩⟩⟩

theorem quotient_witness_of_eleven {S : Type} [Group S]
    (hS : Nonempty (S ≃* NativeSporadic.J3) ∨ Nonempty (S ≃* NativeSporadic.Co1) ∨
      Nonempty (S ≃* NativeSporadic.Co2) ∨ Nonempty (S ≃* NativeSporadic.Co3) ∨
      Nonempty (S ≃* NativeSporadic.HS) ∨ Nonempty (S ≃* NativeSporadic.McL) ∨
      Nonempty (S ≃* NativeSporadic.HN) ∨ Nonempty (S ≃* NativeSporadic.Suz) ∨
      Nonempty (S ≃* NativeSporadic.Ly) ∨ Nonempty (S ≃* NativeSporadic.Th) ∨
      Nonempty (S ≃* NativeSporadic.ON)) :
    ∃ V : Subgroup S, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ((∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Nat.card (normalizer (V : Set S))) ∨
        ∃ t ∈ normalizer (V : Set S), orderOf t = 3 ∧ IsConj t t⁻¹) := by
  obtain ⟨z, y, hz, hy, -, -, -, hyN⟩ :=
    Native.eleven_sporadic_models_commuting_five_and_two_elements hS
  obtain ⟨hV, hV2⟩ := zpowers_ne_bot_and_isPGroup_two hz
  refine ⟨zpowers z, hV, hV2, Or.inl ⟨5, Nat.prime_five, by norm_num, ?_⟩⟩
  rw [← hy]
  exact Subgroup.orderOf_dvd_natCard _ hyN

theorem j4OrderHyp' : SectionRank.J4OrderHyp := by
  show Nat.card NativeSporadic.J4 ∣ 86775571046077562880
  rw [CFSG.Sporadic.J4.card_J4]

theorem center_eq_bot_of_odd_cover {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    (hodd : Odd (Nat.card (center L))) {s : TauCeti.SporadicName}
    (hs : s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .He ∨ s = .Ru)
    (e : L ⧸ center L ≃* Carrier s) : center L = ⊥ := by
  have : Group.IsPerfect L := hL.1
  have hker := ker_comp_mk'_center e
  have hC : (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).ker ≤ center L := hker.le
  have hπ : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hodd' : Odd (Nat.card (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).ker) := by
    rw [hker]
    exact hodd
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact (SectionRank.four_small_sporadic_odd_cover_step hL hodd
      (Or.inr (Or.inr (Or.inr rfl))) e).2 rfl
  · rw [← hker]
    exact SectionRank.J2_perfect_odd_cover_trivial _ hπ hC hodd'
  · rw [← hker]
    exact SectionRank.J4_perfect_odd_cover_trivial j4OrderHyp' _ hπ hC hodd'
  · rw [← hker]
    exact SectionRank.He_perfect_odd_cover_trivial _ hπ hC hodd'
  · rw [← hker]
    exact SectionRank.Ru_perfect_odd_cover_trivial _ hπ hC hodd'

theorem sectionsForceEvenRankFour_fi23_fi24prime' :
    SectionsForceEvenRankFour (Carrier .Fi23) ∧ SectionsForceEvenRankFour (Carrier .Fi24Prime) :=
  sectionsForceEvenRankFour_fi23_fi24prime sectionsForceEvenRankFour_Fi22 hasSection_fi23_fi22
    hasSection_fi24prime_fi23

theorem theta_free_sporadic_component_normalization_at_three_of
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour) {G : Type} [Group G] [Finite G]
    (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) :
    (∀ L ∈ thetaComponents 3 G, NativeSporadic.SporadicRep (L ⧸ center L) →
      A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L → NativeSporadic.SporadicRep (L ⧸ center L) →
      A ≤ normalizer (L : Set G) := by
  have he4 : ¬ 4 ≤ CFSG.Assembly.evenRank G := by
    rw [← GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank]
    omega
  have hmain : ∀ L ∈ thetaComponents 3 G, NativeSporadic.SporadicRep (L ⧸ center L) →
      A ≤ normalizer (L : Set G) := by
    rintro L hL ⟨s, ⟨e⟩⟩
    have hLc : IsComponent L := Theta.isComponent_of_mem_thetaComponents Nat.prime_three hθ hL
    have hodd : IsPGroup 3 (center L) → Odd (Nat.card (center L)) := fun hZ3 => by
      obtain ⟨n, hn⟩ := hZ3.exists_card_eq
      rw [hn]
      exact Odd.pow (by decide)
    have hcover : (s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .He ∨ s = .Ru) →
        A ≤ normalizer (L : Set G) := fun hs =>
      normalizes_of_center_eq_bot hθ he hq h3 hA hL fun hZ3 =>
        center_eq_bot_of_odd_cover hLc.1 (hodd hZ3) hs e
    have hmath : (Nonempty (L ⧸ center L ≃* NativeSporadic.M11) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.M12) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.M22) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.M23) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.M24)) → A ≤ normalizer (L : Set G) := fun h =>
      normalizes_of_quotient_witness hθ he hq h3 hA hL fun _ _ => quotient_witness_of_mathieu h
    have heleven : (Nonempty (L ⧸ center L ≃* NativeSporadic.J3) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.Co1) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.Co2) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.Co3) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.HS) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.McL) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.HN) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.Suz) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.Ly) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.Th) ∨
        Nonempty (L ⧸ center L ≃* NativeSporadic.ON)) → A ≤ normalizer (L : Set G) := fun h =>
      normalizes_of_quotient_witness hθ he hq h3 hA hL fun _ _ => quotient_witness_of_eleven h
    cases s with
    | M11 => exact hmath (Or.inl ⟨e⟩)
    | M12 => exact hmath (Or.inr (Or.inl ⟨e⟩))
    | M22 => exact hmath (Or.inr (Or.inr (Or.inl ⟨e⟩)))
    | M23 => exact hmath (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))
    | M24 => exact hmath (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩))))
    | J1 => exact hcover (Or.inl rfl)
    | J2 => exact hcover (Or.inr (Or.inl rfl))
    | J3 => exact heleven (Or.inl ⟨e⟩)
    | J4 => exact hcover (Or.inr (Or.inr (Or.inl rfl)))
    | Co1 => exact heleven (Or.inr (Or.inl ⟨e⟩))
    | Co2 => exact heleven (Or.inr (Or.inr (Or.inl ⟨e⟩)))
    | Co3 => exact heleven (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))
    | Fi22 => exact absurd (sectionsForceEvenRankFour_Fi22 G L (center L) ⟨e⟩) he4
    | Fi23 => exact absurd (sectionsForceEvenRankFour_fi23_fi24prime'.1 G L (center L) ⟨e⟩) he4
    | Fi24Prime =>
      exact absurd (sectionsForceEvenRankFour_fi23_fi24prime'.2 G L (center L) ⟨e⟩) he4
    | HS => exact heleven (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))))
    | McL => exact heleven (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))))
    | He => exact hcover (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | Ru => exact hcover (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    | Suz => exact heleven (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨e⟩))))))))
    | ONan => exact heleven (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr ⟨e⟩))))))))))
    | HN => exact heleven (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))))))
    | Ly => exact heleven (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨e⟩)))))))))
    | Th => exact heleven (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨e⟩))))))))))
    | B => exact absurd (hB G L (center L) ⟨e⟩) he4
    | M =>
      by_contra hLA
      obtain ⟨-, hK⟩ := three_component_orbit_local_central_cube_obstruction hθ he hq h3 hA hL hLA
      obtain ⟨-, -, hsimple, hnab, -⟩ := hK L ⟨1, A.one_mem, by
        rw [conjugate, inv_one]
        ext x
        simp⟩
      have : IsSimpleGroup (L ⧸ center L) := hsimple
      exact he4 (hM G L (center L) (L ⧸ center L) hnab ⟨MulEquiv.refl _⟩ ⟨e⟩)
  exact ⟨hmain, fun L hL => hmain L (mem_thetaComponents_of_isComponent Nat.prime_three hθ hL)⟩

end CFSG.RankThree.ThetaFree
