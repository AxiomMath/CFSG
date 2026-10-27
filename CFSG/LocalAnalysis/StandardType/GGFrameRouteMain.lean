module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePsiTargets
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteQTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRegionDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

theorem main_fsPoint_E7
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ =>
      ((lab.tag = .twA ∧ lab.rank = 6) ∨ (lab.tag = .D ∧ lab.rank = 6) ∨
        (lab.tag = .twE6 ∧ lab.rank = 0)) ∧ lab.n = 1))
    (hFSx : LargeEvenMarking L (fun lab _ _ _ _ _ =>
        lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B ∧ Subgroup.center L = ⊥)
    (hFSy : LargeEvenMarking L (fun lab _ _ _ _ _ =>
        ((lab.tag = .twA ∧ lab.rank = 6) ∨ (lab.tag = .twE6 ∧ lab.rank = 0)) ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B ∧
        ∃ y ∈ B, ∃ K : Subgroup G, LargeEvenSStar 3 B y K ∧
          (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal ∧
          Subgroup.center K = ⊥ ∧
          LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1)) :
    FSPoint B Bs (fun lab => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) := by
  unfold CFSG.StandardType.LargeEvenMarking CFSG.Assembly.LargeEvenMarkingLegacy at hmark
  obtain ⟨hc, lab, hlab, hraw⟩ := hmark
  by_cases hDlab : lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1
  ·
    have hmarkD : LargeEvenMarking L (fun lab _ _ _ _ _ =>
        lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) :=
      ⟨hc, lab, hlab, largeEvenRawDatum_mono (fun R _ I F h => by
        obtain ⟨hs, hna, θ, _⟩ := h
        exact ⟨hs, hna, θ, hDlab⟩) hraw⟩
    have hx := hFSx hmarkD
    obtain ⟨hxB, hSstar⟩ := sStar_of_restHyp hR
    have hmarkFSLab : LargeEvenMarking L (fun lab _ _ _ _ _ => FSLab lab) :=
      largeEvenMarking_mono (by
        intro lab R _ I F θ h
        exact ⟨h.2.2, Or.inl ⟨h.1, h.2.1⟩⟩) hmarkD
    have hnorm : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
      fsEnds_normal B Bs x L D J hR hmarkFSLab
    exact ⟨hx.1, x, hxB, L, hSstar, hnorm, hx.2, hmarkD⟩
  ·
    have hmarkQ : LargeEvenMarking L (fun lab _ _ _ _ _ =>
        ((lab.tag = .twA ∧ lab.rank = 6) ∨ (lab.tag = .twE6 ∧ lab.rank = 0)) ∧ lab.n = 1) :=
      ⟨hc, lab, hlab, largeEvenRawDatum_mono (fun R _ I F h => by
        obtain ⟨hs, hna, θ, hP⟩ := h
        obtain ⟨hdisj, hn⟩ := hP
        refine ⟨hs, hna, θ, ?_, hn⟩
        rcases hdisj with hA | hD | hC
        · exact Or.inl hA
        · exact absurd ⟨hD.1, hD.2, hn⟩ hDlab
        · exact Or.inr hC) hraw⟩
    obtain ⟨hcard, y, hyB, K, hSStar, hnorm, hcenter, hmarkK⟩ := hFSy hmarkQ
    exact ⟨hcard, y, hyB, K, hSStar, hnorm, hcenter, hmarkK⟩

theorem main_fsPoint_E8
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ =>
      ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .twA ∧ lab.rank = 8) ∨
        (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1))
    (hFSx : LargeEvenMarking L (fun lab _ _ _ _ _ =>
        ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B ∧ Subgroup.center L = ⊥)
    (hFSy : LargeEvenMarking L (fun lab _ _ _ _ _ =>
        lab.tag = .twA ∧ lab.rank = 8 ∧ lab.n = 1) →
      Nat.card Bs = 3 * Nat.card B ∧
        ∃ y ∈ B, ∃ K : Subgroup G, LargeEvenSStar 3 B y K ∧
          (K.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal ∧
          Subgroup.center K = ⊥ ∧
          LargeEvenMarking K (fun lab _ _ _ _ _ =>
            ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1)) :
    FSPoint B Bs (fun lab =>
      ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1) := by
  unfold CFSG.StandardType.LargeEvenMarking CFSG.Assembly.LargeEvenMarkingLegacy at hmark
  obtain ⟨hc, lab, hlab, hraw⟩ := hmark
  by_cases hA8 : lab.tag = .twA ∧ lab.rank = 8 ∧ lab.n = 1
  ·
    have hmarkA8 : LargeEvenMarking L (fun lab _ _ _ _ _ =>
        lab.tag = .twA ∧ lab.rank = 8 ∧ lab.n = 1) :=
      ⟨hc, lab, hlab, largeEvenRawDatum_mono (fun R _ I F h => by
        obtain ⟨hs, hna, θ, _⟩ := h
        exact ⟨hs, hna, θ, hA8.1, hA8.2.1, hA8.2.2⟩) hraw⟩
    obtain ⟨hcard, y, hyB, K, hSStar, hnorm, hcenter, hmarkK⟩ := hFSy hmarkA8
    exact ⟨hcard, y, hyB, K, hSStar, hnorm, hcenter, hmarkK⟩
  ·
    have hmarkFS : LargeEvenMarking L (fun lab _ _ _ _ _ =>
        ((lab.tag = .twD ∧ lab.rank = 7) ∨ (lab.tag = .E7 ∧ lab.rank = 0)) ∧ lab.n = 1) :=
      ⟨hc, lab, hlab, largeEvenRawDatum_mono (fun R _ I F h => by
        obtain ⟨hs, hna, θ, hP⟩ := h
        obtain ⟨hdisj, hn⟩ := hP
        refine ⟨hs, hna, θ, ?_, hn⟩
        rcases hdisj with hD | hA | hC
        · exact Or.inl hD
        · exact absurd ⟨hA.1, hA.2, hn⟩ hA8
        · exact Or.inr hC) hraw⟩
    have hx := hFSx hmarkFS
    obtain ⟨hxB, hSstar⟩ := sStar_of_restHyp hR
    have hmarkFSLab : LargeEvenMarking L (fun lab _ _ _ _ _ => FSLab lab) :=
      largeEvenMarking_mono (by
        intro lab R _ I F θ h
        refine ⟨h.2, ?_⟩
        rcases h.1 with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)) hmarkFS
    have hnorm : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
      fsEnds_normal B Bs x L D J hR hmarkFSLab
    exact ⟨hx.1, x, hxB, L, hSstar, hnorm, hx.2, hmarkFS⟩

end CFSG.StandardType.FrameRoute

end
