module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Orbit
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoLevi
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Quasithin CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar Subgroup
  CFSG.AGLEmbeddingD2.Tits.GN516 CFSG.AGLEmbeddingD2.Tits.GN516.SimpleBQ
  CFSG.AGLEmbeddingD2.Tits.GN516.Nodes
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {Q : Type} [Group Q] [Finite Q] {L T : Subgroup Q} {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
  {π : K →* ↥L} {e : ℕ}

theorem nodeTransitive_of_nodeOrbit_eq_univ (hbq : BorelQuotient D n H π e)
    (hRN : T ≤ Subgroup.normalizer (L : Set Q))
    (h𝒜 : ∀ α ∈ (actHom hRN).range,
      ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    {i : Fin D.rank} (hi : nodeOrbit hbq (actHom hRN).range h𝒜 i = Set.univ) :
    NodeTransitive L T D H π := by
  intro p q
  have hp : p ∈ nodeOrbit hbq (actHom hRN).range h𝒜 i := by
    rw [hi]
    exact Set.mem_univ p
  have hq : q ∈ nodeOrbit hbq (actHom hRN).range h𝒜 i := by
    rw [hi]
    exact Set.mem_univ q
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  change nodeHom hbq (actHom hRN).range h𝒜 a i = p at ha
  change nodeHom hbq (actHom hRN).range h𝒜 b i = q at hb
  obtain ⟨t, hta⟩ := a.2
  obtain ⟨s, hsb⟩ := b.2
  set u : ↥T := s * t⁻¹ with hu_def
  refine ⟨u.1, u.2, ?_⟩
  have hcomp : ∀ (c d : ↥(actHom hRN).range) (x : Fin D.rank),
      nodeHom hbq (actHom hRN).range h𝒜 (c * d) x =
        nodeHom hbq (actHom hRN).range h𝒜 c
          (nodeHom hbq (actHom hRN).range h𝒜 d x) := by
    intro c d x
    rw [map_mul]
    rfl
  have hinv : nodeHom hbq (actHom hRN).range h𝒜 a⁻¹ p = i := by
    have h := hcomp a⁻¹ a i
    rw [inv_mul_cancel, map_one] at h
    change i = nodeHom hbq (actHom hRN).range h𝒜 a⁻¹
      (nodeHom hbq (actHom hRN).range h𝒜 a i) at h
    rw [ha] at h
    exact h.symm
  have hact : nodeHom hbq (actHom hRN).range h𝒜 (b * a⁻¹) p = q := by
    rw [hcomp b a⁻¹ p, hinv, hb]
  have hu_range : actHomRangeOfMem hRN u.2 = b * a⁻¹ := by
    apply Subtype.ext
    change actHom hRN u = (b * a⁻¹).1
    rw [hu_def, map_mul, map_inv, hta, hsb]
    rfl
  have hact_u : nodeHom hbq (actHom hRN).range h𝒜 (actHomRangeOfMem hRN u.2) p = q := by
    rw [hu_range]
    exact hact
  rw [← hact_u]
  exact map_parJ_subtype_conj hbq hRN h𝒜 u.2 p

theorem not_hasCompFactor_map_parJ_nodeOrbit (hbq : BorelQuotient D n H π e)
    (hLs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hT2 : IsPGroup 2 ↥T)
    (hL0 : ∀ (X : Type) [Group X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a)
    (hRN : T ≤ Subgroup.normalizer (L : Set Q))
    (h𝒜 : ∀ α ∈ (actHom hRN).range,
      ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (hsmall : BQSmall D) (hntr : ¬ NodeTransitive L T D H π) (i : Fin D.rank) :
    ¬ HasCompFactor ((parJ D H (nodeOrbit hbq (actHom hRN).range h𝒜 i)).map π) IsCalL0 := by
  classical
  let 𝒜 : Subgroup (MulAut ↥L) := (actHom hRN).range
  let O : Set (Fin D.rank) := nodeOrbit hbq 𝒜 h𝒜 i
  change ¬ HasCompFactor ((parJ D H O).map π) IsCalL0
  have h𝒜2 : IsPGroup 2 ↥𝒜 :=
    hT2.of_surjective (actHom hRN).rangeRestrict (actHom hRN).rangeRestrict_surjective
  have hT : (TauCeti.diagramGraph D.cartan).IsTree :=
    @CFSG.AGLEmbeddingD2.Tits.GN516.Conn.diagram_isTree K ↥L _ _ _ D n H π e hbq hLs hnab
  let act : MulAction ↥𝒜 (Fin D.rank) :=
    { smul := fun a x => nodeHom hbq 𝒜 h𝒜 a x
      one_smul := fun x => by
        change nodeHom hbq 𝒜 h𝒜 1 x = x
        rw [map_one]
        rfl
      mul_smul := fun a b x => by
        change nodeHom hbq 𝒜 h𝒜 (a * b) x =
          nodeHom hbq 𝒜 h𝒜 a (nodeHom hbq 𝒜 h𝒜 b x)
        rw [map_mul]
        rfl }
  have hadj : ∀ (a : ↥𝒜) (u v : Fin D.rank),
      (TauCeti.diagramGraph D.cartan).Adj (act.smul a u) (act.smul a v) ↔
        (TauCeti.diagramGraph D.cartan).Adj u v :=
    fun a u v =>
      CFSG.AGLEmbeddingD2.Tits.GN516.Core.nodePerm_adj_iff hbq a.1 (h𝒜 a.1 a.2) u v
  by_cases hcase : ∃ u ∈ O, ∃ v ∈ O, u ≠ v ∧ (TauCeti.diagramGraph D.cartan).Adj u v
  · obtain ⟨u, huO, v, hvO, huv, huvadj⟩ := hcase
    have huO' : u ∈ O := huO
    have hvO' : v ∈ O := hvO
    obtain ⟨a_u, ha_u⟩ := huO
    obtain ⟨a_v, ha_v⟩ := hvO
    change nodeHom hbq 𝒜 h𝒜 a_u i = u at ha_u
    change nodeHom hbq 𝒜 h𝒜 a_v i = v at ha_v
    have hcomp : ∀ (c d : ↥𝒜) (x : Fin D.rank),
        nodeHom hbq 𝒜 h𝒜 (c * d) x =
          nodeHom hbq 𝒜 h𝒜 c (nodeHom hbq 𝒜 h𝒜 d x) := by
      intro c d x
      rw [map_mul]
      rfl
    have hinv : nodeHom hbq 𝒜 h𝒜 a_u⁻¹ u = i := by
      have h := hcomp a_u⁻¹ a_u i
      rw [inv_mul_cancel, map_one] at h
      change i = nodeHom hbq 𝒜 h𝒜 a_u⁻¹ (nodeHom hbq 𝒜 h𝒜 a_u i) at h
      rw [ha_u] at h
      exact h.symm
    have hgu : act.smul (a_v * a_u⁻¹) u = v := by
      change nodeHom hbq 𝒜 h𝒜 (a_v * a_u⁻¹) u = v
      rw [hcomp a_v a_u⁻¹ u, hinv, ha_v]
    have hO : O = {u, v} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hx
        obtain ⟨b, hb⟩ := hx
        change nodeHom hbq 𝒜 h𝒜 b i = x at hb
        have hx' : act.smul (b * a_u⁻¹) u = x := by
          change nodeHom hbq 𝒜 h𝒜 (b * a_u⁻¹) u = x
          rw [hcomp b a_u⁻¹ u, hinv]
          exact hb
        rcases @CFSG.AGLEmbeddingD2.Tits.GN516.Tree.orbit_subset_of_adj
          (Fin D.rank) _ _ (TauCeti.diagramGraph D.cartan) _ hT (↥𝒜) _ _ act h𝒜2
          hadj u v huvadj ⟨a_v * a_u⁻¹, hgu⟩ (b * a_u⁻¹) with h | h
        · exact Or.inl (hx'.symm.trans h)
        · exact Or.inr (hx'.symm.trans h)
      · rintro (rfl | rfl)
        · exact huO'
        · exact hvO'
    have hrank : 3 ≤ D.rank := by
      by_contra h
      push Not at h
      have huniv : O = Set.univ := by
        rw [hO]
        apply Set.eq_univ_of_forall
        intro x
        by_contra hx
        rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
        have h3 : ({x, u, v} : Set (Fin D.rank)).ncard = 3 := by
          rw [Set.ncard_insert_of_notMem (by simp [hx.1, hx.2]),
            Set.ncard_insert_of_notMem (by simp [huv]), Set.ncard_singleton]
        have hle : ({x, u, v} : Set (Fin D.rank)).ncard ≤ D.rank := by
          have h' := Set.ncard_le_ncard (Set.subset_univ ({x, u, v} : Set (Fin D.rank)))
            (Set.toFinite _)
          rwa [Set.ncard_univ, Nat.card_fin] at h'
        omega
      exact hntr (nodeTransitive_of_nodeOrbit_eq_univ hbq hRN h𝒜 huniv)
    have hedge : SmallEdge D u v := hsmall.2 hrank u v huvadj
    have hperm : nodePerm hbq (a_v * a_u⁻¹).1
        (h𝒜 (a_v * a_u⁻¹).1 (a_v * a_u⁻¹).2) u = v := hgu
    have hdeg : (TauCeti.diagramGraph D.cartan).degree u =
        (TauCeti.diagramGraph D.cartan).degree v := by
      have h := degree_nodePerm hbq (a_v * a_u⁻¹).1
        (h𝒜 (a_v * a_u⁻¹).1 (a_v * a_u⁻¹).2) u
      rw [hperm] at h
      exact h.symm
    have hroot : Nat.card ↥(D.rootGroup (Pi.single u 1)) =
        Nat.card ↥(D.rootGroup (Pi.single v 1)) := by
      have h := card_rootGroup_eq_of_nodePerm hbq (a_v * a_u⁻¹).1
        (h𝒜 (a_v * a_u⁻¹).1 (a_v * a_u⁻¹).2) u
      rw [hperm] at h
      exact h.symm
    rcases hedge with hfirst | hdegne | hrootne
    · rw [hO]
      exact not_hasCompFactor_map_parJ_pair hbq hL0 hfirst
    · exact absurd hdeg hdegne
    · exact absurd hroot hrootne
  · push Not at hcase
    refine not_hasCompFactor_map_parJ_of_pairwise hbq hL0 hsmall.1 (J := O) ?_
    intro u hu v hv huv
    exact hcase u hu v hv huv

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
