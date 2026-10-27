module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapPieces
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2SwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (swapDiagHom swapDiagHom_apply)

local instance twistedE6PilotSwapCTNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩


section Pieces

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  {σ : K →+* K} (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (A : Subgroup Kˣ) {t : G}

theorem SwapCover.exists_perfect_diag_le {T D E : Subgroup G} (h : SwapCover t T D E)
    (X : Subgroup G) (hXt : X ≤ centralizer ({t} : Set G)) :
    ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ P ≤ D ∧ P ≤ centralizer (X : Set G) ∧
      ∀ x ∈ h.piece X, x * (t * x * t⁻¹) ∈ P := by
  set P : Subgroup G := ((h.piece X).subgroupOf h.Kc).map (swapDiagHom h.le_centralizer) with hP
  refine ⟨P, ?_, ?_, ?_, fun x hx => ⟨⟨x, h.piece_le X hx⟩, mem_subgroupOf.2 hx, rfl⟩⟩
  · rw [hP, ← map_commutator,
      CFSG.SeitzReduction.commutator_subgroupOf_eq_self (h.piece_le X) (h.commutator_piece X)]
  · rintro _ ⟨k, -, rfl⟩
    exact h.diag_mem k k.2
  · rintro _ ⟨k, hk, rfl⟩
    exact h.diag_mem_centralizer hXt (mem_subgroupOf.1 hk)

theorem diag_mem_modelToG_relLevi {T D E : Subgroup G} (h : SwapCover t T D E) (hDL : D ≤ L)
    (htL : t ∈ centralizer (L : Set G)) (hA3 : 3 ≤ Nat.card A)
    (hA : ∀ c ∈ A, Units.map σ.toMonoidHom c = c) (r : Fin Tag.F4.rank) :
    ∀ x ∈ h.piece (relTorusG e A r), x * (t * x * t⁻¹) ∈ modelToG e (relLevi K {r}) := by
  obtain ⟨P, hPp, hPD, hPX, hP⟩ :=
    h.exists_perfect_diag_le (relTorusG e A r) (relTorusG_le_centralizer_singleton e A htL r)
  intro x hx
  exact perfect_le_modelToG_relLevi e A hA3 hA (hPD.trans hDL) hPX hPp (hP x hx)

theorem diag_mem_relRankOneG_one [CharP K 2] {T D E : Subgroup G} (h : SwapCover t T D E)
    (hDL : D ≤ L) (htL : t ∈ centralizer (L : Set G)) (hA3 : 3 ≤ Nat.card A)
    (hA : ∀ c ∈ A, Units.map σ.toMonoidHom c = c)
    (hperf : ⁅relRankOne σ 1, relRankOne σ 1⁆ = relRankOne σ 1) :
    ∀ x ∈ h.piece (relTorusG e A 1), x * (t * x * t⁻¹) ∈ relRankOneG e 1 := by
  obtain ⟨P, hPp, hPD, hPX, hP⟩ :=
    h.exists_perfect_diag_le (relTorusG e A 1) (relTorusG_le_centralizer_singleton e A htL 1)
  intro x hx
  exact perfect_le_relRankOneG_one e A hA3 hA hperf (hPD.trans hDL) hPX hPp (hP x hx)

theorem relTorusG_le_normalizer_Kc {N : F4Pilot.AmalgamNeighbour} {D E : Subgroup G}
    (h : SwapCover t (modelToG e (neighbourTorus K A N)) D E) (hAo : Odd (Nat.card A))
    {r : Fin Tag.F4.rank} (hr : r ∈ N.nodes) : relTorusG e A r ≤ normalizer (h.Kc : Set G) := by
  have : Finite Kˣ := inferInstance
  exact h.le_normalizer (relTorusG_le_centralizer_neighbourTorus e A N hr)
    (odd_orderOf_of_mem_relTorusG e A hAo r)

theorem pieceCore_eq_sup_of_mem_nodes {N : F4Pilot.AmalgamNeighbour} {D : Subgroup G}
    (h : SwapCover t (modelToG e (neighbourTorus K A N)) D (neighbourCore e A N))
    (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1) (hAo : Odd (Nat.card A))
    {r : Fin Tag.F4.rank} (hr : r ∈ N.nodes) :
    pieceCore e A {r} = h.piece (relTorusG e A r) ⊔
      (h.piece (relTorusG e A r)).map (MulAut.conj t).toMonoidHom := by
  rw [pieceCore_eq e A N (Finset.singleton_subset_iff.2 hr)]
  exact h.pieceCore_eq_sup htt (relTorusG_le_normalizer_Kc e A h hAo hr)
    (relTorusG_le_centralizer_singleton e A htL r)

theorem exists_mem_piece_diag_eq_relRankOneG {N : F4Pilot.AmalgamNeighbour} {D E : Subgroup G}
    (h : SwapCover t (modelToG e (neighbourTorus K A N)) D E) (htL : t ∈ centralizer (L : Set G))
    (hAo : Odd (Nat.card A)) {r : Fin Tag.F4.rank} (hr : r ∈ N.nodes) (hRD : relRankOneG e r ≤ D)
    (hperf : ⁅relRankOne σ r, relRankOne σ r⁆ = relRankOne σ r) :
    ∀ y ∈ relRankOneG e r, ∃ x ∈ h.piece (relTorusG e A r), x * (t * x * t⁻¹) = y :=
  h.exists_mem_piece_diag_eq (relTorusG_le_normalizer_Kc e A h hAo hr)
    (relTorusG_le_centralizer_singleton e A htL r) hRD (relRankOneG_le_centralizer e A r)
    (modelToG_perfect e (relRankOne_le_C0 σ r) hperf)

theorem piece_le_centralizer_piece_of_relLevi {T D E : Subgroup G} (h : SwapCover t T D E)
    (hDL : D ≤ L) (htL : t ∈ centralizer (L : Set G)) (hA3 : 3 ≤ Nat.card A)
    (hA : ∀ c ∈ A, Units.map σ.toMonoidHom c = c) {a b : Fin Tag.F4.rank}
    (hab : relLevi K {b} ≤ centralizer (relLevi K {a} : Set (ModGL TwistTag.E6.tag K))) :
    h.piece (relTorusG e A b) ≤ centralizer (h.piece (relTorusG e A a) : Set G) :=
  h.piece_le_centralizer_piece_of_le (diag_mem_modelToG_relLevi e A h hDL htL hA3 hA a)
    (diag_mem_modelToG_relLevi e A h hDL htL hA3 hA b) (modelToG_le_centralizer e hab)

theorem pieceCore_le_centralizer_pieceCore_of_swapCover {N : F4Pilot.AmalgamNeighbour}
    {D : Subgroup G}
    (h : SwapCover t (modelToG e (neighbourTorus K A N)) D (neighbourCore e A N))
    (hDL : D ≤ L) (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1) (hA3 : 3 ≤ Nat.card A)
    (hAo : Odd (Nat.card A)) (hA : ∀ c ∈ A, Units.map σ.toMonoidHom c = c)
    {a b : Fin Tag.F4.rank} (ha : a ∈ N.nodes) (hb : b ∈ N.nodes)
    (hab : relLevi K {b} ≤ centralizer (relLevi K {a} : Set (ModGL TwistTag.E6.tag K))) :
    pieceCore e A {b} ≤ centralizer (pieceCore e A {a} : Set G) := by
  rw [pieceCore_eq_sup_of_mem_nodes e A h htL htt hAo ha,
    pieceCore_eq_sup_of_mem_nodes e A h htL htt hAo hb]
  exact h.sup_le_centralizer_sup (piece_le_centralizer_piece_of_relLevi e A h hDL htL hA3 hA hab)

end Pieces

section Model

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {σ : K →+* K}
  (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (A : Subgroup Kˣ)

@[expose] noncomputable def relWeylG : G :=
  ((e.symm ⟨twistedE6RelWeyl K relWordXPrime, twistedE6RelWeyl_mem σ relWordXPrime⟩ : L) : G)

theorem relWeylG_mem : relWeylG e ∈ L := (e.symm _).2

theorem modelToG_map_su6Levi :
    modelToG e ((su6Levi σ).map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom) =
      (modelToG e (su6Levi σ)).map (MulAut.conj (relWeylG e)).toMonoidHom :=
  modelToG_map_conj e (su6Levi σ) ⟨_, twistedE6RelWeyl_mem σ relWordXPrime⟩

theorem map_relWeylG_neighbourTorus_X :
    (modelToG e (neighbourTorus K A .X)).map (MulAut.conj (relWeylG e)).toMonoidHom =
      modelToG e (neighbourTorus K A .X') := by
  rw [relWeylG, ← modelToG_map_conj e _ ⟨_, twistedE6RelWeyl_mem σ relWordXPrime⟩]
  exact congrArg _ (map_conj_relWordXPrime_neighbourTorus_X A)

theorem iSup_relRankOneG (hσ : Function.Surjective σ) : ⨆ r, relRankOneG e r = L := by
  have h1 : ⨆ r, (relRankOne σ r).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) = ⊤ :=
    SeitzQ2.iSup_subgroupOf_eq_top (iSup_relRankOne hσ)
  have h2 : ⨆ r, relRankOneG e r =
      ((⨆ r, (relRankOne σ r).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        e.symm.toMonoidHom).map L.subtype := by
    rw [Subgroup.map_iSup, Subgroup.map_iSup]
    rfl
  rw [h2, h1, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.symm.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

theorem isSimpleGroup_relRankOneG_one [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card (orbitField TwistTag.E6 K σ (relOrbit 1))) :
    IsSimpleGroup (relRankOneG e 1) := by
  have := isSimpleGroup_relRankOne_one σ hq
  have e1 := subgroupOfEquivOfLe (relRankOne_le_C0 σ 1)
  have e2 := UnitaryPilot.modelToGEquiv e ((relRankOne σ 1).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ))
  exact (e2.symm.trans e1).isSimpleGroup

end Model

@[expose] noncomputable def swapCoverX' {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] {σ : K →+* K} (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (A : Subgroup Kˣ) {t : G} (htL : t ∈ centralizer (L : Set G))
    (hX : SwapCover t (modelToG e (neighbourTorus K A .X)) (modelToG e (su6Levi σ))
      (neighbourCore e A .X)) :
    SwapCover t (modelToG e (neighbourTorus K A .X'))
      (modelToG e ((su6Levi σ).map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom))
      (neighbourCore e A .X') :=
  (hX.conj (relWeylG e) (mem_centralizer_iff.1 htL _ (relWeylG_mem e))).cast
    (map_relWeylG_neighbourTorus_X e A) (modelToG_map_su6Levi e).symm
    (neighbourCore_X'_eq_map_conj e A).symm

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {σ : K →+* K} (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (A : Subgroup Kˣ)

theorem exists_aligned_Y (hA3 : 3 ≤ Nat.card A) (hAo : Odd (Nat.card A))
    (hA : ∀ c ∈ A, Units.map σ.toMonoidHom c = c)
    (hRp : ⁅relRankOne σ 1, relRankOne σ 1⁆ = relRankOne σ 1)
    (hq1 : 4 ≤ Nat.card (orbitField TwistTag.E6 K σ (relOrbit 1))) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1)
    (hX : SwapCover t (modelToG e (neighbourTorus K A .X)) (modelToG e (su6Levi σ))
      (neighbourCore e A .X))
    (hY : SwapCover t (modelToG e (neighbourTorus K A .Y)) (modelToG e (omegaMinusLevi σ))
      (neighbourCore e A .Y)) :
    ∃ hY' : SwapCover t (modelToG e (neighbourTorus K A .Y)) (modelToG e (omegaMinusLevi σ))
      (neighbourCore e A .Y), hY'.piece (relTorusG e A 1) = hX.piece (relTorusG e A 1) := by
  have hsimple := isSimpleGroup_relRankOneG_one e hq1
  have hR1X : relRankOneG e 1 ≤ modelToG e (su6Levi σ) :=
    modelToG_mono e (relRankOne_le_su6Levi σ (by decide))
  have hR1Y : relRankOneG e 1 ≤ modelToG e (omegaMinusLevi σ) :=
    modelToG_mono e (relRankOne_le_omegaMinusLevi σ (by decide))
  have hdich := hX.piece_dichotomy hsimple
    (diag_mem_relRankOneG_one e A hX (modelToG_le e _) htL hA3 hA hRp)
    (exists_mem_piece_diag_eq_relRankOneG e A hX htL hAo (r := 1) (by decide) hR1X hRp)
  have hsup : hY.piece (relTorusG e A 1) ⊔
        (hY.piece (relTorusG e A 1)).map (MulAut.conj t).toMonoidHom =
      hX.piece (relTorusG e A 1) ⊔
        (hX.piece (relTorusG e A 1)).map (MulAut.conj t).toMonoidHom := by
    rw [← pieceCore_eq_sup_of_mem_nodes e A hY htL htt hAo (r := 1) (by decide),
      ← pieceCore_eq_sup_of_mem_nodes e A hX htL htt hAo (r := 1) (by decide)]
  have hne : hY.piece (relTorusG e A 1) ≠ ⊥ := by
    intro hbot
    obtain ⟨y, hy⟩ := exists_ne (1 : relRankOneG e 1)
    obtain ⟨x, hx, hxy⟩ := exists_mem_piece_diag_eq_relRankOneG e A hY htL hAo (r := 1) (by decide)
      hR1Y hRp y y.2
    rw [hbot, mem_bot] at hx
    subst hx
    apply hy
    apply Subtype.ext
    rw [← hxy]
    simp
  have htY : t ∈ centralizer (modelToG e (neighbourTorus K A .Y) : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 (modelToG_le e _)) htL
  rcases hX.piece_eq_or_eq_conj hY hsup hdich hne with h1 | h1
  · exact ⟨hY, h1⟩
  · refine ⟨hY.flip htY htt, ?_⟩
    rw [hY.piece_flip htY htt (relTorusG_le_centralizer_singleton e A htL 1), h1,
      map_conj_map_conj_of_mul_self htt]

theorem exists_swapFactor_2E6 (hL : IsSimpleGroup L) (hZ : center L = ⊥)
    (hA3 : 3 ≤ Nat.card A) (hAo : Odd (Nat.card A)) (hA : ∀ c ∈ A, Units.map σ.toMonoidHom c = c)
    {k : Type} [Field k] (ι : k →+* K) (hσk : ∀ c, σ (ι c) = ι c) (hq : 4 ≤ Nat.card k)
    {t : G} (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1)
    (hX : SwapCover t (modelToG e (neighbourTorus K A .X)) (modelToG e (su6Levi σ))
      (neighbourCore e A .X))
    (hY : SwapCover t (modelToG e (neighbourTorus K A .Y)) (modelToG e (omegaMinusLevi σ))
      (neighbourCore e A .Y)) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧ Nonempty (G₁ ⧸ center G₁ ≃* L) ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) ∧
      ∀ r, pieceCore e A {r} ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
  have hσ : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hRp : ∀ r, ⁅relRankOne σ r, relRankOne σ r⁆ = relRankOne σ r :=
    commutator_relRankOne_of_le ι hσk hq
  have hq1 : 4 ≤ Nat.card (orbitField TwistTag.E6 K σ (relOrbit 1)) :=
    hq.trans (card_le_card_orbitField ι hσk _)
  obtain ⟨hY', hal⟩ := exists_aligned_Y e A hA3 hAo hA (hRp 1) hq1 htL htt hX hY
  set F : Fin Tag.F4.rank → Subgroup G := fun r =>
    if r = 0 then hY'.piece (relTorusG e A 0) else hX.piece (relTorusG e A r) with hF
  have hF0 : F 0 = hY'.piece (relTorusG e A 0) := ite_eq_left rfl
  have hFr : ∀ r, r ≠ 0 → F r = hX.piece (relTorusG e A r) := fun r hr => ite_eq_right hr
  have hXn : ∀ r : Fin Tag.F4.rank, r ≠ 0 → r ∈ F4Pilot.AmalgamNeighbour.X.nodes := by decide
  have hM0 : pieceCore e A {0} = hY'.piece (relTorusG e A 0) ⊔
      (hY'.piece (relTorusG e A 0)).map (MulAut.conj t).toMonoidHom :=
    pieceCore_eq_sup_of_mem_nodes e A hY' htL htt hAo (by decide)
  have hMr : ∀ r, r ≠ 0 → pieceCore e A {r} = hX.piece (relTorusG e A r) ⊔
      (hX.piece (relTorusG e A r)).map (MulAut.conj t).toMonoidHom := fun r hr =>
    pieceCore_eq_sup_of_mem_nodes e A hX htL htt hAo (hXn r hr)
  have hFM : ∀ r, F r ≤ pieceCore e A {r} ∧
      (F r).map (MulAut.conj t).toMonoidHom ≤ pieceCore e A {r} := by
    intro r
    by_cases hr : r = 0
    · subst hr
      rw [hF0, hM0]
      exact ⟨le_sup_left, le_sup_right⟩
    · rw [hFr r hr, hMr r hr]
      exact ⟨le_sup_left, le_sup_right⟩
  have hM0j : ∀ j : Fin Tag.F4.rank, j ≠ 0 → j ≠ 1 →
      pieceCore e A {j} ≤ centralizer (pieceCore e A {0} : Set G) := by
    intro j hj0 hj1
    have hj23 : j = 2 ∨ j = 3 := by revert j; decide
    rcases hj23 with rfl | rfl
    · exact pieceCore_le_centralizer_pieceCore_of_swapCover e A hY' (modelToG_le e _) htL htt hA3
        hAo hA
        (a := 0) (b := 2) (by decide) (by decide) (relLevi_le_centralizer_zero (Or.inl rfl))
    · exact pieceCore_le_centralizer_pieceCore_of_swapCover e A (swapCoverX' e A htL hX)
        (modelToG_le e _)
        htL htt hA3 hAo hA (a := 0) (b := 3) (by decide) (by decide)
        (relLevi_le_centralizer_zero (Or.inr rfl))
  have hc : ∀ i j, (F j).map (MulAut.conj t).toMonoidHom ≤ centralizer (F i : Set G) := by
    intro i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · rw [hi, hj, hF0]
      exact hY'.map_piece_le_centralizer_piece _ _
    · rw [hi]
      by_cases hj1 : j = 1
      · rw [hj1, hF0, hFr 1 (by decide), ← hal]
        exact hY'.map_piece_le_centralizer_piece _ _
      · exact (hFM j).2.trans ((hM0j j hj hj1).trans
          (centralizer_le (SetLike.coe_subset_coe.2 (hFM 0).1)))
    · rw [hj]
      by_cases hi1 : i = 1
      · rw [hi1, hF0, hFr 1 (by decide), ← hal]
        exact hY'.map_piece_le_centralizer_piece _ _
      · exact (hFM 0).2.trans ((le_centralizer_iff.1 (hM0j i hi hi1)).trans
          (centralizer_le (SetLike.coe_subset_coe.2 (hFM i).1)))
    · rw [hFr i hi, hFr j hj]
      exact hX.map_piece_le_centralizer_piece _ _
  have hperf : ∀ r, ⁅F r, F r⁆ = F r := by
    intro r
    by_cases hr : r = 0
    · rw [hr, hF0]
      exact hY'.commutator_piece _
    · rw [hFr r hr]
      exact hX.commutator_piece _
  have hFL : ∀ r, ∀ x ∈ F r, x * (t * x * t⁻¹) ∈ L := by
    intro r x hx
    by_cases hr : r = 0
    · rw [hr, hF0] at hx
      exact modelToG_le e _ (hY'.diag_mem x (hY'.piece_le _ hx))
    · rw [hFr r hr] at hx
      exact modelToG_le e _ (hX.diag_mem x (hX.piece_le _ hx))
  have hRF : ∀ r, ∀ y ∈ relRankOneG e r, ∃ x ∈ F r, x * (t * x * t⁻¹) = y := by
    intro r
    by_cases hr : r = 0
    · rw [hr, hF0]
      exact exists_mem_piece_diag_eq_relRankOneG e A hY' htL hAo (r := 0) (by decide)
        (modelToG_mono e (relRankOne_le_omegaMinusLevi σ (by decide))) (hRp 0)
    · rw [hFr r hr]
      exact exists_mem_piece_diag_eq_relRankOneG e A hX htL hAo (hXn r hr)
        (modelToG_mono e (relRankOne_le_su6Levi σ hr)) (hRp r)
  set G₁ : Subgroup G := ⨆ r, F r with hG₁
  have h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) :=
    LinearPilot.map_conj_iSup_le_centralizer hc
  have hδL : ∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L := LinearPilot.mul_conj_mem_of_mem_iSup h₁₂ hFL
  have hsurj : ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
    intro y hy
    rw [← iSup_relRankOneG e hσ] at hy
    refine LinearPilot.exists_mul_conj_eq_of_mem_iSup h₁₂ (fun r y hy => ?_) y hy
    obtain ⟨x, hx, hxy⟩ := hRF r y hy
    exact ⟨x, le_iSup F r hx, hxy⟩
  have hqs : CFSG.Open.IsQuasisimple G₁ := LinearPilot.isQuasisimple_of_linearSwapDiag h₁₂
    (LinearPilot.commutator_iSup_eq_of_forall F hperf) hL hδL hsurj
  have hiso := nonempty_quotient_center_mulEquiv_of_swapDiag' h₁₂ hδL hsurj hZ
  refine ⟨G₁, hqs, hiso, h₁₂, hδL, hsurj, fun r => ?_⟩
  have hle : F r ≤ G₁ := le_iSup F r
  by_cases hr : r = 0
  · rw [hr, hM0]
    rw [hr, hF0] at hle
    exact sup_le_sup hle (map_mono hle)
  · rw [hMr r hr]
    rw [hFr r hr] at hle
    exact sup_le_sup hle (map_mono hle)

end Main

end CFSG.SeitzReduction.TwistedE6Pilot
