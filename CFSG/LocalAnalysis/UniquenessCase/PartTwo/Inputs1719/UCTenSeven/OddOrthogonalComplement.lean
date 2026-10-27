module

public import CFSG.ClassicalInvolution.RouteD.MultiModelOrthGeom
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddSmallOrthogonal
import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
import CFSG.HardMathSupport.Malle.E27Lie.Cross.OrthOddPairs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup Module QuadraticMap CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open scoped MatrixGroups
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {m : ℕ} (A : Fin m → Frame Q)

private def perpAll : Submodule K V := ⨅ i, (A i).perp

private def spanAll : Submodule K V := ⨆ i, (A i).span

omit [Finite K] [FiniteDimensional K V] in
private lemma mem_perpAll {x : V} : x ∈ perpAll A ↔ ∀ i, (A i).coords x = 0 := by
  rw [perpAll, Submodule.mem_iInf]
  exact forall_congr' fun i => Frame.mem_perp_iff (A i)

omit [Finite K] [FiniteDimensional K V] in
private lemma polar_eq_zero_of_mem_spanAll_of_mem_perpAll
    {x y : V} (hx : x ∈ spanAll A) (hy : y ∈ perpAll A) : polar Q x y = 0 := by
  have hyi : ∀ i, y ∈ (A i).perp := (Submodule.mem_iInf _).mp hy
  refine Submodule.iSup_induction (p := fun i => (A i).span) (motive := fun z => polar Q z y = 0)
    hx (fun i z hz => ?_) ?_ ?_
  · obtain ⟨X, rfl⟩ := hz
    rw [polar_comm]
    exact (Frame.mem_perp_iff_forall_incl (A i)).mp (hyi i) X
  · simp
  · intro x z hx hz
    rw [polar_add_left, hx, hz, add_zero]

private noncomputable def proj : V →ₗ[K] V := ∑ i, ((A i).incl).comp ((A i).coords)

omit [Finite K] [FiniteDimensional K V] in
private lemma proj_apply (x : V) :
    proj A x = ∑ i, (A i).incl ((A i).coords x) := by
  rw [proj, LinearMap.sum_apply]
  simp [LinearMap.comp_apply]

omit [Finite K] [FiniteDimensional K V] in
private lemma coords_incl_of_ne (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    {i k : Fin m} (hik : i ≠ k) (X : Matrix (Fin 2) (Fin 2) K) :
    (A k).coords ((A i).incl X) = 0 := by
  have h : (A i).incl X ∈ (A k).perp :=
    (Frame.mem_perp_iff_forall_incl (A k)).mpr fun Y => horth i k hik X Y
  exact (Frame.mem_perp_iff (A k)).mp h

omit [Finite K] [FiniteDimensional K V] in
private lemma coords_proj (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (x : V) (k : Fin m) : (A k).coords (proj A x) = (A k).coords x := by
  rw [proj_apply, map_sum,
    Finset.sum_eq_single k (fun i _ hik => coords_incl_of_ne A horth hik _)
      (fun hk => absurd (Finset.mem_univ k) hk)]
  exact Frame.coords_incl (A k) ((A k).coords x)

omit [Finite K] [FiniteDimensional K V] in
private lemma sub_proj_mem_perpAll (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (x : V) : x - proj A x ∈ perpAll A := by
  rw [mem_perpAll]
  intro k
  rw [map_sub, coords_proj A horth x k, sub_self]

omit [Finite K] [FiniteDimensional K V] in
private lemma mem_spanAll_proj (x : V) : proj A x ∈ spanAll A := by
  rw [proj_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨_, rfl⟩

omit [Finite K] [FiniteDimensional K V] in
private lemma proj_eq_of_mem_spanAll (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    {x : V} (hx : x ∈ spanAll A) : proj A x = x := by
  have hN : spanAll A ≤ LinearMap.ker (LinearMap.id - proj A) := by
    refine iSup_le fun i => ?_
    intro y hy
    obtain ⟨X, rfl⟩ := hy
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rw [proj_apply, Finset.sum_eq_single i]
    · rw [Frame.coords_incl]
    · intro k _ hki
      rw [coords_incl_of_ne A horth (Ne.symm hki), map_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hxN : x ∈ LinearMap.ker (LinearMap.id - proj A) := hN hx
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hxN
  exact hxN.symm

omit [Finite K] [FiniteDimensional K V] in
private lemma eq_zero_of_mem_spanAll_of_forall_polar
    (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j)) {x : V}
    (hx : x ∈ spanAll A) (h : ∀ y ∈ spanAll A, polar Q x y = 0) : x = 0 := by
  have hxP : proj A x = x := proj_eq_of_mem_spanAll A horth hx
  have hcomp : ∀ k : Fin m, (A k).incl ((A k).coords x) = 0 := by
    intro k
    refine (Frame.polarNondegOn_span (A k)) _ ⟨_, rfl⟩ ?_
    intro y hy
    obtain ⟨Y, rfl⟩ := hy
    have h0 : polar Q x ((A k).incl Y) = 0 :=
      h _ (Submodule.mem_iSup_of_mem k ⟨Y, rfl⟩)
    have hxP' : x = ∑ i, (A i).incl ((A i).coords x) := by
      calc x = proj A x := hxP.symm
        _ = ∑ i, (A i).incl ((A i).coords x) := proj_apply A x
    rw [hxP'] at h0
    have hbil : (polarBilin Q) (∑ i, (A i).incl ((A i).coords x)) ((A k).incl Y) = 0 := by
      rwa [polarBilin_apply_apply]
    rw [map_sum, LinearMap.sum_apply] at hbil
    have hsum : (∑ i, polar Q ((A i).incl ((A i).coords x)) ((A k).incl Y)) = 0 := by
      simpa [polarBilin_apply_apply] using hbil
    have hsingle : (∑ i, polar Q ((A i).incl ((A i).coords x)) ((A k).incl Y)) =
        polar Q ((A k).incl ((A k).coords x)) ((A k).incl Y) :=
      Finset.sum_eq_single k (fun i _ hik => horth i k hik _ Y)
        (fun hk => absurd (Finset.mem_univ k) hk)
    rw [hsingle] at hsum
    exact hsum
  rw [← hxP, proj_apply]
  exact Finset.sum_eq_zero fun k _ => hcomp k

omit [Finite K] [FiniteDimensional K V] in
private lemma disjoint_spanAll_perpAll (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j)) :
    Disjoint (spanAll A) (perpAll A) := by
  rw [Submodule.disjoint_def]
  intro x hx hxperp
  refine eq_zero_of_mem_spanAll_of_forall_polar A horth hx fun y hy => ?_
  rw [polar_comm]
  exact polar_eq_zero_of_mem_spanAll_of_mem_perpAll A hy hxperp

omit [Finite K] [FiniteDimensional K V] in
private lemma codisjoint_spanAll_perpAll (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j)) :
    Codisjoint (spanAll A) (perpAll A) := by
  rw [codisjoint_iff, eq_top_iff]
  intro x _
  refine Submodule.mem_sup.mpr ⟨proj A x, mem_spanAll_proj A x,
    x - proj A x, sub_proj_mem_perpAll A horth x, by abel⟩

omit [Finite K] [FiniteDimensional K V] in
private lemma isCompl_spanAll_perpAll (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j)) :
    IsCompl (spanAll A) (perpAll A) :=
  ⟨disjoint_spanAll_perpAll A horth, codisjoint_spanAll_perpAll A horth⟩

omit [Finite K] [FiniteDimensional K V] in
private lemma mem_perpAll_of_forall_polar_spanAll
    (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j)) {x : V}
    (h : ∀ y ∈ spanAll A, polar Q x y = 0) : x ∈ perpAll A := by
  have hmem : x - proj A x ∈ perpAll A := sub_proj_mem_perpAll A horth x
  have hproj : proj A x = 0 := by
    refine eq_zero_of_mem_spanAll_of_forall_polar A horth (mem_spanAll_proj A x) fun y hy => ?_
    rw [show proj A x = x - (x - proj A x) by abel, polar_sub_left, h y hy, zero_sub,
      neg_eq_zero]
    rw [polar_comm]
    exact polar_eq_zero_of_mem_spanAll_of_mem_perpAll A hy hmem
  have : x = x - proj A x := by rw [hproj, sub_zero]
  rw [this]
  exact hmem

omit [Finite K] [FiniteDimensional K V] in
private lemma nondegenerate_perpAll (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (hQ : (polarBilin Q).Nondegenerate) :
    (polarBilin (Q.comp (perpAll A).subtype)).Nondegenerate :=
  CFSG.ClassicalGroups.Orthogonal.Small.nondegenerate_comp_subtype hQ
    (isCompl_spanAll_perpAll A horth).symm
    (fun u hu w hw => by
      rw [polar_comm]
      exact polar_eq_zero_of_mem_spanAll_of_mem_perpAll A hw hu)

omit [Finite K] [FiniteDimensional K V] in
private lemma mem_perpAll_iff_fixed (h2 : (2 : K) ≠ 0) {x : V} :
    x ∈ perpAll A ↔ ∀ i, (A i).La (-1) x = x := by
  rw [mem_perpAll]
  constructor
  · intro hx i
    rw [Frame.La_neg_one_apply, hx i]
    simp
  · intro hx i
    have h : (2 : K) • (A i).incl ((A i).coords x) = 0 := by
      have h' := hx i
      rw [Frame.La_neg_one_apply] at h'
      rw [sub_eq_self] at h'
      exact h'
    have hz : (A i).incl ((A i).coords x) = 0 := by
      rcases smul_eq_zero.mp h with h0 | h0
      · exact absurd h0 h2
      · exact h0
    have hc : (A i).coords x = 0 := by
      have h1 := congrArg (A i).coords hz
      rw [Frame.coords_incl, map_zero] at h1
      exact h1
    exact hc

omit [Finite K] [FiniteDimensional K V] in
private lemma maps_perpAll_of_mem_sylow (h2 : (2 : K) ≠ 0)
    {G : Subgroup (V ≃ₗ[K] V)} (T : Sylow 2 G)
    (hTA : ∀ t ∈ (T : Subgroup G), ∀ i, ∃ k,
      (t : V ≃ₗ[K] V) * (A i).La (-1) * (t : V ≃ₗ[K] V)⁻¹ = (A k).La (-1))
    {t : G} (ht : t ∈ (T : Subgroup G)) :
    (t : V ≃ₗ[K] V) ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub (perpAll A) := by
  refine CFSG.ClassicalGroups.Orthogonal.Small.mem_stabSub.mpr fun x => ?_
  constructor
  · intro hx
    rw [mem_perpAll_iff_fixed A h2] at hx ⊢
    intro i
    obtain ⟨k, hk⟩ := hTA (t⁻¹) (Subgroup.inv_mem _ ht) i
    have hk' : (t : V ≃ₗ[K] V)⁻¹ * (A i).La (-1) * (t : V ≃ₗ[K] V) = (A k).La (-1) := by
      simpa using hk
    have hmul : (A i).La (-1) * (t : V ≃ₗ[K] V) = (t : V ≃ₗ[K] V) * (A k).La (-1) := by
      calc (A i).La (-1) * (t : V ≃ₗ[K] V)
          = (t : V ≃ₗ[K] V) * ((t : V ≃ₗ[K] V)⁻¹ * (A i).La (-1) * (t : V ≃ₗ[K] V)) := by group
        _ = (t : V ≃ₗ[K] V) * (A k).La (-1) := by rw [hk']
    calc (A i).La (-1) ((t : V ≃ₗ[K] V) x) = ((A i).La (-1) * (t : V ≃ₗ[K] V)) x := rfl
      _ = ((t : V ≃ₗ[K] V) * (A k).La (-1)) x := by rw [hmul]
      _ = (t : V ≃ₗ[K] V) ((A k).La (-1) x) := rfl
      _ = (t : V ≃ₗ[K] V) x := by rw [hx k]
  · intro hx
    rw [mem_perpAll_iff_fixed A h2] at hx ⊢
    intro i
    obtain ⟨k, hk⟩ := hTA t ht i
    have hmul : (A i).La (-1) * (t : V ≃ₗ[K] V)⁻¹ = (t : V ≃ₗ[K] V)⁻¹ * (A k).La (-1) := by
      calc (A i).La (-1) * (t : V ≃ₗ[K] V)⁻¹
          = (t : V ≃ₗ[K] V)⁻¹ * ((t : V ≃ₗ[K] V) * (A i).La (-1) * (t : V ≃ₗ[K] V)⁻¹) := by group
        _ = (t : V ≃ₗ[K] V)⁻¹ * (A k).La (-1) := by rw [hk]
    calc (A i).La (-1) x = (A i).La (-1) ((t : V ≃ₗ[K] V)⁻¹ ((t : V ≃ₗ[K] V) x)) := by simp
      _ = ((A i).La (-1) * (t : V ≃ₗ[K] V)⁻¹) ((t : V ≃ₗ[K] V) x) := rfl
      _ = ((t : V ≃ₗ[K] V)⁻¹ * (A k).La (-1)) ((t : V ≃ₗ[K] V) x) := by rw [hmul]
      _ = (t : V ≃ₗ[K] V)⁻¹ ((A k).La (-1) ((t : V ≃ₗ[K] V) x)) := rfl
      _ = (t : V ≃ₗ[K] V)⁻¹ ((t : V ≃ₗ[K] V) x) := by rw [hx k]
      _ = x := by simp

omit [Finite K] [FiniteDimensional K V] in
private lemma fixes_spanAll {g : V ≃ₗ[K] V}
    (hgspan : ∀ i, ∀ x ∈ (A i).span, g x = x) :
    ∀ s ∈ spanAll A, g s = s := by
  intro s hs
  refine Submodule.iSup_induction (p := fun i => (A i).span) (motive := fun z => g z = z)
    hs (fun i z hz => hgspan i z hz) ?_ ?_
  · simp
  · intro x y hx hy
    rw [map_add, hx, hy]

omit [Finite K] [FiniteDimensional K V] in
private lemma maps_perpAll_of_fixes_spanAll (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgspan : ∀ i, ∀ x ∈ (A i).span, g x = x) :
    g ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub (perpAll A) := by
  have hfixS : ∀ s ∈ spanAll A, g s = s := fixes_spanAll A hgspan
  have hforward : ∀ x, x ∈ perpAll A → g x ∈ perpAll A := by
    intro x hx
    refine mem_perpAll_of_forall_polar_spanAll A horth fun y hy => ?_
    have hgy : g⁻¹ y = y := by
      calc g⁻¹ y = g⁻¹ (g y) := by rw [hfixS y hy]
        _ = y := by simp
    have hy' : g⁻¹ y ∈ spanAll A := by rw [hgy]; exact hy
    calc polar Q (g x) y = polar Q (g x) (g (g⁻¹ y)) := by simp
      _ = polar Q x (g⁻¹ y) := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO x _
      _ = 0 := by
        rw [polar_comm]
        exact polar_eq_zero_of_mem_spanAll_of_mem_perpAll A hy' hx
  have hbackward : ∀ x, g x ∈ perpAll A → x ∈ perpAll A := by
    intro x hx
    have hgOinv : g⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem hgO
    have hforward' : ∀ z, z ∈ perpAll A → g⁻¹ z ∈ perpAll A := by
      intro z hz
      refine mem_perpAll_of_forall_polar_spanAll A horth fun y hy => ?_
      have hy' : g y ∈ spanAll A := by rw [hfixS y hy]; exact hy
      calc polar Q (g⁻¹ z) y = polar Q (g⁻¹ z) (g⁻¹ (g y)) := by simp
        _ = polar Q z (g y) :=
            CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgOinv z (g y)
        _ = 0 := by
            rw [polar_comm]
            exact polar_eq_zero_of_mem_spanAll_of_mem_perpAll A hy' hz
    rw [← LinearEquiv.symm_apply_apply g x]
    exact hforward' (g x) hx
  exact CFSG.ClassicalGroups.Orthogonal.Small.mem_stabSub.mpr fun x =>
    ⟨hforward x, hbackward x⟩





private def hypPairSubtype {W : Submodule K V} (P : HypPair (Q.comp W.subtype)) : HypPair Q where
  e := (P.e : V)
  f := (P.f : V)
  Q_e := P.Q_e
  Q_f := P.Q_f
  polar_ef := P.polar_ef

private def frameOfSubtype {W : Submodule K V} (H : Frame (Q.comp W.subtype)) : Frame Q where
  P := hypPairSubtype H.P
  P' := hypPairSubtype H.P'
  orth := ⟨H.orth.ee, H.orth.ef, H.orth.fe, H.orth.ff⟩

omit [Finite K] [FiniteDimensional K V] in
private lemma incl_frameOfSubtype {W : Submodule K V} (H : Frame (Q.comp W.subtype))
    (X : Matrix (Fin 2) (Fin 2) K) :
    (frameOfSubtype H).incl X = (H.incl X : V) := by
  simp [frameOfSubtype, hypPairSubtype, Frame.incl_apply]

omit [Finite K] [FiniteDimensional K V] in
private lemma span_frameOfSubtype_le {W : Submodule K V} (H : Frame (Q.comp W.subtype)) :
    (frameOfSubtype H).span ≤ W := by
  rintro x ⟨X, rfl⟩
  rw [incl_frameOfSubtype]
  exact (H.incl X).2

omit [Finite K] [FiniteDimensional K V] in
private lemma false_of_frame_perpAll
    (hfull : ∀ H : Frame Q, (∀ i, SpanOrth H (A i)) → False)
    (H : Frame (Q.comp (perpAll A).subtype)) : False := by
  refine hfull (frameOfSubtype H) fun i => ?_
  intro X Y
  have hx : (frameOfSubtype H).incl X ∈ perpAll A := span_frameOfSubtype_le H ⟨X, rfl⟩
  exact (Frame.mem_perp_iff_forall_incl (A i)).mp ((Submodule.mem_iInf _).mp hx i) Y

private lemma finrank_perpAll_le_four (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hfull : ∀ H : Frame Q, (∀ i, SpanOrth H (A i)) → False) :
    finrank K (perpAll A) ≤ 4 := by
  by_contra h
  have h5 : 5 ≤ finrank K (perpAll A) := by omega
  obtain ⟨P, hP⟩ := CFSG.HardMathSupport.Malle.E27Lie.exists_two_hypPairs_odd
    (K := K) (V := perpAll A) h2 (nondegenerate_perpAll A horth hQ) h5
  exact false_of_frame_perpAll A hfull ⟨P 0, P 1, hP 0 1 (by decide)⟩

private def frameQuadPlus : Frame (quadPlus 2 K) where
  P :=
    { e := plusVec 2 K 0 true
      f := plusVec 2 K 0 false
      Q_e := quadPlus_plusVec 2 K 0 true
      Q_f := quadPlus_plusVec 2 K 0 false
      polar_ef := by rw [polar_quadPlus_plusVec]; simp }
  P' :=
    { e := plusVec 2 K 1 true
      f := plusVec 2 K 1 false
      Q_e := quadPlus_plusVec 2 K 1 true
      Q_f := quadPlus_plusVec 2 K 1 false
      polar_ef := by rw [polar_quadPlus_plusVec]; simp }
  orth :=
    { ee := by rw [polar_quadPlus_plusVec]; simp
      ef := by rw [polar_quadPlus_plusVec]; simp
      fe := by rw [polar_quadPlus_plusVec]; simp
      ff := by rw [polar_quadPlus_plusVec]; simp }

private def mapHypPair {W : Type*} [AddCommGroup W] [Module K W]
    {Q₁ : QuadraticForm K W} {Q₂ : QuadraticForm K V}
    (e : Q₁.IsometryEquiv Q₂) (P : HypPair Q₂) : HypPair Q₁ where
  e := e.symm P.e
  f := e.symm P.f
  Q_e := by
    rw [QuadraticMap.IsometryEquiv.map_app e.symm P.e, P.Q_e]
  Q_f := by
    rw [QuadraticMap.IsometryEquiv.map_app e.symm P.f, P.Q_f]
  polar_ef := by
    have h := QuadraticMap.Isometry.polar_apply e.symm.toIsometry P.e P.f
    simpa using h.trans P.polar_ef

private def mapFrame {W : Type*} [AddCommGroup W] [Module K W]
    {Q₁ : QuadraticForm K W} {Q₂ : QuadraticForm K V}
    (e : Q₁.IsometryEquiv Q₂) (H : Frame Q₂) : Frame Q₁ where
  P := mapHypPair e H.P
  P' := mapHypPair e H.P'
  orth :=
    { ee := by
        change polar Q₁ (e.symm.toIsometry H.P.e) (e.symm.toIsometry H.P'.e) = 0
        rw [QuadraticMap.Isometry.polar_apply e.symm.toIsometry H.P.e H.P'.e, H.orth.ee]
      ef := by
        change polar Q₁ (e.symm.toIsometry H.P.e) (e.symm.toIsometry H.P'.f) = 0
        rw [QuadraticMap.Isometry.polar_apply e.symm.toIsometry H.P.e H.P'.f, H.orth.ef]
      fe := by
        change polar Q₁ (e.symm.toIsometry H.P.f) (e.symm.toIsometry H.P'.e) = 0
        rw [QuadraticMap.Isometry.polar_apply e.symm.toIsometry H.P.f H.P'.e, H.orth.fe]
      ff := by
        change polar Q₁ (e.symm.toIsometry H.P.f) (e.symm.toIsometry H.P'.f) = 0
        rw [QuadraticMap.Isometry.polar_apply e.symm.toIsometry H.P.f H.P'.f, H.orth.ff] }

omit [Finite K] [FiniteDimensional K V] in
private lemma not_isPlusType_perpAll [FiniteDimensional K V]
    (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (hQ : (polarBilin Q).Nondegenerate)
    (hfull : ∀ H : Frame Q, (∀ i, SpanOrth H (A i)) → False)
    (hdim : finrank K (perpAll A) = 4) :
    ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (perpAll A).subtype) := by
  intro hp
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus
    (nondegenerate_perpAll A horth hQ) (n := 2) (by omega) hp
  exact false_of_frame_perpAll A hfull (mapFrame e frameQuadPlus)





private def frameStab (G : Subgroup (V ≃ₗ[K] V)) : Subgroup G :=
  (stabSub (perpAll A)).comap G.subtype

omit [Finite K] [FiniteDimensional K V] in
private lemma mem_frameStab {G : Subgroup (V ≃ₗ[K] V)} {g : G} :
    g ∈ frameStab A G ↔ (g : V ≃ₗ[K] V) ∈ stabSub (perpAll A) := by
  rw [frameStab, Subgroup.mem_comap]
  rfl

private noncomputable def stabMap (G : Subgroup (V ≃ₗ[K] V)) :
    frameStab A G →* stabSub (perpAll A) where
  toFun g := ⟨(g.1 : V ≃ₗ[K] V), (mem_frameStab A).mp g.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private noncomputable def restrictHom (G : Subgroup (V ≃ₗ[K] V))
    (hGO : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q) :
    frameStab A G →* TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype) :=
  ((resHom (perpAll A)).comp (stabMap A G)).codRestrict _
    fun g => resHom_mem_orthogonalGroup (hGO g.1.2) ((mem_frameStab A).mp g.2)





omit [Finite K] [FiniteDimensional K V] in
private lemma reflect_mem_restrictHom_range
    (hm : 0 < m) {G : Subgroup (V ≃ₗ[K] V)}
    (hGO : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hG : ∀ (a b : V) [Invertible (Q a)] [Invertible (Q b)], Q a * Q b = 1 →
      TauCeti.QuadraticMap.reflection Q a * TauCeti.QuadraticMap.reflection Q b ∈ G)
    {v : perpAll A} [Invertible ((Q.comp (perpAll A).subtype) v)] :
    TauCeti.QuadraticMap.reflectionOrthogonal (Q.comp (perpAll A).subtype) v ∈
      (restrictHom A G hGO).range := by
  classical
  have hvI : Invertible (Q (v : V)) := ‹Invertible ((Q.comp (perpAll A).subtype) v)›
  set c : K := ⅟(Q (v : V)) with hc
  set X : Matrix (Fin 2) (Fin 2) K := !![c, 0; 0, 1] with hX
  set a : V := (A ⟨0, hm⟩).incl X with ha
  have hQa : Q a = c := by
    rw [show Q a = X.det from Frame.Q_incl (A ⟨0, hm⟩) X, Matrix.det_fin_two]
    simp [X]
  have hQa_ne : Q a ≠ 0 := by
    rw [hQa, hc, invOf_eq_inv]
    exact inv_ne_zero (Invertible.ne_zero (Q (v : V)))
  have : Invertible (Q a) := invertibleOfNonzero hQa_ne
  have hprod : Q a * Q (v : V) = 1 := by
    rw [hQa, hc]
    exact invOf_mul_self (Q (v : V))
  set g : V ≃ₗ[K] V :=
    TauCeti.QuadraticMap.reflection Q a * TauCeti.QuadraticMap.reflection Q (v : V) with hg
  have hgG : g ∈ G := hG a (v : V) hprod
  have ha_span : a ∈ spanAll A :=
    Submodule.mem_iSup_of_mem ⟨0, hm⟩ ⟨X, ha.symm⟩
  have hfixa : ∀ x ∈ perpAll A, TauCeti.QuadraticMap.reflection Q a x = x := by
    intro x hx
    rw [TauCeti.QuadraticMap.reflection_apply,
      polar_eq_zero_of_mem_spanAll_of_mem_perpAll A ha_span hx, mul_zero, zero_smul,
      sub_zero]
  have hmapsv : ∀ x ∈ perpAll A,
      TauCeti.QuadraticMap.reflection Q (v : V) x ∈ perpAll A := by
    intro x hx
    rw [TauCeti.QuadraticMap.reflection_apply]
    exact (perpAll A).sub_mem hx ((perpAll A).smul_mem _ v.2)
  have hg_maps : ∀ x ∈ perpAll A, g x ∈ perpAll A := by
    intro x hx
    change TauCeti.QuadraticMap.reflection Q a
      (TauCeti.QuadraticMap.reflection Q (v : V) x) ∈ perpAll A
    rw [hfixa _ (hmapsv x hx)]
    exact hmapsv x hx
  have hg_inv : g⁻¹ =
      TauCeti.QuadraticMap.reflection Q (v : V) * TauCeti.QuadraticMap.reflection Q a := by
    rw [hg, mul_inv_rev]
    have h1 : (TauCeti.QuadraticMap.reflection Q (v : V))⁻¹ =
        TauCeti.QuadraticMap.reflection Q (v : V) := by
      rw [show (TauCeti.QuadraticMap.reflection Q (v : V))⁻¹ =
          (TauCeti.QuadraticMap.reflection Q (v : V)).symm from rfl,
        TauCeti.QuadraticMap.reflection_symm]
    have h2 : (TauCeti.QuadraticMap.reflection Q a)⁻¹ =
        TauCeti.QuadraticMap.reflection Q a := by
      rw [show (TauCeti.QuadraticMap.reflection Q a)⁻¹ =
          (TauCeti.QuadraticMap.reflection Q a).symm from rfl,
        TauCeti.QuadraticMap.reflection_symm]
    rw [h1, h2]
  have hg_maps_inv : ∀ x ∈ perpAll A, g⁻¹ x ∈ perpAll A := by
    intro x hx
    rw [hg_inv]
    change TauCeti.QuadraticMap.reflection Q (v : V)
      (TauCeti.QuadraticMap.reflection Q a x) ∈ perpAll A
    rw [hfixa _ hx]
    exact hmapsv x hx
  have hg_stab : g ∈ stabSub (perpAll A) := by
    refine mem_stabSub.mpr fun x => ⟨hg_maps x, ?_⟩
    intro hx
    rw [← LinearEquiv.symm_apply_apply g x]
    exact hg_maps_inv (g x) hx
  have hres : resHom (perpAll A) ⟨g, hg_stab⟩ =
      TauCeti.QuadraticMap.reflection (Q.comp (perpAll A).subtype) v := by
    refine LinearEquiv.ext fun x => Subtype.ext ?_
    rw [resHom_apply]
    have h1 : g (x : V) = TauCeti.QuadraticMap.reflection Q (v : V) (x : V) := by
      change TauCeti.QuadraticMap.reflection Q a
        (TauCeti.QuadraticMap.reflection Q (v : V) (x : V)) = _
      rw [hfixa _ (hmapsv x x.2)]
    have h2 : ((TauCeti.QuadraticMap.reflection (Q.comp (perpAll A).subtype) v x :
        perpAll A) : V) = TauCeti.QuadraticMap.reflection Q (v : V) (x : V) := by
      have : Invertible (Q (v : V)) := hvI
      rw [TauCeti.QuadraticMap.reflection_apply_eq_sub_div,
        TauCeti.QuadraticMap.reflection_apply_eq_sub_div]
      simp only [Submodule.coe_sub, Submodule.coe_smul, polar_comp_subtype_apply,
        QuadraticMap.comp_apply]
      rfl
    rw [h1, h2]
  have hM : (⟨g, hgG⟩ : G) ∈ frameStab A G := (mem_frameStab A).mpr hg_stab
  refine ⟨⟨⟨g, hgG⟩, hM⟩, ?_⟩
  refine Subtype.ext ?_
  rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  exact hres

omit [Finite K] [FiniteDimensional K V] in
private lemma restrictHom_surjective [FiniteDimensional K V]
    (hm : 0 < m) {G : Subgroup (V ≃ₗ[K] V)}
    (hGO : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hG : ∀ (a b : V) [Invertible (Q a)] [Invertible (Q b)], Q a * Q b = 1 →
      TauCeti.QuadraticMap.reflection Q a * TauCeti.QuadraticMap.reflection Q b ∈ G)
    (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0) :
    Function.Surjective (restrictHom A G hGO) := by
  have : NeZero (2 : K) := ⟨h2⟩
  intro w
  have htop : (restrictHom A G hGO).range = ⊤ := by
    refine TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem
      (Q.comp (perpAll A).subtype) ?_ _ ?_
    · exact CFSG.LieType.Universal.Spin.nondegenerate_of_nondegenerate_polarBilin
        (nondegenerate_perpAll A horth hQ)
    · intro v hv
      exact reflect_mem_restrictHom_range A hm hGO hG (v := v)
  have hw : w ∈ (restrictHom A G hGO).range := by
    rw [htop]
    exact Subgroup.mem_top w
  exact MonoidHom.mem_range.mp hw





private lemma finite_linearEquiv : Finite (V ≃ₗ[K] V) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype V := Fintype.ofInjective (Module.finBasis K V).equivFun.toLinearMap
    (Module.finBasis K V).equivFun.injective
  exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective

omit [Finite K] [FiniteDimensional K V] in
private lemma sylow_le_frameStab (h2 : (2 : K) ≠ 0) {G : Subgroup (V ≃ₗ[K] V)}
    (T : Sylow 2 G)
    (hTA : ∀ t ∈ (T : Subgroup G), ∀ i, ∃ k,
      (t : V ≃ₗ[K] V) * (A i).La (-1) * (t : V ≃ₗ[K] V)⁻¹ = (A k).La (-1)) :
    (T : Subgroup G) ≤ frameStab A G :=
  fun _ ht => (mem_frameStab A).mpr (maps_perpAll_of_mem_sylow A h2 T hTA ht)

omit [Finite K] [FiniteDimensional K V] in
private lemma mem_frameStab_of_fixes (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    {G : Subgroup (V ≃ₗ[K] V)} (hGO : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    {h : G} (hspan : ∀ i, ∀ x ∈ (A i).span, (h : V ≃ₗ[K] V) x = x) :
    h ∈ frameStab A G :=
  (mem_frameStab A).mpr (maps_perpAll_of_fixes_spanAll A horth (hGO h.2) hspan)

omit [Finite K] [FiniteDimensional K V] in
private lemma restrictHom_pow_eq_one {G : Subgroup (V ≃ₗ[K] V)}
    (hGO : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {h : G} {p j : ℕ}
    (hhM : h ∈ frameStab A G) (hhp : h ^ p ^ j = 1) :
    restrictHom A G hGO ⟨h, hhM⟩ ^ p ^ j = 1 := by
  have h1 : (⟨h, hhM⟩ : frameStab A G) ^ p ^ j = 1 := by
    apply Subtype.ext
    simpa using hhp
  rw [← map_pow, h1, map_one]

omit [Finite K] [FiniteDimensional K V] in
private lemma restrictHom_mem_normalizer {G : Subgroup (V ≃ₗ[K] V)}
    [Finite (frameStab A G)] (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ frameStab A G)
    (hGO : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hsurj : Function.Surjective (restrictHom A G hGO))
    {h : G} (hhM : h ∈ frameStab A G)
    (hhN : h ∈ normalizer ((T : Subgroup G) : Set G)) :
    restrictHom A G hGO ⟨h, hhM⟩ ∈
      normalizer (((T.subtype hTM).mapSurjective (f := restrictHom A G hGO) hsurj :
        Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype))) :
        Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype))) := by
  let TM : Sylow 2 (frameStab A G) := T.subtype hTM
  let f : frameStab A G →*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype) :=
    restrictHom A G hGO
  have hnorm : (⟨h, hhM⟩ : frameStab A G) ∈ normalizer (TM : Set (frameStab A G)) := by
    change (⟨h, hhM⟩ : frameStab A G) ∈
      normalizer ((TM : Subgroup (frameStab A G)) : Set (frameStab A G))
    rw [Subgroup.mem_normalizer_iff]
    intro m
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hhN (m : G)
  have hmem : f ⟨h, hhM⟩ ∈ map f (normalizer (TM : Set (frameStab A G))) :=
    Subgroup.mem_map_of_mem f hnorm
  have hle : f ⟨h, hhM⟩ ∈
      normalizer ((map f (TM : Subgroup (frameStab A G)) : Subgroup _) : Set _) :=
    Subgroup.le_normalizer_map f hmem
  have hcoe : (TM : Subgroup (frameStab A G)) = (T.subtype hTM : Subgroup (frameStab A G)) :=
    rfl
  rw [hcoe] at hle
  rw [hcoe] at hle
  change (restrictHom A G hGO) ⟨h, hhM⟩ ∈ normalizer
    ((((T.subtype hTM).mapSurjective (f := f) hsurj :
        Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype))) :
        Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype))) :
        Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype)))
  rw [show (((T.subtype hTM).mapSurjective (f := f) hsurj :
      Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype))) :
      Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype))) =
      map f (T.subtype hTM : Subgroup (frameStab A G))
      from Sylow.coe_mapSurjective hsurj (T.subtype hTM)]
  exact hle

theorem eq_one_of_frames_of_mem_normalizer {K V : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {m : ℕ} (hm : 0 < m)
    (A : Fin m → Frame Q) (horth : ∀ i j, i ≠ j → SpanOrth (A i) (A j))
    (hfull : ∀ H : Frame Q, (∀ i, SpanOrth H (A i)) → False)
    (G : Subgroup (V ≃ₗ[K] V)) (hGO : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hG : ∀ (a b : V) [Invertible (Q a)] [Invertible (Q b)], Q a * Q b = 1 →
      TauCeti.QuadraticMap.reflection Q a * TauCeti.QuadraticMap.reflection Q b ∈ G)
    (T : Sylow 2 G)
    (hTA : ∀ t ∈ (T : Subgroup G), ∀ i, ∃ k,
      (t : V ≃ₗ[K] V) * (A i).La (-1) * (t : V ≃ₗ[K] V)⁻¹ = (A k).La (-1))
    {h : G} {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hhp : h ^ p ^ j = 1)
    (hhN : h ∈ normalizer ((T : Subgroup G) : Set G))
    (hspan : ∀ i, ∀ x ∈ (A i).span, (h : V ≃ₗ[K] V) x = x) :
    h = 1 := by
  classical
  have h2 : (2 : K) ≠ 0 :=
    CFSG.ClassicalInvolution.Models.OrthogonalPairs.IsFundamental.two_ne_zero_of_odd hodd
  have : Finite (V ≃ₗ[K] V) := finite_linearEquiv (K := K) (V := V)
  have : Finite G := Subtype.finite
  have : Finite (frameStab A G) := Subtype.finite
  have hhM : h ∈ frameStab A G := mem_frameStab_of_fixes A horth hGO hspan
  have hTM : (T : Subgroup G) ≤ frameStab A G := sylow_le_frameStab A h2 T hTA
  have hsurj : Function.Surjective (restrictHom A G hGO) :=
    restrictHom_surjective A hm hGO hG horth hQ h2
  let f : frameStab A G →*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype) :=
    restrictHom A G hGO
  let TO : Sylow 2 (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype)) :=
    (T.subtype hTM).mapSurjective (f := f) hsurj
  have hpow : f ⟨h, hhM⟩ ^ p ^ j = 1 := restrictHom_pow_eq_one A hGO hhM hhp
  have hN : f ⟨h, hhM⟩ ∈ normalizer (TO : Set
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpAll A).subtype))) :=
    restrictHom_mem_normalizer A T hTM hGO hsurj hhM hhN
  have hg1 : f ⟨h, hhM⟩ = 1 :=
    eq_one_of_mem_normalizer_sylow_small hodd (nondegenerate_perpAll A horth hQ)
      (finrank_perpAll_le_four A horth h2 hQ hfull)
      (fun hdim => not_isPlusType_perpAll A horth hQ hfull hdim) TO hp hp5 hpow hN
  have hfixW : ∀ x : perpAll A, (h : V ≃ₗ[K] V) (x : V) = (x : V) := by
    intro x
    have hx1 : ((restrictHom A G hGO ⟨h, hhM⟩ : TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (perpAll A).subtype)) : perpAll A ≃ₗ[K] perpAll A) x = x := by
      rw [show (restrictHom A G hGO ⟨h, hhM⟩ : TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (perpAll A).subtype)) = f ⟨h, hhM⟩ from rfl, hg1]
      simp
    have hx2 := congrArg Subtype.val hx1
    change (↑(resHom (perpAll A) ⟨(h : V ≃ₗ[K] V), (mem_frameStab A).mp hhM⟩ x) : V) =
      (x : V) at hx2
    rw [resHom_apply] at hx2
    simpa using hx2
  have hfixS : ∀ s ∈ spanAll A, (h : V ≃ₗ[K] V) s = s := fixes_spanAll A hspan
  refine Subtype.ext ?_
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨s, w, rfl⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_add_of_isCompl
    (isCompl_spanAll_perpAll A horth) v
  rw [map_add, hfixS s s.2, hfixW w]
  simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
