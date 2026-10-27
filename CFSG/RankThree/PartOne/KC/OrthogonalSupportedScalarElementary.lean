module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarCentralizer
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

section Group

theorem eq_of_index_two_of_hom {G A : Type*} [Group G] [Group A] (N : Subgroup G)
    (hN : N.index = 2) (D : G →* A) (hND : ∀ n ∈ N, D n = 1) {g r : G} (hg : g ∉ N)
    (hr : r ∉ N) : D g = D r := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hN
  have h1 : g * a ∈ N := by
    rcases ha g with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hg
  have h2 : r * a ∈ N := by
    rcases ha r with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hr
  have h3 : g * r⁻¹ ∈ N := by
    have := N.mul_mem h1 (N.inv_mem h2)
    simpa [mul_assoc] using this
  have h4 := hND _ h3
  rw [map_mul, map_inv, mul_inv_eq_one] at h4
  exact h4

end Group

section Field

variable {K : Type*} [Field K] [Finite K]

omit [Finite K] in
theorem exists_ne_zero_ne_one_of_two_lt (h : 2 < Nat.card K) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective (fun t : Bool => if t then (1 : K) else 0) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨false, by simp [hx]⟩
    · exact ⟨true, by simp [hcon x hx]⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem eq_one_of_ne_zero_of_card_eq_two (h : Nat.card K = 2) {x : K} (hx : x ≠ 0) : x = 1 := by
  classical
  by_contra hx1
  have : Fintype K := Fintype.ofFinite K
  have hc : ({0, 1, x} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hx1)]
    simp [hx.symm]
  have h3 := Finset.card_le_univ ({0, 1, x} : Finset K)
  rw [Nat.card_eq_fintype_card] at h
  omega

theorem two_eq_zero_of_card_eq_two (h : Nat.card K = 2) : (2 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have h1 := Nat.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, h] at h1
  exact_mod_cast h1

end Field

section Dickson

variable {K : Type*} [Field K] {X : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  {R : QuadraticForm K X}

theorem dicksonHom_reflect (hR : (polarBilin R).Nondegenerate) {v : X} (hv : R v ≠ 0) :
    dicksonHom R hR ⟨reflect R v, reflect_mem_orthogonalGroup R v⟩ =
      Multiplicative.ofAdd (1 : ZMod 2) := by
  let _ : Invertible (R v) := invertibleOfNonzero hv
  have h1 : finrank K (commSpace (reflect R v)) = 1 := by
    rw [reflect_eq_reflection]
    exact finrank_commSpace_reflection hR v
  rw [dicksonHom_apply]
  change Multiplicative.ofAdd ((finrank K (commSpace (reflect R v)) : ℕ) : ZMod 2) = _
  rw [h1, Nat.cast_one]

theorem dicksonHom_apply_orthDerived_eq_one (hR : (polarBilin R).Nondegenerate)
    {g : X ≃ₗ[K] X} (hg : g ∈ orthDerived R) :
    dicksonHom R hR ⟨g, orthDerived_le_orthogonalGroup_of_commutator R hg⟩ = 1 := by
  have hg' : (⟨g, orthDerived_le_orthogonalGroup_of_commutator R hg⟩ :
      ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ∈
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    have hg2 := hg
    rw [orthDerived, ← Subgroup.map_subtype_commutator] at hg2
    obtain ⟨g', hg', hgg'⟩ := hg2
    have : g' = ⟨g, orthDerived_le_orthogonalGroup_of_commutator R hg⟩ := Subtype.ext hgg'
    rwa [← this]
  exact Abelianization.commutator_subset_ker _ hg'

theorem mem_orthDerived_of_dicksonHom_eq_one (hR : (polarBilin R).Nondegenerate) [Nontrivial X]
    (hidx : ((orthDerived R).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup R)).index = 2)
    {g : ↥(TauCeti.QuadraticMap.orthogonalGroup R)} (hg : dicksonHom R hR g = 1) :
    (g : X ≃ₗ[K] X) ∈ orthDerived R := by
  by_contra hgN
  obtain ⟨v, hv⟩ := exists_map_ne_zero hR
  have hD1 : dicksonHom R hR ⟨reflect R v, reflect_mem_orthogonalGroup R v⟩ ≠ 1 := by
    rw [dicksonHom_reflect hR hv, Ne, ofAdd_eq_one]
    decide
  have hrN : (⟨reflect R v, reflect_mem_orthogonalGroup R v⟩ :
      ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ∉
      (orthDerived R).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup R) := by
    intro h
    exact hD1 (dicksonHom_apply_orthDerived_eq_one hR (Subgroup.mem_subgroupOf.mp h))
  have h := eq_of_index_two_of_hom _ hidx (dicksonHom R hR)
    (fun n hn => dicksonHom_apply_orthDerived_eq_one hR (Subgroup.mem_subgroupOf.mp hn))
    (g := g) (fun h => hgN (Subgroup.mem_subgroupOf.mp h)) hrN
  exact hD1 (h.symm.trans hg)

end Dickson

section Main

variable {K : Type} [Field K] [Finite K] {X : Type*} [AddCommGroup X] [Module K X]
  [FiniteDimensional K X] {R : QuadraticForm K X}

omit [Finite K] in
theorem exists_map_ne_zero_of_perp (hR : (polarBilin R).Nondegenerate) (hdim : finrank K X = 6)
    (hno : ¬ ∃ T : Submodule K X, finrank K T = 3 ∧ ∀ x ∈ T, R x = 0) (P : HypPair R) {w : X}
    (hw : w ∈ P.perp) (hw0 : w ≠ 0) : ∃ v ∈ P.perp, polar R w v = 0 ∧ R v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let φ : ↥P.perp →ₗ[K] K := (polarBilin R w).comp P.perp.subtype
  have hφ : φ ≠ 0 := by
    intro h0
    obtain ⟨y, hyP, hy⟩ := (P.polarNondegOn_perp hR).exists_polar_ne_zero hw hw0
    have h1 := LinearMap.congr_fun h0 ⟨y, hyP⟩
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, polarBilin_apply_apply,
      LinearMap.zero_apply] at h1
    exact hy h1
  have hperp4 : finrank K P.perp = 4 := by
    have h := finrank_inf_perp_add_two P (S := ⊤) trivial trivial
    rw [top_inf_eq, finrank_top, hdim] at h
    omega
  have hrange : finrank K (LinearMap.range φ) = 1 := by
    have h1 : finrank K (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ)
      rwa [finrank_self] at this
    have h2 : finrank K (LinearMap.range φ) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
      exact hφ
    omega
  have hker : finrank K (LinearMap.ker φ) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker φ
    omega
  apply hno
  refine ⟨(LinearMap.ker φ).map P.perp.subtype, ?_, ?_⟩
  · rw [Submodule.finrank_map_subtype_eq, hker]
  · rintro _ ⟨y, hy, rfl⟩
    refine hcon y y.2 ?_
    simpa [φ, polarBilin_apply_apply] using hy

theorem eichler_mem_orthDerived_of_regular (hR : (polarBilin R).Nondegenerate)
    (hdim : 3 ≤ finrank K X)
    (h4 : Nat.card K = 2 → finrank K X = 4 →
      ∀ U : Submodule K X, finrank K U = 2 → ∃ u ∈ U, R u ≠ 0)
    (P : HypPair R) {w : X} (hw : w ∈ P.perp) : eichler R P.e w ∈ orthDerived R := by
  by_cases hT : ∃ T : Submodule K X, finrank K T = 3 ∧ ∀ x ∈ T, R x = 0
  · rw [(CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hR hT).1]
    exact eichler_mem_elementaryGroup R P.e w
  by_cases hq : 2 < Nat.card K
  · obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one_of_two_lt hq
    exact CFSG.RankThree.Classical.eichler_mem_commutator_orthogonalGroup hc0 hc1 P hw
  have hcard : Nat.card K = 2 := by
    have := Finite.one_lt_card (α := K)
    omega
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_eq_two hcard
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨⟨n0, hn0⟩, -, -, -, -, hn4⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms R hR
  have hn3 : n0 ≤ 3 := by
    by_contra h
    obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ := hn4 n0 hn0 (by omega)
    exact hT (exists_totallySingular_of_hypPairs h12 h13 h23)
  have hd : finrank K X = 4 ∨ finrank K X = 6 := by omega
  have hts : ∀ U : Submodule K X, finrank K U = finrank K X / 2 → ∃ u ∈ U, R u ≠ 0 := by
    intro U hU
    rcases hd with h4' | h6'
    · exact h4 hcard h4' U (by rw [hU, h4'])
    · by_contra hcon
      push Not at hcon
      exact hT ⟨U, by rw [hU, h6'], hcon⟩
  obtain ⟨-, -, -, hidx, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction R hR hd hts
  have : Nontrivial X := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hnz : ∀ v ∈ P.perp, R v ≠ 0 → eichler R P.e v ∈ orthDerived R := by
    intro v hv hRv
    have hRv1 : R v = 1 := eq_one_of_ne_zero_of_card_eq_two hcard hRv
    have hev : polar R P.e v = 0 := (HypPair.mem_perp.mp hv).1
    have hve : polar R v P.e = 0 := by rw [polar_comm, hev]
    have hRve : R (v + P.e) = 1 := by
      rw [QuadraticMap.map_add R v P.e, hRv1, P.Q_e, hve]
      ring
    have hmem : reflect R v * reflect R (v + P.e) ∈ TauCeti.QuadraticMap.orthogonalGroup R :=
      mul_mem (reflect_mem_orthogonalGroup R v) (reflect_mem_orthogonalGroup R _)
    rw [eichler_eq_reflect_mul_reflect h2 P.Q_e hev hRv1]
    refine mem_orthDerived_of_dicksonHom_eq_one hR hidx
      (g := ⟨reflect R v * reflect R (v + P.e), hmem⟩) ?_
    have hmul : (⟨reflect R v * reflect R (v + P.e), hmem⟩ :
        ↥(TauCeti.QuadraticMap.orthogonalGroup R)) =
        ⟨reflect R v, reflect_mem_orthogonalGroup R v⟩ *
          ⟨reflect R (v + P.e), reflect_mem_orthogonalGroup R _⟩ := rfl
    rw [hmul, map_mul, dicksonHom_reflect hR hRv,
      dicksonHom_reflect hR (by rw [hRve]; exact one_ne_zero), ← ofAdd_add, ← ofAdd_zero]
    congr 1
  by_cases hRw : R w ≠ 0
  · exact hnz w hw hRw
  push Not at hRw
  by_cases hw0 : w = 0
  · rw [hw0, eichler_zero_right]
    exact one_mem _
  have hev : polar R P.e w = 0 := (HypPair.mem_perp.mp hw).1
  rcases hd with h4' | h6'
  · exfalso
    have hli : LinearIndependent K ![P.e, w] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      have h1 := congrArg (fun t => polar R t P.f) hab
      simp only [polar_add_left, polar_smul_left_eq, P.polar_ef, polar_zero_left] at h1
      have hwf : polar R w P.f = 0 := by rw [polar_comm]; exact (HypPair.mem_perp.mp hw).2
      rw [hwf] at h1
      have ha : a = 0 := by linear_combination h1
      rw [ha, zero_smul, zero_add] at hab
      exact ⟨ha, (smul_eq_zero.mp hab).resolve_right hw0⟩
    have hspan : finrank K (Submodule.span K (Set.range ![P.e, w])) = 2 := by
      rw [finrank_span_eq_card hli]
      simp
    obtain ⟨u, hu, hRu⟩ := hts _ (by rw [hspan, h4'])
    refine hRu (map_eq_zero_of_mem_span (S := Set.range ![P.e, w]) ?_ ?_ hu)
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact P.Q_e
      · exact hRw
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      fin_cases i <;> fin_cases j
      · exact P.polar_ee
      · exact hev
      · rw [polar_comm]; exact hev
      · exact polar_self_eq_zero hRw
  · obtain ⟨v, hvP, hwv, hRv⟩ := exists_map_ne_zero_of_perp hR h6' hT P hw hw0
    have hvw : v + w ∈ P.perp := P.perp.add_mem hvP hw
    have hRvw : R (v + w) ≠ 0 := by
      have hvw' : polar R v w = 0 := by rw [polar_comm, hwv]
      rw [QuadraticMap.map_add R v w, hRw, hvw', add_zero, add_zero]
      exact hRv
    have hprod : eichler R P.e w = eichler R P.e v * eichler R P.e (v + w) := by
      rw [eichler_mul (HypPair.mem_perp.mp hvP).1 (HypPair.mem_perp.mp hvw).1]
      congr 1
      rw [← add_assoc, ← two_smul K v, h2, zero_smul, zero_add]
    rw [hprod]
    exact mul_mem (hnz v hvP hRv) (hnz (v + w) hvw hRvw)

end Main

section Ambient

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {W : Submodule K V}

theorem elementaryMapsMem_of_regular (hWnd : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hW3 : 3 ≤ finrank K W)
    (h4 : Nat.card K = 2 → finrank K W = 4 →
      ∀ U : Submodule K W, finrank K U = 2 → ∃ u ∈ U, (Q.comp W.subtype) u ≠ 0) :
    ElementaryMapsMem Q W := by
  intro P he hf w hw
  let P' : HypPair (Q.comp W.subtype) :=
    ⟨⟨P.e, he⟩, ⟨P.f, hf⟩, P.Q_e, P.Q_f, by rw [polar_comp_subtype_eq]; exact P.polar_ef⟩
  have hw' : (⟨w, hw.1⟩ : W) ∈ P'.perp := by
    rw [HypPair.mem_perp, polar_comp_subtype_eq, polar_comp_subtype_eq]
    exact HypPair.mem_perp.mp hw.2
  exact eichler_mem_supportedDerived he hw.1 P.Q_e (HypPair.mem_perp.mp hw.2).1
    (eichler_mem_orthDerived_of_regular hWnd hW3 h4 P' hw')

end Ambient

end CFSG.RankThree.PartOne.KCOrthogonal
