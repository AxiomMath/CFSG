module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmLift
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.LieType.SeitzGeneration.OrthEvenSingular

public section

namespace CFSG.StandardType

namespace RootPlaneOm

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal LayerCores LayerCores.OrthSplit
  LayerFacts OmNonsplit CFSG.Assembly
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup mem_omegaGroup commSpace
  natCast_finrank_commSpace_mul finrank_commSpace_reflection exists_mem_orthogonalGroup_apply_eq)
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] [CharP K 2] in
theorem finrank_le_finrank_inf_ker_add_one (W : Submodule K V) (φ : V →ₗ[K] K) :
    finrank K W ≤ finrank K ↥(W ⊓ LinearMap.ker φ) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker φ)
  have h2 := LinearMap.finrank_range_add_finrank_ker φ
  have h3 : finrank K (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    rwa [Module.finrank_self] at this
  have h4 := Submodule.finrank_le (W ⊔ LinearMap.ker φ)
  omega

theorem exists_singular_pair (hQ : (polarBilin Q).Nondegenerate) {W : Submodule K V}
    (h5 : 5 ≤ finrank K W) :
    ∃ w₁ ∈ W, ∃ w₂ ∈ W, Q w₁ = 0 ∧ Q w₂ = 0 ∧ polar Q w₁ w₂ = 0 ∧
      LinearIndependent K ![w₁, w₂] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨e, heW, he0, hQe⟩ :=
    CFSG.LieType.SeitzGeneration.OrthBlk.exists_singular_of_three_le_charTwo (Q := Q) h2
      (S := W) (by omega)
  obtain ⟨f, hf⟩ : ∃ f, polar Q e f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he0 (eq_zero_of_polar_eq_zero hQ hcon)
  have hS3 : 3 ≤ finrank K ↥((W ⊓ LinearMap.ker (polarBilin Q e)) ⊓
      LinearMap.ker (polarBilin Q f)) := by
    have := finrank_le_finrank_inf_ker_add_one W (polarBilin Q e)
    have := finrank_le_finrank_inf_ker_add_one (W ⊓ LinearMap.ker (polarBilin Q e))
      (polarBilin Q f)
    omega
  obtain ⟨e', he'S, he'0, hQe'⟩ :=
    CFSG.LieType.SeitzGeneration.OrthBlk.exists_singular_of_three_le_charTwo (Q := Q) h2 hS3
  obtain ⟨⟨he'W, he'e⟩, he'f⟩ := Submodule.mem_inf.mp he'S |>.imp_left Submodule.mem_inf.mp
  have hee' : polar Q e e' = 0 := by
    rw [LinearMap.mem_ker, polarBilin_apply_apply] at he'e
    exact he'e
  have hfe' : polar Q f e' = 0 := by
    rw [LinearMap.mem_ker, polarBilin_apply_apply] at he'f
    exact he'f
  refine ⟨e, heW, e', he'W, hQe, hQe', hee', ?_⟩
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun v => polar Q v f) hst
  simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_zero_left] at h1
  rw [QuadraticMap.polar_comm Q e' f, hfe', mul_zero, add_zero] at h1
  have hs : s = 0 := (mul_eq_zero.mp h1).resolve_right hf
  subst hs
  rw [zero_smul, zero_add] at hst
  exact ⟨rfl, (smul_eq_zero.mp hst).resolve_right he'0⟩

theorem exists_conj_pair (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {U : Type*} [Group U]
    (σ : U →* (V ≃ₗ[K] V))
    (hrange : σ.range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {e₁ e₂ w₁ w₂ v : V} (he₁ : Q e₁ = 0) (he₂ : Q e₂ = 0) (he : polar Q e₁ e₂ = 0)
    (hei : LinearIndependent K ![e₁, e₂]) (hw₁ : Q w₁ = 0) (hw₂ : Q w₂ = 0)
    (hw : polar Q w₁ w₂ = 0) (hwi : LinearIndependent K ![w₁, w₂]) (hv : Q v ≠ 0)
    (hv₁ : polar Q v e₁ = 0) (hv₂ : polar Q v e₂ = 0) :
    ∃ u : U, σ u e₁ = w₁ ∧ σ u e₂ = w₂ := by
  have hQ' : Q.polarBilin.Nondegenerate := hQ
  obtain ⟨g, hgO, hg⟩ := exists_mem_orthogonalGroup_apply_eq hQ' (k := 2) ![e₁, e₂] ![w₁, w₂]
    hei hwi (fun i => by fin_cases i <;> simp [he₁, he₂, hw₁, hw₂])
    (fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [he₁, he₂, hw₁, hw₂, he, hw, QuadraticMap.polar_comm Q w₂ w₁,
          QuadraticMap.polar_comm Q e₂ e₁])
  have hg₁ : g e₁ = w₁ := hg 0
  have hg₂ : g e₂ = w₂ := hg 1
  have hΩ : omegaGroup Q hQ' = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ' hT)
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ')
  let _ : Invertible (Q v) := invertibleOfNonzero hv
  set rv := TauCeti.QuadraticMap.reflection Q v with hrv
  have hrvO : rv ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v
  have hrv_fix : ∀ x, polar Q v x = 0 → rv x = x := fun x hx => by
    rw [hrv, TauCeti.QuadraticMap.reflection_apply, hx, mul_zero, zero_smul, sub_zero]
  by_cases hgΩ : g ∈ omegaGroup Q hQ'
  · rw [hΩ, ← hrange] at hgΩ
    obtain ⟨u, hu⟩ := hgΩ
    exact ⟨u, by rw [hu, hg₁], by rw [hu, hg₂]⟩
  · have hgr : g * rv ∈ omegaGroup Q hQ' := by
      rw [mem_omegaGroup] at hgΩ ⊢
      refine ⟨mul_mem hgO hrvO, ?_⟩
      have hodd : ¬ Even (finrank K (commSpace g)) := fun h => hgΩ ⟨hgO, h⟩
      have hmul := natCast_finrank_commSpace_mul hQ' hgO hrvO
      rw [finrank_commSpace_reflection hQ' v, Nat.cast_one] at hmul
      rw [← ZMod.natCast_eq_zero_iff_even, hmul, ← Nat.cast_one, ← Nat.cast_add,
        ZMod.natCast_eq_zero_iff_even, Nat.even_add_one]
      exact hodd
    rw [hΩ, ← hrange] at hgr
    obtain ⟨u, hu⟩ := hgr
    refine ⟨u, ?_, ?_⟩
    · rw [hu, LinearEquiv.mul_apply, hrv_fix e₁ hv₁, hg₁]
    · rw [hu, LinearEquiv.mul_apply, hrv_fix e₂ hv₂, hg₂]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem eichler_commute_of_fix {h : V ≃ₗ[K] V} (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {u w : V} (hu : h u = u) (hw : h w = w) : h * eichler Q u w = eichler Q u w * h := by
  have h1 := eichler_conj (Q := Q) hh u w
  rw [hu, hw] at h1
  calc h * eichler Q u w = h * eichler Q u w * h⁻¹ * h := by group
    _ = eichler Q u w * h := by rw [h1]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem eichler_ne_one (hQ : (polarBilin Q).Nondegenerate) {u w : V} (hu : Q u = 0)
    (huw : polar Q u w = 0) (hi : LinearIndependent K ![w, u]) (hw : Q w = 0) :
    eichler Q u w ≠ 1 := by
  intro h1
  have hu0 : u ≠ 0 := by
    have := hi.ne_zero 1
    simpa using this
  apply hu0
  refine eq_zero_of_polar_eq_zero hQ fun x => ?_
  have h2 := LinearEquiv.congr_fun h1 x
  rw [eichler_apply hu huw, hw, zero_mul, add_zero, LinearEquiv.coe_one, id_eq] at h2
  have h3 : polar Q x u • w + (-polar Q x w) • u = 0 := by
    rw [neg_smul, ← sub_eq_add_neg]
    rw [add_sub_assoc] at h2
    exact add_eq_left.mp h2
  have h4 := (LinearIndependent.pair_iff.mp hi) _ _ h3
  rw [QuadraticMap.polar_comm]
  exact h4.1

section Component

theorem exists_component_fixPart (hQ : (polarBilin Q).Nondegenerate) {U : Type} [Group U]
    {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hrange : σ.range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {G : Type} [Group G] {ψ : U →* G} (hψ : Function.Injective ψ) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {y : U} (hy : y ^ p = 1) {W₀ : Submodule K V} (hW₀ : 5 ≤ finrank K W₀)
    (hW₀y : ∀ v ∈ W₀, σ y v = v) :
    ∃ L₁ : Subgroup G, IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {ψ y}) ∧
      ∀ z : U, z * y = y * z → ψ z ∈ Subgroup.centralizer (L₁ : Set G) →
        ∀ v, σ y v = v → σ z v = v := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hσO : ∀ u, σ u ∈ O := fun u =>
    Subgroup.commutator_le_self O (hrange ▸ (⟨u, rfl⟩ : σ u ∈ σ.range))
  set a := σ y with ha
  have : Fintype (Subgroup.zpowers a) := Fintype.ofFinite _
  have hap : a ^ p = 1 := by rw [ha, ← map_pow, hy, map_one]
  have hA : (Fintype.card (Subgroup.zpowers a) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
    exact natCast_card_ne_zero_of_odd
      (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hap))
  have hAO : Subgroup.zpowers a ≤ O := Subgroup.zpowers_le.mpr (hσO y)
  have hfixW : ∀ v, σ y v = v → v ∈ fixSp (Subgroup.zpowers a) := fun v hv =>
    (mem_fixSp_iff hA).mpr fun g hg => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact zpow_apply_eq_self hv k
  have hR₀ := nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hA hAO)
  have h6 : 6 ≤ finrank K (fixSp (Subgroup.zpowers a)) := by
    have h5 : 5 ≤ finrank K (fixSp (Subgroup.zpowers a)) :=
      hW₀.trans (Submodule.finrank_mono fun v hv => hfixW v (hW₀y v hv))
    obtain ⟨k, hk⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo _ hR₀
    omega
  set O₀ := TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSp (Subgroup.zpowers a)))
    with hO₀
  obtain ⟨hq₀, -⟩ := LayerPDiv.isQuasisimple_commutator_of_not_split hR₀ (by omega)
    (fun h => by omega)
  set L := (⁅O₀, O₀⁆).map (extFix hA) with hL
  have hLC : L ≤ Subgroup.centralizer (Subgroup.zpowers a : Set (V ≃ₗ[K] V)) ⊓ O :=
    (Subgroup.map_mono (ggCommutator_self_le O₀)).trans (fixPart_le hA hAO)
  have hLq : CFSG.IsQuasisimple L := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((⁅O₀, O₀⁆).equivMapOfInjective _ (extFix_injective hA)) hq₀
  have hLO : L ≤ ⁅O, O⁆ := by
    rw [← ggCommutator_eq_of_isQuasisimple hLq]
    exact Subgroup.commutator_mono (hLC.trans inf_le_right) (hLC.trans inf_le_right)
  have hLr : L ≤ σ.range := hrange ▸ hLO
  have hLn : ∀ c ∈ Subgroup.centralizer (Subgroup.zpowers a : Set (V ≃ₗ[K] V)) ⊓ O,
      ∀ g ∈ L, c * g * c⁻¹ ∈ L := fun c hc g hg =>
    conj_mem_map_extFix hA hAO (fun _ hu _ hs => LayerPDiv.conj_mem_commutator_self O₀ hu hs) hc hg
  have hcen : ∀ u : U, u * y = y * u →
      σ u ∈ Subgroup.centralizer (Subgroup.zpowers a : Set (V ≃ₗ[K] V)) ⊓ O := by
    intro u hu
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun g hg => ?_, hσO u⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have h1 : Commute a (σ u) := by
      change σ y * σ u = σ u * σ y
      rw [← map_mul, ← map_mul, hu]
    exact (h1.zpow_left k).eq
  have hCeq : ψ.range ⊓ Subgroup.centralizer {ψ y} = (Subgroup.centralizer {y}).map ψ := by
    ext g
    constructor
    · rintro ⟨⟨u, rfl⟩, hu⟩
      refine ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr (hψ ?_), rfl⟩
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hu
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hu]
  have hLy : L.comap σ ≤ Subgroup.centralizer {y} := by
    intro l hl
    refine Subgroup.mem_centralizer_singleton_iff.mpr (hσ ?_)
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp (hLC hl).1 a (Subgroup.mem_zpowers a)).symm
  let e : ↥((L.comap σ).map ψ) ≃* ↥L :=
    ((L.comap σ).equivMapOfInjective ψ hψ).symm.trans
      (((L.comap σ).equivMapOfInjective _ hσ).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hLr)))
  refine ⟨(L.comap σ).map ψ, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hCeq]
    exact Subgroup.map_mono hLy
  · rw [hCeq]
    refine ggSubnormal_map ψ (ggSubnormal_of_normal hLy fun u hu s hs => ?_)
    have h1 := hLn (σ u) (hcen u (Subgroup.mem_centralizer_singleton_iff.mp hu)) (σ s) hs
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact h1
  · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLq)
  · intro z hzy hzL v hv
    obtain ⟨⟨g₀, g₁⟩, hg, hgz⟩ : σ z ∈ ((O₀.prod (freeCent (Subgroup.zpowers a) Q)).map
        (split hA)) := by
      rw [← centralizer_eq_map_split hA hAO]
      exact hcen z hzy
    obtain ⟨hg₀O, -⟩ := Subgroup.mem_prod.mp hg
    have hg₀c : ∀ m ∈ ⁅O₀, O₀⁆, g₀ * m = m * g₀ := by
      intro m hm
      obtain ⟨l, hl⟩ := hLr (⟨m, hm, rfl⟩ : extFix hA m ∈ L)
      have hlL : l ∈ L.comap σ := by
        rw [Subgroup.mem_comap, hl]
        exact ⟨m, hm, rfl⟩
      have h1 : ψ l * ψ z = ψ z * ψ l :=
        Subgroup.mem_centralizer_iff.mp hzL _ ⟨l, hlL, rfl⟩
      have hzl : z * l = l * z := hψ (by rw [map_mul, map_mul]; exact h1.symm)
      have h2 : σ z * σ l = σ l * σ z := by
        rw [← map_mul, ← map_mul, hzl]
      rw [hl, ← hgz] at h2
      have h3 : split hA (g₀ * m, g₁ * 1) = split hA (m * g₀, 1 * g₁) := by
        rw [← Prod.mk_mul_mk, ← Prod.mk_mul_mk, map_mul, map_mul]
        exact h2
      exact congrArg Prod.fst (split_injective hA h3)
    have hg₀1 : g₀ = 1 := OrthRegular.eq_one_of_commute_orthDerived hR₀ (by omega)
      (fun h => by rcases h with ⟨h, -⟩ | ⟨⟨h, -⟩, -⟩ <;> omega) hg₀O hg₀c
    rw [← hgz, hg₀1]
    have h1 := split_apply_fix hA ((1 : fixSp (Subgroup.zpowers a) ≃ₗ[K]
      fixSp (Subgroup.zpowers a)), g₁) ⟨v, hfixW v hv⟩
    exact h1

end Component

end RootPlaneOm

end CFSG.StandardType
