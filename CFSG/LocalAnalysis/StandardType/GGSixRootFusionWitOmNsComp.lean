module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmCent
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmegaRegular
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageCases
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOBlock
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction

public section

namespace CFSG.StandardType

namespace WitOmNs

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal LayerCores LayerCores.OrthSplit
  OmNonsplit

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_fixComponent (hQ : (polarBilin Q).Nondegenerate) {d : V ≃ₗ[K] V}
    (hdO : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdp : d ^ p = 1) (h6 : 6 ≤ finrank K (LinearMap.ker ((d : V →ₗ[K] V) - LinearMap.id))) :
    ∃ Lp : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple Lp ∧
      Lp ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      (∀ g ∈ Lp, g * d = d * g) ∧
      (∀ c ∈ TauCeti.QuadraticMap.orthogonalGroup Q, c * d = d * c → ∀ g ∈ Lp,
        c * g * c⁻¹ ∈ Lp) ∧
      ∀ z ∈ TauCeti.QuadraticMap.orthogonalGroup Q, z * d = d * z →
        (∀ g ∈ Lp, z * g = g * z) → ∀ v, d v = v → z v = v := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Fintype (Subgroup.zpowers d) := Fintype.ofFinite _
  have hB : (Fintype.card (Subgroup.zpowers d) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
    exact natCast_card_ne_zero_of_odd
      (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hdp))
  have hBO : Subgroup.zpowers d ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.zpowers_le.mpr hdO
  have hfix : ∀ v, v ∈ fixSp (Subgroup.zpowers d) ↔ d v = v := fun v => by
    rw [mem_fixSp_iff hB]
    constructor
    · intro h
      exact h d (Subgroup.mem_zpowers d)
    · intro h g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact zpow_apply_eq_self h k
  have hker : fixSp (Subgroup.zpowers d) = LinearMap.ker ((d : V →ₗ[K] V) - LinearMap.id) := by
    ext v
    rw [hfix, LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_eq_zero]
  have h6' : 6 ≤ finrank K (fixSp (Subgroup.zpowers d)) := by rw [hker]; exact h6
  have hcent : ∀ c : V ≃ₗ[K] V, c * d = d * c →
      c ∈ Subgroup.centralizer (Subgroup.zpowers d : Set (V ≃ₗ[K] V)) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute d c from hc.symm) k).eq
  set R := Q.restrict (fixSp (Subgroup.zpowers d)) with hRdef
  have hR : (polarBilin R).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hB hBO)
  obtain ⟨hq, -⟩ := LayerPDiv.isQuasisimple_commutator_of_not_split hR (by omega)
    (fun h => by omega)
  set O₀ := TauCeti.QuadraticMap.orthogonalGroup R with hO₀
  have hLN : (⁅O₀, O₀⁆).map (extFix hB) ≤ fixPart hB Q :=
    Subgroup.map_mono (Subgroup.commutator_le_self O₀)
  have hfixO := fixPart_le hB hBO (Q := Q)
  refine ⟨(⁅O₀, O₀⁆).map (extFix hB), ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((⁅O₀, O₀⁆).equivMapOfInjective _ (extFix_injective hB)) hq
  · rw [Subgroup.map_commutator]
    have h1 : O₀.map (extFix hB) ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
      fun g hg => (hfixO hg).2
    exact Subgroup.commutator_mono h1 h1
  · intro g hg
    have h1 := (hfixO (hLN hg)).1
    exact (Subgroup.mem_centralizer_iff.mp h1 d (Subgroup.mem_zpowers d)).symm
  · intro c hcO hcd g hg
    exact conj_mem_map_extFix hB hBO
      (fun u hu s hs => LayerPDiv.conj_mem_commutator_self O₀ hu hs) ⟨hcent c hcd, hcO⟩ hg
  · intro z hzO hzd hzL v hv
    have hzC : z ∈ Subgroup.centralizer (Subgroup.zpowers d : Set (V ≃ₗ[K] V)) ⊓
        TauCeti.QuadraticMap.orthogonalGroup Q := ⟨hcent z hzd, hzO⟩
    rw [centralizer_eq_map_split hB hBO] at hzC
    obtain ⟨⟨z₀, z₁⟩, hz01, rfl⟩ := hzC
    obtain ⟨hz₀O, -⟩ := Subgroup.mem_prod.mp hz01
    have hz₀ : z₀ = 1 := by
      refine OrthRegular.eq_one_of_commute_orthDerived hR (by omega)
        (fun h => by rcases h with ⟨h, -⟩ | ⟨⟨h, -⟩, -⟩ <;> omega) hz₀O fun y hy => ?_
      have h1 := hzL (extFix hB y) ⟨y, hy, rfl⟩
      have h2 : split hB (z₀ * y, z₁ * 1) = split hB (y * z₀, 1 * z₁) := by
        rw [← Prod.mk_mul_mk, ← Prod.mk_mul_mk, map_mul, map_mul]
        exact h1
      exact congrArg Prod.fst (split_injective hB h2)
    subst hz₀
    have hv' : v ∈ fixSp (Subgroup.zpowers d) := (hfix v).mpr hv
    have h3 := split_apply_fix hB (1, z₁) ⟨v, hv'⟩
    exact h3

theorem exists_fix_quad_ne_zero (hQ : (polarBilin Q).Nondegenerate) {d : V ≃ₗ[K] V}
    (hdO : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdp : d ^ p = 1) (h1 : 1 ≤ finrank K (LinearMap.ker ((d : V →ₗ[K] V) - LinearMap.id))) :
    ∃ w₀ : V, d w₀ = w₀ ∧ Q w₀ ≠ 0 := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Fintype (Subgroup.zpowers d) := Fintype.ofFinite _
  have hB : (Fintype.card (Subgroup.zpowers d) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
    exact natCast_card_ne_zero_of_odd
      (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hdp))
  have hBO : Subgroup.zpowers d ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.zpowers_le.mpr hdO
  have hfix : ∀ v, v ∈ fixSp (Subgroup.zpowers d) ↔ d v = v := fun v => by
    rw [mem_fixSp_iff hB]
    constructor
    · intro h
      exact h d (Subgroup.mem_zpowers d)
    · intro h g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact zpow_apply_eq_self h k
  have hker : fixSp (Subgroup.zpowers d) = LinearMap.ker ((d : V →ₗ[K] V) - LinearMap.id) := by
    ext v
    rw [hfix, LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_eq_zero]
  set R := Q.restrict (fixSp (Subgroup.zpowers d)) with hRdef
  have hR : (polarBilin R).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hB hBO)
  have : Nontrivial (fixSp (Subgroup.zpowers d)) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [hker]; omega)
  obtain ⟨x, hx0⟩ := exists_ne (0 : fixSp (Subgroup.zpowers d))
  obtain ⟨y, hxy⟩ : ∃ y, polar R x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (hR.1 x fun y => by rw [polarBilin_apply_apply]; exact h y)
  obtain ⟨u, hu⟩ : ∃ u : fixSp (Subgroup.zpowers d), R u ≠ 0 := by
    by_contra h
    push Not at h
    apply hxy
    rw [polar, h, h, h, sub_zero, sub_zero]
  exact ⟨u, (hfix u).mp u.2, hu⟩

theorem exists_splitComponent (hQ : (polarBilin Q).Nondegenerate) {d : V ≃ₗ[K] V}
    (hdO : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdp : d ^ p = 1) (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3)
    (h4 : finrank K (LinearMap.ker ((d : V →ₗ[K] V) - LinearMap.id)) = 4) {S : Submodule K V}
    (hS2 : finrank K S = 2) (hSQ : ∀ x ∈ S, Q x = 0) (hSd : ∀ x ∈ S, d x = x) :
    ∃ Fp Mp : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple Fp ∧
      Nonempty (↥Fp ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧ Fp ≤ Mp ∧
      (∀ x ∈ Mp, ∀ y ∈ Fp, x * y * x⁻¹ ∈ Fp) ∧
      Mp ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      (∀ g ∈ Mp, g * d = d * g) ∧
      ∀ c ∈ TauCeti.QuadraticMap.orthogonalGroup Q, c * d = d * c → ∀ g ∈ Mp,
        c * g * c⁻¹ ∈ Mp := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Fintype (Subgroup.zpowers d) := Fintype.ofFinite _
  have hB : (Fintype.card (Subgroup.zpowers d) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
    exact natCast_card_ne_zero_of_odd
      (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hdp))
  have hBO : Subgroup.zpowers d ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.zpowers_le.mpr hdO
  have hfix : ∀ v, v ∈ fixSp (Subgroup.zpowers d) ↔ d v = v := fun v => by
    rw [mem_fixSp_iff hB]
    constructor
    · intro h
      exact h d (Subgroup.mem_zpowers d)
    · intro h g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact zpow_apply_eq_self h k
  have hker : fixSp (Subgroup.zpowers d) = LinearMap.ker ((d : V →ₗ[K] V) - LinearMap.id) := by
    ext v
    rw [hfix, LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_eq_zero]
  have hcent : ∀ c : V ≃ₗ[K] V, c * d = d * c →
      c ∈ Subgroup.centralizer (Subgroup.zpowers d : Set (V ≃ₗ[K] V)) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute d c from hc.symm) k).eq
  set R := Q.restrict (fixSp (Subgroup.zpowers d)) with hRdef
  have hR : (polarBilin R).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_fixSp hQ hB hBO)
  have h4' : finrank K (fixSp (Subgroup.zpowers d)) = 4 := hker ▸ h4
  have hSW : S ≤ fixSp (Subgroup.zpowers d) := fun x hx => (hfix x).mpr (hSd x hx)
  have hS' : ∃ S' : Submodule K (fixSp (Subgroup.zpowers d)), finrank K S' = 2 ∧
      ∀ x ∈ S', R x = 0 :=
    ⟨S.comap (fixSp (Subgroup.zpowers d)).subtype,
      by rw [← hS2]; exact (Submodule.comapSubtypeEquivOfLe hSW).finrank_eq,
      fun x hx => hSQ x hx⟩
  obtain ⟨-, e, -, -, hcomm, hLq, -, hLn, -, -, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_split_four_derived hK2 hK3 R hR h4' hS'
  obtain ⟨Lf, hLf⟩ : ∃ Lf, Lf = (CFSG.LocalAnalysis.ComponentInitial.determinantLeftFactor K).map
    e.symm.toMonoidHom := ⟨_, rfl⟩
  rw [← hLf] at hcomm hLq hLn
  have hLfc : Lf ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    le_sup_left.trans hcomm.ge
  have hLfO : Lf.map (TauCeti.QuadraticMap.orthogonalGroup R).subtype ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup R, TauCeti.QuadraticMap.orthogonalGroup R⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.map_mono hLfc
  have hfixO := fixPart_le hB hBO (Q := Q)
  have hLN : (⁅TauCeti.QuadraticMap.orthogonalGroup R,
      TauCeti.QuadraticMap.orthogonalGroup R⁆).map (extFix hB) ≤ fixPart hB Q :=
    Subgroup.map_mono (Subgroup.commutator_le_self _)
  obtain ⟨eSL⟩ := CFSG.ComponentClassification.Burgoyne.C.nonempty_equiv_determinantLeftFactor
    (K := K)
  have eF : ↥Lf ≃*
      ↥((Lf.map (TauCeti.QuadraticMap.orthogonalGroup R).subtype).map (extFix hB)) :=
    (Lf.equivMapOfInjective (TauCeti.QuadraticMap.orthogonalGroup R).subtype
      (TauCeti.QuadraticMap.orthogonalGroup R).subtype_injective).trans
      ((Lf.map (TauCeti.QuadraticMap.orthogonalGroup R).subtype).equivMapOfInjective
        (extFix hB) (extFix_injective hB))
  have eD : ↥(CFSG.LocalAnalysis.ComponentInitial.determinantLeftFactor K) ≃* ↥Lf :=
    ((CFSG.LocalAnalysis.ComponentInitial.determinantLeftFactor K).equivMapOfInjective
      e.symm.toMonoidHom e.symm.injective).trans (MulEquiv.subgroupCongr hLf.symm)
  refine ⟨(Lf.map (TauCeti.QuadraticMap.orthogonalGroup R).subtype).map (extFix hB),
    (⁅TauCeti.QuadraticMap.orthogonalGroup R,
      TauCeti.QuadraticMap.orthogonalGroup R⁆).map (extFix hB),
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eF hLq, ⟨eF.symm.trans (eD.symm.trans eSL)⟩,
    Subgroup.map_mono hLfO, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x₀, hx₀, rfl⟩ _ ⟨y₀, ⟨l, hl, rfl⟩, rfl⟩
    rw [← Subgroup.map_subtype_commutator] at hx₀
    obtain ⟨c, hc, rfl⟩ := hx₀
    have h1 := (hLn.conj_mem ⟨l, hLfc hl⟩ (Subgroup.mem_subgroupOf.mpr hl) ⟨c, hc⟩)
    rw [Subgroup.mem_subgroupOf] at h1
    refine ⟨(TauCeti.QuadraticMap.orthogonalGroup R).subtype (c * l * c⁻¹), ⟨_, h1, rfl⟩, ?_⟩
    simp only [map_mul, map_inv]
  · rw [Subgroup.map_commutator]
    have h1 : (TauCeti.QuadraticMap.orthogonalGroup R).map (extFix hB) ≤
        TauCeti.QuadraticMap.orthogonalGroup Q :=
      fun g hg => (hfixO hg).2
    exact Subgroup.commutator_mono h1 h1
  · intro g hg
    have h1 := (hfixO (hLN hg)).1
    exact (Subgroup.mem_centralizer_iff.mp h1 d (Subgroup.mem_zpowers d)).symm
  · intro c hcO hcd g hg
    exact conj_mem_map_extFix hB hBO
      (fun u hu s hs => LayerPDiv.conj_mem_commutator_self
        (TauCeti.QuadraticMap.orthogonalGroup R) hu hs) ⟨hcent c hcd, hcO⟩ hg

end WitOmNs

end CFSG.StandardType
