module

public import CFSG.LocalAnalysis.UniqueFourCatalog.OddClassicalGeneric
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthBig
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU1ThreeQS
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

open CFSG.Open

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

section OrthInvolution

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.ModelFacts
open scoped commutatorElement

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem negI_negI (i : V ≃ₗ[K] V) : negI (negI i) = i :=
  LinearEquiv.ext fun x => by simp [negI_apply]

theorem extGrp_mem_elementaryGroup (h2 : (2 : K) ≠ 0) {i : V ≃ₗ[K] V} (hii : i * i = 1)
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {g' : minusSp i ≃ₗ[K] minusSp i}
    (hg' : g' ∈ elementaryGroup (Q.restrict (minusSp i))) :
    extGrp h2 hii g' ∈ elementaryGroup Q := by
  obtain ⟨g, hg, hgW, hgz⟩ :=
    exists_extend_of_mem_elementaryGroup_restrict (Q := Q) (W := minusSp i) hg'
  have : extGrp h2 hii g' = g := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_eq h2 hii v
    rw [extGrp_apply_add h2 hii g' hu hw, map_add,
      hgz u (fun x hx => polar_plusSp_minusSp h2 hi hu hx), hgW ⟨w, hw⟩, add_comm]
  rw [this]
  exact hg

theorem conj_extGrp (h2 : (2 : K) ≠ 0) {i : V ≃ₗ[K] V} (hii : i * i = 1) {g : V ≃ₗ[K] V}
    (hc : g * i = i * g) (g' : minusSp i ≃ₗ[K] minusSp i) :
    g * extGrp h2 hii g' * g⁻¹ =
      extGrp h2 hii (restrictMinus g hc * g' * (restrictMinus g hc)⁻¹) := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_eq h2 hii v
  have hgi : g⁻¹ * i = i * g⁻¹ := inv_mul_eq_mul_inv_of hc
  have hu' : g⁻¹ u ∈ plusSp i := map_mem_plusSp hgi hu
  have hw' : g⁻¹ w ∈ minusSp i := map_mem_minusSp hgi hw
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_add,
    extGrp_apply_add h2 hii g' hu' hw', map_add, extGrp_apply_add h2 hii _ hu hw,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply, restrictMinus_apply, LinearEquiv.apply_inv_apply']
  rfl

theorem not_isCharTwoType_projElementary_of_involution [Finite K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) {i : V ≃ₗ[K] V} (hii : i * i = 1) (hE : negI i ∈ elementaryGroup Q)
    (hP : plusSp i ≠ ⊥) (hM : minusSp i ≠ ⊥)
    (hq : CFSG.Open.IsQuasisimple ↥(elementaryGroup (Q.restrict (minusSp i)))) :
    ¬ IsCharTwoType (ProjElementary Q) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have hfin : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
  have hfinE : Finite ↥(elementaryGroup Q) := inferInstance
  have htO : negI i ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hE
  have hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    have := negI_mem_orthogonalGroup htO
    rwa [negI_negI] at this
  let E' := elementaryGroup (Q.restrict (minusSp i))
  let φ : ↥E' →* ↥(elementaryGroup Q) :=
    ((extGrp h2 hii).comp E'.subtype).codRestrict (elementaryGroup Q)
      (fun x => extGrp_mem_elementaryGroup h2 hii hi x.2)
  have hφinj : Function.Injective φ := fun a b h =>
    Subtype.ext (extGrp_injective h2 hii (congrArg Subtype.val h))
  have hφapp : ∀ y : ↥E', ((φ y : ↥(elementaryGroup Q)) : V ≃ₗ[K] V) = extGrp h2 hii y.1 :=
    fun y => rfl
  obtain ⟨x₀, hx₀M, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  obtain ⟨y₀, hy₀P, hy₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  refine not_isCharTwoType_quotient_of_quasisimple ((scalars K V).subgroupOf (elementaryGroup Q))
    ?_ (t := ⟨negI i, hE⟩) ?_ ?_ (J := φ.range) ?_ ?_ ?_
    (CFSG.Open.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hφinj).symm hq)
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (commute_of_mem_scalars (Subgroup.mem_subgroupOf.mp hx) g).symm
  · intro ht
    obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp ht)
    have e1 := hc x₀
    have e2 := hc y₀
    rw [negI_apply, mem_minusSp.mp hx₀M, neg_neg] at e1
    rw [negI_apply, mem_plusSp.mp hy₀P] at e2
    have h1 : c = 1 := by
      have : (1 - c) • x₀ = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hx₀)).symm
    have h2' : c = -1 := by
      have : (c + 1) • y₀ = 0 := by rw [add_smul, one_smul, ← e2, neg_add_cancel]
      exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp this).resolve_right hy₀)
    exact h2 (by linear_combination h2' - h1)
  · have : (⟨negI i, hE⟩ : ↥(elementaryGroup Q)) ^ 2 = 1 :=
      Subtype.ext (by simpa [pow_two] using negI_mul_self hii)
    rw [this]
    exact Subgroup.one_mem _
  · rintro _ ⟨y, rfl⟩
    refine Subtype.ext ?_
    change (φ y : V ≃ₗ[K] V) * negI i = negI i * (φ y : V ≃ₗ[K] V)
    rw [hφapp]
    exact mul_negI_comm (extGrp_mem_nM h2 hii hi
      (elementaryGroup_le_orthogonalGroup (Q.restrict (minusSp i)) y.2)).2.1
  · rintro g hg _ ⟨y, rfl⟩
    have hgc' : (g : V ≃ₗ[K] V) * negI i = negI i * (g : V ≃ₗ[K] V) := congrArg Subtype.val hg
    have hc : (g : V ≃ₗ[K] V) * i = i * (g : V ≃ₗ[K] V) := by
      have := mul_negI_comm (i := negI i) hgc'
      rwa [negI_negI] at this
    have hgO : (g : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      elementaryGroup_le_orthogonalGroup Q g.2
    have hrO : restrictMinus (g : V ≃ₗ[K] V) hc ∈
        TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (minusSp i)) :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => map_of_mem hgO (x : V)
    have hmem : restrictMinus (g : V ≃ₗ[K] V) hc * y.1 * (restrictMinus (g : V ≃ₗ[K] V) hc)⁻¹ ∈
        E' := conj_mem_elementaryGroup hrO y.2
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [hφapp]
    change extGrp h2 hii _ = (g : V ≃ₗ[K] V) * (φ y : V ≃ₗ[K] V) * (g : V ≃ₗ[K] V)⁻¹
    rw [hφapp, conj_extGrp h2 hii hc]
  · rw [eq_bot_iff]
    rintro x ⟨⟨y, rfl⟩, hxN⟩
    obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp hxN)
    rw [hφapp] at hc
    have hu : extGrp h2 hii y.1 y₀ = y₀ := by
      have := extGrp_apply_add h2 hii y.1 hy₀P (Submodule.zero_mem (minusSp i))
      rw [add_zero] at this
      rw [this]
      simp
    have hc1 : c = 1 := by
      have := hc y₀
      rw [hu] at this
      have h3 : (1 - c) • y₀ = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy₀)).symm
    have : y = 1 := by
      apply hφinj
      refine Subtype.ext ?_
      rw [hφapp, map_one]
      refine LinearEquiv.ext fun v => ?_
      rw [hc v, hc1, one_smul]
      rfl
    rw [this, map_one]
    exact Subgroup.one_mem _

theorem exists_involution_orth [Finite K] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q} (hPP' : P.Orth P')
    (hdim : 7 ≤ Module.finrank K V) :
    ∃ i : V ≃ₗ[K] V, i * i = 1 ∧ negI i ∈ elementaryGroup Q ∧ plusSp i ≠ ⊥ ∧ minusSp i ≠ ⊥ ∧
      5 ≤ Module.finrank K (minusSp i) := by
  classical
  set a : V := P.e + P.f with ha
  set b : V := P'.e + P'.f with hb
  set c : V := a + b with hc
  set w : V := b - a with hw
  have hQa : Q a = 1 := by
    rw [ha, QuadraticMap.map_add Q, P.Q_e, P.Q_f, P.polar_ef]; ring
  have hQb : Q b = 1 := by
    rw [hb, QuadraticMap.map_add Q, P'.Q_e, P'.Q_f, P'.polar_ef]; ring
  have hab : polar Q a b = 0 := by
    rw [ha, hb, polar_add_left, polar_add_right, polar_add_right, hPP'.ee, hPP'.ef, hPP'.fe,
      hPP'.ff]; ring
  have hba : polar Q b a = 0 := by rw [polar_comm, hab]
  have haa : polar Q a a = 2 := by rw [polar_self_eq_two_mul Q, hQa]; ring
  have hbb : polar Q b b = 2 := by rw [polar_self_eq_two_mul Q, hQb]; ring
  have hQc : Q c = 2 := by rw [hc, QuadraticMap.map_add Q, hQa, hQb, hab]; ring
  have hQw : Q w = 2 := by
    rw [hw, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q, polar_neg_right, hQa,
      hQb, hba]; ring
  have hcw : polar Q c w = 0 := by
    rw [hc, hw, polar_add_left, polar_sub_right, polar_sub_right, hab, hba, haa, hbb]; ring
  have hwc : polar Q w c = 0 := by rw [polar_comm, hcw]
  have hac : polar Q a c = 2 := by rw [hc, polar_add_right, haa, hab]; ring
  have hQa0 : Q a ≠ 0 := by rw [hQa]; exact one_ne_zero
  have hQc0 : Q c ≠ 0 := by rw [hQc]; exact h2
  have hQw0 : Q w ≠ 0 := by rw [hQw]; exact h2
  have hra : reflect Q a c = w := by
    rw [reflect_apply hQa0, hac, hQa, hw, hc]
    module
  set t : V ≃ₗ[K] V := ⁅reflect Q a, reflect Q c⁆ with ht
  have htE : t ∈ elementaryGroup Q := commutatorElement_reflect_mem hQ hPP' a c
  have ht_eq : t = reflect Q w * reflect Q c := by
    show reflect Q a * reflect Q c * (reflect Q a)⁻¹ * (reflect Q c)⁻¹ = _
    rw [reflect_conj (reflect_mem_orthogonalGroup Q a), hra, reflect_inv]
  have hcomm : reflect Q c * reflect Q w = reflect Q w * reflect Q c := by
    have := reflect_conj (reflect_mem_orthogonalGroup Q c) w
    rw [reflect_apply_of_polar_eq_zero hcw, reflect_inv] at this
    calc reflect Q c * reflect Q w = reflect Q c * reflect Q w * (reflect Q c * reflect Q c) := by
          rw [reflect_mul_self, mul_one]
      _ = (reflect Q c * reflect Q w * reflect Q c) * reflect Q c := by group
      _ = reflect Q w * reflect Q c := by rw [this]
  have htt : t * t = 1 := by
    rw [ht_eq]
    calc reflect Q w * reflect Q c * (reflect Q w * reflect Q c)
        = reflect Q w * (reflect Q c * reflect Q w) * reflect Q c := by group
      _ = reflect Q w * (reflect Q w * reflect Q c) * reflect Q c := by rw [hcomm]
      _ = (reflect Q w * reflect Q w) * (reflect Q c * reflect Q c) := by group
      _ = 1 := by rw [reflect_mul_self, reflect_mul_self, one_mul]
  have htx : ∀ x, t x = x - (polar Q c x / 2) • c - (polar Q w x / 2) • w := by
    intro x
    rw [ht_eq, LinearEquiv.mul_apply, reflect_apply hQc0, reflect_apply hQw0, polar_sub_right,
      polar_smul_right_eq, hwc, hQc, hQw]
    simp
  have hct : t c = -c := by
    rw [htx, polar_self_eq_two_mul Q, hQc, hwc]
    have : (2 * 2 : K) / 2 = 2 := by field_simp
    rw [this]
    simp
    module
  have hK₀ : ∀ x, polar Q c x = 0 → polar Q w x = 0 → t x = x := by
    intro x h1 h2'
    rw [htx, h1, h2']
    simp
  let f : V →ₗ[K] K × K := LinearMap.prod (polarBilin Q c) (polarBilin Q w)
  have hker : LinearMap.ker f ≤ plusSp t := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h1 : polar Q c x = 0 := congrArg Prod.fst hx
    have h2' : polar Q w x = 0 := congrArg Prod.snd hx
    exact mem_plusSp.mpr (hK₀ x h1 h2')
  have hdimker : Module.finrank K V ≤ 2 + Module.finrank K (LinearMap.ker f) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h3 : Module.finrank K (LinearMap.range f) ≤ 2 := by
      have := Submodule.finrank_le (LinearMap.range f)
      simpa [Module.finrank_prod] using this
    omega
  have hdimP : 5 ≤ Module.finrank K (plusSp t) :=
    (show 5 ≤ Module.finrank K (LinearMap.ker f) by omega).trans (Submodule.finrank_mono hker)
  have hc0 : c ≠ 0 := by
    intro h0
    apply hQc0
    rw [h0, QuadraticMap.map_zero]
  refine ⟨negI t, negI_mul_self htt, by rwa [negI_negI], ?_, ?_, ?_⟩
  · rw [plusSp_negI]
    intro hbot
    have : c ∈ minusSp t := mem_minusSp.mpr hct
    rw [hbot] at this
    exact hc0 ((Submodule.mem_bot K).mp this)
  · rw [minusSp_negI]
    intro hbot
    rw [hbot] at hdimP
    simp at hdimP
  · rw [minusSp_negI]
    exact hdimP

theorem not_isCharTwoType_projElementary [Finite K] [FiniteDimensional K V]
    (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate) {P P' : HypPair Q}
    (hPP' : P.Orth P') (hdim : 7 ≤ Module.finrank K V) :
    ¬ IsCharTwoType (ProjElementary Q) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  obtain ⟨i, hii, hE, hP, hM, hd⟩ := exists_involution_orth h2 hQ hPP' hdim
  have htO : negI i ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hE
  have hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    have := negI_mem_orthogonalGroup htO
    rwa [negI_negI] at this
  have hndeg : (polarBilin (Q.restrict (minusSp i))).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_minusSp h2 hQ hi hii)
  refine not_isCharTwoType_projElementary_of_involution h2 hii hE hP hM ?_
  by_cases h3 : Nat.card K = 3
  · exact CFSG.ComponentClassification.HarrisLit.T1.isQuasisimple_elementaryGroup_three h3 hndeg
      (by omega) (Or.inl (by omega))
  · have h5 : 5 ≤ Nat.card K := by
      obtain ⟨k, hk⟩ := hodd
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    exact CFSG.ClassicalGroups.Orthogonal.Small.isQuasisimple_elementaryGroup_small hodd h5 hndeg
      (by omega) (Or.inl (by omega))

end OrthInvolution

end CFSG.LocalAnalysis.UniqueFourCatalog
