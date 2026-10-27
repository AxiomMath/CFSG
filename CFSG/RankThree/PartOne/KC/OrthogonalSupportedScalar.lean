module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarConj
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedMaps
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary

public section

namespace CFSG.RankThree.PartOne

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

theorem supported_orthogonal_derived_semilinear_centralizer_scalar_restriction
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (_hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (W : Submodule K V) (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hW3 : 3 ≤ finrank K W) (hperf : Group.IsPerfect ↥(supportedDerived Q W))
    (hW4 : Nat.card K = 2 → finrank K W = 4 →
      ∀ U : Submodule K W, finrank K U = 2 → ∃ u ∈ U, (Q.comp W.subtype) u ≠ 0)
    (σ : K ≃+* K) (F : V ≃+ V) (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (μ : K) (_hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))
    (hκ : ∀ g g' : ↥(orthDerived Q), (g : V ≃ₗ[K] V) ∈ supportedDerived Q W →
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      (QuotientGroup.mk g' : ProjOrthDerived Q) = QuotientGroup.mk g) :
    supportedDerived Q W ≤ orthDerived Q ∧ F '' (W : Set V) = (W : Set V) ∧
      σ = RingEquiv.refl K ∧ (∃ c : Kˣ, ∀ w ∈ W, F w = (c : K) • w) ∧
      {v : V | ∀ g ∈ supportedDerived Q W, g v = v} = (suppPerp Q W : Set V) ∧
      ∀ g ∈ supportedDerived Q W, ∀ v, F (g v) = g (F v) := by
  have hWreg : PolarNondegOn Q W := polarNondegOn_of_nondegenerate hW
  have hsing : ∃ e ∈ W, e ≠ 0 ∧ Q e = 0 := by
    obtain ⟨P'⟩ := CFSG.RankThree.Classical.nonempty_hypPair_of_finite hW hW3
    exact ⟨(P'.e : V), P'.e.2, fun h0 => P'.e_ne_zero (Subtype.ext h0), P'.Q_e⟩
  have hM : ElementaryMapsMem Q W := elementaryMapsMem_of_regular hW hW3 hW4
  have hle : supportedDerived Q W ≤ orthDerived Q :=
    supportedDerived_le_orthDerived_of_perfect hWreg hperf
  have hcomm := commute_of_projective_centralizes F σ hFσ μ hFQ hperf hle hκ
  have hfix : ∀ v, (∀ g ∈ supportedDerived Q W, g v = v) → v ∈ suppPerp Q W := fun v =>
    (forall_fixed_iff_mem_suppPerp hW hW3 hsing hM).mp
  have hFperp : ∀ v ∈ suppPerp Q W, F v ∈ suppPerp Q W := fun v hv =>
    map_mem_suppPerp_of_commute F hcomm hfix hv
  have hFW : ∀ x ∈ W, F x ∈ W := fun x hx => map_mem_of_map_suppPerp F σ μ hFQ hQ hFperp hx
  obtain ⟨hσ, c, hc0, hc⟩ := scalar_restriction_of_commute F σ μ hFQ hcomm hQ hW hW3 hsing hM hFσ
  refine ⟨hle, Set.Subset.antisymm ?_ ?_, RingEquiv.ext hσ, ⟨Units.mk0 c hc0, hc⟩,
    Set.ext fun v => forall_fixed_iff_mem_suppPerp hW hW3 hsing hM, hcomm⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hFW x hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := exists_map_eq_of_mapsTo F W hFW hy
    exact ⟨x, hx, rfl⟩

theorem supported_orthogonal_derived_semilinear_centralizer_scalar_restriction_of_automorphism
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (W : Submodule K V) (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hW3 : 3 ≤ finrank K W) (hperf : Group.IsPerfect ↥(supportedDerived Q W))
    (hW4 : Nat.card K = 2 → finrank K W = 4 →
      ∀ U : Submodule K W, finrank K U = 2 → ∃ u ∈ U, (Q.comp W.subtype) u ≠ 0)
    (σ : K ≃+* K) (F : V ≃+ V) (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (μ : K) (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))
    (κ : ProjOrthDerived Q ≃* ProjOrthDerived Q)
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hκ : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[K] V) ∈ supportedDerived Q W →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g) :
    supportedDerived Q W ≤ orthDerived Q ∧ F '' (W : Set V) = (W : Set V) ∧
      σ = RingEquiv.refl K ∧ (∃ c : Kˣ, ∀ w ∈ W, F w = (c : K) • w) ∧
      {v : V | ∀ g ∈ supportedDerived Q W, g v = v} = (suppPerp Q W : Set V) ∧
      ∀ g ∈ supportedDerived Q W, ∀ v, F (g v) = g (F v) :=
  supported_orthogonal_derived_semilinear_centralizer_scalar_restriction Q hQ hT W hW hW3 hperf
    hW4 σ F hFσ μ hμ hFQ fun g g' hg hg' => (hκF g g' hg').symm.trans (hκ g hg)

namespace KCOrthogonal

theorem semilin_image_eq_of_normalizes_supportedDerived
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {R : Submodule K V}
    (hK : 2 < Nat.card K) (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp R.subtype)).Nondegenerate)
    (hR3 : 3 ≤ finrank K R)
    (F : V ≃+ V) (σ : K ≃+* K)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (μ : K) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))
    (hnorm : (supportedDerived Q R).map (semilinConj F σ hF) = supportedDerived Q R) :
    F '' (R : Set V) = (R : Set V) := by
  have h4 : Nat.card K = 2 → finrank K R = 4 →
      ∀ U : Submodule K R, finrank K U = 2 → ∃ u ∈ U, (Q.comp R.subtype) u ≠ 0 :=
    fun h2 => absurd h2 (by omega)
  have hsing : ∃ e ∈ R, e ≠ 0 ∧ Q e = 0 := by
    obtain ⟨P'⟩ := CFSG.RankThree.Classical.nonempty_hypPair_of_finite hR hR3
    exact ⟨(P'.e : V), P'.e.2, fun h0 => P'.e_ne_zero (Subtype.ext h0), P'.Q_e⟩
  have hM : ElementaryMapsMem Q R := elementaryMapsMem_of_regular hR hR3 h4
  have hfix : ∀ v, (∀ g ∈ supportedDerived Q R, g v = v) → v ∈ suppPerp Q R := fun v =>
    (forall_fixed_iff_mem_suppPerp hR hR3 hsing hM).mp
  have hFperp : ∀ v ∈ suppPerp Q R, F v ∈ suppPerp Q R := by
    intro v hv
    refine hfix (F v) ?_
    intro g hg
    have hg' : g ∈ (supportedDerived Q R).map (semilinConj F σ hF) := by
      rwa [hnorm]
    obtain ⟨u, hu, hfu⟩ := Subgroup.mem_map.mp hg'
    rw [← hfu, semilinConj_apply, AddEquiv.symm_apply_apply, supportedDerived_apply_perp hu hv]
  have hFR : ∀ x ∈ R, F x ∈ R := fun x hx =>
    map_mem_of_map_suppPerp F σ μ hFQ hQ hFperp hx
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hFR x hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := exists_map_eq_of_mapsTo F R hFR hy
    exact ⟨x, hx, rfl⟩

theorem semilinConj_mem_supportedDerived_of_map_eq
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {R R' : Submodule K V}
    (F : V ≃+ V) (σ : K ≃+* K)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (μ : K) (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))
    (hR : F '' (R : Set V) = (R' : Set V)) {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedDerived Q R) :
    semilinConj F σ hF g ∈ supportedDerived Q R' := by
  letI : RingHomInvPair (σ : K →+* K) (σ.symm : K →+* K) :=
    RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair (σ.symm : K →+* K) (σ : K →+* K) :=
    RingHomInvPair.of_ringEquiv_symm σ
  have hmap : R.map (semilinLinearEquiv (σ := σ) F hF).toLinearMap = R' := by
    apply SetLike.coe_injective
    rw [Submodule.map_coe]
    simpa [semilinLinearEquiv] using hR
  have h := autCongr_mem_supportedDerived_of_map_eq (σ := σ)
    (e := semilinLinearEquiv (σ := σ) F hF) μ hμ hFQ hmap hg
  rw [semilinConj_eq_autCongr (σ := σ) F hF]
  exact h

theorem semilinConj_mem_supportedDerived_of_image_eq
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {R : Submodule K V}
    (F : V ≃+ V) (σ : K ≃+* K)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (μ : K) (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))
    (hR : F '' (R : Set V) = (R : Set V)) {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedDerived Q R) :
    semilinConj F σ hF g ∈ supportedDerived Q R :=
  semilinConj_mem_supportedDerived_of_map_eq F σ hF μ hμ hFQ hR hg

theorem map_supportedDerived_semilinConj_of_map_eq
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {R R' : Submodule K V}
    (F : V ≃+ V) (σ : K ≃+* K)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (μ : K) (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))
    (hR : F '' (R : Set V) = (R' : Set V)) :
    (supportedDerived Q R).map (semilinConj F σ hF) = supportedDerived Q R' := by
  letI : RingHomInvPair (σ : K →+* K) (σ.symm : K →+* K) :=
    RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair (σ.symm : K →+* K) (σ : K →+* K) :=
    RingHomInvPair.of_ringEquiv_symm σ
  have hmap : R.map (semilinLinearEquiv (σ := σ) F hF).toLinearMap = R' := by
    apply SetLike.coe_injective
    rw [Submodule.map_coe]
    simpa [semilinLinearEquiv] using hR
  have h := map_supportedDerived_autCongr_of_map_eq (σ := σ)
    (e := semilinLinearEquiv (σ := σ) F hF) μ hμ hFQ hmap
  rw [semilinConj_eq_autCongr (σ := σ) F hF]
  exact h

theorem map_supportedDerived_semilinConj_of_image_eq
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {R : Submodule K V}
    (F : V ≃+ V) (σ : K ≃+* K)
    (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (μ : K) (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))
    (hR : F '' (R : Set V) = (R : Set V)) :
    (supportedDerived Q R).map (semilinConj F σ hF) = supportedDerived Q R :=
  map_supportedDerived_semilinConj_of_map_eq F σ hF μ hμ hFQ hR

theorem map_supportedDerived_conj_of_map_eq
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {R R' : Submodule K V}
    (g : V ≃ₗ[K] V) (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hR : R.map g.toLinearMap = R') :
    (supportedDerived Q R).map (MulAut.conj g).toMonoidHom = supportedDerived Q R' := by
  let F : V ≃+ V := g.toAddEquiv
  let σ : K ≃+* K := RingEquiv.refl K
  have hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v := fun c v => g.map_smul c v
  have hFQ : ∀ v, Q (F v) = (1 : K) * σ (Q v) := by
    intro v
    rw [one_mul, show σ (Q v) = Q v from rfl]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg v
  have hset : F '' (R : Set V) = (R' : Set V) := by
    have hcoe : (R.map g.toLinearMap : Set V) = g.toLinearMap '' (R : Set V) :=
      Submodule.map_coe g.toLinearMap R
    rw [← hR, hcoe]
    rfl
  have hhom : (MulAut.conj g).toMonoidHom = semilinConj F σ hF := by
    refine MonoidHom.ext fun x => LinearEquiv.ext fun v => ?_
    simp [F, σ, semilinConj_apply, MulAut.conj_apply]
  rw [hhom]
  exact map_supportedDerived_semilinConj_of_map_eq F σ hF 1 one_ne_zero hFQ hset

end KCOrthogonal

end CFSG.RankThree.PartOne
