module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerFieldFrame
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerSimilarity
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalFlag
public import CFSG.ClassicalGroups.Orthogonal.EichlerCentralizerScalar

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.LieKnownR2.POmega.Radical
open CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalGroups.PCoreSection
open QuadraticMap
open Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearField

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

private theorem imat_conj_y_pow {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {Q : QuadraticForm F (ι → F)} {A' : (ι → F) ≃ₗ[F] (ι → F)}
    {y : MulAut ↥(spinGroup Q)}
    (hact : ∀ x : ↥(spinGroup Q), spinAction Q (y x) = A' * spinAction Q x * A'⁻¹) :
    ∀ n : ℕ, ∀ x : ↥(spinGroup Q),
      spinAction Q ((y ^ n) x) = (A' ^ n) * spinAction Q x * (A' ^ n)⁻¹ := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    have h1 : (y ^ (m + 1)) x = y ((y ^ m) x) := by rw [pow_succ']; rfl
    rw [h1, hact, ih, pow_succ']
    group

theorem imat_pow_two_eq_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {Q : QuadraticForm F (ι → F)} (hS : SpinOmegaData Q)
    {P : HypPair Q} (hV : 6 ≤ Module.finrank F (ι → F))
    {y : MulAut ↥(spinGroup Q)} (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1)
    {A' : (ι → F) ≃ₗ[F] (ι → F)} (hA' : ∀ v, Q (A' v) = Q v)
    (hact : ∀ x : ↥(spinGroup Q), spinAction Q (y x) = A' * spinAction Q x * A'⁻¹) :
    ∃ k : ℕ, A' ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hy2
  refine ⟨k, ?_⟩
  have hconj := imat_conj_y_pow hact
  have hcomm : ∀ x : ↥(spinGroup Q),
      (A' ^ 2 ^ k) * spinAction Q x = spinAction Q x * (A' ^ 2 ^ k) := by
    intro x
    have hx : (A' ^ 2 ^ k) * spinAction Q x * (A' ^ 2 ^ k)⁻¹ = spinAction Q x := by
      rw [← hconj (2 ^ k) x, hk, MulAut.one_apply]
    calc (A' ^ 2 ^ k) * spinAction Q x
        = ((A' ^ 2 ^ k) * spinAction Q x * (A' ^ 2 ^ k)⁻¹) * (A' ^ 2 ^ k) := by group
      _ = spinAction Q x * (A' ^ 2 ^ k) := by rw [hx]
  have hA'pow : ∀ m : ℕ, ∀ v, Q ((A' ^ m) v) = Q v := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih => exact fun v => (ih (A' v)).trans (hA' v)
  obtain ⟨w₀, hw₀P, hw₀Q, -⟩ :=
    exists_nonsingular_of_finrank hS.nondeg (finrank_span_pair_le P.e P.f)
      (by omega : 5 ≤ Module.finrank F (ι → F))
  have hw₀Pperp : w₀ ∈ HypPair.perp (Q := Q) P := mem_orth_span_pair_iff.mp hw₀P
  let Z : (ι → F) →+ (ι → F) :=
    ((A' ^ 2 ^ k : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) →ₗ[F] (ι → F)).toAddMonoidHom
  have hZ : ∀ x, Z x = (A' ^ 2 ^ k) x := fun x => rfl
  have he : ∀ w ∈ HypPair.perp (Q := Q) P, ∀ x,
      Z (eichler Q P.e w x) = eichler Q P.e w (Z x) := by
    intro w hw x
    obtain ⟨s, hs⟩ : ∃ s : ↥(spinGroup Q), spinAction Q s = eichler Q P.e w := by
      change eichler Q P.e w ∈ (spinAction Q).range
      rw [hS.range_eq]
      exact eichler_mem_elementaryGroup Q P.e w
    have hcx := congrArg (fun e : (ι → F) ≃ₗ[F] (ι → F) => e x) (hcomm s)
    change (A' ^ 2 ^ k) (spinAction Q s x) = spinAction Q s ((A' ^ 2 ^ k) x) at hcx
    rw [hZ, hZ]
    change (A' ^ 2 ^ k) (eichler Q P.e w x) = eichler Q P.e w ((A' ^ 2 ^ k) x)
    rw [← hs]
    exact hcx
  have hf : ∀ w ∈ HypPair.perp (Q := Q) P, ∀ x,
      Z (eichler Q P.f w x) = eichler Q P.f w (Z x) := by
    intro w hw x
    obtain ⟨s, hs⟩ : ∃ s : ↥(spinGroup Q), spinAction Q s = eichler Q P.f w := by
      change eichler Q P.f w ∈ (spinAction Q).range
      rw [hS.range_eq]
      exact eichler_mem_elementaryGroup Q P.f w
    have hcx := congrArg (fun e : (ι → F) ≃ₗ[F] (ι → F) => e x) (hcomm s)
    change (A' ^ 2 ^ k) (spinAction Q s x) = spinAction Q s ((A' ^ 2 ^ k) x) at hcx
    rw [hZ, hZ]
    change (A' ^ 2 ^ k) (eichler Q P.f w x) = eichler Q P.f w ((A' ^ 2 ^ k) x)
    rw [← hs]
    exact hcx
  obtain ⟨μ, hμ⟩ := exists_eq_smul_of_commute_eichler (K := F) (V := ι → F) (Q := Q)
    hS.nondeg P ⟨w₀, hw₀Pperp, hw₀Q⟩ Z he hf
  have hμ1 : μ = 1 := by
    have hQw : Q (Z w₀) = Q w₀ := by rw [hZ]; exact hA'pow (2 ^ k) w₀
    rw [hμ w₀, map_smul_eq_sq] at hQw
    have h2 : (μ ^ 2 - 1) * Q w₀ = 0 := by linear_combination hQw
    rcases mul_eq_zero.mp h2 with h3 | h3
    · have h4 : μ ^ 2 = 1 := sub_eq_zero.mp h3
      rcases sq_eq_one_iff.mp h4 with h5 | h5
      · exact h5
      · rwa [CharTwo.neg_eq] at h5
    · exact absurd h3 hw₀Q
  exact LinearEquiv.ext fun x => by
    change Z x = (1 : (ι → F) ≃ₗ[F] (ι → F)) x
    rw [hμ x, hμ1, one_smul]
    rfl

@[expose] noncomputable def imat_projLin {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} (P : HypPair Q) : V →ₗ[F] V where
  toFun := P.proj
  map_add' := by
    intro x y
    rw [HypPair.proj, HypPair.proj, HypPair.proj, polar_add_left, polar_add_left, add_smul,
      add_smul]
    abel
  map_smul' := by
    intro c x
    rw [HypPair.proj, HypPair.proj, polar_smul_left_eq, polar_smul_left_eq, mul_smul, mul_smul,
      smul_sub, smul_sub]
    abel

@[expose] def imat_stabilizer {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (W : Submodule F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∀ x ∈ W, g x ∈ W}
  mul_mem' := by intro a b ha hb x hx; exact ha _ (hb x hx)
  one_mem' := by intro x hx; simpa using hx
  inv_mem' := by
    intro a ha x hx
    have hmap : Submodule.map (a : V →ₗ[F] V) W = W := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rintro y ⟨z, hz, rfl⟩
        exact ha z hz
      · exact LinearEquiv.finrank_map_eq a W
    have hx' : x ∈ Submodule.map (a : V →ₗ[F] V) W := by rw [hmap]; exact hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx'
    have hxy : a⁻¹ x = y := by
      rw [← hyx]
      simpa using LinearEquiv.symm_apply_apply a y
    rw [hxy]; exact hy

theorem imat_polar_eq_zero_of_mem_siegelY {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] {Q : QuadraticForm F V} {P P' : HypPair Q} (h : P.Orth P')
    {x y : V} (hx : x ∈ siegelY F P.e P'.e) (hy : y ∈ siegelY F P.e P'.e) :
    polar Q x y = 0 := by
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨d₁, d₂, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    P.polar_ee, P'.polar_ee, h.ee, polar_comm Q P'.e P.e]
  ring

private theorem imat_eq_of_mem_siegelY {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {P P' : HypPair Q} (h : P.Orth P') {x : V}
    (hx : x ∈ siegelY F P.e P'.e) :
    x = polar Q P.f x • P.e + polar Q P'.f x • P'.e := by
  obtain ⟨c₁, c₂, hc⟩ := Submodule.mem_span_pair.mp hx
  have h1 : polar Q P.f x = c₁ := by
    rw [← hc]
    simp only [polar_add_right, polar_smul_right_eq, P.polar_fe, h.fe, mul_one, mul_zero,
      add_zero]
  have h2 : polar Q P'.f x = c₂ := by
    rw [← hc]
    simp only [polar_add_right, polar_smul_right_eq, polar_comm Q P'.f P.e, h.ef, P'.polar_fe,
      mul_one, mul_zero, add_zero, zero_add]
  rw [h1, h2]
  exact hc.symm

theorem imat_tau1_sub {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {P P' : HypPair Q} (h : P.Orth P') {x : V}
    (hx : x ∈ siegelY F P.e P'.e) :
    x - eichler Q P.e P'.f x = polar Q x P'.f • P.e := by
  have hxP : polar Q x P.e = 0 :=
    imat_polar_eq_zero_of_mem_siegelY h hx (Submodule.subset_span (by simp))
  rw [eichler_apply P.Q_e h.ef, hxP, P'.Q_f]
  simp

theorem imat_tau2_sub {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {P P' : HypPair Q} (h : P.Orth P') {x : V}
    (hx : x ∈ siegelY F P.e P'.e) :
    x - eichler Q P'.e P.f x = polar Q x P.f • P'.e := by
  have hxP' : polar Q x P'.e = 0 :=
    imat_polar_eq_zero_of_mem_siegelY h hx (Submodule.subset_span (by simp))
  rw [eichler_apply P'.Q_e (by rw [polar_comm]; exact h.fe), hxP', P.Q_f]
  simp

theorem imat_submodule_eq_bot_or_siegelY {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] {Q : QuadraticForm F V} {P P' : HypPair Q} (h : P.Orth P')
    {X : Submodule F V} (hXY : X ≤ siegelY F P.e P'.e)
    (h1 : ∀ x ∈ X, eichler Q P.e P'.f x ∈ X)
    (h2 : ∀ x ∈ X, eichler Q P'.e P.f x ∈ X) :
    X = ⊥ ∨ X = siegelY F P.e P'.e := by
  by_cases hX : X = ⊥
  · exact Or.inl hX
  refine Or.inr (le_antisymm hXY ?_)
  obtain ⟨x, hxX, hx0⟩ : ∃ x ∈ X, x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hX ((Submodule.eq_bot_iff X).mpr hcon)
  have hxY : x ∈ siegelY F P.e P'.e := hXY hxX
  have hb : polar Q x P'.f • P.e ∈ X := by
    have := X.sub_mem hxX (h1 x hxX)
    rwa [imat_tau1_sub h hxY] at this
  have ha : polar Q x P.f • P'.e ∈ X := by
    have := X.sub_mem hxX (h2 x hxX)
    rwa [imat_tau2_sub h hxY] at this
  have hPe : P.e ∈ Submodule.span F {P.e, P'.e} := Submodule.subset_span (by simp)
  have hPe' : P'.e ∈ Submodule.span F {P.e, P'.e} := Submodule.subset_span (by simp)
  have hzero : polar Q x P.f = 0 ∧ polar Q x P'.f = 0 → x = 0 := by
    rintro ⟨h1', h2'⟩
    rw [imat_eq_of_mem_siegelY (Q := Q) h hxY, polar_comm Q P.f x, h1',
      polar_comm Q P'.f x, h2']
    simp
  by_cases hc1 : polar Q x P'.f = 0
  · have hc2 : polar Q x P.f ≠ 0 := by
      intro hc2
      exact hx0 (hzero ⟨hc2, hc1⟩)
    have hPe'X : P'.e ∈ X := by
      have := X.smul_mem (polar Q x P.f)⁻¹ ha
      rwa [smul_smul, inv_mul_cancel₀ hc2, one_smul] at this
    have htau : P'.e - eichler Q P.e P'.f P'.e = P.e := by
      rw [eichler_apply P.Q_e h.ef, polar_comm Q P'.e P.e, h.ee, P'.polar_ef, P'.Q_f]
      simp
    have hPeX : P.e ∈ X := htau ▸ X.sub_mem hPe'X (h1 P'.e hPe'X)
    rw [siegelY, Submodule.span_le]
    rintro v (rfl | rfl)
    · exact hPeX
    · exact hPe'X
  · have hPeX : P.e ∈ X := by
      have := X.smul_mem (polar Q x P'.f)⁻¹ hb
      rwa [smul_smul, inv_mul_cancel₀ hc1, one_smul] at this
    have htau : P.e - eichler Q P'.e P.f P.e = P'.e := by
      rw [eichler_apply P'.Q_e (by rw [polar_comm]; exact h.fe), h.ee, P.polar_ef, P.Q_f]
      simp
    have hPe'X : P'.e ∈ X := htau ▸ X.sub_mem hPeX (h2 P.e hPeX)
    rw [siegelY, Submodule.span_le]
    rintro v (rfl | rfl)
    · exact hPeX
    · exact hPe'X

theorem imat_commutator_orthSiegelCore {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {Q : QuadraticForm F (ι → F)} (hS : SpinOmegaData Q)
    {P P' : HypPair Q} (h : P.Orth P') (hV : 6 ≤ Module.finrank F (ι → F))
    (hW : GGSiegelWIrreducible Q P P')
    {y : MulAut ↥(spinGroup Q)} (htriv : GGTrivialOnNormalizer (siegelRoot Q P.e P'.e) y)
    {A' : (ι → F) ≃ₗ[F] (ι → F)}
    (hact : ∀ x : ↥(spinGroup Q), spinAction Q (y x) = A' * spinAction Q x * A'⁻¹)
    {s : ↥(spinGroup Q)}
    (hs : s ∈ Subgroup.normalizer (siegelRoot Q P.e P'.e : Set (spinGroup Q))) :
    ∃ q ∈ orthSiegelCore Q P.e P'.e,
      A' * spinAction Q s * A'⁻¹ * (spinAction Q s)⁻¹ = spinAction Q q := by
  refine ⟨y s * s⁻¹, siegelO2_le_orthSiegelCore hS h hV hW (htriv.2 s hs), ?_⟩
  rw [map_mul, map_inv, hact s]

theorem imat_commutes_on_Y {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {Q : QuadraticForm F (ι → F)} (hS : SpinOmegaData Q)
    {P P' : HypPair Q} (h : P.Orth P') (hV : 6 ≤ Module.finrank F (ι → F))
    (hW : GGSiegelWIrreducible Q P P')
    {y : MulAut ↥(spinGroup Q)} (htriv : GGTrivialOnNormalizer (siegelRoot Q P.e P'.e) y)
    {A' : (ι → F) ≃ₗ[F] (ι → F)}
    (hact : ∀ x : ↥(spinGroup Q), spinAction Q (y x) = A' * spinAction Q x * A'⁻¹)
    (hstabY : ∀ x ∈ siegelY F P.e P'.e, A' x ∈ siegelY F P.e P'.e)
    {s : ↥(spinGroup Q)}
    (hs : s ∈ Subgroup.normalizer (siegelRoot Q P.e P'.e : Set (spinGroup Q))) :
    ∀ x ∈ siegelY F P.e P'.e, A' (spinAction Q s x) = spinAction Q s (A' x) := by
  obtain ⟨q, hq, hc⟩ := imat_commutator_orthSiegelCore hS h hV hW htriv hact hs
  have h1 : A' * spinAction Q s = spinAction Q q * spinAction Q s * A' := by
    calc A' * spinAction Q s
        = (A' * spinAction Q s * A'⁻¹ * (spinAction Q s)⁻¹) * (spinAction Q s * A') := by group
      _ = spinAction Q q * spinAction Q s * A' := by rw [hc]; group
  intro x hx
  have hsY : spinAction Q s (A' x) ∈ siegelY F P.e P'.e :=
    normalizer_siegelRoot_le_stab hS h hs (A' x) (hstabY x hx)
  calc A' (spinAction Q s x) = (A' * spinAction Q s) x := rfl
    _ = (spinAction Q q * spinAction Q s * A') x := by rw [h1]
    _ = spinAction Q q (spinAction Q s (A' x)) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    _ = spinAction Q s (A' x) := orthSiegelCore_fixes_Y h hq (spinAction Q s (A' x)) hsY

private theorem imat_projLin_mem_perp {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} (P : HypPair Q) (x : V) :
    imat_projLin P x ∈ HypPair.perp P := P.proj_mem_perp x

private theorem imat_projLin_equivariant {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {P : HypPair Q} {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hge : g P.e = P.e) (hgf : g P.f = P.f)
    (x : V) : imat_projLin P (g x) = g (imat_projLin P x) := by
  have h1 : polar Q (g x) P.f = polar Q x P.f := by
    rw [← hgf, polar_map_of_mem hg, hgf]
  have h2 : polar Q (g x) P.e = polar Q x P.e := by
    rw [← hge, polar_map_of_mem hg, hge]
  change P.proj (g x) = g (P.proj x)
  rw [HypPair.proj, HypPair.proj, h1, h2, map_sub, map_sub, map_smul, map_smul, hge, hgf]

private theorem imat_pi_perp {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {P P' : HypPair Q} (h : P.Orth P') {y : V}
    (hy : y ∈ HypPair.perp P) :
    (polar Q P.e (imat_projLin P' y) = 0) ∧ (polar Q P.f (imat_projLin P' y) = 0) ∧
      (polar Q P'.e (imat_projLin P' y) = 0) ∧ (polar Q P'.f (imat_projLin P' y) = 0) := by
  have hz : imat_projLin P' y ∈ HypPair.perp P' := imat_projLin_mem_perp P' y
  rw [HypPair.mem_perp] at hz
  have hpe : polar Q P.e y = 0 := (HypPair.mem_perp.mp hy).1
  have hpf : polar Q P.f y = 0 := (HypPair.mem_perp.mp hy).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · change polar Q P.e (P'.proj y) = 0
    rw [HypPair.proj, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      hpe, h.ee, h.ef]
    ring
  · change polar Q P.f (P'.proj y) = 0
    rw [HypPair.proj, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      hpf, h.ff, h.fe]
    ring
  · change polar Q P'.e (P'.proj y) = 0
    exact hz.1
  · change polar Q P'.f (P'.proj y) = 0
    exact hz.2

theorem imat_pi_mem_siegelW {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {P P' : HypPair Q} (h : P.Orth P') (x : V) :
    imat_projLin P' (imat_projLin P x) ∈ siegelW Q P.e P'.e P.f P'.f := by
  have hy : imat_projLin P x ∈ HypPair.perp P := imat_projLin_mem_perp P x
  obtain ⟨h1, h2, h3, h4⟩ := imat_pi_perp h hy
  rw [siegelW, mem_orth_iff]
  intro y hy'
  have hle : Submodule.span F ({P.e, P'.e, P.f, P'.f} : Set V) ≤
      LinearMap.ker (LinearMap.flip (polarBilin Q)
        (imat_projLin P' (imat_projLin P x))) := by
    rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · change (LinearMap.flip (polarBilin Q)
          (imat_projLin P' (imat_projLin P x))) P.e = 0
      exact h1
    · change (LinearMap.flip (polarBilin Q)
          (imat_projLin P' (imat_projLin P x))) P'.e = 0
      exact h3
    · change (LinearMap.flip (polarBilin Q)
          (imat_projLin P' (imat_projLin P x))) P.f = 0
      exact h2
    · change (LinearMap.flip (polarBilin Q)
          (imat_projLin P' (imat_projLin P x))) P'.f = 0
      exact h4
  exact hle hy'

theorem imat_pi_eq_zero_mem_siegelY {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {P P' : HypPair Q} (h : P.Orth P') {x : V}
    (hx : x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (siegelY F P.e P'.e))
    (h0 : imat_projLin P' (imat_projLin P x) = 0) : x ∈ siegelY F P.e P'.e := by
  have hY' : imat_projLin P x ∈ Submodule.span F {P'.e, P'.f} := by
    have hh := HypPair.eq_add_proj P' (imat_projLin P x)
    rw [show P'.proj (imat_projLin P x) = 0 from h0, add_zero] at hh
    rw [hh]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hxsum : x ∈ Submodule.span F ({P.e, P.f} : Set V) ⊔
      Submodule.span F ({P'.e, P'.f} : Set V) := by
    have hz : polar Q x P.f • P.e + polar Q x P.e • P.f ∈
        Submodule.span F ({P.e, P.f} : Set V) :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    rw [HypPair.eq_add_proj P x]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hz) (Submodule.mem_sup_right hY')
  obtain ⟨z, hz, z', hz', hzz'⟩ := Submodule.mem_sup.mp hxsum
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hz'
  have hxe : α • P.e + β • P.f + (γ • P'.e + δ • P'.f) = x := hzz'
  have hβ : β = 0 := by
    have hh := mem_orth_iff.mp hx P.e (Submodule.subset_span (by simp))
    rw [← hxe, polar_add_right, polar_add_right, polar_add_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq, P.polar_ee, P.polar_ef,
      h.ee, h.ef] at hh
    simpa only [mul_zero, mul_one, zero_add, add_zero] using hh
  have hδ : δ = 0 := by
    have hh := mem_orth_iff.mp hx P'.e (Submodule.subset_span (by simp))
    rw [← hxe, polar_add_right, polar_add_right, polar_add_right, polar_smul_right_eq,
      polar_smul_right_eq, polar_smul_right_eq, polar_smul_right_eq, polar_comm Q P'.e P.e,
      polar_comm Q P'.e P.f, h.ee, h.fe, P'.polar_ee, P'.polar_ef] at hh
    simpa only [mul_zero, mul_one, zero_add, add_zero] using hh
  have hx' : x = α • P.e + γ • P'.e := by
    rw [← hxe]
    simp [hβ, hδ]
  rw [hx']
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem imat_pi_equivariant {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {P P' : HypPair Q} {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hge : g P.e = P.e) (hgf : g P.f = P.f)
    (hge' : g P'.e = P'.e) (hgf' : g P'.f = P'.f) (x : V) :
    imat_projLin P' (imat_projLin P (g x)) =
      g (imat_projLin P' (imat_projLin P x)) := by
  rw [imat_projLin_equivariant hg hge hgf x,
    imat_projLin_equivariant (P := P') hg hge' hgf' (imat_projLin P x)]

theorem imat_mem_ker_eq_zero {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {f : V →ₗ[F] V} {x : V} (h : x ∈ LinearMap.ker f) : f x = 0 := by
  simpa only [LinearMap.mem_ker] using h

theorem imat_Q_eq_zero_of_mem_siegelY {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] {Q : QuadraticForm F V} {P P' : HypPair Q} (h : P.Orth P') {x : V}
    (hx : x ∈ siegelY F P.e P'.e) : Q x = 0 := by
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, P.Q_e, P'.Q_e, polar_smul_left_eq,
    polar_smul_right_eq, h.ee]
  ring

theorem imat_mem_comap_apply {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {f : V →ₗ[F] V} {p : Submodule F V} {x : V} (h : x ∈ Submodule.comap f p) : f x ∈ p := by
  simpa only [Submodule.mem_comap] using h

theorem imat_mem_bot_eq_zero {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {x : V} (h : x ∈ (⊥ : Submodule F V)) : x = 0 := by simpa using h

theorem imat_apply_symm_apply {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (e : V ≃ₗ[F] V) (x : V) : e (e⁻¹ x) = x := LinearEquiv.apply_symm_apply e x

theorem imat_symm_apply_apply {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (e : V ≃ₗ[F] V) (x : V) : e⁻¹ (e x) = x := LinearEquiv.symm_apply_apply e x

end CFSG.StandardType.LieKnownR2.POmega.Inner
