module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallBlock

public section

namespace CFSG.StandardType

namespace SevOmSmall

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal SevOm

section General

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def RestrClosed (Q : QuadraticForm K V) (A : Subgroup (V ≃ₗ[K] V)) : Prop :=
  ∀ W : Submodule K V, (∀ w ∈ W, (∀ v ∈ W, QuadraticMap.polar Q v w = 0) → w = 0) →
    (∀ c ∈ A, ∀ w ∈ W, c w ∈ W) → ∀ c ∈ A, ∃ g ∈ A, (∀ w ∈ W, g w = c w) ∧
      ∀ v, (∀ w ∈ W, QuadraticMap.polar Q w v = 0) → g v = v

theorem isCompl_orthogonal [FiniteDimensional K V] {W : Submodule K V}
    (hW : ∀ w ∈ W, (∀ v ∈ W, QuadraticMap.polar Q v w = 0) → w = 0) :
    IsCompl W (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W) := by
  refine (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint fun x y hxy => ?_).mpr ?_
  · rw [QuadraticMap.polarBilin_apply_apply] at hxy ⊢
    rw [QuadraticMap.polar_comm]
    exact hxy
  · rw [Submodule.disjoint_def]
    intro w hw hw'
    exact hW w hw fun v hv => LinearMap.BilinForm.mem_orthogonal_iff.mp hw' v hv

theorem mem_orthogonal_polar {W : Submodule K V} {v : V} :
    v ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W ↔
      ∀ w ∈ W, QuadraticMap.polar Q w v = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff

theorem aeval_mem_of_mapsTo {x : Module.End K V} {U : Submodule K V} (hU : ∀ u ∈ U, x u ∈ U)
    (f : K[X]) {u : V} (hu : u ∈ U) : aeval x f u ∈ U := by
  have hpow : ∀ n : ℕ, (x ^ n) u ∈ U := by
    intro n
    induction n with
    | zero => simpa using hu
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hU _ ih
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, LinearMap.add_apply]
    exact U.add_mem hf hg
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact U.smul_mem c (hpow n)

theorem aeval_apply_of_fixed {x : Module.End K V} {u : V} (hu : x u = u) (f : K[X]) :
    aeval x f u = f.eval 1 • u := by
  have hpow : ∀ n : ℕ, (x ^ n) u = u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, hu]
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, LinearMap.add_apply, hf, hg, eval_add, add_smul]
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, eval_monomial,
      one_pow, mul_one]

theorem pow_apply_eq (b : V ≃ₗ[K] V) (N : ℕ) (v : V) : (b ^ N) v = (b.toLinearMap ^ N) v := by
  induction N generalizing v with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ, LinearEquiv.mul_apply, pow_succ, Module.End.mul_apply, ih]
    rfl

end General

section Pieces

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

theorem Frame.eq_of_le (F : Frame Q p A r) [Fact p.Prime] (hR : RestrClosed Q A) {i : Fin r}
    {W : Submodule K V} (hWi : W ≤ F.U i) (hW0 : W ≠ ⊥)
    (hWnd : ∀ w ∈ W, (∀ v ∈ W, QuadraticMap.polar Q v w = 0) → w = 0)
    (hWA : ∀ c ∈ A, ∀ w ∈ W, c w ∈ W) : W = F.U i := by
  classical
  have hδ : toAdd (ofAdd (Pi.single i (1 : ZMod p)) : Multiplicative (Fin r → ZMod p)) i ≠ 0 := by
    rw [toAdd_ofAdd, Pi.single_eq_same]
    exact one_ne_zero
  obtain ⟨g, hgA, hgW, hgperp⟩ := hR W hWnd hWA _ (F.mem (ofAdd (Pi.single i 1)))
  obtain ⟨t, rfl⟩ := F.exists_eq hgA
  obtain ⟨w₀, hw₀, hw₀0⟩ := (Submodule.ne_bot_iff W).mp hW0
  have hti : toAdd t i ≠ 0 := by
    intro h0
    refine hw₀0 (F.fpf _ i hδ w₀ (hWi hw₀) ?_)
    rw [← hgW w₀ hw₀]
    exact F.triv t i h0 w₀ (hWi hw₀)
  refine le_antisymm hWi fun v hv => ?_
  obtain ⟨w, hw, w', hw', hww⟩ := exists_add_of_isCompl (isCompl_orthogonal hWnd) v
  have hw'U : w' ∈ F.U i := by
    have : w' = v - w := by rw [← hww]; abel
    rw [this]
    exact (F.U i).sub_mem hv (hWi hw)
  have hw'0 : w' = 0 := F.fpf t i hti w' hw'U (hgperp w' (mem_orthogonal_polar.mp hw'))
  rw [← hww, hw'0, add_zero]
  exact hw

omit [FiniteDimensional K V] in
theorem Frame.commute (F : Frame Q p A r) {c c' : V ≃ₗ[K] V} (hc : c ∈ A) (hc' : c' ∈ A) :
    Commute c.toLinearMap c'.toLinearMap := by
  obtain ⟨t, rfl⟩ := F.exists_eq hc
  obtain ⟨t', rfl⟩ := F.exists_eq hc'
  refine LinearMap.ext fun v => ?_
  change (F.ι t) ((F.ι t') v) = (F.ι t') ((F.ι t) v)
  rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, mul_comm]

omit [FiniteDimensional K V] in
theorem Frame.card_le_of_coords (F : Frame Q p A r) [Fact p.Prime] {H : Subgroup (V ≃ₗ[K] V)}
    (hHA : H ≤ A) (j k : Fin r)
    (hH : ∀ s, F.ι s ∈ H → toAdd s j = 0 → toAdd s k = 0 → s = 1) : Nat.card H ≤ p ^ 2 := by
  classical
  have hex : ∀ c : H, ∃ s, F.ι s = c := fun c => F.exists_eq (hHA c.2)
  choose σ hσ using hex
  let f : H → ZMod p × ZMod p := fun c => (toAdd (σ c) j, toAdd (σ c) k)
  have hf : Function.Injective f := by
    intro c c' hcc
    have h1 : toAdd (σ c) j = toAdd (σ c') j := congrArg Prod.fst hcc
    have h2 : toAdd (σ c) k = toAdd (σ c') k := congrArg Prod.snd hcc
    have hmem : F.ι ((σ c)⁻¹ * σ c') ∈ H := by
      rw [map_mul, map_inv, hσ, hσ]
      exact H.mul_mem (H.inv_mem c.2) c'.2
    have h3 := hH _ hmem (by rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, h1,
      neg_add_cancel]) (by rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, h2,
      neg_add_cancel])
    have hs : σ c = σ c' := by
      rw [← mul_one (σ c), ← h3, ← mul_assoc, mul_inv_cancel, one_mul]
    apply Subtype.ext
    rw [← hσ c, ← hσ c', hs]
  calc Nat.card H ≤ Nat.card (ZMod p × ZMod p) := Nat.card_le_card_of_injective f hf
    _ = p ^ 2 := by rw [Nat.card_prod, Nat.card_zmod, sq]

theorem Frame.le_or_le (F : Frame Q p A r) [Fact p.Prime] (hR : RestrClosed Q A)
    {s₀ : Multiplicative (Fin r → ZMod p)} (hx : OddOrderIsometry Q p (F.ι s₀)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s₀).toLinearMap) (hself : reciprocalPolynomial h = h)
    (i : Fin r) :
    F.U i ≤ primaryComponent (F.ι s₀).toLinearMap h ∨
      F.U i ≤ othersSpace (F.ι s₀).toLinearMap h := by
  classical
  set b := F.ι s₀ with hb
  set π := primaryProjection b.toLinearMap h with hπ
  have hsq := hx.squarefree_minpoly
  have hπU : ∀ u ∈ F.U i, π u ∈ F.U i := fun u hu =>
    aeval_mem_of_mapsTo (fun v hv => F.mapsTo s₀ i v hv) _ hu
  have hπV : ∀ u, π u ∈ primaryComponent b.toLinearMap h := primaryProjection_mem hsq hh
  have hrest : ∀ u, u - π u ∈ othersSpace b.toLinearMap h := by
    intro u
    have hsum := LinearMap.congr_fun (sum_primaryProjection hsq) u
    rw [LinearMap.sum_apply, Module.End.one_apply, ← Finset.add_sum_erase _ _ hh] at hsum
    rw [← eq_sub_of_add_eq' hsum]
    refine Submodule.sum_mem _ fun a ha => ?_
    obtain ⟨hah, haF⟩ := Finset.mem_erase.mp ha
    exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem
      ⟨haF, hah, by rw [hself]; exact hah⟩ (primaryProjection_mem hsq haF u))
  by_cases hW : F.U i ⊓ primaryComponent b.toLinearMap h = ⊥
  · right
    intro u hu
    have h0 : π u = 0 := by
      have h1 : π u ∈ F.U i ⊓ primaryComponent b.toLinearMap h := ⟨hπU u hu, hπV u⟩
      rw [hW] at h1
      exact (Submodule.mem_bot K).mp h1
    have h2 := hrest u
    rwa [h0, sub_zero] at h2
  · left
    have heq := Frame.eq_of_le F hR (inf_le_left : F.U i ⊓ primaryComponent b.toLinearMap h ≤ F.U i)
      hW (fun w hw hw0 => F.nondeg i w hw.1 fun v hv => by
        have h1 : QuadraticMap.polar Q (π v) w = 0 := hw0 _ ⟨hπU v hv, hπV v⟩
        have h2 : QuadraticMap.polar Q (v - π v) w = 0 := by
          rw [QuadraticMap.polar_comm]
          exact hx.polar_orbit_others hh (Submodule.mem_sup_left hw.2) (hrest v)
        have h3 : v = π v + (v - π v) := by abel
        rw [h3, QuadraticMap.polar_add_left, h1, h2, add_zero])
      (fun c hc w hw => ⟨by obtain ⟨t, rfl⟩ := F.exists_eq hc; exact F.mapsTo t i w hw.1,
        apply_mem_primaryComponent (Frame.commute F hc (F.mem s₀)) hw.2⟩)
    rw [← heq]
    exact inf_le_right

theorem Frame.exists_line [Finite K] [CharP K 2] (F : Frame Q p A r) [Fact p.Prime]
    (hR : RestrClosed Q A) {s₀ : Multiplicative (Fin r → ZMod p)}
    (hx : OddOrderIsometry Q p (F.ι s₀)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s₀).toLinearMap) (hne1 : h ≠ X - 1) {j : Fin r}
    (hj : F.U j ≤ primaryComponent (F.ι s₀).toLinearMap h) :
    ∃ u : primaryComponent (F.ι s₀).toLinearMap h, u ≠ 0 ∧ ∀ v ∈ F.U j,
      ∃ z : AdjoinRoot h, ((z • u : primaryComponent (F.ι s₀).toLinearMap h) : V) = v := by
  classical
  set b := F.ι s₀ with hb
  set Vh := primaryComponent b.toLinearMap h with hVh
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hbU : ∀ v ∈ F.U j, b.toLinearMap v ∈ F.U j := fun v hv => F.mapsTo s₀ j v hv
  have hsj : toAdd s₀ j ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot j)
    have h1 : aeval b.toLinearMap h u = h.eval 1 • u :=
      aeval_apply_of_fixed (F.triv s₀ j h0 u hu) h
    rw [mem_primaryComponent.mp (hj hu)] at h1
    have h3 : h.eval 1 = 0 := by
      rcases smul_eq_zero.mp h1.symm with h4 | h4
      · exact h4
      · exact absurd h4 hu0
    have h4 : X - C 1 ∣ h := Polynomial.dvd_iff_isRoot.mpr h3
    have h5 := (Polynomial.irreducible_X_sub_C (1 : K)).associated_of_dvd hirr h4
    exact hne1 ((eq_of_monic_of_associated hmon (monic_X_sub_C 1) h5.symm).trans (by rw [C_1]))
  obtain ⟨u₀, hu₀U, hQu₀⟩ : ∃ u₀ ∈ F.U j, Q u₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot j)
    exact hu0 (F.nondeg j u hu fun v hv => by
      rw [QuadraticMap.polar, hall _ ((F.U j).add_mem hv hu), hall v hv, hall u hu, sub_zero,
        sub_zero])
  have hu₀0 : u₀ ≠ 0 := fun h0 => hQu₀ (by rw [h0, map_zero])
  set u' : Vh := ⟨u₀, hj hu₀U⟩ with hu'
  set W : Submodule K V :=
    ((Submodule.span (AdjoinRoot h) {u'}).restrictScalars K).map Vh.subtype with hWdef
  have hWmem : ∀ v, v ∈ W ↔ ∃ z : AdjoinRoot h, ((z • u' : Vh) : V) = v := by
    intro v
    simp only [hWdef, Submodule.mem_map, Submodule.restrictScalars_mem,
      Submodule.mem_span_singleton, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨_, ⟨z, rfl⟩, rfl⟩
  have hWU : W ≤ F.U j := by
    intro v hv
    obtain ⟨z, rfl⟩ := (hWmem v).mp hv
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [coe_mk_smul_primaryComponent]
    exact aeval_mem_of_mapsTo hbU f hu₀U
  have hpowb : ∀ c ∈ A, ∃ N : ℕ, ∀ v ∈ F.U j, c v = (b ^ N) v := by
    intro c hc
    obtain ⟨t, rfl⟩ := F.exists_eq hc
    refine ⟨((toAdd s₀ j)⁻¹ * toAdd t j).val, fun v hv => ?_⟩
    have hcoord : toAdd (t⁻¹ * s₀ ^ ((toAdd s₀ j)⁻¹ * toAdd t j).val) j = 0 := by
      rw [toAdd_mul, toAdd_inv, toAdd_pow, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
        nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm ((toAdd s₀ j)⁻¹) (toAdd t j), mul_assoc,
        inv_mul_cancel₀ hsj, mul_one, neg_add_cancel]
    have h1 := F.triv _ j hcoord v hv
    rw [map_mul, map_inv, map_pow, LinearEquiv.mul_apply] at h1
    have h2 := congrArg (F.ι t) h1
    rw [← LinearEquiv.mul_apply, mul_inv_cancel] at h2
    exact h2.symm
  have hWA : ∀ c ∈ A, ∀ w ∈ W, c w ∈ W := by
    intro c hc w hw
    obtain ⟨z, rfl⟩ := (hWmem w).mp hw
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
    obtain ⟨N, hN⟩ := hpowb c hc
    refine (hWmem _).mpr ⟨AdjoinRoot.mk h (f * X ^ N), ?_⟩
    rw [coe_mk_smul_primaryComponent, coe_mk_smul_primaryComponent]
    have h1 : c (aeval b.toLinearMap f u₀) = aeval b.toLinearMap f (c u₀) :=
      LinearMap.congr_fun (commute_aeval (Frame.commute F hc (F.mem s₀)) f).eq u₀
    change aeval b.toLinearMap (f * X ^ N) u₀ = c (aeval b.toLinearMap f u₀)
    rw [h1, hN u₀ hu₀U, pow_apply_eq, map_mul, Module.End.mul_apply, aeval_X_pow]
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hroot0 : AdjoinRoot.root h ≠ 0 := fun h0 => by
    rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at hlamp
    exact zero_ne_one hlamp
  have hbroot : ∀ v : Vh, b (v : V) = ((AdjoinRoot.root h • v : Vh) : V) := fun v =>
    (coe_root_smul_primaryComponent b.toLinearMap h v).symm
  have hbW : ∀ w ∈ W, b w ∈ W := by
    intro w hw
    obtain ⟨z, rfl⟩ := (hWmem w).mp hw
    exact (hWmem _).mpr ⟨AdjoinRoot.root h * z, by rw [mul_smul, hbroot]⟩
  have hbsW : ∀ w ∈ W, b.symm w ∈ W := by
    intro w hw
    obtain ⟨z, rfl⟩ := (hWmem w).mp hw
    refine (hWmem _).mpr ⟨(AdjoinRoot.root h)⁻¹ * z, b.injective ?_⟩
    rw [LinearEquiv.apply_symm_apply, hbroot, mul_smul, smul_inv_smul₀ hroot0]
  set Rd : Submodule K V := W ⊓ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W
    with hRd
  have hRb : ∀ w ∈ Rd, b.toLinearMap w ∈ Rd := by
    intro w hw
    refine ⟨hbW w hw.1, mem_orthogonal_polar.mpr fun v hv => ?_⟩
    change QuadraticMap.polar Q v (b w) = 0
    rw [← hx.polar_symm_apply]
    exact mem_orthogonal_polar.mp hw.2 _ (hbsW v hv)
  have h1root : (1 + AdjoinRoot.root h : AdjoinRoot h) ≠ 0 := by
    intro h0
    have h2 : (2 : AdjoinRoot h) = 0 := by
      have := congrArg (algebraMap K (AdjoinRoot h)) (CharTwo.two_eq_zero (R := K))
      rwa [map_ofNat, map_zero] at this
    exact root_ne_one hmon hne1 (by linear_combination h0 - h2)
  have hWnd : ∀ w ∈ W, (∀ v ∈ W, QuadraticMap.polar Q v w = 0) → w = 0 := by
    intro w hw hw0
    by_contra hne
    obtain ⟨z, rfl⟩ := (hWmem w).mp hw
    have hz : z ≠ 0 := fun h0 => hne (by rw [h0, zero_smul, Submodule.coe_zero])
    have hwR : ((z • u' : Vh) : V) ∈ Rd := ⟨hw, mem_orthogonal_polar.mpr hw0⟩
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective z⁻¹
    have hu₀R : u₀ ∈ Rd := by
      have h1 := aeval_mem_of_mapsTo hRb g hwR
      rwa [← coe_mk_smul_primaryComponent, hg, smul_smul, inv_mul_cancel₀ hz, one_smul] at h1
    have hWR : ∀ v ∈ W, v ∈ Rd := by
      intro v hv
      obtain ⟨y, rfl⟩ := (hWmem v).mp hv
      obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective y
      rw [coe_mk_smul_primaryComponent]
      exact aeval_mem_of_mapsTo hRb f hu₀R
    have hv₁W : (((1 + AdjoinRoot.root h)⁻¹ • u' : Vh) : V) ∈ W := (hWmem _).mpr ⟨_, rfl⟩
    have hsum : (((1 + AdjoinRoot.root h)⁻¹ • u' : Vh) : V) +
        b (((1 + AdjoinRoot.root h)⁻¹ • u' : Vh) : V) = u₀ := by
      have e1 : (1 + AdjoinRoot.root h) • ((1 + AdjoinRoot.root h)⁻¹ • u') = u' := by
        rw [smul_smul, mul_inv_cancel₀ h1root, one_smul]
      have e2 : (1 + AdjoinRoot.root h)⁻¹ • u' +
          AdjoinRoot.root h • ((1 + AdjoinRoot.root h)⁻¹ • u') = u' := by
        have h3 := add_smul (1 : AdjoinRoot h) (AdjoinRoot.root h)
          ((1 + AdjoinRoot.root h)⁻¹ • u')
        rw [one_smul, e1] at h3
        exact h3.symm
      rw [hbroot, ← Submodule.coe_add, e2]
    have hpol : QuadraticMap.polar Q (((1 + AdjoinRoot.root h)⁻¹ • u' : Vh) : V)
        (b (((1 + AdjoinRoot.root h)⁻¹ • u' : Vh) : V)) = 0 :=
      mem_orthogonal_polar.mp (hWR _ (hbW _ hv₁W)).2 _ hv₁W
    have hQb : Q (b (((1 + AdjoinRoot.root h)⁻¹ • u' : Vh) : V)) =
        Q (((1 + AdjoinRoot.root h)⁻¹ • u' : Vh) : V) :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem _
    apply hQu₀
    rw [← hsum]
    have h3 : ∀ y y' : V, Q (y + y') = QuadraticMap.polar Q y y' + Q y + Q y' := fun y y' => by
      rw [QuadraticMap.polar]
      ring
    rw [h3, hpol, hQb, zero_add, CharTwo.add_self_eq_zero]
  have hu₀W : u₀ ∈ W := (hWmem u₀).mpr ⟨1, by rw [one_smul]⟩
  have hW0 : W ≠ ⊥ := fun h0 => hu₀0 (by rw [h0] at hu₀W; exact (Submodule.mem_bot K).mp hu₀W)
  have heq := Frame.eq_of_le F hR hWU hW0 hWnd hWA
  refine ⟨u', fun h0 => hu₀0 (congrArg Subtype.val h0), fun v hv => ?_⟩
  rw [← heq] at hv
  exact (hWmem v).mp hv

end Pieces

end SevOmSmall

end CFSG.StandardType
