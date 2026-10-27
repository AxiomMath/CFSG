module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusFix
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

open Polynomial Module Multiplicative CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType

namespace SpNS

section Intertwine

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}

theorem eq_one_or_eq_neg_one_of_intertwine (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hgd : g ∣ cyclotomic p K) (hpq : p ∣ Nat.card K + 1) (a : ZMod p)
    (θ : AdjoinRoot g →ₗ[K] AdjoinRoot g) (hθ : Function.Injective θ)
    (hθζ : ∀ u, θ (AdjoinRoot.root g * u) = AdjoinRoot.root g ^ a.val * θ u) :
    a = 1 ∨ a = -1 := by
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  set ζ := AdjoinRoot.root g with hζ
  have key : ∀ (P : K[X]) (u : AdjoinRoot g), θ (aeval ζ P * u) = aeval (ζ ^ a.val) P * θ u := by
    intro P
    induction P using Polynomial.induction_on with
    | C c =>
      intro u
      rw [aeval_C, aeval_C, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
    | add P Q hP hQ =>
      intro u
      rw [map_add, map_add, add_mul, add_mul, map_add, hP, hQ]
    | monomial n c ih =>
      intro u
      have e1 : aeval ζ (C c * X ^ (n + 1)) * u = aeval ζ (C c * X ^ n) * (ζ * u) := by
        simp only [map_mul, map_pow, aeval_X, aeval_C, pow_succ]
        ring
      have e2 : aeval (ζ ^ a.val) (C c * X ^ (n + 1)) * θ u =
          aeval (ζ ^ a.val) (C c * X ^ n) * (ζ ^ a.val * θ u) := by
        simp only [map_mul, map_pow, aeval_X, aeval_C, pow_succ]
        ring
      rw [e1, e2, ih, hθζ]
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hθ) 1
  have h1 := key g u
  rw [hζ, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul, map_zero, hu, mul_one] at h1
  exact eq_one_or_eq_neg_one_of_aeval hp hp2 hpK hgd hpq h1.symm

end Intertwine

section Isom

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem ne_two_of_dvd_card_add_one (hpq : p ∣ Nat.card K + 1) : p ≠ 2 := by
  rintro rfl
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn] at hpq
  have h2 : 2 ∣ 2 ^ (n : ℕ) := dvd_pow_self 2 n.ne_zero
  have := (Nat.dvd_add_right h2).mp hpq
  omega

theorem torusSignedEltSC_isom (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    (hAlt : B.IsAlt) (hnd : B.Nondegenerate) : GGTorusSignedEltSC p ↥(sesqUnitaryGroup B) := by
  classical
  intro E hE h3 hsc
  have hp2 : p ≠ 2 := ne_two_of_dvd_card_add_one hpq
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpK : (p : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  have hne : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p _),
      natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have hζo := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  set ζ := AdjoinRoot.root g with hζdef
  have hζp : ζ ^ p = 1 := hζo.pow_eq_one
  set S : Set (Module.End K V) :=
    {x | ∃ e ∈ E, (((e : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) = x} with hS
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have h1 := TableB.IsElemAbelian.comm hE he he'
    have h2 := congrArg (fun y : ↥(sesqUnitaryGroup B) =>
      ((y : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) h1
    simp only [Subgroup.coe_mul, Units.val_mul] at h2
    exact h2
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := hE.2 e he
    have h2 := congrArg (fun y : ↥(sesqUnitaryGroup B) =>
      ((y : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) h1
    simpa using h2
  have hSB : ∀ x ∈ S, ∀ u w, B (x u) (x w) = B u w := by
    rintro _ ⟨e, -, rfl⟩ u w
    exact mem_sesqUnitaryGroup.mp e.2 u w
  obtain ⟨s, κ, _, Φ, β, hβ, hact, hdec⟩ := exists_nframe hp hp2 hpK hgd
    (rootPB_dim_eq_two hp hp2 hpK hgd hpq) (aeval_root_pow_pred hp hpK hgd hpq) hAlt hnd S hSc hSp
    hSB
  set b : Basis (Fin 2) K (AdjoinRoot g) :=
    (CoordSL.rootPB g).basis.reindex (finCongr (rootPB_dim_eq_two hp hp2 hpK hgd hpq)) with hb
  have hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v := fun u v => by
    have h1 := bilin_apply_det b hβ (Algebra.lmul K (AdjoinRoot g) ζ) u v
    rw [← Algebra.norm_apply, norm_root_eq_one hp hp2 hpK hgd hpq, one_mul] at h1
    exact h1
  set τ := torHom (K := K) hζp hdec hζβ with hτ
  have hτinj : Function.Injective τ := torHom_injective hζp hdec hζβ hζo
  have hτapp : ∀ f x, (((τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) (Φ x) = Φ (torEquiv hζp f x) := fun f x => frameUnit_apply Φ _ x
  have hEτ : ∀ e ∈ E, ∃ f, τ f = e := by
    intro e he
    obtain ⟨k, hk⟩ := hact _ ⟨e, he, rfl⟩
    refine ⟨fun i => ofAdd (k i : ZMod p), Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))⟩
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [hτapp, torEquiv_apply, hk]
    congr 2
    funext i
    rw [toAdd_ofAdd, ZMod.val_natCast, ← pow_eq_pow_mod _ hζp]
  have hτE : ∀ f, τ f ∈ E := by
    intro f
    refine hsc _ (fun e he => ?_) ?_
    · obtain ⟨f', rfl⟩ := hEτ e he
      rw [← map_mul, ← map_mul, mul_comm]
    · rw [← map_pow]
      convert map_one τ
      funext i
      rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (f i ^ p), toAdd_pow, nsmul_eq_mul,
        ZMod.natCast_self, zero_mul, ofAdd_zero]
  refine ⟨s, τ.comp (MonoidHom.id _), hτinj, ?_, fun i => ?_, fun σ => ?_, fun h hh => ?_⟩
  · ext e
    constructor
    · rintro ⟨f, rfl⟩
      exact hτE f
    · intro he
      obtain ⟨f, hf⟩ := hEτ e he
      exact ⟨f, hf⟩
  ·
    have : Fintype K := Fintype.ofFinite K
    have hσβ : ∀ u v, β (frobL K g u) (frobL K g v) = β u v := fun u v => by
      have h1 := bilin_apply_det b hβ (frobL K g : AdjoinRoot g →ₗ[K] AdjoinRoot g) u v
      rw [det_frobL hp hp2 hpK hgd hpq, one_mul] at h1
      exact h1
    exact torHom_sgn hζp hdec hζβ (frobL_root_mul hp hpK hgd hpq) hσβ i
  · exact torHom_perm hζp hdec hζβ σ
  ·
    have hh' : ∀ f, ∃ f', h * τ f * h⁻¹ = τ f' := fun f => hEτ _ (hh _ (hτE f)) |>.imp
      fun f' hf' => hf'.symm
    exact torHom_normalizer hζp hp hdec hζβ hζo
      (fun a θ hθ hθζ => eq_one_or_eq_neg_one_of_intertwine hp hp2 hpK hgd hpq a θ hθ hθζ) h hh'

end Isom

end SpNS

section Transport

theorem ggTorusSignedEltSC_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGTorusSignedEltSC p R') : GGTorusSignedEltSC p R := by
  intro E hE h3 hsc
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hmem : ∀ x : R, e x ∈ E.map e.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hsc' : ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [hmem]
    refine hsc y (fun x hx => e.injective ?_) ?_
    · rw [map_mul, map_mul]
      exact hg _ ((hmem x).mpr hx)
    · apply e.injective
      rw [map_pow, hgp, map_one]
  obtain ⟨k, τ, hτinj, hτE, hsgn, hperm, hnorm⟩ :=
    h (E.map e.toMonoidHom) (TableB.isElemAbelian_map hE _) (hcard ▸ h3) hsc'
  have hconj : ∀ (w : R') (f f' : Fin k → Multiplicative (ZMod p)),
      w * τ f * w⁻¹ = τ f' → e.symm w * e.symm (τ f) * (e.symm w)⁻¹ = e.symm (τ f') := by
    intro w f f' h
    rw [← map_inv, ← map_mul, ← map_mul, h]
  refine ⟨k, e.symm.toMonoidHom.comp τ, e.symm.injective.comp hτinj, ?_, fun i => ?_,
    fun σ => ?_, fun g hg => ?_⟩
  · ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      have : τ f ∈ τ.range := ⟨f, rfl⟩
      rw [hτE] at this
      rw [← hmem]
      simpa using this
    · intro hx
      have : e x ∈ τ.range := hτE ▸ (hmem x).mpr hx
      obtain ⟨f, hf⟩ := this
      exact ⟨f, by simp [hf]⟩
  · obtain ⟨w, hw⟩ := hsgn i
    exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩
  · obtain ⟨w, hw⟩ := hperm σ
    exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩
  · have hg' : ∀ x ∈ E.map e.toMonoidHom, e g * x * (e g)⁻¹ ∈ E.map e.toMonoidHom := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨g * y * g⁻¹, hg y hy, ?_⟩
      simp
    obtain ⟨π, ε, hε, hrel⟩ := hnorm (e g) hg'
    refine ⟨π, ε, hε, fun f f' hff' => hrel f f' ?_⟩
    apply e.symm.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact hff'

end Transport

section Input

open CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem ggSpNonsplitSignedEltInput_holds : GGSpNonsplitSignedEltInput := by
  intro K _ _ _ m p hm hp hpq
  have : NeZero m := ⟨by omega⟩
  have hinj : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  set e₁ : ↥(LargeEvenSpGroup K m) ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K m))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩ with he₁
  set e₂ : ↥(StatedSp m K) ≃*
      ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm m K)) :=
    (MonoidHom.ofInjective CFSG.RankThree.Classical.spLin_injective).trans
      (MulEquiv.subgroupCongr CFSG.RankThree.Classical.range_spLin) with he₂
  have hLS : LargeEvenSpGroup K m = StatedSp m K := rfl
  exact ggTorusSignedEltSC_of_mulEquiv
    (e₁.symm.trans ((MulEquiv.subgroupCongr hLS).trans e₂))
    (SpNS.torusSignedEltSC_isom hp hpq CFSG.RankThree.Classical.spForm_isAlt
      CFSG.RankThree.Classical.spForm_nondegenerate)

theorem ggSpNonsplitTorusInput_holds :
    GGSpNonsplitTorusInput :=
  ggSpNonsplitTorusInput_of_signedEltSC ggSpNonsplitSignedEltInput_holds

theorem ggCorFiveTwentyWeylInputsOn_spNonsplit :
    GGWeylPseudoReflGenInputOn GGSpNonsplitLabel ∧
      GGWeylCentralizerScalarInputOn GGSpNonsplitLabel ∧
      GGCorFiveTwentyOuterInputOn GGSpNonsplitLabel :=
  ggCorFiveTwentyWeylInputsOn_spNonsplit_of_input ggSpNonsplitTorusInput_holds

end Input

end CFSG.StandardType
