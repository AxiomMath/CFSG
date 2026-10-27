module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsFrame

public section

open Polynomial Module Multiplicative Matrix
open scoped commutatorElement

namespace CFSG.StandardType

namespace OrthNs

open CFSG.Assembly SpNS NbrOrth SpCoord CFSG.LocalAnalysis.ComponentInitial

section Forms

variable {K : Type} [Field K] {L : Type} [Field L]

theorem eq_of_add_of_mul {ζ : L} (hζ : ζ ≠ 1) {q₁ q₂ : L → K} {β : L → L → K}
    (h₁ : ∀ u v, q₁ (u + v) = q₁ u + q₁ v + β u v) (h₂ : ∀ u v, q₂ (u + v) = q₂ u + q₂ v + β u v)
    (hζ₁ : ∀ u, q₁ (ζ * u) = q₁ u) (hζ₂ : ∀ u, q₂ (ζ * u) = q₂ u) : q₁ = q₂ := by
  funext v
  have h := eq_zero_of_add_of_mul hζ (D := fun u => q₁ u - q₂ u)
    (fun u w => by
      show q₁ (u + w) - q₂ (u + w) = (q₁ u - q₂ u) + (q₁ w - q₂ w)
      rw [h₁, h₂]; ring)
    (fun u => by
      show q₁ (ζ * u) - q₂ (ζ * u) = q₁ u - q₂ u
      rw [hζ₁, hζ₂]) v
  exact sub_eq_zero.mp h

end Forms

section Lin

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable abbrev glin (g : GL ι K) : Module.End K (ι → K) :=
  Matrix.toLinAlgEquiv' (g : Matrix ι ι K)

theorem glin_apply (g : GL ι K) (v : ι → K) : glin g v = (g : Matrix ι ι K) *ᵥ v :=
  Matrix.toLinAlgEquiv'_apply _ _

theorem glin_mul (g g' : GL ι K) : glin (g * g') = glin g * glin g' := by
  rw [glin, Units.val_mul, map_mul]

theorem glin_pow (g : GL ι K) (k : ℕ) : glin (g ^ k) = glin g ^ k := by
  rw [glin, Units.val_pow_eq_pow_val, map_pow]

theorem glin_one : glin (1 : GL ι K) = 1 := by
  rw [glin, Units.val_one, map_one]

theorem eq_of_glin {g g' : GL ι K} (h : ∀ v, glin g v = glin g' v) : g = g' :=
  Units.ext (Matrix.toLinAlgEquiv'.injective (LinearMap.ext h))

end Lin

section Comm

theorem conj_commutator_eq {G V : Type*} [Group G] (τ : V → G) {F P : G} {α α' β β' : V → V}
    (hF : ∀ f, F * τ f * F⁻¹ = τ (α f)) (hα : ∀ f, α (α' f) = f)
    (hP : ∀ f, P * τ f * P⁻¹ = τ (β f)) (hβ : ∀ f, β (β' f) = f) (f : V) :
    ⁅F, P⁆ * τ f * ⁅F, P⁆⁻¹ = τ (α (β (α' (β' f)))) := by
  have hF' : ∀ f, F⁻¹ * τ f * F = τ (α' f) := fun f => by
    calc F⁻¹ * τ f * F = F⁻¹ * τ (α (α' f)) * F := by rw [hα]
      _ = F⁻¹ * (F * τ (α' f) * F⁻¹) * F := by rw [hF]
      _ = τ (α' f) := by group
  have hP' : ∀ f, P⁻¹ * τ f * P = τ (β' f) := fun f => by
    calc P⁻¹ * τ f * P = P⁻¹ * τ (β (β' f)) * P := by rw [hβ]
      _ = P⁻¹ * (P * τ (β' f) * P⁻¹) * P := by rw [hP]
      _ = τ (β' f) := by group
  rw [commutatorElement_def]
  calc F * P * F⁻¹ * P⁻¹ * τ f * (F * P * F⁻¹ * P⁻¹)⁻¹
      = F * (P * (F⁻¹ * (P⁻¹ * τ f * P) * F) * P⁻¹) * F⁻¹ := by group
    _ = τ (α (β (α' (β' f)))) := by rw [hP', hF', hP, hF]

variable {p m : ℕ}

theorem sgnAut_sgnAut (i : Fin m) (f : Fin m → Multiplicative (ZMod p)) :
    sgnAut i (sgnAut i f) = f := by
  funext j
  rw [sgnAut_apply, sgnAut_apply]
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

theorem permAut_comp_self (σ : Equiv.Perm (Fin m)) (f : Fin m → Multiplicative (ZMod p)) :
    permAut σ (f ∘ ⇑σ) = f := by
  funext j
  simp [permAut_apply]

theorem sgnAut_permAut_swap {a b : Fin m} (hab : a ≠ b) (f : Fin m → Multiplicative (ZMod p)) :
    sgnAut a (permAut (Equiv.swap a b) (sgnAut a (f ∘ ⇑(Equiv.swap a b)))) = dinv a b f := by
  funext j
  rw [dinv_apply_eq]
  simp only [hab, ↓reduceIte, sgnAut_apply, permAut_apply, Equiv.swap_inv, Function.comp_apply,
    Function.update_apply]
  by_cases hja : j = a
  · rw [hja]
    simp [Equiv.swap_apply_left, hab, Ne.symm hab]
  · by_cases hjb : j = b
    · rw [hjb]
      simp [Equiv.swap_apply_right, Ne.symm hab]
    · simp [hja, hjb, Equiv.swap_apply_of_ne_of_ne hja hjb]

theorem permAut_comm_eq (s₁ s₂ : Equiv.Perm (Fin m)) (f : Fin m → Multiplicative (ZMod p)) :
    permAut s₁ (permAut s₂ ((f ∘ ⇑s₂) ∘ ⇑s₁)) = f ∘ ⇑(s₁ * s₂ * s₁⁻¹ * s₂⁻¹)⁻¹ := by
  funext x
  simp [permAut_apply, _root_.mul_inv_rev]

end Comm

section Omega

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {p : ℕ}

theorem torusEvenSignedEltSC_omega (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    (QF : QuadraticForm K (ι → K)) (hnd : (QuadraticMap.polarBilin QF).Nondegenerate) :
    GGTorusEvenSignedEltSC p ↥(LargeEvenOmega ⇑QF) := by
  classical
  intro E hE h3 hsc
  have hp2 : p ≠ 2 := ne_two_of_dvd_card_add_one hpq
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fintype K := Fintype.ofFinite K
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
  have hζ1 : ζ ≠ 1 := hζo.ne_one hp.one_lt
  set B := QuadraticMap.polarBilin QF with hBdef
  have hAlt : B.IsAlt := fun x => by
    rw [hBdef, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  have hiso : ∀ (x : ↥(LargeEvenOmega ⇑QF)) v, QF (glin (x : GL ι K) v) = QF v := fun x v => by
    rw [glin_apply]
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ x.2) v
  set S : Set (Module.End K (ι → K)) :=
    (fun x : ↥(LargeEvenOmega ⇑QF) => glin (x : GL ι K)) '' (E : Set ↥(LargeEvenOmega ⇑QF))
    with hS
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have h1 := TableB.IsElemAbelian.comm hE he he'
    show glin (e : GL ι K) * glin (e' : GL ι K) = glin (e' : GL ι K) * glin (e : GL ι K)
    rw [← glin_mul, ← glin_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, h1]
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨e, he, rfl⟩
    show glin (e : GL ι K) ^ p = 1
    rw [← glin_pow, ← Subgroup.coe_pow, hE.2 e he, Subgroup.coe_one, glin_one]
  have hSB : ∀ x ∈ S, ∀ u w, B (x u) (x w) = B u w := by
    rintro _ ⟨e, -, rfl⟩ u w
    simp only [hBdef, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    rw [← map_add, hiso, hiso, hiso]
  obtain ⟨s, κ, _, Φ, β, hβ, hact, hdec⟩ := exists_nframe hp hp2 hpK hgd
    (rootPB_dim_eq_two hp hp2 hpK hgd hpq) (aeval_root_pow_pred hp hpK hgd hpq) hAlt hnd S hSc
    hSp hSB
  set b : Basis (Fin 2) K (AdjoinRoot g) :=
    (CoordSL.rootPB g).basis.reindex (finCongr (rootPB_dim_eq_two hp hp2 hpK hgd hpq)) with hb
  have hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v := fun u v => by
    have h1 := bilin_apply_det b hβ (Algebra.lmul K (AdjoinRoot g) ζ) u v
    rw [← Algebra.norm_apply, norm_root_eq_one hp hp2 hpK hgd hpq, one_mul] at h1
    exact h1
  have hσβ : ∀ u v, β (frobL K g u) (frobL K g v) = β u v := fun u v => by
    have h1 := bilin_apply_det b hβ (frobL K g : AdjoinRoot g →ₗ[K] AdjoinRoot g) u v
    rw [det_frobL hp hp2 hpK hgd hpq, one_mul] at h1
    exact h1
  have hσζ : ∀ u, frobL K g (ζ * u) = ζ ^ (p - 1) * frobL K g u :=
    frobL_root_mul hp hpK hgd hpq
  set Qb : Fin s → AdjoinRoot g → K := fun i u => QF (Φ (Pi.single i u, 0)) with hQb
  have hQadd : ∀ i u v, Qb i (u + v) = Qb i u + Qb i v + β u v := fun i u v =>
    quad_single_add hdec i u v
  have hsingle : ∀ (k : Fin s → ℕ) (i : Fin s) (u : AdjoinRoot g),
      (fun j => ζ ^ k j * (Pi.single i u : Fin s → AdjoinRoot g) j) =
        Pi.single i (ζ ^ k i * u) := by
    intro k i u
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  have hexp : ∀ x ∈ E, ∃ k : Fin s → ℕ, ∀ d w,
      glin ((x : ↥(LargeEvenOmega ⇑QF)) : GL ι K) (Φ (d, w)) =
        Φ (fun i => ζ ^ k i * d i, w) := fun x hx => hact _ ⟨x, hx, rfl⟩
  set act : Fin s → Prop := fun i => ∃ x ∈ E, ∃ u : AdjoinRoot g,
    glin ((x : ↥(LargeEvenOmega ⇑QF)) : GL ι K) (Φ (Pi.single i u, 0)) ≠ Φ (Pi.single i u, 0)
    with hactdef
  have hQζ : ∀ i, act i → ∀ u, Qb i (ζ * u) = Qb i u := by
    rintro i ⟨x, hx, u₀, hu₀⟩ u
    obtain ⟨k, hk⟩ := hexp x hx
    have hinv : ∀ v, Qb i (ζ ^ k i * v) = Qb i v := fun v => by
      have h1 := hiso x (Φ (Pi.single i v, 0))
      rw [hk, hsingle] at h1
      exact h1
    have hk1 : ζ ^ k i ≠ 1 := by
      intro h1
      apply hu₀
      rw [hk, hsingle, h1, one_mul]
    have hcop : (k i).Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      rintro ⟨c, hc⟩
      apply hk1
      rw [hc, pow_mul, hζp, one_pow]
    obtain ⟨m, -, hm⟩ := (hζo.pow_of_coprime (k i) hcop).eq_pow_of_pow_eq_one hζp
    have hpowinv : ∀ (m : ℕ) v, Qb i ((ζ ^ k i) ^ m * v) = Qb i v := by
      intro m
      induction m with
      | zero => intro v; rw [pow_zero, one_mul]
      | succ m ih => intro v; rw [pow_succ', mul_assoc, hinv, ih]
    rw [← hm, hpowinv]
  have hQζpow : ∀ i, act i → ∀ (m : ℕ) u, Qb i (ζ ^ m * u) = Qb i u := by
    intro i hi m
    induction m with
    | zero => intro u; rw [pow_zero, one_mul]
    | succ m ih => intro u; rw [pow_succ', mul_assoc, hQζ i hi, ih]
  have hQeq : ∀ i j, act i → act j → Qb i = Qb j := fun i j hi hj =>
    eq_of_add_of_mul hζ1 (hQadd i) (hQadd j) (hQζ i hi) (hQζ j hj)
  have hQσ : ∀ i, act i → ∀ u, Qb i (frobL K g u) = Qb i u := by
    intro i hi
    have h1 := eq_of_add_of_mul hζ1 (q₁ := fun u => Qb i (frobL K g u)) (q₂ := Qb i)
      (β := fun u v => β u v)
      (fun u v => by
        show Qb i (frobL K g (u + v)) = Qb i (frobL K g u) + Qb i (frobL K g v) + β u v
        rw [map_add, hQadd, hσβ])
      (hQadd i)
      (fun u => by
        show Qb i (frobL K g (ζ * u)) = Qb i (frobL K g u)
        rw [hσζ, hQζpow i hi])
      (hQζ i hi)
    exact fun u => congrFun h1 u
  have hfix : ∀ x ∈ E, ∀ (k : Fin s → ℕ), (∀ d w,
      glin ((x : ↥(LargeEvenOmega ⇑QF)) : GL ι K) (Φ (d, w)) =
        Φ (fun i => ζ ^ k i * d i, w)) → ∀ i, ¬ act i → ζ ^ k i = 1 := by
    intro x hx k hk i hi
    by_contra h1
    apply hi
    refine ⟨x, hx, 1, fun h2 => h1 ?_⟩
    rw [hk, hsingle, mul_one] at h2
    have h3 := congrArg (fun y : (Fin s → AdjoinRoot g) × (κ → K) => y.1 i) (Φ.injective h2)
    simpa using h3
  clear_value act
  obtain ⟨k, ⟨eJ⟩⟩ : ∃ k : ℕ, Nonempty (Fin k ≃ {i : Fin s // act i}) :=
    ⟨_, ⟨(Fintype.equivFin {i : Fin s // act i}).symm⟩⟩
  obtain ⟨ext, hext_act, hext_nact⟩ : ∃ ext : (Fin k → Multiplicative (ZMod p)) →*
      (Fin s → Multiplicative (ZMod p)),
      (∀ f i (h : act i), ext f i = f (eJ.symm ⟨i, h⟩)) ∧ (∀ f i, ¬ act i → ext f i = 1) := by
    refine ⟨{ toFun := fun f i => if h : act i then f (eJ.symm ⟨i, h⟩) else 1
              map_one' := ?_
              map_mul' := ?_ }, fun f i h => ?_, fun f i h => ?_⟩
    · funext i
      by_cases h : act i
      · simp [h]
      · simp [h]
    · intro f f'
      funext i
      by_cases h : act i
      · simp [h]
      · simp [h]
    · simp [h]
    · simp [h]
  have hext_inj : Function.Injective ext := by
    intro f f' h
    funext a
    have h1 := congrFun h (eJ a : Fin s)
    rw [hext_act f _ (eJ a).2, hext_act f' _ (eJ a).2] at h1
    simpa using h1
  obtain ⟨torGL, htorGL, htorGL_inj⟩ : ∃ torGL : (Fin s → Multiplicative (ZMod p)) →* GL ι K,
      (∀ F, torGL F = frameGL Φ (torEquiv hζp F)) ∧ Function.Injective torGL := by
    refine ⟨(Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom).comp
      ((sesqUnitaryGroup B).subtype.comp (torHom (K := K) hζp hdec hζβ)), fun F => rfl, ?_⟩
    rw [MonoidHom.coe_comp, MonoidHom.coe_comp]
    exact Matrix.GeneralLinearGroup.toLin.symm.injective.comp
      (Subtype.val_injective.comp (torHom_injective hζp hdec hζβ hζo))
  have hτQ : ∀ f x, QF (Φ (torEquiv hζp (ext f) x)) = QF (Φ x) := by
    intro f x
    refine quad_mono hdec 1 (fun i u => ?_) x
    show Qb i (ζ ^ (toAdd (ext f i)).val * u) = Qb i u
    by_cases hi : act i
    · exact hQζpow i hi _ u
    · rw [hext_nact f i hi, toAdd_one, ZMod.val_zero, pow_zero, one_mul]
  have hFallQ : ∀ x, QF (Φ (monoEquiv (κ := κ) 1 (fun i => if act i then frobL K g
      else LinearEquiv.refl K (AdjoinRoot g)) x)) = QF (Φ x) := fun x =>
    quad_mono hdec 1 (fun i u => by
      show QF (Φ (Pi.single i ((if act i then frobL K g
        else LinearEquiv.refl K (AdjoinRoot g)) u), 0)) = Qb i u
      by_cases hi : act i
      · simp only [hi, ↓reduceIte]
        exact hQσ i hi u
      · simp only [hi, ↓reduceIte]
        rfl) x
  have hτinv : ∀ f, frameGL Φ (monoEquiv (κ := κ) 1 (fun i => if act i then frobL K g
      else LinearEquiv.refl K (AdjoinRoot g))) * torGL (ext f) *
      (frameGL Φ (monoEquiv (κ := κ) 1 (fun i => if act i then frobL K g
      else LinearEquiv.refl K (AdjoinRoot g))))⁻¹ = (torGL (ext f))⁻¹ := by
    intro f
    rw [htorGL, frameGL_conj Φ (fun x => monoEquiv_torEquiv_sgn hζp hσζ act (ext f) x),
      ← htorGL, ← htorGL, ← map_inv]
    congr 1
    funext i
    by_cases hi : act i
    · simp only [hi, ↓reduceIte, Pi.inv_apply]
    · simp only [hi, ↓reduceIte, Pi.inv_apply, hext_nact f i hi]
      exact inv_one.symm
  have hτp : ∀ f, torGL (ext f) ^ p = 1 := fun f => by
    rw [← map_pow, ← map_pow, ReflInner.pow_eq_one_of_zmod, map_one, map_one]
  have hτΩ : ∀ f, torGL (ext f) ∈ LargeEvenOmega ⇑QF := fun f =>
    OrthRestTail.mem_omega_of_conj_inv (by rw [htorGL]; exact frameGL_mem_orth Φ (hτQ f))
      (frameGL_mem_orth Φ hFallQ) (hτinv f) (hp.odd_of_ne_two hp2) (hτp f)
  obtain ⟨τ, hτval⟩ : ∃ τ : (Fin k → Multiplicative (ZMod p)) →* ↥(LargeEvenOmega ⇑QF),
      ∀ f, ((τ f : ↥(LargeEvenOmega ⇑QF)) : GL ι K) = torGL (ext f) :=
    ⟨(torGL.comp ext).codRestrict _ hτΩ, fun f => rfl⟩
  have hτinj : Function.Injective τ := fun f f' h => by
    have h1 := congrArg Subtype.val h
    rw [hτval, hτval] at h1
    exact hext_inj (htorGL_inj h1)
  have hEτ : ∀ x ∈ E, ∃ f, τ f = x := by
    intro x hx
    obtain ⟨kx, hkx⟩ := hexp x hx
    refine ⟨fun a => ofAdd ((kx (eJ a : Fin s) : ℕ) : ZMod p),
      Subtype.ext (eq_of_glin fun v => ?_)⟩
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [hτval, glin_apply, htorGL, frameGL_mulVec, hkx, torEquiv_apply]
    congr 2
    funext i
    congr 1
    by_cases hi : act i
    · rw [hext_act _ i hi]
      simp only [Equiv.apply_symm_apply]
      rw [toAdd_ofAdd, ZMod.val_natCast, ← pow_eq_pow_mod _ hζp]
    · rw [hext_nact _ i hi, hfix x hx kx hkx i hi, toAdd_one, ZMod.val_zero, pow_zero]
  have hτE : τ.range = E := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      refine hsc _ (fun y hy => ?_) ?_
      · obtain ⟨f', rfl⟩ := hEτ y hy
        rw [← map_mul, ← map_mul, mul_comm]
      · rw [← map_pow, ReflInner.pow_eq_one_of_zmod, map_one]
    · intro hx
      obtain ⟨f, hf⟩ := hEτ x hx
      exact ⟨f, hf⟩
  have hdinv : ∀ a b : Fin k, a ≠ b → ∃ w : ↥(LargeEvenOmega ⇑QF), ∀ f,
      w * τ f * w⁻¹ = τ (dinv a b f) := by
    intro a b hab
    have hia : act (eJ a : Fin s) := (eJ a).2
    have hib : act (eJ b : Fin s) := (eJ b).2
    have hiab : (eJ a : Fin s) ≠ (eJ b : Fin s) := fun h => hab (eJ.injective (Subtype.ext h))
    have hFaQ : ∀ x, QF (Φ (monoEquiv (κ := κ) 1 (fun i => if i = (eJ a : Fin s) then frobL K g
        else LinearEquiv.refl K (AdjoinRoot g)) x)) = QF (Φ x) := fun x =>
      quad_mono hdec 1 (fun i u => by
        show QF (Φ (Pi.single i ((if i = (eJ a : Fin s) then frobL K g
          else LinearEquiv.refl K (AdjoinRoot g)) u), 0)) = Qb i u
        by_cases hi : i = (eJ a : Fin s)
        · simp only [hi, ↓reduceIte]
          exact hQσ _ hia u
        · simp only [hi, ↓reduceIte]
          rfl) x
    have hSwQ : ∀ x, QF (Φ (monoEquiv (κ := κ) (Equiv.swap (eJ a : Fin s) (eJ b : Fin s))⁻¹
        (fun _ => LinearEquiv.refl K (AdjoinRoot g)) x)) = QF (Φ x) := fun x =>
      quad_mono hdec _ (fun i u => by
        show Qb i u = Qb ((Equiv.swap (eJ a : Fin s) (eJ b : Fin s))⁻¹ i) u
        rw [Equiv.swap_inv]
        by_cases hi : i = (eJ a : Fin s)
        · rw [hi, Equiv.swap_apply_left, hQeq _ _ hia hib]
        · by_cases hi' : i = (eJ b : Fin s)
          · rw [hi', Equiv.swap_apply_right, hQeq _ _ hib hia]
          · rw [Equiv.swap_apply_of_ne_of_ne hi hi']) x
    have hFa : ∀ F, frameGL Φ (monoEquiv (κ := κ) 1 (fun i => if i = (eJ a : Fin s) then frobL K g
        else LinearEquiv.refl K (AdjoinRoot g))) * torGL F *
        (frameGL Φ (monoEquiv (κ := κ) 1 (fun i => if i = (eJ a : Fin s) then frobL K g
        else LinearEquiv.refl K (AdjoinRoot g))))⁻¹ = torGL (sgnAut (eJ a : Fin s) F) := by
      intro F
      rw [htorGL, frameGL_conj Φ (fun x =>
        monoEquiv_torEquiv_sgn hζp hσζ (· = (eJ a : Fin s)) F x), htorGL]
      congr 2
      funext i
      rw [sgnAut_apply, Function.update_apply]
      by_cases hi : i = (eJ a : Fin s)
      · simp only [hi, ↓reduceIte]
      · simp only [hi, ↓reduceIte]
    have hSw : ∀ F, frameGL Φ (monoEquiv (κ := κ) (Equiv.swap (eJ a : Fin s) (eJ b : Fin s))⁻¹
        (fun _ => LinearEquiv.refl K (AdjoinRoot g))) * torGL F *
        (frameGL Φ (monoEquiv (κ := κ) (Equiv.swap (eJ a : Fin s) (eJ b : Fin s))⁻¹
        (fun _ => LinearEquiv.refl K (AdjoinRoot g))))⁻¹ =
          torGL (permAut (Equiv.swap (eJ a : Fin s) (eJ b : Fin s)) F) := by
      intro F
      rw [htorGL, frameGL_conj Φ (fun x => monoEquiv_torEquiv_perm hζp _ F x), htorGL]
      rfl
    refine ⟨⟨_, Subgroup.commutator_mem_commutator (frameGL_mem_orth Φ hFaQ)
      (frameGL_mem_orth Φ hSwQ)⟩, fun f => Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hτval, hτval]
    rw [conj_commutator_eq torGL hFa (sgnAut_sgnAut _) hSw (permAut_comp_self _) (ext f),
      sgnAut_permAut_swap hiab]
    congr 1
    funext i
    rw [dinv_apply_eq]
    simp only [hiab, ↓reduceIte]
    by_cases hi : act i
    · rw [hext_act _ i hi, hext_act _ i hi, dinv_apply_eq]
      simp only [hab, ↓reduceIte]
      have hiff : (i = (eJ a : Fin s) ∨ i = (eJ b : Fin s)) ↔
          (eJ.symm ⟨i, hi⟩ = a ∨ eJ.symm ⟨i, hi⟩ = b) := by
        rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq, Subtype.ext_iff, Subtype.ext_iff]
      by_cases hc : i = (eJ a : Fin s) ∨ i = (eJ b : Fin s)
      · simp only [hc, hiff.mp hc, ↓reduceIte]
      · simp only [hc, ↓reduceIte]
        split_ifs with h
        · exact absurd (hiff.mpr h) hc
        · rfl
    · rw [hext_nact _ i hi, hext_nact _ i hi]
      split_ifs <;> first | rfl | exact inv_one
  have hPQ : ∀ ρ : Equiv.Perm (Fin k), frameGL Φ (monoEquiv (κ := κ) (ρ.extendDomain eJ)⁻¹
      (fun _ => LinearEquiv.refl K (AdjoinRoot g))) ∈ LargeEvenOrthGroup ⇑QF := by
    intro ρ
    refine frameGL_mem_orth Φ fun x => quad_mono hdec _ (fun i u => ?_) x
    show Qb i u = Qb ((ρ.extendDomain eJ)⁻¹ i) u
    rw [Equiv.Perm.extendDomain_inv]
    by_cases hi : act i
    · rw [Equiv.Perm.extendDomain_apply_subtype _ eJ hi]
      exact congrFun (hQeq i _ hi (eJ _).2) u
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ eJ hi]
  have hP : ∀ (ρ : Equiv.Perm (Fin s)) F, frameGL Φ (monoEquiv (κ := κ) ρ⁻¹
      (fun _ => LinearEquiv.refl K (AdjoinRoot g))) * torGL F * (frameGL Φ (monoEquiv (κ := κ)
      ρ⁻¹ (fun _ => LinearEquiv.refl K (AdjoinRoot g))))⁻¹ = torGL (permAut ρ F) := by
    intro ρ F
    rw [htorGL, frameGL_conj Φ (fun x => monoEquiv_torEquiv_perm hζp ρ F x), htorGL]
    rfl
  have hswap : ∀ j t u : Fin k, j ≠ t → j ≠ u → t ≠ u → ∃ w : ↥(LargeEvenOmega ⇑QF), ∀ f,
      w * τ f * w⁻¹ = τ (f ∘ ⇑(swapComm j t u)⁻¹) := by
    intro j t u _ _ _
    refine ⟨⟨_, Subgroup.commutator_mem_commutator (hPQ (Equiv.swap j t)) (hPQ (Equiv.swap j u))⟩,
      fun f => Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hτval, hτval]
    rw [conj_commutator_eq torGL (hP _) (permAut_comp_self _) (hP _) (permAut_comp_self _) (ext f),
      permAut_comm_eq]
    congr 1
    have hc : (Equiv.swap j t).extendDomain eJ * (Equiv.swap j u).extendDomain eJ *
        ((Equiv.swap j t).extendDomain eJ)⁻¹ * ((Equiv.swap j u).extendDomain eJ)⁻¹ =
        (swapComm j t u).extendDomain eJ := by
      rw [swapComm]
      simp only [Equiv.Perm.extendDomain_inv, Equiv.Perm.extendDomain_mul]
    rw [hc, Equiv.Perm.extendDomain_inv]
    funext i
    simp only [Function.comp_apply]
    by_cases hi : act i
    · rw [Equiv.Perm.extendDomain_apply_subtype _ eJ hi, hext_act _ _ (Subtype.property _),
        hext_act _ i hi]
      simp
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ eJ hi, hext_nact _ i hi,
        hext_nact _ i hi]
  exact ⟨k, τ, hτinj, hτE, hdinv, hswap⟩

end Omega

end OrthNs

end CFSG.StandardType

end
