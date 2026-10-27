module

public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma l05nDA_inv_mem {N : Type*} [Monoid N] {T : Set N}
    (hT : ∀ t ∈ T, ∃ y ∈ Submonoid.closure T, t * y = 1 ∧ y * t = 1) :
    ∀ x ∈ Submonoid.closure T, ∃ y ∈ Submonoid.closure T, x * y = 1 ∧ y * x = 1 := by
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem t ht => exact hT t ht
  | one => exact ⟨1, Submonoid.one_mem _, by simp, by simp⟩
  | mul a b ha hb iha ihb =>
      obtain ⟨a', ha', ha1, ha2⟩ := iha
      obtain ⟨b', hb', hb1, hb2⟩ := ihb
      refine ⟨b' * a', Submonoid.mul_mem _ hb' ha', ?_, ?_⟩
      · calc (a * b) * (b' * a') = a * (b * b') * a' := by simp only [mul_assoc]
          _ = a * 1 * a' := by rw [hb1]
          _ = a * a' := by simp
          _ = 1 := ha1
      · calc (b' * a') * (a * b) = b' * (a' * a) * b := by simp only [mul_assoc]
          _ = b' * 1 * b := by rw [ha2]
          _ = b' * b := by simp
          _ = 1 := hb2

lemma l05nDA_closure_image {M N : Type*} [Group M] [Finite M] [Monoid N]
    (f : M →* N) (S : Set M) :
    f '' ↑(Subgroup.closure S) = ↑(Submonoid.closure (f '' S)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hT : ∀ t ∈ f '' S, ∃ y ∈ Submonoid.closure (f '' S), t * y = 1 ∧ y * t = 1 := by
      rintro _ ⟨s, hs, rfl⟩
      have h1 : s * s ^ (orderOf s - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ orderOf s from orderOf_pos s),
          pow_orderOf_eq_one]
      have h2 : (s ^ (orderOf s - 1)) * s = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ orderOf s from orderOf_pos s),
          pow_orderOf_eq_one]
      refine ⟨f (s ^ (orderOf s - 1)), ?_, ?_, ?_⟩
      · rw [map_pow]
        exact Submonoid.pow_mem (Submonoid.closure (f '' S))
          (Submonoid.subset_closure (show f s ∈ f '' S from ⟨s, hs, rfl⟩)) (orderOf s - 1)
      · rw [← map_mul, h1, map_one]
      · rw [← map_mul, h2, map_one]
    induction hx using Subgroup.closure_induction with
    | mem t ht => exact Submonoid.subset_closure ⟨t, ht, rfl⟩
    | one => simpa using Submonoid.one_mem (Submonoid.closure (f '' S))
    | mul a b ha hb iha ihb => rw [map_mul]; exact Submonoid.mul_mem _ iha ihb
    | inv a ha iha =>
        obtain ⟨y, hy, hy1, hy2⟩ := l05nDA_inv_mem hT (f a) iha
        have h4 : f a⁻¹ * f a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have hyeq : y = f a⁻¹ := by rw [← one_mul y, ← h4, mul_assoc, hy1, mul_one]
        rwa [hyeq] at hy
  · have h2 : Submonoid.closure (f '' S) ≤ Submonoid.map f (Subgroup.closure S).toSubmonoid :=
      Submonoid.closure_le.mpr (fun t ht => by
        obtain ⟨s, hs, rfl⟩ := ht
        exact ⟨s, Subgroup.subset_closure hs, rfl⟩)
    intro x hx
    exact h2 hx

@[expose] noncomputable def l05nDA_conj {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (θ : V ≃ₗ[ZMod p] GGTWE p N) :
    (V ≃ₗ[ZMod p] V) →* (GGTWE p N ≃ₗ[ZMod p] GGTWE p N) where
  toFun g := θ.symm.trans (g.trans θ)
  map_one' := by ext w; simp [LinearEquiv.trans_apply]
  map_mul' f g := by ext w; simp [LinearEquiv.trans_apply, LinearEquiv.mul_apply]

lemma l05nDA_conj_apply {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (θ : V ≃ₗ[ZMod p] GGTWE p N) (g : V ≃ₗ[ZMod p] V) (v : V) :
    l05nDA_conj θ g (θ v) = θ (g v) := by
  simp [l05nDA_conj, LinearEquiv.trans_apply]

lemma l05nDA_conj_coe {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (θ : V ≃ₗ[ZMod p] GGTWE p N) (g : V ≃ₗ[ZMod p] V) :
    (l05nDA_conj θ g : Module.End (ZMod p) (GGTWE p N)) =
      θ.toLinearMap ∘ₗ (g : V →ₗ[ZMod p] V) ∘ₗ θ.symm.toLinearMap := by
  apply LinearMap.ext
  intro w
  simp [l05nDA_conj, LinearEquiv.trans_apply, LinearMap.comp_apply]

lemma l05nDA_conj_injective {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (θ : V ≃ₗ[ZMod p] GGTWE p N) : Function.Injective (l05nDA_conj θ) := by
  intro g h hgh
  ext v
  have h2 := congrArg (fun e => e (θ v)) hgh
  simp only [l05nDA_conj_apply] at h2
  exact θ.injective h2

@[expose] noncomputable def l05nDA_coe {p N : ℕ} :
    (GGTWE p N ≃ₗ[ZMod p] GGTWE p N) →* Module.End (ZMod p) (GGTWE p N) where
  toFun e := (e : Module.End (ZMod p) (GGTWE p N))
  map_one' := rfl
  map_mul' e f := rfl

@[expose] noncomputable def l05nDA_conjEnd {p N : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) :
    (V ≃ₗ[ZMod p] V) →* Module.End (ZMod p) (GGTWE p N) :=
  (l05nDA_coe).comp (l05nDA_conj θ)

lemma l05nDA_conjEnd_apply {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (θ : V ≃ₗ[ZMod p] GGTWE p N) (g : V ≃ₗ[ZMod p] V) :
    l05nDA_conjEnd θ g = (l05nDA_conj θ g : Module.End (ZMod p) (GGTWE p N)) := rfl

@[expose] noncomputable def l05nDA_PhiEnd {p N : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod p] GGTWE p N) : MulAut ↥Bs →* Module.End (ZMod p) (GGTWE p N) :=
  (l05nDA_conjEnd θ).comp (ggLin (p := p) ι)

lemma l05nDA_PhiEnd_apply {p N : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod p] GGTWE p N) (t : MulAut ↥Bs) :
    l05nDA_PhiEnd ι θ t = l05nDA_conjEnd θ (ggLin (p := p) ι t) := rfl

lemma l05nDA_PhiEnd_injective {p N : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod p] GGTWE p N) : Function.Injective (l05nDA_PhiEnd ι θ) := by
  intro a b hab
  have h1 : l05nDA_conjEnd θ (ggLin (p := p) ι a) = l05nDA_conjEnd θ (ggLin (p := p) ι b) := hab
  have h2 : l05nDA_conj θ (ggLin (p := p) ι a) = l05nDA_conj θ (ggLin (p := p) ι b) :=
    LinearEquiv.toLinearMap_injective h1
  exact ggLin_injective (p := p) ι (l05nDA_conj_injective θ h2)

lemma l05nDA_form_apply {p N : ℕ} (f v : GGTWE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot, smul_eq_mul]

lemma l05nDA_refl_apply {p N : ℕ} (c f v : GGTWE p N) :
    ggTWRefl c f v = v - ggDepAdot f v • c := by
  simp [ggTWRefl, ggDepARefl, l05nDA_form_apply]

lemma l05nDA_form_single {p N : ℕ} (f : GGTWE p N) (j : Fin (N - 1)) :
    ggDepAform f (Pi.single j (1 : ZMod p)) = f j := by
  rw [l05nDA_form_apply, ggDepAdot, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb]; simp
  · intro hj; exact absurd (Finset.mem_univ j) hj

lemma l05nDA_form_surj {p N : ℕ} (φ : GGTWE p N →ₗ[ZMod p] ZMod p) :
    ∃ f : GGTWE p N, ggDepAform f = φ := by
  refine ⟨fun j => φ (Pi.single j (1 : ZMod p)), ?_⟩
  apply (Pi.basisFun (ZMod p) (Fin (N - 1))).ext
  intro j
  rw [Pi.basisFun_apply, l05nDA_form_single]

lemma l05nDA_ggIsReflection_iff_isLinRefl {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (t : MulAut ↥Bs) :
    GGIsReflection p t ↔ IsLinRefl (ggLin (p := p) ι t) := by
  haveI : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  haveI : Finite (Additive ↥Bs) := ‹Finite ↥Bs›
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  constructor
  · intro h
    exact exists_of_ggIsReflection (p := p) ι h
  · rintro ⟨x, f, hfx, hform⟩
    exact ggIsReflection_of_eq_reflection (p := p) hp2 ι hfx
      (LinearEquiv.ext fun v => by rw [hform, Module.reflection_apply])

lemma l05nDA_isLinRefl_conj {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) (T : V ≃ₗ[ZMod p] V) :
    IsLinRefl T ↔ IsLinRefl (l05nDA_conj θ T) := by
  constructor
  · rintro ⟨x, f, hfx, hform⟩
    refine ⟨θ x, f.comp θ.symm.toLinearMap, ?_, fun w => ?_⟩
    · simpa [LinearMap.comp_apply] using hfx
    · rw [← θ.apply_symm_apply w, l05nDA_conj_apply, hform, map_sub, map_smul,
        θ.apply_symm_apply, LinearMap.comp_apply]
      rfl
  · rintro ⟨x, f, hfx, hform⟩
    refine ⟨θ.symm x, f.comp θ.toLinearMap, ?_, fun v => ?_⟩
    · simpa [LinearMap.comp_apply] using hfx
    · have h := hform (θ v)
      rw [l05nDA_conj_apply] at h
      have h2 := congrArg θ.symm h
      simp only [map_sub, map_smul, LinearEquiv.symm_apply_apply] at h2
      simpa [LinearMap.comp_apply] using h2

lemma l05nDA_isLinRefl_iff_GGTWIsRefl {p N : ℕ} [Fact p.Prime]
    (T : GGTWE p N ≃ₗ[ZMod p] GGTWE p N) :
    IsLinRefl T ↔ GGTWIsRefl (T : Module.End (ZMod p) (GGTWE p N)) := by
  constructor
  · rintro ⟨x, f, hfx, hform⟩
    obtain ⟨fv, hfv⟩ := l05nDA_form_surj f
    refine ⟨x, fv, ?_, ?_⟩
    · rw [ggTWdot, ← l05nDA_form_apply, hfv]; exact hfx
    · apply LinearMap.ext
      intro v
      change T v = ggTWRefl x fv v
      rw [hform v, l05nDA_refl_apply, ← l05nDA_form_apply, hfv]
  · rintro ⟨c, fv, hdot, heq⟩
    refine ⟨c, ggDepAform fv, ?_, fun v => ?_⟩
    · rw [l05nDA_form_apply]; exact hdot
    · have h := congrArg (fun e : Module.End (ZMod p) (GGTWE p N) => e v) heq
      rw [l05nDA_refl_apply] at h
      rw [l05nDA_form_apply]
      exact h

lemma l05nDA_reflection_iff {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (θ : V ≃ₗ[ZMod p] GGTWE p N)
    (t : MulAut ↥Bs) :
    GGIsReflection p t ↔ GGTWIsRefl (l05nDA_PhiEnd ι θ t) := by
  show GGIsReflection p t ↔ GGTWIsRefl (l05nDA_conjEnd θ (ggLin (p := p) ι t))
  show GGIsReflection p t ↔ GGTWIsRefl ((l05nDA_conj θ (ggLin (p := p) ι t) :
    GGTWE p N ≃ₗ[ZMod p] GGTWE p N) : Module.End (ZMod p) (GGTWE p N))
  exact (l05nDA_ggIsReflection_iff_isLinRefl hp2 ι t).trans
    ((l05nDA_isLinRefl_conj θ (ggLin (p := p) ι t)).trans
      (l05nDA_isLinRefl_iff_GGTWIsRefl (l05nDA_conj θ (ggLin (p := p) ι t))))

lemma l05nDA_PhiEnd_fix {p N : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (θ : V ≃ₗ[ZMod p] GGTWE p N) (t : MulAut ↥Bs) (z : ↥Bs) :
    l05nDA_PhiEnd ι θ t (θ (ι (Additive.ofMul z))) = θ (ι (Additive.ofMul z)) ↔ t z = z := by
  constructor
  · intro h
    have h' : θ (ι (Additive.ofMul (t z))) = θ (ι (Additive.ofMul z)) := by
      have h1 := h
      change l05nDA_conj θ (ggLin (p := p) ι t) (θ (ι (Additive.ofMul z))) = _ at h1
      rw [l05nDA_conj_apply, ggLin_apply_ofMul] at h1
      exact h1
    exact Additive.ofMul.injective (ι.injective (θ.injective h'))
  · intro h
    change l05nDA_conj θ (ggLin (p := p) ι t) (θ (ι (Additive.ofMul z))) = θ (ι (Additive.ofMul z))
    rw [l05nDA_conj_apply, ggLin_apply_ofMul, h]

end CFSG.StandardType

end
