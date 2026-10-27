module

public import CFSG.Quasithin.Background.C4Defs
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.Quasithin

namespace Stellmacher.PU.L3YC

section Linear

variable {F : Type} [Field F] [Fintype F]

theorem eq_zero_or_one_of_card_two (hF : Fintype.card F = 2) (c : F) : c = 0 ∨ c = 1 := by
  classical
  by_contra h
  simp only [not_or] at h
  have hsub : ({0, 1, c} : Finset F) ⊆ Finset.univ := Finset.subset_univ _
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  have hcard : ({0, 1, c} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (fun e => h.2 e.symm)]
    have hc0 : (0 : F) ≠ c := fun e => h.1 e.symm
    simp [h01, hc0]
  have := Finset.card_le_card hsub
  rw [hcard, Finset.card_univ, hF] at this
  omega

theorem exists_gl_of_addEquiv (hF : Fintype.card F = 2) (φ : (Fin 3 → F) ≃+ (Fin 3 → F)) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 3) F,
      ∀ v : Fin 3 → F, (g : Matrix (Fin 3) (Fin 3) F).mulVec v = φ v := by
  have hsm : ∀ (c : F) (v : Fin 3 → F), φ (c • v) = c • φ v := by
    intro c v
    rcases eq_zero_or_one_of_card_two hF c with rfl | rfl
    · simp
    · simp
  let f : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := φ, map_add' := φ.map_add, map_smul' := hsm }
  let g : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := φ.symm, map_add' := φ.symm.map_add,
      map_smul' := fun c v => by
        apply φ.injective
        rw [hsm, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
        rfl }
  have hfg : f * g = 1 := LinearMap.ext fun v => φ.apply_symm_apply v
  have hgf : g * f = 1 := LinearMap.ext fun v => φ.symm_apply_apply v
  let u : LinearMap.GeneralLinearGroup F (Fin 3 → F) := ⟨f, g, hfg, hgf⟩
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm u, fun v => ?_⟩
  have h := Matrix.GeneralLinearGroup.toLin_apply (Matrix.GeneralLinearGroup.toLin.symm u) v
  rw [MulEquiv.apply_symm_apply] at h
  rw [← Matrix.mulVecLin_apply]
  exact h.symm

theorem statedSL_eq_top_of_card_two (hF : Fintype.card F = 2) (n : ℕ) :
    CFSG.Assembly.LowTwoRank.StatedSL n F = ⊤ :=
  CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two (by rw [Nat.card_eq_fintype_card, hF]) n

end Linear

section Core

variable {G : Type} [Group G]

def conjOn (U : Subgroup G) (c : G) (hc : c ∈ Subgroup.normalizer (U : Set G)) : ↥U ≃* ↥U where
  toFun u := ⟨c * u * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc u).mp u.2⟩
  invFun u := ⟨c⁻¹ * u * c, (Subgroup.mem_normalizer_iff''.mp hc u).mp u.2⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

def toAddEquivOf {W : Type} [AddCommGroup W] (ψ : Multiplicative W ≃* Multiplicative W) : W ≃+ W where
  toFun v := Multiplicative.toAdd (ψ (Multiplicative.ofAdd v))
  invFun v := Multiplicative.toAdd (ψ.symm (Multiplicative.ofAdd v))
  left_inv v := by simp
  right_inv v := by simp
  map_add' a b := by simp

theorem inner_of_natural {L U : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F)}
    (hΓ : ∀ g, g ∈ Γ) (α : ↥L →* ↥Γ) (hα : Function.Surjective α)
    (hnat : IsSumOfNaturalModulesVia L U ⊥ α false 1)
    {s : G} (hsU : s ∈ Subgroup.normalizer (U : Set G)) :
    ∃ l : ↥L, ∀ x y : ↥L, (y : G) = ((l : G)⁻¹ * s) * x * ((l : G)⁻¹ * s)⁻¹ → α y = α x := by
  classical
  obtain ⟨hLU, -, β, hβs, hβk, hβe⟩ := hnat
  let e : Multiplicative (Fin 1 → Fin 3 → F) ≃* Multiplicative (Fin 3 → F) :=
    AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (Fin 3 → F))
  let β0 : ↥U →* Multiplicative (Fin 3 → F) := e.toMonoidHom.comp β
  have hβ0s : Function.Surjective β0 := e.surjective.comp hβs
  have hβ0i : Function.Injective β0 := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : β u = 1 := e.injective (by simpa [β0] using hu)
    have h2 : u ∈ β.ker := h1
    rw [hβk, Subgroup.mem_subgroupOf] at h2
    exact Subtype.ext (by simpa using h2)
  let B : ↥U ≃* Multiplicative (Fin 3 → F) := MulEquiv.ofBijective β0 ⟨hβ0i, hβ0s⟩
  have hBe : ∀ (a : ↥L) (u v : ↥U), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (B v) =
        ((α a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (B u)) := by
    intro a u v h
    have := hβe a u v h 0
    simp [B, β0, e, moduleAct] at this ⊢
    exact this
  have hsN : s ∈ Subgroup.normalizer (U : Set G) := hsU
  let ψ : Multiplicative (Fin 3 → F) ≃* Multiplicative (Fin 3 → F) :=
    B.symm.trans ((conjOn U s hsN).trans B)
  obtain ⟨g, hg⟩ := exists_gl_of_addEquiv hF (toAddEquivOf ψ)
  obtain ⟨l, hl⟩ := hα ⟨g, hΓ g⟩
  have hlU : (l : G) ∈ Subgroup.normalizer (U : Set G) := hLU l.2
  have hconj : ∀ u : ↥U, (l : G) * u * (l : G)⁻¹ = s * u * s⁻¹ := by
    intro u
    have hmem : (l : G) * u * (l : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hlU u).mp u.2
    have h1 := hBe l u ⟨_, hmem⟩ rfl
    rw [hl] at h1
    have h2 : Multiplicative.toAdd (B ⟨_, hmem⟩) = Multiplicative.toAdd (B (conjOn U s hsN u)) := by
      rw [h1]
      have := hg (Multiplicative.toAdd (B u))
      simp only [toAddEquivOf, AddEquiv.coe_mk, Equiv.coe_fn_mk, ofAdd_toAdd, ψ, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply] at this
      simpa using this
    have h3 := B.injective (Multiplicative.toAdd.injective h2)
    exact congrArg Subtype.val h3
  set d : G := (l : G)⁻¹ * s with hd
  have hdN : d ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hlU) hsU
  have hdU : ∀ u : G, u ∈ U → d * u * d⁻¹ = u := by
    intro u hu
    have h := hconj ⟨u, hu⟩
    simp only at h
    calc d * u * d⁻¹ = (l : G)⁻¹ * (s * u * s⁻¹) * l := by simp [hd, mul_assoc]
      _ = u := by rw [← h]; group
  have hdU' : ∀ u : G, u ∈ U → d⁻¹ * u * d = u := by
    intro u hu
    have hm : d⁻¹ * u * d ∈ U := (Subgroup.mem_normalizer_iff''.mp hdN u).mp hu
    have h := hdU _ hm
    have e : d * (d⁻¹ * u * d) * d⁻¹ = u := by group
    rw [e] at h
    exact h.symm
  refine ⟨l, fun x y hy => ?_⟩
  have hxU : (x : G) ∈ Subgroup.normalizer (U : Set G) := hLU x.2
  have hyU : (y : G) ∈ Subgroup.normalizer (U : Set G) := hLU y.2
  have key : ∀ d x u : G, d * x * d⁻¹ * u * (d * x * d⁻¹)⁻¹ =
      d * (x * (d⁻¹ * u * d) * x⁻¹) * d⁻¹ := by
    intros; group
  have hmv : ∀ v : Fin 3 → F,
      ((α y : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v =
        ((α x : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v := by
    intro v
    obtain ⟨u, hu⟩ := B.surjective (Multiplicative.ofAdd v)
    have hpm : (x : G) * u * (x : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxU u).mp u.2
    have hqm : (y : G) * u * (y : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hyU u).mp u.2
    have hpq : (y : G) * u * (y : G)⁻¹ = (x : G) * u * (x : G)⁻¹ := by
      have h1 : (y : G) * u * (y : G)⁻¹ = d * ((x : G) * (d⁻¹ * u * d) * (x : G)⁻¹) * d⁻¹ := by
        rw [hy]; exact key d x u
      rw [h1, hdU' u u.2]
      exact hdU _ hpm
    have hx := hBe x u ⟨_, hpm⟩ rfl
    have hy' := hBe y u ⟨_, hqm⟩ rfl
    have hEq : (⟨_, hqm⟩ : ↥U) = ⟨_, hpm⟩ := Subtype.ext hpq
    rw [hEq, hx, hu] at hy'
    simpa using hy'.symm
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have := congrFun (hmv (Pi.single j (1 : F))) i
  simpa [Matrix.mulVec_single_one] using this

theorem inner_of_natural_stated {L U : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hα : Function.Surjective α) (hnat : IsSumOfNaturalModulesVia L U ⊥ α false 1)
    {s : G} (hsU : s ∈ Subgroup.normalizer (U : Set G)) :
    ∃ l : ↥L, ∀ x y : ↥L, (y : G) = ((l : G)⁻¹ * s) * x * ((l : G)⁻¹ * s)⁻¹ → α y = α x :=
  inner_of_natural hF (fun g => by rw [statedSL_eq_top_of_card_two hF]; trivial) α hα hnat hsU

end Core

end Stellmacher.PU.L3YC

end CFSG.Quasithin
