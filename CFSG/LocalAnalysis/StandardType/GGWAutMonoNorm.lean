module

public import CFSG.LocalAnalysis.StandardType.GGWAutCommon
public import CFSG.LocalAnalysis.StandardType.GGRCMonomial
public import CFSG.LocalAnalysis.StandardType.GGRCSignedClass

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Imprim

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggWAut_imprim_frame [Module.Finite (ZMod 3) V] {n : ℕ} (hn : Module.finrank (ZMod 3) V = n)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (habs : ZS.AbsIrred 3 R)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (himp : CFSG.Quasithin.SimsG4.IsImprimitiveOnV R) :
    ∃ f : Module.Basis (Fin n) (ZMod 3) V, ∀ g ∈ R, GGMonomialIn f g :=
  ggRC_monomial_of_imprimitive (p := 3) hn R habs hgen himp

private lemma ggWAutN_zmod3_trichotomy (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = -1 := by
  revert x
  decide

private lemma ggWAutN_monomial_pm1 {n : ℕ} (b : Fin n → V) (g : V ≃ₗ[ZMod 3] V) :
    GGMonomialIn b g ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod 3),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, g (b i) = c i • b (σ i) := by
  constructor
  · rintro ⟨σ, ε, hne, hε⟩
    refine ⟨σ, ε, fun i => ?_, hε⟩
    rcases ggWAutN_zmod3_trichotomy (ε i) with h | h | h
    · exact absurd h (hne i)
    · exact Or.inl h
    · exact Or.inr h
  · rintro ⟨σ, c, hc, hε⟩
    refine ⟨σ, c, fun i => ?_, hε⟩
    rcases hc i with h | h <;> rw [h] <;> norm_num

private lemma ggWAutN_even_pm1 {n : ℕ} (b : Fin n → V) (g : V ≃ₗ[ZMod 3] V) :
    GGMonomialEvenIn b g ↔ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod 3),
      (∀ i, c i = 1 ∨ c i = -1) ∧ (∏ i, c i = 1) ∧ ∀ i, g (b i) = c i • b (σ i) := by
  constructor
  · rintro ⟨σ, ε, hne, hprod, hε⟩
    refine ⟨σ, ε, fun i => ?_, hprod, hε⟩
    rcases ggWAutN_zmod3_trichotomy (ε i) with h | h | h
    · exact absurd h (hne i)
    · exact Or.inl h
    · exact Or.inr h
  · rintro ⟨σ, c, hc, hprod, hε⟩
    refine ⟨σ, c, fun i => ?_, hprod, hε⟩
    rcases hc i with h | h <;> rw [h] <;> norm_num

theorem ggWAut_monomial_type {n : ℕ} (hn : 5 ≤ n) (f : Module.Basis (Fin n) (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (habs : ZS.AbsIrred 3 R)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r}) (hmon : ∀ g ∈ R, GGMonomialIn f g) :
    (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨ (∀ g, g ∈ R ↔ GGMonomialEvenIn f g) := by
  have hmon' : ∀ a ∈ R, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod 3),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (f i) = c i • f (σ i) :=
    fun a ha => (ggWAutN_monomial_pm1 f a).mp (hmon a ha)
  rcases ggRC_signed_class (p := 3) (by norm_num) (by omega) f R habs hgen hmon' with h | h
  · exact Or.inl fun g => (h g).trans (ggWAutN_monomial_pm1 f g).symm
  · exact Or.inr fun g => (h g).trans (ggWAutN_even_pm1 f g).symm

private lemma ggWAutN_repr_basis {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V) (i : Fin n) :
    f.repr (f i) = Finsupp.single i (1 : ZMod 3) :=
  Module.Basis.repr_self f i

private lemma ggWAutN_equivFun_basis {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V) (i : Fin n) :
    f.equivFun (f i) = Pi.single i (1 : ZMod 3) := by
  rw [Module.Basis.equivFun_apply, ggWAutN_repr_basis, Finsupp.single_eq_pi_single]

private lemma ggWAutN_mono_unique {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    {g : V ≃ₗ[ZMod 3] V} {σ σ' : Equiv.Perm (Fin n)} {ε ε' : Fin n → ZMod 3}
    (hε : ∀ i, ε i ≠ 0) (_hε' : ∀ i, ε' i ≠ 0)
    (h : ∀ i, g (f i) = ε i • f (σ i)) (h' : ∀ i, g (f i) = ε' i • f (σ' i)) :
    σ = σ' ∧ ε = ε' := by
  have key : ∀ i, σ i = σ' i ∧ ε i = ε' i := by
    intro i
    have h1 : f.equivFun (g (f i)) = ε i • Pi.single (σ i) (1 : ZMod 3) := by
      rw [h i, map_smul, ggWAutN_equivFun_basis]
    have h2 : f.equivFun (g (f i)) = ε' i • Pi.single (σ' i) (1 : ZMod 3) := by
      rw [h' i, map_smul, ggWAutN_equivFun_basis]
    have hc := congrArg (fun x : Fin n → ZMod 3 => x (σ i)) (h1.symm.trans h2)
    have hc' : ε i = ε' i * (Pi.single (σ' i) (1 : ZMod 3) : Fin n → ZMod 3) (σ i) := by
      simpa [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul] using hc
    by_cases hs : σ' i = σ i
    · rw [hs, Pi.single_eq_same, mul_one] at hc'
      exact ⟨hs.symm, hc'⟩
    · rw [Pi.single_eq_of_ne (Ne.symm hs), mul_zero] at hc'
      exact absurd hc' (hε i)
  exact ⟨Equiv.Perm.ext (fun i => (key i).1), funext (fun i => (key i).2)⟩

private noncomputable def ggWAutN_monoPerm {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (g : V ≃ₗ[ZMod 3] V) (hg : GGMonomialIn f g) : Equiv.Perm (Fin n) :=
  hg.choose

private noncomputable def ggWAutN_monoEps {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (g : V ≃ₗ[ZMod 3] V) (hg : GGMonomialIn f g) : Fin n → ZMod 3 :=
  hg.choose_spec.choose

private lemma ggWAutN_monoEps_ne {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (g : V ≃ₗ[ZMod 3] V) (hg : GGMonomialIn f g) :
    ∀ i, ggWAutN_monoEps f g hg i ≠ 0 :=
  hg.choose_spec.choose_spec.1

private lemma ggWAutN_monoPerm_spec {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (g : V ≃ₗ[ZMod 3] V) (hg : GGMonomialIn f g) :
    ∀ i, g (f i) = ggWAutN_monoEps f g hg i • f (ggWAutN_monoPerm f g hg i) :=
  hg.choose_spec.choose_spec.2

private lemma ggWAutN_mono_of_htype {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (htype : (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨
      (∀ g, g ∈ R ↔ GGMonomialEvenIn f g)) :
    ∀ g ∈ R, GGMonomialIn f g := by
  intro g hg
  rcases htype with h | h
  · exact (h g).mp hg
  · obtain ⟨σ, ε, hε, -, hact⟩ := (h g).mp hg
    exact ⟨σ, ε, hε, hact⟩

private lemma ggWAutN_zmod3_mul_self_all : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide

private lemma ggWAutN_zmod3_one_or_neg_one_all : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by
  decide

private lemma ggWAutN_zmod3_neg_one_ne_one : (-1 : ZMod 3) ≠ 1 := by decide

private noncomputable def ggWAutN_signChange {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (i : Fin n) : V ≃ₗ[ZMod 3] V :=
  Module.reflection (x := f i) (f := (2 : ZMod 3) • f.coord i) (by
    simp [LinearMap.smul_apply, Module.Basis.coord_apply])

private lemma ggWAutN_signChange_self {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (i : Fin n) : ggWAutN_signChange f i (f i) = - f i := by
  rw [ggWAutN_signChange, Module.reflection_apply]
  have hsc : ((2 : ZMod 3) • f.coord i) (f i) = 2 := by
    simp [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  rw [hsc]
  have h2 : (2 : ZMod 3) • (f i) = - f i := by
    rw [show (2 : ZMod 3) = -1 by decide]
    simp
  rw [h2, sub_neg_eq_add, ← two_smul (ZMod 3) (f i), h2]

private lemma ggWAutN_signChange_ne {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    {i j : Fin n} (hij : j ≠ i) : ggWAutN_signChange f i (f j) = f j := by
  rw [ggWAutN_signChange, Module.reflection_apply]
  have hz : ((2 : ZMod 3) • f.coord i) (f j) = 0 := by
    rw [LinearMap.smul_apply, Module.Basis.coord_apply, ggWAutN_repr_basis,
      Finsupp.single_eq_of_ne (Ne.symm hij), smul_zero]
  rw [hz, zero_smul, sub_zero]

private lemma ggWAutN_signChange_isRefl {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (i : Fin n) : IsReflLin (ggWAutN_signChange f i) :=
  ⟨f i, (2 : ZMod 3) • f.coord i, by
    simp [LinearMap.smul_apply, Module.Basis.coord_apply], rfl⟩

private lemma ggWAutN_signChange_prod {n : ℕ} (_f : Module.Basis (Fin n) (ZMod 3) V)
    (i : Fin n) : ∏ j, (if j = i then (-1 : ZMod 3) else 1) = -1 := by
  rw [Finset.prod_ite_eq']
  simp

private noncomputable def ggWAutN_piSmul {n : ℕ} (ε : Fin n → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) where
  toFun x := fun i => ε i * x i
  invFun x := fun i => (ε i)⁻¹ * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp [mul_left_comm]
  left_inv x := by
    ext i
    dsimp only
    rw [← mul_assoc, inv_mul_cancel₀ (hε i), one_mul]
  right_inv x := by
    ext i
    dsimp only
    rw [← mul_assoc, mul_inv_cancel₀ (hε i), one_mul]

private noncomputable def ggWAutN_diagMap {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (ε : Fin n → ZMod 3) (hε : ∀ i, ε i ≠ 0) : V ≃ₗ[ZMod 3] V :=
  f.equivFun.trans ((ggWAutN_piSmul ε hε).trans f.equivFun.symm)

private lemma ggWAutN_equivFun_diag {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (ε : Fin n → ZMod 3) (hε : ∀ i, ε i ≠ 0) (w : V) :
    f.equivFun (ggWAutN_diagMap f ε hε w) = fun i => ε i * f.equivFun w i := by
  rw [ggWAutN_diagMap, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rfl

private lemma ggWAutN_diagMap_apply {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (ε : Fin n → ZMod 3) (hε : ∀ i, ε i ≠ 0) (i : Fin n) :
    ggWAutN_diagMap f ε hε (f i) = ε i • f i := by
  apply f.equivFun.injective
  rw [ggWAutN_equivFun_diag, map_smul, ggWAutN_equivFun_basis]
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [Pi.single_eq_of_ne hj, Pi.smul_apply, Pi.single_eq_of_ne hj, mul_zero,
      smul_zero]

private def ggWAutN_twoSign {n : ℕ} (a k : Fin n) : Fin n → ZMod 3 :=
  fun i => if i = a ∨ i = k then -1 else 1

private lemma ggWAutN_twoSign_ne {n : ℕ} (a k : Fin n) :
    ∀ i, ggWAutN_twoSign a k i ≠ 0 := by
  intro i
  unfold ggWAutN_twoSign
  split_ifs <;> decide

private lemma ggWAutN_twoSign_eq {n : ℕ} {a k : Fin n} (hak : a ≠ k) (i : Fin n) :
    ggWAutN_twoSign a k i =
      (if i = a then (-1 : ZMod 3) else 1) * (if i = k then -1 else 1) := by
  unfold ggWAutN_twoSign
  by_cases hia : i = a <;> by_cases hik : i = k <;> simp_all

private lemma ggWAutN_twoSign_prod {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    {a k : Fin n} (hak : a ≠ k) : ∏ i, ggWAutN_twoSign a k i = 1 := by
  have hcongr : ∏ i, ggWAutN_twoSign a k i =
      ∏ i, ((if i = a then (-1 : ZMod 3) else 1) * (if i = k then -1 else 1)) :=
    Finset.prod_congr rfl (fun i _ => ggWAutN_twoSign_eq hak i)
  rw [hcongr, Finset.prod_mul_distrib, ggWAutN_signChange_prod f a,
    ggWAutN_signChange_prod f k]
  decide

private noncomputable def ggWAutN_permMap {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (τ : Equiv.Perm (Fin n)) : V ≃ₗ[ZMod 3] V :=
  f.repr.trans ((Finsupp.domLCongr τ).trans f.repr.symm)

private lemma ggWAutN_permMap_apply {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    ggWAutN_permMap f τ (f i) = f (τ i) := by
  simp only [ggWAutN_permMap, LinearEquiv.trans_apply]
  rw [ggWAutN_repr_basis, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_single, ← ggWAutN_repr_basis f (τ i),
    LinearEquiv.symm_apply_apply]

private lemma ggWAutN_permMap_mono {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (τ : Equiv.Perm (Fin n)) : GGMonomialIn f (ggWAutN_permMap f τ) :=
  ⟨τ, fun _ => 1, fun _ => one_ne_zero, fun i => by
    rw [ggWAutN_permMap_apply, one_smul]⟩

private lemma ggWAutN_permMap_even {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (τ : Equiv.Perm (Fin n)) : GGMonomialEvenIn f (ggWAutN_permMap f τ) :=
  ⟨τ, fun _ => 1, fun _ => one_ne_zero, by simp, fun i => by
    rw [ggWAutN_permMap_apply, one_smul]⟩

private lemma ggWAutN_permMap_mem_R {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (htype : (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨
      (∀ g, g ∈ R ↔ GGMonomialEvenIn f g)) (τ : Equiv.Perm (Fin n)) :
    ggWAutN_permMap f τ ∈ R := by
  rcases htype with hB | hD
  · exact (hB _).mpr (ggWAutN_permMap_mono f τ)
  · exact (hD _).mpr (ggWAutN_permMap_even f τ)

private noncomputable def ggWAutN_phi {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (htype : (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨
      (∀ g, g ∈ R ↔ GGMonomialEvenIn f g)) : R →* Equiv.Perm (Fin n) where
  toFun x := ggWAutN_monoPerm f (x : V ≃ₗ[ZMod 3] V)
    (ggWAutN_mono_of_htype f R htype x x.property)
  map_one' := by
    have hspec := ggWAutN_monoPerm_spec f ((1 : R) : V ≃ₗ[ZMod 3] V)
      (ggWAutN_mono_of_htype f R htype (1 : R) (1 : R).property)
    have huniq := ggWAutN_mono_unique f
      (ggWAutN_monoEps_ne f _ _)
      (fun _ => one_ne_zero) hspec
      (fun i => by
        show ((1 : R) : V ≃ₗ[ZMod 3] V) (f i) =
          (1 : ZMod 3) • f ((Equiv.refl (Fin n)) i)
        simp)
    rw [show (1 : Equiv.Perm (Fin n)) = Equiv.refl (Fin n) from rfl]
    exact huniq.1
  map_mul' x y := by
    have hx := ggWAutN_monoPerm_spec f (x : V ≃ₗ[ZMod 3] V)
      (ggWAutN_mono_of_htype f R htype x x.property)
    have hy := ggWAutN_monoPerm_spec f (y : V ≃ₗ[ZMod 3] V)
      (ggWAutN_mono_of_htype f R htype y y.property)
    have hxy := ggWAutN_monoPerm_spec f ((x * y : R) : V ≃ₗ[ZMod 3] V)
      (ggWAutN_mono_of_htype f R htype (x * y) (x * y).property)
    have hcomp : ∀ i, ((x * y : R) : V ≃ₗ[ZMod 3] V) (f i) =
        (ggWAutN_monoEps f (y : V ≃ₗ[ZMod 3] V) (ggWAutN_mono_of_htype f R htype y y.property) i *
          ggWAutN_monoEps f (x : V ≃ₗ[ZMod 3] V)
            (ggWAutN_mono_of_htype f R htype x x.property)
            (ggWAutN_monoPerm f (y : V ≃ₗ[ZMod 3] V)
              (ggWAutN_mono_of_htype f R htype y y.property) i)) •
          f ((ggWAutN_monoPerm f (x : V ≃ₗ[ZMod 3] V)
              (ggWAutN_mono_of_htype f R htype x x.property) *
            ggWAutN_monoPerm f (y : V ≃ₗ[ZMod 3] V)
              (ggWAutN_mono_of_htype f R htype y y.property)) i) := by
      intro i
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hy i, map_smul,
        hx (ggWAutN_monoPerm f (y : V ≃ₗ[ZMod 3] V)
          (ggWAutN_mono_of_htype f R htype y y.property) i)]
      rw [smul_smul, Equiv.Perm.mul_apply]
    have huniq := ggWAutN_mono_unique f
      (ggWAutN_monoEps_ne f ((x * y : R) : V ≃ₗ[ZMod 3] V)
        (ggWAutN_mono_of_htype f R htype (x * y) (x * y).property))
      (fun i => mul_ne_zero
        (ggWAutN_monoEps_ne f (y : V ≃ₗ[ZMod 3] V)
          (ggWAutN_mono_of_htype f R htype y y.property) i)
        (ggWAutN_monoEps_ne f (x : V ≃ₗ[ZMod 3] V)
          (ggWAutN_mono_of_htype f R htype x x.property) _))
      hxy hcomp
    exact huniq.1

private lemma ggWAutN_phi_surjective {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (htype : (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨
      (∀ g, g ∈ R ↔ GGMonomialEvenIn f g)) :
    Function.Surjective (ggWAutN_phi f R htype) := by
  intro τ
  refine ⟨⟨ggWAutN_permMap f τ, ggWAutN_permMap_mem_R f R htype τ⟩, ?_⟩
  have h := ggWAutN_mono_unique f
    (ggWAutN_monoEps_ne f (ggWAutN_permMap f τ)
      (ggWAutN_mono_of_htype f R htype (ggWAutN_permMap f τ)
        (ggWAutN_permMap_mem_R f R htype τ)))
    (fun _ => one_ne_zero)
    (ggWAutN_monoPerm_spec f (ggWAutN_permMap f τ)
      (ggWAutN_mono_of_htype f R htype (ggWAutN_permMap f τ)
        (ggWAutN_permMap_mem_R f R htype τ)))
    (fun i => by rw [ggWAutN_permMap_apply, one_smul])
  exact h.1

private lemma ggWAutN_perm_normal_invol_bot {n : ℕ} (hn : 5 ≤ n)
    (P : Subgroup (Equiv.Perm (Fin n))) [P.Normal] (hinv : ∀ x ∈ P, x * x = 1) :
    P = ⊥ := by
  by_contra hP
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  have hcard : 5 ≤ Nat.card (Fin n) := by simpa using hn
  have hAle : alternatingGroup (Fin n) ≤ P :=
    Equiv.Perm.alternatingGroup_le_of_normal hcard (inferInstance : Nontrivial P)
  have hinvA : ∀ x ∈ alternatingGroup (Fin n), x * x = 1 := fun x hx => hinv x (hAle hx)
  have hinvA' : ∀ x : alternatingGroup (Fin n), x * x = 1 := by
    intro x
    apply Subtype.ext
    rw [Subgroup.coe_mul, hinvA (x : Equiv.Perm (Fin n)) x.property, Subgroup.coe_one]
  have hcomm : IsMulCommutative (alternatingGroup (Fin n)) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxy : (x * y) * (x * y) = 1 := hinvA' (x * y)
    have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
    have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hinvA' x)
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hinvA' y)
    calc x * y = (x * y)⁻¹ := h1.symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hx, hy]
  have := hcomm
  have hbot : commutator (alternatingGroup (Fin n)) = ⊥ := commutator_eq_bot _
  have htop : commutator (alternatingGroup (Fin n)) = ⊤ := commutator_alternatingGroup_eq_top hcard
  have htriv : ∀ x : alternatingGroup (Fin n), x = 1 := by
    intro x
    have hx : x ∈ commutator (alternatingGroup (Fin n)) := by rw [htop]; trivial
    rw [hbot] at hx
    simpa using hx
  obtain ⟨x, y, hxy⟩ :=
    (alternatingGroup.nontrivial_of_three_le_card (by omega : 3 ≤ Nat.card (Fin n))).exists_pair_ne
  exact hxy ((htriv x).trans (htriv y).symm)

private lemma ggWAutN_normal_invol_le_Delta {n : ℕ} (hn : 5 ≤ n)
    (f : Module.Basis (Fin n) (ZMod 3) V) (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (htype : (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨
      (∀ g, g ∈ R ↔ GGMonomialEvenIn f g))
    (N : Subgroup (V ≃ₗ[ZMod 3] V)) (hNle : N ≤ R)
    (hNnorm : ∀ r ∈ R, ∀ x ∈ N, r * x * r⁻¹ ∈ N)
    (hinv : ∀ x ∈ N, x * x = 1) :
    N ≤ (ggWAutN_phi f R htype).ker.map R.subtype := by
  intro x hx
  let ψ : N →* Equiv.Perm (Fin n) := (ggWAutN_phi f R htype).comp (Subgroup.inclusion hNle)
  let P : Subgroup (Equiv.Perm (Fin n)) := ψ.range
  have hPnormal : P.Normal := by
    refine ⟨fun y hy τ => ?_⟩
    obtain ⟨y, hyN, rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨r, hr⟩ := ggWAutN_phi_surjective f R htype τ
    let w : V ≃ₗ[ZMod 3] V := (r : V ≃ₗ[ZMod 3] V) * (y : V ≃ₗ[ZMod 3] V) *
      (r : V ≃ₗ[ZMod 3] V)⁻¹
    have hw : w ∈ N := hNnorm r r.property y y.property
    refine MonoidHom.mem_range.mpr ⟨⟨w, hw⟩, ?_⟩
    have heq : Subgroup.inclusion hNle (⟨w, hw⟩ : N) =
        r * Subgroup.inclusion hNle y * r⁻¹ := by
      apply Subtype.ext
      rfl
    simp only [ψ, MonoidHom.comp_apply]
    rw [heq, map_mul, map_mul, map_inv, hr]
  have hinvP : ∀ y ∈ P, y * y = 1 := by
    intro y hy
    obtain ⟨y, hyN, rfl⟩ := MonoidHom.mem_range.mp hy
    have hyy : (y : V ≃ₗ[ZMod 3] V) * y = 1 := by
      simpa using hinv y y.property
    have hyyN : y * y = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hyy, Subgroup.coe_one]
    rw [← map_mul, hyyN, map_one]
  have hPbot : P = ⊥ := ggWAutN_perm_normal_invol_bot hn P hinvP
  have hx1 : ψ ⟨x, hx⟩ = 1 := by
    have : ψ ⟨x, hx⟩ ∈ P := MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
    rw [hPbot] at this
    simpa using this
  rw [Subgroup.mem_map]
  refine ⟨⟨x, hNle hx⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  exact hx1

private lemma ggWAutN_Delta_apply {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (htype : (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨
      (∀ g, g ∈ R ↔ GGMonomialEvenIn f g))
    {x : V ≃ₗ[ZMod 3] V} (hx : x ∈ (ggWAutN_phi f R htype).ker.map R.subtype) :
    ∃ ε : Fin n → ZMod 3, (∀ i, ε i ≠ 0) ∧ ∀ i, x (f i) = ε i • f i := by
  obtain ⟨y, hyker, rfl⟩ := Subgroup.mem_map.mp hx
  have hy1 : ggWAutN_phi f R htype y = 1 := by
    rwa [MonoidHom.mem_ker] at hyker
  refine ⟨ggWAutN_monoEps f (y : V ≃ₗ[ZMod 3] V)
      (ggWAutN_mono_of_htype f R htype y y.property),
    ggWAutN_monoEps_ne f (y : V ≃ₗ[ZMod 3] V)
      (ggWAutN_mono_of_htype f R htype y y.property), fun i => ?_⟩
  have hspec := ggWAutN_monoPerm_spec f (y : V ≃ₗ[ZMod 3] V)
    (ggWAutN_mono_of_htype f R htype y y.property) i
  have hperm : ggWAutN_monoPerm f (y : V ≃ₗ[ZMod 3] V)
      (ggWAutN_mono_of_htype f R htype y y.property) i = i := by
    have h := congrArg (fun p : Equiv.Perm (Fin n) => p i) hy1
    change ((ggWAutN_phi f R htype) y) i = i
    simpa using h
  change (y : V ≃ₗ[ZMod 3] V) (f i) =
    ggWAutN_monoEps f (y : V ≃ₗ[ZMod 3] V)
      (ggWAutN_mono_of_htype f R htype y y.property) i • f i
  rw [hspec, hperm]

private lemma ggWAutN_Delta_sq {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (htype : (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨
      (∀ g, g ∈ R ↔ GGMonomialEvenIn f g))
    {x : V ≃ₗ[ZMod 3] V} (hx : x ∈ (ggWAutN_phi f R htype).ker.map R.subtype) :
    x * x = 1 := by
  obtain ⟨ε, hε, hact⟩ := ggWAutN_Delta_apply f R htype hx
  have hbasis : ∀ i, (x * x) (f i) = f i := by
    intro i
    rw [LinearEquiv.mul_apply, hact i, map_smul, hact i, smul_smul,
      ggWAutN_zmod3_mul_self_all (ε i) (hε i), one_smul]
  apply LinearEquiv.ext
  intro v
  have hmap : (x * x : V →ₗ[ZMod 3] V) = 1 := by
    apply Module.Basis.ext f
    intro i
    change (x * x) (f i) = (1 : V ≃ₗ[ZMod 3] V) (f i)
    rw [hbasis i]
    rfl
  have := LinearMap.congr_fun hmap v
  simpa using this

private lemma ggWAutN_twoSign_mem_Delta {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (htype : (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨
      (∀ g, g ∈ R ↔ GGMonomialEvenIn f g))
    {a k : Fin n} (hak : a ≠ k) :
    ggWAutN_diagMap f (ggWAutN_twoSign a k) (ggWAutN_twoSign_ne a k) ∈
      (ggWAutN_phi f R htype).ker.map R.subtype := by
  have hmono : GGMonomialIn f
      (ggWAutN_diagMap f (ggWAutN_twoSign a k) (ggWAutN_twoSign_ne a k)) :=
    ⟨Equiv.refl _, ggWAutN_twoSign a k, ggWAutN_twoSign_ne a k, fun i => by
      rw [ggWAutN_diagMap_apply]; rfl⟩
  have heven : GGMonomialEvenIn f
      (ggWAutN_diagMap f (ggWAutN_twoSign a k) (ggWAutN_twoSign_ne a k)) :=
    ⟨Equiv.refl _, ggWAutN_twoSign a k, ggWAutN_twoSign_ne a k,
      ggWAutN_twoSign_prod f hak, fun i => by rw [ggWAutN_diagMap_apply]; rfl⟩
  have hR : ggWAutN_diagMap f (ggWAutN_twoSign a k) (ggWAutN_twoSign_ne a k) ∈ R := by
    rcases htype with hB | hD
    · exact (hB _).mpr hmono
    · exact (hD _).mpr heven
  rw [Subgroup.mem_map]
  refine ⟨⟨ggWAutN_diagMap f (ggWAutN_twoSign a k) (ggWAutN_twoSign_ne a k), hR⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  have h := ggWAutN_mono_unique f
    (ggWAutN_monoEps_ne f _ (ggWAutN_mono_of_htype f R htype _ hR))
    (ggWAutN_twoSign_ne a k)
    (ggWAutN_monoPerm_spec f _ (ggWAutN_mono_of_htype f R htype _ hR))
    (fun i => by
      show ggWAutN_diagMap f (ggWAutN_twoSign a k) (ggWAutN_twoSign_ne a k) (f i) =
        ggWAutN_twoSign a k i • f ((Equiv.refl (Fin n)) i)
      rw [ggWAutN_diagMap_apply, Equiv.refl_apply])
  rw [show (1 : Equiv.Perm (Fin n)) = Equiv.refl (Fin n) from rfl]
  exact h.1

private lemma ggWAutN_Delta_conj {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (htype : (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨
      (∀ g, g ∈ R ↔ GGMonomialEvenIn f g))
    (r : V ≃ₗ[ZMod 3] V) (hr : r ∈ R) {δ : V ≃ₗ[ZMod 3] V}
    (hδ : δ ∈ (ggWAutN_phi f R htype).ker.map R.subtype) :
    r * δ * r⁻¹ ∈ (ggWAutN_phi f R htype).ker.map R.subtype := by
  obtain ⟨δ', hδ'ker, hδ'eq⟩ := Subgroup.mem_map.mp hδ
  rw [← hδ'eq]
  rw [Subgroup.mem_map]
  refine ⟨⟨r * (δ' : V ≃ₗ[ZMod 3] V) * r⁻¹, ?_⟩, ?_, rfl⟩
  · exact R.mul_mem (R.mul_mem hr δ'.property) (R.inv_mem hr)
  · rw [MonoidHom.mem_ker] at hδ'ker ⊢
    have heq : (⟨r * (δ' : V ≃ₗ[ZMod 3] V) * r⁻¹,
        R.mul_mem (R.mul_mem hr δ'.property) (R.inv_mem hr)⟩ : R) =
        ⟨r, hr⟩ * δ' * ⟨r, hr⟩⁻¹ := by
      apply Subtype.ext
      simp [Subgroup.coe_mul]
    rw [heq, map_mul, map_mul, map_inv, hδ'ker, mul_one, mul_inv_cancel]

private lemma ggWAutN_support_subsingleton {n : ℕ} (hn : 3 ≤ n) {x : Fin n → ZMod 3}
    (h : ∀ a k : Fin n, a ≠ k → ∃ c : ZMod 3, ∀ i,
      ggWAutN_twoSign a k i * x i = c * x i) :
    ∃ j : Fin n, x = Pi.single j (x j) := by
  have hsupp : ∀ p q : Fin n, x p ≠ 0 → x q ≠ 0 → p = q := by
    intro p q hp hq
    by_contra hpq
    have hthird : ∃ k : Fin n, k ≠ p ∧ k ≠ q := by
      by_contra h
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ {p, q} := by
        intro k _
        by_cases hkp : k = p
        · rw [hkp]; simp
        · have hkq : k = q := by
            by_contra hkq
            exact h ⟨k, hkp, hkq⟩
          rw [hkq]; simp
      have hcard := Finset.card_le_card hsub
      have h2 : ({p, q} : Finset (Fin n)).card ≤ 2 :=
        (Finset.card_insert_le p {q}).trans (by simp)
      have : n ≤ 2 := by
        have := hcard.trans h2
        simpa using this
      omega
    obtain ⟨k, hkp, hkq⟩ := hthird
    have hak : p ≠ k := fun h => hkp h.symm
    obtain ⟨c, hc⟩ := h p k hak
    have hcp : c = -1 := by
      have hp1 : ggWAutN_twoSign p k p = -1 := by simp [ggWAutN_twoSign]
      have h1 := hc p
      rw [hp1] at h1
      have h1 := congrArg (fun t => t * (x p)⁻¹) h1
      rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hp, mul_one, mul_one] at h1
      exact h1.symm
    have hcq : c = 1 := by
      have hq1 : ggWAutN_twoSign p k q = 1 := by
        unfold ggWAutN_twoSign
        rw [if_neg]
        rintro (h | h)
        · exact hpq h.symm
        · exact hkq h.symm
      have h1 := hc q
      rw [hq1, one_mul] at h1
      have h1 := congrArg (fun t => t * (x q)⁻¹) h1
      rw [mul_assoc, mul_inv_cancel₀ hq, mul_one] at h1
      exact h1.symm
    exact absurd (hcp.symm.trans hcq) ggWAutN_zmod3_neg_one_ne_one
  by_cases hsome : ∃ j, x j ≠ 0
  · obtain ⟨j, hj⟩ := hsome
    refine ⟨j, ?_⟩
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · have hxi : x i = 0 := by
        by_contra hxi
        exact hi (hsupp i j hxi hj)
      rw [hxi]
      have h0 : (Pi.single j (x j) : Fin n → ZMod 3) i = 0 :=
        Pi.single_eq_of_ne (M := fun _ : Fin n => ZMod 3) hi (x j)
      exact h0.symm
  · have hsome' : ∀ j, x j = 0 := by
      intro j
      by_contra hj
      exact hsome ⟨j, hj⟩
    refine ⟨⟨0, by omega⟩, ?_⟩
    funext i
    rw [hsome' i, hsome' ⟨0, by omega⟩]
    by_cases hi : i = ⟨0, by omega⟩
    · subst hi; simp
    · rw [Pi.single_eq_of_ne hi]

private lemma ggWAutN_mem_span_of_eigen {n : ℕ} (hn : 3 ≤ n)
    (f : Module.Basis (Fin n) (ZMod 3) V) {w : V}
    (heig : ∀ a k : Fin n, a ≠ k → ∃ c : ZMod 3,
      ggWAutN_diagMap f (ggWAutN_twoSign a k) (ggWAutN_twoSign_ne a k) w = c • w) :
    ∃ j : Fin n, w ∈ Submodule.span (ZMod 3) ({f j} : Set V) := by
  have hcoord : ∀ a k : Fin n, a ≠ k → ∃ c : ZMod 3, ∀ i,
      ggWAutN_twoSign a k i * f.equivFun w i = c * f.equivFun w i := by
    intro a k hak
    obtain ⟨c, hc⟩ := heig a k hak
    refine ⟨c, fun i => ?_⟩
    have hh := congrArg f.equivFun hc
    rw [ggWAutN_equivFun_diag, map_smul] at hh
    have h := congrArg (fun y : Fin n → ZMod 3 => y i) hh
    simpa [Pi.smul_apply, smul_eq_mul] using h
  obtain ⟨j, hj⟩ := ggWAutN_support_subsingleton hn hcoord
  refine ⟨j, ?_⟩
  rw [Submodule.mem_span_singleton]
  refine ⟨f.equivFun w j, ?_⟩
  have hw : f.equivFun w j • f j = w := by
    apply f.equivFun.injective
    rw [map_smul, ggWAutN_equivFun_basis]
    rw [hj]
    ext i
    by_cases hi : i = j
    · subst hi; simp
    · rw [Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero,
        Pi.single_eq_of_ne hi]
  exact hw

theorem ggWAut_monomial_normalizer {n : ℕ} (hn : 5 ≤ n) (f : Module.Basis (Fin n) (ZMod 3) V)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (_habs : ZS.AbsIrred 3 R)
    (htype : (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨ (∀ g, g ∈ R ↔ GGMonomialEvenIn f g))
    (T : V ≃ₗ[ZMod 3] V) (hT : T ∈ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V))) :
    GGMonomialIn f T := by
  classical
  have hn3 : 3 ≤ n := by omega
  let Δ : Subgroup (V ≃ₗ[ZMod 3] V) := (ggWAutN_phi f R htype).ker.map R.subtype
  have hΔleR : ∀ δ ∈ Δ, δ ∈ R := by
    intro δ hδ
    obtain ⟨y, -, hδy⟩ := Subgroup.mem_map.mp hδ
    rw [← hδy]
    exact y.property
  have hle_of_conj : ∀ (S : V ≃ₗ[ZMod 3] V),
      S ∈ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V)) →
      ∀ δ ∈ Δ, S * δ * S⁻¹ ∈ Δ := by
    intro S hS δ hδ
    have hS' : ∀ h : V ≃ₗ[ZMod 3] V, h ∈ R ↔ S⁻¹ * h * S ∈ R := by
      have := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hS)
      simpa [mul_assoc] using this
    let N : Subgroup (V ≃ₗ[ZMod 3] V) := Δ.map (MulAut.conj S).toMonoidHom
    have hconj : ∀ δ : V ≃ₗ[ZMod 3] V,
        (MulEquiv.toMonoidHom (MulAut.conj S)) δ = S * δ * S⁻¹ := by
      intro δ
      exact MulAut.conj_apply S δ
    have hmemN : ∀ x, x ∈ N ↔ ∃ δ ∈ Δ, S * δ * S⁻¹ = x := by
      intro x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨δ, hδ, hδx⟩
        exact ⟨δ, hδ, by rw [hconj] at hδx; exact hδx⟩
      · rintro ⟨δ, hδ, rfl⟩
        exact ⟨δ, hδ, hconj δ⟩
    have hNle : N ≤ R := by
      intro x hx
      obtain ⟨δ, hδ, rfl⟩ := (hmemN x).mp hx
      exact (Subgroup.mem_normalizer_iff.mp hS δ).mp (hΔleR δ hδ)
    have hNnorm : ∀ r ∈ R, ∀ x ∈ N, r * x * r⁻¹ ∈ N := by
      intro r hr x hx
      obtain ⟨δ, hδ, rfl⟩ := (hmemN x).mp hx
      refine (hmemN _).mpr ⟨(S⁻¹ * r * S) * δ * (S⁻¹ * r * S)⁻¹,
        ggWAutN_Delta_conj f R htype (S⁻¹ * r * S) ((hS' r).mp hr) hδ, ?_⟩
      group
    have hinv : ∀ x ∈ N, x * x = 1 := by
      intro x hx
      obtain ⟨δ, hδ, rfl⟩ := (hmemN x).mp hx
      have hδ2 : δ * δ = 1 := ggWAutN_Delta_sq f R htype hδ
      calc (S * δ * S⁻¹) * (S * δ * S⁻¹) = S * (δ * δ) * S⁻¹ := by group
        _ = 1 := by rw [hδ2]; group
    exact ggWAutN_normal_invol_le_Delta hn f R htype N hNle hNnorm hinv
      ((hmemN _).mpr ⟨δ, hδ, rfl⟩)
  have hTinv : ∀ δ ∈ Δ, T⁻¹ * δ * T ∈ Δ :=
    hle_of_conj T⁻¹ (Subgroup.inv_mem _ hT)
  have heig : ∀ i : Fin n, ∃ j : Fin n, T (f i) ∈ Submodule.span (ZMod 3) ({f j} : Set V) := by
    intro i
    apply ggWAutN_mem_span_of_eigen hn3 f
    intro a k hak
    let d : V ≃ₗ[ZMod 3] V :=
      ggWAutN_diagMap f (ggWAutN_twoSign a k) (ggWAutN_twoSign_ne a k)
    have hd : d ∈ Δ := ggWAutN_twoSign_mem_Delta f R htype hak
    have hd' : T⁻¹ * d * T ∈ Δ := hTinv d hd
    obtain ⟨ε, -, hact⟩ := ggWAutN_Delta_apply f R htype hd'
    refine ⟨ε i, ?_⟩
    calc d (T (f i)) = T ((T⁻¹ * d * T) (f i)) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
          exact (LinearEquiv.apply_symm_apply T (d (T (f i)))).symm
      _ = T (ε i • f i) := by rw [hact i]
      _ = ε i • T (f i) := by rw [map_smul]
  let σ : Fin n → Fin n := fun i => Classical.choose (heig i)
  have hσ : ∀ i, T (f i) ∈ Submodule.span (ZMod 3) ({f (σ i)} : Set V) := fun i =>
    Classical.choose_spec (heig i)
  let ε : Fin n → ZMod 3 := fun i =>
    Classical.choose (Submodule.mem_span_singleton.mp (hσ i))
  have hεspec : ∀ i, ε i • f (σ i) = T (f i) := fun i =>
    Classical.choose_spec (Submodule.mem_span_singleton.mp (hσ i))
  have hεne : ∀ i, ε i ≠ 0 := by
    intro i h0
    have hTi : T (f i) ≠ 0 := by
      intro h
      exact (f.ne_zero i) (T.injective (by rw [h, map_zero]))
    exact hTi ((hεspec i).symm.trans (by rw [h0, zero_smul]))
  have hσinj : Function.Injective σ := by
    intro i i' hσeq
    by_contra hii
    have hzero : T (ε i' • f i - ε i • f i') = 0 := by
      rw [map_sub, map_smul, map_smul, ← hεspec i, ← hεspec i', hσeq,
        smul_smul, smul_smul, mul_comm (ε i') (ε i), sub_self]
    have hzV : ε i' • f i - ε i • f i' = 0 := by
      have := congrArg T.symm hzero
      rw [map_zero, LinearEquiv.symm_apply_apply] at this
      exact this
    have hrepr := congrArg f.repr hzV
    rw [map_zero, map_sub, map_smul, map_smul, ggWAutN_repr_basis,
      ggWAutN_repr_basis] at hrepr
    have hc := congrArg (fun y : Fin n →₀ ZMod 3 => y i) hrepr
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hii, smul_eq_mul, mul_one, mul_zero, sub_zero,
      Finsupp.zero_apply] at hc
    exact (hεne i') hc
  have hσbij : Function.Bijective σ :=
    ⟨hσinj, Finite.injective_iff_surjective.mp hσinj⟩
  exact ⟨Equiv.ofBijective σ hσbij, ε, hεne, fun i => (hεspec i).symm⟩

theorem ggWAut_monomial_mem {n : ℕ} (f : Module.Basis (Fin n) (ZMod 3) V)
    (A R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRA : R ≤ A) (hR : R = reflGp A)
    (htype : (∀ g, g ∈ R ↔ GGMonomialIn f g) ∨ (∀ g, g ∈ R ↔ GGMonomialEvenIn f g))
    {a : V ≃ₗ[ZMod 3] V} (ha : a ∈ A) (hmon : GGMonomialIn f a) : a ∈ R := by
  rcases htype with hB | hD
  · exact (hB a).mpr hmon
  · rcases hmon with ⟨σ, ε, hε, hact⟩
    by_cases hprod : ∏ i, ε i = 1
    · exact (hD a).mpr ⟨σ, ε, hε, hprod, hact⟩
    · exfalso
      have hne : ∏ i, ε i ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hε i)
      have hneg : ∏ i, ε i = -1 := by
        rcases ggWAutN_zmod3_one_or_neg_one_all _ hne with h | h
        · exact absurd h hprod
        · exact h
      have hn : 0 < n := by
        by_contra h
        have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
        subst hn0
        exact hprod (by simp)
      let i0 : Fin n := ⟨0, hn⟩
      let s : V ≃ₗ[ZMod 3] V := ggWAutN_signChange f i0
      have hs_apply : ∀ i, s (f i) =
          (if i = i0 then (-1 : ZMod 3) else 1) • f ((Equiv.refl (Fin n)) i) := by
        intro i
        change ggWAutN_signChange f i0 (f i) =
          (if i = i0 then (-1 : ZMod 3) else 1) • f ((Equiv.refl (Fin n)) i)
        by_cases hi : i = i0
        · subst hi; simp [ggWAutN_signChange_self]
        · rw [ggWAutN_signChange_ne f hi, if_neg hi, one_smul]
          rfl
      have hεs : ∀ i, (if i = i0 then (-1 : ZMod 3) else 1) ≠ 0 := by
        intro i; split_ifs <;> decide
      let r : V ≃ₗ[ZMod 3] V := s * a
      have hr_even : GGMonomialEvenIn f r := by
        refine ⟨σ, fun i => ε i * (if σ i = i0 then (-1 : ZMod 3) else 1), ?_, ?_, ?_⟩
        · intro i; exact mul_ne_zero (hε i) (hεs (σ i))
        · rw [Finset.prod_mul_distrib, hneg]
          have hcomp : ∏ i, (if σ i = i0 then (-1 : ZMod 3) else 1) = -1 := by
            rw [Equiv.prod_comp σ (fun i => if i = i0 then (-1 : ZMod 3) else 1)]
            exact ggWAutN_signChange_prod f i0
          rw [hcomp]
          decide
        · intro i
          rw [show r = s * a from rfl, LinearEquiv.mul_apply, hact i, map_smul,
            hs_apply (σ i), smul_smul, Equiv.refl_apply]
      have hrR : r ∈ R := (hD r).mpr hr_even
      have hrA : r ∈ A := hRA hrR
      have hsA : s ∈ A := by
        have hs_eq : s = r * a⁻¹ := by
          rw [show r = s * a from rfl, mul_assoc, mul_inv_cancel, mul_one]
        rw [hs_eq]
        exact A.mul_mem hrA (A.inv_mem ha)
      have hsR : s ∈ R := by
        have : s ∈ reflGp A := Subgroup.subset_closure ⟨hsA, ggWAutN_signChange_isRefl f i0⟩
        rwa [← hR] at this
      have hnotEven : ¬ GGMonomialEvenIn f s := by
        rintro ⟨τ, δ, hδ, hδprod, hδact⟩
        have huniq := ggWAutN_mono_unique f hδ hεs hδact hs_apply
        have hprodδ : ∏ i, δ i = -1 := by
          rw [huniq.2, ggWAutN_signChange_prod f i0]
        rw [hδprod] at hprodδ
        exact absurd hprodδ (Ne.symm ggWAutN_zmod3_neg_one_ne_one)
      exact hnotEven ((hD s).mp hsR)

end Imprim

theorem ggWAut_imprim {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (hn : 5 ≤ Module.finrank (ZMod 3) V) (A R : Subgroup (V ≃ₗ[ZMod 3] V)) (hRA : R ≤ A)
    (hR : R = reflGp A) (habs : ZS.AbsIrred 3 R)
    (himp : CFSG.Quasithin.SimsG4.IsImprimitiveOnV R) :
    ∀ a ∈ A, ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  intro a ha
  let n : ℕ := Module.finrank (ZMod 3) V
  have hn5 : 5 ≤ n := hn
  have hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r} := by
    rw [hR]
    exact ggWAut_reflGp_closure A
  obtain ⟨f, hfmono⟩ := ggWAut_imprim_frame (n := n) rfl R habs hgen himp
  have htype := ggWAut_monomial_type (n := n) hn5 f R habs hgen hfmono
  have ha_norm : a ∈ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hh' : h ∈ reflGp A := by rwa [hR] at hh
      have := ggWAut_reflGp_conj A ha hh'
      rwa [← hR] at this
    · intro hh
      have hh' : a * h * a⁻¹ ∈ reflGp A := by rwa [hR] at hh
      have := ggWAut_reflGp_conj A (A.inv_mem ha) hh'
      have heq : a⁻¹ * (a * h * a⁻¹) * (a⁻¹)⁻¹ = h := by group
      rw [heq] at this
      rwa [← hR] at this
  have hmono : GGMonomialIn f a :=
    ggWAut_monomial_normalizer hn5 f R habs htype a ha_norm
  exact ⟨a, ggWAut_monomial_mem f A R hRA hR htype ha hmono, Or.inl fun _ => rfl⟩

end CFSG.StandardType

end
