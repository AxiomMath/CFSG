module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDet
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public section

namespace CFSG.RankThree.CALinearPrimary

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

section Block

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

@[expose] noncomputable def linearSpecialBlock (x : LinearMap.GeneralLinearGroup k V)
    (h : k[X]) : Subgroup (LinearMap.GeneralLinearGroup k V) where
  carrier := {g | ∃ hg : g ∈ gl_centralizer x,
    (∀ j ∈ primaryFactors (x : Module.End k V), j ≠ h →
      ∀ v ∈ primaryComponent (x : Module.End k V) j, (g : Module.End k V) v = v) ∧
    LinearMap.det (commutantRestrict h
      ⟨(g : Module.End k V), mem_commutant_of_mem_gl_centralizer hg⟩) = 1}
  mul_mem' := by
    rintro g₁ g₂ ⟨hg₁, ht₁, hd₁⟩ ⟨hg₂, ht₂, hd₂⟩
    refine ⟨mul_mem hg₁ hg₂, fun j hj hjh v hv => ?_, ?_⟩
    · change (g₁ : Module.End k V) ((g₂ : Module.End k V) v) = v
      rw [ht₂ j hj hjh v hv, ht₁ j hj hjh v hv]
    · have hmul : commutantRestrict h ⟨((g₁ * g₂ : LinearMap.GeneralLinearGroup k V) :
          Module.End k V), mem_commutant_of_mem_gl_centralizer (mul_mem hg₁ hg₂)⟩ =
          commutantRestrict h ⟨(g₁ : Module.End k V), mem_commutant_of_mem_gl_centralizer hg₁⟩ *
            commutantRestrict h ⟨(g₂ : Module.End k V),
              mem_commutant_of_mem_gl_centralizer hg₂⟩ :=
        LinearMap.ext fun v => Subtype.ext rfl
      rw [hmul, map_mul, hd₁, hd₂, mul_one]
  one_mem' := by
    refine ⟨one_mem (gl_centralizer x), fun j _ _ v _ => rfl, ?_⟩
    have hone : commutantRestrict h ⟨((1 : LinearMap.GeneralLinearGroup k V) : Module.End k V),
        mem_commutant_of_mem_gl_centralizer (one_mem (gl_centralizer x))⟩ = 1 :=
      LinearMap.ext fun v => Subtype.ext rfl
    rw [hone, map_one]
  inv_mem' := by
    rintro g ⟨hg, ht, hd⟩
    refine ⟨inv_mem hg, fun j hj hjh v hv => ?_, ?_⟩
    · have h1 := ht j hj hjh v hv
      calc ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) v =
            ((g⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V)
              ((g : Module.End k V) v) := by rw [h1]
        _ = v := by
          change (((g⁻¹ * g : LinearMap.GeneralLinearGroup k V)) : Module.End k V) v = v
          rw [inv_mul_cancel]
          rfl
    · have hmul : commutantRestrict h ⟨((g⁻¹ : LinearMap.GeneralLinearGroup k V) :
          Module.End k V), mem_commutant_of_mem_gl_centralizer (inv_mem hg)⟩ *
          commutantRestrict h ⟨(g : Module.End k V), mem_commutant_of_mem_gl_centralizer hg⟩ =
            1 := by
        refine LinearMap.ext fun v => Subtype.ext ?_
        change (((g⁻¹ * g : LinearMap.GeneralLinearGroup k V)) : Module.End k V) v = v
        rw [inv_mul_cancel]
        rfl
      have h2 := congrArg LinearMap.det hmul
      rw [map_mul, hd, mul_one, map_one] at h2
      exact h2

theorem mem_linearSpecialBlock {x : LinearMap.GeneralLinearGroup k V} {h : k[X]}
    {g : LinearMap.GeneralLinearGroup k V} :
    g ∈ linearSpecialBlock x h ↔ ∃ hg : g ∈ gl_centralizer x,
      (∀ j ∈ primaryFactors (x : Module.End k V), j ≠ h →
        ∀ v ∈ primaryComponent (x : Module.End k V) j, (g : Module.End k V) v = v) ∧
      LinearMap.det (commutantRestrict h
        ⟨(g : Module.End k V), mem_commutant_of_mem_gl_centralizer hg⟩) = 1 :=
  Iff.rfl

theorem linearSpecialBlock_le_centralizer (x : LinearMap.GeneralLinearGroup k V) (h : k[X]) :
    linearSpecialBlock x h ≤ gl_centralizer x := fun _ hg => hg.1

theorem conj_mem_linearSpecialBlock {x : LinearMap.GeneralLinearGroup k V} {h : k[X]}
    {c : LinearMap.GeneralLinearGroup k V} (hc : c ∈ gl_centralizer x)
    {g : LinearMap.GeneralLinearGroup k V} (hg : g ∈ linearSpecialBlock x h) :
    c * g * c⁻¹ ∈ linearSpecialBlock x h := by
  obtain ⟨hgc, ht, hd⟩ := hg
  refine ⟨mul_mem (mul_mem hc hgc) (inv_mem hc), fun j hj hjh v hv => ?_, ?_⟩
  · have hcv : ((c⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) v ∈
        primaryComponent (x : Module.End k V) j :=
      apply_mem_primaryComponent (mem_gl_centralizer.mp (inv_mem hc)) hv
    change (c : Module.End k V) ((g : Module.End k V)
      (((c⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) v)) = v
    rw [ht j hj hjh _ hcv]
    change (((c * c⁻¹ : LinearMap.GeneralLinearGroup k V)) : Module.End k V) v = v
    rw [mul_inv_cancel]
    rfl
  · have hmul : commutantRestrict h ⟨((c * g * c⁻¹ : LinearMap.GeneralLinearGroup k V) :
        Module.End k V), mem_commutant_of_mem_gl_centralizer
          (mul_mem (mul_mem hc hgc) (inv_mem hc))⟩ =
        commutantRestrict h ⟨(c : Module.End k V), mem_commutant_of_mem_gl_centralizer hc⟩ *
          commutantRestrict h ⟨(g : Module.End k V), mem_commutant_of_mem_gl_centralizer hgc⟩ *
            commutantRestrict h ⟨((c⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V),
              mem_commutant_of_mem_gl_centralizer (inv_mem hc)⟩ :=
      LinearMap.ext fun v => Subtype.ext rfl
    have hinv : commutantRestrict h ⟨((c⁻¹ : LinearMap.GeneralLinearGroup k V) :
        Module.End k V), mem_commutant_of_mem_gl_centralizer (inv_mem hc)⟩ *
        commutantRestrict h ⟨(c : Module.End k V), mem_commutant_of_mem_gl_centralizer hc⟩ =
          1 := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      change (((c⁻¹ * c : LinearMap.GeneralLinearGroup k V)) : Module.End k V) v = v
      rw [inv_mul_cancel]
      rfl
    have h2 := congrArg LinearMap.det hinv
    rw [map_mul, map_one] at h2
    rw [hmul, map_mul, map_mul, hd, mul_one, mul_comm]
    exact h2

variable [FiniteDimensional k V] {x : LinearMap.GeneralLinearGroup k V}

theorem det_eq_one_of_mem_linearSpecialBlock (hsq : Squarefree (minpoly k (x : Module.End k V)))
    {h : k[X]} (hh : h ∈ primaryFactors (x : Module.End k V))
    {g : LinearMap.GeneralLinearGroup k V} (hg : g ∈ linearSpecialBlock x h) :
    LinearMap.det (g : Module.End k V) = 1 := by
  obtain ⟨hgc, ht, hd⟩ := hg
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  rw [det_eq_det_restrict_of_trivial_off hsq hh (mem_gl_centralizer.mp hgc) ht]
  have hres : ∀ hp : ∀ v ∈ primaryComponent (x : Module.End k V) h,
      (g : Module.End k V) v ∈ primaryComponent (x : Module.End k V) h,
      (g : Module.End k V).restrict hp = (commutantRestrict h
        ⟨(g : Module.End k V), mem_commutant_of_mem_gl_centralizer hgc⟩).restrictScalars k :=
    fun hp => LinearMap.ext fun v => rfl
  rw [hres, det_restrictScalars_blockGL, hd, map_one]

@[expose] noncomputable def linearSpecialBlockRestrict (x : LinearMap.GeneralLinearGroup k V)
    (h : k[X]) : linearSpecialBlock x h →*
      _root_.SpecialLinearGroup (AdjoinRoot h) (primaryComponent (x : Module.End k V) h) where
  toFun g := ⟨LinearEquiv.ofLinearMap
      (commutantRestrict h ⟨(g.1 : Module.End k V), mem_commutant_of_mem_gl_centralizer g.2.1⟩)
      (commutantRestrict h ⟨((g.1⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V),
        mem_commutant_of_mem_gl_centralizer (inv_mem g.2.1)⟩)
      (LinearMap.ext fun v => Subtype.ext (by
        change (((g.1 * g.1⁻¹ : LinearMap.GeneralLinearGroup k V)) : Module.End k V) v = v
        rw [mul_inv_cancel]
        rfl))
      (LinearMap.ext fun v => Subtype.ext (by
        change (((g.1⁻¹ * g.1 : LinearMap.GeneralLinearGroup k V)) : Module.End k V) v = v
        rw [inv_mul_cancel]
        rfl)),
    Units.ext (by rw [LinearEquiv.coe_det]; exact g.2.2.2)⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun _ => Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (LinearEquiv.ext fun _ => Subtype.ext rfl)

omit [FiniteDimensional k V] in
theorem coe_linearSpecialBlockRestrict {h : k[X]} (g : linearSpecialBlock x h)
    (v : primaryComponent (x : Module.End k V) h) :
    ((linearSpecialBlockRestrict x h g v : primaryComponent (x : Module.End k V) h) : V) =
      (g.1 : Module.End k V) v := rfl

theorem linearSpecialBlockRestrict_injective (hsq : Squarefree (minpoly k (x : Module.End k V)))
    {h : k[X]} : Function.Injective (linearSpecialBlockRestrict x h) := by
  rw [injective_iff_map_eq_one]
  intro g hg1
  apply Subtype.ext
  apply Units.ext
  refine ext_primaryComponent hsq fun j hj v hv => ?_
  by_cases hjh : j = h
  · subst hjh
    have h1 := congrArg (fun u : _root_.SpecialLinearGroup (AdjoinRoot j)
      (primaryComponent (x : Module.End k V) j) =>
        (((u : primaryComponent (x : Module.End k V) j ≃ₗ[AdjoinRoot j]
          primaryComponent (x : Module.End k V) j) ⟨v, hv⟩ :
            primaryComponent (x : Module.End k V) j) : V)) hg1
    exact h1
  · exact g.2.2.1 j hj hjh v hv

theorem linearSpecialBlockRestrict_surjective
    (hsq : Squarefree (minpoly k (x : Module.End k V))) {h : k[X]}
    (hh : h ∈ primaryFactors (x : Module.End k V)) :
    Function.Surjective (linearSpecialBlockRestrict x h) := by
  classical
  intro u
  set γ : blockGL (x : Module.End k V) h :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm u.1 with hγ
  set g := ((glCentralizerEquivPi hsq).symm (Pi.mulSingle ⟨h, hh⟩ γ) : gl_centralizer x)
    with hgdef
  have hgapp : ∀ (b : primaryFactors (x : Module.End k V)) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End k V) (b : k[X])),
      ((g : LinearMap.GeneralLinearGroup k V) : Module.End k V) v =
        blockApply ((Pi.mulSingle ⟨h, hh⟩ γ : (b : primaryFactors (x : Module.End k V)) →
          blockGL (x : Module.End k V) (b : k[X])) b) v hv := by
    intro b v hv
    rw [← blockApply_glCentralizerEquivPi hsq g b v hv, hgdef, MulEquiv.apply_symm_apply]
  have hgh : ∀ v (hv : v ∈ primaryComponent (x : Module.End k V) h),
      ((g : LinearMap.GeneralLinearGroup k V) : Module.End k V) v =
        ((u.1 ⟨v, hv⟩ : primaryComponent (x : Module.End k V) h) : V) := by
    intro v hv
    rw [hgapp ⟨h, hh⟩ v hv, Pi.mulSingle_eq_same]
    rfl
  have hmem : (g : LinearMap.GeneralLinearGroup k V) ∈ linearSpecialBlock x h := by
    refine ⟨g.2, fun j hj hjh v hv => ?_, ?_⟩
    · rw [hgapp ⟨j, hj⟩ v hv, Pi.mulSingle_eq_of_ne (fun h' => hjh (congrArg Subtype.val h'))]
      rfl
    · have heq : commutantRestrict h ⟨((g : LinearMap.GeneralLinearGroup k V) :
          Module.End k V), mem_commutant_of_mem_gl_centralizer g.2⟩ =
          ((u.1 : primaryComponent (x : Module.End k V) h ≃ₗ[AdjoinRoot h]
            primaryComponent (x : Module.End k V) h) :
              Module.End (AdjoinRoot h) (primaryComponent (x : Module.End k V) h)) :=
        LinearMap.ext fun v => Subtype.ext (hgh v v.2)
      rw [heq]
      exact u.det_eq_one
  exact ⟨⟨_, hmem⟩, Subtype.ext (LinearEquiv.ext fun v => Subtype.ext (hgh v v.2))⟩

theorem isQuasisimple_linearSpecialBlock [Finite k]
    (hsq : Squarefree (minpoly k (x : Module.End k V))) {h : k[X]}
    (hh : h ∈ primaryFactors (x : Module.End k V))
    (hm : 3 ≤ primaryMultiplicity (x : Module.End k V) h ∨
      (2 ≤ primaryMultiplicity (x : Module.End k V) h ∧ 4 ≤ Nat.card (AdjoinRoot h))) :
    CFSG.IsQuasisimple (linearSpecialBlock x h) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have : Finite (AdjoinRoot h) := Module.finite_of_finite k
  let b : Module.Basis (Fin (primaryMultiplicity (x : Module.End k V) h)) (AdjoinRoot h)
      (primaryComponent (x : Module.End k V) h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : linearSpecialBlock x h ≃*
      _root_.SpecialLinearGroup (AdjoinRoot h) (primaryComponent (x : Module.End k V) h) :=
    MulEquiv.ofBijective (linearSpecialBlockRestrict x h)
      ⟨linearSpecialBlockRestrict_injective hsq, linearSpecialBlockRestrict_surjective hsq hh⟩
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm) ?_
  rcases hm with hm | hm
  · exact CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup hm
  · exact CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hm.1 hm.2

theorem linearSpecialBlock_eq_bot (hsq : Squarefree (minpoly k (x : Module.End k V)))
    {h : k[X]} (hh : h ∈ primaryFactors (x : Module.End k V))
    (hm : primaryMultiplicity (x : Module.End k V) h = 1) : linearSpecialBlock x h = ⊥ := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  rw [eq_bot_iff]
  intro g hg
  let b : Module.Basis (Fin 1) (AdjoinRoot h) (primaryComponent (x : Module.End k V) h) :=
    Module.finBasisOfFinrankEq _ _ hm
  have h1 : linearSpecialBlockRestrict x h ⟨g, hg⟩ = 1 := by
    apply (Matrix.SpecialLinearGroup.toLin_equiv b).symm.injective
    rw [map_one]
    ext i j
    fin_cases i
    fin_cases j
    have := ((Matrix.SpecialLinearGroup.toLin_equiv b).symm
      (linearSpecialBlockRestrict x h ⟨g, hg⟩)).2
    rw [Matrix.det_fin_one] at this
    simpa using this
  have h2 := linearSpecialBlockRestrict_injective hsq (h1.trans (map_one _).symm)
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h2)

theorem exists_smul_of_commute_pow_char (hsq : Squarefree (minpoly k (x : Module.End k V)))
    {h : k[X]} (hh : h ∈ primaryFactors (x : Module.End k V)) {ℓ : ℕ} [CharP k ℓ]
    {y : LinearMap.GeneralLinearGroup k V} (hy : y ∈ gl_centralizer x)
    (hcomm : ∀ g ∈ linearSpecialBlock x h, g ^ ℓ = 1 → y * g = g * y) :
    ∃ c : AdjoinRoot h, ∀ v : primaryComponent (x : Module.End k V) h,
      (y : Module.End k V) v = ((c • v : primaryComponent (x : Module.End k V) h) : V) := by
  classical
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have : CharP (AdjoinRoot h) ℓ :=
    charP_of_injective_algebraMap (algebraMap k (AdjoinRoot h)).injective ℓ
  let b : Module.Basis (Fin (primaryMultiplicity (x : Module.End k V) h)) (AdjoinRoot h)
      (primaryComponent (x : Module.End k V) h) := Module.finBasisOfFinrankEq _ _ rfl
  set Y := commutantRestrict h ⟨(y : Module.End k V), mem_commutant_of_mem_gl_centralizer hy⟩
    with hYdef
  have hM : LinearMap.toMatrix b b Y ∈ Set.range (Matrix.scalar
      (Fin (primaryMultiplicity (x : Module.End k V) h))) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    obtain ⟨g, hg⟩ := linearSpecialBlockRestrict_surjective hsq hh
      (Matrix.SpecialLinearGroup.toLin_equiv b
        (Matrix.SpecialLinearGroup.transvection t.hij t.c))
    have hgℓ : g ^ ℓ = 1 := by
      apply linearSpecialBlockRestrict_injective hsq
      rw [map_pow, hg, ← map_pow, map_one]
      have h1 := CFSG.RankThree.CALinearPlane.transvection_pow_char (k := AdjoinRoot h) (ℓ := ℓ)
        t.hij t.c
      rw [pow_one] at h1
      rw [h1, map_one]
    have hyg := hcomm g.1 g.2 (by
      have := congrArg Subtype.val hgℓ
      rwa [Subgroup.coe_pow] at this)
    have hcomm' : Y * ((linearSpecialBlockRestrict x h g : _root_.SpecialLinearGroup
        (AdjoinRoot h) (primaryComponent (x : Module.End k V) h)) :
          Module.End (AdjoinRoot h) (primaryComponent (x : Module.End k V) h)) =
        ((linearSpecialBlockRestrict x h g : _root_.SpecialLinearGroup (AdjoinRoot h)
          (primaryComponent (x : Module.End k V) h)) :
            Module.End (AdjoinRoot h) (primaryComponent (x : Module.End k V) h)) * Y :=
      LinearMap.ext fun v => Subtype.ext
        (congrArg (fun z : LinearMap.GeneralLinearGroup k V => (z : Module.End k V) v) hyg)
    rw [hg, Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq] at hcomm'
    have h2 := congrArg (LinearMap.toMatrix b b) hcomm'
    rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, LinearMap.toMatrix_toLin] at h2
    exact h2.symm
  obtain ⟨c, hc⟩ := hM
  refine ⟨c, fun v => ?_⟩
  have hY : Y = c • LinearMap.id := by
    apply (LinearMap.toMatrix b b).injective
    rw [← hc, map_smul, LinearMap.toMatrix_id, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have h3 := congrArg (fun f : Module.End (AdjoinRoot h) (primaryComponent (x : Module.End k V) h)
    => ((f v : primaryComponent (x : Module.End k V) h) : V)) hY
  exact h3

theorem apply_eq_of_card_le_three [Finite k] (hsq : Squarefree (minpoly k (x : Module.End k V)))
    {h : k[X]} (hh : h ∈ primaryFactors (x : Module.End k V))
    (hm : primaryMultiplicity (x : Module.End k V) h = 2) (h3 : Nat.card (AdjoinRoot h) ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {v : LinearMap.GeneralLinearGroup k V}
    (hv : v ∈ gl_centralizer x) (hvp : v ^ p = 1) :
    ∀ w ∈ primaryComponent (x : Module.End k V) h, (v : Module.End k V) w = w := by
  classical
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have : Finite (AdjoinRoot h) := Module.finite_of_finite k
  have := Fintype.ofFinite (AdjoinRoot h)
  set γ := glCentralizerEquivPi hsq ⟨v, hv⟩ ⟨h, hh⟩ with hγ
  have hγp : γ ^ p = 1 := by
    have h1 : (⟨v, hv⟩ : gl_centralizer x) ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hvp)
    have h2 := congrArg (fun z => glCentralizerEquivPi hsq z ⟨h, hh⟩) h1
    simp only [map_pow, map_one, Pi.pow_apply, Pi.one_apply] at h2
    exact h2
  let b : Module.Basis (Fin 2) (AdjoinRoot h) (primaryComponent (x : Module.End k V) h) :=
    Module.finBasisOfFinrankEq _ _ hm
  have hcard : Nat.card (blockGL (x : Module.End k V) h) = Nat.card (GL (Fin 2) (AdjoinRoot h)) :=
    Nat.card_congr ((LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
      Matrix.GeneralLinearGroup.toLin.symm).toEquiv
  rw [Matrix.card_GL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero,
    pow_one] at hcard
  have hq2 : 2 ≤ Fintype.card (AdjoinRoot h) := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  have hq3 : Fintype.card (AdjoinRoot h) ≤ 3 := by rwa [← Nat.card_eq_fintype_card]
  have h48 : Nat.card (blockGL (x : Module.End k V) h) ∣ 48 := by
    rw [hcard]
    interval_cases (Fintype.card (AdjoinRoot h)) <;> norm_num
  have hord : orderOf γ = 1 := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hγp) with h1 | h1
    · exact h1
    · exfalso
      have hd := (orderOf_dvd_natCard γ).trans h48
      rw [h1, show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] at hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with h2 | h2
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
  have hγ1 : γ = 1 := orderOf_eq_one_iff.mp hord
  intro w hw
  rw [← blockApply_glCentralizerEquivPi hsq ⟨v, hv⟩ ⟨h, hh⟩ w hw]
  change blockApply γ w hw = w
  rw [hγ1]
  rfl

end Block

section Matrix

variable {n : ℕ} {k : Type*} [Field k]

variable (n k) in
@[expose] noncomputable def slGL :
    Matrix.SpecialLinearGroup (Fin n) k →* LinearMap.GeneralLinearGroup k (Fin n → k) :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL

theorem coe_slGL (g : Matrix.SpecialLinearGroup (Fin n) k) :
    ((slGL n k g : LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k)) =
      Matrix.toLin' (g : Matrix (Fin n) (Fin n) k) := rfl

theorem slGL_injective : Function.Injective (slGL n k) :=
  Matrix.GeneralLinearGroup.toLin.injective.comp Matrix.SpecialLinearGroup.toGL_injective

theorem mem_range_slGL {g : LinearMap.GeneralLinearGroup k (Fin n → k)}
    (hg : LinearMap.det (g : Module.End k (Fin n → k)) = 1) : g ∈ (slGL n k).range := by
  obtain ⟨A, rfl⟩ := Matrix.GeneralLinearGroup.toLin.surjective g
  have hA : (A : Matrix (Fin n) (Fin n) k).det = 1 := by
    rw [← LinearMap.det_toLin']
    exact hg
  exact ⟨⟨A, hA⟩, Units.ext rfl⟩

theorem squarefree_minpoly_slGL {p : ℕ} (hpk : (p : k) ≠ 0)
    {a : Matrix.SpecialLinearGroup (Fin n) k} (hap : a ^ p = 1) :
    Squarefree (minpoly k ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
      Module.End k (Fin n → k))) := by
  refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - C 1)
    (Polynomial.separable_X_pow_sub_C (1 : k) hpk one_ne_zero).squarefree ?_
  rw [map_sub, map_pow, aeval_X, aeval_C, map_one, ← Units.val_pow_eq_pow_val, ← map_pow, hap,
    map_one, Units.val_one, sub_self]

variable {a : Matrix.SpecialLinearGroup (Fin n) k}

theorem linearSpecialBlock_le_range_slGL
    (hsq : Squarefree (minpoly k ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
      Module.End k (Fin n → k))))
    {h : k[X]} (hh : h ∈ primaryFactors ((slGL n k a : LinearMap.GeneralLinearGroup k
      (Fin n → k)) : Module.End k (Fin n → k))) :
    linearSpecialBlock (slGL n k a) h ≤ (slGL n k).range := fun _ hg =>
  mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)

theorem comap_linearSpecialBlock_le_centralizer (h : k[X]) :
    (linearSpecialBlock (slGL n k a) h).comap (slGL n k) ≤ Subgroup.centralizer {a} := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply slGL_injective
  rw [map_mul, map_mul]
  exact Units.ext (mem_gl_centralizer.mp (linearSpecialBlock_le_centralizer _ _ hg)).eq

theorem conj_mem_comap_linearSpecialBlock {h : k[X]}
    {c : Matrix.SpecialLinearGroup (Fin n) k} (hc : c ∈ Subgroup.centralizer {a})
    {g : Matrix.SpecialLinearGroup (Fin n) k}
    (hg : g ∈ (linearSpecialBlock (slGL n k a) h).comap (slGL n k)) :
    c * g * c⁻¹ ∈ (linearSpecialBlock (slGL n k a) h).comap (slGL n k) := by
  have hc' : slGL n k c ∈ gl_centralizer (slGL n k a) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← map_mul, ← map_mul, hc]
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact conj_mem_linearSpecialBlock hc' hg

theorem comap_linearSpecialBlock_mulEquiv
    (hsq : Squarefree (minpoly k ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
      Module.End k (Fin n → k))))
    {h : k[X]} (hh : h ∈ primaryFactors ((slGL n k a : LinearMap.GeneralLinearGroup k
      (Fin n → k)) : Module.End k (Fin n → k))) :
    Nonempty ((linearSpecialBlock (slGL n k a) h).comap (slGL n k) ≃*
      linearSpecialBlock (slGL n k a) h) := by
  refine ⟨(Subgroup.equivMapOfInjective _ (slGL n k) slGL_injective).trans
    (MulEquiv.subgroupCongr ?_)⟩
  rw [Subgroup.map_comap_eq, inf_eq_right]
  exact fun _ hg => mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)

end Matrix

section Projective

open CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.RankThree.RegularUnipotent CFSG.RankThree.LinearPointwise

variable {n : ℕ} {k : Type*} [Field k]

theorem conj_eq_of_proj_eq_of_scalars {p : ℕ} (hZ : ∀ z ∈ scalars n k, z ^ p = 1 → z = 1)
    {a g : Matrix.SpecialLinearGroup (Fin n) k} (hap : a ^ p = 1)
    (h : proj n k (g * a * g⁻¹) = proj n k a) : g * a * g⁻¹ = a := by
  rw [proj_eq_proj_iff] at h
  set z := (g * a * g⁻¹)⁻¹ * a with hz
  have hzc : z ∈ Subgroup.center _ := scalars_le_center n k h
  have ha : a = g * a * g⁻¹ * z := by rw [hz, mul_inv_cancel_left]
  have hzp : z ^ p = 1 := by
    have h1 : (g * a * g⁻¹ * z) ^ p = (g * a * g⁻¹) ^ p * z ^ p :=
      Commute.mul_pow (Subgroup.mem_center_iff.mp hzc _) p
    rw [← ha, hap, conj_pow, hap, mul_one, mul_inv_cancel, one_mul] at h1
    exact h1.symm
  rw [hZ z h hzp, mul_one] at ha
  exact ha.symm

theorem mul_comm_of_mem_elementaryAbelian {G : Type*} [Group G] {p : ℕ} {A : Subgroup G}
    [IsElementaryAbelian p A] {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val ((inferInstance : IsMulCommutative A).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

variable {T : Type*} [Group T]

theorem map_centralizer_eq_inf (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    (x : T) : (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T) =
      (MulAut.conj : T →* MulAut T).range ⊓ Subgroup.centralizer {MulAut.conj x} := by
  refine le_antisymm (map_centralizer_le le_rfl x) fun c hc => ?_
  exact mem_map_centralizer_of_mem_range hinj hc.1
    (Subgroup.mem_centralizer_singleton_iff.mp hc.2)

theorem isComponent_of_quasisimple (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    {B : Subgroup (MulAut T)} (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (x : T)
    {J : Subgroup (MulAut T)} (hJq : CFSG.IsQuasisimple J)
    (hJC : J ≤ (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T))
    (hJn : ∀ c ∈ (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T), ∀ j ∈ J,
      c * j * c⁻¹ ∈ J) :
    J ≤ B ⊓ Subgroup.centralizer {MulAut.conj x} ∧
      CFSG.IsComponent (J.subgroupOf (B ⊓ Subgroup.centralizer {MulAut.conj x})) := by
  set L := B ⊓ Subgroup.centralizer {MulAut.conj x} with hL
  set C := (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T) with hC
  have hCL : C ≤ L := map_centralizer_le hB x
  have hJL : J ≤ L := hJC.trans hCL
  have hJ'q : CFSG.IsQuasisimple (J.subgroupOf L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL).symm hJq
  have hCn : (C.subgroupOf L).Normal := by
    refine ⟨fun c hc b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    have hb : (b : MulAut T) * MulAut.conj x = MulAut.conj x * b :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp b.2).2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using conj_mem_map_centralizer hinj hb hc
  have hJ'sub : (J.subgroupOf L).IsSubnormal := by
    refine Subgroup.IsSubnormal.step _ (C.subgroupOf L) (Subgroup.subgroupOf_mono L hJC)
      hCn.isSubnormal ⟨fun j hj c => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hj ⊢
    have hc : ((c : L) : MulAut T) ∈ C := Subgroup.mem_subgroupOf.mp c.2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hJn _ hc _ hj
  exact ⟨hJL, hJ'q, hJ'sub⟩

variable [Finite k]

theorem linearSpecialBlock_image_component {p : ℕ} (hp : p.Prime) (hn3 : 3 ≤ n)
    (hZ : ∀ z ∈ scalars n k, z ^ p = 1 → z = 1) {B : Subgroup (MulAut (projectiveSL n k))}
    (hB : (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ≤ B)
    {a : Matrix.SpecialLinearGroup (Fin n) k} (hap : a ^ p = 1)
    (hsq : Squarefree (minpoly k ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
      Module.End k (Fin n → k))))
    {h : k[X]} (hh : h ∈ primaryFactors ((slGL n k a : LinearMap.GeneralLinearGroup k
      (Fin n → k)) : Module.End k (Fin n → k)))
    (hgood : 3 ≤ primaryMultiplicity ((slGL n k a : LinearMap.GeneralLinearGroup k
        (Fin n → k)) : Module.End k (Fin n → k)) h ∨
      (2 ≤ primaryMultiplicity ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
        Module.End k (Fin n → k)) h ∧ 4 ≤ Nat.card (AdjoinRoot h))) :
    ((linearSpecialBlock (slGL n k a) h).comap (slGL n k)).map
        ((MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).comp (proj n k)) ≤
      (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ⊓
        Subgroup.centralizer {MulAut.conj (proj n k a)} ∧
    (∀ c ∈ (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ⊓
        Subgroup.centralizer {MulAut.conj (proj n k a)},
      ∀ j ∈ ((linearSpecialBlock (slGL n k a) h).comap (slGL n k)).map
        ((MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).comp (proj n k)),
        c * j * c⁻¹ ∈ ((linearSpecialBlock (slGL n k a) h).comap (slGL n k)).map
          ((MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).comp (proj n k))) ∧
    ((linearSpecialBlock (slGL n k a) h).comap (slGL n k)).map
        ((MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).comp (proj n k)) ≤
      B ⊓ Subgroup.centralizer {MulAut.conj (proj n k a)} ∧
    CFSG.IsComponent ((((linearSpecialBlock (slGL n k a) h).comap (slGL n k)).map
        ((MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).comp (proj n k))).subgroupOf
      (B ⊓ Subgroup.centralizer {MulAut.conj (proj n k a)})) ∧
    ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer {MulAut.conj (proj n k a)}),
      ∀ j ∈ ((linearSpecialBlock (slGL n k a) h).comap (slGL n k)).map
        ((MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).comp (proj n k)),
        s * j = j * s := by
  have hinj := conj_injective_projectiveSL (k := k) hn3
  set φ := (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).comp (proj n k)
    with hφ
  set F := (linearSpecialBlock (slGL n k a) h).comap (slGL n k) with hF
  set C := (Subgroup.centralizer {proj n k a}).map
    (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)) with hC
  have hCeq := map_centralizer_eq_inf hinj (proj n k a)
  obtain ⟨eF⟩ := comap_linearSpecialBlock_mulEquiv hsq hh
  have hFq : CFSG.IsQuasisimple F := CFSG.LocalCores.isQuasisimple_of_mulEquiv eF.symm
    (isQuasisimple_linearSpecialBlock hsq hh hgood)
  have hJq : CFSG.IsQuasisimple (F.map φ) := by
    refine CFSG.LocalCores.isQuasisimple_map hFq φ fun hle => ?_
    have hFc : ∀ g ∈ F, g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) :=
      fun g hg => by
        have h1 : proj n k g = 1 := hinj (by rw [map_one]; exact hle hg)
        exact scalars_le_center n k (proj_eq_one_iff.mp h1)
    have hZF : Subgroup.center F = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_center_iff]
      intro g'
      exact Subtype.ext ((Subgroup.mem_center_iff.mp (hFc g g.2)) g')
    obtain ⟨u, w, huw⟩ := hFq.2.2
    apply huw
    induction u using QuotientGroup.induction_on with
    | H u =>
      induction w using QuotientGroup.induction_on with
      | H w =>
        rw [(QuotientGroup.eq_one_iff u).mpr (by rw [hZF]; exact Subgroup.mem_top u),
          (QuotientGroup.eq_one_iff w).mpr (by rw [hZF]; exact Subgroup.mem_top w)]
  have hJC : F.map φ ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨proj n k g, ?_, rfl⟩
    have hga := Subgroup.mem_centralizer_singleton_iff.mp
      (comap_linearSpecialBlock_le_centralizer h hg)
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hga]
  have hJn : ∀ c ∈ C, ∀ j ∈ F.map φ, c * j * c⁻¹ ∈ F.map φ := by
    rintro _ ⟨y', hy', rfl⟩ _ ⟨g, hg, rfl⟩
    obtain ⟨y, rfl⟩ := proj_surjective n k y'
    have hy : y ∈ Subgroup.centralizer {a} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : proj n k (y * a * y⁻¹) = proj n k a := by
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy'
        rw [map_mul, map_mul, map_inv, hy', mul_inv_cancel_right]
      have h2 := conj_eq_of_proj_eq_of_scalars hZ hap h1
      calc y * a = y * a * y⁻¹ * y := by group
        _ = a * y := by rw [h2]
    refine ⟨y * g * y⁻¹, conj_mem_comap_linearSpecialBlock hy hg, ?_⟩
    simp only [hφ, MonoidHom.comp_apply, map_mul, map_inv]
  obtain ⟨hJL, hJcomp⟩ := isComponent_of_quasisimple hinj hB (proj n k a) hJq hJC hJn
  refine ⟨hJC.trans hCeq.le, fun c hc j hj => hJn c (hCeq.ge hc) j hj, hJL, hJcomp,
    core_commute_of_quasisimple hp hinj hB (proj n k a) hJq hJC hJn⟩

theorem core_commute_elementaryAbelian {p ℓ : ℕ} (hp : p.Prime) (hp3 : 3 < p) [Fact ℓ.Prime]
    [CharP k ℓ] (hn3 : 3 ≤ n) (hpk : (p : k) ≠ 0) (hZ : ∀ z ∈ scalars n k, z ^ p = 1 → z = 1)
    (E₀ : Subgroup (Matrix.SpecialLinearGroup (Fin n) k)) [IsElementaryAbelian p E₀]
    {B : Subgroup (MulAut (projectiveSL n k))}
    (hB : (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ≤ B)
    {a : Matrix.SpecialLinearGroup (Fin n) k} (haE : a ∈ E₀) :
    ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer {MulAut.conj (proj n k a)}),
      ∀ v ∈ E₀, s * MulAut.conj (proj n k v) = MulAut.conj (proj n k v) * s := by
  classical
  have hinj := conj_injective_projectiveSL (k := k) hn3
  have hn0 : 0 < n := by omega
  set T := projectiveSL n k with hT
  set φ : Matrix.SpecialLinearGroup (Fin n) k →* MulAut T :=
    (MulAut.conj : T →* MulAut T).comp (proj n k) with hφ
  have hφapp : ∀ g, φ g = MulAut.conj (proj n k g) := fun _ => rfl
  set x := proj n k a with hx
  set L := B ⊓ Subgroup.centralizer {MulAut.conj x} with hL
  set S := inSubgroup (aschbacherSolvableCore p) L with hS
  set C := (Subgroup.centralizer {x}).map (MulAut.conj : T →* MulAut T) with hC
  have hCeq := map_centralizer_eq_inf hinj x
  have hpow : ∀ v ∈ E₀, v ^ p = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
  have hap := hpow a haE
  have hsq := squarefree_minpoly_slGL hpk hap
  set X : Module.End k (Fin n → k) :=
    ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k))
    with hX
  have hliftC : ∀ c ∈ C, ∃ y, y ∈ Subgroup.centralizer {a} ∧ c = φ y := by
    rintro _ ⟨y', hy', rfl⟩
    obtain ⟨y, rfl⟩ := proj_surjective n k y'
    refine ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : proj n k (y * a * y⁻¹) = proj n k a := by
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy'
      rw [map_mul, map_mul, map_inv, ← hx, hy', mul_inv_cancel_right]
    have h2 := conj_eq_of_proj_eq_of_scalars hZ hap h1
    calc y * a = y * a * y⁻¹ * y := by group
      _ = a * y := by rw [h2]
  have hmapC : ∀ y ∈ Subgroup.centralizer {a}, φ y ∈ C := by
    intro y hy
    refine ⟨proj n k y, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]
  have hglC : ∀ y ∈ Subgroup.centralizer {a}, slGL n k y ∈ gl_centralizer (slGL n k a) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← map_mul, ← map_mul, hy]
  set good : k[X] → Prop := fun h => 3 ≤ primaryMultiplicity X h ∨
    (2 ≤ primaryMultiplicity X h ∧ 4 ≤ Nat.card (AdjoinRoot h)) with hgooddef
  have hcomp := fun (h : k[X]) (hh : h ∈ primaryFactors X) (hg : good h) =>
    linearSpecialBlock_image_component hp hn3 hZ hB hap hsq hh hg
  set W : Set (MulAut T) := {w | ∃ h ∈ primaryFactors X, good h ∧
    w ∈ ((linearSpecialBlock (slGL n k a) h).comap (slGL n k)).map φ} with hW
  set Q := C ⊓ Subgroup.centralizer W with hQ
  intro s hs v hv
  have hvcomm : v ∈ Subgroup.centralizer {a} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_comm_of_mem_elementaryAbelian (p := p) hv haE
  have hbC : φ v ∈ C := hmapC v hvcomm
  have hbL : φ v ∈ L := map_centralizer_le hB x hbC
  have : Finite (MulAut T) :=
    Finite.of_injective (fun α : MulAut T => (α : T → T)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hchar := solvable_prime_complement_core_characterization (H := L) hp
  have hSfin : Finite S := inferInstance
  have hScard : ¬ p ∣ Nat.card S := by
    rw [hS, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
    exact hchar.2.2.1
  have hSn : ∀ s ∈ S, φ v * s * (φ v)⁻¹ ∈ S := by
    rintro _ ⟨s', hs', rfl⟩
    refine ⟨⟨φ v, hbL⟩ * s' * ⟨φ v, hbL⟩⁻¹, ?_, rfl⟩
    exact (@Subgroup.normal_of_characteristic _ _ _ hchar.2.1).conj_mem s' hs' _
  refine (commute_of_conj_mul_mem hp (S := S) (Q := Q) hScard (b := φ v)
    (by rw [← map_pow, hpow v hv, map_one]) hSn ?_ ?_ s hs).symm
  · intro s' hs'
    refine ⟨core_conj_mul_mem_map_centralizer hinj hB hbC hs',
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro w ⟨h, hh, hg, hw⟩
    have h1 := (hcomp h hh hg).2.2.2.2 s' hs' w hw
    have hw' : (φ v)⁻¹ * w * φ v ∈
        ((linearSpecialBlock (slGL n k a) h).comap (slGL n k)).map φ := by
      have := (hcomp h hh hg).2.1 (φ v)⁻¹ (hCeq.le (inv_mem hbC)) w hw
      rwa [inv_inv] at this
    have h2 := (hcomp h hh hg).2.2.2.2 s' hs' _ hw'
    have h3 : φ v * s' * (φ v)⁻¹ * w = w * (φ v * s' * (φ v)⁻¹) := by
      calc φ v * s' * (φ v)⁻¹ * w = φ v * (s' * ((φ v)⁻¹ * w * φ v)) * (φ v)⁻¹ := by group
        _ = φ v * (((φ v)⁻¹ * w * φ v) * s') * (φ v)⁻¹ := by rw [h2]
        _ = w * (φ v * s' * (φ v)⁻¹) := by group
    calc w * (s'⁻¹ * (φ v * s' * (φ v)⁻¹)) = s'⁻¹ * (s' * w * s'⁻¹) * (φ v * s' * (φ v)⁻¹) := by
          group
      _ = s'⁻¹ * (w * s' * s'⁻¹) * (φ v * s' * (φ v)⁻¹) := by rw [h1]
      _ = s'⁻¹ * (w * (φ v * s' * (φ v)⁻¹)) := by group
      _ = s'⁻¹ * (φ v * s' * (φ v)⁻¹ * w) := by rw [h3]
      _ = s'⁻¹ * (φ v * s' * (φ v)⁻¹) * w := by group
  · rintro c ⟨hcC, hcW⟩
    obtain ⟨y, hy, rfl⟩ := hliftC c hcC
    have hyG := hglC y hy
    have hvG := hglC v hvcomm
    have hvp : slGL n k v ^ p = 1 := by rw [← map_pow, hpow v hv, map_one]
    have hyv : y * v = v * y := by
      apply slGL_injective
      rw [map_mul, map_mul]
      apply Units.ext
      refine ext_primaryComponent hsq fun j hj w hw => ?_
      change ((slGL n k y : LinearMap.GeneralLinearGroup k (Fin n → k)) :
          Module.End k (Fin n → k)) (((slGL n k v : LinearMap.GeneralLinearGroup k
            (Fin n → k)) : Module.End k (Fin n → k)) w) =
        ((slGL n k v : LinearMap.GeneralLinearGroup k (Fin n → k)) :
          Module.End k (Fin n → k)) (((slGL n k y : LinearMap.GeneralLinearGroup k
            (Fin n → k)) : Module.End k (Fin n → k)) w)
      have hvw : ((slGL n k v : LinearMap.GeneralLinearGroup k (Fin n → k)) :
          Module.End k (Fin n → k)) w ∈ primaryComponent X j :=
        apply_mem_primaryComponent (mem_gl_centralizer.mp hvG) hw
      have hyw : ((slGL n k y : LinearMap.GeneralLinearGroup k (Fin n → k)) :
          Module.End k (Fin n → k)) w ∈ primaryComponent X j :=
        apply_mem_primaryComponent (mem_gl_centralizer.mp hyG) hw
      have hm1 : 1 ≤ primaryMultiplicity X j := by
        have : Fact (Irreducible j) := ⟨irreducible_of_mem_primaryFactors hj⟩
        have hnt : Nontrivial (primaryComponent X j) :=
          Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hj)
        exact Module.finrank_pos
      by_cases hscal : good j ∨ primaryMultiplicity X j = 1
      ·
        have hcomm : ∀ g ∈ linearSpecialBlock (slGL n k a) j, g ^ ℓ = 1 →
            slGL n k y * g = g * slGL n k y := by
          intro g hg hgℓ
          rcases hscal with hgood | hone
          · obtain ⟨g₀, rfl⟩ := linearSpecialBlock_le_range_slGL hsq hj hg
            have hg₀ℓ : g₀ ^ ℓ ^ 1 = 1 := by
              rw [pow_one]
              apply slGL_injective
              rw [map_pow, hgℓ, map_one]
            have hcw := Subgroup.mem_centralizer_iff.mp hcW (φ g₀) ⟨j, hj, hgood, g₀, hg, rfl⟩
            have hprojc : proj n k (y * g₀ * y⁻¹) = proj n k g₀ := by
              have h1 : MulAut.conj (proj n k (g₀ * y)) = MulAut.conj (proj n k (y * g₀)) := by
                rw [map_mul, map_mul, map_mul, map_mul]
                exact hcw
              have h2 := hinj h1
              rw [map_mul, ← h2, map_mul, map_inv, mul_inv_cancel_right]
            have hconj := eq_of_proj_eq_of_pow_eq_one (p := ℓ) hn0
              (MulAut.conj y).toMonoidHom hg₀ℓ hprojc
            have hyg : y * g₀ = g₀ * y := by
              have : y * g₀ * y⁻¹ = g₀ := hconj
              calc y * g₀ = y * g₀ * y⁻¹ * y := by group
                _ = g₀ * y := by rw [this]
            rw [← map_mul, ← map_mul, hyg]
          · rw [linearSpecialBlock_eq_bot hsq hj hone, Subgroup.mem_bot] at hg
            rw [hg, mul_one, one_mul]
        obtain ⟨c, hc⟩ := exists_smul_of_commute_pow_char hsq hj hyG hcomm
        have hlin : ∀ u : primaryComponent X j,
            ((slGL n k v : LinearMap.GeneralLinearGroup k (Fin n → k)) :
              Module.End k (Fin n → k)) ((c • u : primaryComponent X j) : Fin n → k) =
            ((c • (⟨((slGL n k v : LinearMap.GeneralLinearGroup k (Fin n → k)) :
              Module.End k (Fin n → k)) u, apply_mem_primaryComponent
                (mem_gl_centralizer.mp hvG) u.2⟩ : primaryComponent X j) :
                  primaryComponent X j) : Fin n → k) := by
          intro u
          have := map_smul (commutantRestrict j ⟨((slGL n k v : LinearMap.GeneralLinearGroup k
            (Fin n → k)) : Module.End k (Fin n → k)), mem_commutant_of_mem_gl_centralizer hvG⟩) c u
          exact congrArg Subtype.val this
        rw [hc ⟨_, hvw⟩, hc ⟨w, hw⟩, hlin ⟨w, hw⟩]
      ·
        have hm2 : primaryMultiplicity X j = 2 := by
          simp only [hgooddef, not_or, not_and, not_le] at hscal
          omega
        have h3 : Nat.card (AdjoinRoot j) ≤ 3 := by
          simp only [hgooddef, not_or, not_and, not_le] at hscal
          have := hscal.1.2 (by omega)
          omega
        have hvtriv := apply_eq_of_card_le_three hsq hj hm2 h3 hp hp3 hvG hvp
        rw [hvtriv w hw, hvtriv _ hyw]
    show φ v * φ y = φ y * φ v
    rw [← map_mul, ← map_mul, hyv]

end Projective

end CFSG.RankThree.CALinearPrimary
