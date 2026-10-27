module

public import CFSG.RankThree.PartTwo.Census.LinearRank
public import CFSG.LieType.BorelTits.FormFlag
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LieType.BorelTits.CentralQuotient
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Census

open Matrix

section TwoByTwo

variable {K : Type*} [Field K] [CharP K 2]

theorem trace_eq_one_of_pow_three {Y : Matrix (Fin 2) (Fin 2) K} (hY : Y.det = 1)
    (h3 : Y * Y * Y = 1) (h1 : Y ≠ 1) : Y.trace = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [det_fin_two] at hY
  rw [trace_fin_two]
  set a := Y 0 0
  set b := Y 0 1
  set c := Y 1 0
  set d := Y 1 1
  have e00 := congrFun (congrFun h3 0) 0
  have e01 := congrFun (congrFun h3 0) 1
  have e10 := congrFun (congrFun h3 1) 0
  have e11 := congrFun (congrFun h3 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  have f00 : ((a + d) ^ 2 + 1) * a = 1 + (a + d) := by
    linear_combination e00 + (a + (a + d)) * hY + a * h2
  have f01 : ((a + d) ^ 2 + 1) * b = 0 := by
    linear_combination e01 + b * hY + b * h2
  have f10 : ((a + d) ^ 2 + 1) * c = 0 := by
    linear_combination e10 + c * hY + c * h2
  have f11 : ((a + d) ^ 2 + 1) * d = 1 + (a + d) := by
    linear_combination e11 + (d + (a + d)) * hY + d * h2
  by_contra ht
  have hs : (a + d) ^ 2 + 1 ≠ 0 := by
    intro h
    apply ht
    have : (a + d + 1) ^ 2 = 0 := by linear_combination h + (a + d) * h2
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this
    linear_combination this - h2
  have hb : b = 0 := (mul_eq_zero.mp f01).resolve_left hs
  have hc : c = 0 := (mul_eq_zero.mp f10).resolve_left hs
  have had : a = d := by
    have : ((a + d) ^ 2 + 1) * (a - d) = 0 := by linear_combination f00 - f11
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hs)
  rw [hb, hc, ← had] at hY
  have ha : a = 1 := by
    have : (a - 1) ^ 2 = 0 := by linear_combination hY - (a - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this)
  apply h1
  ext i j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · exact hc
  · change d = 1
    rw [← had, ha]

omit [CharP K 2] in
theorem trace_mul_add_trace_mul_adjugate (X Y : Matrix (Fin 2) (Fin 2) K) :
    (X * Y).trace + (X * Y.adjugate).trace = X.trace * Y.trace := by
  rw [adjugate_fin_two]
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring


omit [CharP K 2] in
theorem adjugate_eq_mul_self {Y : Matrix (Fin 2) (Fin 2) K} (hY : Y.det = 1)
    (h3 : Y * Y * Y = 1) : Y.adjugate = Y * Y := by
  have h := mul_adjugate Y
  rw [hY, one_smul] at h
  calc Y.adjugate = (Y * Y * Y) * Y.adjugate := by rw [h3, one_mul]
    _ = Y * Y * (Y * Y.adjugate) := by rw [mul_assoc]
    _ = Y * Y := by rw [h, mul_one]

theorem exists_four_ne_one {A : Type*} [CommGroup A] [Finite A] (hA : ∀ a : A, a ^ 3 = 1)
    (hcard : 3 < Nat.card A) : ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ a * b ≠ 1 ∧ a * b ^ 2 ≠ 1 := by
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  have hza : Nat.card (Subgroup.zpowers a) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA a))
  obtain ⟨b, hb⟩ : ∃ b : A, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have : Subgroup.zpowers a = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [this, Subgroup.card_top] at hza
    omega
  refine ⟨a, b, ha, fun h => hb (h ▸ Subgroup.one_mem _), fun h => hb ?_, fun h => hb ?_⟩
  · rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  · have hb2 : b ^ 2 = a⁻¹ := eq_inv_of_mul_eq_one_right h
    have : b = (a⁻¹) ^ 2 := by
      rw [← hb2, ← pow_mul]
      calc b = b ^ 3 * b := by rw [hA, one_mul]
        _ = b ^ (2 * 2) := by rw [← pow_succ]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) 2

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem card_le_three_of_det_eq_one {A : Type*} [CommGroup A] [Finite A]
    (hA : ∀ a : A, a ^ 3 = 1) (ρ : A →* Module.End K V) (hρ : Function.Injective ρ)
    (hdet : ∀ a, LinearMap.det (ρ a) = 1) (hV : Module.finrank K V ≤ 2) :
    Nat.card A ≤ 3 := by
  have h3 : (3 : K) ≠ 0 := by
    have : (3 : K) = 1 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h2
    rw [this]
    exact one_ne_zero
  rcases Nat.lt_or_ge (Module.finrank K V) 2 with hlt | hge
  ·
    let ρ' : A →* (V ≃ₗ[K] V) :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).toMonoidHom.comp ρ.toHomUnits
    have hρ' : Function.Injective ρ' := by
      intro a b hab
      apply hρ
      have := congrArg (fun e : V ≃ₗ[K] V => (e : V →ₗ[K] V)) hab
      exact this
    have := card_le_pow_finrank_of_faithful Nat.prime_three h3
      hA ρ' hρ'
    calc Nat.card A ≤ 3 ^ Module.finrank K V := this
      _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 := pow_one 3
  · have h2 : Module.finrank K V = 2 := le_antisymm hV hge
    have h0 : (2 : K) = 0 := CharTwo.two_eq_zero
    by_contra hcard
    push Not at hcard
    obtain ⟨a, b, ha, hb, hab, hab2⟩ := exists_four_ne_one hA hcard
    set e := Module.finBasisOfFinrankEq K V h2
    set X : A → Matrix (Fin 2) (Fin 2) K := fun g => LinearMap.toMatrix e e (ρ g)
    have hXmul : ∀ g g', X (g * g') = X g * X g' := fun g g' => by
      simp only [X, map_mul]
      exact LinearMap.toMatrix_mul e (ρ g) (ρ g')
    have hXdet : ∀ g, (X g).det = 1 := fun g => by
      simp only [X, LinearMap.det_toMatrix, hdet]
    have hX1 : X 1 = 1 := by
      change LinearMap.toMatrix e e (ρ 1) = 1
      rw [map_one]
      exact LinearMap.toMatrix_one e
    have hX3 : ∀ g, X g * X g * X g = 1 := fun g => by
      rw [← hXmul, ← hXmul, ← pow_two, ← pow_succ, hA, hX1]
    have hXne : ∀ g, g ≠ 1 → X g ≠ 1 := by
      intro g hg hX
      apply hg
      apply hρ
      rw [map_one]
      apply (LinearMap.toMatrix e e).injective
      rw [LinearMap.toMatrix_one]
      exact hX
    have htr : ∀ g, g ≠ 1 → (X g).trace = 1 := fun g hg =>
      trace_eq_one_of_pow_three (hXdet g) (hX3 g) (hXne g hg)
    have key := trace_mul_add_trace_mul_adjugate (X a) (X b)
    have e1 : X a * X b = X (a * b) := (hXmul a b).symm
    have e2 : X a * (X b * X b) = X (a * b ^ 2) := by rw [pow_two, hXmul, hXmul]
    rw [adjugate_eq_mul_self (hXdet b) (hX3 b), e1, e2, htr _ hab, htr _ hab2, htr _ ha,
      htr _ hb] at key
    apply one_ne_zero (α := K)
    linear_combination -key + h0

end TwoByTwo

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Rep

variable {A : Type*} [Group A] (ρ : A →* Module.End K V)

@[expose] def subRep (W : Submodule K V) (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) :
    A →* Module.End K W where
  toFun a := (ρ a).restrict (hW a)
  map_one' := by
    ext w
    simp [LinearMap.restrict_apply]
  map_mul' a b := by
    ext w
    simp [LinearMap.restrict_apply]

theorem subRep_apply (W : Submodule K V) (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) (a : A) (w : W) :
    ((subRep ρ W hW a w : W) : V) = ρ a w :=
  rfl

@[expose] def quotientRep (W : Submodule K V) (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) :
    A →* Module.End K (V ⧸ W) where
  toFun a := W.mapQ W (ρ a) (hW a)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp

theorem quotientRep_mk (W : Submodule K V) (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) (a : A) (v : V) :
    quotientRep ρ W hW a (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ a v) :=
  rfl

variable [FiniteDimensional K V]

theorem det_eq_det_subRep_mul (W : Submodule K V) (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) (a : A) :
    LinearMap.det (ρ a) =
      LinearMap.det (subRep ρ W hW a) * LinearMap.det (quotientRep ρ W hW a) :=
  LinearMap.det_eq_det_mul_det W (ρ a) (hW a)

end Rep

theorem eq_one_of_fix_of_quot_fix [CharP K 2] {A : Type*} [Group A] (ρ : A →* Module.End K V)
    {W : Submodule K V} {a : A} (ha : a ^ 3 = 1) (hW : ∀ w ∈ W, ρ a w = w)
    (hq : ∀ v, ρ a v - v ∈ W) : ρ a = 1 := by
  have h2 : ∀ v, ρ (a ^ 2) v = v := by
    intro v
    set u := ρ a v - v
    have hu : ρ a u = u := hW u (hq v)
    rw [pow_two, map_mul, Module.End.mul_apply, show ρ a v = v + u by simp [u]]
    rw [map_add, hu, show ρ a v = v + u by simp [u], add_assoc, ← two_smul K u,
      CharTwo.two_eq_zero, zero_smul, add_zero]
  ext v
  rw [show a = (a ^ 2) ^ 2 by rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, ha, one_mul],
    pow_two, map_mul, Module.End.mul_apply, h2, h2, Module.End.one_apply]


section Bounds

variable [CharP K 2]

theorem three_ne_zero_of_charTwo : (3 : K) ≠ 0 := by
  have : (3 : K) = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h2
  rw [this]
  exact one_ne_zero

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

@[expose] noncomputable def toGLRep {A : Type*} [Group A] (σ : A →* Module.End K W) :
    A →* (W ≃ₗ[K] W) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).toMonoidHom.comp σ.toHomUnits

omit [CharP K 2] [FiniteDimensional K W] in
theorem coe_toGLRep {A : Type*} [Group A] (σ : A →* Module.End K W) (a : A) :
    ((toGLRep σ a : W ≃ₗ[K] W) : W →ₗ[K] W) = σ a :=
  rfl

omit [CharP K 2] [FiniteDimensional K W] in
theorem ker_toGLRep {A : Type*} [Group A] (σ : A →* Module.End K W) :
    (toGLRep σ).ker = σ.ker := by
  ext a
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg (fun e : W ≃ₗ[K] W => (e : W →ₗ[K] W)) h
    exact this
  · intro h
    refine LinearEquiv.ext fun w => ?_
    change σ a w = w
    rw [h, Module.End.one_apply]

abbrev rangeCommGroup {A : Type*} [CommGroup A] (τ : A →* (W ≃ₗ[K] W)) :
    CommGroup τ.range :=
  { τ.range.toGroup with
    mul_comm := fun x y => by
      obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      change (x : W ≃ₗ[K] W) * y = y * x
      rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm] }

theorem card_le_card_ker_mul_pow {A : Type*} [CommGroup A] [Finite A]
    (hA : ∀ a : A, a ^ 3 = 1) (σ : A →* Module.End K W) :
    Nat.card A ≤ Nat.card σ.ker * 3 ^ Module.finrank K W := by
  set τ := toGLRep σ
  rw [← Subgroup.card_ker_mul_card_range τ, ker_toGLRep]
  refine Nat.mul_le_mul_left _ ?_
  let := rangeCommGroup τ
  have : Finite τ.range := Finite.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  refine card_le_pow_finrank_of_faithful Nat.prime_three
    three_ne_zero_of_charTwo (fun x => ?_) τ.range.subtype Subtype.val_injective
  obtain ⟨a, ha⟩ := x.2
  apply Subtype.ext
  change (x : W ≃ₗ[K] W) ^ 3 = 1
  rw [← ha, ← map_pow, hA, map_one]

theorem card_le_card_ker_mul_three {A : Type*} [CommGroup A] [Finite A]
    (hA : ∀ a : A, a ^ 3 = 1) (σ : A →* Module.End K W) (hdet : ∀ a, LinearMap.det (σ a) = 1)
    (hW : Module.finrank K W ≤ 2) : Nat.card A ≤ Nat.card σ.ker * 3 := by
  set τ := toGLRep σ
  rw [← Subgroup.card_ker_mul_card_range τ, ker_toGLRep]
  refine Nat.mul_le_mul_left _ ?_
  let := rangeCommGroup τ
  have : Finite τ.range := Finite.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  set ι : (W ≃ₗ[K] W) →* Module.End K W :=
    (Units.coeHom (Module.End K W)).comp
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm.toMonoidHom
  have hι : Function.Injective ι := fun e e' h => LinearEquiv.toLinearMap_injective h
  refine card_le_three_of_det_eq_one (fun x => ?_) (ι.comp τ.range.subtype)
    (hι.comp Subtype.val_injective) (fun x => ?_) hW
  · obtain ⟨a, ha⟩ := x.2
    apply Subtype.ext
    change (x : W ≃ₗ[K] W) ^ 3 = 1
    rw [← ha, ← map_pow, hA, map_one]
  · obtain ⟨a, ha⟩ := x.2
    change LinearMap.det ((x : W ≃ₗ[K] W) : W →ₗ[K] W) = 1
    rw [← ha, coe_toGLRep]
    exact hdet a

omit [CharP K 2] in
theorem eq_one_of_det_eq_one (hW : Module.finrank K W ≤ 1) {g : Module.End K W}
    (hg : LinearMap.det g = 1) : g = 1 := by
  rcases Nat.lt_or_ge (Module.finrank K W) 1 with h0 | h1
  · have : Subsingleton W := (Module.finrank_zero_iff (R := K)).mp (by omega)
    exact LinearMap.ext fun w => Subsingleton.elim _ _
  · set e := Module.finBasisOfFinrankEq K W (le_antisymm hW h1)
    apply (LinearMap.toMatrix e e).injective
    rw [LinearMap.toMatrix_one]
    rw [← LinearMap.det_toMatrix e, Matrix.det_unique] at hg
    ext i j
    fin_cases i
    fin_cases j
    simpa using hg


@[expose] def fixSpace {A : Type*} [Group A] (ρ : A →* Module.End K V) : Submodule K V where
  carrier := {v | ∀ a, ρ a v = v}
  add_mem' ha hb a := by rw [map_add, ha a, hb a]
  zero_mem' a := map_zero _
  smul_mem' c v hv a := by rw [map_smul, hv a]

omit [CharP K 2] in
theorem mem_fixSpace {A : Type*} [Group A] {ρ : A →* Module.End K V} {v : V} :
    v ∈ fixSpace ρ ↔ ∀ a, ρ a v = v :=
  Iff.rfl

variable [FiniteDimensional K V]

theorem card_le_three_of_fix {A : Type*} [CommGroup A] [Finite A] (hA : ∀ a : A, a ^ 3 = 1)
    (ρ : A →* Module.End K V) (hρ : Function.Injective ρ) (hdet : ∀ a, LinearMap.det (ρ a) = 1)
    {U : Submodule K V} (hU : ∀ a, ∀ u ∈ U, ρ a u = u) :
    (Module.finrank K (V ⧸ U) ≤ 2 → Nat.card A ≤ 3) ∧
      (Module.finrank K (V ⧸ U) ≤ 1 → ∀ a : A, a = 1) := by
  have hU' : ∀ a, ∀ u ∈ U, ρ a u ∈ U := fun a u hu => (hU a u hu).symm ▸ hu
  set τ := quotientRep ρ U hU'
  have hres : ∀ a, subRep ρ U hU' a = 1 := fun a => by
    ext u
    exact hU a u u.2
  have hτdet : ∀ a, LinearMap.det (τ a) = 1 := fun a => by
    have := det_eq_det_subRep_mul ρ U hU' a
    rwa [hdet, hres, map_one, one_mul, eq_comm] at this
  have hker : ∀ a, τ a = 1 → a = 1 := by
    intro a ha
    refine hρ ((eq_one_of_fix_of_quot_fix ρ (hA a) (hU a) fun v => ?_).trans (map_one ρ).symm)
    have := congrArg (fun f => f (Submodule.Quotient.mk v)) ha
    simp only [τ, quotientRep_mk, Module.End.one_apply] at this
    exact (Submodule.Quotient.eq U).mp this
  refine ⟨fun h2 => ?_, fun h1 a => hker a (eq_one_of_det_eq_one h1 (hτdet a))⟩
  have h := card_le_card_ker_mul_three hA τ hτdet h2
  have hk : Nat.card τ.ker = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro a ha
    exact hker a ha
  rwa [hk, one_mul] at h


omit [CharP K 2] [FiniteDimensional K V] in
theorem fix_of_mem_ker_subRep {A : Type*} [Group A] {ρ : A →* Module.End K V}
    {W : Submodule K V} {hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W} {a : A}
    (ha : a ∈ (subRep ρ W hW).ker) : ∀ w ∈ W, ρ a w = w := by
  intro w hw
  have := congrArg (fun f : Module.End K W => (f ⟨w, hw⟩ : V)) (MonoidHom.mem_ker.mp ha)
  simpa only [subRep_apply, Module.End.one_apply] using this

theorem card_le_nine_of_dim_three {A : Type*} [CommGroup A] [Finite A] (hA : ∀ a : A, a ^ 3 = 1)
    (ρ : A →* Module.End K V) (hρ : Function.Injective ρ) (hdet : ∀ a, LinearMap.det (ρ a) = 1)
    (hV : Module.finrank K V = 3) {W : Submodule K V} (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W)
    (hW0 : W ≠ ⊥) (hWV : W ≠ ⊤) : Nat.card A ≤ 9 := by
  have hd1 : 0 < Module.finrank K W :=
    Nat.pos_of_ne_zero fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hd2 : Module.finrank K W < 3 := hV ▸ Submodule.finrank_lt hWV
  have hq : Module.finrank K (V ⧸ W) + Module.finrank K W = 3 :=
    hV ▸ W.finrank_quotient_add_finrank
  set σ := subRep ρ W hW
  have hbound := card_le_card_ker_mul_pow hA σ
  have hfix := card_le_three_of_fix (A := σ.ker) (fun b => Subtype.ext (hA b))
    (ρ.comp σ.ker.subtype) (hρ.comp Subtype.val_injective) (fun b => hdet b) (U := W)
    (fun b => fix_of_mem_ker_subRep (ρ := ρ) (hW := hW) b.2)
  rcases (show Module.finrank K W = 1 ∨ Module.finrank K W = 2 by omega) with h1 | h2
  · have hB := hfix.1 (by omega)
    rw [h1, pow_one] at hbound
    omega
  · have hB : Nat.card σ.ker = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => by rw [hfix.2 (by omega) x, hfix.2 (by omega) y]⟩, inferInstance⟩
    rw [h2, hB, one_mul] at hbound
    omega


omit [CharP K 2] [FiniteDimensional K V] in
open CFSG.LieType.BorelTits in
theorem sub_mem_perp_of_fix (F : ReflForm K V) {f : Module.End K V}
    (hf : ∀ u v, F.β (f u) (f v) = F.β u v) {W : Submodule K V} (hW : ∀ w ∈ W, f w = w)
    (v : V) : f v - v ∈ F.perp W := by
  intro w hw
  rw [F.β_sub_right, ← hf w v, hW w hw, sub_self]

open CFSG.LieType.BorelTits in
theorem card_le_nine_of_isotropic {A : Type*} [CommGroup A] [Finite A] (hA : ∀ a : A, a ^ 3 = 1)
    (ρ : A →* Module.End K V) (hρ : Function.Injective ρ) (hdet : ∀ a, LinearMap.det (ρ a) = 1)
    (hV : Module.finrank K V = 4) (F : ReflForm K V)
    (hiso : ∀ a u v, F.β (ρ a u) (ρ a v) = F.β u v) {W : Submodule K V}
    (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) (hW0 : W ≠ ⊥) (hWt : F.IsTotallyIsotropic W) :
    Nat.card A ≤ 9 := by
  have hd1 : 0 < Module.finrank K W :=
    Nat.pos_of_ne_zero fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hperp := F.finrank_perp W
  have hle : Module.finrank K W ≤ Module.finrank K (F.perp W) := Submodule.finrank_mono hWt
  set σ := subRep ρ W hW
  have hbound := card_le_card_ker_mul_pow hA σ
  have hfixW : ∀ b : σ.ker, ∀ w ∈ W, ρ b w = w :=
    fun b => fix_of_mem_ker_subRep (ρ := ρ) (hW := hW) b.2
  rcases (show Module.finrank K W = 1 ∨ Module.finrank K W = 2 by omega) with h1 | h2
  ·
    set B := σ.ker
    have : Fintype B := Fintype.ofFinite B
    have hne : F.perp W ≠ ⊤ := by
      intro h
      rw [h, finrank_top] at hperp
      omega
    obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ ∉ F.perp W := by
      by_contra h
      push Not at h
      exact hne (eq_top_iff.mpr fun v _ => h v)
    set v' := ∑ b : B, ρ b v₀
    have hfix : ∀ b : B, ρ b v' = v' := by
      intro b
      simp only [v', map_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft b) _ _ fun c => ?_
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    have hcard : (Fintype.card B : K) = 1 := by
      obtain ⟨j, hj⟩ := exists_card_eq_pow_of_exponent
        Nat.prime_three (A := B) fun b => Subtype.ext (hA b)
      rw [← Nat.card_eq_fintype_card, hj, Nat.cast_pow]
      have h3 : (3 : K) = 1 := by
        have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
        linear_combination h2
      rw [Nat.cast_ofNat, h3, one_pow]
    have hsub : v' - v₀ ∈ F.perp W := by
      have : v' - v₀ = ∑ b : B, (ρ b v₀ - v₀) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K,
          hcard, one_smul]
      rw [this]
      exact Submodule.sum_mem _ fun b _ =>
        sub_mem_perp_of_fix F (hiso b) (hfixW b) v₀
    have hv'W : v' ∉ W := by
      intro h
      apply hv₀
      have := sub_mem (hWt h) hsub
      rwa [sub_sub_cancel] at this
    set U := fixSpace (ρ.comp B.subtype)
    have hWU : W ⊔ K ∙ v' ≤ U := by
      refine sup_le (fun w hw b => hfixW b w hw) ?_
      rw [Submodule.span_singleton_le_iff_mem]
      exact fun b => hfix b
    have hlt : W < W ⊔ K ∙ v' :=
      lt_of_le_of_ne le_sup_left fun h => hv'W (h ▸ Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self v'))
    have hU2 : 2 ≤ Module.finrank K U := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      have := Submodule.finrank_mono hWU
      omega
    have hq := U.finrank_quotient_add_finrank
    have hB := (card_le_three_of_fix (A := B) (fun b => Subtype.ext (hA b))
      (ρ.comp B.subtype) (hρ.comp Subtype.val_injective) (fun b => hdet b) (U := U)
      (fun b u hu => hu b)).1 (by omega)
    rw [h1, pow_one] at hbound
    omega
  ·
    have hWW : F.perp W = W :=
      (Submodule.eq_of_le_of_finrank_eq hWt (by omega)).symm
    have hB : Nat.card σ.ker = 1 := by
      rw [Subgroup.card_eq_one, eq_bot_iff]
      intro a ha
      have hfa := fix_of_mem_ker_subRep (ρ := ρ) (hW := hW) ha
      refine hρ ((eq_one_of_fix_of_quot_fix ρ (hA a) hfa fun v => ?_).trans (map_one ρ).symm)
      rw [← hWW]
      exact sub_mem_perp_of_fix F (hiso a) hfa v
    rw [h2, hB, one_mul] at hbound
    omega


theorem map_commutator_eq_one {G M : Type*} [Group G] [CommMonoid M] (f : G →* M) (x y : G) :
    f (x * y * x⁻¹ * y⁻¹) = 1 := by
  rw [map_mul, map_mul, map_mul, mul_right_comm (f x) (f y) (f x⁻¹), ← map_mul, mul_inv_cancel,
    map_one, one_mul, ← map_mul, mul_inv_cancel, map_one]

abbrev commGroupOfCommute (G : Type*) [Group G] (h : ∀ a b : G, a * b = b * a) : CommGroup G :=
  { ‹Group G› with mul_comm := h }

theorem card_le_of_central_dim_three {X : Type*} [Group X] [Finite X]
    (ρ : X →* Module.End K V) (hρ : Function.Injective ρ) (hdet : ∀ x, LinearMap.det (ρ x) = 1)
    (hV : Module.finrank K V = 3) (Z : Subgroup X) (hZ : ∀ z ∈ Z, ∃ c : K, ρ z = c • 1)
    {E : Subgroup X} (h3 : ∀ x ∈ E, x ^ 3 ∈ Z)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ Z) {W : Submodule K V}
    (hW : ∀ x ∈ E, ∀ w ∈ W, ρ x w ∈ W) (hW0 : W ≠ ⊥) (hWV : W ≠ ⊤) :
    Nat.card E ≤ 9 * Nat.card Z := by
  have hd1 : 0 < Module.finrank K W :=
    Nat.pos_of_ne_zero fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hd2 : Module.finrank K W < 3 := hV ▸ Submodule.finrank_lt hWV
  have hWE : ∀ x : E, ∀ w ∈ W, (ρ.comp E.subtype) x w ∈ W := fun x => hW x x.2
  set σ := subRep (ρ.comp E.subtype) W hWE
  have hab : ∀ x y : E, x * y = y * x := by
    intro x y
    set c := x * y * x⁻¹ * y⁻¹
    obtain ⟨l, hl⟩ := hZ c (hcomm x x.2 y y.2)
    have hdetV : l ^ 3 = 1 := by
      have := hdet c
      rwa [hl, LinearMap.det_smul, map_one, mul_one, hV] at this
    have hdetW : l ^ Module.finrank K W = 1 := by
      have hσc : σ c = l • 1 := by
        ext w
        change ρ c w = l • w
        rw [hl, LinearMap.smul_apply, Module.End.one_apply]
      have h1 : LinearMap.det (σ c) = 1 := map_commutator_eq_one (LinearMap.det.comp σ) x y
      rwa [hσc, LinearMap.det_smul, map_one, mul_one] at h1
    have hl1 : l = 1 := by
      rcases (show Module.finrank K W = 1 ∨ Module.finrank K W = 2 by omega) with h | h
      · rwa [h, pow_one] at hdetW
      · rw [h] at hdetW
        have hl0 : l ≠ 0 := by
          rintro rfl
          simp at hdetW
        calc l = l ^ 3 * (l ^ 2)⁻¹ := by field_simp
          _ = 1 := by rw [hdetV, hdetW, inv_one, one_mul]
    have hc1 : c = 1 := by
      apply Subtype.ext
      apply hρ
      rw [Subgroup.coe_one, map_one, hl, hl1, one_smul]
    have : x * y * x⁻¹ * y⁻¹ = 1 := hc1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  let := commGroupOfCommute E hab
  set cube : E →* E := powMonoidHom 3
  have hrange : cube.range ≤ Z.subgroupOf E := by
    rintro _ ⟨x, rfl⟩
    exact h3 x x.2
  have hZE : Nat.card (Z.subgroupOf E) ≤ Nat.card Z :=
    Nat.card_le_card_of_injective (fun x : Z.subgroupOf E => (⟨x.1.1, x.2⟩ : Z))
      fun x y h => by
        have := congrArg (fun z : Z => (z : X)) h
        exact Subtype.ext (Subtype.ext this)
  have hker : Nat.card cube.ker ≤ 9 := by
    refine card_le_nine_of_dim_three (A := cube.ker) (fun x => ?_)
      (ρ.comp (E.subtype.comp cube.ker.subtype))
      (hρ.comp (Subtype.val_injective.comp Subtype.val_injective)) (fun x => hdet _) hV
      (W := W) (fun x w hw => hW _ x.1.2 w hw) hW0 hWV
    exact Subtype.ext (MonoidHom.mem_ker.mp x.2)
  rw [← Subgroup.card_ker_mul_card_range cube]
  calc Nat.card cube.ker * Nat.card cube.range ≤ 9 * Nat.card Z :=
        Nat.mul_le_mul hker ((Subgroup.card_le_of_le hrange).trans hZE)


end Bounds

section LocalRank

open CFSG.Assembly CFSG.Assembly.RankThreeEven

theorem localRank_quotient_le_of_central {G : Type*} [Group G] [Finite G] (Z : Subgroup G)
    [Z.Normal] (hZ : Z ≤ Subgroup.center G) (hZ2 : Nat.Coprime (Nat.card Z) 2) {p k : ℕ}
    (hp : p.Prime)
    (h : ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P → ∀ E : Subgroup G, Z ≤ E →
      E ≤ Subgroup.normalizer (P : Set G) → (∀ x ∈ E, x ^ p ∈ Z) →
      (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ Z) → Nat.card E ≤ p ^ k * Nat.card Z) :
    localRank p (G ⧸ Z) ≤ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine csSup_le' ?_
  rintro j ⟨L, ⟨P, hP0, hP2, rfl⟩, rfl⟩
  obtain ⟨E, hEL, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (Subgroup.normalizer (P : Set (G ⧸ Z)))
  obtain ⟨P₀, hP₀2, hP₀P⟩ := CFSG.LieType.BorelTits.exists_isPGroup_map_eq Z hP2
  have hP₀0 : P₀ ≠ ⊥ := by
    rintro rfl
    exact hP0 (by rw [← hP₀P, Subgroup.map_bot])
  set π := QuotientGroup.mk' Z
  set Ê := E.comap π
  have hZÊ : Z ≤ Ê := fun z hz => by
    have : π z = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hz
    change π z ∈ E
    rw [this]
    exact E.one_mem
  have hÊN : Ê ≤ Subgroup.normalizer (P₀ : Set G) := by
    rw [CFSG.LieType.BorelTits.normalizer_eq_comap_normalizer_map Z hZ hZ2 hP₀2, hP₀P]
    exact Subgroup.comap_mono hEL
  have hpow : ∀ x ∈ Ê, x ^ p ∈ Z := by
    intro x hx
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact hE.2 _ hx
  have hcomm : ∀ x ∈ Ê, ∀ y ∈ Ê, x * y * x⁻¹ * y⁻¹ ∈ Z := by
    intro x hx y hy
    have hxy : π x * π y = π y * π x :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
    have : π (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxy, mul_inv_cancel_right,
        mul_inv_cancel]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have hb := h P₀ hP₀0 hP₀2 Ê hZÊ hÊN hpow hcomm
  have hcard : Nat.card Ê = Nat.card Z * Nat.card E :=
    QuotientGroup.card_preimage_mk Z (E : Set (G ⧸ Z))
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hle : Nat.card E ≤ p ^ k := by
    rw [hcard, mul_comm] at hb
    exact Nat.le_of_mul_le_mul_right hb hZpos
  rw [hEc] at hle
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle

end LocalRank

end CFSG.RankThree.PartTwo.Census
