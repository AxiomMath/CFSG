module

public import CFSG.LocalAnalysis.SteinbergCDQuadraticGraphAffine
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.SteinbergCD

open Matrix
open scoped Pointwise

variable {K : Type*} [Field K] [CharP K 2] [Finite K]

omit [CharP K 2] [Finite K] in
theorem exists_GL_mulVec_single {a : Fin 2 → K} (ha : a ≠ 0) :
    ∃ P : GL (Fin 2) K, (P : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = a := by
  by_cases h0 : a 0 = 0
  · have h1 : a 1 ≠ 0 := fun h1 => ha (by
      ext i
      fin_cases i
      · exact h0
      · exact h1)
    refine ⟨GeneralLinearGroup.mkOfDetNeZero !![a 0, 1; a 1, 0]
      (by rw [det_fin_two_of]; simpa [h0] using h1), ?_⟩
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, GeneralLinearGroup.mkOfDetNeZero]
  · refine ⟨GeneralLinearGroup.mkOfDetNeZero !![a 0, 0; a 1, 1]
      (by rw [det_fin_two_of]; simpa using h0), ?_⟩
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, GeneralLinearGroup.mkOfDetNeZero]

omit [CharP K 2] [Finite K] in
theorem exists_GL_mulVec_eq {a b : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ C : GL (Fin 2) K, (C : Matrix (Fin 2) (Fin 2) K) *ᵥ a = b := by
  obtain ⟨P, hP⟩ := exists_GL_mulVec_single ha
  obtain ⟨Q, hQ⟩ := exists_GL_mulVec_single hb
  have hPa : ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ a = ![1, 0] := by
    rw [← hP, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  refine ⟨Q * P⁻¹, ?_⟩
  rw [Units.val_mul, ← mulVec_mulVec, hPa, hQ]

omit [CharP K 2] in
theorem exists_fixed_ne_zero [CharP K 2] {G : Type*} [Group G] (hG : IsPGroup 2 G)
    (ρ : G →* Equiv.Perm (Fin 2 → K)) (h0 : ∀ g, ρ g 0 = 0) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction G (Fin 2 → K) := MulAction.compHom _ ρ
  have hmod := hG.card_modEq_card_fixedPoints (Fin 2 → K)
  have heven : 2 ∣ Nat.card (Fin 2 → K) := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, hn]
    exact dvd_pow (dvd_pow_self 2 n.ne_zero) two_ne_zero
  have hfix : 2 ∣ Nat.card (MulAction.fixedPoints G (Fin 2 → K)) :=
    Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 heven))
  have h0mem : (0 : Fin 2 → K) ∈ MulAction.fixedPoints G (Fin 2 → K) := fun g => h0 g
  obtain ⟨⟨v, hv⟩, hne⟩ : ∃ x : MulAction.fixedPoints G (Fin 2 → K), x ≠ ⟨0, h0mem⟩ := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card (MulAction.fixedPoints G (Fin 2 → K)) = 1 :=
      Nat.card_eq_one_iff_exists.2 ⟨⟨0, h0mem⟩, hall⟩
    rw [h1] at hfix
    norm_num at hfix
  exact ⟨v, fun h => hne (Subtype.ext h), fun g => hv g⟩

section Subgroup

variable {H : Subgroup (QGAut K)} (hHA : H ≤ qgStab K)

variable (H) in
@[expose] def qgStabT : Subgroup H where
  carrier := {x | Multiplicative.toAdd (x : QGAut K) (qgT K) = qgT K}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at *
    change Multiplicative.toAdd (x : QGAut K) (Multiplicative.toAdd (y : QGAut K) (qgT K)) = qgT K
    rw [hy, hx]
  one_mem' := rfl
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hx]
    exact AddAut.neg_apply_self _ _ _

omit [CharP K 2] [Finite K] in
include hHA in
theorem mem_qgStabT_iff {x : H} : x ∈ qgStabT H ↔ qgInduced (x : QGAut K) 0 = 0 := by
  change Multiplicative.toAdd (x : QGAut K) (qgT K) = qgT K ↔ _
  rw [← qgPoint_zero, ← qgPoint_qgInduced (hHA x.2)]
  exact qgPoint_injective.eq_iff

@[expose] noncomputable def qgPermOf : H →* Equiv.Perm (Fin 2 → K) :=
  (qgPerm (K := K)).comp (Subgroup.inclusion hHA)

omit [Finite K] in
include hHA in
theorem eq_one_of_forall {x : H} (h : ∀ v, qgInduced (x : QGAut K) v = v) : x = 1 :=
  Subtype.ext (eq_one_of_qgInduced (hHA x.2) h)

omit [Finite K] in
theorem qgPermOf_injective : Function.Injective (qgPermOf hHA) :=
  qgPerm_injective.comp (Subgroup.inclusion_injective hHA)

omit [Finite K] in
include hHA in
theorem eq_of_qgInduced_eq {x y : H}
    (h : ∀ v, qgInduced (x : QGAut K) v = qgInduced (y : QGAut K) v) : x = y :=
  qgPermOf_injective hHA (Equiv.ext h)

omit [CharP K 2] [Finite K] in
include hHA in
theorem qgInduced_inv_apply (x : H) (v : Fin 2 → K) :
    qgInduced (x : QGAut K) (qgInduced ((x⁻¹ : H) : QGAut K) v) = v := by
  rw [← qgInduced_mul (hHA x.2) (hHA (x⁻¹ : H).2), ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, qgInduced_one]

omit [CharP K 2] [Finite K] in
include hHA in
theorem qgInduced_inv_apply' (x : H) (v : Fin 2 → K) :
    qgInduced ((x⁻¹ : H) : QGAut K) (qgInduced (x : QGAut K) v) = v := by
  rw [← qgInduced_mul (hHA (x⁻¹ : H).2) (hHA x.2), ← Subgroup.coe_mul, inv_mul_cancel,
    Subgroup.coe_one, qgInduced_one]

@[expose] def qgTranslSub : Subgroup H where
  carrier := {x | ∃ u, ∀ v, qgInduced (x : QGAut K) v = v + u}
  one_mem' := ⟨0, fun v => by rw [Subgroup.coe_one, qgInduced_one, add_zero]⟩
  mul_mem' {x y} hx hy := by
    obtain ⟨u, hu⟩ := hx
    obtain ⟨u', hu'⟩ := hy
    refine ⟨u' + u, fun v => ?_⟩
    rw [Subgroup.coe_mul, qgInduced_mul (hHA x.2) (hHA y.2), hu', hu, add_assoc]
  inv_mem' {x} hx := by
    obtain ⟨u, hu⟩ := hx
    refine ⟨-u, fun v => ?_⟩
    have h1 := qgInduced_inv_apply hHA x v
    rw [hu] at h1
    exact eq_add_neg_of_add_eq h1

omit [Finite K] in
include hHA in
theorem eq_of_mem_qgTranslSub {x y : H} (hx : x ∈ qgTranslSub hHA) (hy : y ∈ qgTranslSub hHA)
    (h : qgInduced (x : QGAut K) 0 = qgInduced (y : QGAut K) 0) : x = y := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨u', hu'⟩ := hy
  rw [hu, hu', zero_add, zero_add] at h
  exact eq_of_qgInduced_eq hHA fun v => by rw [hu, hu', h]

theorem qgTranslSub_normal : (qgTranslSub hHA).Normal where
  conj_mem x hx g := by
    obtain ⟨u, hu⟩ := hx
    obtain ⟨w₀, N, σ, hN⟩ := exists_affine_of_mem (hHA g.2)
    refine ⟨(N : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (u i), fun v => ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul,
      qgInduced_mul (mul_mem (hHA g.2) (hHA x.2)) (hHA (g⁻¹ : H).2),
      qgInduced_mul (hHA g.2) (hHA x.2), hu, hN]
    have hσ : (fun i => σ ((qgInduced ((g⁻¹ : H) : QGAut K) v + u) i)) =
        (fun i => σ (qgInduced ((g⁻¹ : H) : QGAut K) v i)) + fun i => σ (u i) := by
      funext i
      simp
    rw [hσ, mulVec_add, ← add_assoc, ← hN, qgInduced_inv_apply hHA g v]

omit [Finite K] in
theorem qgTranslSub_sq {x : H} (hx : x ∈ qgTranslSub hHA) : x * x = 1 := by
  obtain ⟨u, hu⟩ := hx
  have huu : u + u = 0 := funext fun i => CharTwo.add_self_eq_zero (u i)
  exact eq_one_of_forall hHA fun v => by
    rw [Subgroup.coe_mul, qgInduced_mul (hHA x.2) (hHA x.2), hu, hu, add_assoc, huu, add_zero]

omit [Finite K] in
theorem qgTranslSub_comm {x y : H} (hx : x ∈ qgTranslSub hHA) (hy : y ∈ qgTranslSub hHA) :
    x * y = y * x := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨u', hu'⟩ := hy
  exact eq_of_qgInduced_eq hHA fun v => by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, qgInduced_mul (hHA x.2) (hHA y.2),
      qgInduced_mul (hHA y.2) (hHA x.2)]
    simp only [hu, hu']
    exact add_right_comm _ _ _

omit [Finite K] in
theorem isElementaryAbelian_qgTranslSub : IsElementaryAbelian 2 (qgTranslSub hHA) where
  is_comm := ⟨fun x y => Subtype.ext (qgTranslSub_comm hHA x.2 y.2)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, pow_two, qgTranslSub_sq hHA x.2, Subgroup.coe_one])

theorem qgTranslSub_le_pCore : qgTranslSub hHA ≤ CFSG.pCore 2 H := by
  have := isElementaryAbelian_qgTranslSub hHA
  exact le_sSup ⟨qgTranslSub_normal hHA, IsElementaryAbelian.isPGroup 2 _⟩

section Hyp

variable (htrans : ∀ v w : Fin 2 → K, ∃ h ∈ H, qgInduced h v = w)
  (hlin : ∀ M : GL (Fin 2) K, ∃ h ∈ H, ∀ v, qgInduced h v = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ v)

include hHA htrans hlin in
theorem exists_transl_mem (u : Fin 2 → K) : ∃ x ∈ H, ∀ v, qgInduced x v = v + u := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hu : u = 0
  · exact ⟨1, H.one_mem, fun v => by rw [qgInduced_one, hu, add_zero]⟩
  obtain ⟨v₀, hv₀0, hv₀u⟩ : ∃ v₀ : Fin 2 → K, v₀ ≠ 0 ∧ v₀ ≠ u := by
    by_cases h0 : u 0 = 0
    · refine ⟨![1, 0], fun h => ?_, fun h => ?_⟩
      · have := congrFun h 0
        simp at this
      · have := congrFun h 0
        simp [h0] at this
    · refine ⟨![0, 1], fun h => ?_, fun h => ?_⟩
      · have := congrFun h 1
        simp at this
      · have := congrFun h 0
        simp only [Matrix.cons_val_zero] at this
        exact h0 this.symm
  obtain ⟨h, hH, hh⟩ := htrans 0 v₀
  obtain ⟨w₀, M, σ, hM⟩ := exists_affine_of_mem (hHA hH)
  have hw₀ : w₀ = v₀ := by
    have e := hM 0
    rw [hh] at e
    have hz : (fun i => σ ((0 : Fin 2 → K) i)) = 0 := funext fun i => by simp
    rw [hz, mulVec_zero, add_zero] at e
    exact e.symm
  subst hw₀
  set Mm : Matrix (Fin 2) (Fin 2) K := (M : Matrix (Fin 2) (Fin 2) K) with hMm
  set Mi : Matrix (Fin 2) (Fin 2) K := ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hMi
  have hMMi : Mm * Mi = 1 := by rw [hMm, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * Mm = 1 := by rw [hMm, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinj : ∀ y, Mi *ᵥ y = 0 → y = 0 := fun y hy => by
    have := congrArg (Mm *ᵥ ·) hy
    simpa [mulVec_mulVec, hMMi] using this
  have ha : Mi *ᵥ w₀ ≠ 0 := fun h => hv₀0 (hinj _ h)
  have hb : Mi *ᵥ (w₀ + u) ≠ 0 := fun h => hv₀u (by
    have := hinj _ h
    funext i
    have hi := congrFun this i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    linear_combination hi - u i * h2)
  obtain ⟨A', hA'⟩ := exists_GL_mulVec_eq ha hb
  set A : GL (Fin 2) K := GeneralLinearGroup.map (σ.symm : K →+* K) A' with hA
  set B : GL (Fin 2) K := M * A'⁻¹ * M⁻¹ with hB
  obtain ⟨ℓA, hℓA, hℓA'⟩ := hlin A
  obtain ⟨ℓB, hℓB, hℓB'⟩ := hlin B
  have hS : ∀ x ∈ H, x ∈ qgStab K := fun x hx => hHA hx
  have hmem1 : h * ℓA ∈ H := H.mul_mem hH hℓA
  have hmem2 : h * ℓA * h⁻¹ ∈ H := H.mul_mem hmem1 (H.inv_mem hH)
  refine ⟨h * ℓA * h⁻¹ * ℓB, H.mul_mem hmem2 hℓB, fun v => ?_⟩
  rw [qgInduced_mul (hS _ hmem2) (hS _ hℓB), qgInduced_mul (hS _ hmem1) (hS _ (H.inv_mem hH)),
    qgInduced_mul (hS _ hH) (hS _ hℓA)]
  set w := qgInduced h⁻¹ (qgInduced ℓB v) with hw
  have hhw : qgInduced h w = (B : Matrix (Fin 2) (Fin 2) K) *ᵥ v := by
    rw [hw, ← qgInduced_mul (hS _ hH) (hS _ (H.inv_mem hH)), mul_inv_cancel, qgInduced_one,
      hℓB']
  have hσw : (fun i => σ (w i)) = Mi *ᵥ ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v - w₀) := by
    have e := hM w
    rw [hhw] at e
    have e' : Mm *ᵥ (fun i => σ (w i)) = (B : Matrix (Fin 2) (Fin 2) K) *ᵥ v - w₀ := by
      rw [e]
      abel
    rw [← e', mulVec_mulVec, hMiM, one_mulVec]
  have hAσ : (A : Matrix (Fin 2) (Fin 2) K).map σ = (A' : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    simp [hA]
  have hσA : (fun i => σ (((A : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i)) =
      (A' : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (w i) := by
    funext i
    have := RingHom.map_mulVec (σ : K →+* K) (A : Matrix (Fin 2) (Fin 2) K) w i
    simp only [RingEquiv.coe_toRingHom] at this
    rw [this, hAσ]
    rfl
  rw [hℓA', hM, hσA, hσw]
  have hBm : (B : Matrix (Fin 2) (Fin 2) K) =
      Mm * ((A'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Mi := by
    rw [hB, Units.val_mul, Units.val_mul]
  have hAA : (A' : Matrix (Fin 2) (Fin 2) K) *
      ((A'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have k1 : Mm *ᵥ ((A' : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (Mi *ᵥ ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v))) = v := by
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hBm]
    have e : Mm * (A' : Matrix (Fin 2) (Fin 2) K) * Mi *
        (Mm * ((A'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Mi) = 1 := by
      calc _ = Mm * (A' : Matrix (Fin 2) (Fin 2) K) * (Mi * Mm) *
            ((A'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Mi := by
            simp only [mul_assoc]
        _ = Mm * ((A' : Matrix (Fin 2) (Fin 2) K) *
            ((A'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * Mi := by
            rw [hMiM, mul_one]
            simp only [mul_assoc]
        _ = 1 := by rw [hAA, mul_one, hMMi]
    rw [e, one_mulVec]
  have k2 : Mm *ᵥ ((A' : Matrix (Fin 2) (Fin 2) K) *ᵥ (Mi *ᵥ w₀)) = w₀ + u := by
    rw [hA', mulVec_mulVec, hMMi, one_mulVec]
  rw [mulVec_sub, mulVec_sub, mulVec_sub, k1, k2]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply]
  linear_combination (-(u i)) * h2

include htrans hlin in
theorem card_qgTranslSub : Nat.card (qgTranslSub hHA) = Nat.card K ^ 2 := by
  have hbij : Function.Bijective
      (fun x : qgTranslSub hHA => qgInduced ((x : H) : QGAut K) 0) := by
    refine ⟨fun x y hxy => Subtype.ext (eq_of_mem_qgTranslSub hHA x.2 y.2 hxy), fun u => ?_⟩
    obtain ⟨x, hx, hxu⟩ := exists_transl_mem hHA htrans hlin u
    exact ⟨⟨⟨x, hx⟩, ⟨u, hxu⟩⟩, by simp [hxu]⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_fun, Nat.card_fin]

include hHA hlin in
theorem eq_one_of_mem_pCore_of_mem_qgStabT {x : H} (hx : x ∈ CFSG.pCore 2 H)
    (hxt : x ∈ qgStabT H) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup H := CFSG.pCore 2 H ⊓ qgStabT H with hP'def
  have hP' : IsPGroup 2 P' := CFSG.pCore_isPGroup.to_le inf_le_left
  obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero hP' ((qgPermOf hHA).comp P'.subtype)
    (fun y => (mem_qgStabT_iff hHA).1 y.2.2)
  have hall : ∀ y ∈ P', ∀ w, qgInduced ((y : H) : QGAut K) w = w := by
    intro y hy w
    by_cases hw : w = 0
    · subst hw
      exact (mem_qgStabT_iff hHA).1 hy.2
    obtain ⟨C, hC⟩ := exists_GL_mulVec_eq hv0 hw
    obtain ⟨ℓ, hℓ, hℓ'⟩ := hlin C
    have hℓ'' : ∀ v, qgInduced (((⟨ℓ, hℓ⟩ : H) : QGAut K)) v =
        (C : Matrix (Fin 2) (Fin 2) K) *ᵥ v := hℓ'
    have hℓt : (⟨ℓ, hℓ⟩ : H) ∈ qgStabT H := (mem_qgStabT_iff hHA).2 (by rw [hℓ'', mulVec_zero])
    have hmem : (⟨ℓ, hℓ⟩ : H)⁻¹ * y * ⟨ℓ, hℓ⟩ ∈ P' := by
      refine ⟨?_, ?_⟩
      · have := (CFSG.pCore_normal (p := 2) (G := H)).conj_mem y hy.1 (⟨ℓ, hℓ⟩ : H)⁻¹
        rwa [inv_inv] at this
      · exact (qgStabT H).mul_mem ((qgStabT H).mul_mem ((qgStabT H).inv_mem hℓt) hy.2) hℓt
    have h1 := hv ⟨_, hmem⟩
    change qgInduced (((⟨ℓ, hℓ⟩ : H)⁻¹ * y * ⟨ℓ, hℓ⟩ : H) : QGAut K) v = v at h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul,
      qgInduced_mul (mul_mem (hHA ((⟨ℓ, hℓ⟩ : H)⁻¹).2) (hHA y.2)) (hHA (⟨ℓ, hℓ⟩ : H).2),
      qgInduced_mul (hHA ((⟨ℓ, hℓ⟩ : H)⁻¹).2) (hHA y.2)] at h1
    have h2 := congrArg (qgInduced (((⟨ℓ, hℓ⟩ : H) : QGAut K))) h1
    rw [qgInduced_inv_apply hHA ⟨ℓ, hℓ⟩, hℓ'', hC] at h2
    exact h2
  exact eq_one_of_forall hHA (hall x ⟨hx, hxt⟩)

include htrans hlin in
theorem pCore_eq_qgTranslSub : CFSG.pCore 2 H = qgTranslSub hHA := by
  refine le_antisymm (fun x hx => ?_) (qgTranslSub_le_pCore hHA)
  obtain ⟨τ, hτH, hτ⟩ := exists_transl_mem hHA htrans hlin (qgInduced (x : QGAut K) 0)
  have hτT : (⟨τ, hτH⟩ : H) ∈ qgTranslSub hHA := ⟨_, hτ⟩
  have hs : (⟨τ, hτH⟩ : H)⁻¹ * x = 1 := by
    refine eq_one_of_mem_pCore_of_mem_qgStabT hHA hlin
      (mul_mem (inv_mem (qgTranslSub_le_pCore hHA hτT)) hx) ?_
    rw [mem_qgStabT_iff hHA, Subgroup.coe_mul,
      qgInduced_mul (hHA ((⟨τ, hτH⟩ : H)⁻¹).2) (hHA x.2)]
    have h1 := qgInduced_inv_apply' hHA ⟨τ, hτH⟩ 0
    have h2 : qgInduced (((⟨τ, hτH⟩ : H)) : QGAut K) 0 = qgInduced (x : QGAut K) 0 := by
      change qgInduced τ 0 = _
      rw [hτ, zero_add]
    rwa [h2] at h1
  rw [← inv_mul_eq_one.1 hs]
  exact hτT

end Hyp

end Subgroup

theorem characteristic_two_quadratic_graph_affine_semilinear_translations
    (K : Type*) [Field K] [Finite K] [CharP K 2] :
    qgOmega K + qgOmega K = {0} ∪ {e | e.1 = 0 ∧ (e.2.1, e.2.2.1) ≠ (0, 0)} ∧
    AddSubgroup.closure (qgOmega K) = ⊤ ∧
    (∀ α ∈ qgStab K, (qgW K).map (Multiplicative.toAdd α).toAddMonoidHom = qgW K ∧
      (qgZ K).map (Multiplicative.toAdd α).toAddMonoidHom = qgZ K) ∧
    (∀ α ∈ qgStab K, (∀ v, Multiplicative.toAdd α (qgPoint v) = qgPoint v) → α = 1) ∧
    (∀ g : (Fin 2 → K) → Fin 2 → K,
      (∃ α ∈ qgStab K, ∀ v, Multiplicative.toAdd α (qgPoint v) = qgPoint (g v)) ↔
        ∃ (v₀ : Fin 2 → K) (M : GL (Fin 2) K) (σ : K ≃+* K),
          ∀ v, g v = v₀ + (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (v i)) ∧
    (∀ (v₀ v₀' : Fin 2 → K) (M M' : GL (Fin 2) K) (σ σ' : K ≃+* K),
      (∀ v : Fin 2 → K, v₀ + (M : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => σ (v i)) =
        v₀' + (M' : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => σ' (v i))) →
      v₀ = v₀' ∧ M = M' ∧ σ = σ') ∧
    ∀ H : Subgroup (QGAut K), H ≤ qgStab K →
      (∀ e ∈ qgOmega K, ∀ e' ∈ qgOmega K, ∃ h ∈ H, Multiplicative.toAdd h e = e') →
      (∀ M : GL (Fin 2) K, ∃ h ∈ H, Multiplicative.toAdd h (qgT K) = qgT K ∧
        ∀ v, Multiplicative.toAdd h (qgPoint v) =
          qgPoint ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) →
      (∀ x ∈ CFSG.pCore 2 H, ∃ u : Fin 2 → K, ∀ v,
        Multiplicative.toAdd (x : QGAut K) (qgPoint v) = qgPoint (v + u)) ∧
      (∀ u : Fin 2 → K, ∃ x ∈ CFSG.pCore 2 H, ∀ v,
        Multiplicative.toAdd (x : QGAut K) (qgPoint v) = qgPoint (v + u)) ∧
      IsElementaryAbelian 2 (CFSG.pCore 2 H) ∧ Nat.card (CFSG.pCore 2 H) = Nat.card K ^ 2 ∧
      (∀ e ∈ qgOmega K, ∀ e' ∈ qgOmega K,
        ∃! x : H, x ∈ CFSG.pCore 2 H ∧ Multiplicative.toAdd (x : QGAut K) e = e') ∧
      (∀ h : H, ∃ x ∈ CFSG.pCore 2 H, ∃ s ∈ qgStabT H, h = x * s) ∧
      CFSG.pCore 2 H ⊓ qgStabT H = ⊥ := by
  refine ⟨qgOmega_add_qgOmega, closure_qgOmega, fun α hα => ⟨map_qgW hα, map_qgZ hα⟩,
    fun α hα h => eq_one_of_qgInduced hα fun v => qgPoint_injective (by
      rw [qgPoint_qgInduced hα, h]),
    induced_iff_affine, fun _ _ _ _ _ _ h => affine_params_unique h,
    fun H hHA htrans hlin => ?_⟩
  have htrans' : ∀ v w : Fin 2 → K, ∃ h ∈ H, qgInduced h v = w := fun v w => by
    obtain ⟨h, hh, hvw⟩ := htrans _ (qgPoint_mem v) _ (qgPoint_mem w)
    exact ⟨h, hh, qgPoint_injective (by rw [qgPoint_qgInduced (hHA hh), hvw])⟩
  have hlin' : ∀ M : GL (Fin 2) K, ∃ h ∈ H,
      ∀ v, qgInduced h v = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ v := fun M => by
    obtain ⟨h, hh, -, hM⟩ := hlin M
    exact ⟨h, hh, fun v => qgPoint_injective (by rw [qgPoint_qgInduced (hHA hh), hM])⟩
  have hPT := pCore_eq_qgTranslSub hHA htrans' hlin'
  refine ⟨fun x hx => ?_, fun u => ?_, ?_, ?_, fun e he e' he' => ?_, fun h => ?_, ?_⟩
  · rw [hPT] at hx
    obtain ⟨u, hu⟩ := hx
    exact ⟨u, fun v => by rw [← qgPoint_qgInduced (hHA x.2), hu]⟩
  · obtain ⟨x, hx, hxu⟩ := exists_transl_mem hHA htrans' hlin' u
    refine ⟨⟨x, hx⟩, hPT ▸ ⟨u, hxu⟩, fun v => ?_⟩
    rw [← qgPoint_qgInduced (hHA hx)]
    exact congrArg qgPoint (hxu v)
  · rw [hPT]
    exact isElementaryAbelian_qgTranslSub hHA
  · rw [hPT]
    exact card_qgTranslSub hHA htrans' hlin'
  · obtain ⟨v, rfl⟩ := mem_qgOmega_iff_exists.1 he
    obtain ⟨v', rfl⟩ := mem_qgOmega_iff_exists.1 he'
    obtain ⟨x, hx, hxu⟩ := exists_transl_mem hHA htrans' hlin' (v' - v)
    refine ⟨⟨x, hx⟩, ⟨hPT ▸ ⟨_, hxu⟩, ?_⟩, ?_⟩
    · change Multiplicative.toAdd x (qgPoint v) = qgPoint v'
      rw [← qgPoint_qgInduced (hHA hx), hxu, add_sub_cancel]
    · rintro y ⟨hy, hye⟩
      rw [hPT] at hy
      have hx' : (⟨x, hx⟩ : H) ∈ qgTranslSub hHA := ⟨_, hxu⟩
      refine eq_of_mem_qgTranslSub hHA hy hx' ?_
      obtain ⟨u, hu⟩ := hy
      have h1 : v + u = v' := by
        apply qgPoint_injective
        rw [← hu, qgPoint_qgInduced (hHA y.2), hye]
      change qgInduced ((y : H) : QGAut K) 0 = qgInduced x 0
      rw [hu, hxu, zero_add, zero_add, ← h1, add_sub_cancel_left]
  · obtain ⟨x, hx, hxu⟩ := exists_transl_mem hHA htrans' hlin' (qgInduced (h : QGAut K) 0)
    refine ⟨⟨x, hx⟩, hPT ▸ ⟨_, hxu⟩, (⟨x, hx⟩ : H)⁻¹ * h, ?_, by group⟩
    rw [mem_qgStabT_iff hHA, Subgroup.coe_mul,
      qgInduced_mul (hHA ((⟨x, hx⟩ : H)⁻¹).2) (hHA h.2)]
    have h1 := qgInduced_inv_apply' hHA ⟨x, hx⟩ 0
    have h2 : qgInduced (((⟨x, hx⟩ : H)) : QGAut K) 0 = qgInduced (h : QGAut K) 0 := by
      change qgInduced x 0 = _
      rw [hxu, zero_add]
    rwa [h2] at h1
  · rw [eq_bot_iff]
    rintro y ⟨hy, hyt⟩
    exact (Subgroup.mem_bot).2 (eq_one_of_mem_pCore_of_mem_qgStabT hHA hlin' hy hyt)

end CFSG.LocalAnalysis.SteinbergCD
