module

public import CFSG.RankThree.FFModules.Transvections
public import CFSG.RankThree.FFModules.Offenders
public import Mathlib.RepresentationTheory.Irreducible

public section

namespace CFSG.RankThree.FFModules

open scoped MatrixGroups
open Matrix Module

universe u

@[expose] def FFClassificationSL3 (F : Type*) [Field F] : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(3, F) W), ρ.IsIrreducible → (∃ g, ρ g ≠ 1) →
    ∀ B : Subgroup SL(3, F), CFSG.IsElementaryAbelian 2 B → B ≠ ⊥ →
      finrank (ZMod 2) W - finrank (ZMod 2) (fixSub ρ B) ≤ Nat.log 2 (Nat.card B) →
      IsNaturalModule ρ ∨ IsDualNaturalModule ρ

section Factors

variable {K : Type*} [Group K] {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) K V}

@[expose] def factorSub (U U' : Subrepresentation ρ) : Submodule (ZMod 2) U'.toSubmodule :=
  U.toSubmodule.comap U'.toSubmodule.subtype

@[expose] def factorRep (U U' : Subrepresentation ρ) :
    Representation (ZMod 2) K (U'.toSubmodule ⧸ factorSub U U') :=
  U'.toRepresentation.quotient (factorSub U U') fun g _ hx => U.apply_mem_toSubmodule g hx

theorem factorRep_mk (U U' : Subrepresentation ρ) (k : K) (x : U'.toSubmodule) :
    factorRep U U' k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (U'.toRepresentation k x) :=
  rfl

structure IsCompositionSeries (r : ℕ) (Vs : Fin (r + 1) → Subrepresentation ρ) : Prop where
  zero : Vs 0 = ⊥
  last : Vs (Fin.last r) = ⊤
  covBy : ∀ i : Fin r, Vs i.castSucc ⋖ Vs i.succ

theorem factor_invariant_eq_bot_or_top {U U' : Subrepresentation ρ} (h : U ⋖ U')
    (X : Submodule (ZMod 2) (U'.toSubmodule ⧸ factorSub U U'))
    (hX : ∀ k, ∀ x ∈ X, factorRep U U' k x ∈ X) : X = ⊥ ∨ X = ⊤ := by
  let Y : Subrepresentation ρ :=
    { toSubmodule := (X.comap (factorSub U U').mkQ).map U'.toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro k _ ⟨x, hx, rfl⟩
        refine ⟨U'.toRepresentation k x, ?_, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap] at hx ⊢
        exact hX k _ hx }
  have hUY : U ≤ Y := fun v hv => by
    refine ⟨⟨v, h.1.le hv⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr (show _ ∈ factorSub U U' from hv)]
    exact X.zero_mem
  have hYU' : Y ≤ U' := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  rcases eq_or_lt_of_le hUY with hUY' | hUY'
  · left
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hxY : (x : V) ∈ Y := ⟨x, hz, rfl⟩
    rw [← hUY'] at hxY
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hxY
  · right
    have hY : Y = U' := eq_of_le_of_not_lt hYU' (h.2 hUY')
    rw [eq_top_iff]
    intro z _
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hxY : (x : V) ∈ Y := by rw [hY]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hxY
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy

theorem factor_nontrivial {U U' : Subrepresentation ρ} (h : U ⋖ U') :
    Nontrivial (U'.toSubmodule ⧸ factorSub U U') := by
  obtain ⟨v, hvU', hvU⟩ := IsConcreteLE.exists_of_lt h.1
  refine ⟨⟨Submodule.Quotient.mk ⟨v, hvU'⟩, 0, ?_⟩⟩
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  exact hvU

theorem exists_fixed_ne_zero_of_isPGroup {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] [Nontrivial M] (σ : Representation (ZMod 2) K M) {P : Subgroup K}
    (hP : IsPGroup 2 P) : ∃ x : M, x ≠ 0 ∧ ∀ p ∈ P, σ p x = x := by
  let _ : MulAction P M := MulAction.compHom M (σ.comp P.subtype)
  have hdvd : 2 ∣ Nat.card M := by
    have h1 : Nat.card M = 2 ^ Module.finrank (ZMod 2) M := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have h2 : 0 < Module.finrank (ZMod 2) M := Module.finrank_pos
    rw [h1]
    exact dvd_pow_self 2 h2.ne'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : (0 : M) ∈ MulAction.fixedPoints P M := fun p => map_zero (σ p)
  obtain ⟨x, hx, hx0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hdvd h0
  exact ⟨x, fun h => hx0 h.symm, fun p hp => hx ⟨p, hp⟩⟩

theorem factor_finite [Finite V] (U U' : Subrepresentation ρ) :
    Finite (U'.toSubmodule ⧸ factorSub U U') :=
  Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)

end Factors

section PCore

variable {K : Type*} [Group K] {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] {ρ : Representation (ZMod 2) K V}

theorem factor_trivial_pCore {U U' : Subrepresentation ρ} (h : U ⋖ U') {p : K}
    (hp : p ∈ CFSG.pCore 2 K) (x : U'.toSubmodule ⧸ factorSub U U') : factorRep U U' p x = x := by
  have : Nontrivial (U'.toSubmodule ⧸ factorSub U U') := factor_nontrivial h
  have : Finite (U'.toSubmodule ⧸ factorSub U U') := factor_finite U U'
  let X : Submodule (ZMod 2) (U'.toSubmodule ⧸ factorSub U U') :=
    { carrier := {x | ∀ p ∈ CFSG.pCore 2 K, factorRep U U' p x = x}
      add_mem' := fun {x y} hx hy p hp => by rw [map_add, hx p hp, hy p hp]
      zero_mem' := fun p _ => map_zero _
      smul_mem' := fun c x hx p hp => by rw [map_smul, hx p hp] }
  have hX : ∀ k, ∀ x ∈ X, factorRep U U' k x ∈ X := by
    intro k x hx p hp
    have hconj : k⁻¹ * p * k ∈ CFSG.pCore 2 K := by
      have := (CFSG.pCore_normal (p := 2) (G := K)).conj_mem p hp k⁻¹
      rwa [inv_inv] at this
    have e : p = k * (k⁻¹ * p * k) * k⁻¹ := by group
    change factorRep U U' p (factorRep U U' k x) = factorRep U U' k x
    rw [← Module.End.mul_apply, ← map_mul, e, mul_assoc, mul_assoc, inv_mul_cancel, mul_one,
      map_mul, Module.End.mul_apply, hx _ hconj]
  rcases factor_invariant_eq_bot_or_top h X hX with hbot | htop
  · exfalso
    obtain ⟨y, hy0, hy⟩ := exists_fixed_ne_zero_of_isPGroup (factorRep U U')
      (CFSG.pCore_isPGroup (p := 2) (G := K))
    have hyX : y ∈ X := hy
    rw [hbot, Submodule.mem_bot] at hyX
    exact hy0 hyX
  · have hx : x ∈ X := by rw [htop]; exact Submodule.mem_top
    exact hx p hp

theorem factor_isTrivial_pCore {U U' : Subrepresentation ρ} (h : U ⋖ U') :
    Representation.IsTrivial ((factorRep U U').comp (CFSG.pCore 2 K).subtype) :=
  ⟨fun p => LinearMap.ext fun x => factor_trivial_pCore h p.2 x⟩

variable {F : Type*} [Field F] (ψ : K ⧸ CFSG.pCore 2 K ≃* SL(3, F))

@[expose] noncomputable def factorSL3 {U U' : Subrepresentation ρ} (h : U ⋖ U') :
    Representation (ZMod 2) SL(3, F) (U'.toSubmodule ⧸ factorSub U U') :=
  have := factor_isTrivial_pCore h
  ((factorRep U U').ofQuotient (CFSG.pCore 2 K)).comp ψ.symm.toMonoidHom

theorem factorSL3_apply {U U' : Subrepresentation ρ} (h : U ⋖ U') (k : K)
    (x : U'.toSubmodule ⧸ factorSub U U') :
    factorSL3 ψ h (ψ (k : K ⧸ CFSG.pCore 2 K)) x = factorRep U U' k x := by
  simp only [factorSL3, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    Representation.ofQuotient_coe_apply]

theorem factorSL3_isIrreducible {U U' : Subrepresentation ρ} (h : U ⋖ U') :
    (factorSL3 ψ h).IsIrreducible := by
  have : Nontrivial (U'.toSubmodule ⧸ factorSub U U') := factor_nontrivial h
  have hnt : Nontrivial (Subrepresentation (factorSL3 ψ h)) := by
    refine ⟨⟨⊥, ⊤, fun he => ?_⟩⟩
    obtain ⟨x, hx⟩ := exists_ne (0 : U'.toSubmodule ⧸ factorSub U U')
    have h1 : x ∈ (⊤ : Subrepresentation (factorSL3 ψ h)).toSubmodule := Submodule.mem_top
    rw [← he] at h1
    exact hx h1
  refine IsSimpleOrder.mk fun a => ?_
  have hinv : ∀ k, ∀ x ∈ a.toSubmodule, factorRep U U' k x ∈ a.toSubmodule := by
    intro k x hx
    rw [← factorSL3_apply ψ h]
    exact a.apply_mem_toSubmodule _ hx
  rcases factor_invariant_eq_bot_or_top h a.toSubmodule hinv with hb | ht
  · exact Or.inl (Subrepresentation.toSubmodule_injective hb)
  · exact Or.inr (Subrepresentation.toSubmodule_injective ht)

theorem fixSub_factorSL3 {U U' : Subrepresentation ρ} (h : U ⋖ U') (A : Subgroup K) :
    fixSub (factorSL3 ψ h) ((A.map (QuotientGroup.mk' (CFSG.pCore 2 K))).map ψ.toMonoidHom) =
      fixSub (factorRep U U') A := by
  ext x
  rw [mem_fixSub, mem_fixSub]
  constructor
  · intro hx a ha
    rw [← factorSL3_apply ψ h]
    exact hx _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  · rintro hx _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have := factorSL3_apply ψ h a x
    simp only [QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom] at this ⊢
    rw [this]
    exact hx a ha

end PCore

section Transport

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {σ : Representation (ZMod 2) SL(3, F) M}

theorem IsNaturalModule.card_fixSub (h : IsNaturalModule σ) (B : Subgroup SL(3, F)) :
    Nat.card (fixSub σ B) = Nat.card (natFix B) := by
  obtain ⟨φ, hφ⟩ := h
  have key : ∀ w, w ∈ fixSub σ B ↔ φ w ∈ natFix B := by
    intro w
    rw [mem_fixSub, mem_natFix]
    constructor
    · intro hw b hb
      rw [← hφ, hw b hb]
    · intro hw b hb
      apply φ.injective
      rw [hφ, hw b hb]
  exact Nat.card_congr (φ.toEquiv.subtypeEquiv key)

theorem IsDualNaturalModule.card_fixSub (h : IsDualNaturalModule σ) (B : Subgroup SL(3, F)) :
    Nat.card (fixSub σ B) = Nat.card (dualFix B) := by
  obtain ⟨φ, hφ⟩ := h
  have key : ∀ w, w ∈ fixSub σ B ↔ φ w ∈ dualFix B := by
    intro w
    rw [mem_fixSub, mem_dualFix]
    constructor
    · intro hw b hb
      rw [← hφ, hw b hb]
    · intro hw b hb
      apply φ.injective
      rw [hφ, hw b hb]
  exact Nat.card_congr (φ.toEquiv.subtypeEquiv key)

theorem IsNaturalModule.card [Fintype F] (h : IsNaturalModule σ) :
    Nat.card M = Fintype.card F ^ 3 := by
  obtain ⟨φ, -⟩ := h
  rw [Nat.card_congr φ.toEquiv, card_vec]

theorem IsDualNaturalModule.card [Fintype F] (h : IsDualNaturalModule σ) :
    Nat.card M = Fintype.card F ^ 3 := by
  obtain ⟨φ, -⟩ := h
  rw [Nat.card_congr φ.toEquiv, card_vec]

theorem codim_eq_of_card [Finite M] {S : Submodule (ZMod 2) M} {a b : ℕ}
    (hM : Nat.card M = 2 ^ a) (hS : Nat.card S = 2 ^ b) :
    finrank (ZMod 2) M - finrank (ZMod 2) S = a - b := by
  rw [card_eq_two_pow_finrank' (W := M)] at hM
  rw [card_eq_two_pow_finrank] at hS
  rw [Nat.pow_right_injective le_rfl hM, Nat.pow_right_injective le_rfl hS]

theorem le_codim_of_card [Finite M] {S : Submodule (ZMod 2) M} {n : ℕ}
    (h : 2 ^ n * Nat.card S ≤ Nat.card M) :
    n ≤ finrank (ZMod 2) M - finrank (ZMod 2) S := by
  rw [card_eq_two_pow_finrank' (W := M), card_eq_two_pow_finrank, ← pow_add,
    Nat.pow_le_pow_iff_right (by norm_num)] at h
  omega

end Transport

section Main

variable {K : Type*} [Group K] {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] {ρ : Representation (ZMod 2) K V} {F : Type*} [Field F]
  (ψ : K ⧸ CFSG.pCore 2 K ≃* SL(3, F))

open _root_.Classical in
@[expose] noncomputable def nontrivialFactors {r : ℕ} (Vs : Fin (r + 1) → Subrepresentation ρ) :
    Finset (Fin r) :=
  Finset.univ.filter fun i => ∃ k, factorRep (Vs i.castSucc) (Vs i.succ) k ≠ 1

omit [Finite V] in
theorem mem_nontrivialFactors {r : ℕ} {Vs : Fin (r + 1) → Subrepresentation ρ} {i : Fin r} :
    i ∈ nontrivialFactors Vs ↔ ∃ k, factorRep (Vs i.castSucc) (Vs i.succ) k ≠ 1 := by
  classical
  simp [nontrivialFactors]

@[expose] noncomputable def factorCodim {r : ℕ} (Vs : Fin (r + 1) → Subrepresentation ρ)
    (A : Subgroup K) (i : Fin r) : ℕ :=
  finrank (ZMod 2) ((Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) -
    finrank (ZMod 2) (fixSub (factorRep (Vs i.castSucc) (Vs i.succ)) A)

@[expose] def IsNaturalFactor (U U' : Subrepresentation ρ) : Prop :=
  ∃ φ : (U'.toSubmodule ⧸ factorSub U U') ≃+ (Fin 3 → F), ∀ k x,
    φ (factorRep U U' k x) = ((ψ (k : K ⧸ CFSG.pCore 2 K) : SL(3, F)) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ φ x

@[expose] def IsDualNaturalFactor (U U' : Subrepresentation ρ) : Prop :=
  ∃ φ : (U'.toSubmodule ⧸ factorSub U U') ≃+ (Fin 3 → F), ∀ k x,
    φ (factorRep U U' k x) = dualMat (ψ (k : K ⧸ CFSG.pCore 2 K)) *ᵥ φ x

theorem isNaturalFactor_of {U U' : Subrepresentation ρ} (h : U ⋖ U')
    (hN : IsNaturalModule (factorSL3 ψ h)) : IsNaturalFactor ψ U U' := by
  obtain ⟨φ, hφ⟩ := hN
  exact ⟨φ, fun k x => by rw [← factorSL3_apply ψ h, hφ]⟩

theorem isDualNaturalFactor_of {U U' : Subrepresentation ρ} (h : U ⋖ U')
    (hN : IsDualNaturalModule (factorSL3 ψ h)) : IsDualNaturalFactor ψ U U' := by
  obtain ⟨φ, hφ⟩ := hN
  exact ⟨φ, fun k x => by rw [← factorSL3_apply ψ h, hφ]⟩

theorem isNaturalModule_of {U U' : Subrepresentation ρ} (h : U ⋖ U')
    (hN : IsNaturalFactor ψ U U') : IsNaturalModule (factorSL3 ψ h) := by
  obtain ⟨φ, hφ⟩ := hN
  refine ⟨φ, fun g x => ?_⟩
  obtain ⟨q, rfl⟩ := ψ.surjective g
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [factorSL3_apply, hφ]

theorem isDualNaturalModule_of {U U' : Subrepresentation ρ} (h : U ⋖ U')
    (hN : IsDualNaturalFactor ψ U U') : IsDualNaturalModule (factorSL3 ψ h) := by
  obtain ⟨φ, hφ⟩ := hN
  refine ⟨φ, fun g x => ?_⟩
  obtain ⟨q, rfl⟩ := ψ.surjective g
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [factorSL3_apply, hφ]

variable [Fintype F] [CharP F 2]

theorem chief_factors_of_FFClassification {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (hFF : FFClassificationSL3.{u} F) {r : ℕ} {Vs : Fin (r + 1) → Subrepresentation ρ}
    (hVs : IsCompositionSeries r Vs) (A : Subgroup K) [CFSG.IsElementaryAbelian 2 A]
    (hA : ¬A ≤ CFSG.pCore 2 K)
    (hsum : ∑ i ∈ nontrivialFactors Vs, factorCodim Vs A i ≤
      Nat.log 2 (Nat.card (A.map (QuotientGroup.mk' (CFSG.pCore 2 K))))) :
    (∀ i : Fin r, ∀ p ∈ CFSG.pCore 2 K, ∀ x,
      factorRep (Vs i.castSucc) (Vs i.succ) p x = x) ∧
    (∀ i ∈ nontrivialFactors Vs,
      (IsNaturalFactor ψ (Vs i.castSucc) (Vs i.succ) ∨
        IsDualNaturalFactor ψ (Vs i.castSucc) (Vs i.succ)) ∧
      ∀ k : K, (k : K ⧸ CFSG.pCore 2 K) ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) →
        (k : K ⧸ CFSG.pCore 2 K) ≠ 1 → ∀ x, factorRep (Vs i.castSucc) (Vs i.succ) k x = x →
          x = 0) ∧
    (nontrivialFactors Vs).card ≤ 2 ∧
    ((nontrivialFactors Vs).card = 2 → ∃ i j, i ∈ nontrivialFactors Vs ∧
      j ∈ nontrivialFactors Vs ∧ i < j ∧
      (∃ φ : ((Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) ≃+
          ((Vs j.succ).toSubmodule ⧸ factorSub (Vs j.castSucc) (Vs j.succ)),
        ∀ k x, φ (factorRep (Vs i.castSucc) (Vs i.succ) k x) =
          factorRep (Vs j.castSucc) (Vs j.succ) k (φ x)) ∧
      Nat.card (A.map (QuotientGroup.mk' (CFSG.pCore 2 K))) = Fintype.card F ^ 2 ∧
      (IsNaturalFactor ψ (Vs i.castSucc) (Vs i.succ) →
        ∃ H : Submodule F (Fin 3 → F), finrank F H = 2 ∧
          (A.map (QuotientGroup.mk' (CFSG.pCore 2 K))).map ψ.toMonoidHom =
            transvectionGroup H) ∧
      (IsDualNaturalFactor ψ (Vs i.castSucc) (Vs i.succ) →
        ∃ p : Submodule F (Fin 3 → F), finrank F p = 1 ∧
          (A.map (QuotientGroup.mk' (CFSG.pCore 2 K))).map ψ.toMonoidHom =
            transvectionGroup p)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 K with hP
  set Abar := A.map (QuotientGroup.mk' P) with hAbar
  set B := Abar.map ψ.toMonoidHom with hB
  have hBea : CFSG.IsElementaryAbelian 2 B := by
    have : CFSG.IsElementaryAbelian 2 Abar := CFSG.IsElementaryAbelian.map _
    exact CFSG.IsElementaryAbelian.map _
  have hB2 : ∀ b ∈ B, b * b = 1 := fun b hb => by
    rw [← pow_two]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
  have hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun b hb c hc => by
    have := hBea.toIsMulCommutative.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩
    exact congrArg Subtype.val this
  have hcardB : Nat.card B = Nat.card Abar :=
    Nat.card_congr (Abar.equivMapOfInjective _ ψ.injective).toEquiv.symm
  have hBne : B ≠ ⊥ := by
    obtain ⟨a, haA, haP⟩ := Set.not_subset.mp hA
    intro hbot
    have hmem : ψ (a : K ⧸ P) ∈ B := ⟨_, ⟨a, haA, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, map_eq_one_iff _ ψ.injective, QuotientGroup.eq_one_iff] at hmem
    exact haP hmem
  have hBle : Nat.card B ≤ Fintype.card F ^ 2 := card_le_sq_of_elementary hB2 hBc
  have hlog : Nat.log 2 (Nat.card Abar) ≤ 2 * n := by
    rw [← hcardB]
    calc Nat.log 2 (Nat.card B) ≤ Nat.log 2 (Fintype.card F ^ 2) := Nat.log_mono_right hBle
      _ = 2 * n := by rw [hF, ← pow_mul, Nat.log_pow (by norm_num), mul_comm]
  have hcodim : ∀ i : Fin r, factorCodim Vs A i =
      finrank (ZMod 2) ((Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) -
        finrank (ZMod 2) (fixSub (factorSL3 ψ (hVs.covBy i)) B) := by
    intro i
    rw [factorCodim, hB, hAbar, fixSub_factorSL3]
  have hle_sum : ∀ i ∈ nontrivialFactors Vs, factorCodim Vs A i ≤ Nat.log 2 (Nat.card B) := by
    intro i hi
    rw [hcardB]
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans hsum
  have hclass : ∀ i ∈ nontrivialFactors Vs,
      IsNaturalModule (factorSL3 ψ (hVs.covBy i)) ∨
        IsDualNaturalModule (factorSL3 ψ (hVs.covBy i)) := by
    intro i hi
    have : Finite ((Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) :=
      factor_finite _ _
    refine hFF _ (factorSL3 ψ (hVs.covBy i)) (factorSL3_isIrreducible ψ (hVs.covBy i)) ?_ B
      hBea hBne ?_
    · obtain ⟨k, hk⟩ := mem_nontrivialFactors.mp hi
      exact ⟨ψ (k : K ⧸ P), by
        intro h1
        apply hk
        refine LinearMap.ext fun x => ?_
        rw [← factorSL3_apply ψ (hVs.covBy i), h1]⟩
    · rw [← hcodim]
      exact hle_sum i hi
  have hge : ∀ i ∈ nontrivialFactors Vs, n ≤ factorCodim Vs A i := by
    intro i hi
    have : Finite ((Vs i.succ).toSubmodule ⧸ factorSub (Vs i.castSucc) (Vs i.succ)) :=
      factor_finite _ _
    rw [hcodim]
    rcases hclass i hi with hN | hN
    · apply le_codim_of_card
      rw [hN.card_fixSub, hN.card, ← card_vec]
      exact card_natFix_mul_le hF hBne
    · apply le_codim_of_card
      rw [hN.card_fixSub, hN.card, ← card_vec]
      exact card_dualFix_mul_le hF hBne
  have hsumge : (nontrivialFactors Vs).card * n ≤ Nat.log 2 (Nat.card Abar) := by
    calc (nontrivialFactors Vs).card * n = ∑ _i ∈ nontrivialFactors Vs, n := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ nontrivialFactors Vs, factorCodim Vs A i := Finset.sum_le_sum hge
      _ ≤ _ := hsum
  have hm2 : (nontrivialFactors Vs).card ≤ 2 := by
    have h1 := hsumge.trans hlog
    by_contra h2
    push Not at h2
    have : 3 * n ≤ (nontrivialFactors Vs).card * n := Nat.mul_le_mul_right n h2
    omega
  refine ⟨fun i p hp x => factor_trivial_pCore (hVs.covBy i) hp x, fun i hi => ⟨?_, ?_⟩, hm2, ?_⟩
  · rcases hclass i hi with hN | hN
    · exact Or.inl (isNaturalFactor_of ψ _ hN)
    · exact Or.inr (isDualNaturalFactor_of ψ _ hN)
  · intro k hkz hk1 x hx
    have hz : ψ (k : K ⧸ P) ∈ Subgroup.center SL(3, F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := ψ.surjective g
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hkz) q]
    have hz1 : ψ (k : K ⧸ P) ≠ 1 := by
      rwa [Ne, map_eq_one_iff _ ψ.injective]
    have hx' : factorSL3 ψ (hVs.covBy i) (ψ (k : K ⧸ P)) x = x := by
      rw [factorSL3_apply]; exact hx
    rcases hclass i hi with hN | hN
    · exact hN.eq_zero_of_center hz hz1 hx'
    · exact hN.eq_zero_of_center hz hz1 hx'
  · intro hm
    obtain ⟨i, j, hij, hNF⟩ := Finset.card_eq_two.mp hm
    wlog hlt : i < j generalizing i j
    · exact this j i hij.symm (by rw [hNF, Finset.pair_comm]) (lt_of_le_of_ne (not_lt.mp hlt)
        hij.symm)
    have hi : i ∈ nontrivialFactors Vs := by rw [hNF]; exact Finset.mem_insert_self _ _
    have hj : j ∈ nontrivialFactors Vs := by
      rw [hNF]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hsum2 : factorCodim Vs A i + factorCodim Vs A j ≤ 2 * n := by
      have := hsum.trans hlog
      rwa [hNF, Finset.sum_pair hij] at this
    have hci := hge i hi
    have hcj := hge j hj
    have hcieq : factorCodim Vs A i = n := by omega
    have hcjeq : factorCodim Vs A j = n := by omega
    have hlogeq : Nat.log 2 (Nat.card B) = 2 * n := by
      have h1 : 2 * n ≤ Nat.log 2 (Nat.card Abar) := by
        have h2 : factorCodim Vs A i + factorCodim Vs A j ≤ Nat.log 2 (Nat.card Abar) := by
          have := hsum
          rwa [hNF, Finset.sum_pair hij] at this
        rw [hcieq, hcjeq] at h2
        calc 2 * n = n + n := by ring
          _ ≤ _ := h2
      rw [hcardB]
      exact le_antisymm hlog h1
    have hcardBq : Nat.card B = Fintype.card F ^ 2 := by
      have hpB : IsPGroup 2 B := CFSG.IsElementaryAbelian.isPGroup 2 B
      obtain ⟨k, hk⟩ := hpB.exists_card_eq
      rw [hk, Nat.log_pow (by norm_num)] at hlogeq
      rw [hk, hlogeq, hF, ← pow_mul, mul_comm]
    obtain ⟨S, hSdim, hBS⟩ := eq_transvectionGroup_of_card hB2 hBc hcardBq
    have hSbot : S ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hSdim; omega
    have hStop : S ≠ ⊤ := by
      intro h; rw [h, finrank_top, finrank_fin3] at hSdim; omega
    have hcodimN : ∀ l ∈ nontrivialFactors Vs, IsNaturalModule (factorSL3 ψ (hVs.covBy l)) →
        factorCodim Vs A l = (3 - finrank F S) * n := by
      intro l _ hN
      have : Finite ((Vs l.succ).toSubmodule ⧸ factorSub (Vs l.castSucc) (Vs l.succ)) :=
        factor_finite _ _
      rw [hcodim]
      refine codim_eq_of_card (a := 3 * n) (b := finrank F S * n) ?_ ?_ |>.trans ?_
      · rw [hN.card, hF, ← pow_mul, mul_comm]
      · rw [hN.card_fixSub, hBS, card_natFix_transvectionGroup hSbot, hF, ← pow_mul, mul_comm]
      · rw [Nat.sub_mul]
    have hcodimD : ∀ l ∈ nontrivialFactors Vs, IsDualNaturalModule (factorSL3 ψ (hVs.covBy l)) →
        factorCodim Vs A l = finrank F S * n := by
      intro l _ hN
      have : Finite ((Vs l.succ).toSubmodule ⧸ factorSub (Vs l.castSucc) (Vs l.succ)) :=
        factor_finite _ _
      rw [hcodim]
      refine codim_eq_of_card (a := 3 * n) (b := (3 - finrank F S) * n) ?_ ?_ |>.trans ?_
      · rw [hN.card, hF, ← pow_mul, mul_comm]
      · rw [hN.card_fixSub, hBS, card_dualFix_transvectionGroup hStop, hF, ← pow_mul, mul_comm]
      · rw [← Nat.sub_mul]
        congr 1
        omega
    have hpos : 0 < n := hn
    refine ⟨i, j, hi, hj, hlt, ?_, by rw [← hcardB, hcardBq], fun hNi => ?_, fun hDi => ?_⟩
    ·
      rcases hclass i hi with hNi | hDi <;> rcases hclass j hj with hNj | hDj
      · obtain ⟨φi, hφi⟩ := hNi
        obtain ⟨φj, hφj⟩ := hNj
        refine ⟨φi.trans φj.symm, fun k x => ?_⟩
        apply φj.injective
        rw [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, ← factorSL3_apply ψ (hVs.covBy i),
          hφi, ← factorSL3_apply ψ (hVs.covBy j), hφj, AddEquiv.trans_apply,
          AddEquiv.apply_symm_apply]
      · exfalso
        have h1 := hcodimN i hi hNi
        have h2 := hcodimD j hj hDj
        rw [hcieq] at h1
        rw [hcjeq] at h2
        rcases hSdim with h | h <;> rw [h] at h1 h2 <;> omega
      · exfalso
        have h1 := hcodimD i hi hDi
        have h2 := hcodimN j hj hNj
        rw [hcieq] at h1
        rw [hcjeq] at h2
        rcases hSdim with h | h <;> rw [h] at h1 h2 <;> omega
      · obtain ⟨φi, hφi⟩ := hDi
        obtain ⟨φj, hφj⟩ := hDj
        refine ⟨φi.trans φj.symm, fun k x => ?_⟩
        apply φj.injective
        rw [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, ← factorSL3_apply ψ (hVs.covBy i),
          hφi, ← factorSL3_apply ψ (hVs.covBy j), hφj, AddEquiv.trans_apply,
          AddEquiv.apply_symm_apply]
    · have h1 := hcodimN i hi (isNaturalModule_of ψ (hVs.covBy i) hNi)
      rw [hcieq] at h1
      refine ⟨S, ?_, hBS⟩
      rcases hSdim with h | h
      · rw [h] at h1; omega
      · exact h
    · have h1 := hcodimD i hi (isDualNaturalModule_of ψ (hVs.covBy i) hDi)
      rw [hcieq] at h1
      refine ⟨S, ?_, hBS⟩
      rcases hSdim with h | h
      · exact h
      · rw [h] at h1; omega

end Main

end CFSG.RankThree.FFModules
