module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutBasic
public import CFSG.LieType.Chevalley.E6GraphLeviUnitary
public import CFSG.LieType.Chevalley.E6GraphLeviTheta

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SeitzReduction.E6Pilot (IsAutConj IsAutConjIn map_conj_map_conj_eq_conj_mul
  map_map_conj_eq_map_conj)

section TypeFree

variable {P P' : Type*} [Group P] [Group P']

variable {C : Type*} [Group C]

theorem isAutConjIn_map_conj {M J : Subgroup C} (h : IsAutConjIn M J) (hJM : J ≤ M) (g : C) :
    IsAutConjIn (M.map (MulAut.conj g).toMonoidHom) (J.map (MulAut.conj g).toMonoidHom) := by
  set E : M ≃* (M.map (MulAut.conj g).toMonoidHom : Subgroup C) :=
    M.equivMapOfInjective _ (MulAut.conj g).injective with hE
  have hJ : IsAutConj (J.subgroupOf M) := by
    intro α
    obtain ⟨m, hm, hmJ⟩ := h α
    refine ⟨⟨m, hm⟩, ?_⟩
    apply Subgroup.map_injective M.subtype_injective
    rw [hmJ, map_map_conj_eq_map_conj, subgroupOf_map_subtype, inf_of_le_left hJM]
    rfl
  have h1 := hJ.isAutConjIn_map E
  have h2 : ((J.subgroupOf M).map E.toMonoidHom).map
      (M.map (MulAut.conj g).toMonoidHom).subtype = J.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, mem_subgroupOf.1 hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hJM hy⟩, mem_subgroupOf.2 hy, rfl⟩
  rwa [h2] at h1

end TypeFree

section AntiId

variable {K : Type} [Field K]

@[expose] noncomputable def antiIdGL (K : Type) [Field K] : GL (Fin 6) K :=
  ⟨CFSG.LieType.Chevalley.E6GraphLevi.antiId K, CFSG.LieType.Chevalley.E6GraphLevi.antiId K,
    CFSG.LieType.Chevalley.E6GraphLevi.antiId_mul_self,
    CFSG.LieType.Chevalley.E6GraphLevi.antiId_mul_self⟩

theorem coe_antiIdGL :
    ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      CFSG.LieType.Chevalley.E6GraphLevi.antiId K :=
  rfl

theorem isPrimeFormGram_antiIdGL : IsPrimeFormGram (antiIdGL K) where
  symm := CFSG.LieType.Chevalley.E6GraphLevi.antiId_transpose
  prime := by
    intro i j
    rw [coe_antiIdGL]
    change (if j = Fin.rev i then (1 : K) else 0) ∈ (⊥ : Subfield K)
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem det_antiIdGL_ne_zero :
    ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (antiIdGL K).isUnit).ne_zero

theorem rev_eq_or_iff {i j : Fin 6} : (Fin.rev j = i ∨ Fin.rev j = Fin.rev i) ↔
    (j = i ∨ j = Fin.rev i) := by
  constructor
  · rintro (h1 | h1)
    · right
      rw [← h1, Fin.rev_rev]
    · left
      exact Fin.rev_inj.1 h1
  · rintro (h1 | h1)
    · right
      rw [h1]
    · left
      rw [h1, Fin.rev_rev]

@[expose] def jPairDiag (i : Fin 6) (s : Kˣ) : GL (Fin 6) K :=
  ⟨diagonal fun j => if j = i ∨ j = Fin.rev i then (s : K) else 1,
    diagonal fun j => if j = i ∨ j = Fin.rev i then ((s⁻¹ : Kˣ) : K) else 1, by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext j
      split_ifs <;> simp, by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext j
      split_ifs <;> simp⟩

theorem coe_jPairDiag (i : Fin 6) (s : Kˣ) :
    ((jPairDiag i s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagonal fun j => if j = i ∨ j = Fin.rev i then (s : K) else 1 :=
  rfl

theorem det_jPairDiag (i : Fin 6) (s : Kˣ) :
    ((jPairDiag i s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = (s : K) ^ 2 := by
  rw [coe_jPairDiag, det_diagonal, Fin.prod_univ_six]
  fin_cases i <;> simp [Fin.ext_iff, Fin.rev] <;> ring

end AntiId

section Block

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem jPairDiag_mem_primeFormUnitary (i : Fin 6) {s : Kˣ} (hs : h.norm (s : K) = 1) :
    jPairDiag i s ∈ primeFormUnitary h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
  rw [mem_primeFormUnitary, coe_jPairDiag, diagonal_map (map_zero _), diagonal_transpose,
    coe_antiIdGL]
  ext a b
  rw [mul_diagonal, diagonal_mul]
  simp only [CFSG.LieType.Chevalley.E6GraphLevi.antiId, Matrix.of_apply]
  by_cases hb : b = Fin.rev a
  · subst hb
    simp only [rev_eq_or_iff]
    split_ifs
    · rw [mul_one, mul_comm]
      exact hs
    · simp
  · simp [hb]

theorem norm_det_eq_one_of_mem_antiId {A : GL (Fin 6) K}
    (hA : A ∈ primeFormUnitary h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :
    h.norm ((A : Matrix (Fin 6) (Fin 6) K).det) = 1 := by
  have h1 := congrArg Matrix.det (mem_primeFormUnitary.1 hA)
  rw [det_mul, det_mul, det_transpose] at h1
  have h2 : ((A : Matrix (Fin 6) (Fin 6) K).map h.bar).det =
      h.bar (A : Matrix (Fin 6) (Fin 6) K).det := (RingHom.map_det h.bar _).symm
  rw [h2] at h1
  rw [UnitaryFieldData.norm, mul_comm]
  apply mul_right_cancel₀ (det_antiIdGL_ne_zero (K := K))
  linear_combination h1

theorem norm_eq_one_of_sq {s : Kˣ} {u : K} (hsu : (s : K) ^ 2 = u) (hu : h.norm u = 1) :
    h.norm (s : K) = 1 := by
  have := h.charP
  refine CharTwo.sq_injective ?_
  change h.norm (s : K) ^ 2 = 1 ^ 2
  rw [one_pow, ← hu, ← hsu, sq, sq, CFSG.ClassicalGroups.UnitaryFlag.norm_mul_eq h]

theorem det_jPairDiag_units (i : Fin 6) (s : Kˣ) :
    Matrix.GeneralLinearGroup.det (jPairDiag i s : GL (Fin 6) K) = s ^ 2 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_jPairDiag, Units.val_pow_eq_pow_val]

theorem isAutConj_map_mk_of_commute
    {H : Subgroup (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))} (i : Fin 6)
    (hcomm : ∀ (s : Kˣ), ∀ g ∈ H, jPairDiag i s * (g : GL (Fin 6) K) = g * jPairDiag i s)
    (hfield : ∀ (φ : K ≃+* K), ∀ g ∈ H, primeFormFieldSU h isPrimeFormGram_antiIdGL φ g ∈ H) :
    IsAutConj (H.map (QuotientGroup.mk' (normOneScalars h
      (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) 6))) := by
  have := h.finite
  have : CharP K 2 := h.charP
  have hK2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  intro α
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h (isPrimeFormGram_antiIdGL (K := K)) (n := 6)
    (by norm_num) (by norm_num) α
  set u : Kˣ := Matrix.GeneralLinearGroup.det (A : GL (Fin 6) K) with hu
  have huN : h.norm (u : K) = 1 := by
    rw [hu, Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one_of_mem_antiId h A.2
  obtain ⟨s, hs⟩ := CFSG.LieType.Chevalley.E6GraphLevi.exists_sq_eq_of_two hK2 u
  have hsN : h.norm (s : K) = 1 :=
    norm_eq_one_of_sq h (by rw [← Units.val_pow_eq_pow_val, hs]) huN
  have hDU := jPairDiag_mem_primeFormUnitary h i hsN
  have hB : (A : GL (Fin 6) K) * (jPairDiag i s)⁻¹ ∈
      gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    refine (mem_gramSU_iff_unitary h).2 ⟨mul_mem A.2 (inv_mem hDU), ?_⟩
    have hdet : Matrix.GeneralLinearGroup.det ((A : GL (Fin 6) K) * (jPairDiag i s)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hu, det_jPairDiag_units, hs, mul_inv_cancel]
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  refine ⟨QuotientGroup.mk' _ ⟨_, hB⟩, ?_⟩
  have hle : (H.map (QuotientGroup.mk' _)).map α.toMonoidHom ≤
      (H.map (QuotientGroup.mk' _)).map
        (MulAut.conj (QuotientGroup.mk' (normOneScalars h
          (gramSU h ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) 6)
          ⟨_, hB⟩)).toMonoidHom := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    have hφg := hfield φ g hg
    refine ⟨QuotientGroup.mk' _ (primeFormFieldSU h isPrimeFormGram_antiIdGL φ g),
      ⟨_, hφg, rfl⟩, ?_⟩
    have e1 : α (QuotientGroup.mk' _ g) = QuotientGroup.mk' _
        (primeFormConjSU h _ A (primeFormFieldSU h isPrimeFormGram_antiIdGL φ g)) := by
      rw [← hAφ, primeFormPsi_apply, MulAut.mul_apply]
      change primeFormConjAut h _ A (primeFormFieldAut h isPrimeFormGram_antiIdGL φ
        (g : primeFormP h _)) = _
      rw [primeFormFieldAut_mk, primeFormConjAut_mk]
      rfl
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, e1, MulAut.conj_apply, ← map_inv,
      ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hc : jPairDiag i s * (primeFormFieldSU h isPrimeFormGram_antiIdGL φ g : GL (Fin 6) K) =
        (primeFormFieldSU h isPrimeFormGram_antiIdGL φ g : GL (Fin 6) K) * jPairDiag i s :=
      hcomm s _ hφg
    change (A : GL (Fin 6) K) * (jPairDiag i s)⁻¹ *
        (primeFormFieldSU h isPrimeFormGram_antiIdGL φ g : GL (Fin 6) K) *
        ((A : GL (Fin 6) K) * (jPairDiag i s)⁻¹)⁻¹ =
      (A : GL (Fin 6) K) * (primeFormFieldSU h isPrimeFormGram_antiIdGL φ g : GL (Fin 6) K) *
        (A : GL (Fin 6) K)⁻¹
    have hc' : (jPairDiag i s)⁻¹ *
        (primeFormFieldSU h isPrimeFormGram_antiIdGL φ g : GL (Fin 6) K) * jPairDiag i s =
        (primeFormFieldSU h isPrimeFormGram_antiIdGL φ g : GL (Fin 6) K) := by
      rw [mul_assoc, ← hc, inv_mul_cancel_left]
    calc (A : GL (Fin 6) K) * (jPairDiag i s)⁻¹ *
          (primeFormFieldSU h isPrimeFormGram_antiIdGL φ g : GL (Fin 6) K) *
          ((A : GL (Fin 6) K) * (jPairDiag i s)⁻¹)⁻¹
        = (A : GL (Fin 6) K) * ((jPairDiag i s)⁻¹ *
            (primeFormFieldSU h isPrimeFormGram_antiIdGL φ g : GL (Fin 6) K) * jPairDiag i s) *
            (A : GL (Fin 6) K)⁻¹ := by group
      _ = _ := by rw [hc']
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_map_of_injective (MulAut.conj _).injective,
    card_map_of_injective (f := α.toMonoidHom) α.injective]

end Block

end CFSG.SeitzReduction.TwistedE6Pilot
