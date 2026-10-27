module

public import CFSG.RankThree.PartOne.KC.UnitaryTransvectionPointwise
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningIsotropic

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

namespace KCUnitaryTrv

variable {p f : ℕ} {K : Type} [Field K] {m : ℕ} (h : UnitaryFieldData p f K)

local notation "e₀" => (Pi.single (0 : Fin (m + 2)) (1 : K) : Fin (m + 2) → K)
local notation "eₗ" => (Pi.single (Fin.last (m + 1)) (1 : K) : Fin (m + 2) → K)

@[expose] def trvW (K : Type) [Field K] (m : ℕ) : Submodule K (Fin (m + 2) → K) :=
  Submodule.span K {(Pi.single (0 : Fin (m + 2)) (1 : K) : Fin (m + 2) → K)}

theorem trvGram_barTranspose : ((trvGram K m).map h.bar)ᵀ = trvGram K m :=
  isPrimeFormGram_trv.barTranspose h

theorem gramForm_trv_symm : (gramForm h (trvGram K m)).IsSymm :=
  gramForm_isSymm h (trvGram_barTranspose h)

theorem gramForm_trv_e0_e0 : gramForm h (trvGram K m) e₀ e₀ = 0 := by
  rw [gramForm_trv_single_left, trvPerm_zero]
  simp [zero_ne_last.symm]

theorem gramForm_trv_e0_left (y : Fin (m + 2) → K) :
    gramForm h (trvGram K m) e₀ y = y (Fin.last (m + 1)) := by
  rw [gramForm_trv_single_left, trvPerm_zero]

theorem mem_trvW {w : Fin (m + 2) → K} : w ∈ trvW K m ↔ ∃ t : K, w = t • e₀ := by
  rw [trvW, Submodule.mem_span_singleton]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩

theorem trvW_iso : ∀ v ∈ trvW K m, ∀ w ∈ trvW K m, gramForm h (trvGram K m) v w = 0 := by
  intro v hv w hw
  obtain ⟨s, rfl⟩ := mem_trvW.mp hv
  obtain ⟨t, rfl⟩ := mem_trvW.mp hw
  rw [gramForm_trv_smul_single_left, trvPerm_zero]
  simp [zero_ne_last.symm]

theorem mem_orthogonalBilin_trvW {y : Fin (m + 2) → K} :
    y ∈ (trvW K m).orthogonalBilin (gramForm h (trvGram K m)) ↔ y (Fin.last (m + 1)) = 0 := by
  rw [Submodule.mem_orthogonalBilin]
  constructor
  · intro hy
    have := hy e₀ (mem_trvW.mpr ⟨1, by rw [one_smul]⟩)
    rwa [gramForm_trv_e0_left h] at this
  · intro hy w hw
    obtain ⟨t, rfl⟩ := mem_trvW.mp hw
    rw [map_smulₛₗ, LinearMap.smul_apply, gramForm_trv_e0_left, hy, smul_zero]

theorem matrix_eq_of_mulVec_eq {n : ℕ} {M M' : Matrix (Fin n) (Fin n) K}
    (hM : ∀ x, M *ᵥ x = M' *ᵥ x) : M = M' := by
  ext i j
  have := congrFun (hM (Pi.single j 1)) i
  simpa [mulVec_single_one, col_apply] using this

theorem hww_trv : gramForm h (trvGram K m) e₀ e₀ = 0 := gramForm_trv_e0_e0 h

theorem hwy_trv {y : Fin (m + 2) → K} (hy : y (Fin.last (m + 1)) = 0) :
    gramForm h (trvGram K m) e₀ y = 0 := by
  rw [gramForm_trv_e0_left, hy]

@[expose] noncomputable def trvEich (y : Fin (m + 2) → K) (hy : y (Fin.last (m + 1)) = 0) (c : K)
    (hc : c + h.bar c = -gramForm h (trvGram K m) y y) : gramSU h (trvGram K m) :=
  ⟨unipotentGL (eichlerMatrix h (trvGram K m) e₀ y c)
    (eichlerMatrix_sub_one_pow_three (gramForm_trv_symm h) (hww_trv h) (hwy_trv h hy) c),
    eichlerGL_mem (gramForm_trv_symm h) (hww_trv h) (hwy_trv h hy) hc⟩

theorem coe_trvEich (y : Fin (m + 2) → K) (hy : y (Fin.last (m + 1)) = 0) (c : K)
    (hc : c + h.bar c = -gramForm h (trvGram K m) y y) :
    (((trvEich h y hy c hc : gramSU h (trvGram K m)) : GL (Fin (m + 2)) K) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) K) = eichlerMatrix h (trvGram K m) e₀ y c := rfl

theorem trvEich_mem_radical (y : Fin (m + 2) → K) (hy : y (Fin.last (m + 1)) = 0) (c : K)
    (hc : c + h.bar c = -gramForm h (trvGram K m) y y) :
    trvEich h y hy c hc ∈ isotropicRadical h (trvGram K m) (trvW K m) :=
  eichler_mem_radical (gramForm_trv_symm h) (trvW_iso h) (mem_trvW.mpr ⟨1, by rw [one_smul]⟩)
    ((mem_orthogonalBilin_trvW h).mpr hy) hc

theorem eichlerMatrix_trv_zero (c : K) :
    eichlerMatrix h (trvGram K m) e₀ 0 c =
      1 + c • Matrix.single 0 (Fin.last (m + 1)) (1 : K) := by
  ext i j
  have h1 := congrFun (eich_apply h 0 c (Pi.single j 1)) i
  rw [mulVec_single_one, col_apply] at h1
  rw [h1]
  by_cases hi : i = 0 <;> by_cases hj : j = Fin.last (m + 1) <;>
    simp [Matrix.one_apply, Pi.single_apply, hi, hj, eq_comm]

@[expose] noncomputable def trvR (m : ℕ) : Subgroup (gramSU h (trvGram K m)) :=
  isotropicRadical h (trvGram K m) (trvW K m)

@[expose] def trvN (K : Type) [Field K] (m : ℕ) (η : K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K :=
  η • Matrix.single 0 (Fin.last (m + 1)) (1 : K)

theorem trvN_mulVec (η : K) (x : Fin (m + 2) → K) :
    trvN K m η *ᵥ x = (η * x (Fin.last (m + 1))) • e₀ := by
  rw [trvN, smul_mulVec, single_mulVec_eq, one_mul, smul_smul]

end KCUnitaryTrv

@[expose] noncomputable def trvElt {p f : ℕ} {K : Type} [Field K] (m : ℕ)
    (h : UnitaryFieldData p f K) (η : K) (hη : h.bar η = -η) : gramSU h (trvGram K m) :=
  KCUnitaryTrv.trvEich h 0 (by simp) η (by
    have h0 : gramForm h (trvGram K m) 0 0 = 0 := by simp
    rw [h0, neg_zero, hη, add_neg_cancel])

theorem coe_trvElt {p f : ℕ} {K : Type} [Field K] (m : ℕ) (h : UnitaryFieldData p f K) (η : K)
    (hη : h.bar η = -η) :
    (((trvElt m h η hη : gramSU h (trvGram K m)) : GL (Fin (m + 2)) K) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
        1 + η • Matrix.single 0 (Fin.last (m + 1)) (1 : K) :=
  KCUnitaryTrv.eichlerMatrix_trv_zero h η

namespace KCUnitaryTrv

variable {p f : ℕ} {K : Type} [Field K] {m : ℕ} (h : UnitaryFieldData p f K)

local notation "e₀" => (Pi.single (0 : Fin (m + 2)) (1 : K) : Fin (m + 2) → K)
local notation "eₗ" => (Pi.single (Fin.last (m + 1)) (1 : K) : Fin (m + 2) → K)

theorem trvElt_mem_trvR (η : K) (hη : h.bar η = -η) : trvElt m h η hη ∈ trvR h m :=
  trvEich_mem_radical h 0 _ η _

theorem trvR_fix_e0 {r : gramSU h (trvGram K m)} (hr : r ∈ trvR h m) :
    ((r : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ e₀ = e₀ :=
  (mem_isotropicRadical.mp hr).1 e₀ (mem_trvW.mpr ⟨1, by rw [one_smul]⟩)

theorem trvR_comm_trvN {r : gramSU h (trvGram K m)} (hr : r ∈ trvR h m) (η : K) :
    ((r : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * trvN K m η =
      trvN K m η * ((r : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) := by
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [← mulVec_mulVec, ← mulVec_mulVec, trvN_mulVec, trvN_mulVec, mulVec_smul, trvR_fix_e0 h hr]
  have h1 := KCUnitaryDefining.gramForm_mulVec_of_mem_gramSU h r.2 e₀ x
  rw [trvR_fix_e0 h hr, gramForm_trv_e0_left, gramForm_trv_e0_left] at h1
  rw [h1]

theorem trvR_comm_trvElt {η : K} (hη : h.bar η = -η) {r : gramSU h (trvGram K m)}
    (hr : r ∈ trvR h m) : r * trvElt m h η hη = trvElt m h η hη * r := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_trvElt]
  rw [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
  have := trvR_comm_trvN h hr η
  rw [trvN, mul_smul_comm, smul_mul_assoc] at this
  rw [this]

theorem trvR_conj_mem {η : K} (hη0 : η ≠ 0) {g : gramSU h (trvGram K m)}
    (hg : ((g : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * trvN K m η =
      trvN K m η * ((g : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K))
    {r : gramSU h (trvGram K m)} (hr : r ∈ trvR h m) : g * r * g⁻¹ ∈ trvR h m := by
  set gm : Matrix (Fin (m + 2)) (Fin (m + 2)) K :=
    ((g : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) with hgm
  set gi : Matrix (Fin (m + 2)) (Fin (m + 2)) K :=
    (((g⁻¹ : gramSU h (trvGram K m)) : GL (Fin (m + 2)) K) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) K) with hgi
  have hgi' : ((g⁻¹ : gramSU h (trvGram K m)) : GL (Fin (m + 2)) K) =
      (g : GL (Fin (m + 2)) K)⁻¹ := rfl
  have hgg' : gi * gm = 1 := by rw [hgm, hgi, hgi', Units.inv_mul]
  have h1 : gm *ᵥ (trvN K m η *ᵥ eₗ) = trvN K m η *ᵥ (gm *ᵥ eₗ) := by
    rw [mulVec_mulVec, mulVec_mulVec, hg]
  rw [trvN_mulVec, trvN_mulVec, mulVec_smul] at h1
  have hel : eₗ (Fin.last (m + 1)) = 1 := by simp
  rw [hel, mul_one] at h1
  have h2 : gm *ᵥ e₀ = (gm *ᵥ eₗ) (Fin.last (m + 1)) • e₀ := by
    refine smul_right_injective _ hη0 ?_
    show η • (gm *ᵥ e₀) = η • ((gm *ᵥ eₗ) (Fin.last (m + 1)) • e₀)
    rw [h1, smul_smul]
  set μ : K := (gm *ᵥ eₗ) (Fin.last (m + 1)) with hμ
  have h3 : e₀ = gi *ᵥ (gm *ᵥ e₀) := by rw [mulVec_mulVec, hgg', one_mulVec]
  have hμ0 : μ ≠ 0 := by
    intro e
    rw [e, zero_smul] at h2
    rw [h2, mulVec_zero] at h3
    have := congrFun h3 0
    simp at this
  have h4 : gi *ᵥ e₀ = μ⁻¹ • e₀ := by
    have h5 : e₀ = μ • (gi *ᵥ e₀) :=
      calc e₀ = gi *ᵥ (gm *ᵥ e₀) := h3
        _ = gi *ᵥ (μ • e₀) := by rw [h2]
        _ = μ • (gi *ᵥ e₀) := mulVec_smul _ _ _
    calc gi *ᵥ e₀ = μ⁻¹ • (μ • (gi *ᵥ e₀)) := by rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = μ⁻¹ • e₀ := by rw [← h5]
  have hgW : ∀ w ∈ trvW K m, gm *ᵥ w ∈ trvW K m := by
    intro w hw
    obtain ⟨t, rfl⟩ := mem_trvW.mp hw
    exact mem_trvW.mpr ⟨t * μ, by rw [mulVec_smul, h2, smul_smul]⟩
  have hgW' : ∀ w ∈ trvW K m, gi *ᵥ w ∈ trvW K m := by
    intro w hw
    obtain ⟨t, rfl⟩ := mem_trvW.mp hw
    exact mem_trvW.mpr ⟨t * μ⁻¹, by rw [mulVec_smul, h4, smul_smul]⟩
  exact KCUnitaryDefining.conj_mem_isotropicRadical h hgW hgW' hr

theorem trvR_pointwise (hm : 1 ≤ m) (A : primeFormUnitary h (trvGram K m)) (σ : K ≃+* K)
    (hexact : ∀ r ∈ trvR h m, (A : GL (Fin (m + 2)) K) * glAut σ (r : GL (Fin (m + 2)) K) *
      (A : GL (Fin (m + 2)) K)⁻¹ = r) :
    ∃ r' ∈ trvR h m, primeFormConjHom h (trvGram K m) A *
      primeFormFieldHom h (isPrimeFormGram_trv (K := K) (m := m)) σ =
        MulAut.conj (r' : primeFormP h (trvGram K m)) := by
  have hΦ : ∀ (y : Fin (m + 2) → K) (c : K), y (Fin.last (m + 1)) = 0 →
      c + h.bar c = -gramForm h (trvGram K m) y y → ∀ x : Fin (m + 2) → K,
      semilin ((A : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) σ
          (eichlerMatrix h (trvGram K m) (Pi.single 0 1) y c *ᵥ x) =
        eichlerMatrix h (trvGram K m) (Pi.single 0 1) y c *ᵥ
          semilin ((A : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) σ x := by
    intro y c hy hc x
    apply semilin_mulVec _ x
    have h1 := congrArg (fun g : GL (Fin (m + 2)) K => (g : Matrix (Fin (m + 2)) (Fin (m + 2)) K))
      (hexact _ (trvEich_mem_radical h y hy c hc))
    simp only [Units.val_mul, coe_glAut, coe_trvEich] at h1
    have hAi : (↑((A : GL (Fin (m + 2)) K)⁻¹) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *
        ((A : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((A : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *
          (eichlerMatrix h (trvGram K m) (Pi.single 0 1) y c).map σ =
        ((A : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *
          (eichlerMatrix h (trvGram K m) (Pi.single 0 1) y c).map σ *
            (↑((A : GL (Fin (m + 2)) K)⁻¹) * ((A : GL (Fin (m + 2)) K) :
              Matrix (Fin (m + 2)) (Fin (m + 2)) K)) := by rw [hAi, mul_one]
      _ = (((A : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *
          (eichlerMatrix h (trvGram K m) (Pi.single 0 1) y c).map σ *
            ↑((A : GL (Fin (m + 2)) K)⁻¹)) * ((A : GL (Fin (m + 2)) K) :
              Matrix (Fin (m + 2)) (Fin (m + 2)) K) := (Matrix.mul_assoc _ _ _).symm
      _ = _ := by rw [h1]
  obtain ⟨hσ, z, d, hz0, hzn, hd, hAeq⟩ := trv_pointwise h hm (A : GL (Fin (m + 2)) K) A.2 σ hΦ
  have hdb : h.bar d = -d := eq_neg_of_add_eq_zero_right hd
  refine ⟨trvElt m h d hdb, trvElt_mem_trvR h d hdb, ?_⟩
  refine KCUnitaryDefining.primeFormConjHom_mul_fieldHom_eq_conj h isPrimeFormGram_trv
    (z := Units.mk0 z hz0) ?_ hσ
  apply Units.ext
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0, coe_trvElt, hAeq,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

end KCUnitaryTrv

theorem unitary_transvection_centralizer_normal_prime_complements_trivial {p f m : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData p f K) (hp3 : 3 < p) (hm : 1 ≤ m) {η : K}
    (hη : h.bar η = -η) (hη0 : η ≠ 0)
    (B : Subgroup (MulAut (primeFormP h (trvGram K m))))
    (hB : (MulAut.conj : primeFormP h (trvGram K m) →* MulAut (primeFormP h (trvGram K m))).range
      ≤ B)
    (S : Subgroup (MulAut (primeFormP h (trvGram K m))))
    (hSC : S ≤ B ⊓ Subgroup.centralizer
      {MulAut.conj (trvElt m h η hη : primeFormP h (trvGram K m))})
    (hSn : (S.subgroupOf (B ⊓ Subgroup.centralizer
      {MulAut.conj (trvElt m h η hη : primeFormP h (trvGram K m))})).Normal)
    (hSp : ¬ p ∣ Nat.card S) : S = ⊥ := by
  have hn : 1 ≤ m + 2 := by omega
  have hR := KCUnitaryTrv.trvElt_mem_trvR (m := m) h η hη
  refine KCUnitaryDefining.normalPrimeComplementsTrivial_of_radical_data h hp3 (by omega)
    (KCUnitaryTrv.isPrimeFormGram_trv (K := K) (m := m)) (trvElt m h η hη)
    (KCUnitaryDefining.pow_eq_one_of_mem_isotropicRadical h hp3.le hn hR)
    (KCUnitaryTrv.trvN K m η) ?_ (KCUnitaryTrv.trvR h m)
    (fun r hr => KCUnitaryTrv.trvR_comm_trvElt h hη hr)
    (fun r hr => KCUnitaryDefining.pow_eq_one_of_mem_isotropicRadical h hp3.le hn hr)
    (fun g hg r hr => KCUnitaryTrv.trvR_conj_mem h hη0 hg hr)
    (fun A σ hex => KCUnitaryTrv.trvR_pointwise h hm A σ hex) B hB S hSC hSn hSp
  intro g hg
  have h1 := congrArg (fun z : gramSU h (trvGram K m) => ((z : GL (Fin (m + 2)) K) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) K)) hg
  simp only [Subgroup.coe_mul, Units.val_mul] at h1
  rw [coe_trvElt, mul_add, add_mul, mul_one, one_mul] at h1
  exact add_left_cancel h1

end CFSG.RankThree.PartOne
