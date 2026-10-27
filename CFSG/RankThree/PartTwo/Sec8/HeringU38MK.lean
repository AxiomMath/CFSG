module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.RankThree.PartTwo.Sec8.HeringU38MF4

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

open CFSG CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.KGroups Matrix

theorem Mat3.mul_eq (A B : Mat3) : A * B = Mat3.mul A B := rfl

theorem Mat3.one_eq : (1 : Mat3) = Mat3.one := rfl

@[expose] def Mat3.toMat {R : Type*} [Semiring R] (ι : F →+* R) (A : Mat3) :
    Matrix (Fin 3) (Fin 3) R :=
  !![ι A.a00, ι A.a01, ι A.a02; ι A.a10, ι A.a11, ι A.a12; ι A.a20, ι A.a21, ι A.a22]

section ToMat

variable {R : Type*} [CommRing R] (ι : F →+* R)

theorem toMat_mul (A B : Mat3) : (A * B).toMat ι = A.toMat ι * B.toMat ι := by
  rw [Mat3.mul_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mat3.toMat, Mat3.mul, Matrix.mul_apply, Fin.sum_univ_three, map_add, map_mul]

theorem toMat_one : (1 : Mat3).toMat ι = 1 := by
  rw [Mat3.one_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mat3.toMat, Mat3.one]

theorem toMat_det (A : Mat3) : (A.toMat ι).det = ι A.det := by
  rw [Matrix.det_fin_three]
  simp only [Mat3.toMat, Mat3.det, map_add, map_mul, map_sub]
  simp
  ring

theorem toMat_smul (c : F) (A : Mat3) : (Mat3.smul c A).toMat ι = ι c • A.toMat ι := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mat3.toMat, Mat3.smul, map_mul]

theorem toMat_diag (a b c : F) :
    (Mat3.diag a b c).toMat ι = diagonal ![ι a, ι b, ι c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mat3.toMat, Mat3.diag, diagonal_apply]

theorem Mat3.pow_succ' (A : Mat3) (n : ℕ) : A ^ (n + 1) = A ^ n * A := rfl

theorem Mat3.pow_zero' (A : Mat3) : A ^ 0 = 1 := rfl

theorem toMat_pow (A : Mat3) (n : ℕ) : (A ^ n).toMat ι = (A.toMat ι) ^ n := by
  induction n with
  | zero => rw [Mat3.pow_zero', toMat_one, pow_zero]
  | succ n ih => rw [Mat3.pow_succ', toMat_mul, ih, pow_succ]

theorem toMat_injective (hι : Function.Injective ι) : Function.Injective (Mat3.toMat ι) := by
  intro A B hAB
  have h00 : A.a00 = B.a00 := hι (congrFun (congrFun hAB 0) 0)
  have h01 : A.a01 = B.a01 := hι (congrFun (congrFun hAB 0) 1)
  have h02 : A.a02 = B.a02 := hι (congrFun (congrFun hAB 0) 2)
  have h10 : A.a10 = B.a10 := hι (congrFun (congrFun hAB 1) 0)
  have h11 : A.a11 = B.a11 := hι (congrFun (congrFun hAB 1) 1)
  have h12 : A.a12 = B.a12 := hι (congrFun (congrFun hAB 1) 2)
  have h20 : A.a20 = B.a20 := hι (congrFun (congrFun hAB 2) 0)
  have h21 : A.a21 = B.a21 := hι (congrFun (congrFun hAB 2) 1)
  have h22 : A.a22 = B.a22 := hι (congrFun (congrFun hAB 2) 2)
  cases A; cases B
  simp_all

end ToMat

section Bar

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) (ι : F →+* K)

theorem gf4_pow_eight (a : F) : a ^ 8 = cj a := by
  have h4 : ∀ x : F, x * x * x * x = x := by decide +kernel
  calc a ^ 8 = (a * a * a * a) * (a * a * a * a) := by ring
    _ = cj a := by rw [h4]; rfl

theorem bar_ι (a : F) : h.bar (ι a) = ι (cj a) := by
  rw [h.bar_apply, show (2 : ℕ) ^ 3 = 8 by norm_num, ← map_pow, gf4_pow_eight]

theorem toMat_cjT (A : Mat3) : ((A.toMat ι).map h.bar)ᵀ = A.cjT.toMat ι := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mat3.toMat, Mat3.cjT, bar_ι h ι]

theorem isU_toMat {A : Mat3} (hA : IsU A) : ((A.toMat ι).map h.bar)ᵀ * A.toMat ι = 1 := by
  rw [toMat_cjT h ι, ← toMat_mul, hA, toMat_one]

theorem det_toMat {A : Mat3} (hA : A.det = 1) : (A.toMat ι).det = 1 := by
  rw [toMat_det, hA, map_one]

end Bar

section Elements

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) (ι : F →+* K)

@[expose] def mat (g : unitarySU 2 3 K 3) : Matrix (Fin 3) (Fin 3) K :=
  ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem mat_mul (g g' : unitarySU 2 3 K 3) : mat (g * g') = mat g * mat g' := rfl

theorem mat_one : mat (1 : unitarySU 2 3 K 3) = 1 := rfl

theorem mat_inv (g : unitarySU 2 3 K 3) : mat (g⁻¹) = ((mat g).map h.bar)ᵀ := by
  have hg := ((mem_unitarySU_iff h).mp g.2).2
  exact Units.inv_eq_of_mul_eq_one_left hg

theorem mat_pow (g : unitarySU 2 3 K 3) (n : ℕ) : mat (g ^ n) = (mat g) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

theorem mat_injective : Function.Injective (mat (K := K)) := by
  intro g g' hgg
  exact Subtype.ext (Units.ext hgg)

@[expose] noncomputable def toSU (A : Mat3) (hA : IsU A ∧ A.det = 1) : unitarySU 2 3 K 3 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (A.toMat ι) (by rw [det_toMat ι hA.2]; exact one_ne_zero),
    (mem_unitarySU_iff h).mpr ⟨det_toMat ι hA.2, isU_toMat h ι hA.1⟩⟩

theorem mat_toSU (A : Mat3) (hA : IsU A ∧ A.det = 1) : mat (toSU h ι A hA) = A.toMat ι := rfl

@[expose] noncomputable def subgroupOfList (L : List Mat3) (h1 : (1 : Mat3) ∈ L)
    (_hu : ∀ A ∈ L, IsU A ∧ A.det = 1) (hm : ∀ A ∈ L, ∀ B ∈ L, A * B ∈ L)
    (hc : ∀ A ∈ L, A.cjT ∈ L) : Subgroup (unitarySU 2 3 K 3) where
  carrier := {g | ∃ A ∈ L, mat g = A.toMat ι}
  mul_mem' := by
    rintro g g' ⟨A, hA, hg⟩ ⟨B, hB, hg'⟩
    exact ⟨A * B, hm A hA B hB, by rw [mat_mul, hg, hg', toMat_mul]⟩
  one_mem' := ⟨1, h1, by rw [mat_one, toMat_one]⟩
  inv_mem' := by
    rintro g ⟨A, hA, hg⟩
    exact ⟨A.cjT, hc A hA, by rw [mat_inv h, hg, toMat_cjT h ι]⟩

theorem toSU_mem {L : List Mat3} {h1 : (1 : Mat3) ∈ L}
    {hu : ∀ A ∈ L, IsU A ∧ A.det = 1} {hm : ∀ A ∈ L, ∀ B ∈ L, A * B ∈ L}
    {hc : ∀ A ∈ L, A.cjT ∈ L} {A : Mat3} (hA : A ∈ L) :
    toSU h ι A (hu A hA) ∈ subgroupOfList h ι L h1 hu hm hc := ⟨A, hA, rfl⟩

theorem card_subgroupOfList (hι : Function.Injective ι) {L : List Mat3} {h1 : (1 : Mat3) ∈ L}
    {hu : ∀ A ∈ L, IsU A ∧ A.det = 1} {hm : ∀ A ∈ L, ∀ B ∈ L, A * B ∈ L}
    {hc : ∀ A ∈ L, A.cjT ∈ L} (hnd : L.Nodup) :
    Nat.card (subgroupOfList h ι L h1 hu hm hc) = L.length := by
  classical
  let f : {A : Mat3 // A ∈ L} → subgroupOfList h ι L h1 hu hm hc :=
    fun A => ⟨toSU h ι A.1 (hu A.1 A.2), toSU_mem h ι A.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro A B hAB
      have h1 : mat (toSU h ι A.1 (hu A.1 A.2)) = mat (toSU h ι B.1 (hu B.1 B.2)) :=
        congrArg (fun g : subgroupOfList h ι L h1 hu hm hc => mat (g : unitarySU 2 3 K 3)) hAB
      exact Subtype.ext (toMat_injective ι hι h1)
    · rintro ⟨g, A, hA, hg⟩
      refine ⟨⟨A, hA⟩, Subtype.ext (mat_injective ?_)⟩
      exact hg.symm
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  have : Nat.card {A : Mat3 // A ∈ L} = L.toFinset.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun A => (List.mem_toFinset).symm)
  rw [this, List.toFinset_card_of_nodup hnd]

end Elements

end CFSG.RankThree.PartTwo.Sec8.HeringU38M
