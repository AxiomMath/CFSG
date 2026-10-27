module

public import Certificates.Certificate7052
public import CFSG.Open.StatedAPI

public section

namespace CFSG.Quasithin.H13.L34

open Matrix CFSG.Fischer CFSG.Assembly.LowTwoRank

theorem decode_cadd (x y : Fin 4) : (⟨cadd x y⟩ : F4) = ⟨x⟩ + ⟨y⟩ := by
  fin_cases x <;> fin_cases y <;> rfl

theorem decode_cmul (x y : Fin 4) : (⟨cmul x y⟩ : F4) = ⟨x⟩ * ⟨y⟩ := by
  fin_cases x <;> fin_cases y <;> rfl

namespace M3

theorem mem_xs (x : Fin 4) : x ∈ ([0, 1, 2, 3] : List (Fin 4)) := by
  fin_cases x <;> simp

theorem mem_all (A : M3) : A ∈ all := by
  rcases A with ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩
  simp only [all, List.bind_eq_flatMap, List.pure_def, List.mem_flatMap, List.mem_singleton]
  exact ⟨a00, mem_xs _, a01, mem_xs _, a02, mem_xs _, a10, mem_xs _, a11, mem_xs _, a12,
    mem_xs _, a20, mem_xs _, a21, mem_xs _, a22, mem_xs _, rfl⟩

theorem all_check : all.all check = true :=
  Certificates.certificate7052

end M3

namespace M3

@[expose] def toMat (A : M3) : Matrix (Fin 3) (Fin 3) F4 :=
  !![⟨A.a00⟩, ⟨A.a01⟩, ⟨A.a02⟩; ⟨A.a10⟩, ⟨A.a11⟩, ⟨A.a12⟩; ⟨A.a20⟩, ⟨A.a21⟩, ⟨A.a22⟩]

@[expose] def ofMat (A : Matrix (Fin 3) (Fin 3) F4) : M3 :=
  ⟨(A 0 0).code, (A 0 1).code, (A 0 2).code, (A 1 0).code, (A 1 1).code, (A 1 2).code,
    (A 2 0).code, (A 2 1).code, (A 2 2).code⟩

theorem toMat_ofMat (A : Matrix (Fin 3) (Fin 3) F4) : toMat (ofMat A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem decode_add3 (x y z : Fin 4) : (⟨add3 x y z⟩ : F4) = ⟨x⟩ + ⟨y⟩ + ⟨z⟩ := by
  rw [add3, decode_cadd, decode_cadd]

theorem toMat_mul (A B : M3) : toMat (mul A B) = toMat A * toMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, mul, Matrix.mul_apply, Fin.sum_univ_three, decode_add3, decode_cmul]

theorem det_toMat (A : M3) : (toMat A).det = ⟨det A⟩ := by
  rw [Matrix.det_fin_three]
  simp [toMat, det, decode_cadd, decode_add3, decode_cmul, CharTwo.sub_eq_add]
  ring

theorem isScalar_iff (A : M3) : A.IsScalar ↔ ∃ c : F4, toMat A = Matrix.scalar (Fin 3) c := by
  constructor
  · rintro ⟨h01, h02, h10, h12, h20, h21, h0, h1⟩
    refine ⟨⟨A.a00⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMat, h01, h02, h10, h12, h20, h21, h0, h1] <;> rfl
  · rintro ⟨c, hc⟩
    have e : ∀ i j, toMat A i j = Matrix.scalar (Fin 3) c i j := fun i j => by rw [hc]
    have e00 := e 0 0
    have e01 := e 0 1
    have e02 := e 0 2
    have e10 := e 1 0
    have e11 := e 1 1
    have e12 := e 1 2
    have e20 := e 2 0
    have e21 := e 2 1
    have e22 := e 2 2
    simp [toMat] at e00 e01 e02 e10 e11 e12 e20 e21 e22
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact congrArg F4.code e01
    · exact congrArg F4.code e02
    · exact congrArg F4.code e10
    · exact congrArg F4.code e12
    · exact congrArg F4.code e20
    · exact congrArg F4.code e21
    · exact congrArg F4.code (e00.trans e11.symm)
    · exact congrArg F4.code (e11.trans e22.symm)

end M3

theorem cert_F4 (A : Matrix (Fin 3) (Fin 3) F4) (hdet : A.det = 1)
    (h15 : ∃ c : F4, A ^ 15 = Matrix.scalar (Fin 3) c) :
    (∃ c : F4, A ^ 5 = Matrix.scalar (Fin 3) c) ∨ ∃ c : F4, A ^ 3 = Matrix.scalar (Fin 3) c := by
  set R := M3.ofMat A with hR
  have hRA : M3.toMat R = A := M3.toMat_ofMat A
  have hc : M3.check R = true := List.all_eq_true.mp M3.all_check R (M3.mem_all R)
  have h2 : M3.toMat (M3.mul R R) = A ^ 2 := by rw [M3.toMat_mul, hRA, pow_two]
  have h3 : M3.toMat (M3.mul (M3.mul R R) R) = A ^ 3 := by
    rw [M3.toMat_mul, h2, hRA, ← pow_succ]
  have h5 : M3.toMat (M3.mul (M3.mul (M3.mul R R) R) (M3.mul R R)) = A ^ 5 := by
    rw [M3.toMat_mul, h3, h2, ← pow_add]
  have h15' : M3.toMat (M3.mul (M3.mul (M3.mul (M3.mul (M3.mul R R) R) (M3.mul R R))
      (M3.mul (M3.mul (M3.mul R R) R) (M3.mul R R))) (M3.mul (M3.mul (M3.mul R R) R)
      (M3.mul R R))) = A ^ 15 := by
    rw [M3.toMat_mul, M3.toMat_mul, h5, ← pow_add, ← pow_add]
  have hdetR : M3.det R = 1 := by
    have h := M3.det_toMat R
    rw [hRA, hdet] at h
    exact (congrArg F4.code h).symm
  simp only [M3.check, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · exact absurd hdetR hc
  · exact absurd ((M3.isScalar_iff _).mpr (by rw [h15']; exact h15)) hc
  · left
    rw [← h5]
    exact (M3.isScalar_iff _).mp hc
  · right
    rw [← h3]
    exact (M3.isScalar_iff _).mp hc

section Transport

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem det_eq_one_of_mem_statedSL {n : ℕ} {g : GL (Fin n) K} (hg : g ∈ StatedSL n K) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

omit [Finite K] in
theorem mem_statedScalars_iff {n : ℕ} {g : GL (Fin n) K} :
    g ∈ StatedScalars (Fin n) K ↔
      ∃ c : Kˣ, (g : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) (c : K) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Units.ext hc.symm⟩

theorem nonempty_ringEquiv_F4 (hK : Nat.card K = 4) : Nonempty (K ≃+* F4) := by
  have := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (K := K) (K' := F4)
    (by rw [Fintype.card_eq_nat_card, hK, F4.card])⟩

omit [Finite K] in
theorem pow_mk_eq_one_iff (g : ↥(StatedSL 3 K)) (k : ℕ) :
    (QuotientGroup.mk g : StatedProj (StatedSL 3 K)) ^ k = 1 ↔
      ∃ c : Kˣ, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ k =
        Matrix.scalar (Fin 3) (c : K) := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow, mem_statedScalars_iff, Units.val_pow_eq_pow_val]

theorem no_orderOf_eq_fifteen (hK : Nat.card K = 4)
    (x : StatedProj (StatedSL 3 K)) :
    orderOf x ≠ 15 := by
  intro h15
  obtain ⟨φ⟩ := nonempty_ringEquiv_F4 hK
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  set B : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hB
  have hBdet : B.det = 1 := det_eq_one_of_mem_statedSL g.2
  set A : Matrix (Fin 3) (Fin 3) F4 := B.map φ with hA
  have hAdet : A.det = 1 := by
    have h := RingHom.map_det (φ : K →+* F4) B
    rw [hBdet, map_one] at h
    exact h.symm
  have hmap : ∀ k : ℕ, A ^ k = (B ^ k).map φ := fun k =>
    (map_pow ((φ : K →+* F4).mapMatrix) B k).symm
  have h1 := (pow_mk_eq_one_iff g 15).mp (h15 ▸ pow_orderOf_eq_one _)
  obtain ⟨c, hc⟩ := h1
  have hA15 : ∃ d : F4, A ^ 15 = Matrix.scalar (Fin 3) d :=
    ⟨φ c, by rw [hmap, hc, Matrix.scalar_apply, Matrix.diagonal_map (map_zero φ),
      Matrix.scalar_apply]⟩
  have hback : ∀ k : ℕ, (∃ d : F4, A ^ k = Matrix.scalar (Fin 3) d) →
      (QuotientGroup.mk g : StatedProj (StatedSL 3 K)) ^ k = 1 := by
    rintro k ⟨d, hd⟩
    rw [pow_mk_eq_one_iff]
    have hBk : B ^ k = Matrix.scalar (Fin 3) (φ.symm d) := by
      have h := congrArg (fun M => M.map φ.symm) hd
      rw [hmap] at h
      have e : ((B ^ k).map φ).map φ.symm = B ^ k := by
        ext i j
        simp
      rw [e] at h
      rw [h, Matrix.scalar_apply, Matrix.diagonal_map (map_zero φ.symm), Matrix.scalar_apply]
    have hd0 : φ.symm d ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hBk
      rw [Matrix.det_pow, hBdet, one_pow, h0, map_zero, Matrix.det_zero] at this
      exact one_ne_zero this
    exact ⟨Units.mk0 _ hd0, hBk⟩
  rcases cert_F4 A hAdet hA15 with h5 | h3
  · have := orderOf_dvd_of_pow_eq_one (hback 5 h5)
    rw [h15] at this
    omega
  · have := orderOf_dvd_of_pow_eq_one (hback 3 h3)
    rw [h15] at this
    omega

end Transport

end CFSG.Quasithin.H13.L34
