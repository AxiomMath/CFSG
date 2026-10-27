module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CE
public import CFSG.Quasithin.Vol2.Ch10SecQ34B0

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K]

@[expose] def aMat (ω : K) : Matrix (Fin 3) (Fin 3) K := diagonal ![1, ω, ω ^ 2]

@[expose] def bMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem det_aMat {ω : K} (hω : ω ^ 3 = 1) : (aMat ω).det = 1 := by
  rw [aMat, det_diagonal, Fin.prod_univ_three]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, one_mul]
  rw [← pow_succ', hω]

theorem det_bMat : (bMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [bMat, det_fin_three]
  simp

@[expose] def aSL {ω : K} (hω : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨aMat ω, det_aMat hω⟩

@[expose] def bSL : SpecialLinearGroup (Fin 3) K := ⟨bMat, det_bMat⟩

theorem det_scalar_sq {ω : K} (hω : ω ^ 3 = 1) :
    (ω ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
  rw [det_smul, det_one, mul_one, Fintype.card_fin, ← pow_mul, mul_comm, pow_mul, hω, one_pow]

@[expose] def cSL {ω : K} (hω : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨ω ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K), det_scalar_sq hω⟩

theorem bSL_mul_aSL {ω : K} (hω : ω ^ 3 = 1) : bSL * aSL hω = cSL hω * (aSL hω * bSL) := by
  apply Subtype.ext
  change bMat * aMat ω = ω ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K) * (aMat ω * bMat)
  rw [Matrix.smul_mul, Matrix.one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bMat, aMat, Matrix.mul_apply, diagonal_apply]
  · rw [← pow_succ, hω]
  · rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, hω, one_mul]

theorem aSL_pow_three {ω : K} (hω : ω ^ 3 = 1) : aSL hω ^ 3 = 1 := by
  apply Subtype.ext
  change diagonal ![1, ω, ω ^ 2] ^ 3 = (1 : Matrix (Fin 3) (Fin 3) K)
  rw [diagonal_pow, ← diagonal_one]
  congr 1
  ext k
  fin_cases k
  · simp
  · simp [hω]
  · simp only [Fin.reduceFinMk, Pi.pow_apply, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]

theorem bSL_pow_three : (bSL : SpecialLinearGroup (Fin 3) K) ^ 3 = 1 := by
  apply Subtype.ext
  change (bMat ^ 3 : Matrix (Fin 3) (Fin 3) K) = 1
  rw [pow_succ, sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bMat, Matrix.mul_apply, Fin.sum_univ_three]

noncomputable abbrev aP {ω : K} (hω : ω ^ 3 = 1) : StatedProj (StatedSL 3 K) :=
  projSL3 K (specialLinearGroupEquivStatedSL 3 K (aSL hω))

noncomputable abbrev bP (K : Type) [Field K] : StatedProj (StatedSL 3 K) :=
  projSL3 K (specialLinearGroupEquivStatedSL 3 K bSL)

theorem commute_aP_bP {ω : Kˣ} (hω : (ω : K) ^ 3 = 1) : Commute (aP hω) (bP K) := by
  have hc : projSL3 K (specialLinearGroupEquivStatedSL 3 K (cSL hω)) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    refine ⟨ω ^ 2, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    change Matrix.scalar (Fin 3) ((ω ^ 2 : Kˣ) : K) = (ω : K) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K)
    rw [Units.val_pow_eq_pow_val, Matrix.scalar_apply, smul_one_eq_diagonal]
  have h1 : bP K * aP hω = aP hω * bP K := by
    calc bP K * aP hω = projSL3 K (specialLinearGroupEquivStatedSL 3 K (bSL * aSL hω)) := by
          rw [map_mul, map_mul]
      _ = projSL3 K (specialLinearGroupEquivStatedSL 3 K (cSL hω * (aSL hω * bSL))) := by
          rw [bSL_mul_aSL hω]
      _ = projSL3 K (specialLinearGroupEquivStatedSL 3 K (cSL hω)) * (aP hω * bP K) := by
          rw [map_mul, map_mul, map_mul, map_mul]
      _ = aP hω * bP K := by rw [hc, one_mul]
  exact h1.symm

theorem aP_pow_three {ω : K} (hω : ω ^ 3 = 1) : aP hω ^ 3 = 1 := by
  rw [aP, ← map_pow, ← map_pow, aSL_pow_three, map_one, map_one]

theorem bP_pow_three : bP K ^ 3 = 1 := by
  rw [bP, ← map_pow, ← map_pow, bSL_pow_three, map_one, map_one]

noncomputable def threeHom {ω : Kˣ} (hω : (ω : K) ^ 3 = 1) :
    Multiplicative (ZMod 3) × Multiplicative (ZMod 3) →* StatedProj (StatedSL 3 K) :=
  MonoidHom.noncommCoprod (zpowZMod (aP hω) (aP_pow_three hω)) (zpowZMod (bP K) bP_pow_three)
    (fun _ _ => (commute_aP_bP hω).pow_pow _ _)

theorem bMat_pow_zero_zero {j : ℕ} (hj : j = 1 ∨ j = 2) :
    ((bMat : Matrix (Fin 3) (Fin 3) K) ^ j) 0 0 = 0 := by
  rcases hj with rfl | rfl
  · simp [bMat]
  · simp [bMat, sq, Matrix.mul_apply, Fin.sum_univ_three]

theorem threeHom_injective {ω : Kˣ} (hωo : orderOf ω = 3) (hω : (ω : K) ^ 3 = 1) :
    Function.Injective (threeHom hω) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  set i := (Multiplicative.toAdd x.1).val with hi
  set j := (Multiplicative.toAdd x.2).val with hj
  have hi3 : i < 3 := ZMod.val_lt _
  have hj3 : j < 3 := ZMod.val_lt _
  have hx' : projSL3 K (specialLinearGroupEquivStatedSL 3 K (aSL hω ^ i * bSL ^ j)) = 1 := by
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
    exact hx
  obtain ⟨u, hu⟩ := exists_scalar_of_proj_eq_one hx'
  have hmat : ((aSL hω ^ i * bSL ^ j : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (![1, (ω : K), (ω : K) ^ 2] ^ i) * bMat ^ j := by
    change aMat (ω : K) ^ i * bMat ^ j = _
    rw [aMat, diagonal_pow]
  have hu' : diagonal (![1, (ω : K), (ω : K) ^ 2] ^ i) * bMat ^ j =
      Matrix.scalar (Fin 3) (u : K) := by rw [← hmat]; exact hu
  have e00 := congrFun (congrFun hu' 0) 0
  have e11 := congrFun (congrFun hu' 1) 1
  rw [diagonal_mul] at e00 e11
  simp only [Pi.pow_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow,
    one_mul, Matrix.scalar_apply, diagonal_apply_eq] at e00 e11
  have hj0 : j = 0 := by
    by_contra hj0
    have : j = 1 ∨ j = 2 := by omega
    rw [bMat_pow_zero_zero this] at e00
    exact u.ne_zero e00.symm
  rw [hj0, pow_zero] at e00 e11
  simp only [Matrix.one_apply_eq, mul_one] at e00 e11
  have hu1 : (u : K) = 1 := e00.symm
  have hωi : ω ^ i = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, e11, hu1, Units.val_one])
  have hi0 : i = 0 := by
    have h3 := orderOf_dvd_of_pow_eq_one hωi
    rw [hωo] at h3
    omega
  refine Prod.ext ?_ ?_
  · exact Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).mp hi0)
  · exact Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).mp hj0)

end C11AmS

open C11AmS CFSG.Assembly.LowTwoRank

theorem factRankSL3_holds : FactRankSL3 := by
  intro G _ _ L n p hn hp hp2 hpq hL
  have : NeZero p := ⟨hp.ne_zero⟩
  rcases hL with ⟨-, K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩
  · obtain ⟨ζ, hζ⟩ := exists_unit_orderOf hp (by rw [hK]; exact hpq)
    have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
    by_cases hp3 : p = 3
    · subst hp3
      have hω : (ζ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζp, Units.val_one]
      exact exists_elemAbelian_of_injective (e.symm.toMonoidHom.comp (threeHom hω))
        (e.symm.injective.comp (threeHom_injective hζ hω))
    · exact exists_elemAbelian_of_injective
        (e.symm.toMonoidHom.comp ((projSL3 K).comp (diagZMod ζ hζp)))
        (e.symm.injective.comp (diagZModProj_injective hp hp3 hζ hζp))
  · obtain ⟨ζ, hζ⟩ := exists_unit_orderOf hp (by rw [hK]; exact hpq)
    have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
    exact exists_elemAbelian_of_injective (e.symm.toMonoidHom.comp (diagZMod ζ hζp))
      (e.symm.injective.comp (diagZMod_injective hζ hζp))

end CFSG.Quasithin.Vol2.Ch10.SecB
