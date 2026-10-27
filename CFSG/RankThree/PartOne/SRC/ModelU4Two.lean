module

public import CFSG.RankThree.PartOne.SRC.ModelU4
public import CFSG.RankThree.PartOne.SRC.ModelL4Two
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

section Pair4

variable {K : Type} [Field K]

theorem diagMat4_transpose (A B : Matrix (Fin 2) (Fin 2) K) :
    (diagMat4 A B)ᵀ = diagMat4 Aᵀ Bᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagMat4]

theorem diagMat4_map (f : K → K) (hf : f 0 = 0) (A B : Matrix (Fin 2) (Fin 2) K) :
    (diagMat4 A B).map f = diagMat4 (A.map f) (B.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagMat4, hf]

@[expose] noncomputable def blockPairGL4 : GL (Fin 2) K × GL (Fin 2) K →* GL (Fin 4) K where
  toFun x := ⟨diagMat4 (x.1 : Matrix (Fin 2) (Fin 2) K) (x.2 : Matrix (Fin 2) (Fin 2) K),
    diagMat4 ((x.1⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ((x.2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
    rw [← diagMat4_mul, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, mul_inv_cancel,
      Units.val_one, diagMat4_one], by
    rw [← diagMat4_mul, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, inv_mul_cancel,
      Units.val_one, diagMat4_one]⟩
  map_one' := Units.ext (by simp [diagMat4_one])
  map_mul' x y := Units.ext (by simp [diagMat4_mul])

theorem coe_blockPairGL4 (x : GL (Fin 2) K × GL (Fin 2) K) :
    ((blockPairGL4 x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagMat4 (x.1 : Matrix (Fin 2) (Fin 2) K) (x.2 : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem blockPairGL4_mem_statedSU {q : ℕ} (hq : 1 ≤ q) {A B : GL (Fin 2) K}
    (hA : A ∈ StatedSU 2 q K) (hB : B ∈ StatedSU 2 q K) :
    blockPairGL4 (A, B) ∈ StatedSU 4 q K := by
  have hq0 : (0 : K) ^ q = 0 := zero_pow (by omega)
  have key : ∀ (g : GL (Fin 2) K), g ∈ StatedSU 2 q K →
      blockPairGL4 (g, 1) ∈ StatedSU 4 q K ∧ blockPairGL4 (1, g) ∈ StatedSU 4 q K := by
    intro g hg
    rw [StatedSU] at hg
    have hone : ((1 : Matrix (Fin 2) (Fin 2) K).map (· ^ q)) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hq0]
    induction hg using Subgroup.closure_induction with
    | mem g hg' =>
      obtain ⟨hdet, hu⟩ := hg'
      refine ⟨Subgroup.subset_closure ⟨?_, ?_⟩, Subgroup.subset_closure ⟨?_, ?_⟩⟩
      · rw [coe_blockPairGL4, det_diagMat4, hdet]
        simp
      · change ((diagMat4 (g : Matrix (Fin 2) (Fin 2) K) ((1 : GL (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K)).map (fun x => x ^ q))ᵀ *
          diagMat4 (g : Matrix (Fin 2) (Fin 2) K) ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
            = 1
        rw [Units.val_one, diagMat4_map (fun x => x ^ q) hq0, diagMat4_transpose,
          ← diagMat4_mul, hu, hone, Matrix.transpose_one, mul_one, diagMat4_one]
      · rw [coe_blockPairGL4, det_diagMat4, hdet]
        simp
      · change ((diagMat4 ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
            (g : Matrix (Fin 2) (Fin 2) K)).map (fun x => x ^ q))ᵀ *
          diagMat4 ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (g : Matrix (Fin 2) (Fin 2) K)
            = 1
        rw [Units.val_one, diagMat4_map (fun x => x ^ q) hq0, diagMat4_transpose,
          ← diagMat4_mul, hu, hone, Matrix.transpose_one, mul_one, diagMat4_one]
    | one =>
      refine ⟨?_, ?_⟩ <;>
        · rw [Prod.mk_one_one, map_one]
          exact one_mem _
    | mul a b _ _ iha ihb =>
      refine ⟨?_, ?_⟩
      · rw [show ((a * b, (1 : GL (Fin 2) K)) : GL (Fin 2) K × GL (Fin 2) K) = (a, 1) * (b, 1) by
          rw [Prod.mk_mul_mk, mul_one], map_mul]
        exact mul_mem iha.1 ihb.1
      · rw [show (((1 : GL (Fin 2) K), a * b) : GL (Fin 2) K × GL (Fin 2) K) = (1, a) * (1, b) by
          rw [Prod.mk_mul_mk, mul_one], map_mul]
        exact mul_mem iha.2 ihb.2
    | inv a _ iha =>
      refine ⟨?_, ?_⟩
      · rw [show ((a⁻¹, (1 : GL (Fin 2) K)) : GL (Fin 2) K × GL (Fin 2) K) = (a, 1)⁻¹ by
          ext <;> simp, map_inv]
        exact inv_mem iha.1
      · rw [show (((1 : GL (Fin 2) K), a⁻¹) : GL (Fin 2) K × GL (Fin 2) K) = (1, a)⁻¹ by
          ext <;> simp, map_inv]
        exact inv_mem iha.2
  have hAB : blockPairGL4 (A, B) = blockPairGL4 (A, 1) * blockPairGL4 (1, B) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [hAB]
  exact mul_mem (key A hA).1 (key B hB).2

@[expose] noncomputable def blockPairSU4 {q : ℕ} (hq : 1 ≤ q) :
    StatedSU 2 q K × StatedSU 2 q K →* StatedSU 4 q K :=
  (blockPairGL4.comp ((StatedSU 2 q K).subtype.prodMap (StatedSU 2 q K).subtype)).codRestrict
    (StatedSU 4 q K) fun x => blockPairGL4_mem_statedSU hq x.1.2 x.2.2

theorem coe_blockPairSU4 {q : ℕ} (hq : 1 ≤ q) (x : StatedSU 2 q K × StatedSU 2 q K) :
    ((blockPairSU4 hq x : StatedSU 4 q K) : GL (Fin 4) K) =
      blockPairGL4 ((x.1 : GL (Fin 2) K), (x.2 : GL (Fin 2) K)) :=
  rfl

theorem blockPairGL4_commute_negDiag4 (x : GL (Fin 2) K × GL (Fin 2) K) :
    blockPairGL4 x * negDiag4 K = negDiag4 K * blockPairGL4 x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blockPairGL4, coe_negDiag4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagMat4, Matrix.mul_apply, diagonal]

theorem blockPairSU4_commute {q : ℕ} (hq : 1 ≤ q) (hodd : Odd q)
    (x : StatedSU 2 q K × StatedSU 2 q K) :
    blockPairSU4 hq x * negDiagSU4 hodd = negDiagSU4 hodd * blockPairSU4 hq x :=
  Subtype.ext (blockPairGL4_commute_negDiag4 _)

theorem sq_eq_one_of_blockPairSU4_mem_scalars {q : ℕ} (hq : 1 ≤ q)
    {x : StatedSU 2 q K × StatedSU 2 q K}
    (h : (blockPairSU4 hq x : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K) : x ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := h
  have hm := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hc
  have e := fun i j => congrFun (congrFun hm i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  have e22 := e 2 2
  have e23 := e 2 3
  have e32 := e 3 2
  have e33 := e 3 3
  simp [coe_blockPairSU4, coe_blockPairGL4, diagMat4, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply] at e00 e01 e10 e11 e22 e23 e32 e33
  have d1 := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU x.1.2
  have d2 := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU x.2.2
  rw [Matrix.det_fin_two] at d1 d2
  have hrr1 : (c : K) * c = 1 := by
    rw [← e00, ← e11, ← e01, ← e10] at d1
    linear_combination d1
  have hrr2 : (c : K) * c = 1 := by
    rw [← e22, ← e33, ← e23, ← e32] at d2
    linear_combination d2
  refine Prod.ext (Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_))
  · ext i j
    show (((x.1 : GL (Fin 2) K) ^ 2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = _
    rw [pow_two, Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← e00, ← e01, ← e10, ← e11, hrr1]
  · ext i j
    show (((x.2 : GL (Fin 2) K) ^ 2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = _
    rw [pow_two, Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← e22, ← e23, ← e32, ← e33, hrr2]

end Pair4


theorem rankFourCover_psu4_two {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e)
    (h9 : p ^ e ≠ 9) :
    RankFourCover p (StatedProj (StatedSU 4 (p ^ e) (GaloisField p (2 * e)))) := by
  classical
  have hp : p.Prime := Fact.out
  set K := GaloisField p (2 * e) with hKdef
  have hK : Nat.card K = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
  have hodd : Odd (p ^ e) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 : (2 : K) ≠ 0 := by
    have : ringChar K = p := ringChar.eq K p
    exact Ring.two_ne_zero (by rw [this]; exact hp2)
  obtain ⟨e₁⟩ := nonempty_sl2_mulEquiv_statedSU_two (r := p) (f := e) hK
  have hF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p e) = p ^ e :=
    CFSG.LieType.Steinberg.card_fixedSubfield hK
  have hFc : CharP (CFSG.LieType.Steinberg.fixedSubfield K p e) p := by
    have := Fintype.ofFinite (CFSG.LieType.Steinberg.fixedSubfield K p e)
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have hq : 1 ≤ p ^ e := hodd.pos
  let ι : Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield K p e) ×
      Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield K p e) →*
      StatedProj (StatedSU 4 (p ^ e) K) :=
    (QuotientGroup.mk' _).comp ((blockPairSU4 hq).comp (e₁.toMonoidHom.prodMap e₁.toMonoidHom))
  refine rankFourCover_of_cover_ker hp hp2
    (fun _ _ _ ρ hρ hk => rank_four_of_cover_SL2_prod hF hF hp2 he he (by rw [hF]; exact h9)
      (by rw [hF]; exact h9) ρ hρ hk) ι ?_ (orderOf_eq_prime (negDiagPSU4_sq (K := K) hodd)
        (negDiagPSU4_ne_one h2 hodd)) ?_
  · intro x hx
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hx
    have hsq := sq_eq_one_of_blockPairSU4_mem_scalars hq hx
    apply (e₁.prodCongr e₁).injective
    rw [map_pow, map_one]
    exact hsq
  · intro x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, negDiagPSU4, ← map_mul, ← map_mul,
      blockPairSU4_commute hq hodd]

end CFSG.RankThree.PartOne.SRC
