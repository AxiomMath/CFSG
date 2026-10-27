module

public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven Matrix
open scoped MatrixGroups

theorem pRank_le_two_of_noncomm {H : Type} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
    (h4 : ¬ p ^ 4 ∣ Nat.card H) {Q : Subgroup H} (hQ : IsPGroup p Q) {x y : H} (hx : x ∈ Q)
    (hy : y ∈ Q) (hxy : x * y ≠ y * x) : Assembly.pRank p (⊤ : Subgroup H) ≤ 2 := by
  by_cases h3 : p ^ 3 ∣ Nat.card H
  · obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
    have hpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
    have hf1 := (hp.out.pow_dvd_iff_le_factorization hpos).mp h3
    have hf2 : ¬ 4 ≤ (Nat.card H).factorization p := fun h =>
      h4 ((hp.out.pow_dvd_iff_le_factorization hpos).mpr h)
    have hS : Nat.card (S : Subgroup H) = p ^ 3 := by
      rw [S.card_eq_multiplicity]
      congr 1
      omega
    exact pRank_le_two_of_nonabelian hp.out h4 hS ⟨x, hQS hx, y, hQS hy, hxy⟩
  · exact pRank_le_two_of_not_dvd hp.out h3

section Unitriangular

variable {K : Type} [Field K]

@[expose] def IsUnitriThree (M : Matrix (Fin 3) (Fin 3) K) : Prop :=
  M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 2 2 = 1

theorem IsUnitriThree.mul {A B : Matrix (Fin 3) (Fin 3) K} (hA : IsUnitriThree A)
    (hB : IsUnitriThree B) : IsUnitriThree (A * B) := by
  obtain ⟨a10, a20, a21, a00, a11, a22⟩ := hA
  obtain ⟨b10, b20, b21, b00, b11, b22⟩ := hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, a00, a11, a22, b10, b20, b21, b00,
      b11, b22]

theorem IsUnitriThree.det_eq {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUnitriThree A) :
    A.det = 1 := by
  obtain ⟨a10, a20, a21, a00, a11, a22⟩ := hA
  simp [det_fin_three, a10, a20, a21, a00, a11, a22]

@[expose] def unitriangularThree (K : Type) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {A | IsUnitriThree (A : Matrix (Fin 3) (Fin 3) K)}
  mul_mem' {A B} hA hB := by
    change IsUnitriThree ((A : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K))
    exact hA.mul hB
  one_mem' := by
    change IsUnitriThree (1 : Matrix (Fin 3) (Fin 3) K)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  inv_mem' {A} hA := by
    change IsUnitriThree ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    have hdet := (show IsUnitriThree (A : Matrix (Fin 3) (Fin 3) K) from hA).det_eq
    rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
    obtain ⟨a10, a20, a21, a00, a11, a22⟩ := hA
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [adjugate_fin_three, a10, a20, a21, a00, a11, a22]

theorem mem_unitriangularThree {A : GL (Fin 3) K} :
    A ∈ unitriangularThree K ↔ IsUnitriThree (A : Matrix (Fin 3) (Fin 3) K) :=
  Iff.rfl

theorem IsUnitriThree.pow_three [CharP K 3] {N : Matrix (Fin 3) (Fin 3) K}
    (hN : IsUnitriThree N) : N ^ 3 = 1 := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  obtain ⟨a10, a20, a21, a00, a11, a22⟩ := hN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, a00, a11, a22] <;>
    first
      | ring1
      | linear_combination N 0 1 * h3
      | linear_combination N 1 2 * h3
      | linear_combination (N 0 2 + N 0 1 * N 1 2) * h3

theorem isPGroup_unitriangularThree [CharP K 3] : IsPGroup 3 (unitriangularThree K) := by
  intro g
  refine ⟨1, Subtype.ext (Units.ext ?_)⟩
  rw [pow_one, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
  exact (mem_unitriangularThree.mp g.2).pow_three

end Unitriangular

section LinearThree

variable {K : Type} [Field K]

@[expose] def slThreeX (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

@[expose] def slThreeY (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [det_fin_three]⟩

theorem slThreeX_mul_ne : slThreeX K * slThreeY K ≠ slThreeY K * slThreeX K := by
  intro h
  have h' := congrArg Subtype.val h
  change (!![1, 1, 0; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; 0, 1, 1; 0, 0, 1] :
    Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, 1; 0, 0, 1] * !![1, 1, 0; 0, 1, 0; 0, 0, 1] at h'
  have h02 := congrFun (congrFun h' 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h02

theorem pRank_three_SL_three_le [Finite K] (hK : Nat.card K = 3) :
    Assembly.pRank 3 (⊤ : Subgroup (SpecialLinearGroup (Fin 3) K)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  have hcard : Nat.card (SpecialLinearGroup (Fin 3) K) = 5616 := by
    rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hK]
    simp [Fin.prod_univ_three]
  refine pRank_le_two_of_noncomm (by rw [hcard]; decide)
    (Q := (unitriangularThree K).comap SpecialLinearGroup.toGL) ?_ (x := slThreeX K)
    (y := slThreeY K) ?_ ?_ slThreeX_mul_ne
  · intro g
    obtain ⟨k, hk⟩ := isPGroup_unitriangularThree (K := K) ⟨_, g.2⟩
    refine ⟨k, Subtype.ext (SpecialLinearGroup.toGL_injective ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  · show IsUnitriThree (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · show IsUnitriThree (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem center_SL_three_card_eq_one [Finite K] (hK : Nat.card K = 3) :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) = 1 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
  have hone : ∀ z : Subgroup.center (SpecialLinearGroup (Fin 3) K), z = 1 := by
    intro z
    obtain ⟨r, hr, hz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp z.2
    rw [Fintype.card_fin] at hr
    have hr1 : r = 1 := by
      have : r ^ 3 = 1 ^ 3 := by rw [hr, one_pow]
      exact frobenius_inj K 3 this
    apply Subtype.ext
    apply Subtype.ext
    rw [← hz, hr1, map_one]
    rfl
  rw [hone a, hone b]

theorem localRank_three_PSL_three_le_of_card_eq_three [Finite K] (hK : Nat.card K = 3) :
    localRank 3 (ProjectiveSpecialLinearGroup (Fin 3) K) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine localRank_le_of_pRank_le Nat.prime_three ?_
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) K)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (SpecialLinearGroup (Fin 3) K)) :=
    CFSG.SectionRank.pRank_quotient_eq _ (by rw [center_SL_three_card_eq_one hK]; norm_num)
  change CFSG.Open.pRank 3 _ ≤ 2
  rw [h1]
  exact pRank_three_SL_three_le hK

theorem excluded433_A_two_three (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (hq : q.p = 3) (hf : q.exponent = 1) :
    Excluded433 (.lie ⟨.A 2 q, hv⟩) := by
  intro G _ _ hG e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine hG.false_of_localRank_three_le_two
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv))
    (localRank_three_PSL_three_le_of_card_eq_three ?_)
  rw [GaloisField.card _ _ (by rw [hf]; norm_num), hq, hf]
  norm_num

end LinearThree

section UnitaryThree

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F]

@[expose] def suThreeXMat (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![1, 1, 1; 0, 1, -1; 0, 0, 1]

@[expose] def suThreeYMat (i : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, i, 1; 0, 1, i; 0, 0, 1]

theorem isUnitriThree_suThreeXMat : IsUnitriThree (suThreeXMat F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [suThreeXMat]

theorem isUnitriThree_suThreeYMat (i : F) : IsUnitriThree (suThreeYMat i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [suThreeYMat]

@[expose] noncomputable def suThreeX (F : Type) [Field F] : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero (suThreeXMat F)
    (by rw [isUnitriThree_suThreeXMat.det_eq]; exact one_ne_zero)

@[expose] noncomputable def suThreeY (i : F) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero (suThreeYMat i)
    (by rw [(isUnitriThree_suThreeYMat i).det_eq]; exact one_ne_zero)

variable [Finite F] [Fact (Nat.Prime 3)] [CharP F 3]

theorem suThreeX_mem : suThreeX F ∈ SU (unitaryInvolution F 3 1) 3 := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  refine ⟨isUnitriThree_suThreeXMat.det_eq, ?_⟩
  change conjTr (unitaryInvolution F 3 1) (suThreeXMat F) * antidiag 3 * suThreeXMat F = antidiag 3
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [conjTr, antidiag, suThreeXMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]
  all_goals first | ring1 | linear_combination h3

theorem suThreeY_mem {i : F} (hi : i * i = -1) (hσ : unitaryInvolution F 3 1 i = -i) :
    suThreeY i ∈ SU (unitaryInvolution F 3 1) 3 := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  refine ⟨(isUnitriThree_suThreeYMat i).det_eq, ?_⟩
  change conjTr (unitaryInvolution F 3 1) (suThreeYMat i) * antidiag 3 * suThreeYMat i =
    antidiag 3
  have hσ' : frobenius F 3 i = -i := by
    rw [← hσ, unitaryInvolution_apply, pow_one, frobenius_def]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [conjTr, antidiag, suThreeYMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev, hσ']
  all_goals first | ring1 | linear_combination h3 - hi

omit [Finite F] [Fact (Nat.Prime 3)] in
theorem suThreeX_mul_ne {i : F} (hi : i * i = -1) :
    suThreeX F * suThreeY i ≠ suThreeY i * suThreeX F := by
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff F 3 2).mp (by exact_mod_cast h0)
    omega
  intro h
  have h02 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 2) h
  simp only [Units.val_mul] at h02
  change (suThreeXMat F * suThreeYMat i) 0 2 = (suThreeYMat i * suThreeXMat F) 0 2 at h02
  simp [suThreeXMat, suThreeYMat, Matrix.mul_apply, Fin.sum_univ_three] at h02
  have hi0 : i = 0 := by
    have : (2 : F) * i = 0 := by linear_combination h02
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [hi0, mul_zero] at hi
  exact one_ne_zero (neg_eq_zero.mp hi.symm)

theorem pRank_three_SU_three_le (hF : Nat.card F = 9) :
    Assembly.pRank 3 (⊤ : Subgroup (SU (unitaryInvolution F 3 1) 3)) ≤ 2 := by
  have hF' : Nat.card F = (3 ^ 1) ^ 2 := by rw [hF]; norm_num
  obtain ⟨i, hi⟩ : IsSquare (-1 : F) := by
    have := Fintype.ofFinite F
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hF]
    decide
  have hi' : i * i = -1 := hi.symm
  have hσ : unitaryInvolution F 3 1 i = -i := by
    rw [unitaryInvolution_apply, pow_one, pow_succ, pow_two, hi', neg_one_mul]
  obtain ⟨P, hP⟩ := exists_wittMatrix hF' 3
  have hcard : Nat.card (SU (unitaryInvolution F 3 1) 3) = 6048 := by
    rw [Nat.card_congr ((conjEquiv P hP).trans
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hF' 3))).toEquiv]
    exact CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hF
  refine pRank_le_two_of_noncomm (by rw [hcard]; decide)
    (Q := (unitriangularThree F).subgroupOf (SU (unitaryInvolution F 3 1) 3)) ?_
    (x := ⟨suThreeX F, suThreeX_mem⟩) (y := ⟨suThreeY i, suThreeY_mem hi' hσ⟩) ?_ ?_ ?_
  · intro g
    obtain ⟨k, hk⟩ := isPGroup_unitriangularThree (K := F) ⟨_, g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  · exact isUnitriThree_suThreeXMat
  · exact isUnitriThree_suThreeYMat i
  · intro h
    exact suThreeX_mul_ne hi' (congrArg Subtype.val h)

theorem localRank_three_PSU_three_le (hF : Nat.card F = 9) :
    localRank 3 (StatedProj (StatedSU 3 3 F)) ≤ 2 := by
  have hF' : Nat.card F = (3 ^ 1) ^ 2 := by rw [hF]; norm_num
  refine localRank_le_of_pRank_le Nat.prime_three ?_
  obtain ⟨P, hP⟩ := exists_wittMatrix hF' 3
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 3 F))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSU 3 3 F)) :=
    CFSG.SectionRank.pRank_quotient_eq _ (by
      rw [CFSG.LinearGroups.UnitaryThreeOverNine.statedScalars_subgroupOf_statedSU_eq_bot hF,
        Subgroup.card_bot]
      norm_num)
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSU 3 3 F)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (SU (unitaryInvolution F 3 1) 3)) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) ((conjEquiv P hP).trans
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hF' 3)))).symm
  change CFSG.Open.pRank 3 _ ≤ 2
  rw [h1, h2]
  exact pRank_three_SU_three_le hF

end UnitaryThree

theorem excluded433_twistedA_two_three (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.p = 3) (hf : q.exponent = 1) :
    Excluded433 (.lie ⟨.twistedA 2 q, hv⟩) := by
  intro G _ _ hG e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = 3 :=
    (TauCeti.LieTypeIndex.characteristic_twistedA 2 q).trans hq
  have he : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = 1 :=
    (TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q).trans hf
  set K := GaloisField (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩)
    (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩)
  have hK : Nat.card K = 9 := by
    rw [GaloisField.card _ _ (by rw [he]; norm_num), hc, he]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hq3 : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = 3 := by rw [hc, he]; rfl
  have e' := e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv)
  rw [hq3] at e'
  exact hG.false_of_localRank_three_le_two e' (localRank_three_PSU_three_le hK)

end CFSG.RankThree.PartTwo.Census
