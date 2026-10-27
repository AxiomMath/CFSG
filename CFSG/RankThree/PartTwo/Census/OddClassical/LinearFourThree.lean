module

public import CFSG.RankThree.PartTwo.Census.OddClassical.ComponentCentral
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedTools

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven Matrix
open scoped MatrixGroups

abbrev nineBase : Type :=
  ↥(CFSG.LieType.Steinberg.fixedSubfield (GaloisField 3 2) 3 1)

theorem card_galoisField_three_two : Nat.card (GaloisField 3 2) = 9 := by
  rw [GaloisField.card 3 2 (by norm_num)]
  norm_num

theorem card_nineBase : Nat.card nineBase = 3 := by
  have h := CFSG.LieType.Steinberg.card_fixedSubfield (F := GaloisField 3 2) (p := 3) (f := 1)
    (by rw [card_galoisField_three_two]; norm_num)
  rwa [pow_one] at h

theorem fintype_card_nineBase [Fintype nineBase] : Fintype.card nineBase = 3 := by
  rw [← Nat.card_eq_fintype_card, card_nineBase]

theorem mem_nineBase_iff (c : GaloisField 3 2) :
    c ∈ CFSG.LieType.Steinberg.fixedSubfield (GaloisField 3 2) 3 1 ↔ c ^ 3 = c := by
  rw [CFSG.LieType.Steinberg.mem_fixedSubfield, CFSG.LieType.BorelTits.unitaryInvolution_apply,
    pow_one]

theorem exists_mul_self_eq_neg_one_nine : ∃ i : GaloisField 3 2, i * i = -1 := by
  have := Fintype.ofFinite (GaloisField 3 2)
  obtain ⟨i, hi⟩ : IsSquare (-1 : GaloisField 3 2) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card,
      card_galoisField_three_two]
    decide
  exact ⟨i, hi.symm⟩

@[expose] noncomputable def nineI : GaloisField 3 2 := exists_mul_self_eq_neg_one_nine.choose

theorem nineI_mul_self : nineI * nineI = -1 := exists_mul_self_eq_neg_one_nine.choose_spec

theorem two_ne_zero_nine : (2 : GaloisField 3 2) ≠ 0 := by
  intro h0
  have := (CharP.cast_eq_zero_iff (GaloisField 3 2) 3 2).mp (by exact_mod_cast h0)
  omega

theorem nineI_not_mem : nineI ∉ CFSG.LieType.Steinberg.fixedSubfield (GaloisField 3 2) 3 1 := by
  rw [mem_nineBase_iff]
  intro h
  have h' : nineI ^ 3 = -nineI := by
    rw [pow_succ, pow_two, nineI_mul_self, neg_one_mul]
  rw [h'] at h
  have h0 : (2 : GaloisField 3 2) * nineI = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h0 with h2 | h2
  · exact two_ne_zero_nine h2
  · have := nineI_mul_self
    rw [h2, mul_zero] at this
    exact one_ne_zero (neg_eq_zero.mp this.symm)

theorem linearIndependent_one_nineI :
    LinearIndependent nineBase ![(1 : GaloisField 3 2), nineI] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
    exact ⟨(map_eq_zero_iff _ (algebraMap nineBase (GaloisField 3 2)).injective).mp hst, rfl⟩
  · exfalso
    apply nineI_not_mem
    have h1 : t • nineI = -(s • (1 : GaloisField 3 2)) := eq_neg_of_add_eq_zero_right hst
    have hi : nineI = (-(t⁻¹ * s)) • (1 : GaloisField 3 2) :=
      calc nineI = (t⁻¹ * t) • nineI := by rw [inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • (t • nineI) := mul_smul _ _ _
        _ = t⁻¹ • (-(s • (1 : GaloisField 3 2))) := by rw [h1]
        _ = (-(t⁻¹ * s)) • (1 : GaloisField 3 2) := by
          rw [smul_neg, smul_smul]
          exact (neg_smul _ _).symm
    rw [hi, Algebra.smul_def, mul_one]
    exact (-(t⁻¹ * s)).2

theorem finrank_nine : Module.finrank nineBase (GaloisField 3 2) = 2 := by
  have := Fintype.ofFinite (GaloisField 3 2)
  have := Fintype.ofFinite nineBase
  have h := Module.card_eq_pow_finrank (K := nineBase) (V := GaloisField 3 2)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_galoisField_three_two,
    card_nineBase] at h
  have h2 : (3 : ℕ) ^ Module.finrank nineBase (GaloisField 3 2) = 3 ^ 2 := by
    rw [← h]
    norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2

@[expose] noncomputable def nineBasis : Module.Basis (Fin 2) nineBase (GaloisField 3 2) :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_one_nineI
    (by rw [Fintype.card_fin, finrank_nine])

theorem nineBasis_zero : nineBasis 0 = 1 := by
  rw [nineBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

theorem nineBasis_one : nineBasis 1 = nineI := by
  rw [nineBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

@[expose] noncomputable def leftMulNine :
    GaloisField 3 2 →ₐ[nineBase] Matrix (Fin 2) (Fin 2) nineBase :=
  Algebra.leftMulMatrix nineBasis

theorem leftMulNine_injective : Function.Injective leftMulNine :=
  Algebra.leftMulMatrix_injective nineBasis

@[expose] noncomputable def nineR : Matrix (Fin 2) (Fin 2) nineBase := !![0, -1; 1, 0]

theorem leftMulNine_i : leftMulNine nineI = nineR := by
  have col0 : ∀ r, nineBasis.repr (nineI * nineBasis 0) r = nineR r 0 := by
    intro r
    rw [nineBasis_zero, mul_one, ← nineBasis_one, Module.Basis.repr_self]
    fin_cases r <;> simp [nineR]
  have col1 : ∀ r, nineBasis.repr (nineI * nineBasis 1) r = nineR r 1 := by
    intro r
    rw [nineBasis_one, nineI_mul_self, ← nineBasis_zero, map_neg, Module.Basis.repr_self]
    fin_cases r <;> simp [nineR, Finsupp.coe_neg]
  refine Matrix.ext fun r c => ?_
  rw [leftMulNine, Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases c
  · exact col0 r
  · exact col1 r

theorem leftMulNine_algebraMap (a : nineBase) :
    leftMulNine (algebraMap nineBase (GaloisField 3 2) a) = a • 1 := by
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

theorem exists_leftMulNine_eq_of_comm {M : Matrix (Fin 2) (Fin 2) nineBase}
    (hM : M * nineR = nineR * M) : ∃ x : GaloisField 3 2, leftMulNine x = M := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, M = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two M⟩
  have e1 := congrFun (congrFun hM 0) 0
  have e2 := congrFun (congrFun hM 0) 1
  simp [nineR, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2
  refine ⟨algebraMap _ _ a + algebraMap _ _ c * nineI, ?_⟩
  rw [map_add, map_mul, leftMulNine_algebraMap, leftMulNine_algebraMap, leftMulNine_i]
  refine Matrix.ext fun r k => ?_
  fin_cases r <;> fin_cases k <;> simp [nineR]
  all_goals first | linear_combination e1 | linear_combination -e1 | linear_combination e2

@[expose] noncomputable def nineBlock :
    Matrix (Fin 2) (Fin 2) (GaloisField 3 2) →+* Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) nineBase :=
  (Matrix.compRingEquiv (Fin 2) (Fin 2) nineBase).toRingHom.comp
    leftMulNine.toRingHom.mapMatrix

theorem nineBlock_apply (A : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) (a b c d : Fin 2) :
    nineBlock A (a, b) (c, d) = leftMulNine (A a c) b d :=
  rfl

theorem nineBlock_injective : Function.Injective nineBlock := by
  intro A B h
  refine Matrix.ext fun a c => ?_
  apply leftMulNine_injective
  refine Matrix.ext fun b d => ?_
  have := congrFun (congrFun h (a, b)) (c, d)
  rwa [nineBlock_apply, nineBlock_apply] at this

theorem isPerfect_sl2_nine : Group.IsPerfect SL(2, GaloisField 3 2) :=
  CFSG.ClassicalInvolution.sl2_isPerfect (by rw [card_galoisField_three_two]; norm_num)

theorem det_nineBlock (A : SL(2, GaloisField 3 2)) :
    (nineBlock (A : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))).det = 1 := by
  have := isPerfect_sl2_nine
  let D : SL(2, GaloisField 3 2) →* nineBaseˣ := GeneralLinearGroup.det.comp
    ((Units.map nineBlock.toMonoidHom).comp Matrix.SpecialLinearGroup.toGL)
  have h := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_one_of_isPerfect_of_comm D A
  have := congrArg Units.val h
  simpa [D] using this

@[expose] noncomputable def nineSL :
    SL(2, GaloisField 3 2) →* SpecialLinearGroup (Fin 2 × Fin 2) nineBase where
  toFun A := ⟨nineBlock (A : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)), det_nineBlock A⟩
  map_one' := Subtype.ext (by
    change nineBlock ((1 : SL(2, GaloisField 3 2)) : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, map_one])
  map_mul' A B := Subtype.ext (by
    change nineBlock ((A * B : SL(2, GaloisField 3 2)) : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) =
      nineBlock (A : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) *
        nineBlock (B : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))
    rw [Matrix.SpecialLinearGroup.coe_mul, map_mul])

theorem nineSL_injective : Function.Injective nineSL := by
  intro A B h
  exact Subtype.ext (nineBlock_injective (congrArg Subtype.val h))

theorem nineBlock_i_smul_one_apply (x y z w : Fin 2) :
    nineBlock (nineI • (1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))) (x, y) (z, w) =
      if x = z then nineR y w else 0 := by
  rw [nineBlock_apply]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hxz : x = z
  · simp [hxz, leftMulNine_i]
  · simp [hxz]

theorem nineBlock_i_smul_one :
    nineBlock (nineI • (1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))) =
      (blockDiagonal fun _ : Fin 2 => nineR).submatrix (Equiv.prodComm (Fin 2) (Fin 2))
        (Equiv.prodComm (Fin 2) (Fin 2)) := by
  refine Matrix.ext fun ⟨a, b⟩ ⟨c, d⟩ => ?_
  rw [nineBlock_i_smul_one_apply, submatrix_apply, blockDiagonal_apply]
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  by_cases hac : a = c
  · simp [hac]
  · simp [hac]

theorem det_nineBlock_i_smul_one :
    (nineBlock (nineI • (1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)))).det = 1 := by
  rw [nineBlock_i_smul_one, det_submatrix_equiv_self, det_blockDiagonal]
  simp [nineR, det_fin_two]

@[expose] noncomputable def nineInvolution : SpecialLinearGroup (Fin 2 × Fin 2) nineBase :=
  ⟨nineBlock (nineI • (1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))), det_nineBlock_i_smul_one⟩

theorem coe_nineInvolution :
    ((nineInvolution : SpecialLinearGroup (Fin 2 × Fin 2) nineBase) :
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) nineBase) =
      nineBlock (nineI • (1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))) :=
  rfl

theorem nineInvolution_sq_mem_center :
    nineInvolution ^ 2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2 × Fin 2) nineBase) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, ?_, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_fin]
    norm_num
  · rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_nineInvolution, ← map_mul,
      smul_mul_smul_comm, Matrix.one_mul, nineI_mul_self, neg_one_smul, map_neg, map_one,
      map_neg, map_one]

theorem nineInvolution_not_mem_center :
    nineInvolution ∉ Subgroup.center (SpecialLinearGroup (Fin 2 × Fin 2) nineBase) := by
  intro h
  have hs := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center h (0, 0)
  have h01 := congrFun (congrFun hs (0, 0)) (0, 1)
  rw [coe_nineInvolution, nineBlock_i_smul_one_apply, nineBlock_i_smul_one_apply] at h01
  simp [nineR] at h01

theorem isPGroup_center_SL_four :
    IsPGroup 2 (Subgroup.center (SpecialLinearGroup (Fin 2 × Fin 2) nineBase)) := by
  have := Fintype.ofFinite nineBase
  intro z
  obtain ⟨r, hr, hz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp z.2
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hr2 : r ^ 2 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [fintype_card_nineBase] at this
  have hz2 : (z : SpecialLinearGroup (Fin 2 × Fin 2) nineBase) ^ 2 = 1 := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hz, ← map_pow, hr2, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow, hz2]
  rfl

theorem exists_nineBlock_eq_of_comm {M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) nineBase}
    (hM : M * nineBlock (nineI • 1) = nineBlock (nineI • 1) * M) :
    ∃ A, nineBlock A = M := by
  have hblock : ∀ a c : Fin 2, ∃ x : GaloisField 3 2,
      leftMulNine x = Matrix.of fun b d => M (a, b) (c, d) := by
    intro a c
    refine exists_leftMulNine_eq_of_comm ?_
    refine Matrix.ext fun b d => ?_
    have := congrFun (congrFun hM (a, b)) (c, d)
    fin_cases a <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        nineBlock_i_smul_one_apply] at this ⊢ <;>
      linear_combination this
  choose x hx using hblock
  refine ⟨Matrix.of x, Matrix.ext fun ⟨a, b⟩ ⟨c, d⟩ => ?_⟩
  rw [nineBlock_apply, Matrix.of_apply, hx a c, Matrix.of_apply]

theorem conj_mem_range_nineSL {g : SpecialLinearGroup (Fin 2 × Fin 2) nineBase}
    (hg : g * nineInvolution = nineInvolution * g) (B : SL(2, GaloisField 3 2)) :
    g * nineSL B * g⁻¹ ∈ nineSL.range := by
  have hcomm : ∀ x : SpecialLinearGroup (Fin 2 × Fin 2) nineBase,
      x * nineInvolution = nineInvolution * x →
        ∃ A, nineBlock A = (x : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) nineBase) := by
    intro x hx
    refine exists_nineBlock_eq_of_comm ?_
    have h1 : ((x * nineInvolution : SpecialLinearGroup (Fin 2 × Fin 2) nineBase) :
        Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) nineBase) =
        ((nineInvolution * x : SpecialLinearGroup (Fin 2 × Fin 2) nineBase) :
          Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) nineBase) := by rw [hx]
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_nineInvolution] at h1
  obtain ⟨A, hA⟩ := hcomm g hg
  obtain ⟨A', hA'⟩ := hcomm g⁻¹ (Commute.inv_left hg).eq
  have hAA' : A * A' = 1 := nineBlock_injective (by
    rw [map_mul, hA, hA', map_one, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one])
  have hdet : (A * (B : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) * A').det = 1 := by
    rw [det_mul, det_mul, B.2, mul_one, ← det_mul, hAA', det_one]
  refine ⟨⟨A * B * A', hdet⟩, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
  change nineBlock (A * (B : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) * A') i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, map_mul, map_mul, hA,
    hA']
  rfl

theorem not_isCharTwoType_PSL_four_three :
    ¬ IsCharTwoType (ProjectiveSpecialLinearGroup (Fin 2 × Fin 2) nineBase) := by
  refine not_isCharTwoType_of_sl2_component' _ le_rfl nineInvolution_not_mem_center
    nineInvolution_sq_mem_center (J := nineSL.range) ?_ ?_
    (isPGroup_center_SL_four.to_le inf_le_right) (F := GaloisField 3 2)
    (by rw [card_galoisField_three_two]; norm_num)
    (by rw [card_galoisField_three_two]; decide) (MonoidHom.ofInjective nineSL_injective).symm
  · rintro _ ⟨B, rfl⟩
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_nineInvolution]
    change (nineBlock (B : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) *
      nineBlock (nineI • (1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)))) i j =
      (nineBlock (nineI • (1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))) *
        nineBlock (B : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))) i j
    rw [← map_mul, ← map_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  · rintro g hg _ ⟨B, rfl⟩
    exact conj_mem_range_nineSL hg B

section Transport

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

noncomputable def pslCongr {R S : Type} [CommRing R] [CommRing S]
    (φ : SpecialLinearGroup m R ≃* SpecialLinearGroup n S) :
    ProjectiveSpecialLinearGroup m R ≃* ProjectiveSpecialLinearGroup n S :=
  QuotientGroup.congr _ _ φ (by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩ g
      obtain ⟨g', rfl⟩ := φ.surjective g
      change φ g' * φ y = φ y * φ g'
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨φ.symm x, fun g => φ.injective ?_, by simp⟩
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hx])

noncomputable def slReindexEquiv {R : Type} [CommRing R] (e : m ≃ n) :
    SpecialLinearGroup m R ≃* SpecialLinearGroup n R where
  toFun A := ⟨reindex e e (A : Matrix m m R), by rw [det_reindex_self]; exact A.2⟩
  invFun A := ⟨reindex e.symm e.symm (A : Matrix n n R), by rw [det_reindex_self]; exact A.2⟩
  left_inv A := Subtype.ext (by simp)
  right_inv A := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    change reindex e e ((A : Matrix m m R) * (B : Matrix m m R)) =
      reindex e e (A : Matrix m m R) * reindex e e (B : Matrix m m R)
    rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv])

noncomputable def slRingEquiv {R S : Type} [CommRing R] [CommRing S] (f : R ≃+* S) :
    SpecialLinearGroup m R ≃* SpecialLinearGroup m S where
  toFun := SpecialLinearGroup.map f.toRingHom
  invFun := SpecialLinearGroup.map f.symm.toRingHom
  left_inv A := Subtype.ext (by ext i j; simp)
  right_inv A := Subtype.ext (by ext i j; simp)
  map_mul' := map_mul _

end Transport

theorem excluded433_A_three_three (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 3 q).Valid) (hq : q.p = 3) (hf : q.exponent = 1) :
    Excluded433 (.lie ⟨.A 3 q, hv⟩) := by
  intro G _ _ hG e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p q.exponent
  have := Fintype.ofFinite F
  have := Fintype.ofFinite nineBase
  have hF : Fintype.card F = 3 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card _ _ (by rw [hf]; norm_num), hq, hf]
    norm_num
  have : CharP F 3 := hq ▸ (inferInstance : CharP F q.p)
  let f : nineBase ≃+* F :=
    (ZMod.ringEquiv (n := 3) nineBase fintype_card_nineBase).symm.trans
      (ZMod.ringEquiv (n := 3) F hF)
  let ψ : ProjectiveSpecialLinearGroup (Fin 2 × Fin 2) nineBase ≃*
      ProjectiveSpecialLinearGroup (Fin (3 + 1)) F :=
    pslCongr ((slRingEquiv f).trans (slReindexEquiv finProdFinEquiv))
  refine hG.false_of_not_isCharTwoType
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv))
    (fun h => not_isCharTwoType_PSL_four_three ((isCharTwoType_congr ψ).mpr h))

end CFSG.RankThree.PartTwo.Census
