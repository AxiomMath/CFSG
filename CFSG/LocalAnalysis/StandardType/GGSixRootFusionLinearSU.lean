module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section SU

open Matrix CFSG.LieType.Universal.Unitary

@[expose] def ggInvUNil (n l : ℕ) (F : Type*) [Field F] : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun a b => if (b : ℕ) < l ∧ (a : ℕ) + b + 1 = n ∧ (b : ℕ) < a then 1 else 0

@[expose] def ggInvUMatrix (n l : ℕ) (F : Type*) [Field F] : Matrix (Fin n) (Fin n) F :=
  1 + ggInvUNil n l F

variable {F : Type*} [Field F]

theorem ggInvUNil_apply (n l : ℕ) (a b : Fin n) :
    ggInvUNil n l F a b = if (b : ℕ) < l ∧ (a : ℕ) + b + 1 = n ∧ (b : ℕ) < a then 1 else 0 :=
  rfl

theorem ggInvUNil_mul_self (n l : ℕ) : ggInvUNil n l F * ggInvUNil n l F = 0 := by
  ext a c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [ggInvUNil_apply, ggInvUNil_apply]
  by_cases h1 : (b : ℕ) < l ∧ (a : ℕ) + b + 1 = n ∧ (b : ℕ) < a
  · by_cases h2 : (c : ℕ) < l ∧ (b : ℕ) + c + 1 = n ∧ (c : ℕ) < b
    · exfalso
      omega
    · rw [ite_eq_right h2, mul_zero]
  · rw [ite_eq_right h1, zero_mul]

theorem det_ggInvUMatrix (n l : ℕ) : (ggInvUMatrix n l F).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [ggInvUMatrix, ggInvUNil_apply]
  · intro a b hab
    have hab' : a < b := by simpa using hab
    have : (a : ℕ) < b := hab'
    simp only [ggInvUMatrix, Matrix.add_apply, Matrix.one_apply_ne hab'.ne, ggInvUNil_apply,
      zero_add]
    split_ifs with h1
    · omega
    · rfl

theorem ggInvUMatrix_mul_self [CharP F 2] (n l : ℕ) :
    ggInvUMatrix n l F * ggInvUMatrix n l F = 1 := by
  have hN : ggInvUNil n l F + ggInvUNil n l F = 0 := by
    ext a b
    simp [CharTwo.add_self_eq_zero]
  rw [ggInvUMatrix, add_mul, mul_add, mul_add, ggInvUNil_mul_self n l, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, add_assoc, hN, add_zero]

theorem map_ggInvUMatrix (σ : F ≃+* F) (n l : ℕ) :
    (ggInvUMatrix n l F).map σ = ggInvUMatrix n l F := by
  ext a b
  simp only [ggInvUMatrix, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    ggInvUNil_apply, map_add]
  congr 1 <;> split_ifs <;> simp

@[expose] def ggInvUDiag (n l : ℕ) (F : Type*) [Field F] : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun a b => if a = b ∧ (a : ℕ) < l then 1 else 0

theorem antidiag_mul_ggInvUNil {n l : ℕ} (h : 2 * l ≤ n) :
    antidiag n * ggInvUNil n l F = ggInvUDiag n l F := by
  ext a b
  simp only [Matrix.mul_apply, antidiag, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, ggInvUNil_apply, ggInvUDiag]
  simp only [Fin.val_rev, Fin.ext_iff]
  have ha := a.isLt
  have hb := b.isLt
  split_ifs <;> first | rfl | (exfalso; omega)

theorem antidiag_apply_eq (n : ℕ) (c b : Fin n) :
    (antidiag n : Matrix (Fin n) (Fin n) F) c b = if c = Fin.rev b then 1 else 0 := by
  by_cases h : c = Fin.rev b
  · subst h
    simp [antidiag]
  · have h' : ¬ b = Fin.rev c := fun h'' => h (by rw [h'', Fin.rev_rev])
    simp [antidiag, h, h']

theorem ggInvUNil_transpose_mul_antidiag {n l : ℕ} (h : 2 * l ≤ n) :
    (ggInvUNil n l F)ᵀ * antidiag n = ggInvUDiag n l F := by
  ext a b
  simp only [Matrix.mul_apply, antidiag_apply_eq, Matrix.transpose_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ggInvUNil_apply, ggInvUDiag,
    Matrix.of_apply]
  simp only [Fin.val_rev, Fin.ext_iff]
  have ha := a.isLt
  have hb := b.isLt
  split_ifs <;> first | rfl | (exfalso; omega)

theorem ggInvUDiag_mul_ggInvUNil {n l : ℕ} (h : 2 * l ≤ n) :
    ggInvUDiag n l F * ggInvUNil n l F = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  simp only [ggInvUDiag, Matrix.of_apply, ggInvUNil_apply]
  by_cases h1 : a = c ∧ (a : ℕ) < l
  · obtain ⟨rfl, ha⟩ := h1
    rw [ite_eq_left ⟨rfl, ha⟩, one_mul, ite_eq_right (by omega)]
  · rw [ite_eq_right h1, zero_mul]

theorem ggInvUMatrix_isometry [CharP F 2] (σ : F ≃+* F) {n l : ℕ} (h : 2 * l ≤ n) :
    conjTr σ (ggInvUMatrix n l F) * antidiag n * ggInvUMatrix n l F = antidiag n := by
  have hD : ggInvUDiag n l F + ggInvUDiag n l F = 0 := by
    ext a b
    simp [CharTwo.add_self_eq_zero]
  rw [conjTr, map_ggInvUMatrix, ggInvUMatrix, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.add_mul (1 : Matrix (Fin n) (Fin n) F) (ggInvUNil n l F)ᵀ (antidiag n),
    Matrix.one_mul, ggInvUNil_transpose_mul_antidiag h, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, Matrix.mul_one, Matrix.mul_one, antidiag_mul_ggInvUNil h,
    ggInvUDiag_mul_ggInvUNil h, add_zero, add_assoc, hD, add_zero]

@[expose] noncomputable def ggInvSU [CharP F 2] (σ : F ≃+* F) (n l : ℕ) : SU σ n :=
  if h : 2 * l ≤ n then
    ⟨⟨ggInvUMatrix n l F, ggInvUMatrix n l F, ggInvUMatrix_mul_self n l,
        ggInvUMatrix_mul_self n l⟩,
      det_ggInvUMatrix n l, ggInvUMatrix_isometry σ h⟩
  else 1

theorem coe_ggInvSU [CharP F 2] (σ : F ≃+* F) {n l : ℕ} (h : 2 * l ≤ n) :
    (((ggInvSU σ n l : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = ggInvUMatrix n l F := by
  rw [ggInvSU, dite_eq_left h]

theorem eq_zero_of_mul_single_comm {n : ℕ} {Z : Matrix (Fin n) (Fin n) F} {i j : Fin n}
    (hZ : Z * Matrix.single i j 1 = Matrix.single i j 1 * Z) :
    (∀ x, x ≠ i → Z x i = 0) ∧ ∀ y, y ≠ j → Z j y = 0 := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h := congrFun (congrFun hZ x) j
    rwa [Matrix.mul_single_apply_same, mul_one, Matrix.single_mul_apply_of_ne _ _ _ _ _ hx]
      at h
  · have h := congrFun (congrFun hZ i) y
    rwa [Matrix.single_mul_apply_same, one_mul, Matrix.mul_single_apply_of_ne _ _ _ _ _ hy,
      eq_comm] at h

theorem eq_one_of_mem_center_SU_of_sq_eq_one [CharP F 2] (σ : F ≃+* F) {n : ℕ}
    {z : SU σ n} (hz : z ∈ Subgroup.center (SU σ n)) (hz2 : z ^ 2 = 1) : z = 1 := by
  set Z : Matrix (Fin n) (Fin n) F := ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have h1 : (1 : F) ∈ traceZero σ := by
    change (1 : F) + σ 1 = 0
    rw [map_one, CharTwo.add_self_eq_zero]
  have hcomm : ∀ i : Fin n, i ≠ Fin.rev i →
      Z * Matrix.single i (Fin.rev i) 1 = Matrix.single i (Fin.rev i) 1 * Z := by
    intro i hi
    have hc := Subgroup.mem_center_iff.mp hz (longRootHom σ hi (Multiplicative.ofAdd ⟨1, h1⟩))
    have hm := congrArg (fun w : SU σ n => ((w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hc
    simp only [Subgroup.coe_mul, Units.val_mul, coe_longRootHom, toAdd_ofAdd] at hm
    rw [longRootMatrix, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul] at hm
    exact (add_left_cancel hm).symm
  have hdiag : ∀ x y : Fin n, x ≠ y → Z x y = 0 := by
    intro x y hxy
    by_cases hy : y = Fin.rev y
    · have hx : Fin.rev x ≠ Fin.rev (Fin.rev x) := by
        rw [Fin.rev_rev]
        intro h'
        apply hxy
        have h2 : (x : ℕ) + x + 1 = n := by
          have := congrArg Fin.val h'
          rw [Fin.val_rev] at this
          omega
        have h3 : (y : ℕ) + y + 1 = n := by
          have := congrArg Fin.val hy
          rw [Fin.val_rev] at this
          omega
        exact Fin.ext (by omega)
      have := (eq_zero_of_mul_single_comm (hcomm _ hx)).2 y
      rw [Fin.rev_rev] at this
      exact this (Ne.symm hxy)
    · exact (eq_zero_of_mul_single_comm (hcomm y hy)).1 x hxy
  have hsq : Z * Z = 1 := by
    have := congrArg (fun w : SU σ n => ((w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hz2
    simpa [pow_two, Z] using this
  have hone : Z = 1 := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      have h := congrFun (congrFun hsq x) x
      rw [Matrix.mul_apply, Finset.sum_eq_single x (fun c _ hc => by
        rw [hdiag x c (Ne.symm hc), zero_mul]) (by simp), Matrix.one_apply_eq] at h
      have h0 : (Z x x + 1) * (Z x x + 1) = 0 := by
        have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
        linear_combination h + (Z x x + 1) * h2
      have := mul_self_eq_zero.mp h0
      rw [← CharTwo.sub_eq_add] at this
      rw [Matrix.one_apply_eq]
      exact sub_eq_zero.mp this
    · rw [hdiag x y hxy, Matrix.one_apply_ne hxy]
  exact Subtype.ext (Units.ext hone)

end SU

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

@[expose] def GGSUInvolutionClassInput : Prop :=
  ∀ (f n : ℕ), 1 ≤ f → ∀ u : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
    orderOf u = 2 → ∃ l : ℕ, 1 ≤ l ∧ 2 * l ≤ n ∧
      ∃ a : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
        u = a * ggInvSU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n l * a⁻¹

theorem ggRootFusionWitnessAlt_of_specialUnitary (hAS : GGSUInvolutionClassInput) {G : Type}
    [Group G] {n f : ℕ}
    (ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n →* G) {p : ℕ}
    {Bs D E G₀ : Subgroup G} {t : StatedLieTag} {r : G} (hrange : ψ.range = G₀)
    (hker : ψ.ker ≤
      Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n))
    (hr : ∃ v a : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n,
      r = ψ (v * (a * ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n 1 *
        a⁻¹) * v⁻¹))
    (hrep : ∀ l : ℕ, 2 ≤ l → 2 * l ≤ n →
      GGRootFusionWitnessAlt p Bs D E G₀ (Subgroup.normalizer (G₀ : Set G)) t (f + 1) r
        (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n l)))
    {s : G} (hs : s ∈ G₀) (hs2 : orderOf s = 2) :
    GGRootFusionWitnessAlt p Bs D E G₀ (Subgroup.normalizer (G₀ : Set G)) t (f + 1) r s := by
  have hle : ψ.range ≤ Subgroup.normalizer (G₀ : Set G) :=
    fun y hy => Subgroup.le_normalizer (hrange ▸ hy)
  have hkerinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1 := fun z hz hz2 =>
    eq_one_of_mem_center_SU_of_sq_eq_one _ (hker hz) hz2
  obtain ⟨u, hu, hu2⟩ := exists_orderOf_eq_two_of_mem_range ψ hkerinv (hrange ▸ hs) hs2
  obtain ⟨l, hl1, hl2, a, rfl⟩ := hAS (f + 1) n (by omega) u hu2
  have hmN : (ψ a)⁻¹ ∈ Subgroup.normalizer (G₀ : Set G) := Subgroup.inv_mem _ (hle ⟨a, rfl⟩)
  refine GGRootFusionWitnessAlt.of_conj hmN ?_
  have hconj : (ψ a)⁻¹ * s * (ψ a)⁻¹⁻¹ =
      ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n l) := by
    rw [← hu, map_mul, map_mul, map_inv, inv_inv]
    group
  rw [hconj]
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    obtain ⟨v, a', rfl⟩ := hr
    refine ggRootFusionWitnessAlt_of_lift_conj ψ hle (a := (v * a')⁻¹) ?_
    group
  · exact hrep l hl hl2

section Inputs

@[expose] def GGSURootClassInput : Prop :=
  ∀ (n f : ℕ) (γ : Fin (ggU .PSU n (f + 1)).D.rank → ℤ),
    GGRootClass (ggU .PSU n (f + 1)).D .PSU γ → ∀ z ∈ (ggU .PSU n (f + 1)).D.rootGroup γ, z ≠ 1 →
      ∃ a : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n,
        z = a * ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n 1 * a⁻¹

@[expose] def GGSixRootFusionSURepInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSU n (f + 1)).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSU n (f + 1)).D .PSU n (f + 1) ψ →
      GGSixStepOne p B Bs x L D J → GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU .PSU n (f + 1)).D .PSU ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
        Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) →
          ∀ l : ℕ, 2 ≤ l → 2 * l ≤ n →
            GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .PSU (f + 1) r
              (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n l))

theorem ggSixRootFusionWitnessInputFor_PSU (hAS : GGSUInvolutionClassInput)
    (hroot : GGSURootClassInput) (hrep : GGSixRootFusionSURepInput) :
    GGSixRootFusionWitnessInputFor (· = .PSU) := by
  intro G _ _ p B Bs x L D J t n f ψ ht hctx s1 s2 E r hch hC hodd s hs hs2
  subst ht
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by have := hctx.2.2.2.1.1.2.1; omega⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hr : ∃ v a : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n,
      r = ψ (v * (a * ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n 1 *
        a⁻¹) * v⁻¹) := by
    obtain ⟨-, -, -, -, hr2, γ, hγ, v, -, hrv⟩ := hch
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hrv
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [map_one, map_one, orderOf_one] at hr2
      exact absurd hr2 (by norm_num)
    obtain ⟨a, ha⟩ := hroot n f γ hγ z hz hz1
    subst ha
    exact ⟨v, a, rfl⟩
  exact ggRootFusionWitnessAlt_of_specialUnitary hAS ψ hrange hker hr
    (hrep G p B Bs x L D J n f ψ hctx s1 s2 E r hch hC hodd) hs hs2

theorem ggSixRootFusionWitnessInputFor_linearUnitary (hSL : GGSLInvolutionClassInput)
    (hSLrep : GGSixRootFusionSLRepInput) (hSU : GGSUInvolutionClassInput)
    (hSUroot : GGSURootClassInput) (hSUrep : GGSixRootFusionSURepInput) :
    GGSixRootFusionWitnessInputFor GGLinearUnitaryTag := by
  intro G _ _ p B Bs x L D J t n f ψ ht
  rcases ht with rfl | rfl
  · exact ggSixRootFusionWitnessInputFor_PSL hSL hSLrep G p B Bs x L D J .PSL n f ψ rfl
  · exact ggSixRootFusionWitnessInputFor_PSU hSU hSUroot hSUrep G p B Bs x L D J .PSU n f ψ rfl

end Inputs

end CFSG.StandardType
