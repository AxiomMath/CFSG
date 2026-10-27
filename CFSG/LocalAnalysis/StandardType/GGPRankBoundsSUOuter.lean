module

public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSUInner

public section

namespace CFSG.StandardType

namespace PRankBounds

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
  CFSG.ComponentClassification.OuterAutomorphisms

section Frob

variable {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]

@[expose] noncomputable def frobGL : GL (Fin 5) K →* GL (Fin 5) K :=
  Matrix.GeneralLinearGroup.map (unitaryInvolution K 2 1 : K →+* K)

theorem coe_frobGL (A : GL (Fin 5) K) :
    ((frobGL A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      (A : Matrix (Fin 5) (Fin 5) K).map (unitaryInvolution K 2 1) :=
  rfl

theorem frobGL_frobGL (hK : Nat.card K = (2 ^ 1) ^ 2) (A : GL (Fin 5) K) :
    frobGL (frobGL A) = A := by
  apply Units.ext
  rw [coe_frobGL, coe_frobGL]
  ext i j
  simp only [Matrix.map_apply]
  exact unitaryInvolution_involutive hK _

theorem frobGL_mem (hK : Nat.card K = (2 ^ 1) ^ 2) {A : GL (Fin 5) K}
    (hA : A ∈ StatedSU 5 (2 ^ 1) K) : frobGL A ∈ StatedSU 5 (2 ^ 1) K := by
  have hle : StatedSU 5 (2 ^ 1) K ≤ (StatedSU 5 (2 ^ 1) K).comap frobGL := by
    refine (Subgroup.closure_le _).mpr fun B hB => ?_
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [coe_frobGL]
      change ((unitaryInvolution K 2 1 : K →+* K).mapMatrix (B : Matrix (Fin 5) (Fin 5) K)).det
        = 1
      rw [← RingHom.map_det, hB.1, map_one]
    · have hσ : ∀ M : Matrix (Fin 5) (Fin 5) K, M.map (· ^ (2 ^ 1)) =
          M.map (unitaryInvolution K 2 1) := fun M => by
        ext i j
        simp only [Matrix.map_apply, unitaryInvolution_apply]
      have h1 := hB.2
      rw [hσ] at h1
      rw [coe_frobGL, hσ]
      have h2 : ((B : Matrix (Fin 5) (Fin 5) K).map (unitaryInvolution K 2 1)).map
          (unitaryInvolution K 2 1) = (B : Matrix (Fin 5) (Fin 5) K) := by
        ext i j
        simp only [Matrix.map_apply]
        exact unitaryInvolution_involutive hK _
      rw [h2]
      have h3 := congrArg Matrix.transpose h1
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h3
  exact hle hA

@[expose] noncomputable def frobSU (hK : Nat.card K = (2 ^ 1) ^ 2) :
    MulAut (StatedSU 5 (2 ^ 1) K) where
  toFun A := ⟨frobGL A, frobGL_mem hK A.2⟩
  invFun A := ⟨frobGL A, frobGL_mem hK A.2⟩
  left_inv A := Subtype.ext (frobGL_frobGL hK A)
  right_inv A := Subtype.ext (frobGL_frobGL hK A)
  map_mul' A B := Subtype.ext (map_mul frobGL (A : GL (Fin 5) K) B)

theorem coe_frobSU (hK : Nat.card K = (2 ^ 1) ^ 2) (A : StatedSU 5 (2 ^ 1) K) :
    ((frobSU hK A : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) = frobGL (A : GL (Fin 5) K) :=
  rfl

theorem exists_omega_card_four (hK : Nat.card K = (2 ^ 1) ^ 2) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ^ 2 ≠ ω := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have h2 := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ, Fintype.card_eq_nat_card, hK] at h2
    norm_num at h2
  have h4 : ω ^ 4 = ω := by
    have h := FiniteField.pow_card ω
    rw [Fintype.card_eq_nat_card, hK] at h
    norm_num at h
    exact h
  refine ⟨ω, ?_, ?_⟩
  · have : ω * (ω ^ 3 - 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hω0
    · exact sub_eq_zero.mp h
  · intro h2
    have : ω * (ω - 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · exact hω0 h
    · exact hω1 (sub_eq_zero.mp h)

theorem frobSU_not_inner (hK : Nat.card K = (2 ^ 1) ^ 2) :
    frobSU hK ∉ inner (StatedSU 5 (2 ^ 1) K) := by
  rintro ⟨g, hg⟩
  obtain ⟨ω, hω3, hω2⟩ := exists_omega_card_four hK
  set dg : Fin 5 → K := ![ω, ω, ω, 1, 1] with hdg
  have hdet : (Matrix.diagonal dg).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_five]
    show ω * ω * ω * 1 * 1 = 1
    linear_combination hω3
  set A : GL (Fin 5) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal dg)
    (by rw [hdet]; exact one_ne_zero) with hAdef
  have hAmat : (A : Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal dg := rfl
  have hA : A ∈ StatedSU 5 (2 ^ 1) K := by
    refine Subgroup.subset_closure ⟨by rw [hAmat]; exact hdet, ?_⟩
    rw [hAmat]
    have hmap : (Matrix.diagonal dg).map (· ^ (2 ^ 1)) = Matrix.diagonal fun i => dg i ^ 2 := by
      rw [Matrix.diagonal_map (by norm_num)]
      rfl
    rw [hmap, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hdg] <;> linear_combination hω3
  have h1 := congrArg (fun φ : MulAut (StatedSU 5 (2 ^ 1) K) =>
    ((((φ ⟨A, hA⟩ : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))) hg
  simp only [MulAut.conj_apply, coe_frobSU, coe_frobGL] at h1
  have htr := congrArg Matrix.trace h1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul] at htr
  change Matrix.trace (A : Matrix (Fin 5) (Fin 5) K) =
    Matrix.trace ((A : Matrix (Fin 5) (Fin 5) K).map (unitaryInvolution K 2 1)) at htr
  have htrA : Matrix.trace (A : Matrix (Fin 5) (Fin 5) K) = ω := by
    rw [hAmat, Matrix.trace_diagonal, Fin.sum_univ_five]
    show ω + ω + ω + 1 + 1 = ω
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination (ω + 1) * h2
  have htrM : Matrix.trace ((A : Matrix (Fin 5) (Fin 5) K).map (unitaryInvolution K 2 1)) =
      unitaryInvolution K 2 1 (Matrix.trace (A : Matrix (Fin 5) (Fin 5) K)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [htrM, htrA, unitaryInvolution_apply, pow_one] at htr
  exact hω2 htr.symm

end Frob

section Outer

variable {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]

omit [Fact (Nat.Prime 2)] [CharP K 2] [Finite K] in
theorem eq_of_ne_one_of_card_two {Q : Type*} [Group Q] (h : Nat.card Q = 2) {x y : Q}
    (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp h
  rw [hz x hx, hz y hy]

theorem false_of_suFive_outer (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hOut : Nat.card (Outer (StatedSU 5 (2 ^ 1) K)) = 2)
    (α : MulAut (StatedSU 5 (2 ^ 1) K)) (hα : α ∉ inner (StatedSU 5 (2 ^ 1) K))
    (E : Subgroup (StatedSU 5 (2 ^ 1) K)) (hE : IsElemAbelian 3 E) (h27 : 3 ^ 3 ≤ Nat.card E)
    (hfix : ∀ e ∈ E, α e = e) : False := by
  classical
  have hcls : (QuotientGroup.mk α : Outer (StatedSU 5 (2 ^ 1) K)) =
      QuotientGroup.mk (frobSU hK) := by
    refine eq_of_ne_one_of_card_two hOut ?_ ?_
    · intro h
      exact hα ((QuotientGroup.eq_one_iff α).mp h)
    · intro h
      exact frobSU_not_inner hK ((QuotientGroup.eq_one_iff _).mp h)
  obtain ⟨k, hk⟩ := QuotientGroup.eq.mp hcls
  have hσ : frobSU hK = α * MulAut.conj k := by
    rw [hk]
    group
  set g : StatedSU 5 (2 ^ 1) K := (frobSU hK k)⁻¹ with hgdef
  have hge : ∀ e ∈ E, g * frobSU hK e * g⁻¹ = e := by
    intro e he
    have h1 : frobSU hK (k⁻¹ * e * k) = e := by
      rw [hσ, MulAut.mul_apply, MulAut.conj_apply]
      have : k * (k⁻¹ * e * k) * k⁻¹ = e := by group
      rw [this]
      exact hfix e he
    rw [map_mul, map_mul, map_inv] at h1
    rw [hgdef, inv_inv]
    exact h1
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : ExpChar L 2 := ExpChar.prime Nat.prime_two
  set ι' : K →+* L := algebraMap K L with hι'
  set Φ : GL (Fin 5) K →* GL (Fin 5) L := Matrix.GeneralLinearGroup.map ι' with hΦdef
  have hΦ : Function.Injective Φ := CFSG.RankThree.PartTwo.Sec4.map_injective_GL ι'
  set E₀ : Subgroup (GL (Fin 5) K) := E.map (StatedSU 5 (2 ^ 1) K).subtype with hE₀
  set EL : Subgroup (GL (Fin 5) L) := E₀.map Φ with hEL
  have hΦmat : ∀ x : GL (Fin 5) K, ((Φ x : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) =
      (x : Matrix (Fin 5) (Fin 5) K).map ι' := fun x => rfl
  have hmemEL : ∀ y ∈ EL, ∃ x ∈ E, y = Φ ((x : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hcomm : ∀ x ∈ EL, ∀ y ∈ EL, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hmemEL y hy
    rw [← map_mul, ← map_mul]
    congr 1
    have h : x₀ * y₀ = y₀ * x₀ :=
      congrArg Subtype.val ((isMulCommutative_iff.mp hE.1) ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩)
    exact congrArg Subtype.val h
  have hexp : ∀ x ∈ EL, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    rw [← map_pow, ← Subgroup.coe_pow, hE.2 x₀ hx₀, Subgroup.coe_one, map_one]
  have : Finite E₀ :=
    Finite.of_surjective _ ((StatedSU 5 (2 ^ 1) K).subtype.subgroupMap_surjective E)
  have : Finite EL := Finite.of_surjective _ (Φ.subgroupMap_surjective E₀)
  have hcard : Nat.card EL = Nat.card E := by
    rw [hEL, Subgroup.card_map_of_injective hΦ, hE₀,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have h3 : (3 : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have : (3 : L) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  obtain ⟨b, d, hb⟩ := CFSG.RankThree.PartTwo.Sec4.exists_common_eigenbasis_pow_three h3 EL
    hcomm hexp
  set φ : L →+* L := frobenius L 2 with hφ
  have hφinj : Function.Injective φ := frobenius_inj L 2
  set vF : (Fin 5 → L) → (Fin 5 → L) := fun u i => φ (u i) with hvF
  set gL : Matrix (Fin 5) (Fin 5) L :=
    ((Φ ((g : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) : GL (Fin 5) L) :
      Matrix (Fin 5) (Fin 5) L) with hgL
  have htw : ∀ x ∈ EL, ∀ a, (x : Matrix (Fin 5) (Fin 5) L) *ᵥ (gL *ᵥ vF (b a)) =
      (d x a) ^ 2 • (gL *ᵥ vF (b a)) := by
    intro x hx a
    obtain ⟨e, he, rfl⟩ := hmemEL x hx
    have hcomm' : ((e : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) * (g : GL (Fin 5) K) =
        (g : GL (Fin 5) K) * frobGL ((e : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) := by
      have h := congrArg Subtype.val (hge e he)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_frobSU] at h
      calc ((e : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) * (g : GL (Fin 5) K) =
          (g : GL (Fin 5) K) * frobGL ((e : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) *
            (g : GL (Fin 5) K)⁻¹ * (g : GL (Fin 5) K) := by rw [h]
        _ = _ := by group
    have hmat := congrArg (fun y : GL (Fin 5) K => ((Φ y : GL (Fin 5) L) :
      Matrix (Fin 5) (Fin 5) L)) hcomm'
    simp only [map_mul, Units.val_mul] at hmat
    have hfr : ((Φ (frobGL ((e : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K)) : GL (Fin 5) L) :
        Matrix (Fin 5) (Fin 5) L) =
        (((Φ ((e : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K)) : GL (Fin 5) L) :
          Matrix (Fin 5) (Fin 5) L).map φ := by
      rw [hΦmat, hΦmat, coe_frobGL]
      ext i j
      simp only [Matrix.map_apply, unitaryInvolution_apply, pow_one, map_pow, hφ, frobenius_def]
    have hfrv : ∀ u, ((Φ (frobGL ((e : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K)) : GL (Fin 5) L) :
        Matrix (Fin 5) (Fin 5) L) *ᵥ vF u = vF ((((Φ ((e : StatedSU 5 (2 ^ 1) K) :
          GL (Fin 5) K)) : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) *ᵥ u) := by
      intro u
      rw [hfr]
      funext i
      simp only [hvF]
      rw [RingHom.map_mulVec]
      rfl
    rw [Matrix.mulVec_mulVec, hmat, ← Matrix.mulVec_mulVec, hfrv, hb _ hx a]
    have : vF (d (Φ ((e : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K)) a • b a) =
        (d (Φ ((e : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K)) a) ^ 2 • vF (b a) := by
      funext i
      simp only [hvF, Pi.smul_apply, smul_eq_mul, hφ, frobenius_def]
      ring
    rw [this, Matrix.mulVec_smul]
  have hw0 : ∀ a, gL *ᵥ vF (b a) ≠ 0 := by
    intro a h0
    set N : Matrix (Fin 5) (Fin 5) L := (((Φ ((g : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K))⁻¹ :
      GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) with hN
    have hNg : N * gL = 1 := by rw [hN, hgL, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h1 : vF (b a) = 0 := by
      have h2 : N *ᵥ (gL *ᵥ vF (b a)) = N *ᵥ 0 := by rw [h0]
      rwa [Matrix.mulVec_mulVec, hNg, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    apply b.ne_zero a
    funext i
    have := congrFun h1 i
    exact hφinj (by simpa [hvF] using this)
  have hF4 : ∀ (w : Fin 5 → L) (ψ : GL (Fin 5) L → L),
      (∀ x ∈ EL, (x : Matrix (Fin 5) (Fin 5) L) *ᵥ w = ψ x • w) →
        ∀ c, b.repr w c ≠ 0 → ∀ x ∈ EL, ψ x = d x c := by
    intro w ψ hw c hc x hx
    have hxw : (x : Matrix (Fin 5) (Fin 5) L) *ᵥ w = ∑ i, (b.repr w i * d x i) • b i := by
      conv_lhs => rw [← b.sum_repr w]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hb x hx i, smul_smul]
    have h1 : b.repr ((x : Matrix (Fin 5) (Fin 5) L) *ᵥ w) c = b.repr w c * d x c := by
      rw [hxw, b.repr_sum_self]
    rw [hw x hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    exact mul_right_cancel₀ hc (h1.trans (mul_comm _ _))
  have hinvchar : ∀ a, ∃ c, ∀ x ∈ EL, d x c = (d x a)⁻¹ := by
    intro a
    obtain ⟨c, hc⟩ : ∃ c, b.repr (gL *ᵥ vF (b a)) c ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hw0 a
      rw [← b.sum_repr (gL *ᵥ vF (b a))]
      simp [hall]
    refine ⟨c, fun x hx => ?_⟩
    have h1 := hF4 _ (fun x => d x a ^ 2) (fun x hx => htw x hx a) c hc x hx
    have h3a := CFSG.RankThree.PartTwo.Sec4.eigen_pow_three hb hx (hexp x hx) a
    rw [← h1]
    exact eq_inv_of_mul_eq_one_left (by linear_combination h3a)
  set C : Finset (EL → L) := Finset.univ.image fun a => fun x : EL => d x a with hCdef
  have hC5 : C.card ≤ 5 := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin 5)))
      (f := fun a => fun x : EL => d x a)
    simpa using this
  have h := CFSG.RankThree.PartTwo.Sec4.card_sq_le_of_characters (G := EL) (K := L) C.card C ⊤
    le_rfl
    (by
      intro χ hχ x _ y _
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
      exact CFSG.RankThree.PartTwo.Sec4.eigen_mul hb x.2 y.2 a)
    (by
      intro χ hχ x _
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
      exact CFSG.RankThree.PartTwo.Sec4.eigen_pow_three hb x.2 (hexp x x.2) a)
    (by
      intro χ hχ
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
      obtain ⟨c, hc⟩ := hinvchar a
      exact ⟨fun x : EL => d x c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩,
        fun x _ => hc x x.2⟩)
    (by
      intro x _ hx
      apply Subtype.ext
      rw [Subgroup.coe_one]
      refine CFSG.RankThree.PartTwo.Sec4.eigen_ext hb x.2 EL.one_mem fun a => ?_
      rw [CFSG.RankThree.PartTwo.Sec4.eigen_one hb a]
      exact hx _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
  rw [Subgroup.card_top, hcard] at h
  have h' : Nat.card E ^ 2 ≤ 3 ^ 5 := h.trans (Nat.pow_le_pow_right (by norm_num) hC5)
  have h'' : (3 ^ 3) ^ 2 ≤ Nat.card E ^ 2 := Nat.pow_le_pow_left h27 2
  norm_num at h' h''
  omega

end Outer

end PRankBounds

open PRankBounds CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms in
theorem ggUFiveTwoOuterCentInput_holds : GGUFiveTwoOuterCentInput := by
  intro X _ _ hmod α _ hαout E hE hfix
  by_contra hlt
  push Not at hlt
  have hOutX := card_outer_psu5 hmod
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_four hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let e₁ : StatedProj (StatedSU 5 (2 ^ 1) K) ≃* StatedSU 5 (2 ^ 1) K :=
    (QuotientGroup.quotientMulEquivOfEq (scalars_statedSU_five_eq_bot hK)).trans
      QuotientGroup.quotientBot
  set j : X ≃* StatedSU 5 (2 ^ 1) K := e.trans e₁
  have hOutS : Nat.card (Outer (StatedSU 5 (2 ^ 1) K)) = 2 :=
    (Nat.card_congr (equivalence j).toEquiv).symm.trans hOutX
  set α' : MulAut (StatedSU 5 (2 ^ 1) K) := MulAut.congr j α with hα'
  have hα'out : α' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedSU 5 (2 ^ 1) K) := by
    intro h
    apply hαout
    rw [← inner_map_congr j] at h
    obtain ⟨β, hβ, hβα⟩ := h
    have hβα' : β = α := (MulAut.congr j).injective hβα
    rwa [hβα'] at hβ
  refine false_of_suFive_outer hK hOutS α' hα'out (E.comap j.symm.toMonoidHom)
    (isElemAbelian_comap_of_inj _ j.symm.injective hE) ?_ ?_
  · have hcard : Nat.card (E.comap j.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        { toFun := fun y => ⟨j.symm y, y.2⟩
          invFun := fun x => ⟨j x, by
            change j.symm (j x) ∈ E
            rw [MulEquiv.symm_apply_apply]
            exact x.2⟩
          left_inv := fun y => Subtype.ext (by simp)
          right_inv := fun x => Subtype.ext (by simp) }
    rw [hcard]
    exact le_trans (by norm_num) hlt
  · intro y hy
    have hy' : j.symm y ∈ E := hy
    show j (α (j.symm y)) = y
    rw [hfix _ hy', MulEquiv.apply_symm_apply]

section Tag

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank PRankBounds

theorem ggUFiveTwoRankInput_holds : GGUFiveTwoRankInput :=
  ggUFiveTwoRankInput_of_inner_outer ggUFiveTwoLocalInnerInput_holds
    ggUFiveTwoOuterCentInput_holds

end Tag

end CFSG.StandardType
