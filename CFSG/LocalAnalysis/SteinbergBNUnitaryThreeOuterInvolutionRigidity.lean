module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineAutomorphism
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismModel
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public noncomputable section

namespace CFSG.LocalAnalysis

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism CFSG.BenderSuzuki.MatrixGroups

def unitaryPSUEquivPrimeFormOne {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (n : ℕ) :
    unitaryPSU h n ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)) (by
    ext z
    constructor
    · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
      exact ⟨c, hcN, hcn, hy⟩
    · rintro ⟨c, hcN, hcn, hz⟩
      exact ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h n)).symm z, ⟨c, hcN, hcn, hz⟩,
        MulEquiv.apply_symm_apply _ _⟩)

theorem even_unitary_three_outer_involution_bar_conjugate {D : Type} [Group D] {f : ℕ}
    (hf : 2 ≤ f) (hD : StatedClassicalModel D .PSU 3 2 f) (α : MulAut D) (hα : orderOf α = 2)
    (hαout : α ∉ (MulAut.conj : D →* MulAut D).range) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData 2 f K)
      (ζ : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≃* D),
      ∀ x, α (ζ x) = ζ (primeFormFieldAut h isPrimeFormGram_one
        (fieldDataHermitianForm h).conj x) := by
  obtain ⟨⟨-, hf1, -⟩, K, _, _, hK, ⟨eD⟩⟩ := hD
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(3 = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  let Φ : D ≃* primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    eD.trans ((unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm.trans
      (unitaryPSUEquivPrimeFormOne h 3))
  set α' := MulAut.congr Φ α with hα'
  have hα'2 : orderOf α' = 2 := by rw [hα', MulEquiv.orderOf_eq, hα]
  have hout : ∀ y, α' ≠ MulAut.conj y := by
    intro y hy
    apply hαout
    refine ⟨Φ.symm y, ?_⟩
    apply (MulAut.congr Φ).injective
    rw [← hα', hy]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hlift := even_unitary_involution_matrix_lifts h isPrimeFormGram_one (by norm_num) hq α' hα'2
  rcases hlift.1 with hφ | hφ
  · obtain ⟨s, -, -, hs⟩ := hlift.2.1 hφ
    exact absurd (hs.trans (primeFormConjHom_eq_conj h _ s)) (hout _)
  obtain ⟨-, -, C₀, hC₀, hC₀1, -, -, -, -, ⟨θ, -, hθα⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h isPrimeFormGram_one (by norm_num) hq α' hα'2 hφ
  obtain rfl : C₀ = 1 := by
    rcases hC₀1 with h1 | ⟨r, hr, -⟩
    · exact Units.ext h1
    · omega
  have hφJ : primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq α' =
      (fieldDataHermitianForm h).conj := RingEquiv.ext fun x => (hφ x).trans rfl
  refine ⟨K, inferInstance, inferInstance, h, θ.trans Φ.symm, fun x => ?_⟩
  have h1 := hθα (θ x)
  rw [MulEquiv.symm_apply_apply, hφJ] at h1
  simp only [MulEquiv.trans_apply]
  rw [← h1, hα', MulAut.congr_apply]
  simp




variable {K : Type} [Field K]

instance unitaryScalarCenter_normal (J : HermitianForm 3 K) : (scalarCenter J).Normal :=
  Subgroup.normal_of_le_center (scalarCenter_le_center J)

@[expose] def evenUnitaryThreeFrame [CharP K 2] : GL (Fin 3) K where
  val := !![1, 1, 0; 1, 1, 1; 0, 1, 1]
  inv := !![0, 1, 1; 1, 1, 1; 1, 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem coe_evenUnitaryThreeFrame [CharP K 2] :
    ((evenUnitaryThreeFrame : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 1, 0; 1, 1, 1; 0, 1, 1] :=
  rfl

theorem glAut_evenUnitaryThreeFrame [CharP K 2] (φ : K ≃+* K) :
    glAut φ (evenUnitaryThreeFrame : GL (Fin 3) K) = evenUnitaryThreeFrame := by
  apply Units.ext
  rw [coe_glAut, coe_evenUnitaryThreeFrame]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem evenUnitaryThreeFrame_gram {f : ℕ} (h : UnitaryFieldData 2 f K) [CharP K 2] :
    (((evenUnitaryThreeFrame : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
        ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((evenUnitaryThreeFrame : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  rw [coe_evenUnitaryThreeFrame, Units.val_one, Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem specialSubgroup_eq_gramSU {f : ℕ} (h : UnitaryFieldData 2 f K) {J : HermitianForm 3 K}
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hJc : ∀ c, J.conj c = h.bar c) :
    J.specialSubgroup = gramSU h !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext A
  have hct : J.conjTranspose (A : Matrix (Fin 3) (Fin 3) K) =
      ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
    ext i j
    simp [HermitianForm.conjTranspose, hJc]
  rw [HermitianForm.mem_specialSubgroup_iff, mem_gramSU, Units.ext_iff,
    GeneralLinearGroup.val_det_apply, Units.val_one, hct, hJ]

theorem specialLinearGroup_two_simple_perfect_of_charTwo {k : Type*} [Field k]
    (h2 : (2 : k) = 0) (hk : ∃ s : Finset k, s.card = 4) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) ∧
      Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k) := by
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have hr1 : r = 1 := by
      have h3 : (r + 1) ^ 2 = 0 := by linear_combination hr + (r + 1) * h2
      have h4 : r + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
      linear_combination h4 - h2
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) k))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcenter]
  let e : Matrix.SpecialLinearGroup (Fin 2) k ≃* ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective _ ⟨hinj, QuotientGroup.mk'_surjective _⟩
  obtain ⟨-, hsimp, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := k) (n := 2) le_rfl
    (Or.inr hk)
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := k) (n := 2) le_rfl (Or.inr hk)
  exact ⟨e.isSimpleGroup, Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

theorem even_unitary_three_subline_rigidity_of_bar_conjugate {D : Type} [Group D] {f : ℕ}
    [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hJc : ∀ c, J.conj c = h.bar c) (α : MulAut D)
    (ζ : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≃* D)
    (hζ : ∀ x, α (ζ x) = ζ (primeFormFieldAut h isPrimeFormGram_one J.conj x))
    (Ψ : MulAut (J.specialSubgroup ⧸ scalarCenter J))
    (hΨ : ∀ g : J.specialSubgroup, ∃ hg : glAut J.conj (g : GL (Fin 3) K) ∈ J.specialSubgroup,
      Ψ (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    (hΨfix : ∀ x ∈ sublineL J (scalarCenter J) hJ, Ψ x = x)
    (htwo : ∀ P : Subgroup (MulAut (J.specialSubgroup ⧸ scalarCenter J)), IsPGroup 2 P →
      (∀ β ∈ P, ∀ x ∈ sublineL J (scalarCenter J) hJ, β x = x) → Nat.card P ≤ 2) :
    Nat.card (unitaryCoverFixedField J) = 2 ^ f ∧
    ∃ j : Matrix.SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) →* D,
      Function.Injective j ∧ (∀ x ∈ j.range, α x = x) ∧ IsSimpleGroup j.range ∧
      Group.IsPerfect j.range ∧ (¬∀ a b : j.range, a * b = b * a) ∧
      (∀ P : Subgroup (MulAut D), IsPGroup 2 P → (∀ β ∈ P, ∀ x ∈ j.range, β x = x) →
        Nat.card P ≤ 2) ∧
      ∃ η : J.specialSubgroup ⧸ scalarCenter J ≃* D,
        (∀ g : J.specialSubgroup, ∃ hg : glAut J.conj (g : GL (Fin 3) K) ∈ J.specialSubgroup,
          α (η (QuotientGroup.mk g)) = η (QuotientGroup.mk ⟨_, hg⟩)) ∧
        ∀ m : Matrix.SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J),
          ∃ g : J.specialSubgroup, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
              !![(m 0 0 : K), 0, (m 0 1 : K); 0, 1, 0; (m 1 0 : K), 0, (m 1 1 : K)] ∧
            j m = η (QuotientGroup.mk g) := by
  classical
  have hS := specialSubgroup_eq_gramSU h hJ hJc
  set B : GL (Fin 3) K := evenUnitaryThreeFrame with hBdef
  have hB := evenUnitaryThreeFrame_gram h
  let ψ : J.specialSubgroup ≃* gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (MulEquiv.subgroupCongr hS).trans (gramTransportSU h hB)
  have hψ : ∀ g : J.specialSubgroup, ((ψ g : gramSU h _) : GL (Fin 3) K) = B * g * B⁻¹ :=
    fun g => rfl
  have hmap : (scalarCenter J).map (ψ : J.specialSubgroup →* gramSU h
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      normOneScalars h (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3 := by
    ext z
    constructor
    · rintro ⟨y, ⟨c, hy, hcn, hc3⟩, rfl⟩
      have hc0 : c ≠ 0 := by
        rintro rfl
        simp at hcn
      refine ⟨Units.mk0 c hc0, ?_, ?_, ?_⟩
      · change c * h.bar c = 1
        rw [← hJc]
        exact hcn
      · apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc3, Units.val_one]
      · have hyc : (y : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) :=
          Units.ext (by rw [hy, GeneralLinearGroup.coe_scalar, Units.val_mk0])
        change ((ψ y : gramSU h _) : GL (Fin 3) K) = _
        rw [hψ, hyc, (commute_scalar _ B).eq, mul_inv_cancel_right]
    · rintro ⟨c, -, -, hz⟩
      refine ⟨ψ.symm z, ?_, ψ.apply_symm_apply z⟩
      apply mem_scalarCenter_of_scalar J hJ (c := (c : K))
      have h1 : ((ψ.symm z : J.specialSubgroup) : GL (Fin 3) K) = B⁻¹ * z * B⁻¹⁻¹ := rfl
      rw [h1, hz, (commute_scalar c B⁻¹).eq, mul_inv_cancel_right, GeneralLinearGroup.coe_scalar]
  let ε : J.specialSubgroup ⧸ scalarCenter J ≃*
      primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    QuotientGroup.congr _ _ ψ hmap
  let η : J.specialSubgroup ⧸ scalarCenter J ≃* D := ε.trans ζ
  have hη : ∀ g : J.specialSubgroup, η (QuotientGroup.mk g) = ζ (QuotientGroup.mk (ψ g)) :=
    fun g => congrArg ζ (QuotientGroup.congr_mk _ _ _ _ g)
  have hαη : ∀ (g : J.specialSubgroup) (hg : glAut J.conj (g : GL (Fin 3) K) ∈ J.specialSubgroup),
      α (η (QuotientGroup.mk g)) = η (QuotientGroup.mk ⟨_, hg⟩) := by
    intro g hg
    rw [hη, hη, hζ, primeFormFieldAut_mk]
    congr 2
    apply Subtype.ext
    change glAut J.conj (B * (g : GL (Fin 3) K) * B⁻¹) = B * glAut J.conj (g : GL (Fin 3) K) * B⁻¹
    rw [map_mul, map_mul, map_inv, hBdef, glAut_evenUnitaryThreeFrame]
  have hαΨ : ∀ x, α (η x) = η (Ψ x) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨hg, hΨg⟩ := hΨ g
    rw [hΨg, hαη g hg]
  let j : Matrix.SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) →* D :=
    η.toMonoidHom.comp ((QuotientGroup.mk' (scalarCenter J)).comp (sublineHom J hJ))
  have hj : ∀ m, j m = η (QuotientGroup.mk (sublineHom J hJ m)) := fun m => rfl
  have hjinj : Function.Injective j := by
    intro m m' hmm
    have h1 : (QuotientGroup.mk (sublineHom J hJ m) : J.specialSubgroup ⧸ scalarCenter J) =
        QuotientGroup.mk (sublineHom J hJ m') := η.injective hmm
    obtain ⟨c, hc, -, -⟩ := exists_scalar_of_mk_eq le_rfl h1
    have h11 := congrFun (congrFun hc 1) 1
    rw [scalar_apply, mul_diagonal, coe_sublineHom, coe_sublineHom] at h11
    simp only [of_apply, cons_val', cons_val_one, cons_val_zero, empty_val', cons_val_fin_one,
      one_mul] at h11
    rw [h11, map_one, Matrix.mul_one] at hc
    exact sublineHom_injective hJ (Subtype.ext (Units.ext hc))
  have hjfix : ∀ x ∈ j.range, α x = x := by
    rintro _ ⟨m, rfl⟩
    have h1 := hΨfix (QuotientGroup.mk (sublineHom J hJ m)) ⟨m, rfl⟩
    rw [hj, hαΨ, h1]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [hJc, h.mem_fixedField])).trans h.card_fixedField
  have hk : Nat.card (unitaryCoverFixedField J) = 2 ^ f :=
    CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism.card_fixedField J hfixed
  have hk4 : ∃ s : Finset (unitaryCoverFixedField J), s.card = 4 := by
    have : Fintype (unitaryCoverFixedField J) := Fintype.ofFinite _
    have h4 : 4 ≤ (Finset.univ : Finset (unitaryCoverFixedField J)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
    exact ⟨s, hs⟩
  have h2k : (2 : unitaryCoverFixedField J) = 0 := CharTwo.two_eq_zero
  obtain ⟨hSLs, hSLp⟩ := specialLinearGroup_two_simple_perfect_of_charTwo h2k hk4
  let eJ := MonoidHom.ofInjective hjinj
  have hJs : IsSimpleGroup j.range := eJ.symm.isSimpleGroup
  have hJp : Group.IsPerfect j.range :=
    Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hJnab : ¬∀ a b : j.range, a * b = b * a := by
    intro hab
    have h1 : commutator j.range = ⊥ := by
      rw [_root_.commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro x _ y _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab x y
    have h2 := hJp.commutator_eq_top
    rw [h1] at h2
    obtain ⟨x, y, hxy⟩ := hJs.exists_pair_ne
    exact hxy (by
      have hx : x ∈ (⊥ : Subgroup j.range) := h2 ▸ Subgroup.mem_top x
      have hy : y ∈ (⊥ : Subgroup j.range) := h2 ▸ Subgroup.mem_top y
      rw [Subgroup.mem_bot] at hx hy
      rw [hx, hy])
  have hjtwo : ∀ P : Subgroup (MulAut D), IsPGroup 2 P → (∀ β ∈ P, ∀ x ∈ j.range, β x = x) →
      Nat.card P ≤ 2 := by
    intro P hP hPfix
    have hP' := hP.map (MulAut.congr η.symm).toMonoidHom
    have hfix' : ∀ β ∈ P.map (MulAut.congr η.symm).toMonoidHom,
        ∀ x ∈ sublineL J (scalarCenter J) hJ, β x = x := by
      rintro _ ⟨β, hβ, rfl⟩ _ ⟨m, rfl⟩
      have h1 := hPfix β hβ (j m) ⟨m, rfl⟩
      rw [hj] at h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
        MulEquiv.symm_symm]
      change η.symm (β (η (QuotientGroup.mk (sublineHom J hJ m)))) = _
      rw [h1, MulEquiv.symm_apply_apply]
      rfl
    have h2 := htwo _ hP' hfix'
    rwa [Subgroup.card_map_of_injective (MulAut.congr η.symm).injective] at h2
  refine ⟨hk, j, hjinj, hjfix, hJs, hJp, hJnab, hjtwo, η, fun g => ?_, fun m => ?_⟩
  · obtain ⟨hg, -⟩ := hΨ g
    exact ⟨hg, hαη g hg⟩
  · exact ⟨sublineHom J hJ m, coe_sublineHom hJ m, rfl⟩

theorem even_unitary_three_outer_involution_perfect_fixed_rigidity {D : Type} [Group D] {f : ℕ}
    (hf : 2 ≤ f) (hD : StatedClassicalModel D .PSU 3 2 f) (α : MulAut D) (hα : orderOf α = 2)
    (hαout : α ∉ (MulAut.conj : D →* MulAut D).range) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (F : HermitianForm 3 K),
      F.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
      Nat.card K = (2 ^ f) ^ 2 ∧ (∀ c : K, F.conj c = c ^ 2 ^ f) ∧
      (∀ g : F.specialSubgroup, g ∈ scalarCenter F ↔
        ∃ c : K, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c) ∧
      Nat.card (unitaryCoverFixedField F) = 2 ^ f ∧
      ∃ j : Matrix.SpecialLinearGroup (Fin 2) (unitaryCoverFixedField F) →* D,
        Function.Injective j ∧ (∀ x ∈ j.range, α x = x) ∧ IsSimpleGroup j.range ∧
        Group.IsPerfect j.range ∧ (¬∀ a b : j.range, a * b = b * a) ∧
        (∀ P : Subgroup (MulAut D), IsPGroup 2 P → (∀ β ∈ P, ∀ x ∈ j.range, β x = x) →
          Nat.card P ≤ 2) ∧
        ∃ η : F.specialSubgroup ⧸ scalarCenter F ≃* D,
          (∀ g : F.specialSubgroup, ∃ hg : glAut F.conj (g : GL (Fin 3) K) ∈ F.specialSubgroup,
            α (η (QuotientGroup.mk g)) = η (QuotientGroup.mk ⟨_, hg⟩)) ∧
          ∀ m : Matrix.SpecialLinearGroup (Fin 2) (unitaryCoverFixedField F),
            ∃ g : F.specialSubgroup, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
                !![(m 0 0 : K), 0, (m 0 1 : K); 0, 1, 0; (m 1 0 : K), 0, (m 1 1 : K)] ∧
              j m = η (QuotientGroup.mk g) := by
  obtain ⟨K, _, _, h, ζ, hζ⟩ := even_unitary_three_outer_involution_bar_conjugate hf hD α hα hαout
  have : CharP K 2 := h.charP
  have hF : (fieldDataHermitianForm h).form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  have hcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [h.card]
    ring
  obtain ⟨-, -, -, -, -, -, -, -, -, hbar, -, hrange, -, -, -, htwo, -⟩ :=
    unitary_central_cover_subline_automorphism_two_part (fieldDataHermitianForm h) f hf hcard
      (card_fixed_fieldDataHermitianForm h) hF (scalarCenter _) le_rfl
  have hmem : sublineAutHom _ (scalarCenter _) hF le_rfl
      (SemidirectProduct.inr ⟨(fieldDataHermitianForm h).conj, Subgroup.mem_zpowers _⟩) ∈
        sublineFixingAut _ (scalarCenter _) hF := by
    rw [← hrange]
    exact ⟨_, rfl⟩
  obtain ⟨hk, j, hjinj, hjfix, hJs, hJp, hJnab, hjtwo, η, hη, hjm⟩ :=
    even_unitary_three_subline_rigidity_of_bar_conjugate h hf (fieldDataHermitianForm h) hF
      (fieldDataHermitianForm_conj h) α ζ hζ _ hbar ((mem_sublineFixingAut hF).mp hmem) htwo
  refine ⟨K, inferInstance, inferInstance, fieldDataHermitianForm h, hF, hcard,
    fun c => (fieldDataHermitianForm_conj h c).trans (h.bar_apply c), fun g => ⟨fun hg => ?_,
      fun ⟨c, hc⟩ => mem_scalarCenter_of_scalar _ hF hc⟩, hk, j, hjinj, hjfix, hJs, hJp, hJnab,
    hjtwo, η, hη, hjm⟩
  obtain ⟨c, hc, -, -⟩ := (mem_scalarCenter _).mp hg
  exact ⟨c, hc⟩

end CFSG.LocalAnalysis
