module

public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.GH74.KGroups.Cover

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

section Perfect

theorem eq_of_mk_eq_of_perfect {Γ : Type*} [Group Γ] (hperf : Group.IsPerfect Γ)
    (Z : Subgroup Γ) [Z.Normal] (hZ : Z ≤ Subgroup.center Γ) (α β : Γ ≃* Γ)
    (hαβ : ∀ g : Γ, (QuotientGroup.mk (α g) : Γ ⧸ Z) = QuotientGroup.mk (β g)) : α = β := by
  have hz : ∀ g : Γ, (β g)⁻¹ * α g ∈ Subgroup.center Γ := fun g =>
    hZ ((QuotientGroup.eq).mp (hαβ g).symm)
  let z : Γ →* Subgroup.center Γ :=
    { toFun := fun g => ⟨(β g)⁻¹ * α g, hz g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun g g' => by
        apply Subtype.ext
        have hc := (Subgroup.mem_center_iff.mp (hz g)) (β g')⁻¹
        calc (β (g * g'))⁻¹ * α (g * g') = (β g')⁻¹ * ((β g)⁻¹ * α g) * α g' := by
              simp [mul_assoc]
          _ = (β g)⁻¹ * α g * ((β g')⁻¹ * α g') := by
              rw [hc]
              simp only [mul_assoc] }
  have h1 := CFSG.GH74.KGroups.hom_center_trivial hperf z
  refine MulEquiv.ext fun g => ?_
  have h2 := congrArg Subtype.val (h1 g)
  have h3 : (β g)⁻¹ * α g = 1 := h2
  exact (inv_mul_eq_one.mp h3).symm

end Perfect

section Classify

variable {f : ℕ} {K : Type} [Field K]

abbrev gamma5 (h : UnitaryFieldData 2 f K) : Subgroup (GL (Fin 5) K) :=
  gramSU h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)

abbrev unit5 (h : UnitaryFieldData 2 f K) : Subgroup (GL (Fin 5) K) :=
  primeFormUnitary h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)

theorem iterate_induced {h : UnitaryFieldData 2 f K} (θ : gamma5 h ≃* gamma5 h)
    (θb : MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)))
    (hθb : ∀ g : gamma5 h, θb (g : primeFormP h _) = ((θ g : gamma5 h) : primeFormP h _))
    (n : ℕ) (g : gamma5 h) :
    (θb ^ n) (g : primeFormP h _) = (((θ ^ n) g : gamma5 h) : primeFormP h _) := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, hθb, ih, pow_succ, MulAut.mul_apply]

theorem su5_aut_classification (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    (hperf : Group.IsPerfect (gamma5 h)) (hcen : Nat.card (Subgroup.center (gamma5 h)) = 5)
    (θ : gamma5 h ≃* gamma5 h) (hθ : θ ^ 5 = 1) :
    (∃ (P : unit5 h) (c : Kˣ), h.norm (c : K) = 1 ∧
      (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c ∧
      ∀ g : gamma5 h, ((θ g : gamma5 h) : GL (Fin 5) K) =
        (P : GL (Fin 5) K) * g * (P : GL (Fin 5) K)⁻¹) ∨
    ∃ (φ : K ≃+* K) (M : unit5 h), φ ^ 5 = 1 ∧ φ ≠ 1 ∧ ∀ g : gamma5 h,
      ((θ g : gamma5 h) : GL (Fin 5) K) = (M : GL (Fin 5) K) *
        glAut φ ((M : GL (Fin 5) K)⁻¹ * (g : GL (Fin 5) K) * (M : GL (Fin 5) K)) *
          (M : GL (Fin 5) K)⁻¹ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn : 3 ≤ 5 := by norm_num
  have hq : ¬(5 = 3 ∧ 2 ^ f = 2) := fun hh => absurd hh.1 (by norm_num)
  have hC : IsPrimeFormGram (1 : GL (Fin 5) K) := isPrimeFormGram_one
  have hfin : Finite K := h.finite
  set Z := normOneScalars h (gamma5 h) 5 with hZdef
  have hZc : Z ≤ Subgroup.center (gamma5 h) := normOneScalars_le_center h _ 5
  have hZcard : Nat.card Z = 5 := by
    rw [hZdef, CFSG.RankThree.Classical.card_normOneScalars_one h (by norm_num)]
    exact Nat.gcd_eq_left h5
  have hZeq : Z = Subgroup.center (gamma5 h) :=
    Subgroup.eq_of_le_of_card_ge hZc (by rw [hZcard, hcen])
  have hmap : Z.map θ.toMonoidHom = Z := by
    rw [hZeq]
    exact CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv θ
  set θb : MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) :=
    QuotientGroup.congr Z Z θ hmap with hθbdef
  have hθb : ∀ g : gamma5 h, θb (g : primeFormP h _) = ((θ g : gamma5 h) : primeFormP h _) :=
    fun g => QuotientGroup.congr_mk _ _ _ _ g
  have hθb5 : θb ^ 5 = 1 := by
    refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
    rw [iterate_induced θ θb hθb 5 g, hθ]
    rfl
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq θb
  rw [primeFormPsi_apply] at hAφ
  have hφθ : primeFormFieldFactor h hC hn hq θb = φ := by
    rw [← hAφ]
    exact primeFormFieldFactor_apply h hC hn hq A φ
  have hφ5 : φ ^ 5 = 1 := by
    have := congrArg (primeFormFieldFactor h hC hn hq) hθb5
    rwa [map_pow, hφθ, map_one] at this
  by_cases hφ1 : φ = 1
  · left
    have hθc : θb = primeFormConjHom h _ A := by
      rw [← hAφ, hφ1, map_one, mul_one]
    have hA5 : primeFormConjHom h _ (A ^ 5) = 1 := by
      rw [map_pow, ← hθc]
      exact hθb5
    obtain ⟨-, c, hc1, hcA⟩ := (primeFormPsi_eq_one_iff h hC hn
      (⟨A ^ 5, 1⟩ : unit5 h ⋊[primeFormFieldU h hC] (K ≃+* K))).mp (by
        rw [primeFormPsi_apply, map_one, mul_one]
        exact hA5)
    refine ⟨A, c, hc1, ?_, fun g => ?_⟩
    · have := hcA
      simpa using this
    have hθeq : θ = primeFormConjSU h _ A := by
      refine eq_of_mk_eq_of_perfect hperf Z hZc θ (primeFormConjSU h _ A) fun g => ?_
      rw [← primeFormConjAut_mk, ← hθb g, hθc]
      rfl
    rw [hθeq]
    rfl
  · right
    have hφord : orderOf φ = 5 := orderOf_eq_prime hφ5 hφ1
    have hθne : θb ≠ 1 := by
      intro h1
      apply hφ1
      rw [← hφθ, h1, map_one]
    have hθord : orderOf θb = 5 := orderOf_eq_prime hθb5 hθne
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hq Nat.prime_five
        (by norm_num) (by norm_num) θb hθord φ hφθ hφord
    refine ⟨φ, M, hφ5, hφ1, fun g => ?_⟩
    set θF : gamma5 h ≃* gamma5 h := (primeFormConjSU h _ M⁻¹).trans
      ((primeFormFieldSU h hC φ).trans (primeFormConjSU h _ M)) with hθF
    have hθeq : θ = θF := by
      refine eq_of_mk_eq_of_perfect hperf Z hZc θ θF fun g => ?_
      have h1 : θb = primeFormConjHom h _ M * primeFormFieldHom h hC φ *
          (primeFormConjHom h _ M)⁻¹ := by
        rw [hM.symm]
        group
      rw [← hθb g, h1]
      simp only [MulAut.mul_apply]
      rw [← map_inv, primeFormConjHom, MonoidHom.coe_mk, OneHom.coe_mk, primeFormConjAut_mk,
        primeFormFieldHom, MonoidHom.coe_mk, OneHom.coe_mk, primeFormFieldAut_mk,
        primeFormConjAut_mk]
      rfl
    rw [hθeq]
    have h2 : ((θF g : gamma5 h) : GL (Fin 5) K) = (M : GL (Fin 5) K) *
        glAut φ (((M⁻¹ : unit5 h) : GL (Fin 5) K) * (g : GL (Fin 5) K) *
          ((M⁻¹ : unit5 h) : GL (Fin 5) K)⁻¹) * (M : GL (Fin 5) K)⁻¹ := rfl
    rw [h2]
    simp only [Subgroup.coe_inv, inv_inv]

end Classify

end CFSG.RankThree.PartOne
