module

public import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentLift
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.RankThree.PartOne.Q1327R.Aut9
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDual

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryRegular
open scoped commutatorElement

variable {ℓ f : ℕ} {K : Type} [Field K]

abbrev idGram (K : Type) [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem isPrimeFormGram_idGram {n : ℕ} : IsPrimeFormGram (1 : GL (Fin n) K) :=
  CFSG.RankThree.PartOne.Q1327R.isPG1

section Scalars

variable (h : UnitaryFieldData ℓ f K) (n : ℕ)

@[expose] def idScalarKernel : Subgroup (primeFormUnitary h (idGram K n)) where
  carrier := {A | ∃ c : Kˣ, c ^ (ℓ ^ f + 1) = 1 ∧
    (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c}
  one_mem' := ⟨1, one_pow _, by simp⟩
  mul_mem' := by
    rintro A A' ⟨c, hc, hA⟩ ⟨c', hc', hA'⟩
    refine ⟨c * c', by rw [mul_pow, hc, hc', one_mul], ?_⟩
    rw [Subgroup.coe_mul, hA, hA', map_mul]
  inv_mem' := by
    rintro A ⟨c, hc, hA⟩
    refine ⟨c⁻¹, by rw [inv_pow, hc, inv_one], ?_⟩
    rw [Subgroup.coe_inv, hA, map_inv]

variable {h n} in
theorem mem_idScalarKernel {A : primeFormUnitary h (idGram K n)} :
    A ∈ idScalarKernel h n ↔ ∃ c : Kˣ, c ^ (ℓ ^ f + 1) = 1 ∧
      (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := Iff.rfl

instance idScalarKernel_normal : (idScalarKernel h n).Normal where
  conj_mem := by
    rintro A ⟨c, hc, hA⟩ g
    refine ⟨c, hc, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hA]
    rw [(commute_scalar c (g : GL (Fin n) K)).eq, mul_inv_cancel_right]

theorem pow_succ_eq_one_iff_norm (c : Kˣ) : c ^ (ℓ ^ f + 1) = 1 ↔ h.norm (c : K) = 1 := by
  rw [h.norm_eq_pow, ← Units.val_pow_eq_pow_val, Units.val_eq_one]

end Scalars

section Bridge

variable (h : UnitaryFieldData ℓ f K) (n : ℕ)

noncomputable abbrev idForm : (Fin n → K) →ₛₗ[h.bar] (Fin n → K) →ₗ[K] K :=
  gramForm h (idGram K n)

theorem idForm_isSymm : (idForm h n).IsSymm := by
  refine gramForm_isSymm h ?_
  simp [idGram]

theorem idForm_separatingLeft : (idForm h n).SeparatingLeft := by
  refine gramForm_separatingLeft h ?_
  simp [idGram]

variable {h n}

theorem toLin_mem_sesqUnitaryGroup_iff (g : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.toLin g ∈ sesqUnitaryGroup (idForm h n) ↔
      g ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_sesqUnitaryGroup, mem_primeFormUnitary, ← gramForm_isometry_iff]
  simp only [Matrix.GeneralLinearGroup.coe_toLin]
  rfl

variable (h n)

@[expose] noncomputable def toLinU :
    primeFormUnitary h (idGram K n) →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
    LinearMap.GeneralLinearGroup K (Fin n → K)).toMonoidHom.comp
    (primeFormUnitary h (idGram K n)).subtype

variable {h n}

theorem toLinU_injective : Function.Injective (toLinU h n) :=
  fun _ _ e => Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective e)

theorem toLinU_mem (A : primeFormUnitary h (idGram K n)) :
    toLinU h n A ∈ sesqUnitaryGroup (idForm h n) :=
  (toLin_mem_sesqUnitaryGroup_iff _).mpr A.2

theorem exists_toLinU {g : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hg : g ∈ sesqUnitaryGroup (idForm h n)) : ∃ A, toLinU h n A = g := by
  refine ⟨⟨Matrix.GeneralLinearGroup.toLin.symm g, ?_⟩, ?_⟩
  · rw [← toLin_mem_sesqUnitaryGroup_iff, MulEquiv.apply_symm_apply]
    exact hg
  · exact MulEquiv.apply_symm_apply (Matrix.GeneralLinearGroup.toLin : GL (Fin n) K ≃*
      LinearMap.GeneralLinearGroup K (Fin n → K)) g

theorem toLinU_apply (A : primeFormUnitary h (idGram K n)) :
    toLinU h n A = Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) := rfl

end Bridge

section Realization

variable {h : UnitaryFieldData ℓ f K} {n : ℕ}

theorem not_three_two (hq : 3 < ℓ ^ f) : ¬(n = 3 ∧ ℓ ^ f = 2) := by
  rintro ⟨-, h2⟩
  omega

theorem ringAut_commute (h : UnitaryFieldData ℓ f K) (a b : K ≃+* K) : Commute a b := by
  have := h.finite
  obtain ⟨-, hcyc⟩ := card_ringAut_and_isCyclic h.prime K h.card
  let _ : CommGroup (RingAut K) := hcyc.commGroup
  exact mul_comm a b

theorem primeFormConjHom_eq_one_iff (hn : 3 ≤ n) (hq : 3 < ℓ ^ f)
    (A : primeFormUnitary h (idGram K n)) :
    primeFormConjHom h (idGram K n) A = 1 ↔ A ∈ idScalarKernel h n := by
  have key := (unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_idGram (K := K) (n := n)) hn (not_three_two hq)).2.2.1 ⟨A, 1⟩
  rw [primeFormPsi_apply, map_one, mul_one] at key
  rw [key]
  constructor
  · rintro ⟨-, c, hc, hA⟩
    exact ⟨c, (pow_succ_eq_one_iff_norm h c).mpr hc, hA⟩
  · rintro ⟨c, hc, hA⟩
    exact ⟨rfl, c, (pow_succ_eq_one_iff_norm h c).mp hc, hA⟩

theorem surjective_primeFormPsi (hn : 3 ≤ n) (hq : 3 < ℓ ^ f) :
    Function.Surjective (primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n))) :=
  (unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_idGram (K := K) (n := n))
    hn (not_three_two hq)).2.1

theorem primeFormPsi_eq_one_iff' (hn : 3 ≤ n) (hq : 3 < ℓ ^ f)
    (g : primeFormUnitary h (idGram K n) ⋊[primeFormFieldU h
      (isPrimeFormGram_idGram (K := K) (n := n))] (K ≃+* K)) :
    primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) g = 1 ↔
      g.right = RingEquiv.refl K ∧ g.left ∈ idScalarKernel h n := by
  have key := (unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_idGram (K := K) (n := n)) hn (not_three_two hq)).2.2.1 g
  rw [key]
  constructor
  · rintro ⟨hr, c, hc, hA⟩
    exact ⟨hr, c, (pow_succ_eq_one_iff_norm h c).mpr hc, hA⟩
  · rintro ⟨hr, c, hc, hA⟩
    exact ⟨hr, c, (pow_succ_eq_one_iff_norm h c).mp hc, hA⟩

theorem primeFormD_normal (hn : 3 ≤ n) (hq : 3 < ℓ ^ f) :
    (primeFormD h (idGram K n)).Normal :=
  (unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_idGram (K := K) (n := n))
    hn (not_three_two hq)).2.2.2.2.2.2.2.2.1

theorem commutator_mem_primeFormD (hn : 3 ≤ n) (hq : 3 < ℓ ^ f)
    (α β : MulAut (primeFormP h (idGram K n))) : ⁅α, β⁆ ∈ primeFormD h (idGram K n) := by
  have hker := (unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_idGram (K := K) (n := n)) hn (not_three_two hq)).2.2.2.2.2.2.2.1
  rw [← hker, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_commute]
  exact ringAut_commute h _ _

theorem mem_inner_iff (α : MulAut (primeFormP h (idGram K n))) :
    α ∈ (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range ↔
      ∃ s : gramSU h (idGram K n), α = primeFormConjHom h (idGram K n) ⟨s, s.2.1⟩ :=
  mem_inner_primeFormP h (idGram K n) α

theorem finite_primeFormP : Finite (primeFormP h (idGram K n)) := by
  have := h.finite
  infer_instance

theorem conj_injective (hn : 3 ≤ n) (hq : 3 < ℓ ^ f) :
    Function.Injective (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))) :=
  conj_injective_primeFormP h (isPrimeFormGram_idGram (K := K) (n := n)) hn (not_three_two hq)

end Realization

section Lift

variable {h : UnitaryFieldData ℓ f K} {n p : ℕ}

theorem scalar_eq_one_iff (hn : 1 ≤ n) {c : Kˣ} :
    (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) = 1 ↔ c = 1 := by
  constructor
  · intro hc
    have := congrFun (congrFun (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
      hc) ⟨0, hn⟩) ⟨0, hn⟩
    apply Units.ext
    simpa using this
  · rintro rfl
    exact map_one _

theorem eq_of_mk_eq_of_pow_eq_one_of_noTorsion
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1) (hn : 1 ≤ n)
    {g₁ g₂ : gramSU h (idGram K n)} (hg₁ : g₁ ^ p = 1) (hg₂ : g₂ ^ p = 1)
    (hπ : (g₁ : primeFormP h (idGram K n)) = (g₂ : primeFormP h (idGram K n))) : g₁ = g₂ := by
  have hz : g₁⁻¹ * g₂ ∈ normOneScalars h (gramSU h (idGram K n)) n := QuotientGroup.eq.mp hπ
  have hcen : g₁⁻¹ * g₂ ∈ Subgroup.center (gramSU h (idGram K n)) :=
    normOneScalars_le_center h _ n hz
  obtain ⟨c, hcN, hcn, hc⟩ := hz
  have hg₂' : g₂ = g₁ * (g₁⁻¹ * g₂) := by simp
  have hcomm : Commute g₁ (g₁⁻¹ * g₂) := Subgroup.mem_center_iff.mp hcen g₁
  have hzp : (g₁⁻¹ * g₂) ^ p = 1 := by
    have := hg₂
    rw [hg₂', hcomm.mul_pow, hg₁, one_mul] at this
    exact this
  have hmat : (((g₁⁻¹ * g₂) ^ p : gramSU h (idGram K n)) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) (c ^ p) := by
    rw [Subgroup.coe_pow, hc, ← map_pow]
  have hc1 : c ^ p = 1 := by
    rw [hzp, Subgroup.coe_one] at hmat
    exact (scalar_eq_one_iff hn).mp hmat.symm
  have hc0 : c = 1 := hZp c hcN hcn hc1
  have hz1 : g₁⁻¹ * g₂ = 1 := by
    apply Subtype.ext
    rw [hc, hc0, map_one, Subgroup.coe_one]
  rw [hg₂', hz1, mul_one]

variable (h) in
noncomputable def scalarNormOne (n : ℕ) : Subgroup Kˣ :=
  (Units.map h.normHom).ker ⊓ (powMonoidHom n : Kˣ →* Kˣ).ker

theorem mem_scalarNormOne {c : Kˣ} :
    c ∈ scalarNormOne h n ↔ h.norm (c : K) = 1 ∧ c ^ n = 1 := by
  rw [scalarNormOne, Subgroup.mem_inf, h.mem_ker_normUnits, MonoidHom.mem_ker]
  rfl

theorem exists_pow_eq_of_noTorsion
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1) {c₀ : Kˣ}
    (hN : h.norm (c₀ : K) = 1) (hn : c₀ ^ n = 1) :
    ∃ c : Kˣ, h.norm (c : K) = 1 ∧ c ^ n = 1 ∧ c ^ p = c₀ := by
  have := h.finite
  have : Finite (scalarNormOne h n) := inferInstance
  let φ : scalarNormOne h n →* scalarNormOne h n := powMonoidHom p
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hs' : (s : Kˣ) ^ p = 1 := congrArg Subtype.val hs
    obtain ⟨hs1, hs2⟩ := mem_scalarNormOne.mp s.2
    exact Subtype.ext (hZp s hs1 hs2 hs')
  obtain ⟨s, hs⟩ := Finite.injective_iff_surjective.mp hinj ⟨c₀, mem_scalarNormOne.mpr ⟨hN, hn⟩⟩
  obtain ⟨hs1, hs2⟩ := mem_scalarNormOne.mp s.2
  exact ⟨s, hs1, hs2, congrArg Subtype.val hs⟩

end Lift

section Lift2

variable {h : UnitaryFieldData ℓ f K} {n p : ℕ}

theorem scalar_mem_gramSU (hn : 1 ≤ n) {c : Kˣ} (hN : h.norm (c : K) = 1) (hcn : c ^ n = 1) :
    (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) ∈ gramSU h (idGram K n) := by
  have := scalar_mem_unitarySU h hn hN hcn
  rw [unitarySU_eq_gramSU h n] at this
  exact this

theorem exists_lift_of_orderOf (hn : 3 ≤ n) (hq : 3 < ℓ ^ f) (hp : p.Prime)
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1)
    {t : MulAut (primeFormP h (idGram K n))}
    (ht : t ∈ (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range) (htp : orderOf t = p) :
    ∃ x : gramSU h (idGram K n), x ^ p = 1 ∧ orderOf x = p ∧
      MulAut.conj (x : primeFormP h (idGram K n)) = t := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, rfl⟩ := ht
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hord : orderOf (g : primeFormP h (idGram K n)) = p :=
    (orderOf_injective _ (conj_injective hn hq) (g : primeFormP h (idGram K n))).symm.trans htp
  have hgp : (g : primeFormP h (idGram K n)) ^ p = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hg : g ^ p ∈ normOneScalars h (gramSU h (idGram K n)) n :=
    (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact hgp)
  obtain ⟨c₀, hc₀N, hc₀n, hc₀⟩ := hg
  obtain ⟨c₁, hc₁N, hc₁n, hc₁p⟩ := exists_pow_eq_of_noTorsion hZp
    (c₀ := c₀⁻¹) (by rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hc₀N, inv_one])
    (by rw [inv_pow, hc₀n, inv_one])
  let z : gramSU h (idGram K n) := ⟨GeneralLinearGroup.scalar (Fin n) c₁,
    scalar_mem_gramSU (by omega) hc₁N hc₁n⟩
  have hz : z ∈ normOneScalars h (gramSU h (idGram K n)) n := ⟨c₁, hc₁N, hc₁n, rfl⟩
  have hzc : Commute g z := Subgroup.mem_center_iff.mp (normOneScalars_le_center h _ n hz) g
  have hgp' : ((g : GL (Fin n) K)) ^ p = GeneralLinearGroup.scalar (Fin n) c₀ := by
    rw [← Subgroup.coe_pow]
    exact hc₀
  have hxp : (g * z) ^ p = 1 := by
    rw [hzc.mul_pow]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hgp']
    change GeneralLinearGroup.scalar (Fin n) c₀ *
      (GeneralLinearGroup.scalar (Fin n) c₁) ^ p = 1
    rw [← map_pow, hc₁p, ← map_mul, mul_inv_cancel, map_one]
  have hπ : ((g * z : gramSU h (idGram K n)) : primeFormP h (idGram K n)) =
      (g : primeFormP h (idGram K n)) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
  have hne : g * z ≠ 1 := by
    intro h1
    rw [h1] at hπ
    have : (g : primeFormP h (idGram K n)) = 1 := hπ.symm
    rw [this, orderOf_one] at hord
    exact hp.one_lt.ne hord
  exact ⟨g * z, hxp, orderOf_eq_prime hxp hne, by rw [hπ]⟩

end Lift2

end CFSG.RankThree.PartOne.KCUnitaryModel
