module

public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

theorem fixes_conj_of_fixes {X : Type*} [Group X] {α β γ φ : MulAut X} (hα : α = γ * φ * γ⁻¹)
    (hβ : ∀ z, α z = z → β z = z) : ∀ z, φ z = z → (γ⁻¹ * β * γ) z = z := by
  intro z hz
  have h1 : α (γ z) = γ z := by
    rw [hα, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hz]
  rw [MulAut.mul_apply, MulAut.mul_apply, hβ _ h1, MulAut.inv_apply, MulEquiv.symm_apply_apply]

theorem mem_zpowers_of_conj {X : Type*} [Group X] {α β γ φ : MulAut X}
    (hα : α = γ * φ * γ⁻¹) (h : γ⁻¹ * β * γ ∈ Subgroup.zpowers φ) :
    β ∈ Subgroup.zpowers α := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [hα, conj_zpow, hk]
  group

theorem exists_pow_eq_of_mem_zpowers {M : Type*} [Group M] {α β : M} (h3 : α ^ 3 = 1)
    (h : β ∈ Subgroup.zpowers α) : ∃ i : ℕ, β = α ^ i := by
  have hfin : IsOfFinOrder α := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, h3⟩
  rw [← hfin.mem_powers_iff_mem_zpowers] at h
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp h
  exact ⟨i, hi.symm⟩

theorem fixes_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {α β : MulAut X}
    (hβ : ∀ z, α z = z → β z = z) :
    ∀ y, MulAut.congr e α y = y → MulAut.congr e β y = y := by
  intro y hy
  have hy' : e (α (e.symm y)) = y := hy
  change e (β (e.symm y)) = y
  rw [hβ (e.symm y) (by rw [← MulEquiv.apply_eq_iff_eq e, hy', MulEquiv.apply_symm_apply]),
    MulEquiv.apply_symm_apply]

theorem mem_zpowers_of_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {α β : MulAut X}
    (h : MulAut.congr e β ∈ Subgroup.zpowers (MulAut.congr e α)) : β ∈ Subgroup.zpowers α := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, (MulAut.congr e).injective (by rw [map_zpow, hk])⟩

theorem orderOf_eq_three_of_not_isInnerAut {X : Type*} [Group X] {α : MulAut X}
    (h3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) : orderOf α = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h3 fun h1 => hout (h1 ▸ ⟨1, map_one _⟩)

theorem mem_zpowers_of_fixes_psl2' {K : Type} [Field K] [Finite K] {α : MulAut (PSL2 K)}
    (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) {β : MulAut (PSL2 K)}
    (hβ : ∀ z, α z = z → β z = z) : β ∈ Subgroup.zpowers α := by
  have hD : α ∉ (pglAction K).range := fun hD =>
    hout (isInnerAut_of_mem_inndiag_of_pow_three hD hα3)
  obtain ⟨σ, hσ, g, hαg⟩ := linear_two_prime_order_field_descent Nat.prime_three α
    (orderOf_eq_three_of_not_isInnerAut hα3 hout) hD
  refine mem_zpowers_of_conj hαg ?_
  exact CFSG.SignalizerFunctorTheorem.CatalogBridge.mem_zpowers_of_fixes_psl2
    (by decide : Odd 3) hσ _ fun x hx => fixes_conj_of_fixes hαg hβ x hx

theorem mem_zpowers_of_fixes_projectiveSL {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 3 ≤ n) {α : MulAut (projectiveSL n K)} (hα3 : α ^ 3 = 1)
    (hD : α ∉ linearAutGroup n K) {β : MulAut (projectiveSL n K)}
    (hβ : ∀ z, α z = z → β z = z) : β ∈ Subgroup.zpowers α := by
  obtain ⟨σ, -, H, hαH⟩ := linear_order_three_field_descent hn α hα3 hD
  refine mem_zpowers_of_conj hαH ?_
  have hfix := fixes_conj_of_fixes hαH hβ
  obtain ⟨-, -, -, -, -, -, hcent⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.linear_quadratic_field_full_centralizer_rigidity
      σ hn
  rw [← hcent, Subgroup.mem_centralizer_iff]
  rintro _ ⟨B, rfl⟩
  set g : Matrix.SpecialLinearGroup (Fin n) K :=
    Matrix.SpecialLinearGroup.map
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField K σ).subtype B with hg
  have hconj : CFSG.ComponentClassification.UnbalancedCatalog.subfieldConj n σ B =
      MulAut.conj (proj n K g) := by
    rw [← conjAut_toGL]
    rfl
  have hgfix : fieldAut n K σ (proj n K g) = proj n K g := by
    rw [fieldAut_proj]
    congr 1
    ext i j
    exact CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField_coe K σ (B i j)
  set β' := (conjAut n K H)⁻¹ * β * conjAut n K H with hβ'
  have h2 : β' * MulAut.conj (proj n K g) * β'⁻¹ = MulAut.conj (proj n K g) := by
    rw [mul_mulAutConj_mul_inv, hfix _ hgfix]
  rw [hconj]
  calc MulAut.conj (proj n K g) * β' =
      (β' * MulAut.conj (proj n K g) * β'⁻¹) * β' := by rw [h2]
    _ = β' * MulAut.conj (proj n K g) := by group

theorem mem_zpowers_of_fixes_unitaryPSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (hq₀ : p ^ (f / 3) ≠ 2)
    {α : MulAut (unitaryPSU h 3)} (hα3 : α ^ 3 = 1) (hD : α ∉ (psuConj h).range)
    {β : MulAut (unitaryPSU h 3)} (hβ : ∀ z, α z = z → β z = z) : β ∈ Subgroup.zpowers α := by
  have := h.finite
  obtain ⟨σ, hσ, H, hαH⟩ := unitary_order_three_field_descent hq α hα3 hD
  refine mem_zpowers_of_conj hαH ?_
  have hfix := fixes_conj_of_fixes hαH hβ
  set β' := (psuConj h H)⁻¹ * β * psuConj h H with hβ'
  set e := psuPrimeFormEquiv h with he
  have h0 := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three
    (by norm_num) hσ
  have hbar := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h Nat.prime_three
    (by norm_num) hσ
  obtain ⟨hfs, hzp, -⟩ := CFSG.RankThree.Classical.fixingSubgroup_range_subfieldPSU h 3 h0
    hbar le_rfl (fun h' => by omega) (fun h' => hq₀ h'.2)
  have hmem : MulAut.congr e β' ∈ fixingSubgroup
      (MulAut (UnitaryHigher.primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
      ((CFSG.RankThree.Classical.subfieldPSU h h0 hbar 3).range :
        Set (UnitaryHigher.primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    rw [MulAut.smul_def]
    have hy' := CFSG.RankThree.Classical.range_subfieldPSU_le h 3 h0 hbar hy
    have hy'' : MulAut.congr e (psuField h σ) y = y := by
      rw [congr_psuField]
      exact hy'
    exact fixes_congr e hfix y hy''
  rw [hfs, hzp, ← congr_psuField] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, (MulAut.congr e).injective ?_⟩
  rw [map_zpow, hk]

end CFSG.RankThree.PartTwo.KFacts
