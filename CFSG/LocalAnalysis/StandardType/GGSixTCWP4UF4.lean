module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UExc
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UComb
public import CFSG.LocalAnalysis.StandardType.GGExcFiveFour
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE

section Check

theorem f4_check_A :
    ∀ α ∈ rootFinset .F4, ∀ α' ∈ rootFinset .F4, iform α α' = 0 → iform α α = iform α' α' →
      α + α' ∈ rootFinset .F4 ∨ ∀ γ ∈ rootFinset .F4, iform γ γ ≤ iform α α := by
  decide +kernel

theorem f4_check_B :
    ∀ α ∈ rootFinset .F4, (∀ γ ∈ rootFinset .F4, iform γ γ ≤ iform α α) →
      ∀ α' ∈ rootFinset .F4, iform α α' = 0 → iform α α = iform α' α' →
        ∀ β ∈ rootFinset .F4, iform β β = iform α α → iform β α' = 0 → β ≠ α → β ≠ -α →
          iform α β = 0 := by
  decide +kernel

theorem f4_finrank_le_one
    {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} (hρR : ∀ γ, IsRoot .F4 (ρ γ) ↔ IsRoot .F4 γ)
    (hρ : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ)
    (horth : ∀ γ ∈ Ψ, ∀ δ ∈ (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) '' Ψ,
      iform γ δ = 0 ∧ ¬ IsRoot .F4 (γ + δ)) :
    Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨α, hα, β, hβ, hne1, hne2, hαβ⟩ := exists_pair_ne_of_two_le_finrank_span hΨ hlt
  have hmax : ∀ γ ∈ Ψ, ∀ δ ∈ rootFinset .F4, iform δ δ ≤ iform γ γ := by
    intro γ hγ
    obtain ⟨h0, hnr⟩ := horth γ hγ (ρ γ) ⟨γ, hγ, rfl⟩
    rcases f4_check_A γ (mem_rootFinset.2 (hΨ.isRoot γ hγ)) (ρ γ)
        (mem_rootFinset.2 ((hρR γ).2 (hΨ.isRoot γ hγ))) h0 (hρ γ γ).symm with hsum | hm
    · exact absurd (mem_rootFinset.1 hsum) hnr
    · exact hm
  have hαΦ : α ∈ rootFinset .F4 := mem_rootFinset.2 (hΨ.isRoot α hα)
  have hβΦ : β ∈ rootFinset .F4 := mem_rootFinset.2 (hΨ.isRoot β hβ)
  have hnorm : iform β β = iform α α :=
    le_antisymm (hmax α hα β hβΦ) (hmax β hβ α hαΦ)
  obtain ⟨h0, -⟩ := horth α hα (ρ α) ⟨α, hα, rfl⟩
  obtain ⟨hβ0, -⟩ := horth β hβ (ρ α) ⟨α, hα, rfl⟩
  exact hαβ (f4_check_B α hαΦ (hmax α hα) (ρ α) (mem_rootFinset.2 ((hρR α).2 (hΨ.isRoot α hα)))
    h0 (hρ α α).symm β hβΦ hnorm hβ0 hne1 hne2)

end Check

section Toral

private theorem zmod3_two_sq : ((2 : ℕ) : ZMod 3) ^ 2 = 1 := by decide

theorem utoralAt_F4_three
    {n : ℕ} (hn : 3 ^ 4 ≤ n) : UToralAt .F4 3 n := by
  intro K _ _ _ A hA hel hcard
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hAfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hAset : (A : Set (ModGL .F4 (AlgebraicClosure K))).Finite := Set.toFinite _
  obtain ⟨K₁, hK₁, -, -, hdesc⟩ := exists_descent_subgroup (τ := .F4) (ℓ := 2) (r := 3)
    (by norm_num) (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hA hAset ∅ (M := 1) le_rfl
  have : Finite K₁ := hK₁
  have : Fintype K₁ := Fintype.ofFinite K₁
  set ι := K₁.subtype with hι
  have hA₁C : A.comap (baseChangeGL ι) ≤ adjointGroup .F4 K₁ := comap_le_adjointGroup ι hdesc
  have hcomm₁ : ∀ x ∈ A.comap (baseChangeGL ι), ∀ y ∈ A.comap (baseChangeGL ι), x * y = y * x :=
    fun x hx y hy => baseChangeGL_injective ι (by
      rw [map_mul, map_mul]
      exact hel.comm (Subgroup.mem_comap.mp hx) (Subgroup.mem_comap.mp hy))
  have hpow₁ : ∀ x ∈ A.comap (baseChangeGL ι), x ^ 3 = 1 := fun x hx =>
    baseChangeGL_injective ι (by rw [map_pow, map_one]; exact hel.2 _ (Subgroup.mem_comap.mp hx))
  have hcard₁ : Nat.card (A.comap (baseChangeGL ι)) = Nat.card A := by
    have hrange : A ≤ (baseChangeGL (τ := .F4) ι).range := fun x hx => by
      obtain ⟨y, -, hy⟩ := hdesc x hx
      exact ⟨y, hy⟩
    conv_rhs => rw [← Subgroup.map_comap_eq_self hrange]
    exact (Subgroup.card_map_of_injective (baseChangeGL_injective ι)).symm
  set E := (A.comap (baseChangeGL ι)).subgroupOf (adjointGroup .F4 K₁) with hE
  have hEel : IsElemAbelian 3 E :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hcomm₁ _ a.2 _ b.2))⟩⟩,
      fun x hx => Subtype.ext ((Subgroup.coe_pow _ x 3).trans (hpow₁ _ hx))⟩
  have hEcard : Nat.card E = Nat.card A := by
    rw [← hcard₁]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁C).toEquiv
  have hord : orderOf (Nat.card K₁ : ZMod 3) = 1 ∨ orderOf (Nat.card K₁ : ZMod 3) = 2 := by
    obtain ⟨m, -, hm⟩ := FiniteField.card K₁ 2
    have hsq : (Nat.card K₁ : ZMod 3) ^ 2 = 1 := by
      rw [Nat.card_eq_fintype_card, hm, Nat.cast_pow, ← pow_mul, mul_comm, pow_mul]
      rw [zmod3_two_sq, one_pow]
    exact (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hsq)
  have hdeg : ExcMaxToral.excDegCount .F4 (orderOf (Nat.card K₁ : ZMod 3)) = 4 := by
    rcases hord with h | h <;> rw [h] <;> decide
  obtain ⟨Fr, hFr, D, hΦ, hqD, -, hmem, -⟩ :=
    ExcMaxToral.adjointMaxElemToral .F4 K₁ 3 hK₁ inferInstance (by norm_num) (by norm_num)
      (by rw [hdeg]) E hEel (by rw [hdeg, hEcard, hcard]; exact hn)
  let : Algebra K₁ (AlgebraicClosure K) := ι.toAlgebra
  let σ : AlgebraicClosure K₁ →ₐ[K₁] AlgebraicClosure K := IsAlgClosed.lift
  have hσ : σ.toRingHom.comp (algebraMap K₁ (AlgebraicClosure K₁)) = ι := by
    ext c
    exact σ.commutes c
  have hH : torusGroup .F4 (AlgebraicClosure K₁) ≤
      (torusGroup .F4 (AlgebraicClosure K)).comap (baseChangeGL σ.toRingHom) := by
    rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
    exact torusElt_mem_torusGroup i _
  refine ⟨baseChangeGL σ.toRingHom D.g0, baseChangeGL_mem_adjointGroup _ D.g0_mem, fun x hx => ?_⟩
  obtain ⟨x₁, hx₁C, rfl⟩ := hdesc x hx
  have hxE : (⟨x₁, hx₁C⟩ : ↥(adjointGroup .F4 K₁)) ∈ E := Subgroup.mem_comap.mpr hx
  have htor := (mem_twistedTorusOf.1 (hmem _ hxE)).1
  have hcalc : (baseChangeGL σ.toRingHom D.g0)⁻¹ * baseChangeGL ι x₁ *
      baseChangeGL σ.toRingHom D.g0 = baseChangeGL σ.toRingHom (D.g0⁻¹ *
        baseChangeGL (algebraMap K₁ (AlgebraicClosure K₁)) x₁ * D.g0) := by
    rw [map_mul, map_mul, map_inv, baseChangeGL_baseChangeGL, hσ]
  rw [hι] at hcalc
  rw [hcalc]
  exact hH htor

end Toral

end CFSG.StandardType.TableCRes
