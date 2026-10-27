module

public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne.CTP

section Fixed

variable {P : Type*} [Group P]

theorem fixedSubgroup_conj (d f : MulAut P) :
    fixedSubgroup (d * f * d⁻¹) = (fixedSubgroup f).map d.toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine ⟨d⁻¹ x, ?_, by simp⟩
    have h : d (f (d⁻¹ x)) = x := hx
    have h2 := congrArg (fun y => d⁻¹ y) h
    change f (d⁻¹ x) = d⁻¹ x
    simpa using h2
  · rintro ⟨y, hy, rfl⟩
    have hy' : f y = y := hy
    change d (f (d⁻¹ (d y))) = d y
    simp [hy']

theorem map_closure_union {Q : Type*} [Group Q] (f : P →* Q) (A B : Subgroup P) :
    (Subgroup.closure ((A : Set P) ∪ (B : Set P))).map f =
      Subgroup.closure ((A.map f : Set Q) ∪ (B.map f : Set Q)) := by
  rw [MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map, ← Subgroup.coe_map]

theorem fixedSubgroup_eq_of_zpowers_eq {K : Type*} [Group K] (φ : K →* MulAut P) {σ τ : K}
    (hzp : Subgroup.zpowers σ = Subgroup.zpowers τ) :
    fixedSubgroup (φ σ) = fixedSubgroup (φ τ) := by
  have key : ∀ {a b : K}, Subgroup.zpowers a = Subgroup.zpowers b →
      ∀ x, φ a x = x → φ b x = x := by
    intro a b hab x hx
    have hb : b ∈ Subgroup.zpowers a := hab ▸ Subgroup.mem_zpowers b
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hstab : Subgroup.zpowers (φ a) ≤ MulAction.stabilizer (MulAut P) x :=
      (Subgroup.zpowers_le (H := MulAction.stabilizer (MulAut P) x)).mpr hx
    have : φ (a ^ m) ∈ Subgroup.zpowers (φ a) := by
      rw [map_zpow]
      exact Subgroup.zpow_mem_zpowers _ m
    exact hstab this
  ext x
  exact ⟨fun hx => key hzp x hx, fun hx => key hzp.symm x hx⟩

end Fixed

section Fields

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])

theorem isCyclic_ringEquiv_of_card {K : Type} [Field K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) : IsCyclic (K ≃+* K) := by
  obtain ⟨σ₀, -, -, htop, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ₀, htop⟩

theorem zpowers_ringEquiv_eq_of_orderOf {K : Type} [Field K] {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {σ τ : K ≃+* K} (hσ : orderOf σ = p)
    (hτ : orderOf τ = p) : Subgroup.zpowers σ = Subgroup.zpowers τ := by
  have hcyc := isCyclic_ringEquiv_of_card hℓ hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hσ, hτ]

theorem fixedField_eq_of_orderOf {K : Type} [Field K] {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {σ τ : K ≃+* K} (hσ : orderOf σ = p) (hτ : orderOf τ = p) :
    (σ : K →+* K).eqLocusField (RingHom.id K) = (τ : K →+* K).eqLocusField (RingHom.id K) := by
  have hzp := zpowers_ringEquiv_eq_of_orderOf hℓ hf hK hσ hτ
  have key : ∀ {a b : K ≃+* K}, Subgroup.zpowers a = Subgroup.zpowers b →
      ∀ x, a x = x → b x = x := by
    intro a b hab x hx
    have hb : b ∈ Subgroup.zpowers a := hab ▸ Subgroup.mem_zpowers b
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hstab : Subgroup.zpowers a ≤ MulAction.stabilizer (K ≃+* K) x :=
      (Subgroup.zpowers_le (H := MulAction.stabilizer (K ≃+* K) x)).mpr hx
    exact hstab (Subgroup.zpow_mem_zpowers a m)
  ext x
  exact ⟨fun hx => RingHom.mem_eqLocusField.mpr
      (key hzp x (RingHom.mem_eqLocusField.mp hx)),
    fun hx => RingHom.mem_eqLocusField.mpr
      (key hzp.symm x (RingHom.mem_eqLocusField.mp hx))⟩

end Fields

section Abstract

variable {P : Type} [Group P]

theorem fieldAutData_of_standard {p : ℕ} (D : Subgroup (MulAut P)) (S : Set (MulAut P))
    (hrank : ∀ E : Subgroup (MulAut P), CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 2 →
      ∃ g : P, g ≠ 1 ∧ MulAut.conj g ∈ E)
    (hdesc : ∀ α : MulAut P, IsOuterOfOrder p α → ∃ d ∈ D, ∃ f ∈ S, α = d * f * d⁻¹)
    (hfix : ∀ f ∈ S, ∀ f' ∈ S, fixedSubgroup f = fixedSubgroup f')
    (hcenter : ∀ f ∈ S, p ∣ Nat.card (fixedSubgroup f) → ∀ x ∈ fixedSubgroup f,
      (∀ y ∈ fixedSubgroup f, x * y = y * x) → x = 1)
    (hpair : ∀ f ∈ S, ∀ d ∈ D, (fixedSubgroup f).map d.toMonoidHom ≠ fixedSubgroup f →
      Subgroup.closure ((fixedSubgroup f : Set P) ∪
        ((fixedSubgroup f).map d.toMonoidHom : Set P)) = ⊤ ∨
          ¬ p ∣ Nat.card (fixedSubgroup f)) :
    FieldAutData P p := by
  refine ⟨hrank, ?_, ?_⟩
  · intro σ hσ hdvd x hx hcomm
    obtain ⟨d, -, f, hf, rfl⟩ := hdesc σ hσ
    have hF := fixedSubgroup_conj d f
    rw [hF] at hx hcomm hdvd
    rw [Subgroup.card_map_of_injective d.injective] at hdvd
    obtain ⟨y, hy, rfl⟩ := hx
    have hy1 : y = 1 := by
      refine hcenter f hf hdvd y hy fun z hz => ?_
      have h1 := hcomm (d z) ⟨z, hz, rfl⟩
      exact d.injective (by simpa using h1)
    rw [hy1, map_one]
  · intro σ τ hσ hτ hne
    obtain ⟨d₁, hd₁, f₁, hf₁, rfl⟩ := hdesc σ hσ
    obtain ⟨d₂, hd₂, f₂, hf₂, rfl⟩ := hdesc τ hτ
    have h₁ := fixedSubgroup_conj d₁ f₁
    have h₂ := fixedSubgroup_conj d₂ f₂
    rw [← hfix f₁ hf₁ f₂ hf₂] at h₂
    rw [h₁, h₂] at hne ⊢
    set R := fixedSubgroup f₁ with hR
    have hd : d₁⁻¹ * d₂ ∈ D := D.mul_mem (D.inv_mem hd₁) hd₂
    have hne' : R.map (d₁⁻¹ * d₂).toMonoidHom ≠ R := by
      intro h
      apply hne
      have h3 : R.map d₂.toMonoidHom = (R.map (d₁⁻¹ * d₂).toMonoidHom).map d₁.toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext z
        simp
      rw [h3, h]
    rcases hpair f₁ hf₁ _ hd hne' with hg | hsmall
    · left
      have h4 := congrArg (Subgroup.map d₁.toMonoidHom) hg
      rw [map_closure_union, Subgroup.map_top_of_surjective _ d₁.surjective] at h4
      have h5 : (R.map (d₁⁻¹ * d₂).toMonoidHom).map d₁.toMonoidHom = R.map d₂.toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext z
        simp
      rw [h5] at h4
      exact h4
    · right
      rw [Subgroup.card_map_of_injective d₁.injective]
      exact hsmall

end Abstract

end CFSG.RankThree.PartOne.CTP
