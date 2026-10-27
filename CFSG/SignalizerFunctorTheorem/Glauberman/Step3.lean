module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.Sylow
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.InvariantSylow

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

theorem Setting.step3 (h : Setting p A θ) {q : ℕ} (hq : q = 2 ∨ q = 3)
    {S M₁ M₂ : Subgroup G} (hS : Maximal (signalizerPrimeCompatible p 1 q A θ) S)
    (hM₁ : Maximal (solvableSignalizerCompatible p 1 A θ) M₁)
    (hM₂ : Maximal (solvableSignalizerCompatible p 1 A θ) M₂) (h₁ : S ≤ M₁) (h₂ : S ≤ M₂) :
    M₁ = M₂ := by
  classical
  obtain ⟨r, hr, hqr, hrmem, hsupp⟩ : ∃ r : ℕ, r.Prime ∧ q ≠ r ∧ (r = 2 ∨ r = 3) ∧
      ∀ ℓ : ℕ, (ℓ = 2 ∨ ℓ = 3) → ℓ = q ∨ ℓ = r := by
    rcases hq with rfl | rfl
    · exact ⟨3, Nat.prime_three, by decide, Or.inr rfl, by rintro ℓ (rfl | rfl) <;> simp⟩
    · exact ⟨2, Nat.prime_two, by decide, Or.inl rfl, by rintro ℓ (rfl | rfl) <;> simp⟩
  have hqp : q.Prime := by
    rcases hq with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  set C := signalizerCommonFixed p 1 A θ with hC
  have hSc : signalizerCompatible p 1 A θ S := hS.prop.1
  have hCc : signalizerCompatible p 1 A θ C := compatible_commonFixed
  have key : ∀ M : Subgroup G, Maximal (solvableSignalizerCompatible p 1 A θ) M → S ≤ M →
      ∃ R : Subgroup G, IsSylowOf r R M ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
        subgroupProduct S R = (M : Set G) := by
    intro M hM hSM
    have hMc : signalizerCompatible p 1 A θ M := hM.prop.1
    have hSyl : IsSylowOf q S M := h.isSylowOf_of_maximal hqp hS hMc hSM
    have hbotA : A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)]
      exact le_top
    obtain ⟨R, -, hR, hRA⟩ := h.exists_invariant_sylow hr hMc (IsPGroup.of_bot)
      bot_le hbotA
    refine ⟨R, hR, hRA, subgroupProduct_eq_of_isSylowOf hqp hr hqr ?_ hSyl hR⟩
    intro ℓ hℓ hd
    exact hsupp ℓ (h.prime_support hMc hℓ hd)
  obtain ⟨R₁, hR₁, hR₁A, hprod₁⟩ := key M₁ hM₁ h₁
  obtain ⟨R₂, hR₂, hR₂A, hprod₂⟩ := key M₂ hM₂ h₂
  have hM₁c : signalizerCompatible p 1 A θ M₁ := hM₁.prop.1
  have hM₂c : signalizerCompatible p 1 A θ M₂ := hM₂.prop.1
  have hR₁pc : signalizerPrimeCompatible p 1 r A θ R₁ :=
    ⟨signalizer_compatible_of_le p 1 A θ hM₁c hR₁.le hR₁A, hR₁.isPGroup⟩
  have hR₂pc : signalizerPrimeCompatible p 1 r A θ R₂ :=
    ⟨signalizer_compatible_of_le p 1 A θ hM₂c hR₂.le hR₂A, hR₂.isPGroup⟩
  obtain ⟨Rh₁, hR₁le, hRh₁⟩ := Finite.exists_le_maximal
    (p := signalizerPrimeCompatible p 1 r A θ) hR₁pc
  obtain ⟨Rh₂, hR₂le, hRh₂⟩ := Finite.exists_le_maximal
    (p := signalizerPrimeCompatible p 1 r A θ) hR₂pc
  obtain ⟨c₀, hc₀⟩ := signalizer_prime_transitivity p 1 r h.prime hr
    (h.p_ne hrmem) A h.elementary h.large θ h.conditions.coprime h.conditions.normalized
    h.conditions.balanced Rh₁ Rh₂ hRh₁ hRh₂
  have hSC : IsSylowOf q (S ⊓ C) C := h.isSylowOf_inf_commonFixed hq hS
  have hRC : IsSylowOf r (Rh₁ ⊓ C) C := h.isSylowOf_inf_commonFixed hrmem hRh₁
  have hCprod : subgroupProduct (S ⊓ C) (Rh₁ ⊓ C) = (C : Set G) :=
    subgroupProduct_eq_of_isSylowOf hqp hr hqr
      (fun ℓ hℓ hd => hsupp ℓ (h.prime_support hCc hℓ hd)) hSC hRC
  have hc₀prod : c₀.val ∈ subgroupProduct (S ⊓ C) (Rh₁ ⊓ C) := by
    rw [hCprod]
    exact c₀.property
  obtain ⟨s, hs, t, ht, hst⟩ := hc₀prod
  have hsS : s ∈ S := hs.1
  have hsC : s ∈ C := hs.2
  have hconj : conjugateSubgroup s Rh₁ = Rh₂ := by
    have htfix : conjugateSubgroup t Rh₁ = Rh₁ := conjugate_subgroup_eq_of_mem t Rh₁ ht.1
    rw [← hc₀, ← hst, ← conjugate_subgroup_mul, htfix]
  set R₁' := conjugateSubgroup s R₁ with hR₁'
  have hR₁'le : R₁' ≤ Rh₂ := by
    rw [← hconj]
    exact Subgroup.map_mono hR₁le
  set V := R₁' ⊔ R₂ with hV
  have hVle : V ≤ Rh₂ := sup_le hR₁'le hR₂le
  have hsA : s ∈ Subgroup.centralizer (A : Set G) := commonFixed_le_centralizer hsC
  have hR₁'A : A ≤ Subgroup.normalizer (R₁' : Set G) :=
    le_normalizer_conj_of_mem_centralizer hsA hR₁A
  have hVA : A ≤ Subgroup.normalizer (V : Set G) :=
    (le_inf hR₁'A hR₂A).trans (Subgroup.inf_normalizer_le_normalizer_sup R₁' R₂)
  have hVc : signalizerCompatible p 1 A θ V :=
    signalizer_compatible_of_le p 1 A θ hRh₂.prop.1 hVle hVA
  have hperm₁ : ∀ v ∈ R₁, ∀ s' ∈ S, ∃ s'' ∈ S, ∃ v' ∈ R₁, v * s' = s'' * v' :=
    permute_of_subgroupProduct_eq h₁ hR₁.le hprod₁
  have hperm₂ : ∀ v ∈ R₂, ∀ s' ∈ S, ∃ s'' ∈ S, ∃ v' ∈ R₂, v * s' = s'' * v' :=
    permute_of_subgroupProduct_eq h₂ hR₂.le hprod₂
  have hpermV : ∀ v ∈ V, ∀ s' ∈ S, ∃ s'' ∈ S, ∃ v' ∈ V, v * s' = s'' * v' :=
    permute_sup (permute_conj hperm₁ hsS) hperm₂
  have hSV : subgroupProduct S V = ((S ⊔ V : Subgroup G) : Set G) :=
    subgroupProduct_eq_sup_of_permute hpermV
  have hMstarc : signalizerCompatible p 1 A θ (S ⊔ V) :=
    h.compatible_sup_of_permute hSc hVc hSV
  have hMstarsolv : Group.IsSolvable (S ⊔ V : Subgroup G) :=
    isSolvable_of_prime_support hqp hr hqr
      (fun ℓ hℓ hd => hsupp ℓ (h.prime_support hMstarc hℓ hd))
  have hMstar : solvableSignalizerCompatible p 1 A θ (S ⊔ V) := ⟨hMstarc, hMstarsolv⟩
  have hM₂le : M₂ ≤ S ⊔ V := by
    intro m hm
    have hm' : m ∈ subgroupProduct S R₂ := by
      rw [hprod₂]
      exact hm
    obtain ⟨a, ha, b, hb, rfl⟩ := hm'
    exact (S ⊔ V).mul_mem (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right (Subgroup.mem_sup_right hb))
  have hM₁le : M₁ ≤ S ⊔ V :=
    (le_sup_conj_of_subgroupProduct_eq hprod₁ hsS (h₁ hsS)).trans
      (sup_le_sup_left le_sup_left S)
  exact le_antisymm (hM₁le.trans (hM₂.le_of_ge hMstar hM₂le))
    (hM₂le.trans (hM₁.le_of_ge hMstar hM₁le))

end CFSG.SignalizerFunctorTheorem.Glauberman
