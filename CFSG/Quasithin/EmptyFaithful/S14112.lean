module

public import CFSG.Quasithin.EmptyFaithful.Skeleton
public import CFSG.Quasithin.EmptyFaithful.S141
public import CFSG.Quasithin.EmptyFaithful.S1412

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma14111Concl (T Mc C₂ : Subgroup G) : Prop :=
  C₂ ≠ ⊥ ∧ C₂ ≤ baum T ∧ (C₂.subgroupOf (baum T)).Characteristic ∧
    ∀ M : Subgroup G, InM T M →
      (∀ m ∈ M, ∃ c ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G),
        ∃ n ∈ M ⊓ Subgroup.normalizer (C₂ : Set G), m = c * n) ∨
      (M = Mc ∧ 2 < Nat.card (quasithinOmegaOneCenter T))

@[expose] def StageLemma14111 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G), quasithinQTFE14Cat G T Mc →
    ∃ C₂ : Subgroup G, Lemma14111Concl T Mc C₂

omit [Finite G] in
theorem ordLE_of_factorization {T M M' C₂ : Subgroup G}
    (hfac : ∀ m ∈ M, ∃ c ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G),
      ∃ n ∈ M ⊓ Subgroup.normalizer (C₂ : Set G), m = c * n)
    (hN : Subgroup.normalizer (C₂ : Set G) ≤ M') : OrdLE T M M' := by
  intro m hm
  obtain ⟨c, hc, n, hn, rfl⟩ := hfac m hm
  refine ⟨n, ⟨hn.1, hN hn.2⟩, n⁻¹ * c * n, ⟨?_, ?_⟩, by group⟩
  · exact M.mul_mem (M.mul_mem (M.inv_mem hn.1) hc.1) hn.1
  · have hnV : n ∈ Subgroup.normalizer (VZ T M : Set G) :=
      le_normalizer_conjClosure _ M hn.1
    have hcen : c ∈ Subgroup.centralizer (VZ T M : Set G) := hc.2
    show n⁻¹ * c * n ∈ Subgroup.centralizer (VZ T M : Set G)
    rw [Subgroup.mem_centralizer_iff] at hcen ⊢
    intro v hv
    have hv' : n * v * n⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hnV v).mp hv
    have h1 := hcen _ hv'
    calc v * (n⁻¹ * c * n) = n⁻¹ * ((n * v * n⁻¹) * c) * n := by group
      _ = n⁻¹ * (c * (n * v * n⁻¹)) * n := by rw [h1]
      _ = n⁻¹ * c * n * v := by group

theorem isMf_of_lemma14111Concl {T Mc C₂ Mf : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hC : Lemma14111Concl T Mc C₂) (hMf : quasithinIsMaxTwoLocal Mf)
    (hNMf : Subgroup.normalizer (C₂ : Set G) ≤ Mf) : IsMf T Mc Mf := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hEven := h.qtke.2.1
  have hTN : T ≤ Subgroup.normalizer (C₂ : Set G) := by
    have h1 : T ≤ Subgroup.normalizer (baum T : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
    have h2 := normalizer_le_normalizer_of_characteristic_subgroupOf hC.2.1 hC.2.2.1
    exact h1.trans h2
  have hTMf : T ≤ Mf := hTN.trans hNMf
  have hMfT : InM T Mf := ⟨hMf, hTMf⟩
  have hv : ∀ M, InM T M → IsHv T M := fun M hM => by
    have := isHv_of_inM hEven S (hS ▸ hM)
    rwa [hS] at this
  have hA : ∀ M, InM T M → M ≠ Mc → OrdLE T M Mf := by
    intro M hM hne
    rcases hC.2.2.2 M hM with hfac | ⟨heq, -⟩
    · exact ordLE_of_factorization hfac hNMf
    · exact absurd heq hne
  have hne : Mf ≠ Mc := by
    intro heq
    apply ne_mc_of_greatest h (M := Mc) ⟨h.inM_mc, fun M₁ hM₁ => ?_⟩ rfl
    by_cases h1 : M₁ = Mc
    · rw [h1]; exact ordLE_refl T Mc
    · rw [← heq]; exact hA M₁ hM₁ h1
  refine ⟨⟨hMfT, fun M' hM' hle => ?_⟩, hne, fun M' hM' hne' => hA M' hM' hne'⟩
  by_cases hM'c : M' = Mc
  ·
    exfalso
    apply hne
    rw [hM'c] at hle
    have hle' : Mf ≤ Mc := le_of_ordLE_of_centralizer_le hle h.centralizer_le_mc
    exact (hMf.2 Mc h.mc_max.1 hle').symm
  · exact (eq_of_ordLE_antisymm (hv Mf hMfT) (hv M' hM') hle (hA M' hM' hM'c)).symm

theorem stageMfExists_of_stageLemma14111 (h11 : StageLemma14111) : StageMfExists := by
  intro G _ _ T Mc h
  obtain ⟨C₂, hC⟩ := h11 G T Mc h
  have hC₂p : IsPGroup 2 C₂ :=
    h.sylow.1.to_le (hC.2.1.trans inf_le_left)
  obtain ⟨Mf, hMf, hNMf⟩ :=
    exists_maxTwoLocal_ge (L := Subgroup.normalizer (C₂ : Set G)) ⟨C₂, hC.1, hC₂p, rfl⟩
  exact ⟨Mf, isMf_of_lemma14111Concl h hC hMf hNMf⟩

end CFSG.Quasithin
