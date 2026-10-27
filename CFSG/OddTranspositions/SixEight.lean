module

public import CFSG.OddTranspositions.HypothesisC

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem inter_D_subset_perp (hC : HypothesisC D) {X : Subgroup G}
    (hX : X = Subgroup.closure ((X : Set G) ∩ D))
    (hdX : hC.d ∈ X)
    (hEX : hC.E ⊆ (X : Set G))
    (hproper : X ≠ ⊤) :
    (X : Set G) ∩ D ⊆ hC.alpha ∪ DalphaStar D hC.alpha := by
  classical
  have hαF : hC.alpha = normSet D hC.E \ hC.E := hC.alpha_eq_normSet_diff
  set F : Set G := normSet D hC.E \ hC.E with hF
  have hαFeq : hC.alpha = F := by rw [hαF, hF]
  rw [hC.DalphaStar_alpha, hαFeq]
  have hblock : IsBlock D hC.alpha := hC.isBlock_alpha
  have hN : IsNormalSet D := hC.setup.normal
  have hodd : IsOddTransp D := hC.setup.oddT
  have hdα : hC.d ∈ hC.alpha := hC.d_mem_alpha
  have hdF : hC.d ∈ F := hαFeq ▸ hdα
  have hHle : Halpha D hC.alpha ≤ X := by
    rw [Halpha, Subgroup.closure_le]
    intro x hx
    rw [hC.DalphaStar_alpha] at hx
    exact hEX hx
  set Δ : Set G := (X : Set G) ∩ D with hΔ
  have hΔD : Δ ⊆ D := by
    rw [hΔ]
    exact Set.inter_subset_right
  have hXΔ : Subgroup.closure Δ = X := hX.symm
  suffices hmain : Δ ⊆ F ∪ hC.E by
    exact hmain
  by_cases htr : ∀ a ∈ Δ, ∀ b ∈ Δ, ∃ x ∈ X, x * a * x⁻¹ = b
  ·
    exfalso
    have hdΔ : hC.d ∈ Δ := by
      rw [hΔ]
      exact ⟨hdX, hC.hd⟩
    have hαX : hC.alpha ⊆ (X : Set G) := by
      intro a ha
      obtain ⟨e₀, he₀⟩ := OddLocal.nonempty hC.hE
      have he₀D : e₀ ∈ D := (OddLocal.subset_commSet hN hC.hE he₀).1
      have he₀Δ : e₀ ∈ Δ := by
        rw [hΔ]
        exact ⟨hEX he₀, he₀D⟩
      obtain ⟨x, hxX, hxd⟩ := htr hC.d hdΔ e₀ he₀Δ
      have hB : e₀ ∈ (fun y => x * y * x⁻¹) '' hC.alpha := ⟨hC.d, hdα, hxd⟩
      have hne : (fun y => x * y * x⁻¹) '' hC.alpha ≠ hC.alpha := by
        intro himg
        have he₀α : e₀ ∈ hC.alpha := himg ▸ hB
        have he₀' : e₀ ∈ DalphaStar D hC.alpha := by
          rw [hC.DalphaStar_alpha]
          exact he₀
        obtain ⟨β, hβ, he₀β⟩ := mem_DalphaStar_iff.mp he₀'
        have hβclass : β ∈ blockClass hC.alpha := (mem_Dalpha_iff.mp hβ).1
        have hβα : β = hC.alpha :=
          eq_of_mem_of_mem_blockClass hblock hβclass (mem_blockClass_self hC.alpha)
            ⟨e₀, he₀β, he₀α⟩
        exact (mem_Dalpha_iff.mp hβ).2.2.1 hβα
      have hcommBlocks : ∀ p ∈ hC.alpha,
          ∀ q ∈ (fun y => x * y * x⁻¹) '' hC.alpha, Commute p q :=
        commute_block_of_mem_apply hN hodd hblock hne (A := hC.d) hdα (B := e₀) hB
          (OddLocal.subset_commSet hN hC.hE he₀).2.1.symm
      have hDα : (fun y => x * y * x⁻¹) '' hC.alpha ∈ Dalpha D hC.alpha := by
        refine ⟨mem_blockClass_iff.mpr ⟨x, rfl⟩, ?_, hne, hcommBlocks⟩
        rintro y ⟨z, hz, rfl⟩
        exact hN x z (hblock.subset hz)
      have hsubE : (fun y => x * y * x⁻¹) '' hC.alpha ⊆ hC.E := by
        rw [← hC.DalphaStar_alpha]
        exact subset_DalphaStar hDα
      have haX : x * a * x⁻¹ ∈ (X : Set G) := hEX (hsubE ⟨a, ha, rfl⟩)
      have hmem : a = x⁻¹ * (x * a * x⁻¹) * x := by group
      rw [hmem]
      exact X.mul_mem (X.mul_mem (X.inv_mem hxX) haX) hxX
    have hCd : ∀ c ∈ D, Commute c hC.d → c ∈ Δ := by
      intro c hcD hcd
      by_cases hcα : c ∈ hC.alpha
      · exact ⟨hαX hcα, hcD⟩
      · have hcE : c ∈ hC.E := by
          by_cases hcd' : c = hC.d
          · exact absurd (hcd' ▸ hdα) hcα
          · obtain ⟨β, hβclass, hcβ⟩ :=
              exists_mem_blockClass_of_mem hC.setup.isClass hblock hcD
            have hβα : β ≠ hC.alpha := by
              intro h
              exact hcα (h ▸ hcβ)
            obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hβclass
            have hDα : (fun y => g * y * g⁻¹) '' hC.alpha ∈ Dalpha D hC.alpha := by
              refine ⟨mem_blockClass_iff.mpr ⟨g, rfl⟩, ?_, hβα, ?_⟩
              · rintro y ⟨z, hz, rfl⟩
                exact hN g z (hblock.subset hz)
              · exact commute_block_of_mem_apply hN hodd hblock hβα (A := hC.d) hdα
                  (B := c) hcβ hcd.symm
            have hmem : c ∈ DalphaStar D hC.alpha :=
              mem_DalphaStar_iff.mpr ⟨_, hDα, hcβ⟩
            rwa [hC.DalphaStar_alpha] at hmem
        exact ⟨hEX hcE, hcD⟩
    have hCa : ∀ a ∈ Δ, ∀ c ∈ D, Commute c a → c ∈ Δ := by
      intro a ha c hcD hca
      obtain ⟨x, hxX, rfl⟩ := htr hC.d hdΔ a ha
      have hconj : Commute (x⁻¹ * c * x) hC.d := by
        have h := hca.conj x⁻¹
        simpa [mul_assoc] using h
      have hmem : x⁻¹ * c * x ∈ Δ :=
        hCd _ (by simpa using hN x⁻¹ c hcD) hconj
      have hc : c = x * (x⁻¹ * c * x) * x⁻¹ := by group
      rw [hc]
      exact ⟨X.mul_mem (X.mul_mem hxX hmem.1) (X.inv_mem hxX),
        by simpa using hN x _ hmem.2⟩
    have hDΔ : D ⊆ Δ := by
      intro c hcD
      by_contra hcΔ
      have hreach : Reach D hC.d c := reach_of_not_disconnected hC.conn hC.hd hcD
      exact hcΔ (mem_of_reach (S := Δ)
        (fun a ha b hb hab => hCa a ha b hb hab.symm) hdΔ hreach)
    apply hproper
    rw [hX]
    have hInter : Δ = D := Set.Subset.antisymm hΔD hDΔ
    rw [hInter]
    exact hC.setup.gen
  ·
    obtain ⟨e₀, he₀⟩ := OddLocal.nonempty hC.hE
    have he₀D : e₀ ∈ D := (OddLocal.subset_commSet hN hC.hE he₀).1
    have he₀Δ : e₀ ∈ Δ := by
      rw [hΔ]
      exact ⟨hEX he₀, he₀D⟩
    set Δ₁ : Set G := {y | ∃ x ∈ X, y = x * e₀ * x⁻¹} with hΔ₁
    set Δ₂ : Set G := Δ \ Δ₁ with hΔ₂
    have hΔ₁Δ : Δ₁ ⊆ Δ := by
      intro y hy
      rw [hΔ₁] at hy
      obtain ⟨x, hxX, rfl⟩ := hy
      rw [hΔ]
      exact ⟨X.mul_mem (X.mul_mem hxX he₀Δ.1) (X.inv_mem hxX), hN x e₀ he₀D⟩
    have hΔ₂Δ : Δ₂ ⊆ Δ := by
      rw [hΔ₂]
      exact Set.sdiff_subset
    have hEΔ₁ : hC.E ⊆ Δ₁ := by
      intro e he
      have he₀' : e₀ ∈ DalphaStar D hC.alpha := by
        rw [hC.DalphaStar_alpha]
        exact he₀
      have he' : e ∈ DalphaStar D hC.alpha := by
        rw [hC.DalphaStar_alpha]
        exact he
      obtain ⟨h, hh, hhe⟩ := hC.Halpha_transitive e₀ he₀' e he'
      rw [hΔ₁]
      exact ⟨h, hHle hh, hhe.symm⟩
    have hΔ₂ne : Δ₂.Nonempty := by
      by_contra hne
      have hempty : Δ₂ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      apply htr
      intro a ha b hb
      have ha₁ : a ∈ Δ₁ := by
        by_contra h
        have ha₂ : a ∈ Δ₂ := ⟨ha, h⟩
        rw [hempty] at ha₂
        exact (Set.notMem_empty a) ha₂
      have hb₁ : b ∈ Δ₁ := by
        by_contra h
        have hb₂ : b ∈ Δ₂ := ⟨hb, h⟩
        rw [hempty] at hb₂
        exact (Set.notMem_empty b) hb₂
      rw [hΔ₁] at ha₁ hb₁
      obtain ⟨x, hxX, rfl⟩ := ha₁
      obtain ⟨y, hyX, rfl⟩ := hb₁
      exact ⟨y * x⁻¹, X.mul_mem hyX (X.inv_mem hxX), by group⟩
    have hP : ∀ g ∈ Subgroup.closure Δ, ∀ x ∈ Δ₁, g * x * g⁻¹ ∈ Δ₁ := by
      intro g hg x hx
      have hgX : g ∈ X := hXΔ ▸ hg
      rw [hΔ₁] at hx ⊢
      obtain ⟨y, hyX, rfl⟩ := hx
      exact ⟨g * y, X.mul_mem hgX hyX, by group⟩
    have hQ : ∀ g ∈ Subgroup.closure Δ, ∀ x ∈ Δ₂, g * x * g⁻¹ ∈ Δ₂ := by
      intro g hg x hx
      have hgX : g ∈ X := hXΔ ▸ hg
      have hx' : x ∈ Δ \ Δ₁ := hx
      refine ⟨?_, ?_⟩
      · rw [hΔ]
        exact ⟨X.mul_mem (X.mul_mem hgX hx'.1.1) (X.inv_mem hgX), hN g x hx'.1.2⟩
      · intro hmem
        rw [hΔ₁] at hmem
        obtain ⟨y, hyX, hxy⟩ := hmem
        exact hx'.2 ⟨g⁻¹ * y, X.mul_mem (X.inv_mem hgX) hyX, by
          have hxeq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
          rw [hxeq, hxy]
          group⟩
    have hdisj : Disjoint Δ₁ Δ₂ := by
      rw [Set.disjoint_left]
      intro x hx₁ hx₂
      exact hx₂.2 hx₁
    have hcomm := commute_of_isOddTransp_invariant_partition
      (hodd.mono (fun x hx => hΔD hx)) hΔ₁Δ hΔ₂Δ hP hQ hdisj
    have hΔ₂F : Δ₂ ⊆ F := by
      intro v hv
      have hv' : v ∈ Δ \ Δ₁ := hv
      have hvD : v ∈ D := hΔD hv'.1
      have hvE : v ∉ hC.E := fun hve => hv'.2 (hEΔ₁ hve)
      have hcommE : ∀ e ∈ hC.E, Commute v e :=
        fun e he => (hcomm e (hEΔ₁ he) v hv).symm
      have hnorm : v ∈ normSet D hC.E :=
        ⟨hvD, OddLocal.mem_normalizer_of_commute hcommE⟩
      rw [hF]
      exact ⟨hnorm, hvE⟩
    have hΔ₁F : ∀ x ∈ Δ₁, x ∉ hC.E → x ∈ F := by
      intro x hx hxE
      have hxD : x ∈ D := hΔD (hΔ₁Δ hx)
      obtain ⟨β, hβclass, hxβ⟩ :=
        exists_mem_blockClass_of_mem hC.setup.isClass hblock hxD
      obtain ⟨v, hv⟩ := hΔ₂ne
      have hxα : x ∈ hC.alpha := by
        by_cases hβα : β = hC.alpha
        · rw [hβα] at hxβ
          exact hxβ
        · obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hβclass
          have hDα : (fun y => g * y * g⁻¹) '' hC.alpha ∈ Dalpha D hC.alpha := by
            refine ⟨mem_blockClass_iff.mpr ⟨g, rfl⟩, ?_, hβα, ?_⟩
            · rintro y ⟨z, hz, rfl⟩
              exact hN g z (hblock.subset hz)
            · exact commute_block_of_mem_apply hN hodd hblock hβα (A := v)
                (hαFeq.symm ▸ hΔ₂F hv) (B := x) hxβ (hcomm x hx v hv).symm
          have hmemE : x ∈ DalphaStar D hC.alpha :=
            mem_DalphaStar_iff.mpr ⟨_, hDα, hxβ⟩
          rw [hC.DalphaStar_alpha] at hmemE
          exact absurd hmemE hxE
      rw [hαFeq] at hxα
      exact hxα
    have hΔnorm : ∀ x ∈ Δ, x ∈ Subgroup.normalizer hC.E := by
      intro x hx
      by_cases hxE : x ∈ hC.E
      · exact OddLocal.closure_commSet_le_normalizer hC.hE
          (Subgroup.subset_closure (OddLocal.subset_commSet hN hC.hE hxE))
      · have hxF : x ∈ F := by
          by_cases hx₁ : x ∈ Δ₁
          · exact hΔ₁F x hx₁ hxE
          · exact hΔ₂F ⟨hx, hx₁⟩
        rw [hF] at hxF
        exact hxF.1.2
    have hXnorm : X ≤ Subgroup.normalizer hC.E := by
      rw [← hXΔ, Subgroup.closure_le]
      exact hΔnorm
    have hΔ₁E : Δ₁ ⊆ hC.E := by
      intro y hy
      rw [hΔ₁] at hy
      obtain ⟨x, hxX, rfl⟩ := hy
      exact (Subgroup.mem_set_normalizer_iff.mp (hXnorm hxX) e₀).mp he₀
    intro y hy
    by_cases hy₁ : y ∈ Δ₁
    · right
      exact hΔ₁E hy₁
    · left
      exact hΔ₂F ⟨hy, hy₁⟩

end CFSG.OddTranspositions
