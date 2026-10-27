module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoComp
public import CFSG.GroupTheory.ComponentDirectProduct
public import CFSG.Goldschmidt.Steps.G310Comp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem s1611e3_normal_subgroup_prod_l3 {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hc : Subgroup.center L = ⊥) (K : Subgroup (L × L)) [K.Normal] :
    K = ⊥ ∨ K = (⊤ : Subgroup L).prod (⊥ : Subgroup L) ∨
    K = (⊥ : Subgroup L).prod (⊤ : Subgroup L) ∨ K = ⊤ := by
  have hfst : Function.Surjective (MonoidHom.fst L L) := fun a => ⟨(a, 1), rfl⟩
  have hsnd : Function.Surjective (MonoidHom.snd L L) := fun a => ⟨(1, a), rfl⟩
  have hKfst : K.map (MonoidHom.fst L L) = ⊥ ∨ K.map (MonoidHom.fst L L) = ⊤ :=
    ((inferInstance : K.Normal).map (MonoidHom.fst L L) hfst).eq_bot_or_eq_top
  have hKsnd : K.map (MonoidHom.snd L L) = ⊥ ∨ K.map (MonoidHom.snd L L) = ⊤ :=
    ((inferInstance : K.Normal).map (MonoidHom.snd L L) hsnd).eq_bot_or_eq_top
  by_cases h1 : K.map (MonoidHom.fst L L) = ⊥
  ·
    have hKle : K ≤ (⊥ : Subgroup L).prod (⊤ : Subgroup L) := by
      intro x hx
      have hx1 : (MonoidHom.fst L L) x = 1 := by
        have : (MonoidHom.fst L L) x ∈ K.map (MonoidHom.fst L L) := ⟨x, hx, rfl⟩
        rw [h1] at this
        exact Subgroup.mem_bot.mp this
      exact Subgroup.mem_prod.mpr ⟨hx1, Subgroup.mem_top _⟩
    rcases hKsnd with h2 | h2
    · left
      refine le_antisymm ?_ bot_le
      intro x hx
      have hx1 : x.1 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp (hKle hx)).1
      have hx2 : x.2 = 1 := by
        have : (MonoidHom.snd L L) x ∈ K.map (MonoidHom.snd L L) := ⟨x, hx, rfl⟩
        rw [h2] at this
        exact Subgroup.mem_bot.mp this
      exact Subgroup.mem_bot.mpr (Prod.ext hx1 hx2)
    · right; right; left
      refine le_antisymm hKle ?_
      intro x hx
      have hx1 : x.1 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hx).1
      obtain ⟨k, hk, hk2⟩ := Subgroup.mem_map.mp
        (show x.2 ∈ K.map (MonoidHom.snd L L) by rw [h2]; exact Subgroup.mem_top _)
      have hk1 : k.1 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp (hKle hk)).1
      have hkx : k = x := Prod.ext (by rw [hk1, hx1]) hk2
      rwa [hkx] at hk
  ·
    have hex : ∃ u v : L, (u, v) ∈ K ∧ u ≠ 1 := by
      by_contra hcon
      apply h1
      rw [Subgroup.eq_bot_iff_forall]
      intro b hb
      obtain ⟨k, hk, hk1⟩ := Subgroup.mem_map.mp hb
      have hk1' : k.1 = 1 := by
        by_contra hkne
        exact hcon ⟨k.1, k.2, hk, hkne⟩
      rwa [← hk1]
    obtain ⟨u, v, huv, hu⟩ := hex
    have hL1 : (⊤ : Subgroup L).prod (⊥ : Subgroup L) ≤ K := by
      intro x hx
      have hx2 : x.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hx).2
      have hx_eq : x = (x.1, (1 : L)) := Prod.ext rfl hx2
      have hmem := s16c7_inl_mem_of_normal hc K huv hu x.1
      rw [hx_eq]
      exact hmem
    rcases hKsnd with h2 | h2
    · right; left
      refine le_antisymm ?_ hL1
      intro x hx
      have hx2 : x.2 = 1 := by
        have : (MonoidHom.snd L L) x ∈ K.map (MonoidHom.snd L L) := ⟨x, hx, rfl⟩
        rw [h2] at this
        exact Subgroup.mem_bot.mp this
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, hx2⟩
    · right; right; right
      refine top_le_iff.mp ?_
      intro x _
      obtain ⟨k, hk, hk2⟩ := Subgroup.mem_map.mp
        (show x.2 ∈ K.map (MonoidHom.snd L L) by rw [h2]; exact Subgroup.mem_top _)
      have hk1K : (k.1, (1 : L)) ∈ K :=
        hL1 (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩)
      have hkeq : k = (k.1, x.2) := Prod.ext rfl hk2
      have hkx : (k.1, x.2) ∈ K := hkeq ▸ hk
      have hprod : (k.1, (1 : L))⁻¹ * (k.1, x.2) = (1, x.2) := by ext <;> simp
      have h1x : (1, x.2) ∈ K := by
        rw [← hprod]
        exact K.mul_mem (K.inv_mem hk1K) hkx
      have hx1K : (x.1, (1 : L)) ∈ K :=
        hL1 (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩)
      simpa using K.mul_mem hx1K h1x

theorem s1611e3_components_of_iso_l3_or_sq {P : Type} [Group P] [Finite P]
    {X : Subgroup P} {L : Type} [Group L] [Finite L] (hL : IsL3 L 1)
    (h : Nonempty (↥X ≃* L) ∨ Nonempty (↥X ≃* L × L)) :
    ∀ L0 : Subgroup P, CFSG.Open.IsComponentOf L0 X → IsL3 ↥L0 1 := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    haveI hXsimple : IsSimpleGroup ↥X := e.isSimpleGroup_congr.mpr (isSimpleGroup_of_isL3 hL)
    intro L0 hL0
    have hKc : CFSG.IsComponent (L0.subgroupOf X) :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hL0.1).mp
        ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open L0 X).mpr hL0)
    have hL0ne : L0 ≠ ⊥ := by
      have hq : CFSG.IsQuasisimple ↥L0 :=
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L0).mp
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open L0).mpr
            hL0.2.2))
      exact (Subgroup.nontrivial_iff_ne_bot L0).mp (CFSG.LocalCores.isQuasisimple_nontrivial hq)
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hXsimple hKc.2 with hbot | htop
    · exfalso
      apply hL0ne
      have hdisj : Disjoint L0 X := Subgroup.subgroupOf_eq_bot.mp hbot
      rw [← inf_of_le_left hL0.1]
      exact disjoint_iff.mp hdisj
    · have hLX : L0 = X := by
        refine le_antisymm hL0.1 ?_
        exact Subgroup.subgroupOf_eq_top.mp htop
      rw [hLX]
      exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL
  · obtain ⟨e⟩ := h
    classical
    obtain ⟨H₁, H₂, hH₁X, hH₂X, hsup, hinf, hL3₁, hL3₂, hnorm₁, hnorm₂, -⟩ :=
      s16c7_components (A := X) (X := L) hL e
    have hcomm₁₂ : ∀ a ∈ H₁, ∀ b ∈ H₂, Commute a b := by
      intro a ha b hb
      have hmem : ⁅a, b⁆ ∈ H₁ ⊓ H₂ := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h : b * a⁻¹ * b⁻¹ ∈ H₁ := hnorm₁ b (hH₂X hb) a⁻¹ (H₁.inv_mem ha)
          have hdef : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
            rw [commutatorElement_def]; group
          rw [hdef]
          exact H₁.mul_mem ha h
        · have h : a * b * a⁻¹ ∈ H₂ := hnorm₂ a (hH₁X ha) b hb
          have hdef : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by
            rw [commutatorElement_def]
          rw [hdef]
          exact H₂.mul_mem h (H₂.inv_mem hb)
      have hone : ⁅a, b⁆ = 1 := Subgroup.mem_bot.mp (hinf ▸ hmem)
      exact commutatorElement_eq_one_iff_commute.mp hone
    intro L0 hL0
    let 𝒜 : Finset (Subgroup P) := {H₁, H₂}
    have hAle : ∀ A ∈ 𝒜, A ≤ X := by
      intro A hA
      simp only [𝒜, Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl <;> assumption
    have hAn : ∀ A ∈ 𝒜, (A.subgroupOf X).Normal := by
      intro A hA
      simp only [𝒜, Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl
      · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hH₁X, Subgroup.le_normalizer_iff]
        exact hnorm₁
      · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hH₂X, Subgroup.le_normalizer_iff]
        exact hnorm₂
    have hAs : ∀ A ∈ 𝒜, IsSimpleGroup ↥A := by
      intro A hA
      simp only [𝒜, Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl
      · exact isSimpleGroup_of_isL3 hL3₁
      · exact isSimpleGroup_of_isL3 hL3₂
    have hAnab : ∀ A ∈ 𝒜, ¬ IsMulCommutative ↥A := by
      intro A hA
      simp only [𝒜, Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl
      · intro hc
        obtain ⟨a, b, hab⟩ :=
          CFSG.Goldschmidt.G310.exists_mul_ne_of_quasisimple (s16c7_isQuasisimple_of_isL3 hL3₁)
        exact hab (hc.is_comm.comm a b)
      · intro hc
        obtain ⟨a, b, hab⟩ :=
          CFSG.Goldschmidt.G310.exists_mul_ne_of_quasisimple (s16c7_isQuasisimple_of_isL3 hL3₂)
        exact hab (hc.is_comm.comm a b)
    have hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
      intro A hA B hB hne a ha b hb
      simp only [𝒜, Finset.mem_insert, Finset.mem_singleton] at hA hB
      rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
      · exact absurd rfl hne
      · exact hcomm₁₂ a ha b hb
      · exact (hcomm₁₂ b hb a ha).symm
      · exact absurd rfl hne
    have hsup' : 𝒜.sup id = X := by
      simp only [𝒜, Finset.sup_insert, Finset.sup_singleton, id_eq]
      exact hsup
    obtain ⟨A, hA, hLA⟩ :=
      CFSG.GroupTheory.eq_of_isComponentOf_sup_of_direct (N := X) 𝒜 hAle hAn hAs hAnab
        hcomm hsup' L0 hL0
    rw [hLA]
    simp only [𝒜, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl
    · exact hL3₁
    · exact hL3₂


theorem s1611e3_quotient_prod_l3 {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hc : Subgroup.center L = ⊥) {K : Subgroup (L × L)} [K.Normal] :
    K = ⊤ ∨ Nonempty ((L × L) ⧸ K ≃* L) ∨ Nonempty ((L × L) ⧸ K ≃* L × L) := by
  have hker_snd : (MonoidHom.snd L L).ker = (⊤ : Subgroup L).prod (⊥ : Subgroup L) := by
    ext x
    exact ⟨fun h => ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr h⟩,
      fun h => Subgroup.mem_bot.mp h.2⟩
  have hker_fst : (MonoidHom.fst L L).ker = (⊥ : Subgroup L).prod (⊤ : Subgroup L) := by
    ext x
    exact ⟨fun h => ⟨Subgroup.mem_bot.mpr h, Subgroup.mem_top _⟩,
      fun h => Subgroup.mem_bot.mp h.1⟩
  rcases s1611e3_normal_subgroup_prod_l3 hc K with h | h | h | h
  · subst h
    exact Or.inr (Or.inr ⟨QuotientGroup.quotientBot⟩)
  · subst h
    refine Or.inr (Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq hker_snd.symm).trans ?_⟩)
    exact QuotientGroup.quotientKerEquivOfSurjective
      (φ := MonoidHom.snd L L) (fun a => ⟨(1, a), rfl⟩)
  · subst h
    refine Or.inr (Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq hker_fst.symm).trans ?_⟩)
    exact QuotientGroup.quotientKerEquivOfSurjective
      (φ := MonoidHom.fst L L) (fun a => ⟨(a, 1), rfl⟩)
  · exact Or.inl h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
