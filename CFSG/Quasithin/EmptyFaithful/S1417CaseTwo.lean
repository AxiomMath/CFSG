module

public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1417Orth
public import CFSG.Quasithin.EmptyFaithful.S1417Concl
public import CFSG.Quasithin.EmptyFaithful.S1417NaturalMore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1417

section CaseTwo

variable {G : Type} [Group G] [Finite G] {T M V : Subgroup G}

theorem caseTwo_core (hVe : IsElemAbelian 2 V) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {L₁ L₂ : Subgroup (MulAut (IntMod V hVe))} {t : MulAut (IntMod V hVe)}
    (hN₁ : ActsAsNaturalL2 L₁ (commV L₁)) (hN₂ : ActsAsNaturalL2 L₂ (commV L₂))
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hLinf : L₁ ⊓ L₂ = ⊥)
    (hinf : commV L₁ ⊓ commV L₂ = ⊥) (hUtop : commV L₁ ⊔ commV L₂ = ⊤)
    (hL₁X : L₁ ≤ autI hVe M) (hL₂X : L₂ ≤ autI hVe M) (htX : t ∈ autI hVe M) (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (ht₁ : B1.conjAut t L₁ = L₂)
    (hXt : autI hVe M = (L₁ ⊔ L₂) ⊔ Subgroup.zpowers t)
    (hY : autI hVe (thompsonJ M) = L₁ ⊔ L₂)
    (hcv₁ : (commV L₁).map t.toMonoidHom = commV L₂)
    (hcv₂ : (commV L₂).map t.toMonoidHom = commV L₁)
    (hE4 : Nat.card (omegaOneCenterOf (thompsonJ T) ⊓ V : Subgroup G) = 4) (R : Prop) (hR : R) :
    Lemma1417CaseTwoCore T M V R := by
  have hht₁ : ∀ u ∈ commV L₁, t u ∈ commV L₂ := fun u hu => by
    have : t u ∈ (commV L₁).map t.toMonoidHom := ⟨u, hu, rfl⟩
    rwa [hcv₁] at this
  have hht₂ : ∀ u ∈ commV L₂, t u ∈ commV L₁ := fun u hu => by
    have : t u ∈ (commV L₂).map t.toMonoidHom := ⟨u, hu, rfl⟩
    rwa [hcv₂] at this
  obtain ⟨hcard16, q, hq1, hq2, hq3, hq4⟩ :=
    exists_quad_orthogonal hN₁ hN₂ hc hinf hUtop hht₁ hht₂
  obtain ⟨tg, htgM, htg⟩ := (mem_autI hVe).1 htX
  set Y₁ : Subgroup G := preI hVe M hMN L₁ with hY₁
  set Y₂ : Subgroup G := preI hVe M hMN L₂ with hY₂
  have hA₁ : autOn Y₁ V = L₁ := autI_preI hVe hL₁X
  have hA₂ : autOn Y₂ V = L₂ := autI_preI hVe hL₂X
  have hY₁N : Y₁ ≤ Subgroup.normalizer (V : Set G) := (preI_le hVe).trans hMN
  have hY₂N : Y₂ ≤ Subgroup.normalizer (V : Set G) := (preI_le hVe).trans hMN
  have hcomm₁ : ⁅V, Y₁⁆ = (commV L₁).map (inclMod hVe) := by
    rw [commutator_eq_map_commV hVe hY₁N]
    exact congrArg (fun L => (commV L).map (inclMod hVe)) hA₁
  have hcomm₂ : ⁅V, Y₂⁆ = (commV L₂).map (inclMod hVe) := by
    rw [commutator_eq_map_commV hVe hY₂N]
    exact congrArg (fun L => (commV L).map (inclMod hVe)) hA₂
  refine ⟨⟨hcard16, q, hq1, hq2, hq3, ?_⟩, Y₁, Y₂, ⟨tg, ?_⟩, preI_le hVe, preI_le hVe, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hE4, hR⟩
  · exact hXt.trans hq4
  · exact tg.2
  · exact htgM
  · rw [hA₁]
    exact nonempty_equiv_perm hN₁
  · rw [hA₂]
    exact nonempty_equiv_perm hN₂
  · rw [hA₁, hA₂]
    exact hLinf
  · rw [hA₁, hA₂]
    exact hc
  · change t ^ 2 = 1 at ht2
    rw [show conjAct V tg = t from htg]
    exact ht2
  · rw [show conjAct V tg = t from htg]
    exact ht1
  · rw [hA₁, hA₂, show conjAct V tg = t from htg]
    exact (conjAut_eq_map t L₁).symm.trans ht₁
  · rw [hA₁, hA₂, show conjAct V tg = t from htg]
    exact hXt
  · rw [hA₁, hA₂]
    exact hY
  · rw [hcomm₁, hcomm₂, ← Subgroup.map_inf _ _ _ (inclMod_injective hVe), hinf, Subgroup.map_bot]
  · rw [hcomm₁, hcomm₂, ← Subgroup.map_sup, hUtop, map_inclMod_top]
  · rw [hcomm₁, Subgroup.card_map_of_injective (inclMod_injective hVe)]
    exact (card_of_actsAsNaturalL2 hN₁).2
  · rw [hcomm₂, Subgroup.card_map_of_injective (inclMod_injective hVe)]
    exact (card_of_actsAsNaturalL2 hN₂).2

end CaseTwo

end S1417

end CFSG.Quasithin
