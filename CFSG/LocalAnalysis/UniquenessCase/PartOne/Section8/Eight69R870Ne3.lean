module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Core
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableAltTenDef
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847ThinNe3

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Layer
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70AltTen
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Member
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem r870_of_r847ThinNe3 {G : Type} [Group G] [Finite G] (D : Data G)
    (hK3 : Section7.StronglyEmbeddedThree) (hKS : Section7.StronglyEmbeddedSolvableAltTen)
    (hSg : UC6S846.SigmaStd D) (hcore : Sec7CoreOdd D) (h847 : UC22.R847ThinNe3 D) :
    R870 D := by
  intro L X H hc q hq hq2 hXq hsp
  have hX := eight70_perfect hc
  obtain ⟨-, -, hXHM⟩ := eight70_config hc
  have hXH : X ≤ H := hXHM.trans inf_le_left
  have hXM : X ≤ D.M := hXHM.trans inf_le_right
  by_cases hq3 : q = 3
  · subst hq3
    exact eight70_three hK3 hcore hc hXq hsp
  have hq5 : 5 ≤ q := by
    rcases Nat.lt_or_ge q 5 with h | h
    · interval_cases q <;> simp_all (config := { decide := true })
    · exact h
  obtain ⟨k, hkM, hkp, hk5⟩ := hcore q hq hq2 hsp
  obtain ⟨hno, h75⟩ := hk5 hq5
  subst hkp
  have hH : k.Config H := eight70_kconfig k hc hkM hXq
  have hXHk : X ≤ H ⊓ k.M := hkM ▸ hXHM
  rcases eight70_solvable_or_altTen k hq5 hno hH h75 hKS with hsol | ⟨hp5, hF, hY⟩
  · exact eight70_not_isSolvable k.prime hXHk hX (by omega) hsol
  obtain ⟨hXN, hXp⟩ := eight70_map_le_and_perfect (p := k.p) hXHk hX
  obtain ⟨hXF, f, hf⟩ := hY _ hXN hXp
  have hXI : X ≤ Section7.layerLift k.p H := eight70_le_layerLift hXH hX hXF
  obtain ⟨hI, hIK⟩ := eight70_layer_equiv k hH h75 hF
  have hXK : X ⊓ (CFSG.pPrimeCore k.p ↥H).map H.subtype = ⊥ :=
    le_bot_iff.1 (hIK ▸ inf_le_inf_right _ hXI)
  have h5X : 2 ≤ CFSG.Open.pRank 5 X := by
    rw [← hp5]
    omega
  obtain ⟨X₁, X₂, hX₁, hX₂, hsup, hinf, h₁, h₂, hcomm, h3X⟩ :=
    eight70_split (eight70_equiv_alt5_prod hXH hX h5X hXK f hf)
  obtain ⟨Y, hYC, hthin, hYA⟩ := eight70_member hc.hyp hX₁ hX₂ hsup hinf h₁ h₂ hcomm
  have hns : ¬ IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hYC
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact eight70_three hK3 hcore hc (by omega) (UC6S846.sp_of_mem_sig hSg hns hpσ)
  have hgen : ∀ Xa Xb : Subgroup G, Xa ≤ X → Xb ≤ X →
      Nonempty (↥Xa ≃* alternatingGroup (Fin 5)) → Nonempty (↥Xb ≃* alternatingGroup (Fin 5)) →
      (∀ x ∈ Xa, ∀ y ∈ Xb, x * y = y * x) →
      (∀ A : Subgroup G, A ≤ Xa → Odd (Nat.card A) → A ≤ Y) → False := by
    intro Xa Xb hXa hXb ha hb hab hAY
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h60 : Nat.card ↥Xa = 60 := by
      rw [Nat.card_congr ha.some.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 1) (G := ↥Xa)
      (by rw [h60]; norm_num)
    let A : Subgroup G := A₀.map Xa.subtype
    have hAXa : A ≤ Xa := Subgroup.map_subtype_le A₀
    have hA3 : Nat.card A = 3 := by
      rw [Subgroup.card_map_of_injective Xa.subtype_injective, hA₀, pow_one]
    have hAY' : A ≤ Y := hAY A hAXa (by rw [hA3]; decide)
    have hN : normalizer (A : Set G) ≤ D.M :=
      h847 Y hYC hthin A hAY' 3 Nat.prime_three (by norm_num) hA3 p hpσ hp3
    have hIM := eight70_le_of_normalizer_le hI (hXa.trans hXI) (hXb.trans hXI) ha hb hab hAXa hA3
      (hXa.trans hXM) (hXb.trans hXM) hN
    exact k.step72L H hH (hkM ▸ hIM)
  rcases hYA with hYA | hYA
  · exact hgen X₁ X₂ hX₁ hX₂ h₁ h₂ hcomm hYA
  · exact hgen X₂ X₁ hX₂ hX₁ h₂ h₁ (fun x hx y hy => (hcomm y hy x hx).symm) hYA

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
