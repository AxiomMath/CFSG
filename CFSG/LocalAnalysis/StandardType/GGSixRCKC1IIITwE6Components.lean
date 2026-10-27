module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIITwE6Prime
public import CFSG.LocalAnalysis.StandardType.GGCompListMarked
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LocalAnalysis.StandardType.GGExcTwoCompListsRE
import CFSG.LocalAnalysis.StandardType.GGK0CompREMult
import CFSG.LocalAnalysis.StandardType.GGK0ExcB3Holds

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
open CFSG.Open (StatedLieAdmissible)


theorem twistedE6_compConfig_has_component_label
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .twistedE6 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (hcfg : RCKRP.RCKCompConfig .twistedE6 n 1 ψ p G₀ A B₁ D J L K e) :
    ∃ labK : LargeEvenLabel,
      labK ∈ [⟨.twA, 5, 1⟩, ⟨.D, 4, 1⟩, ⟨.twD, 5, 1⟩, ⟨.triD4, 0, 1⟩,
        ⟨.twA, 4, 1⟩, ⟨.twA, 2, 3⟩] ∧
      GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
  classical
  have hp3 := prime_eq_three_of_twistedE6_compConfig n ψ p G₀ A B₁ D J L K e hcfg
  subst p
  obtain ⟨hG0, -, -, -, hA, hB1A, hDB1, -, hAnormG0, hMarkG, -, -, -, -, -, hAcapBot,
    -, -, -, -, -, -, -, -, -, heD, hene, hKcomp, -, -⟩ := hcfg
  obtain ⟨⟨hAdm, -⟩, -, hperfG0, hLM⟩ := hG0
  have hn0 : n = 0 := by
    simpa [StatedLieAdmissible] using hAdm.2.2
  subst n
  have heA : e ∈ A := hB1A (hDB1 heD)
  have heN : e ∈ Subgroup.normalizer (G₀ : Set X) := hAnormG0 heA
  let α : MulAut ↥G₀ := G₀.normalizerMonoidHom ⟨e, heN⟩
  have hα3 : α ^ 3 = 1 := by
    have he3 : (⟨e, heN⟩ : Subgroup.normalizer (G₀ : Set X)) ^ 3 = 1 :=
      Subtype.ext (hA.2 e heA)
    change (G₀.normalizerMonoidHom ⟨e, heN⟩) ^ 3 = 1
    rw [← map_pow, he3, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have heC : e ∈ Subgroup.centralizer (G₀ : Set X) :=
      (normalizerMonoidHom_eq_one_iff (X := G₀) heN).mp h1
    have hmem : e ∈ A ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨heA, heC⟩
    rw [hAcapBot] at hmem
    exact hene (Subgroup.mem_bot.mp hmem)
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMarkG
  obtain ⟨labPure, hΛPure, hHasPure, R₀, hR₀, I₀, F₀, θ₀, htag, hrank, hchar, hdeg⟩ :=
    largeEvenMarking_exists_hasLabel
      (largeEvenMarking_of_lieModel_centerQuot hperfG0 hLM)
  have hpure : labPure = (⟨.twE6, 0, 1⟩ : LargeEvenLabel) := by
    rcases labPure with ⟨tag, rank, nn⟩
    have htag' : tag = .twE6 := by
      cases tag <;> simp [markTag] at htag
      · exfalso
        by_cases h3 : rank = 3
        · rw [if_pos h3] at htag
          cases htag
        · rw [if_neg h3] at htag
          cases htag
      · exfalso
        by_cases h2 : rank = 2
        · rw [if_pos h2] at htag
          cases htag
        · rw [if_neg h2] at htag
          by_cases h3 : rank = 3
          · rw [if_pos h3] at htag
            cases htag
          · rw [if_neg h3] at htag
            cases htag
      · rfl
    subst htag'
    have hrank0 : rank = 0 := by simpa [LargeEvenInLambda2] using hΛPure.2
    have hnn : nn = 1 := by simpa [markDeg] using hdeg
    subst hrank0
    subst hnn
    rfl
  have hHasPure' : GGHasLabel (⟨.twE6, 0, 1⟩ : LargeEvenLabel)
      (↥G₀ ⧸ Subgroup.center ↥G₀) := by
    rw [← hpure]
    exact hHasPure
  have hHasOrig : GGHasLabel lab (↥G₀ ⧸ Subgroup.center ↥G₀) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun θ _ => ⟨θ⟩)) hraw
  have hiso : GGLabelIso lab (⟨.twE6, 0, 1⟩ : LargeEvenLabel) :=
    ggLabelRigidInput_holds lab _ (↥G₀ ⧸ Subgroup.center ↥G₀) hΛ
      (by simp [LargeEvenInLambda2]) hHasOrig hHasPure'
  have hrawInv : LargeEvenRawDatum lab fun R _ I _ =>
      ∃ θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ (fun x y : ↥G₀ => y = α x) β := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    obtain ⟨β, hβ, hind⟩ := hθ e⁻¹ (A.inv_mem heA)
    refine ⟨θ, β, hβ, ?_⟩
    intro x y hxy
    subst hxy
    have hcoe : ((α x : ↥G₀) : X) = e * (x : X) * e⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe G₀ ⟨e, heN⟩ x
    exact hind x (α x) (by simpa [inv_inv] using hcoe)
  have hmarked : LargeEvenRawDatum (⟨.twE6, 0, 1⟩ : LargeEvenLabel) fun R _ I _ =>
      ∃ θ : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ (fun x y : ↥G₀ => y = α x) β :=
    largeEvenRawDatum_of_ggLabelIso hiso hrawInv
  have hKle : K ≤ G₀ := hKcomp.1.trans inf_le_left
  have hfixed : ggFixSub α = ggAutFixedSubgroup α := by
    ext x
    rfl
  have hK0 : IsComponentOf (K.subgroupOf G₀) (ggFixSub α) := by
    rw [hfixed]
    exact isComponentOf_subgroupOf_ggAutFixed (X := G₀) (J := K) (g := e) heN hKle hKcomp
  have hRE : GGK0CompRE :=
    ggK0CompRE_of_mult (ggK0CompREMult_of_excB
      (CFSG.StandardType.GGK0ExcB3Prod.ggK0ExcB3_holds.toB2.toExcB))
  have hlist : GGCompList (⟨.twE6, 0, 1⟩ : LargeEvenLabel) 3
      (· ∈ [⟨.twA, 5, 1⟩, ⟨.D, 4, 1⟩, ⟨.twD, 5, 1⟩, ⟨.triD4, 0, 1⟩,
        ⟨.twA, 4, 1⟩, ⟨.twA, 2, 3⟩]) :=
    ggTwE6TwoThreeComp_of_K0RE hRE
  obtain ⟨labK, hmem, hlabel⟩ :=
    GGCompList.of_rawMarking hlist hperf hα3 hα1 hmarked hK0
  exact ⟨labK, hmem,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKle) hlabel⟩

end CFSG.StandardType.RCKC1

end
