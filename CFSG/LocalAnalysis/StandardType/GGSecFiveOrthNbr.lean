module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthALRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSpinor
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthNbrClass
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthNbrPump
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthNbrFix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthNbrJoin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

private lemma ct_nb5_eq_neg_self_zmod3 (c : ZMod 3) (h : c = -c) : c = 0 := by
  have h' : c + c = 0 := eq_neg_iff_add_eq_zero.mp h
  have h2 : (2 : ZMod 3) * c = 0 := by rwa [two_mul]
  exact (mul_eq_zero.mp h2).resolve_left (by decide : (2 : ZMod 3) ≠ 0)

theorem GGOrthSetup.exists_nbr
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hPump : GGSecFivePumpReadInput)
    (hFix : GGSecFiveFixInput) :
    ∃ (c₁ c₂ : ZMod 3) (y : G) (K : Subgroup G), c₁ ≠ c₂ ∧ c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ GGNbr 3 B x D J y K ∧
      (∀ a ∈ ggAutomizer L Bs, GGIsReflection 3 a → OrthReflOfNorm Q c₁ (ggLin (p := 3) ι a)) ∧
      (∃ s ∈ ggAutomizer K Bs, GGIsReflection 3 s ∧ OrthReflOfNorm Q c₂ (ggLin (p := 3) ι s)) ∧
      GGWeylReflectionGroup 3 (ggAutomizer K Bs) ∧ ¬ GGWeylOfType 3 CoxeterMatrix.G₂ (ggAutomizer K Bs) ∧
      ggAutomizer J Bs ≤ ggAutomizer K Bs ∧ ggAutomizer J Bs ≤ ggAutomizer L Bs ∧ ¬ ggAutomizer L Bs ≤ ggAutomizer K Bs ∧
      ¬ ggAutomizer K Bs ≤ ggAutomizer L Bs ∧ ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAInf 3 B Bs x L D J ∧
      ((∃ n : ℕ, 2 ≤ n ∧ GGWeylOfType 3 (CoxeterMatrix.B n) (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) ∨
        GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ∨
        GGWeylOfType 3 CoxeterMatrix.G₂ (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) := by
  obtain ⟨c₁, hc₁, hL', a₀, ha₀, ha₀r⟩ := ggOrthNbr_classL S
  obtain ⟨y, K, hnb, s, hs, hsr, hsc⟩ := ggOrthNbr_exists_other S hc₁ hL'
  obtain ⟨hWeyl, hneG2, hJK, hJL, hKInf⟩ := ggOrthNbr_pump S hL hP hPump hnb
  have hnotLK : ¬ ggAutomizer L Bs ≤ ggAutomizer K Bs := ggOrthNbr_not_le S hFix hnb
  have hjoin := ggOrthNbr_join S hc₁ hL' ⟨a₀, ha₀, ha₀r⟩ hnb hs hsr hsc
  have hnotKL : ¬ ggAutomizer K Bs ≤ ggAutomizer L Bs := by
    intro hKL
    have hsL : s ∈ ggAutomizer L Bs := hKL hs
    have h1 : OrthReflOfNorm Q c₁ (ggLin (p := 3) ι s) := hL' s hsL hsr
    have hceq : c₁ = -c₁ := orthReflOfNorm_unique h1 hsc
    exact hc₁ (ct_nb5_eq_neg_self_zmod3 c₁ hceq)
  have hc₂ne : c₁ ≠ -c₁ := fun h => hc₁ (ct_nb5_eq_neg_self_zmod3 c₁ h)
  have hnegc₁ : -c₁ ≠ 0 := neg_ne_zero.mpr hc₁
  have hsup : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAInf 3 B Bs x L D J :=
    sup_le le_sup_left hKInf
  exact ⟨c₁, -c₁, y, K, hc₂ne, hc₁, hnegc₁, hnb, hL', ⟨s, hs, hsr, hsc⟩,
    hWeyl, hneG2, hJK, hJL, hnotLK, hnotKL, hsup, hjoin⟩

end CFSG.StandardType.OrthF3

end
