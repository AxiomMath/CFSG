module

public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeTypeAFrame
public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Case

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSecFiveLeviCase (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  (∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbr p B Bs x L D J n f y K) ∨
    (∃ (n : ℕ) (y : G) (K : Subgroup G), GGTypeAHalfNbr p B Bs x L D J n y K) ∨
    (∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeCNbr p B Bs x L D J n f y K)

theorem GGTypeASplitConfig.exists_typeANbr {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} (h : GGTypeASplitConfig p B Bs x L D J n f) :
    ∃ (y : G) (K : Subgroup G), GGTypeANbr p B Bs x L D J n f y K := by
  obtain ⟨hmod, hpq, hn, -, hsc, y, K, hnbr, hmodK, hW⟩ := h
  exact ⟨y, K, hmod, hpq, hn, hsc, hnbr, hmodK, hW⟩

theorem GGTypeASplitConfig.leviCase {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (h : GGTypeASplitConfig p B Bs x L D J n f) : GGSecFiveLeviCase p B Bs x L D J := by
  obtain ⟨y, K, hN⟩ := h.exists_typeANbr
  exact Or.inl ⟨n, f, y, K, hN⟩

end Case

section Inputs

@[expose] def GGSecFiveCompatRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs) →
        GGScalarsOrWeyl' p B Bs x D J →
          GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
          ¬ GGSecFiveLeviCase p B Bs x L D J → GGSecFiveCompat p B x L D J

theorem ggSecFiveCompatRestInput_of_compatNbrSome (h : GGCompatNbrSomeInput) :
    GGSecFiveCompatRestInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn _ _ t n f ψ hpres _
  exact h G p B Bs x L D J hcfg hOp hInn t n f ψ hpres

end Inputs

section Main

theorem ggSecFiveCompat_of_leviCase (hA : GGTypeAEndNodeInput) (hE : GGTypeAJoinEndNodeInput)
    (hC : GGTypeACorankTwoInput) (hH : GGTypeAHalfEndNodesInput) (hSpL : GGSpLiftInput)
    (hSpE : GGSpJoinEndNodeInput) (hSpJ : GGSpJoinInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hOp : GGOpAutTrivial p Bs) (hInn : GGInnerDiagAll p B Bs x L D J)
    (hNoTr : GGNoTransvection p Bs) (hlevi : GGSecFiveLeviCase p B Bs x L D J) :
    GGSecFiveCompat p B x L D J := by
  rcases hlevi with ⟨n, f, y, K, hN⟩ | ⟨n, y, K, hN⟩ | ⟨n, f, y, K, hN⟩
  · by_cases hsplit : ∃ n' f' : ℕ, GGTypeASplitConfig p B Bs x L D J n' f'
    · obtain ⟨n', f', hS⟩ := hsplit
      exact ggSecFiveCompat_of_endNodeInput hA hcfg hOp hInn hNoTr hS
    have hdiv : p ∣ n + 3 := by
      by_contra hp
      exact hsplit ⟨n, f, hN.splitConfig hp⟩
    by_cases hjoin : ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ L ⊔ K
    · exact ggSecFiveCompat_of_join hE hcfg hOp hInn hNoTr hN hjoin
    · push Not at hjoin
      exact ggSecFiveCompat_of_corankTwo hE hC hcfg hOp hInn hNoTr hN hdiv hjoin
  · exact ggSecFiveCompat_of_half hH hcfg hOp hInn hNoTr hN
  · exact ggSecFiveCompat_of_typeC hSpL hSpE hSpJ hcfg hOp hInn hNoTr hN

theorem ggCompatNbrSomeInput_of_secFive (hc₃ : GGNoTransvectionInput) (hd : GGCoxeterLabelInput)
    (hA : GGTypeAEndNodeInput) (hE : GGTypeAJoinEndNodeInput) (hC : GGTypeACorankTwoInput)
    (hH : GGTypeAHalfEndNodesInput) (hSpL : GGSpLiftInput) (hSpE : GGSpJoinEndNodeInput)
    (hSpJ : GGSpJoinInput) (hrest : GGSecFiveCompatRestInput) : GGCompatNbrSomeInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn t n f ψ hpres
  have hNoTr := hc₃ G p B Bs x L D J hcfg hOp hInn
  by_cases hlevi : GGSecFiveLeviCase p B Bs x L D J
  · exact ggSecFiveCompat_of_leviCase hA hE hC hH hSpL hSpE hSpJ hcfg hOp hInn hNoTr hlevi
  · exact hrest G p B Bs x L D J hcfg hOp hInn hNoTr (hd G p B Bs x L D J hcfg hOp hInn hNoTr)
      t n f ψ hpres hlevi

end Main

end CFSG.StandardType
