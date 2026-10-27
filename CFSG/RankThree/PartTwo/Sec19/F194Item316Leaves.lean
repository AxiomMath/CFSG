module

public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
public import CFSG.RankThree.PartTwo.Sec19.F194Item316Glue
import CFSG.RankThree.PartTwo.Sec19.SimsItem316Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo

section Defs

variable {G : Type} [Group G]

@[expose] def IsUniqueAbelianBlock (M L : Subgroup G) : Prop :=
  IsBlock M L ∧ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L) ∧ CFSG.Open.IsElemAbelian 2 (blockU L) ∧
    CFSG.maximalTwoLocalsContaining (L : Set G) = {M}

@[expose] def IsSolomonBlock (M L : Subgroup G) : Prop :=
  IsUniqueAbelianBlock M L ∧ Subgroup.normalizer (L : Set G) = M

@[expose] def IsScriptXType (L : Subgroup G) : Prop :=
  (∃ n : ℕ, IsLin2Type L n) ∨ ∃ n : ℕ, Odd n ∧ IsAltNaturalType L n

@[expose] def IsSolomonTypes (L : Subgroup G) : Prop :=
  (∃ n : ℕ, Even n ∧ IsAltNaturalType L n) ∨ IsA7FourType L

@[expose] def IsHaradaHallTypes (L : Subgroup G) : Prop :=
  (∃ m : ℕ, 4 ≤ m ∧ IsOmegaPlusType L m) ∨ (∃ m : ℕ, 2 ≤ m ∧ IsOmegaMinusType L m) ∨
    IsA6Z3Type L

@[expose] def IsSmallOrthType (L : Subgroup G) : Prop :=
  (∃ m : ℕ, m ≤ 3 ∧ IsOmegaPlusType L m) ∨ ∃ m : ℕ, m ≤ 1 ∧ IsOmegaMinusType L m

theorem isTypeScriptL_cases {L : Subgroup G} (h : IsTypeScriptL L) :
    IsScriptXType L ∨ IsSolomonTypes L ∨ IsHaradaHallTypes L ∨ IsSmallOrthType L := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨m, hm⟩ | ⟨m, hm⟩ | h6 | h7
  · exact Or.inl (Or.inl ⟨n, hn⟩)
  · rcases Nat.even_or_odd n with he | ho
    · exact Or.inr (Or.inl (Or.inl ⟨n, he, hn⟩))
    · exact Or.inl (Or.inr ⟨n, ho, hn⟩)
  · rcases Nat.lt_or_ge m 4 with hlt | hge
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, by omega, hm⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨m, hge, hm⟩)))
  · rcases Nat.lt_or_ge m 2 with hlt | hge
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, by omega, hm⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨m, hge, hm⟩))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr h6))))
  · exact Or.inr (Or.inl (Or.inr h7))

end Defs

@[expose] def Item316ScriptX : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ∀ M L : Subgroup G, CFSG.IsMaximalTwoLocal M → IsBlock M L → IsScriptXType L →
      CFSG.Assembly.InCatalog G

@[expose] def Item316Small : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    CFSG.Assembly.evenRank G = 3 →
    ∀ M L : Subgroup G, CFSG.IsMaximalTwoLocal M → IsBlock M L → IsSmallOrthType L →
      CFSG.Assembly.InCatalog G

@[expose] def Lit316Harada : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    CFSG.Assembly.evenRank G = 3 →
    ∀ M J : Subgroup G, CFSG.IsMaximalTwoLocal M → IsBlock M J → ⁅J, J⁆ = J →
      (IsOmegaMinusType J 2 ∨ IsOmegaMinusType J 3) →
      CFSG.Open.IsElemAbelian 2 (blockU J) →
      CFSG.maximalTwoLocalsContaining (J : Set G) = {M} →
      CFSG.Assembly.InCatalog G

@[expose] def Lit316Hall : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ∀ M L : Subgroup G, CFSG.IsMaximalTwoLocal M → IsBlock M L → ⁅L, L⁆ = L → IsA6Z3Type L →
      CFSG.Open.IsElemAbelian 2 (blockU L) →
      CFSG.maximalTwoLocalsContaining (L : Set G) = {M} →
      (∀ t ∈ CFSG.Open.pCoreOf 2 M, t ≠ 1 →
        CFSG.generalizedFitting ↥(Subgroup.centralizer ({t} : Set G)) =
          CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G))) →
      CFSG.Assembly.InCatalog G

@[expose] def Lit316SolomonEven : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    CFSG.Assembly.evenRank G = 3 →
    ∀ M X : Subgroup G, CFSG.IsMaximalTwoLocal M → IsBlock M X →
      CFSG.Open.IsElemAbelian 2 (blockU X) → Subgroup.normalizer (X : Set G) = M →
      CFSG.maximalTwoLocalsContaining (X : Set G) = {M} →
      (∃ n : ℕ, (n = 6 ∨ n = 8 ∨ n = 10) ∧ IsAltNaturalType X n) →
      (∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 →
        CFSG.generalizedFitting ↥(Subgroup.centralizer ({x} : Set G)) =
          CFSG.pCore 2 ↥(Subgroup.centralizer ({x} : Set G))) →
      CFSG.Assembly.InCatalog G

@[expose] def Lit316SolomonSeven : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ∀ M X : Subgroup G, CFSG.IsMaximalTwoLocal M → IsBlock M X →
      CFSG.Open.IsElemAbelian 2 (blockU X) → Subgroup.normalizer (X : Set G) = M →
      CFSG.maximalTwoLocalsContaining (X : Set G) = {M} → IsA7FourType X →
      (∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 →
        CFSG.generalizedFitting ↥(Subgroup.centralizer ({x} : Set G)) =
          CFSG.pCore 2 ↥(Subgroup.centralizer ({x} : Set G))) →
      CFSG.Assembly.InCatalog G

@[expose] def Lit316NonGood : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    CFSG.Assembly.evenRank G = 3 →
    ∀ M L : Subgroup G, CFSG.IsMaximalTwoLocal M → IsBlock M L →
      ((IsSolomonTypes L ∧ ¬ IsSolomonBlock M L) ∨
        (IsHaradaHallTypes L ∧ ¬ IsUniqueAbelianBlock M L)) →
      CFSG.Assembly.InCatalog G

theorem item316_of_leaves (hX : Item316ScriptX) (hS : Item316Small) (hH : Lit316Harada)
    (hHall : Lit316Hall) (hE : Lit316SolomonEven) (h7 : Lit316SolomonSeven)
    (hN : Lit316NonGood) : Item316 := by
  intro G _ _ hsimple hnonab hK hchar he M L hM hL
  obtain ⟨hB, hT⟩ := hL
  have hcent : ∀ t ∈ CFSG.Open.pCoreOf 2 M, t ≠ 1 →
      CFSG.generalizedFitting ↥(Subgroup.centralizer ({t} : Set G)) =
        CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G)) :=
    fun t ht h1 => generalizedFitting_centralizer_eq_pCore hchar ht h1
  rcases isTypeScriptL_cases hT with h | h | h | h
  · exact hX G hsimple hnonab hK hchar M L hM hB h
  · by_cases hg : IsSolomonBlock M L
    · obtain ⟨⟨-, hq, hab, huniq⟩, hnorm⟩ := hg
      rcases h with ⟨n, hev, hn⟩ | h7'
      · exact hE G hsimple hnonab hK hchar he M L hM hB hab hnorm huniq
          ⟨n, Narrow316.mem_of_isAltNaturalType_of_even he hM hB.2.1 hq hn hev, hn⟩ hcent
      · exact h7 G hsimple hnonab hK hchar M L hM hB hab hnorm huniq h7' hcent
    · exact hN G hsimple hnonab hK hchar he M L hM hB (Or.inl ⟨h, hg⟩)
  · by_cases hg : IsUniqueAbelianBlock M L
    · obtain ⟨-, hq, hab, huniq⟩ := hg
      have hperf : ⁅L, L⁆ = L := commutator_eq_of_isShort_of_isQuasisimple hB.1 hq
      rcases h with ⟨m, hm, hm'⟩ | ⟨m, hm, hm'⟩ | h6
      · exact absurd (Narrow316.lt_four_of_isOmegaPlusType he hM hB.2.1 hm') (by omega)
      · have hm4 := Narrow316.lt_four_of_isOmegaMinusType he hM hB.2.1 hm'
        have h23 : IsOmegaMinusType L 2 ∨ IsOmegaMinusType L 3 := by
          obtain rfl | rfl : m = 2 ∨ m = 3 := by omega
          exacts [Or.inl hm', Or.inr hm']
        exact hH G hsimple hnonab hK hchar he M L hM hB hperf h23 hab huniq
      · exact hHall G hsimple hnonab hK hchar M L hM hB hperf h6 hab huniq hcent
    · exact hN G hsimple hnonab hK hchar he M L hM hB (Or.inr ⟨h, hg⟩)
  · exact hS G hsimple hnonab hK hchar he M L hM hB h

end CFSG.RankThree.PartTwo.Sec19
