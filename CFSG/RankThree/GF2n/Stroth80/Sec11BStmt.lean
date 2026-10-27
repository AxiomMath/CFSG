module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

abbrev XbarMod (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] : Type :=
  ↥(Xbar M Q Z B) ⧸ Subgroup.center ↥(Xbar M Q Z B)

@[expose] def IsLmChar2 (Y : Type) [Group Y] : Prop :=
  ∃ m x : ℕ, CFSG.Blueprint.LieModel Y .PSL m 2 x

@[expose] def IsSpChar2 (Y : Type) [Group Y] : Prop :=
  ∃ m x : ℕ, CFSG.Blueprint.LieModel Y .PSp m 2 x

@[expose] def IsOmegaChar2 (Y : Type) [Group Y] : Prop :=
  ∃ m x : ℕ, CFSG.Blueprint.LieModel Y .POmegaPlus m 2 x ∨
    CFSG.Blueprint.LieModel Y .POmegaMinus m 2 x ∨
    CFSG.Blueprint.LieModel Y .PSL 4 2 x ∨ CFSG.Blueprint.LieModel Y .PSU 4 2 x

@[expose] def CaseVICore (M Q Z S : Subgroup G) (n : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
    ∃ φ : S →* GL (Fin n) K, φ.range = StatedSL n K ∧ φ.ker = Q.subgroupOf S ∧
      ∃ V₁ V₂ : Subgroup G, Z ≤ V₁ ∧ V₁ ≤ Q ∧ Z ≤ V₂ ∧ V₂ ≤ Q ∧ V₁ ⊓ V₂ = Z ∧
        V₁ ⊔ V₂ = Q ∧
        SectionAct (ι := Fin n) K S V₁ Z φ (fun g => (g : Matrix (Fin n) (Fin n) K)) ∧
        SectionAct (ι := Fin n) K S V₂ Z φ
          (fun g => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ) ∧
        (∃ x ∈ M, conjSubgroup x V₁ = V₂)

theorem CaseVI.of_core {M Q Z S : Subgroup G} {n : ℕ} (h : CaseVICore M Q Z S n)
    (hc : CentDvd M Q Z S) : CaseVI M Q Z S := by
  obtain ⟨K, hK, hf, hcard, φ, hr, hk, V₁, V₂, h1, h2, h3, h4, h5, h6, hA1, hA2, hx⟩ := h
  exact ⟨n, K, hK, hf, hcard, φ, hr, hk, V₁, V₂, h1, h2, h3, h4, h5, h6, hA1, hA2, hx, hc⟩

@[expose] def Stroth117Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n →
    (∃ a ∈ LB M Q B, IsA2 Q Z a) →
    IsLmChar2 (XbarMod M Q Z B) ∨ IsSpChar2 (XbarMod M Q Z B) ∨ IsOmegaChar2 (XbarMod M Q Z B)

@[expose] def ExcludedByElevenSeven (Y : Type) [Group Y] : Prop :=
  ∃ (t : StatedLieTag) (m x : ℕ), (t = .G2 ∨ t = .trialityD4 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨
    t = .E8 ∨ t = .twistedE6 ∨ t = .twistedB2 ∨ (t = .PSU ∧ (m = 3 ∨ 5 ≤ m))) ∧
    CFSG.Blueprint.LieModel Y t m 2 x

@[expose] def Stroth117ExclStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → (∃ a ∈ LB M Q B, IsA2 Q Z a) →
    ¬ ExcludedByElevenSeven (XbarMod M Q Z B)

@[expose] def Stroth118Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n →
    (∃ a ∈ LB M Q B, IsA2 Q Z a) → ¬ IsSpChar2 (XbarMod M Q Z B)

@[expose] def Stroth119Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n →
    (∃ a ∈ LB M Q B, IsA2 Q Z a) → IsOmegaChar2 (XbarMod M Q Z B) →
    ∃ y : ℕ, 2 ^ y = Nat.card Z ∧ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 4 2 y

@[expose] def Stroth1110Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n →
    (∃ a ∈ LB M Q B, IsA2 Q Z a) → IsLmChar2 (XbarMod M Q Z B) →
    Xbar M Q Z B = bar M Q (Lgen M (LB M Q B)) ∧ CaseVICore M Q Z (Lgen M (LB M Q B)) n

end CFSG.RankThree.GF2n.Stroth80
