module

public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof417
import CFSG.RankThree.PartTwo.Sec4.Item417ResProofOutFacts
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)


namespace Res417

theorem isList46_of_centralizer (h46 : Item4_6) {G : Type} [Group G] [Finite G]
    (hG : SectionFourHyp G) {L : Subgroup G} (hL : IsComponent L) {c : G}
    (hcC : c ∈ Subgroup.centralizer (L : Set G)) (hc3 : orderOf c = 3) :
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) := by
  set H := Subgroup.centralizer ({c} : Set G) with hHdef
  have hcH : c ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hLH : L ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hcC x hx)
  have hH : SectionFourHyp H := sectionFourHyp_subgroup hG H
  have h3H : 3 ∣ Nat.card (Subgroup.center H) := by
    have hz : (⟨c, hcH⟩ : H) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)
    have hord : orderOf (⟨⟨c, hcH⟩, hz⟩ : Subgroup.center H) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc3]
    exact hord ▸ orderOf_dvd_natCard _
  have hL' : L.subgroupOf H ∈ thetaComponents 3 H := mem_thetaComponents_subgroupOf hL hLH
  exact Sec21.Item223PrintProof.isList46_of_mulEquiv
    (thetaQuotCongr (Subgroup.subgroupOfEquivOfLe hLH)) (h46 H hH h3H _ hL')

end Res417

section Certs


@[expose] def IsInnerOutConf417 {G : Type} [Group G] [Finite G] (L A E : Subgroup G) (c : G)
    (m : ℕ) : Prop :=
  SectionFourHyp G ∧ CFSG.pCore 2 G = ⊥ ∧ IsComponent L ∧
    (∀ (A E : Subgroup G) (c : G) (m : ℕ), IsQuad417 L A E c m → m ≤ 4) ∧
    IsQuad417 L A E c m ∧ A ≤ Subgroup.normalizer (L : Set G) ∧
    (¬ ∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField) ∧
    ¬ IsSLThreePiTheta L ∧ (∀ a ∈ A, ¬ InducesOuterTheta a L) ∧ c ∉ L ∧
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L)

@[expose] def Item417OutL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerOutConf417 L A E c m →
      (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p e))) →
      Alt417 L A m

@[expose] def Item417OutL3Eps : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerOutConf417 L A E c m →
      (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
        (IsSLThreeEpsAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField p e)) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 p e))) →
      Alt417 L A m

@[expose] def Item417OutLieP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerOutConf417 L A E c m →
      (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
        (Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 p 1 ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField p 1)) ∨
          (p % 3 = 1 ∧ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 p 1)) ∨
          (p % 3 = 2 ∧
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 4 (GaloisField p 1))))) →
      Alt417 L A m

@[expose] def Item417OutAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerOutConf417 L A E c m →
      ((∃ n : ℕ, n ≤ 9 ∧ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin n))) ∨
        IsExtOf (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6))
          (Multiplicative (ZMod 3)) ∨
        IsExtOf (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7))
          (Multiplicative (ZMod 3))) →
      Alt417 L A m

@[expose] def Item417OutSpor : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerOutConf417 L A E c m →
      ((∃ s ∈ sporadics46,
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.Carrier s)) ∨
        ∃ s ∈ sporadicCovers46, IsExtOf (L ⧸ aschbacherSolvableCore 3 L)
          (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3))) →
      Alt417 L A m

@[expose] def Item417OutChevTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerOutConf417 L A E c m →
      (IsChevTwoRankTwoModel (L ⧸ aschbacherSolvableCore 3 L) ∨
        ∃ n : ℕ, 1 ≤ n ∧ IsSLThreeEpsAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ n)) →
      Alt417 L A m

@[expose] def Item417OutSmallTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerOutConf417 L A E c m →
      (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 5 (GaloisField 2 1)) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 3 (GaloisField 2 1)) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 5 2 2)) →
      Alt417 L A m

@[expose] def Item417OutCharThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerOutConf417 L A E c m →
      ((∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 3 e)) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 3 e))) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 4 (GaloisField 3 1)) ∨
        (Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) ≤ 3 ∧
          (Blueprint.ChevalleyExceptionalModel
              ((L ⧸ aschbacherSolvableCore 3 L) ⧸
                Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) .G2 3 1 ∨
            Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
              Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* projSU 4 3 1)))) →
      Alt417 L A m

theorem item4_17InnerOut_of (h46 : Item4_6) (h1 : Item417OutL2) (h2 : Item417OutL3Eps)
    (h3 : Item417OutLieP) (h4 : Item417OutAlt) (h5 : Item417OutSpor) (h6 : Item417OutChevTwo)
    (h7 : Item417OutSmallTwo) (h8 : Item417OutCharThree) : Item4_17InnerOut := by
  intro G _ _ hG hO2 L hL hstar A E c m hq hAL hf hSL hout hcL
  have hconf : IsInnerOutConf417 L A E c m :=
    ⟨hG, hO2, hL, hstar, hq, hAL, hf, hSL, hout, hcL,
      Res417.center_thetaQuot_eq_bot hL hq.1 hq.2.2.1 hAL hout hcL,
      Res417.eq_sup_of_inner hL hq.1 hq.2.2.1 hAL hout hcL⟩
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := by
    have : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hq.2.2.1 ▸ Subgroup.mem_zpowers c
    exact this.2
  rcases Res417.isList46_of_centralizer h46 hG hL hcC hq.2.2.2.1 with h | h | h | h | h | h | h | h
  · exact h1 G L A E c m hconf h
  · exact h2 G L A E c m hconf h
  · exact h3 G L A E c m hconf h
  · exact h4 G L A E c m hconf h
  · exact h5 G L A E c m hconf h
  · exact h6 G L A E c m hconf h
  · exact h7 G L A E c m hconf h
  · exact h8 G L A E c m hconf h

end Certs

end CFSG.RankThree.PartTwo.Sec4
