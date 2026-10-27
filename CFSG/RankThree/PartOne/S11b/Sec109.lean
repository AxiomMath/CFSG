module

public import CFSG.RankThree.PartOne.S11.Sec11Two

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

namespace Sec109

variable {G : Type} [Group G] [Finite G]

@[expose] def StructureB (L B : Subgroup G) : Prop :=
  ∃ b₁ b₂ x₁ x₂ x : G, b₁ ∈ B ∧ b₂ ∈ B ∧ B = Subgroup.closure {b₁, b₂} ∧
    orderOf b₁ = 7 ∧ orderOf b₂ = 7 ∧ x₁ ∈ L ∧ x₂ ∈ L ∧ x₁ ∈ normalizer (B : Set G) ∧
    x₂ ∈ normalizer (B : Set G) ∧ orderOf x₁ = 3 ∧ orderOf x₂ = 3 ∧ x₁ * x₂ = x₂ * x₁ ∧
    zpowers b₂ = B ⊓ centralizer ({x₁} : Set G) ∧ zpowers b₁ = B ⊓ centralizer ({x₂} : Set G) ∧
    x ∈ Subgroup.closure {x₁, x₂} ∧ x ≠ 1 ∧ (∃ lam : ℤ, ¬ ((7 : ℤ) ∣ lam - 1) ∧
      ∀ b ∈ B, x * b * x⁻¹ = b ^ lam) ∧ centralizer (B : Set G) ⊓ L = B

structure Config (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ) : Prop where
  setup : SteinbergBM.SectionTenSetup G p A
  p_eq : p = 7
  n_mem : n = 6 ∨ n = 7
  model : StatedClassicalModel ↥L .PSL n 2 1
  c_mem : c ∈ A
  c_ne_one : c ≠ 1
  L_mem : L ∈ sectionTenAt p (sectionTenZeroStar p A) c
  B_eq : B = A ⊓ L
  B_card : Nat.card B = 49
  A_eq : A = B ⊔ zpowers c
  structure_B : StructureB L B

structure Witness (A : Subgroup G) (c : G) (B : Subgroup G) (b : G) (S : Subgroup G) : Prop where
  b_mem : b ∈ B
  b_ne_one : b ≠ 1
  S_le : S ≤ centralizer ({b} : Set G)
  S_ne_bot : S ≠ ⊥
  S_two : IsPGroup 2 S
  S_norm : A ≤ normalizer (S : Set G)
  S_comm : S = ⁅S, zpowers c⁆

@[expose] def Setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZeroStar p A, ∀ n : ℕ, StatedClassicalModel ↥L .PSL n 2 1 →
      ∃ (c : G) (B : Subgroup G), Config p A c L B n

@[expose] def WitnessExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ),
    Config p A c L B n → ∃ (b : G) (S : Subgroup G), Witness A c B b S

@[expose] def ComponentExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ),
    Config p A c L B n → ∀ (b : G) (S : Subgroup G), Witness A c B b S →
      ∃ (S' K : Subgroup G), Witness A c B b S' ∧ K ∈ sectionTenAt p (sectionTenZero p A) b ∧
        S' ≤ K

@[expose] def MaximalExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ),
    Config p A c L B n → ∀ (b : G) (S K : Subgroup G), Witness A c B b S →
      K ∈ sectionTenAt p (sectionTenZero p A) b → S ≤ K →
        ∃ (b' : G) (S' K' : Subgroup G), Witness A c B b' S' ∧
          K' ∈ sectionTenAt p (sectionTenZeroStar p A) b' ∧ S' ≤ K'

@[expose] def FieldCaseImpossible : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ),
    Config p A c L B n → ∀ (b : G) (S K : Subgroup G), Witness A c B b S →
      K ∈ sectionTenAt p (sectionTenZeroStar p A) b → S ≤ K →
      CFSG.Blueprint.EvenLieType (K ⧸ Subgroup.center K) → ¬ p ∣ Nat.card (Subgroup.center K) →
      ∀ a d : G, a ∈ A → d ∈ A → d ≠ 1 →
        A = zpowers a ⊔ zpowers b ⊔ zpowers d → zpowers d = A ⊓ K → InducesFieldAut p a K →
        c ∉ zpowers b ⊔ zpowers d → False

@[expose] def MixedCaseImpossible : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ),
    Config p A c L B n → ∀ (b : G) (S K : Subgroup G), Witness A c B b S →
      K ∈ sectionTenAt p (sectionTenZeroStar p A) b → S ≤ K →
      CFSG.Blueprint.EvenLieType (K ⧸ Subgroup.center K) → ¬ p ∣ Nat.card (Subgroup.center K) →
      ∀ a d : G, a ∈ A → d ∈ A → d ≠ 1 →
        A = zpowers a ⊔ zpowers b ⊔ zpowers d → zpowers d = A ⊓ K → InducesFieldAut p a K →
        c ∈ zpowers b ⊔ zpowers d → False

@[expose] def InnerCaseImpossible : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ),
    Config p A c L B n → ∀ (b : G) (S K : Subgroup G), Witness A c B b S →
      K ∈ sectionTenAt p (sectionTenZeroStar p A) b → S ≤ K → K ∈ sectionTenOne p A → False

omit [Finite G] in
theorem inner_of_mem_sup {p : ℕ} {A K : Subgroup G} (hAK : A ≤ normalizer (K : Set G)) {b d : G}
    (hbK : ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ = 1) (hdK : d ∈ K) (hbA : b ∈ A) (hdA : d ∈ A) {c : G}
    (hcA : c ∈ A) (hc : c ∈ zpowers b ⊔ zpowers d) :
    ∃ q : K ⧸ aschbacherSolvableCore p K, thetaQuotientAction p hAK ⟨c, hcA⟩ = MulAut.conj q := by
  set f := thetaQuotientAction p hAK with hf
  set H : Subgroup A := (MulAut.conj : (K ⧸ aschbacherSolvableCore p K) →*
    MulAut (K ⧸ aschbacherSolvableCore p K)).range.comap f with hH
  have hb : (⟨b, hbA⟩ : A) ∈ H := by
    have h1 : f ⟨b, hbA⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hf, mem_ker_thetaQuotientAction_iff]
      intro k hk
      rw [hbK k hk]
      exact Subgroup.one_mem _
    refine ⟨1, ?_⟩
    rw [map_one, h1]
  have hd : (⟨d, hdA⟩ : A) ∈ H :=
    ⟨((⟨d, hdK⟩ : K) : K ⧸ aschbacherSolvableCore p K),
      (thetaQuotientAction_eq_conj_of_mem hAK ⟨d, hdA⟩ hdK).symm⟩
  have hsup : zpowers (⟨b, hbA⟩ : A) ⊔ zpowers (⟨d, hdA⟩ : A) ≤ H :=
    sup_le ((Subgroup.zpowers_le).2 hb) ((Subgroup.zpowers_le).2 hd)
  have hmap : (zpowers (⟨b, hbA⟩ : A) ⊔ zpowers (⟨d, hdA⟩ : A)).map A.subtype =
      zpowers b ⊔ zpowers d := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  rw [← hmap] at hc
  obtain ⟨a, ha, hac⟩ := hc
  have hac' : a = ⟨c, hcA⟩ := Subtype.ext hac
  rw [hac'] at ha
  obtain ⟨q, hq⟩ := hsup ha
  exact ⟨q, hq.symm⟩

theorem inSec10Nine_of_steps (h112 : InSec11Two) (hsetup : Setup) (hwit : WitnessExists)
    (hcomp : ComponentExists) (hmax : MaximalExists) (hfield : FieldCaseImpossible)
    (hmixed : MixedCaseImpossible) (hinner : InnerCaseImpossible) : InSec10Nine := by
  intro G _ _ p A h L hL n hmodel
  obtain ⟨c, B, cfg⟩ := hsetup G p A h L hL n hmodel
  obtain ⟨b, S, hW⟩ := hwit G p A c L B n cfg
  obtain ⟨S₁, K, hW₁, hK0, hSK⟩ := hcomp G p A c L B n cfg b S hW
  obtain ⟨b', S', K', hW', hK', hSK'⟩ := hmax G p A c L B n cfg b S₁ K hW₁ hK0 hSK
  have hKstar : K' ∈ sectionTenZeroStar p A := hK'.1
  have hb'A : b' ∈ A := by
    have : b' ∈ B := hW'.b_mem
    rw [cfg.B_eq] at this
    exact this.1
  have hKF : K' ∈ thetaComponentFamily p A := (sectionTenZeroStar_subset p A).2.2.1 hKstar.2
  by_cases h1 : K' ∈ sectionTenOne p A
  · exact hinner G p A c L B n cfg b' S' K' hW' hK' hSK' h1
  · have h2 : K' ∈ sectionTenTwo p A := ⟨hKF, h1⟩
    obtain ⟨hEven, hZ, a, d, haA, hdA, hd1, hAeq, hdK, hfa⟩ :=
      h112 G p A h b' hb'A hW'.b_ne_one K' ⟨⟨hKstar, h2⟩, hK'.2⟩
    by_cases hc : c ∈ zpowers b' ⊔ zpowers d
    · exact hmixed G p A c L B n cfg b' S' K' hW' hK' hSK' hEven hZ a d haA hdA hd1 hAeq hdK
        hfa hc
    · exact hfield G p A c L B n cfg b' S' K' hW' hK' hSK' hEven hZ a d haA hdA hd1 hAeq hdK
        hfa hc

end Sec109

end CFSG.RankThree.PartOne
