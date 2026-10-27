module

public import CFSG.RankThree.PartTwo.Sec4.Statements417
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts

@[expose] def IsSLThreePiTheta {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
    (IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e) ∨
      IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e)

theorem IsQuad417.le_normalizer (h45 : Item4_5) {G : Type} [Group G] [Finite G]
    (hG : SectionFourHyp G) {L A E : Subgroup G} {c : G} {m : ℕ} (hL : IsComponent L)
    (h : IsQuad417 L A E c m) : A ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨hmax, hcard, -, -, hE, hEA, -⟩ := h
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.prop
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  have hm : 3 ≤ m := by
    have hdvd : 3 ^ 3 ∣ 3 ^ m := by
      rw [← hcard, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
      exact Subgroup.card_dvd_of_le hEA
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  exact h45 G hG A hA3 (Or.inr ⟨hAe, m, hm, hcard⟩) L (mem_thetaComponents_of_isComponent3 hL)

namespace Res417

theorem isSLThreePiAt_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {q : ℕ}
    (h : IsSLThreePiAt Y q) : IsSLThreePiAt X q := by
  obtain ⟨K, hK, hKf, h⟩ := h
  refine ⟨K, hK, hKf, ?_⟩
  rcases h with ⟨h1, h2, ⟨f⟩⟩ | ⟨h1, h2, ⟨f⟩⟩
  · exact Or.inl ⟨h1, h2, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨h1, h2, ⟨e.trans f⟩⟩

theorem isoLThreePi_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    [Fact p.Prime] (h : IsoLThreePi Y p f) : IsoLThreePi X p f := by
  rcases h with ⟨h1, ⟨e'⟩⟩ | ⟨h1, ⟨e'⟩⟩
  · exact Or.inl ⟨h1, ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨h1, ⟨e.trans e'⟩⟩

end Res417

open Res417

section Certs


@[expose] def Item4_17SL3Pi : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → CFSG.pCore 2 G = ⊥ →
    ∀ L : Subgroup G, IsComponent L →
    (∀ (A E : Subgroup G) (c : G) (m : ℕ), IsQuad417 L A E c m → m ≤ 4) →
    ∀ (A E : Subgroup G) (c : G) (m : ℕ), IsQuad417 L A E c m →
      A ≤ Subgroup.normalizer (L : Set G) →
      (¬ ∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField) →
      IsSLThreePiTheta L → Alt417 L A m

@[expose] def Item4_17InnerIn : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → CFSG.pCore 2 G = ⊥ →
    ∀ L : Subgroup G, IsComponent L →
    (∀ (A E : Subgroup G) (c : G) (m : ℕ), IsQuad417 L A E c m → m ≤ 4) →
    ∀ (A E : Subgroup G) (c : G) (m : ℕ), IsQuad417 L A E c m →
      A ≤ Subgroup.normalizer (L : Set G) →
      (¬ ∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField) →
      ¬ IsSLThreePiTheta L → (∀ a ∈ A, ¬ InducesOuterTheta a L) → c ∈ L → Alt417 L A m

@[expose] def Item4_17InnerOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → CFSG.pCore 2 G = ⊥ →
    ∀ L : Subgroup G, IsComponent L →
    (∀ (A E : Subgroup G) (c : G) (m : ℕ), IsQuad417 L A E c m → m ≤ 4) →
    ∀ (A E : Subgroup G) (c : G) (m : ℕ), IsQuad417 L A E c m →
      A ≤ Subgroup.normalizer (L : Set G) →
      (¬ ∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField) →
      ¬ IsSLThreePiTheta L → (∀ a ∈ A, ¬ InducesOuterTheta a L) → c ∉ L → Alt417 L A m

theorem exists_field_of_inducesOuterTheta (h47 : Item4_7) {G : Type} [Group G] [Finite G]
    (hG : SectionFourHyp G) {L A E : Subgroup G} {c : G} {m : ℕ} (hL : IsComponent L)
    (hq : IsQuad417 L A E c m) (hSL : ¬ IsSLThreePiTheta L) {a : G} (haA : a ∈ A)
    (ha : InducesOuterTheta a L) :
    ∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField := by
  obtain ⟨hAmax, -, hAc, hc3, -, -, -⟩ := hq
  have hA := hAmax.prop
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set H := Subgroup.centralizer ({c} : Set G) with hHdef
  have hcH : c ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hLH : L ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hcAC.2 x hx)
  have hAH : A ≤ H := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (hcomm c hcAC.1 a ha).symm
  have hH : SectionFourHyp H := sectionFourHyp_subgroup hG H
  have h3H : 3 ∣ Nat.card (Subgroup.center H) := by
    have hz : (⟨c, hcH⟩ : H) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)
    have hord : orderOf (⟨⟨c, hcH⟩, hz⟩ : Subgroup.center H) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc3]
    exact hord ▸ orderOf_dvd_natCard _
  set L' := L.subgroupOf H with hL'def
  have hL' : L' ∈ thetaComponents 3 H := mem_thetaComponents_subgroupOf hL hLH
  set eθ : L' ⧸ aschbacherSolvableCore 3 L' ≃* L ⧸ aschbacherSolvableCore 3 L :=
    thetaQuotCongr (Subgroup.subgroupOfEquivOfLe hLH) with heθ
  have haH := hAH haA
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact KFacts.not_inducesOuterTheta_one L ha
  have ha3 : orderOf (⟨a, haH⟩ : H) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hA.2 a haA) ha1
  have h47' := h47 H hH h3H L' hL' ⟨a, haH⟩ ha3 (inducesOuterTheta_subgroupOf hLH haH ha)
  have hLL : L'.map H.subtype = L := by
    rw [hL'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLH]
  have hk : ∀ k : AutKind, InducesStdKind L' ⟨a, haH⟩ k → InducesStdKind L a k := by
    intro k hk
    have h1 := Sec13.inducesStdKind_sub H L' hk
    rwa [hLL] at h1
  have hSLq : ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
      (IsSLThreePiAt (L' ⧸ aschbacherSolvableCore 3 L') (p ^ e) ∨
        IsoLThreePi (L' ⧸ aschbacherSolvableCore 3 L') p e) → False := by
    intro p e _ he h
    refine hSL ⟨p, e, inferInstance, he, ?_⟩
    rcases h with h | h
    · exact Or.inl (isSLThreePiAt_congr eθ.symm h)
    · exact Or.inr (isoLThreePi_congr eθ.symm h)
  rcases h47' with ⟨p, e, _, -, -, -, hf⟩ | ⟨p, e, _, -, he, -, hsl, -⟩ | ⟨-, hf⟩ |
      ⟨n, hn, hsl, -⟩ | ⟨n, -, -, hgf, -⟩
  · exact ⟨a, haA, Or.inl (hk _ hf)⟩
  · exact (hSLq p e he hsl).elim
  · exact ⟨a, haA, Or.inl (hk _ hf)⟩
  · exact (hSLq 2 n hn hsl).elim
  · exact ⟨a, haA, Or.inr (hk _ hgf)⟩

theorem item4_17_of (h45 : Item4_5) (h47 : Item4_7) (hSL3 : Item4_17SL3Pi)
    (hI : Item4_17InnerIn) (hJ : Item4_17InnerOut) : Item4_17 := by
  intro G _ _ hG h2 L hL hstar A E c m hq
  have hAL := hq.le_normalizer h45 hG hL
  by_cases h1 : ∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField
  · exact Or.inl h1
  by_cases hSL : IsSLThreePiTheta L
  · exact hSL3 G hG h2 L hL hstar A E c m hq hAL h1 hSL
  by_cases hout : ∃ a ∈ A, InducesOuterTheta a L
  · obtain ⟨a, haA, ha⟩ := hout
    exact Or.inl (exists_field_of_inducesOuterTheta h47 hG hL hq hSL haA ha)
  push Not at hout
  by_cases hcL : c ∈ L
  · exact hI G hG h2 L hL hstar A E c m hq hAL h1 hSL hout hcL
  · exact hJ G hG h2 L hL hstar A E c m hq hAL h1 hSL hout hcL

end Certs

end CFSG.RankThree.PartTwo.Sec4
