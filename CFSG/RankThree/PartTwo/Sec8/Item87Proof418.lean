module

import CFSG.RankThree.PartTwo.KFacts.KS44Transport
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartTwo.Sec8.Pairs

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def IsType418 (X : Type) [Group X] (n : ℕ) : Prop :=
  IsoSUThree X (2 ^ (3 * n)) ∨ Nonempty (X ≃* projSL 2 (GaloisField 2 (3 * n))) ∨
    Nonempty (X ≃* projSL 3 (GaloisField 2 (3 * n)))

theorem IsType418.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : IsType418 Y n) : IsType418 X n := by
  rcases h with ⟨K, hK, hKf, hc, ⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl ⟨K, hK, hKf, hc, ⟨e.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨e.trans f⟩)
  · exact Or.inr (Or.inr ⟨e.trans f⟩)


@[expose] def Item418Theta : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → 3 ∣ Nat.card (Subgroup.center G) →
    ∀ a b : G, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → b ≠ 1 → a ∉ Subgroup.zpowers b →
    ∀ L ∈ thetaComponents 3 G, ∀ K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}),
    ∀ n : ℕ, 1 ≤ n → IsType418 (K ⧸ aschbacherSolvableCore 3 K) n →
      KFacts.InducesStdKind K a .field →
      (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) ∧
        ¬ (KFacts.InducesStdKind L b .field ∨ KFacts.InducesStdKind L b .graphField)

namespace Item87Proof

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_mem_thetaComponentsIn {D M K : Subgroup G} {M' : Subgroup D}
    (hM' : M'.map D.subtype = M) (hK : K ∈ thetaComponentsIn M) :
    K.subgroupOf D ∈ thetaComponentsIn M' := by
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  set e : M' ≃* M := (M'.equivMapOfInjective D.subtype D.subtype_injective).trans
    (MulEquiv.subgroupCongr hM') with he
  have he' : ∀ z : M', ((e z : M) : G) = ((z : D) : G) := fun _ => rfl
  have hmem := map_mulEquiv_mem_thetaComponents Nat.prime_three e.symm hK'
  have hle : K.subgroupOf D ≤ M' := by
    intro z hz
    have hz' : (z : G) ∈ M := hKM (Subgroup.mem_subgroupOf.mp hz)
    rw [← hM'] at hz'
    obtain ⟨w, hw, hwz⟩ := hz'
    have : w = z := Subtype.ext hwz
    rwa [← this]
  refine mem_thetaComponentsIn_iff.mpr ⟨hle, ?_⟩
  convert hmem using 1
  ext z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · intro hz
    refine ⟨e z, ?_, by simp⟩
    change e z ∈ K.subgroupOf M
    rw [Subgroup.mem_subgroupOf, he']
    exact hz
  · rintro ⟨w, hw, hwz⟩
    have hez : e z = w := by
      rw [← hwz]
      simp
    change w ∈ K.subgroupOf M at hw
    rw [Subgroup.mem_subgroupOf, ← hez, he'] at hw
    exact hw

theorem item418_centralizer (h418 : Item418Theta) (hG : TheoremFourHyp G) {f a b : G}
    (hf3 : f ^ 3 = 1) (hf1 : f ≠ 1) (haf : a ∈ Subgroup.centralizer ({f} : Set G))
    (hbf : b ∈ Subgroup.centralizer ({f} : Set G)) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a) (hb1 : b ≠ 1) (habz : a ∉ Subgroup.zpowers b) {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 f) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b})) {n : ℕ} (hn : 1 ≤ n)
    (htype : IsType418 (K ⧸ aschbacherSolvableCore 3 K) n)
    (hKa : KFacts.InducesStdKind K a .field) :
    (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) ∧
      ¬ (KFacts.InducesStdKind L b .field ∨ KFacts.InducesStdKind L b .graphField) := by
  set D := Subgroup.centralizer ({f} : Set G) with hD
  have hS4 : SectionFourHyp D := hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG hf1)
  obtain ⟨hLD, hL'⟩ := PartOne.mem_thetaComponentsAt_iff.mp hL
  set f' : D := ⟨f, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hf'
  set a' : D := ⟨a, haf⟩ with ha'
  set b' : D := ⟨b, hbf⟩ with hb'
  have hf'Z : f' ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp z.2)
  have hZ3 : 3 ∣ Nat.card (Subgroup.center D) := by
    have h1 : orderOf (⟨f', hf'Z⟩ : Subgroup.center D) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hf3 hf1
    rw [← h1]
    exact orderOf_dvd_natCard _
  have ha'3 : a' ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have ha'b' : a' * b' = b' * a' := Subtype.ext hab
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have ha'z : a' ∉ Subgroup.zpowers b' := by
    rintro ⟨k, hk⟩
    exact habz ⟨k, by simpa [hb', ha'] using congrArg Subtype.val hk⟩
  set L' := L.subgroupOf D with hL'def
  have hL'map : L'.map D.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLD
  set M' := L' ⊓ Subgroup.centralizer ({b'} : Set D) with hM'
  have hM'map : M'.map D.subtype = L ⊓ Subgroup.centralizer {b} := by
    rw [hM', Subgroup.map_inf _ _ _ D.subtype_injective, hL'map,
      GroupTheory.SteinbergBY.map_subtype_centralizer_singleton D b', ← inf_assoc,
      inf_eq_left.mpr hLD]
  have hK'mem : K.subgroupOf D ∈ thetaComponentsIn M' := subgroupOf_mem_thetaComponentsIn hM'map hK
  have hKD : K ≤ D :=
    (le_of_mem_thetaComponentsIn hK).trans (inf_le_left.trans hLD)
  set K' := K.subgroupOf D with hK'def
  have hK'map : K'.map D.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKD
  have htype' : IsType418 (K' ⧸ aschbacherSolvableCore 3 K') n :=
    IsType418.of_mulEquiv (Sec14.quotThetaEquiv (Subgroup.subgroupOfEquivOfLe hKD)) htype
  have hθK := KFacts.thetaQuotMap_iff_of_injective D.subtype D.subtype_injective K'
  have ha'N : a' ∈ Subgroup.normalizer (K' : Set D) := by
    have h := hKa.mem_normalizer
    rw [← hK'map] at h
    exact (Sec13.coe_mem_normalizer_map_iff D).mp h
  have hK'a : KFacts.InducesStdKind K' a' .field := by
    refine KFacts.InducesStdKind.of_map D.subtype K' hθK ha'N ?_
    rw [hK'map]
    exact hKa
  obtain ⟨h1, h2⟩ := h418 D hS4 hZ3 a' b' ha'3 hb'3 ha'b' hb'1 ha'z L' hL' K' hK'mem n hn htype'
    hK'a
  refine ⟨?_, ?_⟩
  · rcases h1 with h | h
    · have := Sec13.inducesStdKind_sub D L' h
      rw [hL'map] at this
      exact Or.inl this
    · have := Sec13.inducesStdKind_sub D L' h
      rw [hL'map] at this
      exact Or.inr this
  · have hθL := KFacts.thetaQuotMap_iff_of_injective D.subtype D.subtype_injective L'
    rintro (h | h)
    · have hbN : b' ∈ Subgroup.normalizer (L' : Set D) := by
        have h' := h.mem_normalizer
        rw [← hL'map] at h'
        exact (Sec13.coe_mem_normalizer_map_iff D).mp h'
      refine h2 (Or.inl (KFacts.InducesStdKind.of_map D.subtype L' hθL hbN ?_))
      rw [hL'map]
      exact h
    · have hbN : b' ∈ Subgroup.normalizer (L' : Set D) := by
        have h' := h.mem_normalizer
        rw [← hL'map] at h'
        exact (Sec13.coe_mem_normalizer_map_iff D).mp h'
      refine h2 (Or.inr (KFacts.InducesStdKind.of_map D.subtype L' hθL hbN ?_))
      rw [hL'map]
      exact h

end Item87Proof

end CFSG.RankThree.PartTwo.Sec8
