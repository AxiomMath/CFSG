module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS

@[expose] noncomputable def KS1615EF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Sec8.IsZ3PGLThreePi ↥(lBarA c L A) →
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∧
      ∃ E F : Subgroup G, c ∈ E ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
        E ≤ Subgroup.normalizer (L : Set G) ∧
        Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
          (Subgroup.zpowers c : Set G) ∧
        Sec4.IsTypeCOn E L ∧ Subgroup.zpowers c ⊔ (A ⊓ L) ≤ E ⊓ F ∧
        F ≤ E ⊔ L ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧
        Nat.card (F ⊓ L : Subgroup G) = 9 ∧
        (∀ y ∈ F ⊓ L, y ≠ 1 → ∀ z ∈ F ⊓ L, z ≠ 1 → ∃ l ∈ L, l * y * l⁻¹ = z) ∧
        F ≤ Subgroup.normalizer (E : Set G)

variable {G : Type} [Group G] [Finite G]

theorem mem_partTwoE_of_thetaCen {E : Subgroup G} {X : Set G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEX : E ≤ Subgroup.centralizer X) (hev : ¬ Odd (Nat.card (thetaCen X))) :
    E ∈ partTwoE G := by
  obtain ⟨-, -, hc3, -⟩ := solvable_prime_complement_core_characterization
    (H := ↥(Subgroup.centralizer X)) Nat.prime_three
  have hΘ3 : ¬ 3 ∣ Nat.card (thetaCen X) := by
    change ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 ↥(Subgroup.centralizer X)).map
      (Subgroup.centralizer X).subtype)
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hc3
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  have hEN : E ≤ Subgroup.normalizer ((thetaCen X : Subgroup G) : Set G) :=
    hEX.trans (centralizer_le_normalizer_thetaCen X)
  have h2 : 2 ∣ Nat.card (thetaCen X) := by
    rcases Nat.even_or_odd (Nat.card (thetaCen X)) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hev
  obtain ⟨T, hET, hT1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two E (thetaCen X) hE3 hEN
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hΘ3) h2
  exact ⟨hE, hE27, _, hT1, T.isPGroup'.map _, hET⟩

end CFSG.RankThree.PartTwo.Sec16
