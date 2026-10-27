module

public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec16.Item16Tail15

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS

@[expose] noncomputable def KS1617E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → (∃ x ∈ Subgroup.normalizer (A : Set G), x ^ 3 = 1 ∧ x ∉ A) →
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∧
      ∃ E : Subgroup G, c ∈ E ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
        E ≤ Subgroup.normalizer (L : Set G) ∧
        Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
          (Subgroup.zpowers c : Set G) ∧
        Sec4.IsTypeCOn E L ∧ A ≤ E ⊔ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧
        (∀ y ∈ A ⊓ L, y ≠ 1 → ∀ z ∈ A ⊓ L, z ≠ 1 → ∃ l ∈ L, l * y * l⁻¹ = z) ∧
        A ≤ Subgroup.normalizer (E : Set G) ∧
        ∀ a ∈ A, ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ L, w * a * w⁻¹ ∈ E

variable {G : Type} [Group G] [Finite G]

theorem card_thetaCen_conj (w a : G) :
    Nat.card (thetaCen ({w * a * w⁻¹} : Set G)) = Nat.card (thetaCen ({a} : Set G)) := by
  have h1 := map_inSubgroup_aschbacherSolvableCore (MulAut.conj w)
    (Subgroup.centralizer ({a} : Set G))
  rw [map_centralizer_singleton] at h1
  have heq : thetaCen ({w * a * w⁻¹} : Set G) =
      (thetaCen ({a} : Set G)).map (MulAut.conj w).toMonoidHom := by
    rw [thetaCen, thetaCen, h1]
    rfl
  rw [heq, Subgroup.card_map_of_injective (MulAut.conj w).injective]

theorem mem_partTwoS_of_odd {A L : Subgroup G} {c : G} (h : Sec13Data G A c L)
    (hodd : ∀ a ∈ A, a ≠ 1 → Odd (Nat.card (thetaCen ({a} : Set G)))) : A ∈ partTwoS G := by
  refine ⟨h.mem_partTwoF, fun a ha ha1 => ?_, fun B hBA hB9 => ?_⟩
  · have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h.commute hx ha)
    have hAθ : A ≤ Subgroup.normalizer ((thetaCen ({a} : Set G) : Subgroup G) : Set G) :=
      hAC.trans (centralizer_le_normalizer_thetaCen _)
    exact (hodd a ha ha1).of_dvd_nat
      (Subgroup.card_dvd_of_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hAθ))
  · have hBne : B ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hB9
      omega
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
    have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
    exact (hodd b (hBA hb) hb1').of_dvd_nat
      (Subgroup.card_dvd_of_le (thetaT_le_thetaCen hb hb1'))

theorem step1617_of (hE : KS1617E) (h138 : Item138N) (h1614 : Step1614) : Step1617 := by
  intro G _ _ A c L h x hxW hx3
  by_contra hxA
  obtain ⟨hL3, E, hcE, hEe, hE27, hEN, hEsec, hEC, hAEL, hAL9, hfus, hANE, hfuse⟩ :=
    hE G A c L h ⟨x, hxW, hx3, hxA⟩
  by_cases hE𝓔 : E ∈ partTwoE G
  · have hreach : E ∈ reachE A := ⟨hE𝓔, Relation.ReflTransGen.single ⟨h.toSec13Data.mem_partTwoE,
      hE𝓔, ⟨Subgroup.zpowers c, h.zpowers_mem_omegaA, Subgroup.zpowers_le.mpr hcE⟩⟩⟩
    have hTE : HypT E := hypT_of_mem_reachE h.toTheoremFourHyp h.partTwoS_eq h.hypR hreach
    obtain ⟨-, -, hF138⟩ := h138 G A c L h.toSec13Data hL3 E hcE hEe hE27 hEN hEsec
      (Or.inr hTE) hEC
    obtain ⟨-, hΩA⟩ := hF138 A hAEL h.isElemAbelian h.card_eq hAL9 hfus hANE
    obtain ⟨-, hΩ9⟩ := hΩA h.hypS_or_hypT
    rw [h1614 G A c L h, Set.ncard_singleton] at hΩ9
    omega
  · have hoddE : ∀ e ∈ E, e ≠ 1 → Odd (Nat.card (thetaCen ({e} : Set G))) := by
      intro e he _
      by_contra hev
      have hEC' : E ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr
          (by simpa using congrArg Subtype.val (hEe.1.is_comm.comm ⟨y, hy⟩ ⟨e, he⟩))
      exact hE𝓔 (mem_partTwoE_of_thetaCen hEe hE27 hEC' hev)
    have hodd : ∀ a ∈ A, a ≠ 1 → Odd (Nat.card (thetaCen ({a} : Set G))) := by
      intro a ha ha1
      obtain ⟨w, -, hwa⟩ := hfuse a ha
      have hwa1 : w * a * w⁻¹ ≠ 1 := by
        intro h1
        apply ha1
        calc a = w⁻¹ * (w * a * w⁻¹) * w := by group
          _ = 1 := by rw [h1]; group
      have h1 := hoddE _ hwa hwa1
      rwa [card_thetaCen_conj] at h1
    have hS := mem_partTwoS_of_odd h.toSec13Data hodd
    rw [h.partTwoS_eq] at hS
    simp at hS

end CFSG.RankThree.PartTwo.Sec16
