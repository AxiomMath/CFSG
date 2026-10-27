module

public import CFSG.RankThree.PartTwo.Sec16.Item16Statements
import CFSG.RankThree.PartTwo.Sec15.Item15Steps
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

structure CE162 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y₁ Y₂ S₁ S₂ : Subgroup G) :
    Prop where
  mem₁ : Y₁ ∈ scriptY0Star A LB
  mem₂ : Y₂ ∈ scriptY0Star A LB
  s₁ : S₁ ∈ scriptQPiStar A LB (Subgroup.normalizer (Y₁ : Set G)) (piOf 2)
  s₂ : S₂ ∈ scriptQPiStar A LB (Subgroup.normalizer (Y₂ : Set G)) (piOf 2)
  ne_bot : S₁ ⊓ S₂ ≠ ⊥
  not_conj : ¬ ∃ x ∈ xA A, Y₁ = Y₂.map (MulAut.conj x).toMonoidHom

@[expose] def MaxCE162 (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (Y₁ Y₂ S₁ S₂ : Subgroup G) : Prop :=
  CE162 A LB Y₁ Y₂ S₁ S₂ ∧ ∀ Y₁' Y₂' S₁' S₂' : Subgroup G, CE162 A LB Y₁' Y₂' S₁' S₂' →
    Nat.card (S₁' ⊓ S₂' : Subgroup G) ≤ Nat.card (S₁ ⊓ S₂ : Subgroup G)

omit [Finite G] in
theorem CE162.symm {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y₁ Y₂ S₁ S₂ : Subgroup G}
    (h : CE162 A LB Y₁ Y₂ S₁ S₂) : CE162 A LB Y₂ Y₁ S₂ S₁ := by
  refine ⟨h.mem₂, h.mem₁, h.s₂, h.s₁, by rw [inf_comm]; exact h.ne_bot, ?_⟩
  rintro ⟨x, hx, hxY⟩
  refine h.not_conj ⟨x⁻¹, inv_mem hx, ?_⟩
  rw [hxY, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]

omit [Finite G] in
theorem MaxCE162.symm {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y₁ Y₂ S₁ S₂ : Subgroup G} (h : MaxCE162 A LB Y₁ Y₂ S₁ S₂) :
    MaxCE162 A LB Y₂ Y₁ S₂ S₁ := by
  refine ⟨h.1.symm, fun Y₁' Y₂' S₁' S₂' h' => ?_⟩
  rw [inf_comm S₂ S₁]
  exact h.2 Y₁' Y₂' S₁' S₂' h'

theorem exists_maxCE162 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y₁ Y₂ S₁ S₂ : Subgroup G} (h : CE162 A LB Y₁ Y₂ S₁ S₂) :
    ∃ Y₁' Y₂' S₁' S₂' : Subgroup G, MaxCE162 A LB Y₁' Y₂' S₁' S₂' := by
  set s : Set (Subgroup G × Subgroup G × Subgroup G × Subgroup G) :=
    {p | CE162 A LB p.1 p.2.1 p.2.2.1 p.2.2.2} with hs
  obtain ⟨⟨Y₁', Y₂', S₁', S₂'⟩, hmem, hmax⟩ := Set.exists_max_image s
    (fun p => Nat.card (p.2.2.1 ⊓ p.2.2.2 : Subgroup G)) (Set.toFinite s)
    ⟨(Y₁, Y₂, S₁, S₂), h⟩
  exact ⟨Y₁', Y₂', S₁', S₂', hmem, fun Y₁'' Y₂'' S₁'' S₂'' h'' =>
    hmax (Y₁'', Y₂'', S₁'', S₂'') h''⟩

theorem item162_of_noMaxCE162 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hno : ∀ Y₁ Y₂ S₁ S₂ : Subgroup G, ¬ MaxCE162 A LB Y₁ Y₂ S₁ S₂) : Item162 A LB := by
  intro Y₁ hY₁ Y₂ hY₂ hQ
  obtain ⟨Q, hQ, hQ1⟩ := hQ
  by_contra hnc
  have hQ₁ : Q ∈ scriptQPi A LB (Subgroup.normalizer (Y₁ : Set G)) (piOf 2) :=
    ⟨⟨hQ.1.1, hQ.1.2.trans inf_le_left⟩, hQ.2⟩
  have hQ₂ : Q ∈ scriptQPi A LB (Subgroup.normalizer (Y₂ : Set G)) (piOf 2) :=
    ⟨⟨hQ.1.1, hQ.1.2.trans inf_le_right⟩, hQ.2⟩
  obtain ⟨S₁, hQS₁, hS₁⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A LB (Subgroup.normalizer (Y₁ : Set G)) (piOf 2))) hQ₁
  obtain ⟨S₂, hQS₂, hS₂⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A LB (Subgroup.normalizer (Y₂ : Set G)) (piOf 2))) hQ₂
  have hU : S₁ ⊓ S₂ ≠ ⊥ := fun h0 => hQ1 (le_bot_iff.mp (h0 ▸ le_inf hQS₁ hQS₂))
  obtain ⟨Y₁', Y₂', S₁', S₂', hmax⟩ := exists_maxCE162 ⟨hY₁, hY₂, hS₁, hS₂, hU, hnc⟩
  exact hno Y₁' Y₂' S₁' S₂' hmax

theorem sec15R_of_point {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    {c' : G} {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c') :
    Sec15R G A c' L' :=
  { toSec14Std :=
      { toSec13Data :=
          { toPartTwoStanding := h.toPartTwoStanding
            partTwoS_eq := h.partTwoS_eq
            mem_partTwoF := h.mem_partTwoF
            not_mem_partTwoT := h.not_mem_partTwoT
            zpowers_mem_omegaA := hc'
            mem_lA := hL' }
        hypS_or_hypT := h.hypS_or_hypT
        chosen136 := h.chosen136 }
    hypR := h.hypR }

@[expose] def Step162U (A : Subgroup G) : Prop :=
  ∀ (c : G) (L : Subgroup G), Sec15R G A c L →
    ∀ Y₁ Y₂ S₁ S₂ : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂ → S₁ ≤ S₂

structure Conf162 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L Y₁ Y₂ S : Subgroup G) : Prop where
  maxCE : MaxCE162 A LB Y₁ Y₂ S S
  le_y : L ≤ Y₁
  meets₁ : MeetsY4 A LB L Y₁
  meets₂ : MeetsY4 A LB L Y₂

@[expose] def Step162L (A : Subgroup G) : Prop :=
  ∀ (c : G) (L : Subgroup G), Sec15R G A c L →
    ∀ Y₁ Y₂ S : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S S →
      ∃ (c' : G) (L' Y₁' Y₂' S' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
        Conf162 A (lB A) c' L' Y₁' Y₂' S'

@[expose] def Step162W (A : Subgroup G) : Prop :=
  ∀ (c : G) (L Y₁ Y₂ S : Subgroup G), Sec15R G A c L → Conf162 A (lB A) c L Y₁ Y₂ S →
    ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)

@[expose] def Step162A10 (A : Subgroup G) : Prop :=
  ∀ (c : G) (L Y₁ Y₂ S : Subgroup G), Sec15R G A c L → Conf162 A (lB A) c L Y₁ Y₂ S →
    ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      ∀ Y₃ ∈ scriptY0Star A (lB A), IsEmpty (↥Y₃ ⧸ CFSG.pCore 2 ↥Y₃ ≃* alternatingGroup (Fin 10))

@[expose] def Step162A7 (A : Subgroup G) : Prop :=
  ∀ (c : G) (L Y₁ Y₂ S : Subgroup G), Sec15R G A c L → Conf162 A (lB A) c L Y₁ Y₂ S →
    ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    Nonempty (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 7)) →
    Nonempty (↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7)) → False

theorem a7_of_not_normalizer_le {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
    {L : Subgroup G} (h1514 : Item1514 A LB c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A LB) (hYL : MeetsY4 A LB L Y)
    (hW : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∧
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))) := by
  rcases h1514 Y hY hYL with ⟨-, -, hΩ, -, -⟩ | ⟨h7, -, -, hY'⟩ | ⟨-, -, -, hΩ, -⟩
  · exact absurd (normalizer_le_of_omegaA_eq hΩ) hW
  · exact ⟨h7, hY'⟩
  · exact absurd (normalizer_le_of_omegaA_eq hΩ) hW

theorem rank3II_16_2_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h1514 : ∀ (c' : G) (L' : Subgroup G), Sec15R G A c' L' → Item1514 A (lB A) c' L')
    (hU : Step162U A) (hL : Step162L A) (hW : Step162W A) (hA10 : Step162A10 A)
    (hA7 : Step162A7 A) : Item162 A (lB A) := by
  refine item162_of_noMaxCE162 fun Y₁ Y₂ S₁ S₂ hmax => ?_
  have hS : S₁ = S₂ := le_antisymm (hU c L h Y₁ Y₂ S₁ S₂ hmax)
    (hU c L h Y₂ Y₁ S₂ S₁ hmax.symm)
  subst hS
  obtain ⟨c', L', Y₁', Y₂', S', hc', hL', hconf⟩ := hL c L h Y₁ Y₂ S₁ hmax
  have h' : Sec15R G A c' L' := sec15R_of_point h hc' hL'
  by_cases hWH : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c' : Set G)
  · exact hW c' L' Y₁' Y₂' S' h' hconf hWH
  · obtain ⟨h7, hY₁⟩ := a7_of_not_normalizer_le (h1514 c' L' h') hconf.maxCE.1.mem₁
      hconf.meets₁ hWH
    obtain ⟨-, hY₂⟩ := a7_of_not_normalizer_le (h1514 c' L' h') hconf.maxCE.1.mem₂
      hconf.meets₂ hWH
    have h10 := hA10 c' L' Y₁' Y₂' S' h' hconf hWH h7
    rcases hY₁ with hY₁ | ⟨⟨φ₁⟩⟩
    · rcases hY₂ with hY₂ | ⟨⟨φ₂⟩⟩
      · exact hA7 c' L' Y₁' Y₂' S' h' hconf hWH h7 hY₁ hY₂
      · exact (h10 Y₂' hconf.maxCE.1.mem₂).false φ₂
    · exact (h10 Y₁' hconf.maxCE.1.mem₁).false φ₁

end CFSG.RankThree.PartTwo.Sec16
