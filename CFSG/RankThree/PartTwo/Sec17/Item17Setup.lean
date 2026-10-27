module

public import CFSG.RankThree.PartTwo.Sec16.Item16Statements
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

variable {G : Type} [Group G] [Finite G]

@[expose] def Claim17M (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y₀ ∈ scriptY0Star A LB, scriptY0Star A LB = {Y₀} →
    CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) =
      {Subgroup.normalizer (Y₀ : Set G)}

structure Sec17Std (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G) :
    Prop extends Sec15R G A c L where
  mem_y0Star : Y₀ ∈ scriptY0Star A (lB A)
  y0Star_eq : scriptY0Star A (lB A) = {Y₀}
  normalizer_le : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Y₀ : Set G)
  qStar_le : ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), S ≤ Subgroup.normalizer (Y₀ : Set G)
  le_y0 : L ≤ Y₀
  a10_or_omega : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) ∨
    omegaA A = {Subgroup.zpowers c}
  normalizer_c_le : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
    Subgroup.normalizer (Y₀ : Set G)
  scriptM_eq : CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) =
    {Subgroup.normalizer (Y₀ : Set G)}
  not_l34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
    CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))

theorem exists_sec17Std {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h169 : Item169 A (lB A) L) (h163 : Item163 A (lB A) c L) (h164 : Item164 A (lB A) c)
    (hM : Claim17M A (lB A)) : ∃ Y₀ : Subgroup G, Sec17Std G A c L Y₀ := by
  obtain ⟨⟨Y, hY⟩, hL34⟩ := h169
  obtain ⟨Y₀, -, hY₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hY
  obtain ⟨hW, hS, hstar, hLY, h5⟩ := h163 Y₀ hY₀
  exact ⟨Y₀, ⟨h, hY₀, hstar, hW, hS, hLY, h5, h164 Y₀ hY₀, hM Y₀ hY₀ hstar, hL34⟩⟩

theorem Sec17Std.eq_of_mem_y0Star {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) : Y = Y₀ := by
  have := h.y0Star_eq ▸ hY
  exact this

end CFSG.RankThree.PartTwo.Sec17
