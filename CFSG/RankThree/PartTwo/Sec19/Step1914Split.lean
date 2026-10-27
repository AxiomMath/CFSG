module

public import CFSG.RankThree.PartTwo.Sec19.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step1914Tri : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M →
      L ≤ M ∨
        (Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) ∧
          E = Subgroup.zpowers c ⊔ (E ⊓ L) ∧ Subgroup.zpowers c ⊓ (E ⊓ L) = ⊥) ∨
        Nonempty (L ⧸ CFSG.pCore 2 L ≃* CFSG.Blueprint.NativeSporadic.M12)

@[expose] def Step1914More : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M →
      Sec4.IsExtOf
        (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E))
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))

theorem step1914_of_split (hT : Step1914Tri) (hM : Step1914More) : Step1914 :=
  fun G _ _ A c L E M h => ⟨hT G A c L E M h, hM G A c L E M h⟩

theorem step1914Tri_of_step1914 (h : Step1914) : Step1914Tri :=
  fun G _ _ A c L E M hctx => (h G A c L E M hctx).1

theorem step1914More_of_step1914 (h : Step1914) : Step1914More :=
  fun G _ _ A c L E M hctx => (h G A c L E M hctx).2

theorem step1914_iff_split : Step1914 ↔ Step1914Tri ∧ Step1914More :=
  ⟨fun h => ⟨step1914Tri_of_step1914 h, step1914More_of_step1914 h⟩,
    fun h => step1914_of_split h.1 h.2⟩

end CFSG.RankThree.PartTwo.Sec19
