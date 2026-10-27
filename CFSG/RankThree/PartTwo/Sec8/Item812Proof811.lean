module

public import CFSG.RankThree.PartTwo.Sec8.Steps
import CFSG.RankThree.PartTwo.KFacts.K71Residual
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Residual

variable {G : Type} [Group G] [Finite G]

theorem isPerfect_inSubgroup_perfectResidual_sec8 (H : Subgroup G) :
    Group.IsPerfect (inSubgroup perfectResidual H) := by
  have := (CFSG.perfect_residual_characterization (G := H)).2.2.1
  exact Group.IsPerfect.map H.subtype

theorem perfectResidual_inf_centralizer_eq {b e : G} {X Le : Subgroup G}
    (hXb : X ≤ Subgroup.centralizer ({b} : Set G))
    (hLe : Le ≤ Subgroup.centralizer ({e} : Set G))
    (h1 : inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({b} : Set G)) ≤ X)
    (h2 : inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({e} : Set G)) ≤ Le) :
    inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({e} : Set G)) =
      inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have hK₁ : inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({e} : Set G)) ≤
      X ⊓ Subgroup.centralizer ({e} : Set G) := Subgroup.map_subtype_le _
  have hK₂ : inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({b} : Set G)) ≤
      Le ⊓ Subgroup.centralizer ({b} : Set G) := Subgroup.map_subtype_le _
  refine le_antisymm ?_ ?_
  · refine KFacts.le_inSubgroup_perfectResidual (isPerfect_inSubgroup_perfectResidual_sec8 _)
      (le_inf h2 ?_)
    exact (hK₁.trans inf_le_left).trans hXb
  · refine KFacts.le_inSubgroup_perfectResidual (isPerfect_inSubgroup_perfectResidual_sec8 _)
      (le_inf h1 ?_)
    exact (hK₂.trans inf_le_left).trans hLe

end Residual

section Item811


@[expose] def Pair84Sym : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ (e : G) (Le : Subgroup G), PairRel A e Le b X → PairRel A b X e Le

@[expose] def Pair811Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)) →
    ∀ (e : G) (Le : Subgroup G), PairRel A e Le b X → PairRel A b X e Le →
      (IsUnitaryTwo (Le ⧸ aschbacherSolvableCore 3 Le) 3 ∨
        Nonempty (Le ⧸ aschbacherSolvableCore 3 Le ≃* projSp 2 (GaloisField 2 3))) →
      sec8B A X = Subgroup.closure {b, e} ⊔
          (A ⊓ inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({e} : Set G))) ∧
        sec8B A Le = Subgroup.closure {e, b} ⊔
          (A ⊓ inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({b} : Set G)))

theorem item811_of (h87 : Item87) (h89 : Item89) (hsym : Pair84Sym) (hgen : Pair811Gen) :
    Item811 := by
  intro G _ _ A c L a b X n h e Le hrel
  obtain ⟨Y, hY, hIJ⟩ := h87 G A c L a b X n h
  obtain ⟨hX, -, hΩ⟩ := h89 G A c L a b X n h Y hY hIJ
  have hrel' := hsym G A c L a b X n h e Le hrel
  obtain ⟨h1, h2⟩ := hgen G A c L a b X n h hX e Le hrel hrel' (hΩ _ hrel.1)
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := by
    obtain ⟨X', -, rfl⟩ := hrel.2.2.1
    exact Subgroup.map_subtype_le X'
  have hLe : Le ≤ Subgroup.centralizer ({e} : Set G) := by
    obtain ⟨L', -, rfl⟩ := hrel'.2.2.1
    exact Subgroup.map_subtype_le L'
  have hK := perfectResidual_inf_centralizer_eq hXb hLe hrel.2.2.2.1 hrel'.2.2.2.1
  rw [h1, h2, hK, Set.pair_comm]

end Item811

end CFSG.RankThree.PartTwo.Sec8
