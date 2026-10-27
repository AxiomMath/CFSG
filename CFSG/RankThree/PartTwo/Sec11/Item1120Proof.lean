module

public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
public import CFSG.RankThree.PartTwo.Sec11.Steps
public import CFSG.RankThree.PartTwo.Sec11.Item1119ProofBasic
import CFSG.RankThree.PartTwo.Sec11.Item1116NoFifteen

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section Statements

@[expose] def Step1120V0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s} →
      g ∈ Subgroup.normalizer ((Subgroup.closure {s, a, x ^ 3} : Subgroup G) : Set G)

end Statements

namespace Item1120Proof

open Item1119Proof

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem R_le_normalizer_V (h45 : Sec4.Item4_5) (h113 : Item113)
    (h : Sec11Data G A c L a R Y d x s r g) :
    R ≤ Subgroup.normalizer ((Subgroup.closure {s, x, a} : Subgroup G) : Set G) := by
  set V := Subgroup.closure ({s, x, a} : Set G) with hV
  obtain ⟨hrR, -, -⟩ := Item1116Proof.mem_R h
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have hxV : x ∈ V := Subgroup.subset_closure (by simp)
  have haV : a ∈ V := Subgroup.subset_closure (by simp)
  have hcV : c ∈ V := Subgroup.zpowers_le.mpr hsV h.c_mem_zpowers_s
  have hsxV : Subgroup.closure ({s, x} : Set G) ≤ V := by
    rw [Subgroup.closure_le]
    rintro y (hy | hy) <;> rw [hy]
    exacts [hsV, hxV]
  have hcaV : Subgroup.closure ({c, a} : Set G) ≤ V := by
    rw [Subgroup.closure_le]
    rintro y (hy | hy) <;> rw [hy]
    exacts [hcV, haV]
  have hr1 := h.R_le_normalizer_V h45 hrR
  have hr2 : r ∈ Subgroup.normalizer ((Subgroup.closure {c, a} : Subgroup G) : Set G) :=
    h.closure_rs_le_normalizer h45 h113 (Subgroup.subset_closure (by simp))
  have hrV : r ∈ Subgroup.normalizer (V : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have hle : Subgroup.closure ({s, x, a} : Set G) ≤ V.comap (MulAut.conj r).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      change r * w * r⁻¹ ∈ V
      rcases hw with hw | hw | hw <;> rw [hw]
      · exact hsxV ((Subgroup.mem_normalizer_iff.mp hr1 _).mp (Subgroup.subset_closure (by simp)))
      · exact hsxV ((Subgroup.mem_normalizer_iff.mp hr1 _).mp (Subgroup.subset_closure (by simp)))
      · exact hcaV ((Subgroup.mem_normalizer_iff.mp hr2 _).mp (Subgroup.subset_closure (by simp)))
    exact hle hz
  rw [h.R_eq, Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with hy | hy | hy <;> rw [hy]
  · exact hrV
  · exact Subgroup.le_normalizer hxV
  · exact Subgroup.le_normalizer hsV

theorem closure_eq_R (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    Subgroup.closure ({s, x, a} : Set G) = R := by
  rw [Item1116NoFifteen.R_eq_of_closure_eq h hrs]
  congr 1
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

end Data

end Item1120Proof

end CFSG.RankThree.PartTwo.Sec11
