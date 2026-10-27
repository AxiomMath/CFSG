module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
import CFSG.HardMathSupport.Timmesfeld.RootAut.Linear

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExcTwo
open CFSG.LieType.Steinberg.Adjoint (iform iform_comm)

theorem frameE7Root_parseval : ∀ k l : Fin Tag.E7.rank,
    (∑ j : Fin 7, iform (Pi.single k 1 : Fin Tag.E7.rank → ℤ) (frameE7Root j) *
      iform (frameE7Root j) (Pi.single l 1 : Fin Tag.E7.rank → ℤ)) =
      2 * iform (Pi.single k 1 : Fin Tag.E7.rank → ℤ) (Pi.single l 1) := by
  decide +kernel

theorem frameE8Root_parseval : ∀ k l : Fin Tag.E8.rank,
    (∑ j : Fin 8, iform (Pi.single k 1 : Fin Tag.E8.rank → ℤ) (frameE8Root j) *
      iform (frameE8Root j) (Pi.single l 1 : Fin Tag.E8.rank → ℤ)) =
      2 * iform (Pi.single k 1 : Fin Tag.E8.rank → ℤ) (Pi.single l 1) := by
  decide +kernel

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {τ : Tag} {d : ℕ}

theorem iform_eq_sum_single_left (x y : Fin τ.rank → ℤ) :
    iform x y = ∑ i, x i * iform (Pi.single i 1 : Fin τ.rank → ℤ) y := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [CFSG.HardMathSupport.Timmesfeld.RootAut.iform_sum_smul_left]

@[expose] def FrameParseval (F : OrthFrame τ d) : Prop :=
  ∀ k l : Fin τ.rank, ∑ j, iform (Pi.single k 1 : Fin τ.rank → ℤ) (F.root j) *
    iform (F.root j) (Pi.single l 1 : Fin τ.rank → ℤ) =
      2 * iform (Pi.single k 1 : Fin τ.rank → ℤ) (Pi.single l 1)

theorem frameE7_parseval : FrameParseval frameE7 := frameE7Root_parseval

theorem frameE8_parseval : FrameParseval frameE8 := frameE8Root_parseval

theorem FrameParseval.sum_eq {F : OrthFrame τ d} (hF : FrameParseval F) (γ : Fin τ.rank → ℤ)
    (l : Fin τ.rank) : ∑ j, iform γ (F.root j) * iform (F.root j) (Pi.single l 1) =
      2 * iform γ (Pi.single l 1) := by
  calc ∑ j, iform γ (F.root j) * iform (F.root j) (Pi.single l 1)
      = ∑ j, ∑ k, γ k * (iform (Pi.single k 1 : Fin τ.rank → ℤ) (F.root j) *
          iform (F.root j) (Pi.single l 1)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [iform_eq_sum_single_left γ (F.root j), Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k, γ k * ∑ j, iform (Pi.single k 1 : Fin τ.rank → ℤ) (F.root j) *
          iform (F.root j) (Pi.single l 1) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
    _ = 2 * iform γ (Pi.single l 1) := by
        rw [iform_eq_sum_single_left γ (Pi.single l 1), Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hF k l]
        ring

@[expose] def frameDual (F : OrthFrame τ d) (γ : Fin τ.rank → ℤ) : Fin (d + 1) → ZMod 3 :=
  fun j => (iform γ (F.root j) : ZMod 3)

@[expose] def frameLift (F : OrthFrame τ d) (v : Fin (d + 1) → ZMod 3) : Fin τ.rank → ℤ :=
  ∑ j, ((v j).val : ℤ) • F.root j

theorem iform_frameLift (F : OrthFrame τ d) (v : Fin (d + 1) → ZMod 3) (δ : Fin τ.rank → ℤ) :
    (iform (frameLift F v) δ : ZMod 3) = v ⬝ᵥ frameDual F δ := by
  rw [frameLift, CFSG.HardMathSupport.Timmesfeld.RootAut.iform_sum_smul_left, dotProduct]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ZMod.natCast_zmod_val, frameDual, iform_comm (F.root j) δ]

theorem zmod3_neg_two_mul (c : ZMod 3) : -(2 * c) = c := by
  revert c
  decide

theorem iform_frameLift_neg_dual {F : OrthFrame τ d} (hF : FrameParseval F) (γ : Fin τ.rank → ℤ)
    (l : Fin τ.rank) :
    (iform (frameLift F (-frameDual F γ)) (Pi.single l 1) : ZMod 3) =
      (iform γ (Pi.single l 1) : ZMod 3) := by
  have h := congrArg (Int.cast : ℤ → ZMod 3) (hF.sum_eq γ l)
  push_cast at h
  rw [iform_frameLift, dotProduct]
  have h4 : ∀ j, (-frameDual F γ) j * frameDual F (Pi.single l 1) j =
      -((iform γ (F.root j) : ZMod 3) * (iform (F.root j) (Pi.single l 1) : ZMod 3)) := by
    intro j
    simp only [Pi.neg_apply, frameDual, iform_comm (Pi.single l 1) (F.root j), neg_mul]
  rw [Finset.sum_congr rfl fun j _ => h4 j, Finset.sum_neg_distrib, h]
  exact zmod3_neg_two_mul _

end CFSG.StandardType.SmallExc

end
