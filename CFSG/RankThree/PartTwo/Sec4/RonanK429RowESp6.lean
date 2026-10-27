module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowETools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6 card_H6)
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Open (StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Matrix
open scoped Matrix

namespace Sp6

abbrev ι6 : Type := Fin 3 ⊕ Fin 3

@[expose] def matH : H6 →* Matrix ι6 ι6 (ZMod 2) :=
  (Units.coeHom (Matrix ι6 ι6 (ZMod 2))).comp (StatedSp 3 (ZMod 2)).subtype

theorem matH_injective : Function.Injective matH := by
  intro g h e
  exact Subtype.ext (Units.ext e)

@[expose] def bM : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def bMi : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def y0M : Matrix ι6 ι6 (ZMod 2) := fromBlocks bM 0 0 bMiᵀ

@[expose] def y0Mi : Matrix ι6 ι6 (ZMod 2) := fromBlocks bMi 0 0 bMᵀ

theorem y0M_mul_y0Mi : y0M * y0Mi = 1 := by decide +kernel

theorem y0Mi_mul_y0M : y0Mi * y0M = 1 := by decide +kernel

theorem y0M_sp : y0Mᵀ * fromBlocks 0 1 (-1) 0 * y0M = fromBlocks 0 1 (-1) 0 := by
  decide +kernel

@[expose] def y0 : H6 :=
  ⟨⟨y0M, y0Mi, y0M_mul_y0Mi, y0Mi_mul_y0M⟩,
    CFSG.Open.StatedAPI.mem_statedSp_iff.mpr y0M_sp⟩

theorem matH_y0 : matH y0 = y0M := rfl

theorem y0M_pow_seven : y0M ^ 7 = 1 := by decide +kernel

theorem y0M_ne_one : y0M ≠ 1 := by decide +kernel

theorem orderOf_y0 : orderOf y0 = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime (matH_injective ?_) fun h => y0M_ne_one ?_
  · rw [map_pow, matH_y0, y0M_pow_seven, map_one]
  · rw [← matH_y0, h, map_one]

@[expose] def v6 : ι6 → ZMod 2 := fun i => if i = Sum.inl 0 ∨ i = Sum.inr 0 then 1 else 0

@[expose] def ex6 : ι6 → ℕ
  | Sum.inl i => i
  | Sum.inr i => 3 + i

@[expose] def kr6 : Matrix ι6 ι6 (ZMod 2) := Matrix.of fun i j => (y0M ^ ex6 j *ᵥ v6) i

@[expose] def kr6i : Matrix ι6 ι6 (ZMod 2) :=
  fromBlocks !![1, 0, 1; 1, 1, 1; 1, 1, 0] !![0, 0, 1; 1, 1, 1; 1, 0, 0]
    !![0, 1, 0; 1, 0, 0; 0, 1, 1] !![0, 1, 1; 1, 1, 0; 0, 1, 0]

theorem kr6i_mul_kr6 : kr6i * kr6 = 1 := by decide +kernel

theorem commute_y0_check :
    ∀ w : ι6 → ZMod 2, krylovPoly y0M kr6i ex6 w ^ 3 = 1 → krylovPoly y0M kr6i ex6 w = 1 := by
  decide +kernel

theorem eq_one_of_commute_y0 (s : H6) (hs : s * y0 = y0 * s) (h3 : s ^ 3 = 1) : s = 1 := by
  have hm : matH s * y0M = y0M * matH s := by
    rw [← matH_y0, ← map_mul, ← map_mul, hs]
  have heq := eq_krylovPoly_of_commute (kr := kr6) (kr' := kr6i) (v := v6) (e := ex6)
    (fun _ _ => rfl) kr6i_mul_kr6 hm
  have h3' : krylovPoly y0M kr6i ex6 (matH s *ᵥ v6) ^ 3 = 1 := by
    rw [← heq, ← map_pow, h3, map_one]
  apply matH_injective
  rw [map_one, heq]
  exact commute_y0_check _ h3'

theorem not_sq_seven_dvd : ¬ 7 ^ 2 ∣ Nat.card H6 := by
  rw [card_H6]
  norm_num

theorem good429_H6 (x : H6) (hx : orderOf x = 3) :
    Good429 (Subgroup.centralizer ({x} : Set H6)) := by
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have h7 := not_dvd_card_centralizer_of_sylow (by norm_num) orderOf_y0 not_sq_seven_dvd
    eq_one_of_commute_y0 hx3 hx1
  refine good429_of_not_dvd (N := 1451520) (B := 114)
    (card_H6 ▸ Subgroup.card_subgroup_dvd_card _) (by norm_num) (by norm_num) [7]
    (by simpa using h7) (by decide +kernel)

end Sp6

theorem noCfgS429_sp62 {S : Type} [Group S] [Finite S] (hna : ∃ a b : S, a * b ≠ b * a)
    [IsSimpleGroup S] (e : S ≃* projSp 3 (GaloisField 2 1)) : NoCfgS429 S := by
  let φ : S ≃* H6 := e.trans Item434SmallTwoIII.sp62Equiv
  have hout : ¬ 3 ∣ Nat.card (Outer H6) := by
    rw [Item434SmallTwoIII.card_outer_H6]
    norm_num
  exact noCfgS429_of_model φ (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv φ hout) Sp6.good429_H6

theorem eight_Sp6 : RowSOf429 (projSp 3 (GaloisField 2 1)) :=
  rowSOf429_of_noCfg fun S _ _ hs hna ⟨e⟩ => by
    haveI := hs
    exact noCfgS429_sp62 hna e

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
