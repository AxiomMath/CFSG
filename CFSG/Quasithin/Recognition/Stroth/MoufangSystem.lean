module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Recognition.Stroth.MoufangT3
public import CFSG.Quasithin.Recognition.Stroth.MoufangFaithful
public import CFSG.GH74.GLS.SP.Pre
public import CFSG.GH74.GLS.SP.Local.SPLFaith
public import CFSG.GH74.GLS.SP.Local.SPLRestrict

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

theorem moufangRankTwoSystem (n : ℕ) : MoufangRankTwoSystem n := by
  intro V _ Γ _ D _ _ _ _ hn hP hT hM hdeg t ht
  letI : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
    moufangCartan_normal (t := t) ht hn hP hT
  let P : PreRankTwoSystem ↥(littleGroup D Γ n) n :=
    { B := moufangB D Γ n t
      N := moufangN D Γ n t
      normal := moufangCartan_normal (t := t) ht hn hP hT
      w₁ := titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
      w₂ := titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
      U := rootU (D := D) (Γ := Γ) (n := n) t
      root := rootL (D := D) (Γ := Γ) (n := n) t
      isTits := isTitsSystem_moufang (t := t) ht hn hP hT hM
      w₁_ne_w₂ := titsW1_ne_titsW2 (t := t) ht hn hP hT hM
      isSplit := isSplit_moufangB (t := t) ht hn hP hT hM hdeg
      isSaturated := isSaturated_moufang (t := t) ht hn hP hT hM
      card_weyl := card_weyl_tits (t := t) ht hn hP hT hM
      three_le := hn
      roots := isRootGroupSystem_moufang (t := t) ht hn hP hT hM }
  let R : RankTwoSystem ↥(littleGroup D Γ n) n :=
    P.toSystem (faithfulOnBuilding_moufang (t := t) ht hn hP hT hM)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi1 hin
    have hmap : ∀ j : ℤ, (R.root j).map (littleGroup D Γ n).subtype =
        rootD (D := D) (Γ := Γ) (n := n) t j :=
      fun j => rootL_map_subtype (t := t) ht hn j
    constructor
    · rw [hmap i, rootD_eq_aptRoot_of_pos (t := t) (by omega)]
    · rw [hmap (-i), rootD_eq_aptRoot_of_nonpos (t := t) (by omega)]
      congr 1
      ring
  · change Subgroup.closure (⋃ i ∈ {i : ℤ | IsRoot n i},
      (rootL (D := D) (Γ := Γ) (n := n) t i : Set ↥(littleGroup D Γ n))) = ⊤
    exact rootL_closure_eq_top (t := t) ht hn hP hT hM
  · rfl
  · change parabolic (moufangB D Γ n t) (moufangN D Γ n t)
      ({titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
        Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) =
      (MulAction.stabilizer D (t (n + 1))).subgroupOf (littleGroup D Γ n)
    exact parabolic_titsW1_eq_stabilizer (t := t) ht hn hP hT hM
  · change parabolic (moufangB D Γ n t) (moufangN D Γ n t)
      ({titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
        Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) =
      (MulAction.stabilizer D (t n)).subgroupOf (littleGroup D Γ n)
    exact parabolic_titsW2_eq_stabilizer (t := t) ht hn hP hT hM

end CFSG.Quasithin.Stroth
