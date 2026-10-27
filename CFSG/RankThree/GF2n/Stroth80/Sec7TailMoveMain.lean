module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveYConj
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveYCommute
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveFar
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveConjInL
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveLComm
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveNormalizer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Group X]
  [Finite X] {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

theorem MoveFrame.sec717Move_frame (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hK : ∀ a ∈ V, h * a * h⁻¹ ∈ normalizer (V : Set X))
    (hN : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb) :
    ∃ n ∈ normalizer (L : Set X), n ∉ normalizer (V : Set X) := by
  have hcomm := F.Y_comm_V h hK hN
  have hVY := F.Y_inf_V h hK hN
  have hRb := F.Y_le_Rb h hK hN
  have hInf := F.Y_inf_Nb h hK hN
  have hnc := F.Y_not_conj_into_V h hN hcomm hRb hVY
  have hVnot := F.Y_hVnot h hnc
  have hYx := F.Y_commute_Yx h hK hN hcomm hRb hVnot
  have hfar := F.Y_x_le_NbY h hK hN hcomm hRb hYx
  obtain ⟨a, ha, ha1⟩ := F.exists_ne_one
  have hex : ∃ x ∈ L, x * (h * a * h⁻¹) * x⁻¹ ≠ h * a * h⁻¹ := by
    by_contra hcon
    push Not at hcon
    have hyL : h * a * h⁻¹ ∈ L := by
      refine F.CL _ (hRb a ha) (fun l hl => ?_)
      have := hcon l hl
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    exact ha1 (hInf a ha (F.L_le_Nb hyL))
  obtain ⟨x, hxL, hxy⟩ := hex
  obtain ⟨s, hs, hs1, g, hgL, hgV⟩ :=
    F.exists_conj_in_L h hK hRb hInf hVnot hfar a ha ha1 x hxL hxy
  obtain ⟨hNg, hcomm'⟩ := F.L_comm_Vg s g hs hs1 hgL hgV
  have hLNb := F.L_le_Nbg s g hs hs1 hgL hgV hNg hcomm'
  exact F.normalizer_move s g hs hs1 hgL hgV hcomm' hLNb

end CFSG.RankThree.GF2n.Stroth80
