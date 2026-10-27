module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaNormalizerIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The equation-(8) index parameters
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The source parameters
`u = |U:N_U(A)|` and `p0 = |N_U(A):N_U(P)|`, together with the index-tower
factorization of `|U:U∩M|`. -/
public structure SecondCaseLinearIndexParameters
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    {d : SecondCaseComponentData w}
    (od : SecondCaseLinearOmegaData c w d) where
  u : ℕ
  p0 : ℕ
  u_def : u = (normalizerIn c.U od.A).relIndex c.U
  p0_def : p0 = (normalizerIn c.U od.P).relIndex (normalizerIn c.U od.A)
  index_factor : (c.U ⊓ w.M).relIndex c.U = u * p0
  u_pos : 0 < u
  p0_pos : 0 < p0
  u_le_p : u ≤ od.p

/-- Construct the equation-(8) index parameters from the proved normalizer
containment and normalizer-index bound. -/
public noncomputable def secondCase_linearIndexParameters
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (hsS : (od.s : G) ∈ (c.S : Subgroup G))
    (hsS0 : (od.s : G) ∉ c.S0)
    (hS0centU : (c.S0 : Subgroup G) ≤
      Subgroup.centralizer (c.U : Set G)) :
    SecondCaseLinearIndexParameters c w od := by
  classical
  let NP : Subgroup G := normalizerIn c.U od.P
  let NA : Subgroup G := normalizerIn c.U od.A
  let u : ℕ := NA.relIndex c.U
  let p0 : ℕ := NP.relIndex NA
  have hNPleNA : NP ≤ NA := by
    simpa [NP, NA] using secondCase_linear_omega_NU_P_le_NU_A c w d od
  have hNAleU : NA ≤ c.U := inf_le_left
  have hfactor0 : NP.relIndex NA * NA.relIndex c.U = NP.relIndex c.U :=
    Subgroup.relIndex_mul_relIndex NP NA c.U hNPleNA hNAleU
  have hNPeq : NP = c.U ⊓ w.M :=
    secondCase_linear_omega_NU_P_eq_U_inter_M c w d od
  have hfactor : (c.U ⊓ w.M).relIndex c.U = u * p0 := by
    calc
      (c.U ⊓ w.M).relIndex c.U = NP.relIndex c.U := by rw [hNPeq]
      _ = NP.relIndex NA * NA.relIndex c.U := hfactor0.symm
      _ = u * p0 := by
        simp only [u, p0]
        exact Nat.mul_comm _ _
  have huPos : 0 < u := by
    rw [show u = (NA.subgroupOf c.U).index by rfl, Subgroup.index_eq_card]
    exact Nat.card_pos
  have hp0Pos : 0 < p0 := by
    rw [show p0 = (NP.subgroupOf NA).index by rfl, Subgroup.index_eq_card]
    exact Nat.card_pos
  have huLe : u ≤ od.p := by
    simpa [u, NA] using secondCase_linear_omega_normalizerIndex_le_p
      hmin c w d od hsS hsS0 hS0centU
  exact
    { u := u
      p0 := p0
      u_def := rfl
      p0_def := rfl
      index_factor := hfactor
      u_pos := huPos
      p0_pos := hp0Pos
      u_le_p := huLe }

end CFSG.GorensteinWalter
