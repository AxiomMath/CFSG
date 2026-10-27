module

public import CFSG.Monster.AxisCount.BabyGroups
public import CFSG.Monster.AxisCount.BabyBalance
public import CFSG.Monster.B.Cbar.SylowTwoAux
public import CFSG.Monster.Existence.TwoB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B
  CFSG.Monster.B.Short

theorem orbit_Jstar_aStarMinus_eq : MulAction.orbit Jstar aStarMinus = {aStarMinus} := by
  ext x
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact fix_aStarMinus_of_mem_Jstar hg
  · rintro rfl
    exact MulAction.mem_orbit_self _

theorem orbit_congr_subgroup {K : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)} (h : K = Cgen) (x : SpaceB) :
    MulAction.orbit K x = MulAction.orbit Cgen x := by
  subst h
  rfl

theorem natCard_Cgen_eq_babyTotal_mul_Jstar {R : Fin 10 → Type*} [∀ i, Fintype (R i)]
    (S : Setup (SpaceB ≃ₗ[ℚ] SpaceB) SpaceB (Fin 10) R)
    (hH : S.H = Jstar) (hτ : S.τ = tauB) (hv₀ : S.v 0 = aStarMinus)
    (hD : ∀ i, Pairwise (Function.onFun Disjoint (S.D i))) (hO : Function.Injective S.orb)
    (hM : S.M = babyM) (hL : S.L = babyL)
    (hcl : ∀ i, S.v i ∈ MulAction.orbit Cgen aStarMinus) :
    Nat.card Cgen = babyTotal * Nat.card Jstar := by
  have hfin : Finite S.H := hH ▸ inferInstance
  have hclos : Subgroup.closure ((S.H : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ∪ {S.τ}) = Cgen := by
    rw [hH, hτ]
    exact closure_Jstar_union_tauB
  have h0 : Nat.card (S.orb 0) = 1 := by
    have e : S.orb 0 = {aStarMinus} := by
      change MulAction.orbit S.H (S.v 0) = _
      rw [hv₀, hH]
      exact orbit_Jstar_aStarMinus_eq
    rw [e, Nat.card_coe_set_eq, Set.ncard_singleton]
  obtain ⟨-, htot⟩ := S.card_orb_eq_babySizes hD hO hM hL h0
  have hX : S.X0 = MulAction.orbit Cgen aStarMinus := by
    have hv : ∀ i, S.v i ∈ MulAction.orbit
        (Subgroup.closure ((S.H : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ∪ {S.τ})) (S.v 0) := by
      intro i
      rw [hclos, hv₀]
      exact hcl i
    have := S.X0_eq_orbit 0 hv
    rw [hv₀] at this
    rw [this]
    exact orbit_congr_subgroup hclos _
  rw [natCard_Cgen_eq_orbit_mul_Jstar, ← hX, htot]

theorem natCard_Jstar :
    Nat.card Jstar = 2 ^ 24 * 42305421312000 := by
  have h := natCard_Gvis_eq_mul_Jstar
  rw [CFSG.Monster.Existence.natCard_Gvis, CFSG.Monster.Existence.twoBCentralizerOrder] at h
  omega

theorem natCard_Cbar_of
    (h : Nat.card Cgen = babyTotal * Nat.card Jstar) :
    Nat.card Cbar = 4154781481226426191177580544000000 := by
  have h2 := CFSG.Monster.B.natCard_Cgen
  rw [h, natCard_Jstar, babyTotal] at h2
  omega

end CFSG.Monster.AxisCount
