module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedF4ClassDefs
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane
public import CFSG.LocalAnalysis.StandardType.GGLieCoreCent
public import CFSG.LocalAnalysis.StandardType.GGSixA6F4ClsSpComp
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.StandardType.LieCore

theorem ggA6F4_three
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {G : Type} [Group G] [Finite G]
    (e : G ≃* ↥(adjointGroup .F4 K)) (x : G) (hx : orderOf x = 3) (L : Subgroup G)
    (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G))) :
    Nonempty (↥L ≃* ↥(CFSG.SeitzReduction.F4Pilot.C3Levi K)) := by
  have hx' : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq, hx]
  have hcent : (Subgroup.centralizer ({x} : Set G)).map (e : G →* ↥(adjointGroup .F4 K)) =
      Subgroup.centralizer ({e x} : Set ↥(adjointGroup .F4 K)) := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      simpa using congrArg e hz
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      apply e.injective
      simpa using hy
  have hL' : CFSG.Open.IsComponentOf (L.map (e : G →* ↥(adjointGroup .F4 K)))
      (Subgroup.centralizer ({e x} : Set ↥(adjointGroup .F4 K))) := by
    have h0 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e
      ((CFSG.Assembly.isComponentOf_iff_open).1 hL)
    rwa [hcent] at h0
  obtain ⟨F, hFfield, hFfinite, hFcard, ⟨φ⟩⟩ :=
    ggA6F4_comp_iso_sp (K := K) hK (e x) hx' (L.map (e : G →* ↥(adjointGroup .F4 K))) hL'
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hcard : Fintype.card F = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hFcard, hK]
  let eFK : F ≃+* K := FiniteField.ringEquivOfCardEq hcard
  exact ⟨(Subgroup.equivMapOfInjective L (e : G →* ↥(adjointGroup .F4 K)) e.injective).trans
    (φ.trans ((CFSG.SeitzReduction.F4Pilot.statedSpCongr eFK 3).trans
      (CFSG.SeitzReduction.F4Pilot.c3LeviEquiv K)))⟩

end CFSG.StandardType.A6Red
