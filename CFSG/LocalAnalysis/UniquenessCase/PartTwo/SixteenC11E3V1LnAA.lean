module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1LnCov
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1LnCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s1611e3_v1_ln3_model {D : Data G} (h : S1611e3Std D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsLn ↥L₀ 3 1) (hL : IsLn ↥(lBar ⊥ V hV L) 3 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    (∀ t ∈ Mbar D.M ⊥ V hV, orderOf t = 2 → 3 ≤ rkIdx (fixV (Subgroup.zpowers t))) ∧
    (∀ E ∈ calABar 2 D.M ⊥ V hV, rk ↥E ≤ 2) ∧
    (∀ E ∈ calABar 3 D.M ⊥ V hV, False) := by
  obtain ⟨Z, hN, hZ, hZne, hcomm, hJ⟩ :=
    s1611e3_v1_ln3_cover h hc hs hsig hK hdir hL₀ hL hsum hV1 hM
  exact s1611e3_v1_ln3_coord (s15_Infra_vtil_sq_eq_one ⊥ V hV) hM hK hdir hL₀ hJ hN hZ hZne
    hcomm

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
