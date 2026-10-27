module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerUnitaryJ

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGSecFiveRouteCfg.cornerRowThree_denseNbr_marking (hLJ : GGSecFivePermNbrLabelOfJInput)
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {n : ℕ} (hn : 5 ≤ n) {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {H E : Subgroup ↥L}
    (R : GGQ2Frame.Realization H E (GGQ2Frame.planeEntry .symplectic (n - 1)))
    {u : GGQ2Frame.PlaneRaw.V (n - 1)} (hu : ∀ i, u i ≠ 0)
    {c : GGQ2Frame.PlaneRaw.Code (n - 1)} (hcu : c = .extension u ∨ c = .extension (-u))
    (hc : GGQ2Frame.PlaneRaw.admissible .symplectic c) (hJ : J = (R.component c).map L.subtype)
    {K : Subgroup G} (hK : GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 n eta K) :
    GGInnerDiagOnLabel (fun p lab => lab.tag = .twA ∧ lab.rank = n - 1 ∧ lab.n = 1 ∧
      p ∣ 2 ^ lab.n + 1) 3 Bs K := by
  have h2 : n - 1 - 1 = n - 2 := by omega
  have hc' : (GGQ2Frame.planeEntry .symplectic (n - 1)).admissible c := And.intro (by omega) hc
  refine hR.qTwoOrth_denseNbr_marking hLJ hRig hn h𝒦 hL hK ?_
  rw [← h2]
  rcases hcu with rfl | rfl
  · exact corner_hasLabel_twA_J_of_extension_full R hc' hu hJ
  · exact corner_hasLabel_twA_J_of_extension_full R hc' (fun i => neg_ne_zero.mpr (hu i)) hJ

end CFSG.StandardType

end
