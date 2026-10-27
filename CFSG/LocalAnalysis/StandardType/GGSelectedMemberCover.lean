module

public import CFSG.LocalAnalysis.StandardType.GGLieOddCoverSplit
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IPerfect
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoE7D6
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplit

public section

namespace CFSG.StandardType.SelectedMemberCover

open CFSG.LieType.Universal CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag StatedLieAdmissible)


theorem exists_ordinary_source_cover
    {U C : Type} [Group U] [Group C] [Finite U] (pi : U →* C)
    (hpiker : pi.ker ≤ Subgroup.center U) (hpiodd : Odd (Nat.card pi.ker))
    {M : Subgroup U} [Group.IsPerfect ↥M] {t : StatedLieTag} {n f : ℕ}
    (ht : GGPosTag t) (hadm : StatedLieAdmissible t n 2 f)
    (rho : (ggU t n f).K →* ↥(M.map pi)) (hrho : Function.Surjective rho)
    (hrhoker : rho.ker ≤ Subgroup.center (ggU t n f).K) :
    ∃ Phi : (ggU t n f).K →* U,
      Phi.range = M ∧ Phi.ker ≤ Subgroup.center (ggU t n f).K ∧
      pi.comp Phi = (M.map pi).subtype.comp rho := by
  let piM : ↥M →* ↥(M.map pi) := pi.subgroupMap M
  have hpiM : Function.Surjective piM := pi.subgroupMap_surjective M
  have hkerM : piM.ker ≤ Subgroup.center ↥M := by
    rw [show piM.ker = pi.ker.subgroupOf M from Subgroup.ker_subgroupMap M pi]
    intro m hm
    have hz : (m : U) ∈ Subgroup.center U := hpiker hm
    apply Subgroup.mem_center_iff.mpr
    intro m'
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz (m' : U))
  have hoddM : Odd (Nat.card piM.ker) := by
    rw [show piM.ker = pi.ker.subgroupOf M from Subgroup.ker_subgroupMap M pi]
    exact Odd.of_dvd_nat hpiodd
      (Subgroup.card_comap_dvd_of_injective pi.ker M.subtype M.subtype_injective)
  letI : Finite (ggU t n f).K := LieKnownR2.OddCenter.finite_ggU ht hadm
  obtain ⟨PhiM, hcomm, hsurj, -⟩ :=
    CFSG.SeitzReduction.SeitzQ2.exists_surjective_of_oddCentralSplit
      (β := rho) (η := piM) (LieOddCover.oddCentralSplit_ggU_pos ht hadm)
      hrho hpiM hkerM hoddM
  have hker : PhiM.ker ≤ Subgroup.center (ggU t n f).K := by
    intro z hz
    apply hrhoker
    change rho z = 1
    rw [← hcomm z, show PhiM z = 1 from hz, map_one]
  refine ⟨M.subtype.comp PhiM, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · rw [MonoidHom.ker_comp_of_injective PhiM M.subtype M.subtype_injective]
    exact hker
  · ext z
    exact congrArg Subtype.val (hcomm z)

end CFSG.StandardType.SelectedMemberCover

namespace CFSG.StandardType.SelectedMemberCover

open CFSG.LieType.Universal CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.SelectedRoot CFSG.StandardType.RankOneXfer
open CFSG.Open (StatedLieTag StatedLieAdmissible)


theorem selected_of_native_member
    {U C G : Type} [Group U] [Group C] [Group G] [Finite U]
    (D : UniversalRootDatum U) (pi : U →* C)
    (hpiker : pi.ker ≤ Subgroup.center U) (hpiodd : Odd (Nat.card pi.ker))
    (psi : U →* G) (hpsiker : psi.ker ≤ Subgroup.center U)
    {M : Subgroup U} [Group.IsPerfect ↥M] {L : Subgroup G} (hML : M.map psi = L)
    {t : StatedLieTag} {n : ℕ} (ht : GGPosTag t) (hadm : StatedLieAdmissible t n 2 1)
    (rho : (ggU t n 1).K →* ↥(M.map pi)) (hrho : Function.Surjective rho)
    (hrhoker : rho.ker ≤ Subgroup.center (ggU t n 1).K)
    {gamma : Fin D.rank → ℤ}
    (source : SelectedSL2Model D (GaloisField 2 1) gamma)
    {delta : Fin (ggU t n 1).D.rank → ℤ} (hdelta : delta ∈ (ggU t n 1).D.roots)
    (phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* (ggU t n 1).K)
    (hinj : Function.Injective phi)
    (hupper : (sl2UpperUniSub (GaloisField 2 1)).map phi = (ggU t n 1).D.rootGroup delta)
    (u0 : U)
    (hmap : (D.rootGroup gamma).map (pi.comp (MulAut.conj u0).toMonoidHom) =
      ((ggU t n 1).D.rootGroup delta).map ((M.map pi).subtype.comp rho)) :
    ∃ (Phi : (ggU t n 1).K →* U) (psiPrime : (ggU t n 1).K →* G)
      (model : SelectedSL2Model D (GaloisField 2 1) gamma)
      (member : SelectedSL2Model (ggU t n 1).D (GaloisField 2 1) delta),
      Phi.range = M ∧ Phi.ker ≤ Subgroup.center (ggU t n 1).K ∧
      pi.comp Phi = (M.map pi).subtype.comp rho ∧ psiPrime = psi.comp Phi ∧
      psiPrime.range = L ∧ psiPrime.ker ≤ Subgroup.center (ggU t n 1).K ∧
      member.phi = phi ∧
      ((psi.comp (MulAut.conj u0).toMonoidHom).comp model.phi).range =
        (psiPrime.comp member.phi).range := by
  obtain ⟨Phi, hPhiRange, hPhiKer, hPhiComm⟩ :=
    exists_ordinary_source_cover pi hpiker hpiodd ht hadm rho hrho hrhoker
  let member : SelectedSL2Model (ggU t n 1).D (GaloisField 2 1) delta :=
    SelectedSL2Model.ofGF2Upper (ggU t n 1).D delta hdelta phi hinj hupper
  obtain ⟨model, -, hcomp⟩ := SelectedSL2Model.exists_pullback_of_upper_map_eq
    D (ggU t n 1).D source member Phi hPhiKer pi hpiker hpiodd u0 (by
      rw [hPhiComm]
      exact hmap)
  refine ⟨Phi, psi.comp Phi, model, member, hPhiRange, hPhiKer, hPhiComm, rfl, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hPhiRange, hML]
  · exact FieldTwoE7.ker_comp_le_center_of_perfect Phi hPhiKer
      (RCKK1I.rckK1I_ggU_perfect ht hadm) psi hpsiker
  · exact SelectedSL2Model.ofGF2Upper_phi (ggU t n 1).D delta hdelta phi hinj hupper
  · congr 1
    ext z
    exact congrArg psi (DFunLike.congr_fun hcomp z)

end CFSG.StandardType.SelectedMemberCover
