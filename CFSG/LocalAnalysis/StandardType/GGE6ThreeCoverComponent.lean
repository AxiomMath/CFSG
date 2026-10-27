module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedComponents
public import CFSG.LocalAnalysis.StandardType.GGTCJDescent
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeKacSingle
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCentralizer1585

public section

namespace CFSG.StandardType.E6CoverComponent

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.E6KacSingle


private theorem label_eq_of_pair {a labL labJ : LargeEvenLabel}
    (hpair : GGPairE6Three 3 labL labJ) (hiso : GGLabelIso a labJ) : a = labJ := by
  have hlabels := hpair.2.2
  clear hpair
  rcases hlabels with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold GGLabelIso at hiso
     rcases hiso with h | h | h | h | h | h | h | h <;> simp_all)

theorem exists_unique_position
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {L R : Type} [Group L] [Group R]
    (theta : L ⧸ Subgroup.center L ≃* R)
    {labL labJ : LargeEvenLabel} {I : Set (MulAut R)} {y : MulAut L}
    (M : MarkedRationalKacRealization Omega labL 3 R I (ggInducedAut theta y))
    (hL : LargeEvenInLambda2 labL) (hJ : LargeEvenInLambda2 labJ)
    (hpair : GGPairE6Three 3 labL labJ) (hb : 3 ∣ 2 ^ labL.n - 1 ∨ 3 ∣ 2 ^ labL.n + 1)
    (J : Subgroup L) (hcomp : IsComponentOf J (ggAutFixedSubgroup y))
    (hhJ : GGHasLabel labJ (J ⧸ Subgroup.center J)) :
    ∃ j : Fin M.row.D.orbits.length,
      M.row.D.orbits[j].qs = true ∧
      J.map (theta.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = component M j ∧
      M.row.D.orbits[j].lab = labJ ∧ ∀ k, k = j := by
  let psi : L →* R := theta.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hpsi : Function.Surjective psi :=
    theta.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center L))
  have hker : psi.ker ≤ Subgroup.center L := by
    intro l hl
    have hl' : theta (QuotientGroup.mk' (Subgroup.center L) l) = 1 := by
      simpa [psi, MonoidHom.mem_ker] using hl
    have hl'' : QuotientGroup.mk' (Subgroup.center L) l = 1 :=
      theta.injective (by simpa using hl')
    exact (QuotientGroup.eq_one_iff l).mp hl''
  have hphi : ∀ l : L, ggInducedAut theta y (psi l) = psi (y l) := by
    intro l
    exact ggInducedAut_apply theta y l
  have hcomp' : IsComponentOf J (ggFixSub y) := hcomp
  obtain ⟨hJR, ⟨eJ⟩⟩ := TCJ.ggTCJ_descent psi hpsi hker y (ggInducedAut theta y)
    hphi J hcomp'
  have htau : M.tau ≠ .G2 := by
    rw [← M.tau_eq]
    cases M.row.T <;> simp [GGK0MarkedKacIface1587.absTag]
  obtain ⟨j, hqs, hJmap⟩ := GGK0MarkedComponents.exists_component_position_of_realization
    Nat.prime_three (by decide : 3 ≠ 2) M htau hJR
  change J.map psi = component M j at hJmap
  have hHasJmap : GGHasLabel labJ (J.map psi ⧸ Subgroup.center (J.map psi)) :=
    ggHasLabel_of_mulEquiv eJ hhJ
  have hHasOrbit := (M.label j hqs).2
  change GGHasLabel M.row.D.orbits[j].lab (component M j ⧸ Subgroup.center (component M j))
    at hHasOrbit
  rw [← hJmap] at hHasOrbit
  have hOrbitLabel : M.row.D.orbits[j].lab = labJ :=
    label_eq_of_pair hpair (ggLabelRigidInput_holds _ _ _
      (M.label j hqs).1 hJ hHasOrbit hHasJmap)
  have hlength : M.row.D.orbits.length = 1 := by
    rcases hpair.2.1 with htag | htag
    all_goals
      have htype := M.row.type_eq
      simp only [ggKacTypeOfLabel, htag] at htype
      obtain ⟨hT, htw⟩ := Prod.mk.inj (Option.some.inj htype)
      obtain ⟨T, tw, hTtw, hD⟩ := M.row.valid
      have hType : ggKacTypeOfLabel labL = some (M.row.T, M.row.tw) := M.row.type_eq
      rw [hType] at hTtw
      cases Option.some.inj hTtw
      have hpair' : GGPairE6Three 3
          ⟨(if M.row.tw then .twE6 else .E6), 0, labL.n⟩ M.row.D.orbits[j].lab := by
        rw [hOrbitLabel]
        have hrank : labL.rank = 0 := by
          simpa only [LargeEvenInLambda2, htag] using hL.2
        have htag' : (if M.row.tw then .twE6 else .E6) = labL.tag := by
          rw [← htw, htag]
          rfl
        have hlab : (⟨(if M.row.tw then .twE6 else .E6), 0, labL.n⟩ : LargeEvenLabel) =
            labL := by
          cases labL
          simp only [LargeEvenLabel.mk.injEq]
          exact ⟨htag', hrank.symm, trivial⟩
        rw [hlab]
        exact hpair
      have hD' : M.row.D ∈ ggKacTable .E6 M.row.tw 3 labL.n := by
        simpa only [← hT] using hD
      exact orbits_length_eq_one_of_pair hL.1 hb hD' (List.getElem_mem j.2) hpair'
  refine ⟨j, hqs, hJmap, hOrbitLabel, ?_⟩
  intro k
  apply Fin.ext
  have hjlt := j.isLt
  have hklt := k.isLt
  omega

end CFSG.StandardType.E6CoverComponent
