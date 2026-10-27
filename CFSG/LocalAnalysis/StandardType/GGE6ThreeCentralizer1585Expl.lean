module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCentralizer1585
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyConjNormalizer
public import CFSG.LocalAnalysis.StandardType.GGJ4eComm
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6EvenRootTorus

public section

namespace CFSG.StandardType.E6Centralizer1585

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587

theorem markedCentreExplicit1585_holds
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    MarkedCentreExplicit1585 Omega := by
  intro lab p R instR I phi ρ g
  constructor
  · rintro ⟨hgCentre, hgModel⟩
    rw [connectedCentre, Subgroup.mem_map] at hgCentre
    obtain ⟨z, hzCenter, hzg⟩ := hgCentre
    have hzg' : (z : CFSG.Blueprint.Chevalley.ModGL ρ.tau Omega) = g := hzg
    have hgAdj : g ∈ CFSG.Blueprint.Chevalley.adjointGroup ρ.tau Omega :=
      ((CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.mem_model ρ.setup.D).1
        hgModel).1
    have hT : ∀ t : Fin ρ.tau.rank → Omegaˣ,
        Commute g (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
          ρ.tau t) := by
      intro t
      have ht : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit ρ.tau t ∈
          connectedCentralizer ρ := by
        rw [connectedCentralizer]
        exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨t, rfl⟩)
      have h := Subgroup.mem_center_iff.1 hzCenter
        ⟨CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit ρ.tau t, ht⟩
      have hc := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at hc
      rw [hzg'] at hc
      exact hc.symm
    have hgtorus : g ∈ CFSG.LieType.Chevalley.torusGroup ρ.tau Omega :=
      CFSG.HardMathSupport.Timmesfeld.Torality.mem_torusGroup_of_forall_commute_rootDiagUnit
        hgAdj hT
    obtain ⟨b, hb⟩ := CFSG.LieType.Chevalley.exists_rootDiagUnit_eq_of_mem_torusGroup hgtorus
    refine ⟨hgModel, b, hb.symm, ?_⟩
    intro v hv
    have hvroot : CFSG.Blueprint.Chevalley.IsRoot ρ.tau v := hv.1
    have hmemC : CFSG.Blueprint.Chevalley.pinnedX ρ.tau Omega v 1 ∈ connectedCentralizer ρ := by
      rw [connectedCentralizer]
      exact Subgroup.mem_sup_right
        ((le_iSup₂ (f := fun α (_ : α ∈ CFSG.LieType.Chevalley.kernelRoots
            (CFSG.LieType.AlgebraicGroups.rootCharHom ρ.a)) =>
              CFSG.Blueprint.Chevalley.rootSubgroup ρ.tau Omega α) v hv)
          (Subgroup.subset_closure ⟨(1 : Omega), rfl⟩))
    have hcomm : Commute
        (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit ρ.tau b)
        (CFSG.Blueprint.Chevalley.pinnedX ρ.tau Omega v 1) := by
      have h := Subgroup.mem_center_iff.1 hzCenter
        ⟨CFSG.Blueprint.Chevalley.pinnedX ρ.tau Omega v 1, hmemC⟩
      have hc := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at hc
      rw [hzg', hb] at hc
      exact hc.symm
    exact CFSG.LieType.Chevalley.rootChar_eq_one_of_commute_rootDiagUnit_pinnedX b hvroot hcomm
  · rintro ⟨hgModel, b, hb, hχ⟩
    refine ⟨?_, hgModel⟩
    have hle : connectedCentralizer ρ ≤
        Subgroup.centralizer
          ({CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit ρ.tau b} :
            Set (CFSG.Blueprint.Chevalley.ModGL ρ.tau Omega)) := by
      rw [connectedCentralizer]
      refine sup_le ?_ ?_
      · rw [Subgroup.closure_le]
        rintro _ ⟨b', rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff,
          ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
          ← CFSG.LieType.Chevalley.rootDiagUnit_mul, mul_comm b' b]
      · refine iSup₂_le ?_
        intro α hα
        rw [CFSG.Blueprint.Chevalley.rootSubgroup, Subgroup.closure_le]
        rintro _ ⟨c, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        have hconj := CFSG.LieType.Chevalley.rootDiagUnit_conj_pinnedX (K := Omega) b hα.1 c
        rw [hχ α hα] at hconj
        simp only [Units.val_one, one_mul] at hconj
        calc CFSG.Blueprint.Chevalley.pinnedX ρ.tau Omega α c *
              CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit ρ.tau b
            = (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit ρ.tau b *
                CFSG.Blueprint.Chevalley.pinnedX ρ.tau Omega α c *
                (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
                  ρ.tau b)⁻¹) *
                CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit ρ.tau b := by
              rw [hconj]
          _ = CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit ρ.tau b *
                CFSG.Blueprint.Chevalley.pinnedX ρ.tau Omega α c := by group
    rw [connectedCentre, Subgroup.mem_map]
    refine ⟨⟨CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit ρ.tau b, ?_⟩,
      ?_, hb⟩
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨b, rfl⟩)
    · rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle y.2)

end CFSG.StandardType.E6Centralizer1585

end
