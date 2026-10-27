module

public import CFSG.Monster.Tri.LeechModelTrace
public import CFSG.Monster.Existence.ELevelCheck
public import CFSG.Monster.Tri.LeechModelFixInputs
public import Certificates.Certificate10049
public meta import CFSG.Monster.Existence.ELevelCheck
public meta import CFSG.Monster.Existence.ELevelConv
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumCheck
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.CosetCertData
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import Certificates.Data.CFSGNative.MonsterB.CosetEnum
public meta import Certificates.Data.CFSGNative.MonsterB.Short
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphLocal
public meta import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.GeomNative
public meta import CFSG.Monster.B.TwoA.Base.Par45A
public meta import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Monster.B.TwoA.Par3.MainBase
public meta import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase
public meta import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.Monster.Tri.LeechCover
public import CFSG.Open.MonsterY443Defs
public meta import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
public meta import CFSG.Sporadic.Co1Base
public meta import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.F2Spec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel CFSG.Monster.VisCert
  CFSG.Monster.Existence CFSG.Monster.B.TwoA.Census

theorem fixCountX_le :
    ∀ i ∈ ({1, 2, 6} : Finset ℕ), fixCountX i ≤ 4071 :=
  Certificates.certificate10049

theorem ncard_fixShort_monoAO_le
    {i : ℕ} (hi : i ∈ ({1, 2, 6} : Finset ℕ)) :
    (fixShort (monoAO i)).ncard ≤ 4071 := by
  refine le_trans ?_ (fixCountX_le i hi)
  set L := shortPacked.filter fun x => kapX (tT i) (tD i) x == x with hL
  have hsub : fixShort (monoAO i) ⊆ vecX '' (L.toFinset : Set ℕ) := by
    rintro y ⟨hys, hyf⟩
    obtain ⟨x, hxs, hx24, hxy⟩ := mem_shortPacked hys
    refine ⟨x, ?_, hxy⟩
    simp only [Finset.mem_coe, List.mem_toFinset, hL, List.mem_filter, beq_iff_eq]
    refine ⟨hxs, ?_⟩
    apply vecX_injective_lt (kapX_lt _ _ _) hx24
    rw [← modTwoEnd_vecX]
    change modTwoEnd (monoAO i) (vecX x) = vecX x
    rw [hxy]
    exact hyf
  calc (fixShort (monoAO i)).ncard ≤ (vecX '' (L.toFinset : Set ℕ)).ncard :=
        Set.ncard_le_ncard hsub ((Finset.finite_toSet _).image _)
    _ ≤ (L.toFinset : Set ℕ).ncard := Set.ncard_image_le (Finset.finite_toSet _)
    _ = L.toFinset.card := Set.ncard_coe_finset _
    _ ≤ L.length := List.toFinset_card_le _

end CFSG.Monster.Tri.Leech
