module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLinear
import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import Certificates.Certificate1002
public import Certificates.Certificate2151
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate9130
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10015
public import Certificates.Certificate10016
public import Certificates.Certificate10017
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section LinMarkCertificates

theorem linMark_holds :
    ∀ (X : Type) [Group X] [Finite X] (ℓ n : ℕ), 5 ≤ ℓ → 2 ≤ n →
      LargeEvenMarking X (fun lab _ _ _ _ _ => lab = ⟨.A, ℓ, n⟩) →
        GGMarkingAll (K := X) fun lab _ _ _ _ _ => lab = ⟨.A, ℓ, n⟩ := by
  intro X _ _ ℓ n hℓ hn hmark
  intro P hP
  obtain ⟨lab₁, hlab₁_eq, hlab₁⟩ :=
    CFSG.StandardType.FrameRoute.exists_glaLabel (X := X) hmark
  subst hlab₁_eq
  obtain ⟨hX, lab₂, hlab₂_inLam, hraw₂⟩ := hP
  have hP' : CFSG.StandardType.LargeEvenMarking X (fun lab _ _ _ _ _ => lab = lab₂) :=
    ⟨hX, lab₂, hlab₂_inLam, CFSG.StandardType.largeEvenRawDatum_mono
      (fun R _ I F h => ⟨h.1, h.2.1, by obtain ⟨θ, _⟩ := h.2.2; exact ⟨θ, rfl⟩⟩) hraw₂⟩
  obtain ⟨lab₂', hlab₂'_eq, hlab₂'⟩ :=
    CFSG.StandardType.FrameRoute.exists_glaLabel (X := X) hP'
  rw [hlab₂'_eq] at hlab₂'
  have hRk2 : CFSG.LocalAnalysis.GLTheoremA.Rk2IsLabel X ⟨.A, ℓ, n⟩ := hlab₁
  have hge : ℓ - 1 ≤ CFSG.Open.evenRank X :=
    CFSG.LocalAnalysis.GLTheoremA.rk2_low_a_ge X ⟨.A, ℓ, n⟩ hRk2 rfl hn
  have he : 4 ≤ CFSG.Open.evenRank X := by omega
  rcases CFSG.LocalAnalysis.GLTheoremA.Y10F.label_eq_or_BC he hlab₁ hlab₂' with heq | hBC
  · refine ⟨hX, lab₂, hlab₂_inLam,
      CFSG.StandardType.largeEvenRawDatum_mono ?_ hraw₂⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, heq.symm⟩
  · obtain ⟨hBC₁, -, -, -⟩ := hBC
    rcases hBC₁ with h | h <;> cases h

end LinMarkCertificates

end CFSG.StandardType.TablePThreeKG

end
