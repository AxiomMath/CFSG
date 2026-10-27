module

public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Monster.Existence.GMSBridge
public import CFSG.Monster.GMS.Defs
public import Certificates.Certificate3014
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3053
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3024
public import Certificates.Certificate3027
public import Certificates.Certificate8955

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Blueprint CFSG.Monster.GMS

@[expose] noncomputable def centToDA : cent tGriess →* DA := piA.comp centTEquiv.toMonoidHom

theorem centToDA_surjective : Function.Surjective centToDA :=
  piA_surjective.comp centTEquiv.surjective

theorem ker_centToDA :
    centToDA.ker = Subgroup.center (cent tGriess) := by
  ext g
  have h1 : centToDA g = piA (centTEquiv g) := rfl
  rw [MonoidHom.mem_ker, h1, ← MonoidHom.mem_ker, ker_piA, ← center_CfullA,
    ← center_map_mulEquiv centTEquiv]
  constructor
  · rintro ⟨g', hg', hgg⟩
    have h2 : g' = g := centTEquiv.injective hgg
    rwa [← h2]
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem gmsF2Type_DA
    (hNF : ∀ c : CfullA, (c * uA * c⁻¹ = uA ∨ c * uA * c⁻¹ = uA * tStarA) →
      (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen) :
    GMSF2Type (phiB uBar) DA :=
  ⟨isSimpleGroup_DA, uHatA, orderOf_uHatA,
    ⟨(centralizerUHatEquiv hNF).trans
      (@centralizerMulEquiv Cbar NativeSporadic.B _ Units.instGroup phiB uBar)⟩⟩

theorem gmsDoubleF2Centralizer_tGriess
    (hNF : ∀ c : CfullA, (c * uA * c⁻¹ = uA ∨ c * uA * c⁻¹ = uA * tStarA) →
      (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen) :
    GMSDoubleF2Centralizer (phiB uBar) tGriess := by
  refine ⟨orderOf_tGriess, isPerfect_cent_tGriess.commutator_eq_top, DA, inferInstance, centToDA,
    centToDA_surjective, ?_, gmsF2Type_DA hNF⟩
  rw [ker_centToDA]
  exact center_cent_tGriess

theorem gmsF1Type_MGriess
    (hNF : ∀ c : CfullA, (c * uA * c⁻¹ = uA ∨ c * uA * c⁻¹ = uA * tStarA) →
      (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen) :
    GMSF1Type (phiB uBar) tGriess xGriess :=
  ⟨gmsDoubleF2Centralizer_tGriess hNF, gmsLeechCentralizer_xGriess⟩

end CFSG.Monster.Existence
