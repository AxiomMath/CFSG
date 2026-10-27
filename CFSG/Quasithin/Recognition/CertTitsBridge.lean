module

public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.Recognition.CertTitsSimpleMain
public import CFSG.Quasithin.Recognition.CertTits
public import CFSG.Blueprint.Catalog
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Quasithin.Recognition.CertTits
public meta import CFSG.Open.QuasithinDefs
public import Certificates.Certificate8072
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Tits (titsD titsDGen titsDerivedArrs titsDerived_perm titsChains_check
  titsDerivedArrs_size titsModelEquiv isInvA_of_allPermsOK)

theorem titsBridge_array₁ :
    titsArray CFSG.Open.quasithinTitsData1 = titsDerivedArrs[0]! :=
  Certificates.certificate8072.1

theorem titsBridge_array₂ :
    titsArray CFSG.Open.quasithinTitsData2 = titsDerivedArrs[1]! :=
  Certificates.certificate8072.2

theorem titsBridge_isInv {j : ℕ} (hj : j < 2) :
    isInvA 1755 titsDerivedArrs[j]! (invCand 1755 titsDerivedArrs[j]!) = true :=
  isInvA_of_allPermsOK titsChains_check.2.2.2.2.2.2.1 (by rw [titsDerivedArrs_size]; omega)

theorem titsBridge_closure :
    Subgroup.closure ({permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1),
      permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)} : Set (Equiv.Perm (Fin 1755))) =
      titsD := by
  rw [titsBridge_array₁, titsBridge_array₂, titsDerived_perm (by norm_num),
    titsDerived_perm (by norm_num), titsD]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two]
  tauto

noncomputable def quasithinTitsEquivD :
    CFSG.Open.quasithinTits ≃* titsD :=
  (unitsClosurePairEquiv _ _ _ _
    (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData1
      (by rw [titsBridge_array₁]; exact titsBridge_isInv (by norm_num)))
    (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData2
      (by rw [titsBridge_array₂]; exact titsBridge_isInv (by norm_num)))).trans
    (MulEquiv.subgroupCongr titsBridge_closure)

theorem titsModelBridge_of_lieModel
    (X : Type) [Group X]
    (h : CFSG.Blueprint.LieModel X .Tits 0 2 1) : Nonempty (X ≃* CFSG.Open.quasithinTits) := by
  have hree : CFSG.Blueprint.ReeTitsModel X .Tits 2 1 := by
    rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hree⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact hree
    · exact absurd hsz (by decide)
  obtain ⟨e⟩ := titsModelEquiv X 2 1 hree
  exact ⟨e.trans quasithinTitsEquivD.symm⟩

end CFSG.Quasithin
