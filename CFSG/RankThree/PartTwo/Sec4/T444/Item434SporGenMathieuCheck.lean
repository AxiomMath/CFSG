module

public import Certificates.Certificate8035

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporGen


theorem m12_genA_check : m12GenCheck sigAW sigAP genAa genAb = true :=
  Certificates.certificate8035.1

theorem m12_genA2_check : m12GenCheck sigA2W sigA2P genA2a genA2b = true :=
  Certificates.certificate8035.2.1

theorem m12_fix_check : m12FixCheck = true :=
  Certificates.certificate8035.2.2.1

theorem m12_cent_check : ∀ v : CFSG.GH74.M12.Hyp.G12, CFSG.GH74.M12.Hyp.tbl v.1 ∈
    CFSG.RankThree.PartTwo.Toolkit.M12.ET ++ CFSG.RankThree.PartTwo.Toolkit.M12.FT → v ≠ 1 →
    Nat.card (Subgroup.centralizer ({v} : Set CFSG.GH74.M12.Hyp.G12)) = 54 :=
  Certificates.certificate8035.2.2.2.1

theorem m22_chain_check : m22ChainCheck = true :=
  Certificates.certificate8035.2.2.2.2.1

theorem m22_sift_check : m22SiftCheck = true :=
  Certificates.certificate8035.2.2.2.2.2.1

theorem m22_elt_check : m22EltCheck = true :=
  Certificates.certificate8035.2.2.2.2.2.2

end CFSG.RankThree.PartTwo.Sec4.Item434SporGen
