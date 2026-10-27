
module

public import CFSG.Monster.B.TwoA.Amalgam.KernelsBase

public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Amalgam.CoreP4
public import CFSG.Monster.B.TwoA.Par2.Main
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Sp8.SubgeomOrder

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8

theorem Vhat_le_A8 :
    Vhat ≤ A8 := Echain_le_A8 (i := 2) (by norm_num) (by norm_num)

theorem E3_le_A8 :
    E3 ≤ A8 := Echain_le_A8 (i := 3) (by norm_num) (by norm_num)

theorem Lgrp_le_Jhat :
    Lgrp ≤ Jhat := by
  rw [← centralizer_xhat]
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 xhat_mem_A8_e0)

theorem Lgrp_le_Ntwo :
    Lgrp ≤ Ntwo :=
  (Subgroup.centralizer_le fun _ h => Vhat_le_A8 h).trans Ctwo_le_Ntwo

theorem Lgrp_le_K3 :
    Lgrp ≤ K3 :=
  (Subgroup.centralizer_le fun _ h => E3_le_A8 h).trans C3_le_K3

theorem Ehat_le_Xgrp :
    Ehat ≤ Xgrp := Ehat_le_H1.trans H1_le_Xgrp

theorem R2_le_Xgrp :
    R2 ≤ Xgrp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [R2_eq_map_pCore_Ntwo]
  exact map_pCore_le_of_sylow (exists_sylow_X_inf_Kchain 2 (by norm_num) (by norm_num))

theorem R3_le_Xgrp :
    R3 ≤ Xgrp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [R3_eq_pCore_K3]
  exact map_pCore_le_of_sylow (exists_sylow_X_inf_Kchain 3 (by norm_num) (by norm_num))

theorem Nc_zero :
    Nc 0 = Ehat ⊓ Subgroup.centralizer {cQ} := pCore_P1

theorem Nc_one :
    Nc 1 = R2 ⊓ Subgroup.centralizer {cQ} := Par2.map_pCore_H2

theorem Nc_two :
    Nc 2 = R3 ⊓ Subgroup.centralizer {cQ} := Par3.map_pCore_P3

theorem Nc_three :
    Nc 3 = Lgrp := pCore_P4

theorem Lgrp_le_centralizer :
    Lgrp ≤ Subgroup.centralizer {cQ} := fun _ h => (Lgrp_le_P4 h).2

theorem natCard_Nc :
    Nat.card (Nc 0) = 2 ^ 22 ∧ Nat.card (Nc 1) = 2 ^ 30 ∧
    Nat.card (Nc 2) = 2 ^ 32 ∧ Nat.card (Nc 3) = 2 ^ 25 := by
  rw [Nc_zero, Nc_one, Nc_two, Nc_three]
  exact ⟨natCard_N1, Par2.natCard_R2c, Par3.natCard_R3c, natCard_Lgrp⟩

theorem Nc_le_Pc
    (i j : Fin 4) : Nc i ≤ Pc j := by
  fin_cases i <;> fin_cases j
  · exact (Nc_zero ▸ le_inf (inf_le_left.trans Ehat_le_Jhat) inf_le_right :)
  · exact (Nc_zero ▸ le_inf (inf_le_left.trans Ehat_le_Ntwo) inf_le_right :)
  · exact (Nc_zero ▸ le_inf (inf_le_left.trans Ehat_le_K3) inf_le_right :)
  · exact (Nc_zero ▸ le_inf (inf_le_left.trans Ehat_le_Xgrp) inf_le_right :)
  · exact (Nc_one ▸ le_inf (inf_le_left.trans R2_le_Jhat) inf_le_right :)
  · exact (Nc_one ▸ le_inf (inf_le_left.trans R2_le_Ntwo) inf_le_right :)
  · exact (Nc_one ▸ le_inf R2c_le_K3 inf_le_right :)
  · exact (Nc_one ▸ le_inf (inf_le_left.trans R2_le_Xgrp) inf_le_right :)
  · exact (Nc_two ▸ le_inf (inf_le_left.trans R3_le_Jhat) inf_le_right :)
  · exact (Nc_two ▸ le_inf (inf_le_left.trans R3_le_Ntwo) inf_le_right :)
  · exact (Nc_two ▸ le_inf (inf_le_left.trans Par3.R3_le_K3) inf_le_right :)
  · exact (Nc_two ▸ le_inf (inf_le_left.trans R3_le_Xgrp) inf_le_right :)
  · exact (Nc_three ▸ le_inf Lgrp_le_Jhat Lgrp_le_centralizer :)
  · exact (Nc_three ▸ le_inf Lgrp_le_Ntwo Lgrp_le_centralizer :)
  · exact (Nc_three ▸ le_inf Lgrp_le_K3 Lgrp_le_centralizer :)
  · exact (Nc_three ▸ Lgrp_le_P4 :)

theorem Nc_le_Bam
    (i : Fin 4) : Nc i ≤ Bam := le_iInf fun j => Nc_le_Pc i j

theorem comap_map_of_Bam_le
    (i : Fin 4) {H : Subgroup Dfull} (hH : Bam ≤ H) :
    ((H.subgroupOf (Pc i)).map (QuotientGroup.mk' (CFSG.pCore 2 (Pc i)))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 (Pc i))) = H.subgroupOf (Pc i) := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left]
  intro g hg
  rw [Subgroup.mem_subgroupOf]
  exact hH (Nc_le_Bam i ⟨g, hg, rfl⟩)

theorem short_local_centralizer_kernels_common :
    Nc 0 = Ehat ⊓ Subgroup.centralizer {cQ} ∧ Nc 1 = R2 ⊓ Subgroup.centralizer {cQ} ∧
    Nc 2 = R3 ⊓ Subgroup.centralizer {cQ} ∧ Nc 3 = Lgrp ∧
    R2 = (CFSG.pCore 2 Ntwo).map Ntwo.subtype ∧ R3 = (CFSG.pCore 2 K3).map K3.subtype ∧
    Nat.card (Nc 0) = 2 ^ 22 ∧ Nat.card (Nc 1) = 2 ^ 30 ∧ Nat.card (Nc 2) = 2 ^ 32 ∧
    Nat.card (Nc 3) = 2 ^ 25 ∧
    (∀ i, Nc i ≤ Bam) ∧
    (∀ (i : Fin 4) (J : Set (Fin 4)),
      ((((⨅ j ∈ J, Pc j) ⊓ Pc i).subgroupOf (Pc i)).map
          (QuotientGroup.mk' (CFSG.pCore 2 (Pc i)))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 (Pc i))) = ((⨅ j ∈ J, Pc j) ⊓ Pc i).subgroupOf (Pc i)) ∧
    (∀ (i : Fin 4) (H : Subgroup Dfull), Bam ≤ H →
      ((H.subgroupOf (Pc i)).map (QuotientGroup.mk' (CFSG.pCore 2 (Pc i)))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 (Pc i))) = H.subgroupOf (Pc i)) := by
  obtain ⟨h0, h1, h2, h3⟩ := natCard_Nc
  refine ⟨Nc_zero, Nc_one, Nc_two, Nc_three, R2_eq_map_pCore_Ntwo, R3_eq_pCore_K3, h0, h1, h2, h3,
    Nc_le_Bam, fun i J => comap_map_of_Bam_le i ?_, fun i _ hH => comap_map_of_Bam_le i hH⟩
  exact le_inf (le_iInf₂ fun j _ => Bam_le_Pc j) (Bam_le_Pc i)

end CFSG.Monster.B.TwoA.Amalgam
