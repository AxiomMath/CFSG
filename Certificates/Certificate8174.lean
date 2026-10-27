
module

public import Certificates.Certificate8174Base

import Certificates.Kernel.M12Loc.Checks
import Certificates.Kernel.M12Cent.Check
import CFSG.Certificates.Kernel.M12LocSound

public section

namespace Certificates

open CertificateChecks

open CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.KC.M12Loc Subgroup
open scoped commutatorElement

open CertificateChecks.KernelM12Loc in
open CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 Subgroup in
open scoped commutatorElement in
theorem certificate8174 : Nat.card (normalizer (P0 : Set G12)) = 108 ∧
    (∀ g ∈ normalizer (P0 : Set G12), g ^ 2 ∈ P0 ∧ g ∈ normalizer (basisE.sub : Set G12) ∧
      g ∈ normalizer (basisF.sub : Set G12)) ∧
    Nat.card (centralizer (basisE.sub : Set G12)) = 9 ∧
    Nat.card (centralizer (basisF.sub : Set G12)) = 9 ∧
    Nat.card (normalizer (basisA.sub : Set G12)) = 54 ∧
    Nat.card (centralizer (basisA.sub : Set G12)) = 9 ∧
    Nat.card (normalizer ((zpowers (x * y) : Subgroup G12) : Set G12)) = 72 ∧
    (∀ g ∈ normalizer ((zpowers (x * y) : Subgroup G12) : Set G12),
      ∀ h ∈ normalizer ((zpowers (x * y) : Subgroup G12) : Set G12),
        psiT (tbl (g * h).1) = psiT (tbl g.1) * psiT (tbl h.1)) ∧
    (∀ g ∈ normalizer ((zpowers (x * y) : Subgroup G12) : Set G12),
      ∀ h ∈ normalizer ((zpowers (x * y) : Subgroup G12) : Set G12),
        psiT (tbl g.1) = psiT (tbl h.1) → g = h) ∧
    ∀ g ∈ normalizer ((zpowers (x * y) : Subgroup G12) : Set G12),
      Equiv.Perm.sign (psiT (tbl g.1)).2 = 1 := by
  have hcent : CFSG.KC.M12Cent.centCheck zT KernelM12Cent.D.S KernelM12Cent.D.W
      KernelM12Cent.D.C KernelM12Cent.D.R = true := by
    rw [← KernelM12Cent.t_eq]
    exact KernelM12Cent.cent_ok
  have hNz := mem_nz_tables hcent TT_eq nz_list nz_swap
  have hsz := exists_tbl_of_listOK TT_eq nz_list
  have hndz : nodupB (D.TNP.map CFSG.KC.M12Cent.keyT) = true := by
    have h := nz_list
    unfold listOK at h
    simp only [Bool.and_eq_true] at h
    exact h.1.2
  have hNa := mem_na_tables TT_eq na_list orb_ok
  obtain ⟨hLa, hnda, -⟩ := listOK_spec TT_eq na_list
  have hcardNa : Nat.card Na = 72 := by
    rw [card_of_tables8174 hNa (exists_tbl_of_listOK TT_eq na_list) (hnda.of_map _), ← hLa,
      List.length_map]
    rfl
  obtain ⟨hmul, hinj, hsign⟩ :=
    psi_of_rows hNa (psiRows_of_split psi_rows_0 psi_rows_1 psi_rows_2) psi_val
  exact ⟨card_eq_countOK (q := predN [xT, yT] P0T) (normalizer_P0_le_nz center_ok)
      (fun g => mem_normalizer_pair_iff tbl_x tbl_y mem_P0_iff g) hNz hsz hndz count_NP,
    np_of_npOK center_ok hNz np_ok,
    card_eq_countOK (q := predC [zT, xT]) (centralizer_le_nz basisE rfl)
      (fun g => mem_centralizer_pair_iff tbl_z tbl_x g) hNz hsz hndz count_CE,
    card_eq_countOK (q := predC [zT, yT]) (centralizer_le_nz basisF rfl)
      (fun g => mem_centralizer_pair_iff tbl_z tbl_y g) hNz hsz hndz count_CF,
    card_eq_countOK (q := predN [zT, aT] AT) (normalizer_A_le_nz afix_ok)
      (fun g => mem_normalizer_pair_iff tbl_z tbl_a mem_A_iff g) hNz hsz hndz count_NA,
    card_eq_countOK (q := predC [zT, aT]) (centralizer_le_nz basisA rfl)
      (fun g => mem_centralizer_pair_iff tbl_z tbl_a g) hNz hsz hndz count_CA,
    hcardNa, hmul, hinj, hsign⟩

end Certificates
