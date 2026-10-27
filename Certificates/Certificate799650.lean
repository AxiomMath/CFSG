module

public import Certificates.Data.FF81Sp6Levi
import Certificates.Kernel.Sp62.Final
import Certificates.Kernel.Sp62.Levi799650
import CFSG.Certificates.Kernel.Sp62Pk.LeviSound

open CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi

namespace CertificateChecks.Batch799650

open CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi

theorem levi_tab (j : Fin 5) {o n : ℕ} (ho : offC j = o) (hn : centOrder j = n)
    (h : leviK REC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) o n 2 = true)
    (hm : n ≤ 64 * 2) : allCheck leviPred (closureT (gs j)) = true := by
  subst ho hn
  obtain ⟨hcl, hrec⟩ := clos_ok j
  have hsz : (closureT (gs j)).size = centOrder j := by
    simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at hcl
    exact hcl.1.1.1
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hsz] at ht
  rw [leviPred_eq zc_ok (hrec t ht)]
  exact CFSG.KC.G2Three.allBelow_g2 h hm t ht

theorem levi_0 : leviCheck = true := by
  have h3 := levi_tab 3 rfl rfl levi3_ok (by decide)
  have h4 := levi_tab 4 rfl rfl levi4_ok (by decide)
  unfold leviCheck
  rw [Bool.and_eq_true]
  exact ⟨h3, h4⟩

end CertificateChecks.Batch799650

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi in
theorem certificate799650 : leviCheck = true :=
  CertificateChecks.Batch799650.levi_0

end Certificates

end
