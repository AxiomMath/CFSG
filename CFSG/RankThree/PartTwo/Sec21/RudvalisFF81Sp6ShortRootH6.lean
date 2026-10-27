module

public import Certificates.Certificate899109
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

theorem cert899109_facts : Sp6SRFacts := Certificates.certificate899109

noncomputable def sH : H6 := Classical.choose cert899109_facts.1

theorem mat6_sH : mat6 sH = dec6 srC := Classical.choose_spec cert899109_facts.1

theorem sH_at : Sp6SRAt zH sH := cert899109_facts.2 zH sH mat6_zH mat6_sH

theorem sH_comm_z0 : sH * zH 0 = zH 0 * sH := sH_at.1.2.2.1

theorem sH_comm_u : sH * (zH 1 * zH 2) = zH 1 * zH 2 * sH := sH_at.1.2.2.2.1

theorem card_cen_sH : Nat.card (Subgroup.centralizer {sH}) = 4608 := sH_at.2.1

theorem srConcl_H6 : SRConcl (⊤ : Subgroup H6) (zH 0) (zH 1) (zH 2) sH := sH_at.2.2.1

theorem card_le_of_isPGroup {R : Subgroup H6} (hR : R ≤ Subgroup.centralizer {sH})
    (h2 : IsPGroup 2 R) (hN : Subgroup.centralizer {sH} ≤ Nor R) : Nat.card R ≤ 128 :=
  sH_at.2.2.2.1 R hR h2 hN

theorem w_comm (i : Fin 3) : zH 1 * zH 2 ^ 2 * zH i = zH i * (zH 1 * zH 2 ^ 2) := by
  have h1 : Commute (zH 1) (zH i) := zH_comm 1 i
  have h2 : Commute (zH 2) (zH i) := zH_comm 2 i
  exact (h1.mul_left (h2.pow_left 2)).eq

theorem s_cases {s : H6} (h0 : s * zH 0 = zH 0 * s) (hu : s * (zH 1 * zH 2) = zH 1 * zH 2 * s)
    (hss : s * s = 1) (hne : s ≠ 1)
    (hinv : s * (zH 1 * zH 2 ^ 2) * s⁻¹ = (zH 1 * zH 2 ^ 2)⁻¹) :
    ∃ g : H6, (∀ i, g * zH i = zH i * g) ∧ s = g * sH * g⁻¹ := by
  rcases sH_at.2.2.2.2 s h0 hu hss hne hinv with e | e | e
  · exact ⟨1, fun i => by rw [one_mul, mul_one], by rw [e, one_mul, inv_one, mul_one]⟩
  · exact ⟨_, w_comm, e⟩
  · refine ⟨_, fun i => ?_, by rw [e, inv_inv]⟩
    exact ((Commute.inv_left (w_comm i : Commute (zH 1 * zH 2 ^ 2) (zH i)))).eq

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR
