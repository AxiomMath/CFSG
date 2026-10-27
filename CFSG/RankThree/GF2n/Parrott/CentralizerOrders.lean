module

public import CFSG.RankThree.GF2n.Parrott.Section3Lift
public import CFSG.RankThree.GF2n.Parrott.FixDimBound

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem card_centralizer_sigma1Nine (h : Tim79a.ParrottHyp z) :
    Nat.card (Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z))) =
      10368 := by
  have hx3 : IsPGroup 3 (Subgroup.zpowers (sigma1Nine (z := z) D)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, sigma1Nine_order (z := z) D]
    norm_num
  have hcop : Nat.Coprime 3 (Nat.card ((J z).subgroupOf (H z))) :=
    coprime_three_card_J_subgroupOf (z := z)
  have hmain := CFSG.card_centralizer_eq_card_inf_mul_card_quotient
    (G := ↥(H z)) (p := 3) (N := (J z).subgroupOf (H z))
    (x := sigma1Nine (z := z) D) hx3 hcop
  rw [hmain, card_centralizer_quotient_eq (D := D) (sigma1Nine (z := z) D),
    qH_sigma1Nine, card_centralizer_sigma1_QA45,
    card_centralizer_inf_J_subgroupOf (z := z) (x := sigma1Nine (z := z) D),
    card_centralizerJ_sigma1Nine h D]

end CFSG.RankThree.GF2n.Parrott
