module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.CenBSylow
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B1Normal
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.SetupOfLift
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.RankBound
public import CFSG.Mathlib.GroupTheory.CoprimeInvariantSylowTwo

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

private theorem odd_card_of_forall_odd_orderOf {G : Type*} [Group G] [Finite G]
    (h : ∀ g : G, Odd (orderOf g)) : Odd (Nat.card G) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hodd
  have hgodd := h g
  rw [hg] at hgodd
  exact absurd hgodd (by decide)

theorem odd_cen {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) : Odd (Nat.card ↥(cB b z)) := by
  obtain ⟨Y, hYle, hY3, hdecomp, hYnorm⟩ := exists_cen_complement h
  have hYodd : Odd (Nat.card Y) := by
    by_contra hYeven
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hYeven
    obtain ⟨E, hEle, hEa, hEcard⟩ := exists_elemAbelian_six h (b1_normal h)
    have hE3 : IsPGroup 3 E := IsPGroup.of_card (p := 3) (n := 6) hEcard
    have hNnorm : nB b z ≤ Subgroup.normalizer (Y : Set G) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact hYnorm m hm y hy
      · intro hy
        have hmem : m⁻¹ * (m * y * m⁻¹) * (m⁻¹)⁻¹ ∈ Y := hYnorm m⁻¹ ((nB b z).inv_mem hm) _ hy
        have heq : m⁻¹ * (m * y * m⁻¹) * (m⁻¹)⁻¹ = y := by group
        rwa [heq] at hmem
    have hEnorm : E ≤ Subgroup.normalizer (Y : Set G) := hEle.trans hNnorm
    obtain ⟨T, hTY, hT2, hTne, hEnormT⟩ :=
      CFSG.CoprimeInvariantSylowTwo.exists_isPGroup_ne_bot_normalizer hEnorm hE3 hY3 hYeven
    have hle := card_le_of_normalizer_isPGroup_two h.hypA h.model hTne hT2 hEnormT hEa
    rw [hEcard] at hle
    norm_num at hle
  refine odd_card_of_forall_odd_orderOf fun g => ?_
  rw [← Subgroup.orderOf_coe g]
  have hx : (g : G) ∈ cB b z := g.2
  obtain ⟨w, hw, y, hy, hxeq⟩ := hdecomp (g : G) hx
  rw [hxeq]
  have hwodd : Odd (orderOf w) := by
    have hdvd : orderOf w ∣ Nat.card (GGFF.Bt b z) := Subgroup.orderOf_dvd_natCard _ hw
    rw [GGFF.SettingCore.card_Bt h.settingCore] at hdvd
    exact Odd.of_dvd_nat (by decide : Odd 81) hdvd
  have hyodd : Odd (orderOf y) :=
    Odd.of_dvd_nat hYodd (Subgroup.orderOf_dvd_natCard Y hy)
  have hcomm : Commute w y := Subgroup.mem_centralizer_iff.mp (hYle hy) w hw
  exact Odd.of_dvd_nat (hwodd.mul hyodd) hcomm.orderOf_mul_dvd_mul_orderOf

end CFSG.StandardType.FF81.PropOne

end
