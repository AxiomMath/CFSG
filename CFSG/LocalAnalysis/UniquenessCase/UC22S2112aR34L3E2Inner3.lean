module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3E2Core
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3E2PSL
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3E2PSU
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34FixOdd
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private theorem uc22s2112r34_l3E2Inner3_fixed_odd {D : Data G} (hKF7 : KF7Use D)
    (hH : H1930 D) (c : Ctx21 D (Choice214U D)) {L : Subgroup G} (hL : L ∈ calC D.M)
    {p : ℕ} (hp : p.Prime) (hpσ : p ∈ D.sig) (hMs : IsStronglyPEmbedded p D.M)
    {y : G} (hy : y ∈ c.B0) (hBN : c.B0 ≤ normalizer (L : Set G)) (hy3 : orderOf y = 3)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) {Y : Subgroup (BarInf L)}
    (hY : Y ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨y, hBN hy⟩))
    (hYs : IsSimpleGroup Y) (hYp : 2 ≤ CFSG.pRank p Y) : False := by
  have hYp' : 2 ≤ Open.pRank p Y := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hYp
  obtain ⟨E, hEY, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hYp'
  have hp2Y : p ^ 2 ∣ Nat.card ↥Y := hEc ▸ Subgroup.card_dvd_of_le hEY
  have hpY : p ∣ Nat.card ↥Y := (dvd_pow_self p two_ne_zero).trans hp2Y
  have hrank : 2 ≤ Open.pRank p (signalizerFixedSubgroup (inducedBarInfAutHom L ⟨y, hBN hy⟩)) :=
    UC6S846.le_pRank' hp (hEY.trans hY) hEel hEc
  have := hYs
  refine uc22s2112r34_false_of_fixed_odd hKF7 hH c hL hpσ hMs hy (hBN hy)
    (hy3 ▸ (Nat.prime_three : Nat.Prime 3)) (by rw [hy3]; norm_num) hpN hrank hY ?_
    (MonoidHom.id ↥Y) Function.surjective_id hpY ?_
  ·
    intro hsolv
    have : IsMulCommutative ↥Y := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.2 hsolv⟩⟩
    have hprime := Group.is_simple_iff_prime_card.1 hYs
    rw [← (Nat.prime_dvd_prime_iff_eq hp hprime).1 hpY] at hp2Y
    have h2 := hp.two_le
    have hle := Nat.le_of_dvd hp.pos hp2Y
    nlinarith
  ·
    rintro rfl ⟨e⟩
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [Nat.card_congr e.toEquiv, h60] at hp2Y
    norm_num at hp2Y


theorem s21_12aFR34L3E2Inner3_of_kf7 {D : Data G} (hKF7 : KF7Use D) :
    S21_12aFR34L3E2Inner3 D := by
  intro hH c L hL hBN hfaith t p f ht hp hp2 hf2 hX hpσ hMs hpN h3 y hy hy3 K x hK hxK hxr hx5
    hxp hcomm
  have hsimple : IsSimpleGroup (BarInf L) :=
    (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have hZ : center (BarInf L) = ⊥ := center_barInf_eq_bot hL.2.2
  let θ : MulAut (BarInf L) := inducedBarInfAutHom L ⟨y, hBN hy⟩
  have hcomm' : θ * MulAut.conj x = MulAut.conj x * θ := hcomm
  have hconj_inj : Function.Injective (MulAut.conj : BarInf L →* MulAut (BarInf L)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center (BarInf L) := by
      rw [mem_center_iff]
      intro w
      have h := congrArg (fun φ : MulAut (BarInf L) => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc w * z = z * w * z⁻¹ * z := by rw [h]
        _ = z * w := by group
    rwa [hZ, mem_bot] at hzc
  have hconjid : θ * MulAut.conj x * θ⁻¹ = MulAut.conj (θ x) := by
    ext z
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    rw [show θ (θ⁻¹ z) = z from MulEquiv.apply_symm_apply θ z]
  have hθx : θ x = x := by
    apply hconj_inj
    rw [← hconjid, hcomm']
    group
  have hyN3 : (⟨y, hBN hy⟩ : ↥(normalizer (L : Set G))) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (⟨y, hBN hy⟩ : ↥(normalizer (L : Set G)))
    rwa [Subgroup.orderOf_mk, hy3] at h
  have hθ3 : θ ^ 3 = 1 := by
    change inducedBarInfAutHom L ⟨y, hBN hy⟩ ^ 3 = 1
    rw [← map_pow, hyN3, map_one]
  have hx3 : orderOf x ≠ 3 := by omega
  rcases ht with rfl | rfl
  ·
    rcases uc22s2112r34_l3E2_trichotomy_psl hp hp2 hX.admissible hX θ hθ3 hK hxK hxr hx3 hxp
      hθx with hinn | ⟨K', hK', hK'θ⟩ | ⟨Y, hY, hYs, hYp⟩
    · exact hinn
    · exfalso
      exact uc22s2112r34_false_of_fund_odd hKF7 hH c hL hp hp2 hf2 hpσ hMs hy (hBN hy)
        (hy3 ▸ (Nat.prime_three : Nat.Prime 3)) (by rw [hy3]; norm_num) hpN hK' hK'θ
    · exfalso
      exact uc22s2112r34_l3E2Inner3_fixed_odd hKF7 hH c hL hp hpσ hMs hy hBN hy3 hpN
        hY hYs hYp
  ·
    have h3' : 3 ∣ p ^ f + 1 := by
      have h : 3 ∣ Nat.gcd 3 (p ^ f + 1) := by simpa [genericOrders] using h3
      exact h.trans (Nat.gcd_dvd_right 3 (p ^ f + 1))
    rcases uc22s2112r34_l3E2_trichotomy_psu hp hp2 h3' hX.admissible hX θ hθ3 hK hxK hxr hx3
      hxp hθx with hinn | ⟨K', hK', hK'θ⟩ | ⟨Y, hY, hYs, hYp⟩
    · exact hinn
    · exfalso
      exact uc22s2112r34_false_of_fund_odd hKF7 hH c hL hp hp2 hf2 hpσ hMs hy (hBN hy)
        (hy3 ▸ (Nat.prime_three : Nat.Prime 3)) (by rw [hy3]; norm_num) hpN hK' hK'θ
    · exfalso
      exact uc22s2112r34_l3E2Inner3_fixed_odd hKF7 hH c hL hp hpσ hMs hy hBN hy3 hpN
        hY hYs hYp

end CFSG.LocalAnalysis.UniquenessCase.UC22
