module

public import CFSG.Quasithin.Recognition.F112Crit.L2EvenFour
public import CFSG.Quasithin.Recognition.F112Crit.McLOrders
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearSz

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.GH74.Uniqueness.Bender McLOrd

namespace ListedNoMcLProof

theorem card_eq_of_index_le_two {Q W : Type} [Group Q] [Group W] [Finite W] (f : Q →* W)
    (hidx : f.range.index ≤ 2) : ∃ c, (c = 1 ∨ c = 2) ∧ Nat.card W = c * Nat.card f.range := by
  have hW := Subgroup.card_mul_index f.range
  have hpos : 0 < Nat.card W := Nat.card_pos
  refine ⟨f.range.index, ?_, by rw [mul_comm, hW]⟩
  have h0 : f.range.index ≠ 0 := fun h => by
    rw [h, mul_zero] at hW
    omega
  omega

theorem card_range_mul_card_ker {Q W : Type} [Group Q] [Group W] (f : Q →* W) :
    Nat.card f.range * Nat.card f.ker = Nat.card Q := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem center_eq_bot {K : Type*} [Group K] [IsSimpleGroup K] (hns : ¬ Group.IsSolvable K) :
    Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · refine absurd (IsSimpleGroup.comm_iff_isSolvable.mp fun a b => ?_) hns
    exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm

theorem zU_two_top {g : ℕ} (hg : 1 ≤ g) : zU 2 g (2 * (g * 3)) :=
  zU_top (n := 2) (t := 1) (Or.inl rfl) le_rfl (by omega)

theorem card_statedProj_statedSU_three {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F]
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (2 ^ n) F)) = ordTwistedA 2 (2 ^ n) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (f := n) (n := 3) Nat.prime_two
    hn hF (by norm_num)]
  rfl

end ListedNoMcLProof

open ListedNoMcLProof in
theorem listedNoMcL : ListedNoMcL := by
  intro K _ _ hK hns hA5 W _ hW f hker _ hidx
  have hw := mcLArith_of_isMcLaughlinGroup hW
  haveI : Finite W := Nat.finite_of_card_ne_zero hw.1.ne'
  obtain ⟨c, hc, hcW⟩ := card_eq_of_index_le_two f hidx
  have hrk := card_range_mul_card_ker f
  have hsK : Nat.card f.range ∣ Nat.card K := hrk ▸ dvd_mul_right _ _
  rcases cases_of_listed_of_not_isSolvable hK hns with ⟨n, hn, ⟨e⟩⟩ | ⟨a, -, ⟨e⟩⟩ |
    ⟨n, hn, F, _, _, hF, ⟨e⟩⟩ | ⟨n, hn, F, _, _, hF, ⟨e⟩⟩
  ·
    haveI := (BenderType.linear n hn e).isSimple
    have hk1 : f.ker = ⊥ := le_bot_iff.mp (hker.trans (center_eq_bot hns).le)
    have hs : Nat.card f.range = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      have h := hrk
      rw [hk1, Subgroup.card_bot, mul_one, Nat.card_congr e.toEquiv,
        CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psl2_even (by omega)] at h
      exact h
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
    · exact hA5 ⟨e⟩
    · rw [hs] at hcW
      rcases hc with rfl | rfl
      · exact hw.2.2.2.1 (by rw [hcW]; norm_num)
      · exact hw.2.2.2.2 (by rw [hcW]; norm_num)
    · obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega) (by omega)
      refine false_of_top hw hc hcW (j := n) (r := (2 ^ n) ^ 2 - 1) (dvd_of_eq hs)
        (odd_pow_sub_one (by omega) (by norm_num)) h4 hp ?_
      rw [hs, ← pow_mul, mul_comm n 2]
      exact dvd_mul_of_dvd_right hp.dvd _
  ·
    have h3 : 3 ∣ c * Nat.card f.range := hcW ▸ hw.2.1
    have h3' : 3 ∣ Nat.card f.range := by
      rcases hc with rfl | rfl
      · simpa using h3
      · exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3
    have h3K := h3'.trans hsK
    rw [Nat.card_congr e.toEquiv] at h3K
    exact CFSG.SignalizerFunctorTheorem.CatalogBridge.not_three_dvd_card_sz a h3K
  ·
    haveI : Finite (StatedSU 3 (2 ^ n) F) := Finite.of_equiv K e.toEquiv
    set Z₀ := (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F) with hZ₀
    obtain ⟨i, hB⟩ := benderType_statedProj hn hF
    haveI := hB.isSimple
    have hcent : Subgroup.center (StatedSU 3 (2 ^ n) F) ≤ Z₀ := by
      intro z hz
      have hz' : (QuotientGroup.mk' Z₀ z : StatedProj (StatedSU 3 (2 ^ n) F)) ∈
          Subgroup.center (StatedProj (StatedSU 3 (2 ^ n) F)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z₀ g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
      rw [center_eq_bot (not_isSolvable_statedProj hn hF), Subgroup.mem_bot,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz'
      exact hz'
    have hkerZ : f.ker.map e.toMonoidHom ≤ Z₀ := by
      rintro _ ⟨x, hx, rfl⟩
      refine hcent (Subgroup.mem_center_iff.mpr fun g => ?_)
      have hxc := Subgroup.mem_center_iff.mp (hker hx)
      apply e.symm.injective
      simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.symm_apply_apply]
      exact hxc (e.symm g)
    have hdvd : Nat.card f.ker ∣ Nat.card Z₀ := by
      rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
      exact Subgroup.card_dvd_of_le hkerZ
    have hZp : ∀ q, q.Prime → q ∣ Nat.card Z₀ → q = 3 := by
      intro q hq hqd
      haveI := Fact.mk hq
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' q hqd
      have h3 : z ^ 3 = 1 := Subtype.ext (statedSU_three_kernel z.1 z.2)
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
        (hz ▸ orderOf_dvd_of_pow_eq_one h3)
    have hZodd : Odd (Nat.card Z₀) := by
      rcases Nat.even_or_odd (Nat.card Z₀) with h | h
      · exact absurd (hZp 2 Nat.prime_two (even_iff_two_dvd.mp h)) (by norm_num)
      · exact h
    have hKc : Nat.card K = ordTwistedA 2 (2 ^ n) * Nat.card Z₀ := by
      rw [Nat.card_congr e.toEquiv, Subgroup.card_eq_card_quotient_mul_card_subgroup Z₀,
        ← card_statedProj_statedSU_three (by omega) hF]
    obtain ⟨⟨r, hr, hrw⟩, hprim⟩ := profile_ordTwistedA (n := 2) (g := n) le_rfl (by omega)
    have hrw3 : ordTwistedA 2 (2 ^ n) = 2 ^ (n * 3) * r := hrw
    obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * (n * 3)) (by omega) (by omega)
    refine false_of_top hw hc hcW (j := n * 3) (r := r * Nat.card Z₀) ?_ (hr.mul hZodd)
      (by omega) hp ?_
    · have h := hsK
      rwa [hKc, hrw3, mul_assoc] at h
    · have hpK : p ∣ Nat.card f.range * Nat.card f.ker := by
        rw [hrk, hKc]
        exact dvd_mul_of_dvd_left ((hprim p _ hp (by omega)).mpr (zU_two_top (by omega))) _
      rcases hp.prime.dvd_mul.mp hpK with h | h
      · exact h
      · have h3 := hZp p hp.prime (h.trans hdvd)
        have := hp.eq_two_of_dvd_three (by omega) (dvd_of_eq h3)
        omega
  ·
    obtain ⟨i, hB⟩ := benderType_statedProj hn hF
    haveI := (hB.of_mulEquiv e.symm).isSimple
    have hk1 : f.ker = ⊥ := le_bot_iff.mp (hker.trans (center_eq_bot hns).le)
    have hs : Nat.card f.range = ordTwistedA 2 (2 ^ n) := by
      have h := hrk
      rw [hk1, Subgroup.card_bot, mul_one, Nat.card_congr e.toEquiv,
        card_statedProj_statedSU_three (by omega) hF] at h
      exact h
    obtain ⟨⟨r, hr, hrw⟩, hprim⟩ := profile_ordTwistedA (n := 2) (g := n) le_rfl (by omega)
    have hrw3 : ordTwistedA 2 (2 ^ n) = 2 ^ (n * 3) * r := hrw
    obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * (n * 3)) (by omega) (by omega)
    refine false_of_top hw hc hcW (j := n * 3) (r := r) (dvd_of_eq (hs.trans hrw3)) hr
      (by omega) hp ?_
    rw [hs]
    exact (hprim p _ hp (by omega)).mpr (zU_two_top (by omega))

theorem f112SliceFDBigPlus_of_l2EvenThree (h8 : L2Even 3) :
    CFSG.Quasithin.H13.F112SliceFDBigPlus :=
  f112SliceFDBigPlus_of_l2Eight listedNoMcL h8

end CFSG.Quasithin.F112Crit

end
