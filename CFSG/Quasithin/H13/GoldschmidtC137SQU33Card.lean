module

public import CFSG.Quasithin.H13.GoldschmidtC137SQU33Sec
public import CFSG.Quasithin.H13.GoldschmidtC137SQBurn
public import CFSG.Quasithin.H13.GoldschmidtC137SQFrat
public import CFSG.Quasithin.H13.GoldschmidtC137SQSyl7

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

theorem card_normalizer_dvd_of_sylow_seven {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hcard : Nat.card Y = 6048)
    (hnc : ∀ t b : Y, orderOf t = 2 → orderOf b = 7 → t * b ≠ b * t)
    {H : Subgroup Y} (PH : Sylow 7 H) (hPH : Nat.card PH = 7) :
    Nat.card (Subgroup.normalizer (PH : Set H)) ∣ 21 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set QH : Subgroup Y := (PH : Subgroup H).map H.subtype with hQH
  have hQcard : Nat.card QH = 7 := by
    rw [hQH, Subgroup.card_map_of_injective H.subtype_injective]
    exact hPH
  have hQp : IsPGroup 7 QH := PH.2.map H.subtype
  have hQidx : ¬ 7 ∣ QH.index := by
    have := QH.card_mul_index
    rw [hQcard, hcard] at this
    have h : QH.index = 864 := by omega
    rw [h]
    norm_num
  let QY : Sylow 7 Y := hQp.toSylow hQidx
  have h21 := card_normalizer_seven hcard hnc QY
  have hle : (Subgroup.normalizer (PH : Set H)).map H.subtype ≤
      Subgroup.normalizer (QY : Set Y) := by
    rintro _ ⟨n, hn, rfl⟩
    refine mem_normalizer_of_conj_le (QY : Subgroup Y) fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨n * x * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn x).1 hx, rfl⟩
  have hd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective H.subtype_injective, h21] at hd
  exact hd

theorem card_section_u33 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hcard : Nat.card Y = 6048)
    (hnc : ∀ t b : Y, orderOf t = 2 → orderOf b = 7 → t * b ≠ b * t)
    {H : Subgroup Y} (hH : H ≠ ⊤) (N : Subgroup H) [N.Normal]
    (hs : IsSimpleGroup (H ⧸ N)) (hnab : ∃ a b : H ⧸ N, a * b ≠ b * a) :
    Nat.card (H ⧸ N) = 168 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨h60, hleH⟩ := sixty_le_card_section N hs hnab
  have hSH : Nat.card (H ⧸ N) ∣ Nat.card H :=
    ⟨Nat.card N, Subgroup.card_eq_card_quotient_mul_card_subgroup N⟩
  have hH6048 : Nat.card H ∣ 6048 := hcard ▸ Subgroup.card_subgroup_dvd_card H
  have hS6048 : Nat.card (H ⧸ N) ∣ 6048 := hSH.trans hH6048
  have hH672 : Nat.card H ≤ 672 := by
    have hd := card_dvd_factorial_index hH
    rw [hcard] at hd
    have h9 := nine_le_of_dvd_factorial hd
    have hmul := H.card_mul_index
    rw [hcard] at hmul
    by_contra h
    have : 673 * 9 ≤ Nat.card H * H.index := Nat.mul_le_mul (by omega) h9
    omega
  have h7 : 7 ∣ Nat.card (H ⧸ N) := by
    by_contra h7
    have hcop : Nat.Coprime (Nat.card (H ⧸ N)) 7 :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h7 |>.symm
    have h864 : Nat.card (H ⧸ N) ∣ 864 :=
      hcop.dvd_of_dvd_mul_right (by norm_num; exact hS6048)
    obtain ⟨a, b, hab⟩ := exists_pow_two_pow_three_of_dvd h864
    have hsolv := isSolvable_of_card_two_three hab
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y)
  let π : H →* (H ⧸ N) := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have h7H : 7 ∣ Nat.card H := h7.trans hSH
  obtain ⟨PH⟩ : Nonempty (Sylow 7 H) := inferInstance
  have hPH : Nat.card PH = 7 := card_sylow_seven_of_dvd h7H hH6048 PH
  obtain ⟨Pb, hPbcoe⟩ : ∃ Pb : Sylow 7 (H ⧸ N),
      (Pb : Subgroup (H ⧸ N)) = (PH : Subgroup H).map π := ⟨PH.mapSurjective hπ, rfl⟩
  have hPb : Nat.card Pb = 7 := card_sylow_seven_of_dvd h7 hS6048 Pb
  have hNH := card_normalizer_dvd_of_sylow_seven hcard hnc PH hPH
  have hNS : Subgroup.normalizer (Pb : Set (H ⧸ N)) ≤
      (Subgroup.normalizer (PH : Set H)).map π := by
    intro s hs'
    have hcoe : ((Pb : Subgroup (H ⧸ N)) : Set (H ⧸ N)) = (Pb : Set (H ⧸ N)) := Sylow.coe_coe Pb
    rw [← hcoe, hPbcoe] at hs'
    obtain ⟨n, hn, hns⟩ := exists_mem_normalizer_map_eq π hπ PH hs'
    exact ⟨n, hn, hns⟩
  have hNSdvd : Nat.card (Subgroup.normalizer (Pb : Set (H ⧸ N))) ∣ 21 :=
    (Subgroup.card_dvd_of_le hNS).trans ((Subgroup.card_map_dvd _ π).trans hNH)
  have h7N : 7 ∣ Nat.card (Subgroup.normalizer (Pb : Set (H ⧸ N))) := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer : (Pb : Subgroup (H ⧸ N)) ≤ _)
    rwa [hPb] at this
  have hle21 := Nat.le_of_dvd (by norm_num) hNSdvd
  have hcases : Nat.card (Subgroup.normalizer (Pb : Set (H ⧸ N))) = 7 ∨
      Nat.card (Subgroup.normalizer (Pb : Set (H ⧸ N))) = 21 := by
    generalize Nat.card (Subgroup.normalizer (Pb : Set (H ⧸ N))) = m at hNSdvd h7N hle21
    interval_cases m <;> omega
  rcases hcases with hN7 | hN21
  · exfalso
    have heq : (Pb : Subgroup (H ⧸ N)) = Subgroup.normalizer (Pb : Set (H ⧸ N)) :=
      Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by rw [hN7, hPb])
    have : IsCyclic (Pb : Subgroup (H ⧸ N)) := isCyclic_of_prime_card hPb
    refine false_of_normalizer_le_centralizer Pb (by omega) (by omega) ?_
    intro g hg
    have hgP : g ∈ (Pb : Subgroup (H ⧸ N)) := by rw [heq]; exact hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := (Pb : Subgroup (H ⧸ N)))).is_comm.comm ⟨h, hh⟩ ⟨g, hgP⟩)
  · have hidx : (Subgroup.normalizer (Pb : Set (H ⧸ N))).index =
        Nat.card (Sylow 7 (H ⧸ N)) := (Sylow.card_eq_index_normalizer Pb).symm
    have hmul := (Subgroup.normalizer (Pb : Set (H ⧸ N))).card_mul_index
    rw [hN21] at hmul
    have hmod : Nat.card (Sylow 7 (H ⧸ N)) % 7 = 1 := card_sylow_modEq_one (p := 7) (G := H ⧸ N)
    have hdvd288 : (Subgroup.normalizer (Pb : Set (H ⧸ N))).index ∣ 288 := by
      have : 21 * (Subgroup.normalizer (Pb : Set (H ⧸ N))).index ∣ 21 * 288 := by
        rw [hmul]
        exact hS6048
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    rcases sylow_seven_count_cases' hdvd288 (hidx ▸ hmod) with h1 | h8 | h36 | h288
    · omega
    · omega
    · omega
    · omega

end CFSG.Quasithin.H13.U3.GC137.SQ
