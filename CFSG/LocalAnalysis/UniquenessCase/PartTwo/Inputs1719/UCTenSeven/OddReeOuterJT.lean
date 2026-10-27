module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReeSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReePhi6Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped MatrixGroups

private lemma two_dvd_three_pow_sq_sub_one (n : ℕ) : 2 ∣ (3 ^ n) ^ 2 - 1 := by
  have h1 : (3 : ℕ) ^ n % 2 = 1 := Nat.odd_iff.mp (Odd.pow (n := n) (by norm_num : Odd 3))
  have h2 : (3 ^ n) ^ 2 % 2 = 1 := by rw [Nat.pow_mod, h1]
  omega

private lemma three_pow_dvd_three_pow_card (n : ℕ) :
    3 ^ n ∣ 3 ^ n * ((3 ^ n) ^ 2 - 1) / 2 := by
  have h2 : 2 ∣ 3 ^ n * ((3 ^ n) ^ 2 - 1) := dvd_mul_of_dvd_right (two_dvd_three_pow_sq_sub_one n) _
  have hdouble : 2 * (3 ^ n * ((3 ^ n) ^ 2 - 1) / 2) = 3 ^ n * ((3 ^ n) ^ 2 - 1) :=
    Nat.mul_div_cancel' h2
  have hodd : Odd (3 ^ n) := Odd.pow (n := n) (by norm_num : Odd 3)
  have hcop : Nat.Coprime (3 ^ n) 2 := hodd.coprime_two_right
  refine hcop.dvd_of_dvd_mul_right ?_
  rw [mul_comm, hdouble]
  exact dvd_mul_right _ _

private lemma three_pow_succ_not_dvd_three_pow_card {n : ℕ} (hn : 1 ≤ n) :
    ¬ 3 ^ (n + 1) ∣ 3 ^ n * ((3 ^ n) ^ 2 - 1) / 2 := by
  intro h
  have h2 : 2 ∣ 3 ^ n * ((3 ^ n) ^ 2 - 1) := dvd_mul_of_dvd_right (two_dvd_three_pow_sq_sub_one n) _
  have hdouble : 2 * (3 ^ n * ((3 ^ n) ^ 2 - 1) / 2) = 3 ^ n * ((3 ^ n) ^ 2 - 1) :=
    Nat.mul_div_cancel' h2
  have hdvd : 3 ^ (n + 1) ∣ 3 ^ n * ((3 ^ n) ^ 2 - 1) := by
    rw [← hdouble, mul_comm]
    exact h.mul_right 2
  rw [pow_succ] at hdvd
  have hpos : 0 < 3 ^ n := by positivity
  have h3 : 3 ∣ (3 ^ n) ^ 2 - 1 := (Nat.mul_dvd_mul_iff_left hpos).mp hdvd
  have h3sq : 3 ∣ (3 ^ n) ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _
  have hge : 1 ≤ (3 ^ n) ^ 2 := by
    have hpos2 : 0 < (3 ^ n) ^ 2 := by positivity
    omega
  have hone : (3 ^ n) ^ 2 - ((3 ^ n) ^ 2 - 1) = 1 := by omega
  have hsub := Nat.dvd_sub h3sq h3
  rw [hone] at hsub
  norm_num at hsub

private lemma three_pow_card_injective {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (h : 3 ^ d * ((3 ^ d) ^ 2 - 1) / 2 = 3 ^ m * ((3 ^ m) ^ 2 - 1) / 2) : d = m := by
  rcases Nat.lt_trichotomy d m with hlt | heq | hgt
  · exfalso
    have h1 : 3 ^ (d + 1) ∣ 3 ^ m := Nat.pow_dvd_pow 3 (by omega)
    have h2 : 3 ^ m ∣ 3 ^ m * ((3 ^ m) ^ 2 - 1) / 2 := three_pow_dvd_three_pow_card m
    have h3 : 3 ^ (d + 1) ∣ 3 ^ d * ((3 ^ d) ^ 2 - 1) / 2 := by
      rw [h]
      exact h1.trans h2
    exact three_pow_succ_not_dvd_three_pow_card hd h3
  · exact heq
  · exfalso
    have h1 : 3 ^ (m + 1) ∣ 3 ^ d := Nat.pow_dvd_pow 3 (by omega)
    have h2 : 3 ^ d ∣ 3 ^ d * ((3 ^ d) ^ 2 - 1) / 2 := three_pow_dvd_three_pow_card d
    have h3 : 3 ^ (m + 1) ∣ 3 ^ m * ((3 ^ m) ^ 2 - 1) / 2 := by
      rw [← h]
      exact h1.trans h2
    exact three_pow_succ_not_dvd_three_pow_card hm h3

private lemma eight_dvd_three_pow_sq_sub_one (n : ℕ) : 8 ∣ (3 ^ n) ^ 2 - 1 :=
  CFSG.Walter.Suzuki.eight_dvd_sq_sub_one (Odd.pow (n := n) (by norm_num : Odd 3))

private lemma four_dvd_three_pow_sq_sub_one_div_two (n : ℕ) : 4 ∣ ((3 ^ n) ^ 2 - 1) / 2 := by
  obtain ⟨t, ht⟩ := eight_dvd_three_pow_sq_sub_one n
  have h : ((3 ^ n) ^ 2 - 1) / 2 = 4 * t := by
    rw [ht]
    rw [show 8 * t = 4 * t * 2 by ring]
    exact Nat.mul_div_cancel (4 * t) (by norm_num)
  rw [h]
  exact dvd_mul_right 4 t

private lemma twelve_dvd_three_pow_card {n : ℕ} (hn : 3 ≤ n) :
    12 ∣ 3 ^ n * ((3 ^ n) ^ 2 - 1) / 2 := by
  have h2 : 2 ∣ (3 ^ n) ^ 2 - 1 := two_dvd_three_pow_sq_sub_one n
  have h3 : 3 ∣ 3 ^ n := dvd_pow_self 3 (by omega)
  have h4 : 4 ∣ ((3 ^ n) ^ 2 - 1) / 2 := four_dvd_three_pow_sq_sub_one_div_two n
  rw [Nat.mul_div_assoc (3 ^ n) h2]
  obtain ⟨a, ha⟩ := h3
  obtain ⟨b, hb⟩ := h4
  refine ⟨a * b, ?_⟩
  rw [hb, ha]
  ring

private lemma twelve_lt_three_pow_card {n : ℕ} (hn : 3 ≤ n) :
    12 < 3 ^ n * ((3 ^ n) ^ 2 - 1) / 2 := by
  have h2 : 2 ∣ (3 ^ n) ^ 2 - 1 := two_dvd_three_pow_sq_sub_one n
  have hdouble : 2 * (3 ^ n * ((3 ^ n) ^ 2 - 1) / 2) = 3 ^ n * ((3 ^ n) ^ 2 - 1) :=
    Nat.mul_div_cancel' (dvd_mul_of_dvd_right h2 _)
  have hx : 27 ≤ 3 ^ n := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK : 728 ≤ (3 ^ n) ^ 2 - 1 := by
    have hsq : 729 ≤ (3 ^ n) ^ 2 := by
      calc 729 = 27 ^ 2 := by norm_num
        _ ≤ (3 ^ n) ^ 2 := Nat.pow_le_pow_left hx 2
    omega
  have hprod : 27 * 728 ≤ 3 ^ n * ((3 ^ n) ^ 2 - 1) := Nat.mul_le_mul hx hK
  omega

theorem dvd_of_mulEquiv_psl2 {p d e : ℕ} [Fact p.Prime]
    (hp3 : p = 3) (hd : 3 ≤ d) (he : Odd e) (R : Subgroup PSL(2, GaloisField p e))
    (eR : R ≃* PSL(2, GaloisField 3 d)) : d ∣ e := by
  subst hp3
  have hd0 : d ≠ 0 := by omega
  have hdcard : Nat.card (GaloisField 3 d) = 3 ^ d := GaloisField.card 3 d hd0
  have hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 3 d)) := by
    rw [hdcard]
    exact ⟨3, d, Nat.prime_three, by norm_num, by omega, rfl⟩
  have hcardR : Nat.card R = 3 ^ d * ((3 ^ d) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eR.toEquiv]
    exact CFSG.Walter.Suzuki.card_psl2_of_card (K := GaloisField 3 d) hK hdcard
  have h12 : 12 ∣ Nat.card R := by
    rw [hcardR]
    exact twelve_dvd_three_pow_card hd
  rcases psl2_three_subgroup_cases (p := 3) rfl he R h12 with hR12 | ⟨m, hm3, hmdvd, ⟨eRm⟩⟩
  · rw [hcardR] at hR12
    exact absurd hR12 (ne_of_gt (twelve_lt_three_pow_card hd))
  · have hm0 : m ≠ 0 := by omega
    have hmcard : Nat.card (GaloisField 3 m) = 3 ^ m := GaloisField.card 3 m hm0
    have hKm : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 3 m)) := by
      rw [hmcard]
      exact ⟨3, m, Nat.prime_three, by norm_num, by omega, rfl⟩
    have hEq : 3 ^ d * ((3 ^ d) ^ 2 - 1) / 2 = 3 ^ m * ((3 ^ m) ^ 2 - 1) / 2 := by
      rw [← hcardR, Nat.card_congr eRm.toEquiv]
      exact CFSG.Walter.Suzuki.card_psl2_of_card (K := GaloisField 3 m) hKm hmcard
    have hdm : d = m := three_pow_card_injective (by omega) (by omega) hEq
    rw [hdm]
    exact hmdvd

theorem ree_card_eq_of_psl2_le
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X) {f : ℕ}
    (hmod : CFSG.Blueprint.LieModel X .twistedG2 0 3 f) {M : Subgroup X}
    (hidx : ∀ N : Subgroup ↥M, N.index ≠ 2) {j : X} (hjM : j ∈ M) (hj : orderOf j = 2)
    {d : ℕ} (hd : 3 ≤ d) {F : Subgroup X} (hFM : F ≤ M)
    (hFj : F ≤ centralizer ({j} : Set X)) (eF : F ≃* PSL(2, GaloisField 3 d)) :
    ∃ e : ℕ, d ∣ e ∧ e ∣ f ∧
      Nat.card M = (3 ^ e) ^ 3 * ((3 ^ e) ^ 3 + 1) * (3 ^ e - 1) := by
  classical
  obtain ⟨-, -, -, -, ⟨k, rfl⟩, hf3⟩ := CFSG.Blueprint.LieModel.admissible hmod
  obtain ⟨J, hJp, hJf, hJt⟩ := ree_exists_jtHyp hXs hmod hj
  have hd0 : d ≠ 0 := by omega
  have hdcard : Nat.card (GaloisField 3 d) = 3 ^ d := GaloisField.card 3 d hd0
  have hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 3 d)) := by
    rw [hdcard]
    exact ⟨3, d, Nat.prime_three, by norm_num, by omega, rfl⟩
  have hFcard : Nat.card F = 3 ^ d * ((3 ^ d) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eF.toEquiv]
    exact CFSG.Walter.Suzuki.card_psl2_of_card (K := GaloisField 3 d) hK hdcard
  have hFbig : 12 < Nat.card F := hFcard ▸ twelve_lt_three_pow_card hd
  have h12F : 12 ∣ Nat.card F := hFcard ▸ twelve_dvd_three_pow_card hd
  have hkey : ∀ x ∈ F, x ∉ J.F → ∀ y ∈ F, y ∉ J.F → x⁻¹ * y ∈ J.F := by
    intro x hxF hxJ y hyF hyJ
    have hxj : x ∈ centralizer ({J.t} : Set X) := by
      rw [hJt]
      exact hFj hxF
    have hyj : y ∈ centralizer ({J.t} : Set X) := by
      rw [hJt]
      exact hFj hyF
    have htx : J.t * x ∈ J.F := (J.mem_centralizer_t.mp hxj).resolve_left hxJ
    have hty : J.t * y ∈ J.F := (J.mem_centralizer_t.mp hyj).resolve_left hyJ
    have heq : (J.t * x)⁻¹ * (J.t * y) = x⁻¹ * y := by
      rw [mul_inv_rev, J.t_inv, mul_assoc, ← mul_assoc J.t J.t y, J.t_mul_t, one_mul]
    rw [← heq]
    exact J.F.mul_mem (J.F.inv_mem htx) hty
  have hidx2 : (J.F.subgroupOf F).index ∣ 2 := by
    by_cases htop : J.F.subgroupOf F = ⊤
    · rw [htop, Subgroup.index_top]
      norm_num
    · obtain ⟨a, ha⟩ : ∃ a : ↥F, a ∉ J.F.subgroupOf F := by
        by_contra h
        push Not at h
        exact htop (top_unique (fun x _ => h x))
      refine (Subgroup.index_dvd_two_iff).mpr ⟨a, fun b => ?_⟩
      by_cases hb : b ∈ J.F.subgroupOf F
      · exact Or.inr hb
      · left
        have hbJ : (b : X) ∉ J.F := fun h => hb ((Subgroup.mem_subgroupOf).mpr h)
        have haJ : (a : X) ∉ J.F := fun h => ha ((Subgroup.mem_subgroupOf).mpr h)
        have hbJ' : ((b⁻¹ : ↥F) : X) ∉ J.F := by
          intro h
          exact hbJ (by simpa using J.F.inv_mem h)
        have hkey' := hkey ((b⁻¹ : ↥F) : X) (F.inv_mem b.2) hbJ' (a : X) a.2 haJ
        exact (Subgroup.mem_subgroupOf).mpr (by simpa using hkey')
  have hidxle : (J.F.subgroupOf F).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx2
  have hidxpos : 0 < (J.F.subgroupOf F).index := by
    have h := Subgroup.index_mul_card (H := J.F.subgroupOf F)
    rcases Nat.eq_zero_or_pos (J.F.subgroupOf F).index with h0 | hpos
    · rw [h0, zero_mul] at h
      have hN : 0 < Nat.card ↥F := Nat.card_pos
      omega
    · exact hpos
  have hnormal : (J.F.subgroupOf F).Normal := by
    rcases Nat.lt_or_ge (J.F.subgroupOf F).index 2 with hlt | hge
    · exact Subgroup.normal_of_index_eq_one (by omega)
    · exact Subgroup.normal_of_index_eq_two (by omega)
  have hPSLsimple : IsSimpleGroup (PSL(2, GaloisField 3 d)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [hdcard]
      calc 4 ≤ 3 ^ 3 := by norm_num
        _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd)
  have hFsimple : IsSimpleGroup ↥F := (MulEquiv.isSimpleGroup_congr eF).mpr hPSLsimple
  have hFJ : F ≤ J.F := by
    have hnormal' : (J.F.subgroupOf F).Normal := hnormal
    rcases hFsimple.eq_bot_or_eq_top_of_normal (J.F.subgroupOf F) with hbot | htop
    · exfalso
      have hi : (J.F.subgroupOf F).index = Nat.card ↥F := by
        rw [hbot, Subgroup.index_bot]
      rw [hi] at hidxle
      omega
    · exact (Subgroup.subgroupOf_eq_top).mp htop
  let R : Subgroup (PSL(2, GaloisField J.p J.f)) := (M.subgroupOf J.F).map J.iso.toMonoidHom
  have hcard_sub : Nat.card ↥(M.subgroupOf J.F) = Nat.card ↥(M ⊓ J.F) := by
    have h := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := M ⊓ J.F) (K := J.F) inf_le_right).toEquiv
    rwa [Subgroup.inf_subgroupOf_right] at h
  have hRcardMF : Nat.card R = Nat.card ↥(M ⊓ J.F) := by
    rw [show Nat.card R = Nat.card ↥((M.subgroupOf J.F).map J.iso.toMonoidHom) from rfl,
      Subgroup.card_map_of_injective J.iso.injective, hcard_sub]
  have hFdvd : Nat.card F ∣ Nat.card ↥(M ⊓ J.F) :=
    Subgroup.card_dvd_of_le (le_inf hFM hFJ)
  have h12 : 12 ∣ Nat.card R := by
    rw [hRcardMF]
    exact h12F.trans hFdvd
  have hfodd : Odd J.f := by
    rw [hJf]
    exact ⟨k, by ring⟩
  rcases psl2_three_subgroup_cases (p := J.p) hJp hfodd R h12 with hR12 | ⟨m, hm3, hmdvd, ⟨eRm⟩⟩
  · exfalso
    have hle12 : Nat.card F ≤ 12 := by
      have h := hFdvd
      rw [← hRcardMF, hR12] at h
      exact Nat.le_of_dvd (by norm_num) h
    omega
  · have hm0 : m ≠ 0 := by omega
    have hmodd : Odd m := Odd.of_dvd_nat hfodd hmdvd
    let e' : ↥(M.subgroupOf J.F) ≃* PSL(2, GaloisField J.p m) :=
      (Subgroup.equivMapOfInjective (M.subgroupOf J.F) J.iso.toMonoidHom
        J.iso.injective).trans eRm
    have hdm : d ∣ m := by
      have hle : F.subgroupOf J.F ≤ M.subgroupOf J.F := by
        intro x hx
        exact (Subgroup.mem_subgroupOf).mpr (hFM ((Subgroup.mem_subgroupOf).mp hx))
      let K : Subgroup ↥(M.subgroupOf J.F) := (F.subgroupOf J.F).subgroupOf (M.subgroupOf J.F)
      let R' : Subgroup (PSL(2, GaloisField J.p m)) := K.map e'.toMonoidHom
      have hR' : R' ≃* PSL(2, GaloisField 3 d) :=
        (Subgroup.equivMapOfInjective K e'.toMonoidHom e'.injective).symm.trans
          ((Subgroup.subgroupOfEquivOfLe hle).trans
            ((Subgroup.subgroupOfEquivOfLe hFJ).trans eF))
      exact dvd_of_mulEquiv_psl2 (p := J.p) hJp hd hmodd R' hR'
    have hm5 : 5 < J.p ^ m := by
      rw [hJp]
      calc 5 < 3 ^ 3 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    obtain ⟨JM, hJMp, hJMf, -⟩ :=
      exists_jtHyp_subgroup J M (by rw [hJt]; exact hjM) hidx hm5 e'
    refine ⟨m, hdm, ?_, ?_⟩
    · rw [← hJf]
      exact hmdvd
    · have hcard := jtHyp_card_eq_of_three JM (hJMp.trans hJp)
      have hJMq : JM.q = 3 ^ m := by
        rw [show JM.q = JM.p ^ JM.f from rfl, hJMp, hJp, hJMf]
      rw [hJMq] at hcard
      exact hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
