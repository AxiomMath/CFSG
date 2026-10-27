module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin

variable {H : Type} [Group H] [Finite H]

theorem f112sl_oTwoRes_sup_pCoreOf {L : Subgroup H} {n : ℕ} (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L)) :
    oTwoRes L ⊔ pCoreOf 2 L = L := by
  refine le_antisymm (sup_le (oTwoRes_le L) (pCoreOf_le 2 L)) ?_
  let Q : Subgroup ↥L := CFSG.Open.pCore 2 ↥L
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' Q
  let A : Subgroup ↥L := (oTwoRes L).subgroupOf L
  have hAn : A.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoRes_le L)).mpr (le_normalizer_oTwoRes L)
  have hQ : Q = (pCoreOf 2 L).subgroupOf L := by
    ext x
    simp [Q, CFSG.Open.pCoreOf, Subgroup.mem_subgroupOf]
  have hsimple : IsSimpleGroup (oTwoQuot ↥L) := by
    obtain ⟨e⟩ := h2
    have hcard : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [GaloisField.card 2 n (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    haveI : IsSimpleGroup
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard
    exact e.isSimpleGroup
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3dvd : 3 ∣ Nat.card (oTwoQuot ↥L) := by
    rw [IsL2Quot.card (by omega) h2]
    refine Dvd.dvd.mul_left ?_ _
    have h1 : 4 ^ n % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have h2' : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega
  obtain ⟨y, hy3⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Q y
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hzodd : Odd (orderOf (x ^ 2 ^ k)) := by
    rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hord, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
    exact hm
  have hzne : π (x ^ 2 ^ k) ≠ 1 := by
    rw [map_pow, hx]
    intro h
    have hdvd : 3 ∣ 2 ^ k := by
      rw [← hy3]
      exact orderOf_dvd_of_pow_eq_one h
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at h32
  have hne : A.map π ≠ ⊥ := by
    intro hbot
    have hmem : π (x ^ 2 ^ k) ∈ A.map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr
        (Subgroup.subset_closure ⟨(x ^ 2 ^ k).2, orderOf (x ^ 2 ^ k), hzodd,
          by
            rw [← Subgroup.orderOf_coe (x ^ 2 ^ k)]
            exact pow_orderOf_eq_one ((x ^ 2 ^ k : ↥L) : H)⟩))
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hzne hmem
  have hAn' : (A.map π).Normal := hAn.map π (QuotientGroup.mk'_surjective Q)
  haveI : (A.map π).Normal := hAn'
  have hAtop : A.map π = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.map π) with h | h
    · exact absurd h hne
    · exact h
  intro l hl
  let l' : ↥L := ⟨l, hl⟩
  have hl' : π l' ∈ A.map π := by rw [hAtop]; exact Subgroup.mem_top _
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hl'
  have hker : ((a⁻¹ * l' : ↥L) : H) ∈ pCoreOf 2 L := by
    have h1 : π (a⁻¹ * l') = 1 := by
      rw [map_mul, map_inv, haeq, inv_mul_cancel]
    have h2 : a⁻¹ * l' ∈ Q := (QuotientGroup.eq_one_iff (a⁻¹ * l')).mp h1
    rw [hQ] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have haM : (a : H) ∈ oTwoRes L := Subgroup.mem_subgroupOf.mp ha
  have hl_eq : l' = a * (a⁻¹ * l') := by group
  have hval : l = (a : H) * ((a⁻¹ * l' : ↥L) : H) := by
    have h := congrArg (fun z : ↥L => (z : H)) hl_eq
    exact h
  change l ∈ oTwoRes L ⊔ pCoreOf 2 L
  rw [hval]
  exact Subgroup.mul_mem_sup haM hker

end CFSG.Quasithin.F112R.St84
