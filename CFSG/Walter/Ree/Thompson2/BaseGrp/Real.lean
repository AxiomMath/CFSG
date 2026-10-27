module

public import CFSG.Walter.ReeOrder.WardLocal.Four
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Walter.Ree.Thompson2.BaseGrp.Setup

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

open CFSG.Walter.Ward

variable {G : Type} [Group G] [Finite G]

theorem exists_inv_of_inverted {p : ℕ} [Fact p.Prime] {A : Subgroup G} {ι : G}
    (hι : ∀ a ∈ A, ι * a * ι⁻¹ = a⁻¹) (hp : ¬ p ∣ A.index) {c : G}
    (hc : IsPGroup p (Subgroup.zpowers c)) : ∃ n : G, n * c * n⁻¹ = c⁻¹ := by
  obtain ⟨P⟩ : Nonempty (Sylow p A) := inferInstance
  have hPm : IsPGroup p ((P : Subgroup A).map A.subtype) := P.isPGroup'.map _
  obtain ⟨Q, hQ⟩ := hPm.exists_le_sylow
  have hcard : Nat.card Q ≤ Nat.card ((P : Subgroup A).map A.subtype) := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, Sylow.card_eq_multiplicity,
      Sylow.card_eq_multiplicity, ← Subgroup.card_mul_index A, Nat.factorization_mul
      Nat.card_pos.ne' (Subgroup.index_ne_zero_of_finite), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hp, add_zero]
  have hQeq : ((P : Subgroup A).map A.subtype) = Q := Subgroup.eq_of_le_of_card_ge hQ hcard
  obtain ⟨Q', hQ'⟩ := hc.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q Q'
  have hcQ : c ∈ (Q' : Subgroup G) := hQ' (Subgroup.mem_zpowers c)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hcQ
  rw [← hQeq] at hcQ
  obtain ⟨a, -, ha⟩ := hcQ
  have ha' : (a : G) = g⁻¹ * c * g := by
    change A.subtype a = _
    rw [ha, MulAut.smul_def, ← map_inv, MulAut.conj_apply]
    group
  refine ⟨g * ι * g⁻¹, ?_⟩
  have := hι a a.2
  rw [ha'] at this
  calc g * ι * g⁻¹ * c * (g * ι * g⁻¹)⁻¹ = g * (ι * (g⁻¹ * c * g) * ι⁻¹) * g⁻¹ := by group
    _ = c⁻¹ := by rw [this]; group

theorem exists_inv_of_orderOf_seven
    (h : ReeTypeHyp G) {c : G} (hc : orderOf c = 7) :
    ∃ n : G, n * c * n⁻¹ = c⁻¹ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp7 : IsPGroup 7 (Subgroup.zpowers c) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hc, pow_one])
  obtain ⟨⟨n, hn, hq⟩, hG⟩ := ward_order h
  have h7G : 7 ∣ Nat.card G := hc ▸ orderOf_dvd_natCard c
  set q := h.q with hqdef
  obtain ⟨h7q, h7q1⟩ := seven_not_dvd_q (n := n)
  rw [← hq] at h7q h7q1
  have hq3 : 27 ≤ q := by
    rw [hq]; calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h7a : 7 ∣ q ^ 3 + 1 := by
    rw [hG] at h7G
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h7G with h1 | h1
    · rcases (Nat.Prime.dvd_mul (by norm_num)).mp h1 with h2 | h2
      · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h2) h7q
      · exact h2
    · exact absurd h1 h7q1
  have hfac : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    have : q ≤ q ^ 2 := by nlinarith
    zify [this]
    ring
  obtain ⟨hm, hM⟩ := WardLocal.ward_four h (k := n) hq
  rw [hfac] at h7a
  rcases (Nat.Prime.dvd_mul (by norm_num)).mp h7a with hB | hA
  ·
    have hF := JT.psl2Facts h.L h.iso h.p_ne_two (by change 5 < q; omega)
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := h.L) 2 (by
      rw [hF.card]
      have hodd : Odd q := by rw [hq]; exact Odd.pow (by decide)
      obtain ⟨r, hr⟩ := hodd
      change 2 ∣ q * (q ^ 2 - 1) / 2
      rw [hr]
      refine ⟨(2 * r + 1) * (r * (r + 1)), ?_⟩
      have : (2 * r + 1) ^ 2 - 1 = 4 * (r * (r + 1)) := by
        have : (2 * r + 1) ^ 2 = 4 * (r * (r + 1)) + 1 := by ring
        omega
      rw [this, show (2 * r + 1) * (4 * (r * (r + 1))) = 2 * (2 * ((2 * r + 1) * (r * (r + 1))))
        by ring, Nat.mul_div_cancel_left _ (by norm_num)])
    have hv2 : orderOf (v : G) = 2 := by rw [Subgroup.orderOf_coe, hv]
    obtain ⟨U, w, hU, -, hUcard⟩ := hF.even_torus v v.2 hv2
    have hq4 : q % 4 = 3 := by
      rw [hq, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
    have hUc : 2 * Nat.card U = q + 1 := by
      rcases hUcard with ⟨-, h1⟩ | ⟨h1, -⟩
      · exact h1
      · change q % 4 = 1 at h1; omega
    refine exists_inv_of_inverted (A := U) (ι := w) hU.inv ?_ hp7
    have hidx : Nat.card U * U.index = Nat.card U * (2 * (q ^ 3 * (q ^ 2 - q + 1) * (q - 1))) := by
      rw [Subgroup.card_mul_index, hG, hfac]
      have : q + 1 = 2 * Nat.card U := hUc.symm
      rw [this]
      ring
    have hUpos : 0 < Nat.card U := Nat.card_pos
    rw [Nat.eq_of_mul_eq_mul_left hUpos hidx]
    have h7' : ¬ 7 ∣ q ^ 2 - q + 1 := by
      intro h'
      have : (q ^ 2 - q + 1) % 7 = 3 := by
        have hq7 : q % 7 = 6 := by omega
        have : q ≤ q ^ 2 := by nlinarith
        have e : q ^ 2 - q + 1 = (q - 1) * q + 1 := by
          zify [this, (by omega : 1 ≤ q)]; ring
        rw [e, Nat.add_mod, Nat.mul_mod]
        rw [show (q - 1) % 7 = 5 by omega, hq7]
      omega
    intro h'
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h' with h1 | h1
    · omega
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul (by norm_num)).mp h2 with h3 | h3
      · exact h7q (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3)
      · exact h7' h3
    · exact h7q1 h2
  ·
    rw [hm] at hA
    have hcase : ∃ s : Bool, 7 ∣ (if s then q + 1 + 3 * 3 ^ n else q + 1 - 3 * 3 ^ n) := by
      rcases (Nat.Prime.dvd_mul (by norm_num)).mp hA with h1 | h1
      · exact ⟨true, by simpa using h1⟩
      · exact ⟨false, by simpa using h1⟩
    obtain ⟨s, hs⟩ := hcase
    obtain ⟨M, W, -, hMc, hcop, -, -, hWc, hW6, -, hN, hfpf⟩ := hM s
    obtain ⟨⟨ι, hιW⟩, hι2⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 (by rw [hW6]; norm_num)
    have hι : orderOf ι = 2 := by rw [← Subgroup.orderOf_mk ι hιW, hι2]
    have hιι : ι * ι = 1 := by rw [← sq, ← hι, pow_orderOf_eq_one]
    have hι1 : ι ≠ 1 := by rintro rfl; simp at hι
    have hιN : ι ∈ Subgroup.normalizer (M : Set G) := by rw [hN]; exact Subgroup.mem_sup_right hιW
    have hinv := JT.inv_of_inf_centralizer_eq_bot hιι hιN (hfpf ι hιW hι1)
    refine exists_inv_of_inverted (A := M) (ι := ι) hinv ?_ hp7
    intro h7
    rw [← hMc] at hs
    exact (by norm_num : ¬ 7 ∣ 1) (hcop ▸ Nat.dvd_gcd hs h7)

end CFSG.Walter.Ree.T2.BaseGrp
