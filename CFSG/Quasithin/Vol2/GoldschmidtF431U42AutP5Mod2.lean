module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Mod1
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Nrm

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem Q1_le_P1h : Q1 ≤ P1h :=
  Q1_le_That.trans (That_le_Bh.trans Bh_le_P1h)

theorem card_pCore_P1h_ge :
    32 ≤ Nat.card (CFSG.Open.pCore 2 ↥P1h) := by
  have hn : (Q1.subgroupOf P1h).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := Q1_conj_mem g.2 hn
    simpa using this⟩
  have hp : IsPGroup 2 (Q1.subgroupOf P1h) :=
    (isSylowTwoOf_That_Bh.2.1.to_le Q1_le_That).of_equiv
      (Subgroup.subgroupOfEquivOfLe Q1_le_P1h).symm
  have hle : Q1.subgroupOf P1h ≤ CFSG.Open.pCore 2 ↥P1h :=
    CFSG.LieType.BorelTits.le_pCore 2 hn hp
  have h1 := Subgroup.card_le_of_le hle
  have h2 : Nat.card (Q1.subgroupOf P1h) = Nat.card Q1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q1_le_P1h).toEquiv
  exact card_Q1_ge.trans (h2 ▸ h1)

theorem c3_not_normalizes_That : comp (comp c3L fhatL) (comp c3L c3L) ∉ Thl := by
  decide +kernel

theorem mem_That_of_normalizes
    {y : Ah} (hy : y ∈ Subgroup.normalizer (That : Set Ah)) (hyB : y ∈ Bh) : y ∈ That := by
  set N := Subgroup.normalizer (That : Set Ah) ⊓ Bh with hN
  have hTN : That ≤ N := le_inf Subgroup.le_normalizer That_le_Bh
  have h128 : 128 ∣ Nat.card N := card_That ▸ Subgroup.card_dvd_of_le hTN
  have h384 : Nat.card N ∣ 384 := card_Bh ▸ Subgroup.card_dvd_of_le inf_le_right
  have hcases : Nat.card N = 128 ∨ Nat.card N = 384 := by
    obtain ⟨m, hm⟩ := h128
    have hm3 : m ∣ 3 := by
      have : 128 * m ∣ 128 * 3 := by simpa [hm] using h384
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hm3 with rfl | rfl
    · left; simpa using hm
    · right; simpa using hm
  rcases hcases with h | h
  · have : N = That := (Subgroup.eq_of_le_of_card_ge hTN (by rw [h, card_That])).symm
    have hyN : y ∈ N := ⟨hy, hyB⟩
    rw [this] at hyN
    exact hyN
  · exfalso
    have hNB : N = Bh := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, card_Bh])
    have hc3 : c3A ∈ Subgroup.normalizer (That : Set Ah) := by
      have : c3A ∈ N := hNB ▸ c3A_mem_Bh
      exact this.1
    have h1 : c3A * fhatA * c3A⁻¹ ∈ That := (Subgroup.mem_normalizer_iff.1 hc3 fhatA).1
      fhatA_mem_That
    obtain ⟨l, hl, hrep⟩ := (mem_That_iff _).1 h1
    have hc3 : RepL c3L ((c3A : Ah) : P45) := U42.repL_c3
    have hc3i : RepL (comp c3L c3L) (((c3A : Ah) : P45)⁻¹) := U42.repL_c3_inv
    have h2 : RepL (comp (comp c3L fhatL) (comp c3L c3L))
        ((c3A * fhatA * c3A⁻¹ : Ah) : P45) := repL_mul (repL_mul hc3 repL_fhat) hc3i
    exact c3_not_normalizes_That (by rw [repL_unique h2 hrep]; exact hl)

theorem twoPart_P1h :
    twoPart (⊤ : Subgroup ↥P1h) = 128 := by
  rw [twoPart_eq_of_card_eq (k := 7) (m := 9) (by norm_num)
    (by rw [Subgroup.card_top, card_P1h]; norm_num)]
  norm_num

theorem P1h_selfNormalizing :
    ∀ S : Subgroup ↥P1h, IsSylowTwoOf S ⊤ → Subgroup.normalizer (S : Set ↥P1h) ≤ S := by
  intro S hS
  have hThatP : That ≤ P1h := That_le_Bh.trans Bh_le_P1h
  set T' : Subgroup ↥P1h := That.subgroupOf P1h with hT'
  have hTcard : Nat.card T' = 128 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hThatP).toEquiv).trans card_That
  have hT'syl : IsSylowTwoOf T' ⊤ := by
    refine isSylowTwoOf_of_card_eq le_top ?_ ?_
    · exact isSylowTwoOf_That_Bh.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hThatP).symm
    · rw [hTcard, twoPart_P1h]
  obtain ⟨c, hc⟩ := U42.exists_conj_isSylowTwoOf_top hT'syl hS
  intro n hn
  have hmemS : ∀ h : ↥P1h, h ∈ T' ↔ c * h * c⁻¹ ∈ S := by
    intro h
    rw [← hc]
    constructor
    · intro hh
      exact ⟨h, hh, rfl⟩
    · rintro ⟨y, hy, hyc⟩
      have : y = h := by
        have h1 : c * y * c⁻¹ = c * h * c⁻¹ := hyc
        simpa using h1
      rwa [← this]
  set n' : ↥P1h := c⁻¹ * n * c with hn'
  have hnn : ∀ h : ↥P1h, h ∈ T' ↔ n' * h * n'⁻¹ ∈ T' := by
    intro h
    rw [hmemS h, hmemS (n' * h * n'⁻¹)]
    have e : c * (n' * h * n'⁻¹) * c⁻¹ = n * (c * h * c⁻¹) * n⁻¹ := by
      rw [hn']
      group
    rw [e]
    exact Subgroup.mem_normalizer_iff.1 hn _
  have hnorm : (n' : Ah) ∈ Subgroup.normalizer (That : Set Ah) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have := (hnn ⟨a, hThatP ha⟩).1 ha
      exact this
    · intro ha
      have haP : a ∈ P1h := by
        have h1 : (n' : Ah)⁻¹ * ((n' : Ah) * a * (n' : Ah)⁻¹) * (n' : Ah) ∈ P1h :=
          P1h.mul_mem (P1h.mul_mem (P1h.inv_mem n'.2) (hThatP ha)) n'.2
        simpa [mul_assoc] using h1
      exact (hnn ⟨a, haP⟩).2 ha
  have hn'That : (n' : Ah) ∈ That :=
    mem_That_of_normalizes hnorm (normalizer_That_le_Bh hnorm)
  have hn'T : n' ∈ T' := hn'That
  have : n = c * n' * c⁻¹ := by rw [hn']; group
  rw [this, ← hc]
  exact ⟨n', hn'T, rfl⟩

theorem a4_in_P1h {v b : ↥P1h}
    (hv : v * v = 1) (hb : b * b * b = 1) (hvw : b * v * b⁻¹ ≠ v)
    (hcomm : v * (b * v * b⁻¹) = (b * v * b⁻¹) * v)
    (hrel : b * (b * v * b⁻¹) * b⁻¹ = v * (b * v * b⁻¹)) :
    v ∈ CFSG.Open.pCore 2 ↥P1h := by
  have hQ := CFSG.LieType.BorelTits.pCore_normal 2 (G := ↥P1h)
  have hp := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥P1h)
  have hcard : twoPart (⊤ : Subgroup ↥P1h) ≤ 4 * Nat.card (CFSG.Open.pCore 2 ↥P1h) := by
    rw [twoPart_P1h]
    have := card_pCore_P1h_ge
    omega
  exact klein_le_of_a4 hQ hp hcard P1h_selfNormalizing hv hb hvw hcomm hrel

end CFSG.Quasithin.H13.F431.U42Aut
