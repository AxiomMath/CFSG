module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusTools
public import CFSG.Sporadic.Schreier.RuAutInner
public import Certificates.Certificate8038
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG.Blueprint CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native
open scoped commutatorElement

theorem ruSyl_facts :
    (∃ S : Subgroup (Equiv.Perm (Fin 4060)), S ≤ ruP ∧ Nat.card S = 27 ∧
      ∀ g ∈ S, g ≠ 1 → ¬ 7 ∣ {p : Fin 4060 | g p = p}.ncard) ∧
    (∃ w ∈ ruP, orderOf w = 7 ∧ ∀ p : Fin 4060, w p ≠ p) :=
  Certificates.certificate8038

theorem finite_ruP :
    Finite ruP :=
  Nat.finite_of_card_ne_zero (by rw [card_ruP]; norm_num)

theorem exists_conj_mem_of_isPGroup
    {p n : ℕ} [Fact p.Prime]
    {Q : Subgroup (Equiv.Perm (Fin 4060))} (hQp : IsPGroup p (Q.subgroupOf ruP))
    (hQi : ¬ p ∣ (Q.subgroupOf ruP).index) {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hgo : orderOf g = p ^ n) : ∃ c ∈ ruP, c * g * c⁻¹ ∈ Q := by
  have := finite_ruP
  set Q₁ : Sylow p ruP := hQp.toSylow hQi with hQ₁
  set g' : ruP := ⟨g, hg⟩ with hg'
  have hp : IsPGroup p (Subgroup.zpowers g') :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hgo])
  obtain ⟨Q₂, hQ₂⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ruP Q₂ Q₁
  refine ⟨c, c.2, ?_⟩
  have hmem : g' ∈ (Q₂ : Subgroup ruP) := hQ₂ (Subgroup.mem_zpowers g')
  have h1 : MulAut.conj c • g' ∈ ((c • Q₂ : Sylow p ruP) : Subgroup ruP) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
  rw [hc, hQ₁, IsPGroup.toSylow_coe, Subgroup.mem_subgroupOf] at h1
  simpa [MulAut.smul_def, MulAut.conj_apply, hg'] using h1

theorem ncard_fixedPoints_conj (c g : Equiv.Perm (Fin 4060)) :
    {p : Fin 4060 | (c * g * c⁻¹) p = p}.ncard = {p : Fin 4060 | g p = p}.ncard := by
  have e : {p : Fin 4060 | (c * g * c⁻¹) p = p} = c '' {p : Fin 4060 | g p = p} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_image, Equiv.Perm.mul_apply]
    constructor
    · intro hp
      refine ⟨c⁻¹ p, ?_, by simp⟩
      have := congrArg (⇑(c⁻¹)) hp
      simpa using this
    · rintro ⟨q, hq, rfl⟩
      simp [hq]
  rw [e, Set.ncard_image_of_injective _ c.injective]

theorem pow_ne_of_orderOf_eq_seven {w : Equiv.Perm (Fin 4060)} (hw7 : orderOf w = 7)
    (hw : ∀ p, w p ≠ p) {k : ℕ} (hk0 : k % 7 ≠ 0) (p : Fin 4060) : (w ^ k) p ≠ p := by
  intro hp
  obtain ⟨m, hm⟩ : ∃ m, k * m % 7 = 1 := by
    rcases (by omega : k % 7 = 1 ∨ k % 7 = 2 ∨ k % 7 = 3 ∨ k % 7 = 4 ∨ k % 7 = 5 ∨
      k % 7 = 6) with h | h | h | h | h | h
    · exact ⟨1, by omega⟩
    · exact ⟨4, by omega⟩
    · exact ⟨5, by omega⟩
    · exact ⟨2, by omega⟩
    · exact ⟨3, by omega⟩
    · exact ⟨6, by omega⟩
  have e : (w ^ k) ^ m = w := by
    rw [← pow_mul, ← pow_mod_orderOf, hw7, hm, pow_one]
  apply hw p
  rw [← e]
  exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hp m

theorem ne_of_orderOf_eq_seven
    {h : Equiv.Perm (Fin 4060)}
    (hh : h ∈ ruP) (h7 : orderOf h = 7) (p : Fin 4060) : h p ≠ p := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨-, w, hwP, hw7, hwfix⟩ := ruSyl_facts
  have hWP : Subgroup.zpowers w ≤ ruP := (Subgroup.zpowers_le).2 hwP
  have hWcard : Nat.card ((Subgroup.zpowers w).subgroupOf ruP) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWP).toEquiv, Nat.card_zpowers, hw7]
  have hWp : IsPGroup 7 ((Subgroup.zpowers w).subgroupOf ruP) :=
    IsPGroup.of_card (n := 1) (by rw [hWcard, pow_one])
  have hWi : ¬ 7 ∣ ((Subgroup.zpowers w).subgroupOf ruP).index := by
    have h := ((Subgroup.zpowers w).subgroupOf ruP).card_mul_index
    rw [hWcard, card_ruP] at h
    have hi : ((Subgroup.zpowers w).subgroupOf ruP).index = 20846592000 := by omega
    rw [hi]
    norm_num
  obtain ⟨c, -, hc⟩ := exists_conj_mem_of_isPGroup (n := 1) hWp hWi hh (by rw [h7, pow_one])
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.2 hc : c * h * c⁻¹ ∈ Submonoid.powers w)
  replace hk : w ^ k = c * h * c⁻¹ := hk
  intro hp
  have hk0 : k % 7 ≠ 0 := by
    intro h0
    rw [← pow_mod_orderOf, hw7, h0, pow_zero] at hk
    have h1 : h = 1 := by
      calc h = c⁻¹ * (c * h * c⁻¹) * c := by group
        _ = 1 := by rw [← hk]; group
    rw [h1, orderOf_one] at h7
    exact absurd h7 (by norm_num)
  apply pow_ne_of_orderOf_eq_seven hw7 hwfix hk0 (c p)
  rw [hk]
  simp [hp]

section Orders

theorem not_seven_dvd_ncard_fixedPoints {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hg3 : orderOf g = 3) : ¬ 7 ∣ {p : Fin 4060 | g p = p}.ncard := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨S₀, hS₀, hS27, hSfix⟩, -⟩ := ruSyl_facts
  have hScard : Nat.card (S₀.subgroupOf ruP) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀).toEquiv, hS27]
  have hSp : IsPGroup 3 (S₀.subgroupOf ruP) := IsPGroup.of_card (n := 3) hScard
  have hSi : ¬ 3 ∣ (S₀.subgroupOf ruP).index := by
    have h := (S₀.subgroupOf ruP).card_mul_index
    rw [hScard, card_ruP] at h
    have hi : (S₀.subgroupOf ruP).index = 5404672000 := by omega
    rw [hi]
    norm_num
  obtain ⟨c, -, hc⟩ := exists_conj_mem_of_isPGroup (n := 1) hSp hSi hg (by rw [hg3, pow_one])
  have hne : c * g * c⁻¹ ≠ 1 := by
    intro h1
    have : g = 1 := by
      calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hg3
    exact absurd hg3 (by norm_num)
  have h := hSfix _ hc hne
  rwa [ncard_fixedPoints_conj] at h

theorem false_of_commute {g h : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP) (hh : h ∈ ruP)
    (hg3 : orderOf g = 3) (hh7 : orderOf h = 7) (hgh : g * h = h * g) : False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hinv : ∀ p : Fin 4060, g p = p ↔ g (h p) = h p := by
    intro p
    have e : g (h p) = h (g p) := by
      rw [← Equiv.Perm.mul_apply, hgh, Equiv.Perm.mul_apply]
    rw [e]
    exact h.injective.eq_iff.symm
  set σ : Equiv.Perm {p : Fin 4060 // g p = p} := h.subtypePerm fun p => (hinv p).symm with hσ
  have hσ7 : σ ^ 7 ^ 1 = 1 := by
    rw [pow_one, hσ, Equiv.Perm.subtypePerm_pow]
    ext q
    simp [← hh7, pow_orderOf_eq_one]
  have hcard : ¬ 7 ∣ Fintype.card {p : Fin 4060 // g p = p} := by
    rw [← Nat.card_eq_fintype_card]
    have := not_seven_dvd_ncard_fixedPoints hg hg3
    rwa [← Nat.card_coe_set_eq] at this
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 7) (n := 1) hcard hσ7
  exact ne_of_orderOf_eq_seven hh hh7 a.1 (congrArg Subtype.val ha)

end Orders

theorem eq_one_of_suzukiOrder_dvd_ru {a : ℕ} (ha : 1 ≤ a)
    (h : suzukiOrder a ∣ 145926144000) : a = 1 := by
  have ha8 : a ≤ 8 := le_of_suzukiOrder_dvd (B := 8) (by norm_num) (by norm_num) h
  interval_cases a
  · rfl
  all_goals exact absurd h (by decide)

theorem threePrimeB3_ruP :
    ThreePrimeB3 ruP := by
  intro β hβ C Y R hC hYC hsn hYp _ hRY hRn hRs hsz
  obtain ⟨g, rfl⟩ := mulAut_inner β
  have hg3 : g ^ 3 = 1 := by
    have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow]; exact hβ
    have h2 : g ^ 3 ∈ Subgroup.center ruP := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun φ : MulAut ruP => φ x) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g ^ 3 = g ^ 3 * x * (g ^ 3)⁻¹ * g ^ 3 := by rw [this]
        _ = g ^ 3 * x := by group
    rw [center_ruP, Subgroup.mem_bot] at h2
    exact h2
  by_cases hg1 : g = 1
  · subst hg1
    have hCtop : C = ⊤ := by
      ext z
      simp [hC z]
    have := isSimpleGroup_ruP
    have hsimp : IsSimpleGroup C :=
      ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
    exact commutator_eq_bot_of_isSimpleGroup_or_isSolvable (Or.inl hsimp) hYC hsn hYp hRY hRn hRs
  · exfalso
    have hgo : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    obtain ⟨f, hf⟩ := hsz
    obtain ⟨a, ha, hcard⟩ := card_eq_suzukiOrder hf
    have hdvd : suzukiOrder a ∣ Nat.card C := by
      rw [← hcard]
      exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hYC)
    have ha1 : a = 1 := eq_one_of_suzukiOrder_dvd_ru ha
      (card_ruP ▸ hdvd.trans (Subgroup.card_subgroup_dvd_card C))
    subst ha1
    have h7 : 7 ∣ Nat.card C := (show 7 ∣ suzukiOrder 1 by decide).trans hdvd
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have := finite_ruP
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' 7 h7
    have hhC : MulAut.conj g (h : ruP) = h := (hC h).mp h.2
    rw [MulAut.conj_apply] at hhC
    refine false_of_commute g.2 (h : ruP).2 (by rw [Subgroup.orderOf_coe, hgo])
      (by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hh]) ?_
    have e : g * (h : ruP) = (h : ruP) * g := by
      calc g * (h : ruP) = g * (h : ruP) * g⁻¹ * g := by group
        _ = (h : ruP) * g := by rw [hhC]
    exact congrArg Subtype.val e

theorem threePrimeB3_ru :
    ThreePrimeB3 (NativeSporadic.Carrier .Ru) :=
  threePrimeB3_of_mulEquiv (Q := NativeSporadic.Carrier .Ru) ruEquivP threePrimeB3_ruP

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
