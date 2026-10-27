module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec117G2
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley
open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 CFSG.HardMathSupport.Kantor79 QuadraticMap Module

theorem not_dvd_two_of_dvd_two_pow_sub_one {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (h : p ∣ 2 ^ n - 1) : ¬ p ∣ 2 := by
  intro h2
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  subst hp2
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem two_pow_mul_eq (e k : ℕ) : (2 ^ e) ^ k = 2 ^ (k * e) := by
  rw [← pow_mul, mul_comm]

theorem not_card_g2_dvd_o6_plus {e : ℕ} (he : 2 ≤ e) :
    ¬ (2 ^ e) ^ 6 * ((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 2 - 1) ∣
      2 * (2 ^ e) ^ 6 * ((2 ^ e) ^ 3 - 1) * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 4 - 1) := by
  intro h
  obtain ⟨p, hp, hpd, hpk⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (6 * e) (by omega) (by omega)
  have hpL : p ∣ (2 ^ e) ^ 6 * ((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 2 - 1) := by
    rw [two_pow_mul_eq e 6]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpd _) _
  have h2 := not_dvd_two_of_dvd_two_pow_sub_one hp (by omega) hpd
  have hpR := hpL.trans h
  simp only [two_pow_mul_eq e] at hpR
  rcases (Nat.Prime.dvd_mul hp).mp hpR with hpR | h4
  · rcases (Nat.Prime.dvd_mul hp).mp hpR with hpR | h2'
    · rcases (Nat.Prime.dvd_mul hp).mp hpR with hpR | h3
      · rcases (Nat.Prime.dvd_mul hp).mp hpR with h2'' | h6
        · exact h2 h2''
        · exact h2 (hp.dvd_of_dvd_pow h6)
      · exact hpk (3 * e) (by omega) (by omega) h3
    · exact hpk (2 * e) (by omega) (by omega) h2'
  · exact hpk (4 * e) (by omega) (by omega) h4

theorem not_card_g2_dvd_o6_minus {e : ℕ} (he : 2 ≤ e) :
    ¬ (2 ^ e) ^ 6 * ((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 2 - 1) ∣
      2 * (2 ^ e) ^ 6 * ((2 ^ e) ^ 3 + 1) * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 4 - 1) := by
  rcases Nat.eq_or_lt_of_le he with rfl | he3
  · norm_num
  intro h
  obtain ⟨p, hp, hpd, hpk⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (3 * e) (by omega) (by omega)
  have hA : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hB : 1 ≤ 2 ^ (3 * e) := Nat.one_le_two_pow
  have h6 : 2 ^ (3 * e) - 1 ∣ 2 ^ (6 * e) - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ (3 * e)) 1 2
    rwa [one_pow, ← pow_mul, show 3 * e * 2 = 6 * e by ring] at this
  have hpL : p ∣ (2 ^ e) ^ 6 * ((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 2 - 1) := by
    rw [two_pow_mul_eq e 6]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hpd.trans h6) _) _
  have h2 := not_dvd_two_of_dvd_two_pow_sub_one hp (by omega) hpd
  have hpR := hpL.trans h
  simp only [two_pow_mul_eq e] at hpR
  rcases (Nat.Prime.dvd_mul hp).mp hpR with hpR | h4
  · rcases (Nat.Prime.dvd_mul hp).mp hpR with hpR | h2'
    · rcases (Nat.Prime.dvd_mul hp).mp hpR with hpR | h3
      · rcases (Nat.Prime.dvd_mul hp).mp hpR with h2'' | h6'
        · exact h2 h2''
        · exact h2 (hp.dvd_of_dvd_pow h6')
      ·
        refine h2 ?_
        have := Nat.dvd_sub h3 hpd
        rwa [show 2 ^ (3 * e) + 1 - (2 ^ (3 * e) - 1) = 2 by omega] at this
    · exact hpk (2 * e) (by omega) (by omega) h2'
  ·
    refine hpk e (by omega) (by omega) ?_
    have hmul : p ∣ 2 ^ e * (2 ^ (3 * e) - 1) := dvd_mul_of_dvd_right hpd _
    have := Nat.dvd_sub h4 hmul
    have hsplit : 2 ^ (4 * e) = 2 ^ e * 2 ^ (3 * e) := by rw [← pow_add]; ring_nf
    rwa [hsplit, Nat.mul_sub_one, show 2 ^ e * 2 ^ (3 * e) - 1 - (2 ^ e * 2 ^ (3 * e) - 2 ^ e) =
      2 ^ e - 1 by
        have : 2 ^ e ≤ 2 ^ e * 2 ^ (3 * e) := Nat.le_mul_of_pos_right _ (by omega)
        omega] at this

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem Ctx.not_lieModel_g2_of_two_pow_eq (hc : Ctx M Q Z B) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    {x : ℕ} (hLie : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .G2 0 2 x)
    (hxZ : 2 ^ x = Nat.card Z) : False := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφk, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  have hKZ : Nat.card K = Nat.card Z := hD.card
  have hx2 : 2 ≤ x := two_le_of_lieModel_g2 hLie
  have hK : Nat.card K = 2 ^ x := hKZ.trans hxZ.symm
  have hK4 : 4 ≤ Nat.card K := hKZ ▸ hc.hyp.q4
  obtain ⟨K', _, _, _, hK', ρV, hρinj, hρQ, hV, t₀, ht₀⟩ :=
    hc.exists_g2_cmComm_action ha2 hLie hD φ hφπ hφk hφQ
  have hnd := hc.cmCommQf_nondegenerate hD φ hφπ
  have h6 : finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 6 :=
    finrank_eq_six_of_g2 hK4 hnd ρV hρinj hρQ hV (hK'.trans hK.symm) (MulEquiv.refl _) ht₀
      (g2_short_class_not_admissible K')
      (g2_exists_long_root_generators K' (by rw [hK']; exact hK ▸ hK4))
  have hle : ρV.range ≤ TauCeti.QuadraticMap.orthogonalGroup (cmCommQf B φ) := by
    rintro _ ⟨g, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hρQ g)
  have hdvd : Nat.card (adjointGroup .G2 K') ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (cmCommQf B φ)) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  rw [(CFSG.LieType.Chevalley.exact_G2_finite_order K' hK').2.1] at hdvd
  have hnd' := nondegenerate_polarBilin hnd
  have hdim : finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 2 * (2 + 1) := by rw [h6]
  have hIcc : ∀ f : ℕ → ℤ, ∏ i ∈ Finset.Icc 1 2, f i = f 1 * f 2 := fun f => by
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by decide)]
  have hA : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (cmCommQf B φ)
  · have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd' hdim
      (Or.inl ⟨rfl, hplus⟩)
    rw [hK, hIcc] at hO
    have hO' : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (cmCommQf B φ)) =
        2 * (2 ^ x) ^ 6 * ((2 ^ x) ^ 3 - 1) * ((2 ^ x) ^ 2 - 1) * ((2 ^ x) ^ 4 - 1) := by
      have h3 : 1 ≤ (2 ^ x) ^ 3 := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ (2 ^ x) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h4 : 1 ≤ (2 ^ x) ^ 4 := Nat.one_le_pow _ _ (by omega)
      zify [h3, h2, h4]
      rw [hO]
      push_cast
      ring
    rw [hO'] at hdvd
    exact not_card_g2_dvd_o6_plus hx2 hdvd
  · have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd' hdim
      (Or.inr ⟨rfl, hplus⟩)
    rw [hK, hIcc] at hO
    have hO' : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (cmCommQf B φ)) =
        2 * (2 ^ x) ^ 6 * ((2 ^ x) ^ 3 + 1) * ((2 ^ x) ^ 2 - 1) * ((2 ^ x) ^ 4 - 1) := by
      have h2 : 1 ≤ (2 ^ x) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h4 : 1 ≤ (2 ^ x) ^ 4 := Nat.one_le_pow _ _ (by omega)
      zify [h2, h4]
      rw [hO]
      push_cast
      ring
    rw [hO'] at hdvd
    exact not_card_g2_dvd_o6_minus hx2 hdvd

end CFSG.RankThree.GF2n.Stroth80
