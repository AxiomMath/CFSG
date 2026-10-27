module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeRankOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.Quasithin.SteinbergBT

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.QuasithinUnique.Setup.X6

theorem prime_dvd_of_odd_dvd_two_pow_mul_prime_pow {p m b c : ℕ} (hp : p.Prime) (hm : Odd m)
    (hm1 : m ≠ 1) (h : m ∣ 2 ^ b * p ^ c) : p ∣ m := by
  have hcop : Nat.Coprime m (2 ^ b) := Nat.Coprime.pow_right b (Nat.coprime_two_right.2 hm)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (hcop.dvd_of_dvd_mul_left h)
  rcases i with _ | i
  · exact absurd (by rw [hi, pow_zero]) hm1
  · rw [hi]
    exact dvd_pow_self p (Nat.succ_ne_zero i)

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem reeLocalBlock_le_of_canonicalRep_mem
    {D : Subgroup (ModGL F4.tag K)}
    (hUD : F4.reeFixedPosUnipotent K a ≤ D) (j : Fin F4.fixedOrbitCount)
    (hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ D) :
    F4.reeLocalBlock K a j ≤ D :=
  sup_le ((reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j).trans hUD)
    (reeFixedOrbitNegUnipotent_le_of_posUnipotent hUD (fixedOrbitElement_mem j) (h := 1)
      (one_mem _) (by rwa [one_mul]) fun α hα => by
        rw [fixedOrbitElement_inv]
        exact height_fixedOrbitElement_smul_neg hα)

theorem large_Ree_two_prime_positive_subgroup_overgroups_are_Borel
    (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D : Subgroup (ModGL F4.tag K)} (hDΓ : D ≤ F4.reeGamma K a)
    (hUD : F4.reeFixedPosUnipotent K a ≤ D) {b c : ℕ} (hD : Nat.card D = 2 ^ b * p ^ c) :
    D ≤ F4.reeFixedBorel K a := by
  obtain ⟨hle, -, -⟩ := large_Ree_positive_root_overgroup_parabolic_containment hK hDΓ hUD
  have hq8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqeven : Even (2 ^ (2 * a + 1)) := Nat.even_pow.2 ⟨even_two, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ (2 * a + 1) = m + 1 := ⟨2 ^ (2 * a + 1) - 1, by omega⟩
  rw [hm] at hq8 hqeven
  have hmodd : Odd m := by
    obtain ⟨r, hr⟩ := hqeven
    exact ⟨r - 1, by omega⟩
  have hpm : ∀ k : ℕ, Odd k → k ≠ 1 → k ∣ Nat.card D → p ∣ k := fun k hk hk1 h =>
    prime_dvd_of_odd_dvd_two_pow_mul_prime_pow hp hk hk1 (hD ▸ h)
  have hp2' : ¬p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hpm1 : p ∣ m → p ∣ m * (m + 2) + 2 → False := fun h1 h2 =>
    hp2' ((Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).1 h2)
  have hJ : {j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ D} = ∅ := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hn
    have hMD := reeLocalBlock_le_of_canonicalRep_mem hUD j hn
    obtain ⟨⟨h1, -, -⟩, ⟨h2, -, -⟩⟩ :=
      large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
    match j, hMD with
    | ⟨0, _⟩, hMD =>
      rw [h1] at hMD
      have hdvd := card_dvd_of_le hMD
      rw [card_rankOneGroupOne hK, hm, show (m + 1) ^ 2 = m * (m + 2) + 1 by ring,
        Nat.add_sub_cancel] at hdvd
      have h3 : p ∣ m := hpm m hmodd (by omega)
        ((Dvd.intro ((m + 1) * (m + 2)) (by ring)).trans hdvd)
      have h4 : p ∣ m + 2 := hpm (m + 2) (hmodd.add_even even_two) (by omega)
        ((Dvd.intro ((m + 1) * m) (by ring)).trans hdvd)
      exact hp2' ((Nat.dvd_add_right h3).1 h4)
    | ⟨1, _⟩, hMD =>
      rw [h2] at hMD
      have hdvd := card_dvd_of_le hMD
      rw [card_rankOneGroupTwo ha hK, hm, Nat.add_sub_cancel,
        show (m + 1) ^ 2 + 1 = m * (m + 2) + 2 by ring] at hdvd
      have h3 : p ∣ m := hpm m hmodd (by omega)
        ((Dvd.intro ((m + 1) ^ 2 * (m * (m + 2) + 2)) (by ring)).trans hdvd)
      have hodd : Odd (m * (m + 2) + 2) := by
        obtain ⟨r, hr⟩ := hmodd
        exact ⟨2 * r ^ 2 + 4 * r + 2, by subst hr; ring⟩
      have h4 : p ∣ m * (m + 2) + 2 := hpm _ hodd (by omega)
        ((Dvd.intro ((m + 1) ^ 2 * m) (by ring)).trans hdvd)
      exact hpm1 h3 h4
  rw [hJ, reeParabolic_empty] at hle
  exact hle

end CFSG.Quasithin.SteinbergBT
