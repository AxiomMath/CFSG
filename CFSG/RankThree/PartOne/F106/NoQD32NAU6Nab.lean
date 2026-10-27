module

public import CFSG.RankThree.PartOne.F106.NoQD32NAU6Count
public import CFSG.RankThree.PartOne.F106.NoQD32NAU6Out
public import Certificates.Certificate271034

public section

namespace CFSG.RankThree.PartOne.F106

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

open scoped _root_.Classical in
theorem u6_nonabelian_false
    {X : Type} [Group X] [Finite X] (hmod : StatedClassicalModel X .PSU 6 2 1)
    (α : MulAut X) (hα : α ^ 5 = 1) {Y R : Subgroup X}
    (hexp : ∀ y ∈ Y, y ^ 3 = 1) (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (hRN : R ≤ Subgroup.normalizer (Y : Set X)) (hαY : ∀ y ∈ Y, α y ∈ Y)
    (hαR : ∀ r ∈ R, α r ∈ R) (hαnt : ∃ r ∈ R, α r * r⁻¹ ∉ Subgroup.centralizer (Y : Set X))
    (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : X) ∈ Subgroup.centralizer (Y : Set X))
    (hB : ∀ r ∈ R, (∀ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Y : Set X)) →
      r ∈ Subgroup.centralizer (Y : Set X)) : False := by
  have hmod0 := hmod
  have hord : Nat.card X = CFSG.Open.ordTwistedA (6 - 1) (2 ^ 1) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl
  obtain ⟨-, K, _, hfin, hK, ⟨e⟩⟩ := hmod
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  obtain ⟨ω⟩ := exists_cube (K := K) (by rw [hK]; norm_num)
  have hf : u6ThreeCert.Facts :=
    U6SylowCert.facts_of_check _ (Certificates.certificate271061 : U6ThreeRankCheck)
  have hna : u6ThreeCert.NAFacts :=
    U6SylowCert.NAFacts.of_naCheck _ (Certificates.certificate271034 : U6NACheck)
  have hG : Nat.card (StatedProj (StatedSU 6 (2 ^ 1) K)) = 9196830720 := by
    rw [← Nat.card_congr e.toEquiv, hord]
    unfold CFSG.Open.ordTwistedA
    decide +kernel
  have : Finite (StatedProj (StatedSU 6 (2 ^ 1) K)) :=
    Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  let T0 : U6Tab ω hK u6ThreeCert := U6Tab.ofFacts hf
  have hB' : ∀ r : ↥R, (∀ y ∈ Y, (r : X) * y * (r : X)⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Y : Set X)) →
      (r : X) ∈ Subgroup.centralizer (Y : Set X) := fun r hr => hB r r.2 hr
  have hV : 3 ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y) :=
    card_quotient_pow_four Nat.prime_three (by norm_num) hexp hcl hRN ψ hψs hψc hB'
  have hYp : IsPGroup 3 ↥Y := fun y => ⟨1, Subtype.ext (by simpa using hexp y y.2)⟩
  have hYZ : Nat.card ↥Y = Nat.card (↥Y ⧸ Subgroup.center ↥Y) * Nat.card (Subgroup.center ↥Y) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hZpos : 0 < Nat.card (Subgroup.center ↥Y) := Nat.card_pos
  have hYnt : Nontrivial ↥Y := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hYZ]
    calc 1 < 3 ^ 4 * 1 := by norm_num
      _ ≤ _ := Nat.mul_le_mul hV hZpos
  have hZ2 : 2 ≤ Nat.card (Subgroup.center ↥Y) := by
    have := Finite.one_lt_card_iff_nontrivial.mpr (hYp.center_nontrivial)
    omega
  have hY3 : IsPGroup 3 (Y.map e.toMonoidHom) := fun y => by
    obtain ⟨a, ha, hay⟩ := y.2
    have h3 : (y : StatedProj (StatedSU 6 (2 ^ 1) K)) ^ 3 = 1 := by
      rw [← hay, ← map_pow, hexp a ha, map_one]
    exact ⟨1, Subtype.ext h3⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_le_of_sylow (p := 3) (k := 6) T0.S T0.card
    (by rw [hG]; norm_num) _ hY3
  have hYcard : Nat.card ↥((Y.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom) =
      Nat.card ↥Y := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective e.injective]
  have hdvd : Nat.card ↥Y ∣ 3 ^ 6 := by
    rw [← hYcard, ← T0.card]
    exact Subgroup.card_dvd_of_le hg
  have h243 : 243 ≤ Nat.card ↥Y := by
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have h162 : 2 * 81 ≤ Nat.card ↥Y := by
      rw [hYZ]
      calc 2 * 81 = 3 ^ 4 * 2 := by norm_num
        _ ≤ _ := Nat.mul_le_mul hV hZ2
    rw [hjeq] at h162 ⊢
    interval_cases j <;> omega
  have hexp1 : ∀ y ∈ (Y.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom, y ^ 3 = 1 :=
    map_pow_of_pow _ _ 3 (map_pow_of_pow e.toMonoidHom Y 3 hexp)
  have hY1 : (Y.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = u6Y0 ω hK u6ThreeCert :=
    T0.eq_Y0_of_exp_three hna hg hexp1 (by rw [hYcard]; exact h243)
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_conj e g Y (u6Y0 ω hK u6ThreeCert) hY1
  have hY243 : Nat.card ↥Y = 243 := by
    rw [Nat.card_congr φ.toEquiv]
    exact T0.card_Y0 hna
  have hZ3 : Nat.card (Subgroup.center ↥Y) = 3 ∧
      Nat.card (↥Y ⧸ Subgroup.center ↥Y) = 3 ^ 4 := by
    rw [hY243] at hYZ
    generalize Nat.card (↥Y ⧸ Subgroup.center ↥Y) = a at hV hYZ ⊢
    generalize Nat.card (Subgroup.center ↥Y) = b at hZ2 hYZ ⊢
    have hb : b ≤ 3 := by nlinarith
    interval_cases b <;> omega
  have hZ0 : Nat.card (Subgroup.center ↥(u6Y0 ω hK u6ThreeCert)) = 3 := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ,
      Subgroup.card_map_of_injective φ.injective]
    exact hZ3.1
  let trz : X → Prop := fun x => trZeroP (StatedSU 6 (2 ^ 1) K) (e x)
  have hconj : ∀ n x : X, trz (n * x * n⁻¹) ↔ trz x := by
    intro n x
    simp only [trz, map_mul, map_inv]
    exact trZeroP_conj _ (e n) (e x)
  have h1tr : trz 1 := by
    have h := (sel_trZero_iff (ω := ω) (hK := hK) (c := u6ThreeCert) 0).mpr
      (by rw [T0.tab_zero]; exact hna.oneTr)
    simpa [trz, T0.sel_zero] using h
  have hQcard : Nat.card (Qset Y trz) = 48 := by
    have h := card_Qset_congr (Y := Y) (Y' := u6Y0 ω hK u6ThreeCert) (pr := trz)
      (pr' := trZeroP (StatedSU 6 (2 ^ 1) K)) φ (fun y => by
        rw [hφ y]
        exact (trZeroP_conj _ g (e y)).symm)
    rw [h]
    exact T0.card_Qset_Y0 hna hZ0
  have hAcard : Nat.card (Aset Y trz) = 16 := by
    have := card_Qset (Y := Y) (pr := trz)
    rw [hQcard, hZ3.1] at this
    omega
  obtain ⟨a, ha⟩ := exists_conj_of_pow_five_psu6 hmod0 α hα
  have hαa : ∀ x, α x = a * x * a⁻¹ := fun x => by rw [ha]; rfl
  have hnormY : a ∈ Subgroup.normalizer (Y : Set X) := by
    have hmapY : Y.map (MulAut.conj a).toMonoidHom = Y := by
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨y, hy, rfl⟩
        have := hαY y hy
        rw [hαa] at this
        exact this
      · rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapY
  have hnR : ∀ r ∈ R, a * r * a⁻¹ ∈ R := fun r hr => by
    rw [← hαa]
    exact hαR r hr
  have hnt : ∃ r ∈ R, a * r * a⁻¹ * r⁻¹ ∉ Subgroup.centralizer (Y : Set X) := by
    obtain ⟨r, hr, hnc⟩ := hαnt
    exact ⟨r, hr, by rwa [hαa] at hnc⟩
  have hτ1 : actN Y ⟨a, hnormY⟩ ≠ 1 := actN_ne_one hRN ⟨a, hnormY⟩ hnR hB' hnt
  have hτ5 : (actN Y ⟨a, hnormY⟩) ^ 5 = 1 :=
    actN_pow_eq_one a hnormY (by rw [← ha]; exact hα)
  have : Fintype (↥Y ⧸ Subgroup.center ↥Y) := Fintype.ofFinite _
  let A : Finset (↥Y ⧸ Subgroup.center ↥Y) := Finset.univ.filter fun v => v ∈ Aset Y trz
  have hAc : A.card = 16 := by
    have h1 : A.card = Nat.card {v : ↥Y ⧸ Subgroup.center ↥Y // v ∈ Aset Y trz} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1]
    exact hAcard
  have h5 := five_dvd_card_of_invariant hZ3.2 (actN Y ⟨a, hnormY⟩) hτ5 hτ1 A
    (by simpa [A] using one_not_mem_Aset (Y := Y) h1tr)
    (fun v hv => by
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact actN_mem_Aset (pr := trz) a hnormY (hconj a) hv)
  rw [hAc] at h5
  omega

end CFSG.RankThree.PartOne.F106
