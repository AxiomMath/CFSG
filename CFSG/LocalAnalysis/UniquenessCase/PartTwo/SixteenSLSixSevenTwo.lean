module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLSixSevenComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLSixSevenFixers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoCommon
public import CFSG.Quasithin.Vol2.Ch10SecQ9H46

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16nt_prime_sq_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ^ 2 ∣ 2 ^ 17 * (3 ^ 5 * (5 * (7 ^ 2 * 31)))) : p = 3 ∨ p = 7 := by
  have hpd : p ∣ 2 ^ 17 * (3 ^ 5 * (5 * (7 ^ 2 * 31))) :=
    (dvd_pow_self p (by norm_num)).trans hd
  rcases hp.dvd_mul.mp hpd with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  rcases hp.dvd_mul.mp h with h | h
  · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
  rcases hp.dvd_mul.mp h with h | h
  · exfalso
    have h5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    subst h5
    norm_num at hd
  rcases hp.dvd_mul.mp h with h | h
  · right; exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow h)
  · exfalso
    have h31 : p = 31 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    subst h31
    norm_num at hd

private theorem s16nt_prime_sq_seven {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ^ 2 ∣ 2 ^ 23 * (3 ^ 5 * (5 * (7 ^ 2 * (31 * 127))))) : p = 3 ∨ p = 7 := by
  have hpd : p ∣ 2 ^ 23 * (3 ^ 5 * (5 * (7 ^ 2 * (31 * 127)))) :=
    (dvd_pow_self p (by norm_num)).trans hd
  rcases hp.dvd_mul.mp hpd with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
  rcases hp.dvd_mul.mp h with h | h
  · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
  rcases hp.dvd_mul.mp h with h | h
  · exfalso
    have h5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    subst h5
    norm_num at hd
  rcases hp.dvd_mul.mp h with h | h
  · right; exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow h)
  rcases hp.dvd_mul.mp h with h | h
  · exfalso
    have h31 : p = 31 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    subst h31
    norm_num at hd
  · exfalso
    have h127 : p = 127 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    subst h127
    norm_num at hd

private theorem s16nt_star_sum {n : ℕ}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2 := by
  have hs' : S16kStar D V₀ V L hV := c.toS16kStar hs
  exact hs'.sumOfNat_map (N := fun H U Z => BinaryNaturalSL H U Z n 1)
    (N' := fun H U Z => BinaryNaturalSL H U Z n 1) (k := 2)
    (fun ρ θ hθ heq hker I hI hNI =>
      s16k_binaryNaturalSL_map hNI ρ hker θ hθ heq) hsum

private theorem s16nt_sl_two_fix_three (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    S168e3Fix (Mbar D.M V₀ V hV) 3 := by
  have hn6 : 6 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn3 : 3 ≤ n := by omega
  have hcomm : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) = ⊤ := by
    simpa only [wTil, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hS : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1)
      (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2 := by
    simpa only [wTil, lBar] using hsum
  obtain ⟨I₁, I₂, hZ₁, hZ₂, -, -, hsup, hN₁, hN₂⟩ :=
    s16k_sum_two_data_of_comm_top hcomm hS
  obtain ⟨K₁, hK₁f, hK₁fin, hK₁card, hR₁⟩ := hN₁
  obtain ⟨K₂, hK₂f, hK₂fin, hK₂card, hR₂⟩ := hN₂
  letI : Field K₁ := hK₁f
  letI : Finite K₁ := hK₁fin
  letI : Field K₂ := hK₂f
  letI : Finite K₂ := hK₂fin
  obtain ⟨π₁, h₁⟩ := hR₁
  obtain ⟨π₂, h₂⟩ := hR₂
  have hK₁ : Nat.card K₁ = 2 := by simpa using hK₁card
  have hK₂ : Nat.card K₂ = 2 := by simpa using hK₂card
  have hπ₁ : Function.Surjective π₁ := h₁.1
  have hπ₂ : Function.Surjective π₂ := h₂.1
  obtain ⟨hinj₁, -, hEq | hEq⟩ :=
    s16k_sl_two_equiv (n := n) hn3 hSL hK₁ hK₂ hπ₁ hπ₂
  · have hpair : S16kPairFix (FFModel.nat (StatedSL n K₁))
        (FFModel.nat (StatedSL n K₂)) π₁ π₂ 3 :=
      s16k_pairFix_of_equiv_nat hinj₁ hπ₂ hEq
        (fun a b hab => (s16k_sl_pair_fix hK₁ hn6 a b hab).1)
    have hne := s16k_nat_exists_ne_ker (⟨0, by omega⟩ : Fin n) (StatedSL n K₁)
    exact s16k_sum_two_transport_of_le (barSub_mono V₀ V hV c.setting.hyp151.le)
      hZ₁ hZ₂ hsup h₁ h₂ Nat.prime_three (by norm_num) hne hpair
  · have hpair : S16kPairFix (FFModel.nat (StatedSL n K₁))
        (FFModel.nat (StatedSL n K₂)) π₁ π₂ 3 :=
      s16k_pairFix_of_equiv_nat hinj₁ hπ₂ hEq
        (fun a b hab => (s16k_sl_pair_fix hK₁ hn6 a b hab).2)
    have hne := s16k_nat_exists_ne_ker (⟨0, by omega⟩ : Fin n) (StatedSL n K₁)
    exact s16k_sum_two_transport_of_le (barSub_mono V₀ V hV c.setting.hyp151.le)
      hZ₁ hZ₂ hsup h₁ h₂ Nat.prime_three (by norm_num) hne hpair

private theorem s16nt_sl_two_fix_seven (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2)
    (hdiv : 7 ∣ Nat.card ↥(lBar V₀ V hV L)) :
    ∀ x : Vtil V₀ V hV, x ≠ 1 →
      ∃ b ∈ Mbar D.M V₀ V hV, orderOf b = 7 ∧ b x = x := by
  have hsumStar := s16nt_star_sum c hs hsum
  have htop : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  have hsumTop : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
    simpa only [htop] using hsumStar
  have hfix : ∀ x : vStar D.M V₀ V hV L, x ≠ 1 →
      ∃ b ∈ lStar D.M V₀ V hV L, orderOf b = 7 ∧ b x = x :=
    s168e3_ln_fix_order_seven (H := lStar D.M V₀ V hV L) hn hsumTop
  exact s168e3_pointFix_of_star c hs Nat.prime_seven (by norm_num) hdiv hfix

theorem s16nt_sl_six_seven_two_false
    {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm3 : 3 ≤ m + 1 := by omega
  have hLm : IsLn ↥(lBar V₀ V hV L) (m + 1) 1 := s16k_isLn_of_isSLn hm3 hSL
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_sl_six_seven_component_at_three c hcomp hn hSL
  have hclass : StatedClassicalModel
      ↥(lBar V₀ V hV L) .PSL (m + 1) 2 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hLm (by decide)
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(lBar V₀ V hV L)) ∣ 2 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound
      ↥(lBar V₀ V hV L) (m + 1) 2 1 hclass).2.2.2.2 (by omega)
    simpa using h
  have haut : Nat.card (MulAut ↥(lBar V₀ V hV L)) ∣
      2 * Nat.card ↥(lBar V₀ V hV L) :=
    CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F.card_mulAut_dvd_of_outer hout
  have hsumStar := s16nt_star_sum c hs hsum
  have hF : s16e_two_Fam D V₀ V L hV
      (fun H U Z => BinaryNaturalSL H U Z (m + 1) 1) :=
    s16e_two_fam_ln D hV hm3 hLm hsumStar
  have hcardStar : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣
      6 * (2 * Nat.card ↥(lBar V₀ V hV L)) :=
    s16e_two_card_mbar D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting c.ne hs
      hF (a := 2 * Nat.card ↥(lBar V₀ V hV L)) haut
  have hcard12 : Nat.card ↥(Mbar D.M V₀ V hV) ∣
      12 * Nat.card ↥(lBar V₀ V hV L) := by
    rw [c23_card_mbar_v1Sub_eq D c.std.h1217 c.setting.hyp151 hV] at hcardStar
    rwa [show 6 * (2 * Nat.card ↥(lBar V₀ V hV L)) =
      12 * Nat.card ↥(lBar V₀ V hV L) by ring] at hcardStar
  have hHcard : Nat.card ↥(lBar V₀ V hV L) = 20158709760 ∨
      Nat.card ↥(lBar V₀ V hV L) = 163849992929280 := by
    have hn' := hn
    rcases hn' with h6 | h7
    · left
      have hc6 : StatedClassicalModel
          ↥(lBar V₀ V hV L) .PSL 6 2 1 := h6 ▸ hclass
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hc6]
      decide
    · right
      have hc7 : StatedClassicalModel
          ↥(lBar V₀ V hV L) .PSL 7 2 1 := h7 ▸ hclass
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hc7]
      decide
  have hsig : D.sig ⊆ ({3, 7} : Set ℕ) := by
    intro p hp
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    have hpM : p ^ 2 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
      have h := s168e3_two_pow_dvd_card c hp
      rwa [c23_card_mbar_v1Sub_eq D c.std.h1217 c.setting.hyp151 hV] at h
    have hp12 : p ^ 2 ∣ 12 * Nat.card ↥(lBar V₀ V hV L) := hpM.trans hcard12
    have hHc := hHcard
    rcases hHc with hc | hc
    · rw [hc] at hp12
      rw [show 12 * 20158709760 = 2 ^ 17 * (3 ^ 5 * (5 * (7 ^ 2 * 31))) by norm_num] at hp12
      have := s16nt_prime_sq_six hpp hp2 hp12
      rcases this with h3 | h7
      · rw [h3]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
      · rw [h7]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
    · rw [hc] at hp12
      rw [show 12 * 163849992929280 =
        2 ^ 23 * (3 ^ 5 * (5 * (7 ^ 2 * (31 * 127)))) by norm_num] at hp12
      have := s16nt_prime_sq_seven hpp hp2 hp12
      rcases this with h3 | h7
      · rw [h3]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
      · rw [h7]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hcube : ¬ 7 ^ 3 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    intro h
    have h' : 7 ^ 3 ∣ 12 * Nat.card ↥(lBar V₀ V hV L) := h.trans hcard12
    have hHc := hHcard
    rcases hHc with hc | hc
    · rw [hc] at h'
      norm_num at h'
    · rw [hc] at h'
      norm_num at h'
  have hdiv7 : 7 ∣ Nat.card ↥(lBar V₀ V hV L) := by
    have hHc := hHcard
    rcases hHc with hc | hc <;> rw [hc] <;> norm_num
  obtain ⟨p, hp⟩ := c.std.hx.sig_nonempty
  have hp37 : p = 3 ∨ p = 7 := hsig hp
  rcases hp37 with rfl | rfl
  · exact s168e3_false_of_fix c Nat.prime_three hp
      (s16nt_sl_two_fix_three c hs hn hSL hsum)
  · exact s168e3_false_of_kernel c Nat.prime_seven hp
      (s168e3_kernel_of_cube Nat.prime_seven (Mbar D.M V₀ V hV) hcube
        (s16nt_sl_two_fix_seven c hs hn hSL hsum hdiv7))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
