module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.RankThree.PartOne.S12K.OrdRigid
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

@[expose] def idxU (n g k : ℕ) : Prop :=
  ∃ i ∈ Finset.Icc 2 (n + 1), (Even i ∧ k ∣ g * i) ∨ (Odd i ∧ k ∣ 2 * (g * i) ∧ ¬ k ∣ g * i)

theorem profile_idxU {n g : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g) :
    Profile (ordTwistedA n (2 ^ g)) (g * (n * (n + 1) / 2)) (idxU n g) := by
  set F : ℕ → ℕ := fun i => (((2 ^ g : ℕ) : ℤ) ^ i - (-1) ^ i).toNat
  have hq : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have hFe : ∀ i, Even i → F i = (2 ^ g) ^ i - 1 := fun i hi =>
    toNat_pow_sub_neg_one_pow_of_even hq hi
  have hFo : ∀ i, Odd i → F i = (2 ^ g) ^ i + 1 := fun i hi =>
    toNat_pow_sub_neg_one_pow_of_odd hi
  have hP : Odd (∏ i ∈ Finset.Icc 2 (n + 1), F i) := odd_prod fun i hi => by
    have hi0 : 0 < i := by simp at hi; omega
    rcases Nat.even_or_odd i with h | h
    · rw [hFe i h]; exact odd_pow_sub_one hg hi0
    · rw [hFo i h]; exact odd_pow_add_one hg hi0
  have hm : ordTwistedA n (2 ^ g) = 2 ^ (g * (n * (n + 1) / 2)) *
      (∏ i ∈ Finset.Icc 2 (n + 1), F i) / Nat.gcd (n + 1) (2 ^ g + 1) := by
    rw [ordTwistedA, pow_mul]
  have hsq : (2 ^ g + 1) * (2 ^ g + 1) ∣ ∏ i ∈ Finset.Icc 2 (n + 1), F i := by
    have h23 : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 (n + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]; omega
    have := Finset.prod_dvd_prod_of_subset _ _ F h23
    rw [Finset.prod_pair (by norm_num), hFe 2 even_two, hFo 3 (by decide)] at this
    exact (mul_dvd_mul (add_one_dvd_sq_sub_one _) (add_one_dvd_pow_add_one _ (by decide))).trans
      this
  refine Profile.of_div hm hP (Nat.gcd_dvd_right _ _) hsq (Nat.gcd_pos_of_pos_left _ (by omega))
    (fun p k hp hk => ?_)
  rw [(Nat.Prime.prime hp.prime).dvd_finsetProd_iff]
  refine exists_congr fun i => and_congr_right fun _ => ?_
  rcases Nat.even_or_odd i with h | h
  · rw [hFe i h, PrimDiv.dvd_pow_sub_one_iff hp hk]
    exact ⟨fun h' => Or.inl ⟨h, h'⟩, fun h' => h'.elim (fun h'' => h''.2)
      (fun h'' => absurd h (Nat.not_even_iff_odd.mpr h''.1))⟩
  · rw [hFo i h, PrimDiv.dvd_pow_add_one_iff hp hk]
    exact ⟨fun h' => Or.inr ⟨h, h'⟩, fun h' => h'.elim
      (fun h'' => absurd h''.1 (Nat.not_even_iff_odd.mpr h)) (fun h'' => h''.2)⟩

theorem ordTwistedA_two_mul_ne {s f g : ℕ} (hs : 2 ≤ s) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordTwistedA (2 * s) (2 ^ f) ≠ ordTwistedA (2 * s - 1) (2 ^ g) := by
  intro hm
  have hX := profile_idxU (n := 2 * s) (by omega) hf
  have hY := profile_idxU (n := 2 * s - 1) (by omega) hg
  rw [← hm] at hY
  obtain ⟨hN, hZ⟩ := hX.transfer hY
  have e1 : 2 * s * (2 * s + 1) / 2 = s * (2 * s + 1) := tri_even s
  have e2 : (2 * s - 1) * (2 * s - 1 + 1) / 2 = s * (2 * s - 1) := by
    rw [show 2 * s - 1 + 1 = 2 * s by omega, mul_comm, mul_assoc, Nat.mul_div_cancel_left _ two_pos,
      mul_comm]
  rw [e1, e2] at hN
  have hrel : f * (2 * s + 1) = g * (2 * s - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < s by omega)
    calc s * (f * (2 * s + 1)) = f * (s * (2 * s + 1)) := by ring
      _ = g * (s * (2 * s - 1)) := hN
      _ = s * (g * (2 * s - 1)) := by ring
  have hodd : Odd (2 * s - 1) := ⟨s - 1, by omega⟩
  have hcop : Nat.Coprime (2 * s - 1) (2 * s + 1) := by
    rw [show 2 * s + 1 = 2 + (2 * s - 1) by omega, Nat.coprime_add_self_right]
    exact Nat.coprime_two_right.mpr hodd
  obtain ⟨c, hc⟩ : (2 * s - 1) ∣ f :=
    hcop.dvd_of_dvd_mul_right ⟨g, by rw [hrel, mul_comm]⟩
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, mul_zero] at hc; omega
    · exact h0
  have hgc : g = (2 * s + 1) * c := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 * s - 1 by omega)
    rw [← hrel, hc]
    ring
  have hk2 : 2 ≤ f * (2 * s) := by nlinarith
  have hk6 : f * (2 * s) ≠ 6 := by
    intro h6
    have h3 : 3 ≤ 2 * s - 1 := by omega
    have : 3 * 1 * (2 * s) ≤ (2 * s - 1) * c * (2 * s) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul h3 hc0)
    rw [← hc] at this
    omega
  have hkX : idxU (2 * s) f (f * (2 * s)) :=
    ⟨2 * s, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Or.inl ⟨even_two_mul s, dvd_rfl⟩⟩
  obtain ⟨i, hi, hcase⟩ := (hZ _ hk2 hk6).mp hkX
  obtain ⟨hi2, hi'⟩ := Finset.mem_Icc.mp hi
  have hi2s : i ≤ 2 * s := by omega
  have hcop' : Nat.Coprime (2 * s * (2 * s - 1)) (2 * s + 1) :=
    Nat.Coprime.mul_left (by
      rw [show 2 * s + 1 = 1 + 2 * s by omega, Nat.coprime_add_self_right]
      exact Nat.coprime_one_right _) hcop
  rcases hcase with ⟨-, hd⟩ | ⟨-, hd, -⟩
  ·
    rw [hc, hgc] at hd
    have hd' : 2 * s * (2 * s - 1) ∣ (2 * s + 1) * i := by
      have : 2 * s * (2 * s - 1) * c ∣ (2 * s + 1) * i * c := by
        rw [show 2 * s * (2 * s - 1) * c = (2 * s - 1) * c * (2 * s) by ring,
          show (2 * s + 1) * i * c = (2 * s + 1) * c * i by ring]
        exact hd
      exact Nat.dvd_of_mul_dvd_mul_right hc0 this
    have hdi := hcop'.dvd_of_dvd_mul_left hd'
    have hle := Nat.le_of_dvd (by omega) hdi
    have : 2 * s * 3 ≤ 2 * s * (2 * s - 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  ·
    rw [hc, hgc] at hd
    have hd' : s * (2 * s - 1) ∣ (2 * s + 1) * i := by
      have : s * (2 * s - 1) * (2 * c) ∣ (2 * s + 1) * i * (2 * c) := by
        rw [show s * (2 * s - 1) * (2 * c) = (2 * s - 1) * c * (2 * s) by ring,
          show (2 * s + 1) * i * (2 * c) = 2 * ((2 * s + 1) * c * i) by ring]
        exact hd
      exact Nat.dvd_of_mul_dvd_mul_right (by omega) this
    have hcop'' : Nat.Coprime (s * (2 * s - 1)) (2 * s + 1) :=
      Nat.Coprime.coprime_dvd_left ⟨2, by ring⟩ hcop'
    have hdi := hcop''.dvd_of_dvd_mul_left hd'
    have hle := Nat.le_of_dvd (by omega) hdi
    have : s * 3 ≤ s * (2 * s - 1) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem idxU_top {n g t : ℕ} (hn : n = 2 * t ∨ n = 2 * t + 1) (ht : 1 ≤ t) (hg : 0 < g) :
    idxU n g (2 * (g * (2 * t + 1))) := by
  refine ⟨2 * t + 1, ?_, Or.inr ⟨odd_two_mul_add_one t, dvd_rfl, fun h => ?_⟩⟩
  · simp only [Finset.mem_Icc]; omega
  · have h0 : 0 < g * (2 * t + 1) := by positivity
    have := Nat.le_of_dvd h0 h
    omega

theorem idxU_le {n g t k : ℕ} (hn : n = 2 * t ∨ n = 2 * t + 1) (hg : 0 < g)
    (hk : idxU n g k) : k ≤ 2 * (g * (2 * t + 1)) := by
  obtain ⟨i, hi, ⟨-, hd⟩ | ⟨ho, hd, -⟩⟩ := hk
  · simp only [Finset.mem_Icc] at hi
    calc k ≤ g * i := Nat.le_of_dvd (Nat.mul_pos hg (by omega)) hd
      _ ≤ g * (2 * (2 * t + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (g * (2 * t + 1)) := by ring
  · simp only [Finset.mem_Icc] at hi
    obtain ⟨j, rfl⟩ := ho
    calc k ≤ 2 * (g * (2 * j + 1)) := Nat.le_of_dvd (by positivity) hd
      _ ≤ 2 * (g * (2 * t + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))

theorem eq_of_ordTwistedA_three_two_eq {u g : ℕ} (hu : 2 ≤ u) (hg : 1 ≤ g)
    (hug : (u, g) ≠ (2, 1)) (h : ordTwistedA 3 (2 ^ 1) = ordTwistedA u (2 ^ g)) :
    u = 3 ∧ g = 1 := by
  have hX := profile_idxU (n := 3) (by norm_num) (by norm_num : 1 ≤ 1)
  have hY := profile_idxU hu hg
  rw [← h] at hY
  have hN := (hX.transfer hY).1
  norm_num at hN
  have hu3 : u ≤ 3 := by
    by_contra hu4
    have h1 : 4 * 5 ≤ u * (u + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : u * (u + 1) / 2 ≤ g * (u * (u + 1) / 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  interval_cases u
  · have hg2 : g = 2 := by norm_num at hN; omega
    subst hg2
    exact absurd h (by decide)
  · exact ⟨rfl, by norm_num at hN; omega⟩

theorem ordTwistedA_inj_two_pow {n u f g : ℕ} (hn : 2 ≤ n) (hu : 2 ≤ u) (hf : 1 ≤ f)
    (hg : 1 ≤ g) (hnf : (n, f) ≠ (2, 1)) (hug : (u, g) ≠ (2, 1))
    (h : ordTwistedA n (2 ^ f) = ordTwistedA u (2 ^ g)) : n = u ∧ f = g := by
  obtain ⟨t, ht1, ht⟩ := exists_half hn
  obtain ⟨s, hs1, hs⟩ := exists_half hu
  by_cases hsmX : f = 1 ∧ t = 1
  · obtain ⟨rfl, rfl⟩ := hsmX
    rcases ht with rfl | rfl
    · exact absurd rfl hnf
    · obtain ⟨rfl, rfl⟩ := eq_of_ordTwistedA_three_two_eq hu hg hug h
      exact ⟨rfl, rfl⟩
  by_cases hsmY : g = 1 ∧ s = 1
  · obtain ⟨rfl, rfl⟩ := hsmY
    rcases hs with rfl | rfl
    · exact absurd rfl hug
    · obtain ⟨rfl, rfl⟩ := eq_of_ordTwistedA_three_two_eq hn hf hnf h.symm
      exact ⟨rfl, rfl⟩
  have hX := profile_idxU hn hf
  have hY := profile_idxU hu hg
  rw [← h] at hY
  obtain ⟨hN, hZ⟩ := hX.transfer hY
  have h6X := two_mul_ne_six hf ht1 hsmX
  have h6Y := two_mul_ne_six hg hs1 hsmY
  have hfX : 1 ≤ f * (2 * t + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hgY : 1 ≤ g * (2 * s + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h1 := idxU_le hs (by omega) ((hZ _ (by omega) h6X).mp (idxU_top ht ht1 (by omega)))
  have h2 := idxU_le ht (by omega) ((hZ _ (by omega) h6Y).mpr (idxU_top hs hs1 (by omega)))
  have hW : f * (2 * t + 1) = g * (2 * s + 1) := by omega
  have hW0 : 0 < f * (2 * t + 1) := by positivity
  rcases ht with rfl | rfl <;> rcases hs with rfl | rfl
  · rw [tri_even, tri_even] at hN
    have hts : t = s := by
      apply Nat.eq_of_mul_eq_mul_right hW0
      calc t * (f * (2 * t + 1)) = f * (t * (2 * t + 1)) := by ring
        _ = g * (s * (2 * s + 1)) := hN
        _ = s * (g * (2 * s + 1)) := by ring
        _ = s * (f * (2 * t + 1)) := by rw [hW]
    subst hts
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * t + 1) hW⟩
  · rw [tri_even, tri_odd] at hN
    have hts : t = s + 1 := by
      apply Nat.eq_of_mul_eq_mul_right hW0
      calc t * (f * (2 * t + 1)) = f * (t * (2 * t + 1)) := by ring
        _ = g * ((2 * s + 1) * (s + 1)) := hN
        _ = (s + 1) * (g * (2 * s + 1)) := by ring
        _ = (s + 1) * (f * (2 * t + 1)) := by rw [hW]
    subst hts
    rw [show 2 * s + 1 = 2 * (s + 1) - 1 by omega] at h
    exact absurd h (ordTwistedA_two_mul_ne (s := s + 1) (by omega) hf hg)
  · rw [tri_odd, tri_even] at hN
    have hts : s = t + 1 := by
      apply Nat.eq_of_mul_eq_mul_right hW0
      calc s * (f * (2 * t + 1)) = s * (g * (2 * s + 1)) := by rw [hW]
        _ = g * (s * (2 * s + 1)) := by ring
        _ = f * ((2 * t + 1) * (t + 1)) := hN.symm
        _ = (t + 1) * (f * (2 * t + 1)) := by ring
    subst hts
    rw [show 2 * t + 1 = 2 * (t + 1) - 1 by omega] at h
    exact absurd h.symm (ordTwistedA_two_mul_ne (s := t + 1) (by omega) hg hf)
  · rw [tri_odd, tri_odd] at hN
    have hts : t = s := by
      apply Nat.eq_of_mul_eq_mul_right hW0
      apply Nat.add_right_cancel (m := f * (2 * t + 1))
      calc t * (f * (2 * t + 1)) + f * (2 * t + 1) = f * ((2 * t + 1) * (t + 1)) := by ring
        _ = g * ((2 * s + 1) * (s + 1)) := hN
        _ = s * (g * (2 * s + 1)) + g * (2 * s + 1) := by ring
        _ = s * (f * (2 * t + 1)) + f * (2 * t + 1) := by rw [hW]
    subst hts
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * t + 1) hW⟩

@[expose] def SUmEvenTypeDetAt (m : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ) (t : StatedLieTag) (n f' : ℕ),
    LieModel X .PSU m 2 f → StatedLieAdmissible t n 2 f' → LieModel X t n 2 f' →
      t = .PSU ∧ n = m ∧ f' = f

theorem evenLieOrder_eq_ordTwistedA {t : StatedLieTag} {n g m f : ℕ}
    (hadm : StatedLieAdmissible t n 2 g) (hm : 4 ≤ m) (hf : 1 ≤ f)
    (h : F4Pilot.evenLieOrder t n g = ordTwistedA (m - 1) (2 ^ f)) :
    t = .PSU ∧ n = m ∧ g = f := by
  have hG2 : t = .G2 → 2 ≤ g := fun ht => F4Pilot.two_le_of_admissible_G2 (ht ▸ hadm)
  obtain ⟨-, hg, ht⟩ := hadm
  have hu : 2 ≤ m - 1 := by omega
  cases t
  case PSL => exact absurd h (ordA_ne_ordTwistedA (by obtain ⟨hn, -⟩ := ht; omega) hg hu hf)
  case PSU =>
    obtain ⟨hn, hn32⟩ := ht
    have hng : (n - 1, g) ≠ (2, 1) := fun h21 => by
      obtain ⟨h1, h2⟩ := Prod.mk.inj h21
      subst h2
      exact hn32 (Prod.ext (by simp only; omega) (by norm_num))
    have hmf : (m - 1, f) ≠ (2, 1) := fun h21 => by
      have := (Prod.mk.inj h21).1
      omega
    obtain ⟨h1, h2⟩ := ordTwistedA_inj_two_pow (n := n - 1) (by omega) hu hg hf hng hmf h
    exact ⟨rfl, by omega, h2⟩
  case PSp =>
    obtain ⟨hn, -⟩ := ht
    rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
    · exact absurd h.symm (RankThree.PartOne.S12K.ordTwistedA_ne_ordBC_two hu hf hg)
    · exact absurd h (ordBC_ne_ordTwistedA hn3 hg hu hf)
  case POmegaOdd => exact absurd rfl ht.2
  case POmegaPlus => exact absurd h (ordD_ne_ordTwistedA ht hg hu hf)
  case POmegaMinus => exact absurd h (ordTwistedD_ne_ordTwistedA ht hg hu hf)
  case G2 => exact absurd h (ordG2_ne_ordTwistedA (hG2 rfl) hu hf)
  case F4 => exact absurd h (ordF4_ne_ordTwistedA hg hu hf)
  case E6 => exact absurd h (ordE6_ne_ordTwistedA hg hu hf)
  case E7 => exact absurd h (ordE7_ne_ordTwistedA hg hu hf)
  case E8 => exact absurd h (ordE8_ne_ordTwistedA hg hu hf)
  case twistedE6 => exact absurd h (ordTwistedE6_ne_ordTwistedA hg hu hf)
  case trialityD4 => exact absurd h (ordTrialityD4_ne_ordTwistedA hg hu hf)
  case twistedB2 => exact absurd h (ordSuzuki_ne_ordTwistedA ht.2.2.1 ht.2.2.2 hu hf)
  case twistedG2 => exact absurd ht.2.1 (by norm_num)
  case twistedF4 => exact absurd h (ordTwistedF4_ne_ordTwistedA hg hu hf)
  case Tits => exact absurd h (ordTits_ne_ordTwistedA hu hf)

section Orders


theorem lieModel_PSU_two_unique_of_card_eq {X Y : Type} [Group X] [Group Y] {m f : ℕ}
    (hm : 4 ≤ m) (hX : LieModel X .PSU m 2 f) {t : StatedLieTag} {n f' : ℕ}
    (h : LieModel Y t n 2 f') (hcard : Nat.card Y = Nat.card X) : t = .PSU ∧ n = m ∧ f' = f := by
  refine evenLieOrder_eq_ordTwistedA (F4Pilot.statedLieAdmissible_of_lieModel h) hm
    (F4Pilot.statedLieAdmissible_of_lieModel hX).2.1 ?_
  rw [← F4Pilot.card_eq_evenLieOrder h, hcard,
    F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hX]
  rfl

theorem sumEvenTypeDetAt {m : ℕ} (hm : 4 ≤ m) : SUmEvenTypeDetAt m :=
  fun _ _ _ _ _ _ hX _ h => lieModel_PSU_two_unique_of_card_eq hm hX h rfl

end Orders

end CFSG.SeitzReduction.UnitaryPilot
