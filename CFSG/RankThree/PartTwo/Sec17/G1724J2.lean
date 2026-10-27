module

public import CFSG.RankThree.PartTwo.KFacts.KS14MultJ2
public import CFSG.RankThree.OddKernel.ComponentRanks

public section

namespace CFSG.RankThree.PartTwo.Sec17.G1724

open CFSG CFSG.Blueprint
open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu
open CFSG.RankThree.PartTwo.KFacts.KS14
open scoped Pointwise
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ okA keyPts eltOf rep_eltOf eq_of_rep rep_mul
  rep_pow rep_conj commute_of_commA subOf gElt subOf_eq_closure_gElt card_subOf okA_spec card_GJ
  rep_one)

theorem pow_eq_one_of_mem_zpowers {H : Type*} [Group H] {g a : H} {n : ℕ} (hg : g ^ n = 1)
    (ha : a ∈ Subgroup.zpowers g) : a ^ n = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

section Witness

noncomputable def xE : GJ := eltOf j2x5Arr chkMult5_parts.1

noncomputable def yE : GJ := eltOf j2y5Arr chkMult5_parts.2.1

noncomputable def gE : GJ := eltOf j2g5Arr chkMult5_parts.2.2.1

theorem xE_pow_five : xE ^ 5 = 1 :=
  eq_of_rep (rep_pow (rep_eltOf _) 5) rep_one chkMult5_parts.2.2.2.1

theorem xE_mul_comm : xE * yE = yE * xE :=
  (commute_of_commA (rep_eltOf _) (rep_eltOf _) chkMult5_parts.2.2.2.2.1).eq

theorem gE_conj_x : gE * xE * gE⁻¹ = xE ^ 4 :=
  eq_of_rep (rep_conj (rep_eltOf _) (okA_spec chkMult5_parts.2.2.1).1 (rep_eltOf _))
    (rep_pow (rep_eltOf _) 4) chkMult5_parts.2.2.2.2.2.1

theorem gE_conj_y : gE * yE * gE⁻¹ = xE ^ 3 * yE :=
  eq_of_rep (rep_conj (rep_eltOf _) (okA_spec chkMult5_parts.2.2.1).1 (rep_eltOf _))
    (rep_mul (rep_pow (rep_eltOf _) 3) (rep_eltOf _)) chkMult5_parts.2.2.2.2.2.2.1

theorem xE_ne_one : xE ≠ 1 := by
  intro h
  have h0 := rep_eltOf (t := j2x5Arr) chkMult5_parts.1 0
  have h1 : eltOf j2x5Arr chkMult5_parts.1 = 1 := h
  rw [h1] at h0
  have h2 : j2x5Arr[((0 : Fin 315) : ℕ)]! = 54 := by decide +kernel
  rw [h2] at h0
  simp at h0

theorem card_closure_xy : Nat.card (Subgroup.closure ({xE, yE} : Set GJ)) = 25 := by
  have hgs : ∀ k < gensE25.size, validA 315 gensE25[k]! = true ∧ inP gensE25[k]! = true := by
    intro k hk
    have hk2 : k < 2 := hk
    interval_cases k
    · exact okA_spec chkMult5_parts.1
    · exact okA_spec chkMult5_parts.2.1
  have hcard := card_subOf (by decide) chkMult5_parts.2.2.2.2.2.2.2.1 hgs
  rw [chkMult5_parts.2.2.2.2.2.2.2.2] at hcard
  rw [subOf_eq_closure_gElt gensE25 hgs] at hcard
  have hset : {g | ∃ k, ∃ hk : k < gensE25.size, gElt gensE25 hgs k hk = g} =
      ({xE, yE} : Set GJ) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k < 2 := hk
      interval_cases k
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
  rwa [hset] at hcard

theorem yE_pow_five : yE ^ 5 = 1 := by
  have hx5 := xE_pow_five
  have hxy := xE_mul_comm
  have hgx := gE_conj_x
  have hgy := gE_conj_y
  have hcard := card_closure_xy
  have hx1 := xE_ne_one
  set x := xE with hxdef
  set y := yE with hydef
  set g := gE with hgdef
  set P := Subgroup.closure ({x, y} : Set GJ) with hP
  have hxP : x ∈ P := Subgroup.subset_closure (by simp)
  have hyP : y ∈ P := Subgroup.subset_closure (by simp)
  have hgen : ∀ a ∈ ({x, y} : Set GJ), ∀ b ∈ ({x, y} : Set GJ), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hxy
    · exact hxy.symm
    · rfl
  have hcomm : ∀ a b : GJ, a ∈ P → b ∈ P → a * b = b * a := fun a b ha hb =>
    commute_of_mem_closure hgen ha hb
  have hy25 : y ^ 25 = 1 := by
    have h1 := pow_card_eq_one' (G := ↥P) (x := ⟨y, hyP⟩)
    rw [hcard] at h1
    exact congrArg Subtype.val h1
  set u := y ^ 5 with hu
  have hu5 : u ^ 5 = 1 := by rw [hu, ← pow_mul]; exact hy25
  have huP : u ∈ P := P.pow_mem hyP 5
  have hgu : g * u * g⁻¹ = u := by
    rw [hu, ← conj_pow, hgy, ((show Commute x y from hxy).pow_left 3).mul_pow, ← pow_mul,
      mul_comm 3 5, pow_mul, hx5, one_pow, one_mul]
  by_contra hy5
  have hu1 : u ≠ 1 := hy5
  have hord_x : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have hord_u : orderOf u = 5 := orderOf_eq_prime hu5 hu1
  by_cases hux : u ∈ Subgroup.zpowers x
  ·
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hux
    have h1 : g * u * g⁻¹ = x ^ (4 * j) := by
      rw [← hj, ← conj_zpow, hgx, ← zpow_natCast, ← zpow_mul]
      norm_num
    rw [hgu] at h1
    have hjh : x ^ j = x ^ (4 * j) := hj.trans h1
    have h2 : x ^ (4 * j - j) = 1 := by rw [zpow_sub, ← hjh, mul_inv_cancel]
    have hdiv : ((5 : ℕ) : ℤ) ∣ 4 * j - j := by
      rw [← hord_x]
      exact orderOf_dvd_iff_zpow_eq_one.mpr h2
    have h5j : (5 : ℤ) ∣ j := by
      have h3 : (5 : ℤ) ∣ 4 * j - j := by exact_mod_cast hdiv
      omega
    have h6 : x ^ j = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hord_x]; exact_mod_cast h5j)
    exact hu1 (hj ▸ h6)
  · have hH1 : Nat.card (Subgroup.zpowers x) = 5 := by rw [Nat.card_zpowers, hord_x]
    set K := Subgroup.zpowers x ⊔ Subgroup.zpowers u with hK
    have hKP : K ≤ P :=
      sup_le (Subgroup.zpowers_le.mpr hxP) (Subgroup.zpowers_le.mpr huP)
    have hd1 : 5 ∣ Nat.card K := hH1 ▸ Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers x ≤ K)
    have hd2 : Nat.card K ∣ 25 := hcard ▸ Subgroup.card_dvd_of_le hKP
    have hK5 : Nat.card K ≠ 5 := by
      intro h5
      have heq : Subgroup.zpowers x = K :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h5, hH1])
      exact hux (heq ▸ (le_sup_right : Subgroup.zpowers u ≤ K) (Subgroup.mem_zpowers u))
    have hK25 : Nat.card K = 25 := by
      obtain ⟨i, hi, hiK⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp
        (show Nat.card K ∣ 5 ^ 2 by simpa using hd2)
      interval_cases i
      · rw [hiK] at hd1; omega
      · exact absurd (by simpa using hiK) hK5
      · simpa using hiK
    have hKeq : K = P := Subgroup.eq_of_le_of_card_ge hKP (by rw [hK25, hcard])
    have hyK : y ∈ K := hKeq ▸ hyP
    have hxn : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers u : Set GJ) := by
      intro a ha
      have haP : a ∈ P := Subgroup.zpowers_le.mpr hxP ha
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      have hnP : n ∈ P := Subgroup.zpowers_le.mpr huP hn
      rw [hcomm a n haP hnP, mul_inv_cancel_right]
      exact hn
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers x)
      (Subgroup.zpowers u) hxn
    have hyK' : y ∈ (Subgroup.zpowers x : Set GJ) * (Subgroup.zpowers u : Set GJ) := by
      rw [← hmul]
      exact hyK
    obtain ⟨a, ha, b, hb, hab⟩ := hyK'
    have haP : a ∈ P := Subgroup.zpowers_le.mpr hxP ha
    have hbP : b ∈ P := Subgroup.zpowers_le.mpr huP hb
    have ha5 : a ^ 5 = 1 := pow_eq_one_of_mem_zpowers hx5 ha
    have hb5 : b ^ 5 = 1 := pow_eq_one_of_mem_zpowers hu5 hb
    have hy5' : y ^ 5 = 1 := by
      rw [← hab, (show Commute a b from hcomm a b haP hbP).mul_pow, ha5, hb5, one_mul]
    exact hy5 hy5'

end Witness

section Rank

theorem two_le_pRank_five_GJ : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup GJ) := by
  have hx5 := xE_pow_five
  have hxy := xE_mul_comm
  have hord_x : orderOf xE = 5 := orderOf_eq_prime hx5 xE_ne_one
  have hEcard : Nat.card (Subgroup.zpowers xE) = 5 ^ 1 := by
    rw [Nat.card_zpowers, hord_x, pow_one]
  have hE : CFSG.Open.IsElemAbelian 5 (Subgroup.zpowers xE) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => pow_eq_one_of_mem_zpowers hx5 ha⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact Subtype.ext (Commute.zpow_zpow_self xE i j).eq
  have hbE : yE ∉ Subgroup.zpowers xE := by
    intro hy
    have hle : Subgroup.closure ({xE, yE} : Set GJ) ≤ Subgroup.zpowers xE := by
      rw [Subgroup.closure_le]
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact Subgroup.mem_zpowers _
      · exact hy
    have h1 := Subgroup.card_le_of_le hle
    rw [card_closure_xy, hEcard] at h1
    omega
  have hbc : ∀ e ∈ Subgroup.zpowers xE, Commute e yE := by
    intro e he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact (show Commute xE yE from hxy).zpow_left i
  exact CFSG.RankThree.OddKernel.succ_le_pRank_of_commute (p := 5) (by norm_num) hE hEcard hbc
    yE_pow_five hbE le_top (Subgroup.mem_top _)

end Rank

theorem two_le_pRank_five_J2 :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup NativeSporadic.J2) :=
  calc 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup GJ) := two_le_pRank_five_GJ
    _ = CFSG.Open.pRank 5 (⊤ : Subgroup NativeSporadic.J2) :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) nativeEquivP).symm

end CFSG.RankThree.PartTwo.Sec17.G1724
