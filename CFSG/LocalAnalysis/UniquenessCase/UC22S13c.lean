module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen4a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.UC1K337
import CFSG.GH74.KGroups.CoverEven
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.F13 Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s13c_mem_sup_of_inner {M K : Subgroup G} (hKn : (K.subgroupOf M).Normal)
    [(barImage M K).Normal] {y : G} (hy : y ∈ M)
    (h : MulAut.conjNormal (H := barImage M K)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hy⟩ : Bar2 M) ∈
      (MulAut.conj : ↥(barImage M K) →* MulAut ↥(barImage M K)).range) :
    y ∈ K ⊔ cMStar M K := by
  obtain ⟨j, hj⟩ := h
  refine uc22s13b_mem_sup_cMStar_of_inner hKn hy ⟨j, j.2, fun k hk => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥(barImage M K) => ((φ ⟨k, hk⟩ : ↥(barImage M K)) : Bar2 M))
    hj
  simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1
  exact h1.symm

theorem uc22s13c_inner_of_isU3 {M K : Subgroup G} (hK : K ∈ calC M)
    (hKn : (K.subgroupOf M).Normal) {m k : ℕ} (hk : m = 2 ^ k) (hU : IsU3 (Bar2 K) m) {r : ℕ}
    (hr : r.Prime) (hr7 : 7 ≤ r) {y : G} (hy : y ∈ M) (hyr : y ^ r = 1) :
    y ∈ K ⊔ cMStar M K := by
  haveI : (barImage M K).Normal := PartTwo.s13_barImage_normal hKn
  have hrn : ¬ r ∣ 6 * m := by
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h6 | h2k
    · have := Nat.le_of_dvd (by norm_num) h6
      omega
    · rw [hk] at h2k
      have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h2k)
      omega
  have hyr' : (⟨y, hy⟩ : ↥M) ^ r = 1 := Subtype.ext (by simpa using hyr)
  refine uc22s13c_mem_sup_of_inner hKn hy ?_
  obtain ⟨e⟩ := PartTwo.s13_bar_equiv hK
  refine uc22p2214_out_mem_of_congr e.symm (uc22p2214_inner_of_prime_U3 hU hr hrn ?_)
  rw [← map_pow, ← map_pow, ← map_pow, hyr', map_one, map_one, map_one]

theorem uc22s13c_dvd_two_pow_two_mul_sub_one {q m : ℕ} (h : q ∣ 2 ^ m + 1) :
    q ∣ 2 ^ (2 * m) - 1 := by
  have h1 : 2 ^ (2 * m) - 1 = (2 ^ m + 1) * (2 ^ m - 1) := by
    rw [← Nat.sq_sub_sq, one_pow, ← pow_mul, mul_comm m 2]
  rw [h1]
  exact dvd_mul_of_dvd_left h _

theorem uc22s13c_three_lt_minFac {m k : ℕ} (hk : m = 2 ^ k) (hm2 : 2 ≤ m) :
    (Nat.minFac (2 ^ m + 1)).Prime ∧ 3 < Nat.minFac (2 ^ m + 1) ∧
      Nat.minFac (2 ^ m + 1) ∣ 2 ^ m + 1 := by
  have hq : (Nat.minFac (2 ^ m + 1)).Prime := Nat.minFac_prime (by
    have := Nat.one_le_two_pow (n := m)
    omega)
  have hqd : Nat.minFac (2 ^ m + 1) ∣ 2 ^ m + 1 := Nat.minFac_dvd _
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  have hm_even : Even m := by
    rw [hk]
    exact (Nat.even_pow' hk0).2 even_two
  obtain ⟨j, hj⟩ := hm_even
  have h3 : (2 ^ m + 1) % 3 = 2 := by
    rw [hj, ← two_mul, pow_mul, Nat.add_mod, Nat.pow_mod]
    norm_num
  have h2 : (2 ^ m + 1) % 2 = 1 := by
    rw [Nat.add_mod, Nat.pow_mod]
    have hm0 : m ≠ 0 := by omega
    simp [Nat.zero_pow (Nat.pos_of_ne_zero hm0)]
  refine ⟨hq, ?_, hqd⟩
  have hq2 : Nat.minFac (2 ^ m + 1) ≠ 2 := by
    intro h
    rw [h] at hqd
    omega
  have hq3 : Nat.minFac (2 ^ m + 1) ≠ 3 := by
    intro h
    rw [h] at hqd
    omega
  have := hq.two_le
  omega

theorem uc22s13c_not_isU3 (D : Data G) (hH : Hyp131 D) (h846 : F08.R846 D)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) {n : ℕ}
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s : ℕ} (hs : Odd s) (hsn : s ∣ n) {r : ℕ}
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {X : Subgroup G} (hXL : X ≤ L) (hXr : Nat.card X = r)
    {g : G} (hg : g ∉ D.M) (hYM : X.map (MulAut.conj g).toMonoidHom ≤ D.M) :
    ¬ ∃ m : ℕ, IsU3 (Bar2 K) m := by
  rintro ⟨m₀, hU₀⟩
  obtain ⟨m, ⟨k, hk⟩, hU⟩ : ∃ m : ℕ, (∃ k : ℕ, m = 2 ^ k) ∧ IsU3 (Bar2 K) m := by
    rcases hH.thinOrU3 K hK with hthin | h
    · exact absurd hthin (PartTwo.S17.not_thin8_of_isU3 hU₀)
    · exact h
  have hm2 : 2 ≤ m := PartTwo.s13_two_le_of_isU3 hU
  have hr7 : 7 ≤ r := PartTwo.s13_seven_le_of_dvd hs hr hrs
  have hr2 : r ≠ 2 := by omega
  obtain ⟨hq, hq3, hqd⟩ := uc22s13c_three_lt_minFac hk hm2
  set q := Nat.minFac (2 ^ m + 1)
  have hKn : (K.subgroupOf D.M).Normal := hH.normal K hK
  have hse : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M :=
    h846 K hK m (uc22p22d_isSU3_of_isU3 hK.2.2 hU) q hq hq3 hqd
  have hNY := PartTwo.s13_normalizer_map_conj_le g
    (hH.uniq L hL n hshape s hs hsn r hr hrs X hXL hXr).1
  have hYr : Nat.card ↥(X.map (MulAut.conj g).toMonoidHom) = r :=
    (PartTwo.s13_card_map_conj X g).trans hXr
  have hin : X.map (MulAut.conj g).toMonoidHom ≤ K ⊔ cMStar D.M K := by
    intro y hy
    have hyr : y ^ r = 1 := by
      have h1 := Subgroup.orderOf_dvd_natCard _ hy
      rw [hYr] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    exact uc22s13c_inner_of_isU3 hK hKn hk hU hr hr7 (hYM hy) hyr
  obtain ⟨e⟩ := PartTwo.s13_bar_equiv hK
  obtain ⟨f⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even hm2 hU
  have hcard : Nat.card ↥(barImage D.M K) = Nat.card (CFSG.Open.PSU3 2 m) :=
    (Nat.card_congr e.symm.toEquiv).trans (Nat.card_congr f.toEquiv)
  have hqK : q ∣ Nat.card ↥(barImage D.M K) := by
    rw [hcard]
    exact (CFSG.SignalizerFunctorTheorem.CatalogBridge.prime_dvd_card_psu3_iff (by omega) hq
      (by omega)).2 (Or.inr (Or.inl (uc22s13c_dvd_two_pow_two_mul_sub_one hqd)))
  have hrK : r ∣ Nat.card ↥(barImage D.M K) :=
    PartTwo.s13_r_dvd_card_bar D hq (by omega) hse hr hr2 hYM hYr hg hNY hK hin hqK
  have hrK' : r ∣ Nat.card (Bar2 K) := by
    rwa [Nat.card_congr e.toEquiv]
  have h2s : (2 : ZMod r) ^ s = 1 := by
    have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have h0 : ((2 ^ s - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrs
    rw [Nat.cast_sub h1] at h0
    push_cast at h0
    exact sub_eq_zero.1 h0
  have hodd : Odd (orderOf (2 : ZMod r)) := hs.of_dvd_nat (orderOf_dvd_of_pow_eq_one h2s)
  exact (InS3.k337_holds r hr hr2 m m ⟨k, hk⟩ ⟨k, hk⟩).2.2.2.2 hodd (Bar2 K) hU hrK'

end CFSG.LocalAnalysis.UniquenessCase.UC22
