module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2U
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2G2D4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4
import CFSG.LocalAnalysis.UniquenessCase.UC22S218D4
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Aut
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Out
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4Out
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21j
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.LieType.Multipliers.U62Sylow
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_false_of_torusFacts_of_pair {Tor Out : ℕ → Prop} {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hF : TorusFacts218 (BarInf L) n Tor Out) {r : ℕ} {A : Subgroup (BarInf L)}
    (hAe : IsElemAbelian r A) (hAc : Nat.card A = r ^ 2) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ 2 ^ c.n - 1) (hY2 : ¬ r ∣ Nat.card (Sylow 2 (BarInf L)))
    (hrZ : ¬ r ∣ Nat.card (center (Bar2 L))) {p : ℕ} (hp : p ∈ D.sig)
    (hpair : (L.subgroupOf D.M).Normal → ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L) →
      ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ D.M ∧
        IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k) :
    False := by
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  have hrσ : r ∉ D.sig := uc22s2114_not_mem_sig hSg hns hH c hr hrn
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hrK := not_dvd_card_solvableRadical hL.2.2 hr hr2 hrZ
  have hrL : 2 ≤ CFSG.Open.pRank r L := by
    rw [pRank_eq_pRank_barInf hr hrK]
    exact CFSG.SectionRank.le_pRank hr.one_lt le_top hAe hAc
  have hML : D.M ≤ normalizer (L : Set G) := by
    by_contra hML
    obtain ⟨E, hEL, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hr hrL
    have := UC6S846.calCRankTwice D.M L hL hML r hr hr2 hrZ E hEL hEel 2 hEc
    exact hrσ (hSg.four_mem r hr hr2 (by omega))
  obtain ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ :=
    hpair ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hML) hrK
  exact uc22s217u3a_false_of_sp D Ch hH c hr hrn
    (uc22s2114_strongly_of_pair D hSg h614 hL hML hF hpp
      (h76 p hp hp2 (UC6S846.sp_of_mem_sig hSg hns hp)) hr hr2 hY2 hrK hrσ hEL hEel hEc hQM
      hQel hQc hpow)

theorem uc22s2114_false_of_isU4_of_dvd (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : IsU4 (BarInf L) f) (hf : 2 ∣ f)
    (hn : 2 ∣ c.n) {p : ℕ} (hp : p ∈ D.sig) (hpf : p ∣ 2 ^ f + 1) : False := by
  have h3n : 3 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 3 ∣ 2 ^ 2 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have h3f : 3 ∣ 2 ^ f - 1 :=
    (by norm_num : 3 ∣ 2 ^ 2 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have hZ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Nat.card (center (Bar2 L)) := fun ℓ hℓ => by
    rw [uc22s2114_center_bar2_eq_bot_of_isU4_of_ne_one hGA hL hX (by omega), card_bot]
    exact hℓ.not_dvd_one
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hsq : 2 ^ (2 * f) - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [h2]
    zify [h1, Nat.one_le_pow 2 (2 ^ f) (by omega)]
    ring
  have hp2f : p ∣ 2 ^ (2 * f) - 1 := hsq ▸ Dvd.dvd.mul_left hpf _
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h2 : 3 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hpf h3f
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rw [show 2 ^ f + 1 - (2 ^ f - 1) = 2 by omega] at h2
    omega
  have hpK := not_dvd_card_solvableRadical hL.2.2 hpp hp2 (hZ p hpp)
  obtain ⟨T, hTc, hTE, hTo⟩ := uc22s218_u4_torus hX
  obtain ⟨E₀, hE₀T, hE₀, hE₀c⟩ := hTE 3 Nat.prime_three h3f
  obtain ⟨y, hyT, hyo⟩ := hTo p hpp hp2f
  refine uc22s2114_false_of_torusFacts_of_pair hSg h614 h76 hH c hL (torusFacts218_U4 hX) hE₀
    hE₀c Nat.prime_three (by norm_num) h3n
    (uc22s2114_u4_not_dvd_card_sylow hX Nat.prime_three (by norm_num) h3f)
    (hZ 3 Nat.prime_three) hp fun hN hrK => ?_
  have := hN
  refine uc22s218_exists_pair_of_outer hL.1.le (CFSG.solvableRadical ↥L) hpp Nat.prime_three hp3
    hpK hrK (h4 p hp) hE₀ hE₀c hyo (fun e he => hTc y hyT e (hE₀T he)) ?_
    (fun V hV hVc => uc22s218_u4_outer_pair hX hpp hp2 hpf Nat.prime_three h3f V hV hVc)
  by_contra hcen
  have hy1 := (uc22s218_u4_fieldBorel hX).center_eq_one y fun x =>
    (by_contra fun h => hcen ⟨x, h⟩ : x * y = y * x).symm
  rw [hy1, orderOf_one] at hyo
  exact hpp.one_lt.ne hyo

theorem uc22s2114_false_of_isU4_even (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : IsU4 (BarInf L) f) (hf : 2 ∣ f)
    (hn : 2 ∣ c.n) : False := by
  obtain ⟨p, hp⟩ := hSg.nonempty
  by_cases hpf : p ∣ 2 ^ f + 1
  · exact uc22s2114_false_of_isU4_of_dvd hGA hSg h614 h76 h4 hH c hL hX hf hn hp hpf
  · exact uc22s2114_false_of_isU4 hGA hSg h614 h76 h4 hH c hL hX hf hn hp hpf

section D4


theorem uc22s2114_false_of_is3D4_of_dvd {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : Is3D4 (BarInf L) f) (hf : 4 ∣ f)
    (hn : 4 ∣ c.n) {p : ℕ} (hp : p ∈ D.sig) (hpf : p ∣ 2 ^ (2 * f) + 2 ^ f + 1) : False := by
  have h5f : 5 ∣ 2 ^ f - 1 :=
    (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have h5n : 5 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have hZ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Nat.card (center (Bar2 L)) := fun ℓ hℓ => by
    rw [center_bar2_eq_bot_of_is3D4 hL hX, card_bot]
    exact hℓ.not_dvd_one
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hcube : 2 ^ (3 * f) - 1 = (2 ^ f - 1) * (2 ^ (2 * f) + 2 ^ f + 1) := by
    have h3 : 2 ^ (3 * f) = (2 ^ f) ^ 3 := by rw [← pow_mul, mul_comm]
    have h2 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [h3, h2]
    zify [h1, Nat.one_le_pow 3 (2 ^ f) (by omega)]
    ring
  have hp3f : p ∣ 2 ^ (3 * f) - 1 := hcube ▸ Dvd.dvd.mul_left hpf _
  have hp5 : p ≠ 5 := by
    rintro rfl
    obtain ⟨a, ha⟩ := h5f
    have h2 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [h2, show 2 ^ f = 5 * a + 1 by omega] at hpf
    have : (5 * a + 1) ^ 2 + (5 * a + 1) + 1 = 5 * (5 * a ^ 2 + 3 * a) + 3 := by ring
    omega
  have hpK := not_dvd_card_solvableRadical hL.2.2 hpp hp2 (hZ p hpp)
  have haut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (BarInf L))) ≤ 3 := by
    have h1 := pRank_mulAut_le_of_fieldBorel (uc22s218_d4_fieldBorel hX) hpp
    have h2 := uc22s218_d4_pRank_le_two hX hpp hp2
    omega
  obtain ⟨T, hTc, hTE, hTo⟩ := uc22s218_d4_torus hX
  obtain ⟨E₀, hE₀T, hE₀, hE₀c⟩ := hTE 5 Nat.prime_five h5f
  obtain ⟨y, hyT, hyo⟩ := hTo p hpp hp3f
  refine uc22s2114_false_of_torusFacts_of_pair hSg h614 h76 hH c hL (torusFacts218_3D4 hX) hE₀
    hE₀c Nat.prime_five (by norm_num) h5n
    (uc22s2114_d4_not_dvd_card_sylow hX Nat.prime_five (by norm_num) (by norm_num) h5f)
    (hZ 5 Nat.prime_five) hp fun hN hrK => ?_
  have := hN
  refine uc22s218_exists_pair_of_kernel hL.1.le (CFSG.solvableRadical ↥L) hpp Nat.prime_five hp5
    hpK hrK haut (h4 p hp) hE₀ hE₀c hyo (fun e he => hTc y hyT e (hE₀T he)) ?_
  by_contra hcen
  have hy1 := (uc22s218_d4_fieldBorel hX).center_eq_one y fun x =>
    (by_contra fun h => hcen ⟨x, h⟩ : x * y = y * x).symm
  rw [hy1, orderOf_one] at hyo
  exact hpp.one_lt.ne hyo

theorem uc22s2114_false_of_is3D4_four_dvd {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : Is3D4 (BarInf L) f) (hf : 4 ∣ f)
    (hn : 4 ∣ c.n) : False := by
  obtain ⟨p, hp⟩ := hSg.nonempty
  by_cases hpf : p ∣ 2 ^ (2 * f) + 2 ^ f + 1
  · exact uc22s2114_false_of_is3D4_of_dvd hSg h614 h76 h4 hH c hL hX hf hn hp hpf
  · exact uc22s2114_false_of_is3D4 hSg h614 h76 h4 hH c hL hX hf hn hp hpf

end D4

end CFSG.LocalAnalysis.UniquenessCase.UC22
