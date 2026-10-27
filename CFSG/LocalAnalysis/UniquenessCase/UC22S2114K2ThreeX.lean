module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218CenL
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Three
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Weir
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2G2D4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S218D4
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Aut
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21j
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_exists_mem_kernel_of_pRank_le {L M : Subgroup G} (hLM : L ≤ M)
    [(L.subgroupOf M).Normal] (K : Subgroup ↥L) [K.Characteristic] {p k : ℕ} (hp : p.Prime)
    (haut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (↥L ⧸ K))) ≤ k)
    (hrank : k + 1 ≤ CFSG.Open.pRank p M) :
    ∃ (x : G) (hx : x ∈ M), x ≠ 1 ∧ x ^ p = 1 ∧
      uc22s218_rhoK L K ⟨x, le_normalizer_of_normal_subgroupOf hLM hx⟩ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  obtain ⟨A, hAM, hAel, hAc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hrank
  let ρA : ↥A →* MulAut (↥L ⧸ K) :=
    (uc22s218_rhoK L K).comp (Subgroup.inclusion (hAM.trans hML))
  have : IsMulCommutative ↥A := hAel.1
  have hnotinj : ¬ Function.Injective ρA := fun hinj => by
    have h := CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm' a b)
      (fun a => Subtype.ext (hAel.2 _ a.2)) hAc ρA hinj (H := ⊤) le_top
    omega
  obtain ⟨a, ha1, hρa⟩ : ∃ a : ↥A, a ≠ 1 ∧ ρA a = 1 := by
    by_contra h
    exact hnotinj ((injective_iff_map_eq_one ρA).2 fun a ha =>
      by_contra fun h' => h ⟨a, h', ha⟩)
  exact ⟨(a : G), hAM a.2, fun h => ha1 (Subtype.ext h), hAel.2 _ a.2, hρa⟩


theorem uc22s2114_false_of_is3D4_three {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : Is3D4 (BarInf L) f)
    (hf : 4 ∣ f) (hn : 4 ∣ c.n) {p : ℕ} (hp : p ∈ D.sig) (hpl : ¬ p ∣ 2 ^ f + 1)
    (hpm : ¬ p ∣ 2 ^ (2 * f) - 2 ^ f + 1) (hpf : ¬ p ∣ f) : False := by
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have h5f : 5 ∣ 2 ^ f - 1 :=
    (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have h15 : 15 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 15 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have h5n : 5 ∣ 2 ^ c.n - 1 := (by norm_num : 5 ∣ 15).trans h15
  have h3σ : 3 ∉ D.sig :=
    uc22s2114_not_mem_sig hSg hns hH c Nat.prime_three ((by norm_num : 3 ∣ 15).trans h15)
  have hZ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Nat.card (center (Bar2 L)) := fun ℓ hℓ => by
    rw [center_bar2_eq_bot_of_is3D4 hL hX, card_bot]
    exact hℓ.not_dvd_one
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  obtain ⟨T, hTc, hTE, hTo⟩ := uc22s218_d4_torus hX
  have hY2 := uc22s2114_d4_not_dvd_card_sylow hX Nat.prime_five (by norm_num) (by norm_num) h5f
  by_cases hpd : p ∣ 2 ^ (2 * f) + 2 ^ f + 1
  ·
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hcube : 2 ^ (3 * f) - 1 = (2 ^ f - 1) * (2 ^ (2 * f) + 2 ^ f + 1) := by
      have h3 : 2 ^ (3 * f) = (2 ^ f) ^ 3 := by rw [← pow_mul, mul_comm]
      have h2 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [h3, h2]
      zify [h1, Nat.one_le_pow 3 (2 ^ f) (by omega)]
      ring
    have hp3f : p ∣ 2 ^ (3 * f) - 1 := hcube ▸ Dvd.dvd.mul_left hpd _
    have hp5 : p ≠ 5 := by
      rintro rfl
      obtain ⟨a, ha⟩ := h5f
      have h2 : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [h2, show 2 ^ f = 5 * a + 1 by omega] at hpd
      have : (5 * a + 1) ^ 2 + (5 * a + 1) + 1 = 5 * (5 * a ^ 2 + 3 * a) + 3 := by ring
      omega
    have hp3 : ¬ p ∣ 3 * f := fun h => by
      rcases hpp.dvd_mul.1 h with h | h
      · exact h3σ ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 h ▸ hp)
      · exact hpf h
    have hpK := not_dvd_card_solvableRadical hL.2.2 hpp hp2 (hZ p hpp)
    have haut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (BarInf L))) ≤ 2 :=
      (pRank_mulAut_le_of_fieldBorel_of_not_dvd (uc22s218_d4_fieldBorel hX) hpp hp3).trans
        (uc22s218_d4_pRank_le_two hX hpp hp2)
    obtain ⟨E₀, hE₀T, hE₀, hE₀c⟩ := hTE 5 Nat.prime_five h5f
    obtain ⟨y, hyT, hyo⟩ := hTo p hpp hp3f
    refine uc22s2114_false_of_torusFacts_of_pair hSg h614 h76 hH c hL (torusFacts218_3D4 hX) hE₀
      hE₀c Nat.prime_five (by norm_num) h5n hY2 (hZ 5 Nat.prime_five) hp fun hN hrK => ?_
    have := hN
    obtain ⟨x, hxM, hx1, hxp, hρ⟩ := uc22s2114_exists_mem_kernel_of_pRank_le hL.1.le
      (CFSG.solvableRadical ↥L) hpp haut (by have := hSg.three_le p hp; omega)
    refine uc22s218_exists_pair_of_kernel_elem hL.1.le (CFSG.solvableRadical ↥L) hpp
      Nat.prime_five hp5 hpK hrK hxM hx1 hxp hρ hE₀ hE₀c hyo
      (fun e he => hTc y hyT e (hE₀T he)) ?_
    by_contra hcen
    have hy1 := (uc22s218_d4_fieldBorel hX).center_eq_one y fun x =>
      (by_contra fun h => hcen ⟨x, h⟩ : x * y = y * x).symm
    rw [hy1, orderOf_one] at hyo
    exact hpp.one_lt.ne hyo
  · refine uc22s2114_false_of_torusFacts_three hSg h614 h76 hH c hL (torusFacts218_3D4 hX) hTc
      hTE Nat.prime_five (by norm_num) h5f h5n hY2 (hZ 5 Nat.prime_five) hp (hZ p hpp) ?_
    by_cases hpq : p ∣ 2 ^ f - 1
    · exact Or.inl hpq
    · exact Or.inr ⟨⟨hpq, hpd⟩, uc22s2114_pRank_le_one_of_is3D4 hL hX hpp hp2 hpq hpl hpd hpm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
