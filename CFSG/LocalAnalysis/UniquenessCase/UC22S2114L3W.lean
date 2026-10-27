module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Weir
import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Quasithin.H13.KG4413 (not_dvd_index_of_isPSL3)
open CFSG.Quasithin.H13.L32A.C.SkPf (isSylowTwoOf_sylow)

variable {G : Type} [Group G] [Finite G]


theorem uc22s2114_false_of_isL3_four_three (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ}
    (hX : IsL3 (BarInf L) f) (hf : 4 ∣ f) (hn : 4 ∣ c.n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Nat.Prime 5 := by norm_num
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  have hf4 : 4 ≤ f := by
    have := (LieModel.admissible hX).2.1
    omega
  have h15 : 15 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 15 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have h5n : 5 ∣ 2 ^ c.n - 1 := (by norm_num : 5 ∣ 15).trans h15
  have h5f : 5 ∣ 2 ^ f - 1 :=
    (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have h3σ : 3 ∉ D.sig :=
    uc22s2114_not_mem_sig hSg hns hH c Nat.prime_three ((by norm_num : 3 ∣ 15).trans h15)
  have h5σ : 5 ∉ D.sig := uc22s2114_not_mem_sig hSg hns hH c h5 h5n
  have hZ := uc22s2114_card_center_bar2_dvd_three hGA hL hX (by omega) (by omega)
  have hK : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → ¬ ℓ ∣ Nat.card (CFSG.solvableRadical ↥L) :=
    fun ℓ hℓ hℓ2 hℓ3 => not_dvd_card_solvableRadical hL.2.2 hℓ hℓ2 fun h =>
      hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 (h.trans hZ))
  have h5K := hK 5 h5 (by norm_num) (by norm_num)
  have h5L : 2 ≤ CFSG.Open.pRank 5 L := by
    obtain ⟨T, -, hTE⟩ := uc22s218_l3_torus hX
    obtain ⟨A, -, hAe, hAc⟩ := hTE 5 h5 h5f (by norm_num)
    rw [pRank_eq_pRank_barInf h5 h5K]
    exact CFSG.SectionRank.le_pRank h5.one_lt le_top hAe hAc
  have hML : D.M ≤ normalizer (L : Set G) := by
    by_contra hML
    obtain ⟨E, hEL, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank h5 h5L
    have := UC6S846.calCRankTwice D.M L hL hML 5 h5 (by norm_num)
      (fun h => absurd (h.trans hZ) (by norm_num)) E hEL hEel 2 hEc
    exact h5σ (hSg.four_mem 5 h5 (by norm_num) (by omega))
  have : (L.subgroupOf D.M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hML
  have hY2 : ¬ 5 ∣ Nat.card (Sylow 2 (BarInf L)) := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 (BarInf L)) := inferInstance
    rw [Sylow.card_eq_index_normalizer P]
    exact not_dvd_index_of_isPSL3 (LieModel.statedClassicalModel hX (by decide))
      (isSylowTwoOf_sylow P) h5 (by norm_num) h5f
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp3 : p ≠ 3 := fun h => h3σ (h ▸ hp)
  have hp5 : p ≠ 5 := fun h => h5σ (h ▸ hp)
  have hpK := hK p hpp hp2 hp3
  have hF := torusFacts218_L3 hX
  obtain ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ : ∃ E Q : Subgroup G, E ≤ L ∧
      IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2 ∧ Q ≤ D.M ∧ IsElemAbelian p Q ∧
        Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
    by_cases hpf : p ∣ 2 ^ f - 1
    · obtain ⟨E, Q, hEL, hEel, hEc, hQL, hQel, hQc, hpow⟩ :=
        uc22s2114_exists_pair_of_torus hX hpp hpf hp3 h5 h5f (by norm_num) hp5 hpK h5K
      exact ⟨E, Q, hEL, hEel, hEc, hQL.trans hLM, hQel, hQc, hpow⟩
    · have h1 := uc22s2114_pRank_le_one_of_isL3 hGA hL hX (by omega) hpp hp2 hpf
      exact uc22s2114_exists_pair_of_out hLM hF hpp hp2 hpf hpK h5 (by norm_num) hY2 h5L h5K
        hp5 (by have := hSg.three_le p hp; omega)
  exact uc22s217u3a_false_of_sp D Ch hH c h5 h5n
    (uc22s2114_strongly_of_pair D hSg h614 hL hML hF hpp
      (h76 p hp hp2 (UC6S846.sp_of_mem_sig hSg hns hp)) h5 (by norm_num) hY2 h5K h5σ hEL hEel
      hEc hQM hQel hQc hpow)

end CFSG.LocalAnalysis.UniquenessCase.UC22
