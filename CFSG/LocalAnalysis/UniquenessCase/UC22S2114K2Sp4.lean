module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S218NTorus
import CFSG.LocalAnalysis.UniquenessCase.UC22S218NFour
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_false_of_isSp4 (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : IsSp4 (BarInf L) f) (hf : 2 ∣ f)
    (hn : 2 ∣ c.n) : False := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  have hX2 : IsSp4 (Bar2 L) f := uc22s218n_isSp4_bar2 hGA hL hX
  have h3n : 3 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 3 ∣ 2 ^ 2 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have h3f : 3 ∣ 2 ^ f - 1 :=
    (by norm_num : 3 ∣ 2 ^ 2 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have h3σ : 3 ∉ D.sig := uc22s2114_not_mem_sig hSg hns hH c h3 h3n
  have hML : D.M ≤ normalizer (L : Set G) := by
    by_contra hML
    obtain ⟨E, hEL, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank h3
      (uc22p218c_pRank_eq_two_of_bar2 hX2 h3 h3f).ge
    have := UC6S846.calCRankTwice D.M L hL hML 3 h3 (by norm_num)
      (by rw [uc22p218d_center_eq_bot_sp4 hX2, card_bot]; norm_num) E hEL hEel 2 hEc
    exact h3σ (hSg.four_mem 3 h3 (by norm_num) (by omega))
  have : (L.subgroupOf D.M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hML
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp3 : p ≠ 3 := fun h => h3σ (h ▸ hp)
  obtain ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ : ∃ E Q : Subgroup G, E ≤ L ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ Q ≤ D.M ∧ IsElemAbelian p Q ∧
        Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
    by_cases hpf : p ∣ 2 ^ f - 1
    · obtain ⟨E, Q, hEL, hEel, hEc, hQL, hQel, hQc, hpow⟩ :=
        uc22s218n_exists_pow_torus_inner hX2 hpp hp2 hpf h3 (by norm_num) h3f hp3
      exact ⟨E, Q, hEL, hEel, hEc, hQL.trans hLM, hQel, hQc, hpow⟩
    · have hpL := uc22p218d_pRank_le_two_of_bar2 hX2 hpp hp2
      exact uc22p218s_exists_pow_torus hLM hX2 hpp hp2 hpf h3 (by norm_num) h3f
        (by have := h4 p hp; omega)
  exact uc22s217u3a_false_of_sp D Ch hH c h3 h3n
    (uc22s218n_stronglyEmbedded_of_torus D hSg h614 hL hML hX2 hpp
      (h76 p hp hp2 (UC6S846.sp_of_mem_sig hSg hns hp)) h3 (by norm_num) h3f h3σ hEL hEel hEc
      hQM hQel hQc hpow)

end CFSG.LocalAnalysis.UniquenessCase.UC22
