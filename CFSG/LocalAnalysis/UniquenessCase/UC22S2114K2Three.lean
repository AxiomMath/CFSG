module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Weir
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Tor
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2U
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2G2D4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U4
import CFSG.LocalAnalysis.UniquenessCase.UC22S218G2
import CFSG.LocalAnalysis.UniquenessCase.UC22S218NTorus
import CFSG.LocalAnalysis.UniquenessCase.UC22S218NFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_false_of_torusFacts_three {Tor Out : ℕ → Prop} {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hF : TorusFacts218 (BarInf L) n Tor Out) {T : Subgroup (BarInf L)}
    (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hTE : ∀ ℓ : ℕ, ℓ.Prime → Tor ℓ →
      ∃ A : Subgroup (BarInf L), A ≤ T ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrT : Tor r) (hrn : r ∣ 2 ^ c.n - 1)
    (hY2 : ¬ r ∣ Nat.card (Sylow 2 (BarInf L))) (hrZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    {p : ℕ} (hp : p ∈ D.sig) (hpZ : ¬ p ∣ Nat.card (center (Bar2 L)))
    (hpTO : Tor p ∨ (Out p ∧ CFSG.Open.pRank p L ≤ 1)) : False := by
  obtain ⟨A, hAT, hAe, hAc⟩ := hTE r hr hrT
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hrσ : r ∉ D.sig :=
    uc22s2114_not_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hH c hr hrn
  have hpr : p ≠ r := fun h => hrσ (h ▸ hp)
  have hpK := not_dvd_card_solvableRadical hL.2.2 hpp hp2 hpZ
  refine uc22s2114_false_of_torusFacts_of_pair hSg h614 h76 hH c hL hF hAe hAc hr hr2 hrn hY2
    hrZ hp fun hN hrK => ?_
  rcases hpTO with hpT | ⟨hpO, hpL⟩
  · obtain ⟨B, hBT, hBe, hBc⟩ := hTE p hpp hpT
    obtain ⟨E, Q, hEL, hEel, hEc, hQL, hQel, hQc, hpow⟩ :=
      uc22s2114_exists_pair_of_abelian hTc hAT hAe hAc hBT hBe hBc hpp hr hpr hpK hrK
    exact ⟨E, Q, hEL, hEel, hEc, hQL.trans hL.1.le, hQel, hQc, hpow⟩
  · have hrL : 2 ≤ CFSG.Open.pRank r L := by
      rw [pRank_eq_pRank_barInf hr hrK]
      exact CFSG.SectionRank.le_pRank hr.one_lt le_top hAe hAc
    have := hN
    exact uc22s2114_exists_pair_of_out hL.1.le hF hpp hp2 hpO hpK hr hr2 hY2 hrL hrK hpr
      (by have := hSg.three_le p hp; omega)

section Table


theorem uc22s2114_false_of_isSp4_three (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ}
    (hX : IsSp4 (BarInf L) f) (hf : 2 ∣ f) (hn : 2 ∣ c.n) {p : ℕ} (hp : p ∈ D.sig)
    (hpf : ¬ p ∣ 2 ^ f + 1) : False := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  have hX2 : IsSp4 (Bar2 L) f := uc22s218n_isSp4_bar2 hGA hL hX
  have hf2 : 2 ≤ f := by
    have := (CFSG.Blueprint.LieModel.admissible hX).2.1
    omega
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
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp3 : p ≠ 3 := fun h => h3σ (h ▸ hp)
  obtain ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ : ∃ E Q : Subgroup G, E ≤ L ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ Q ≤ D.M ∧ IsElemAbelian p Q ∧
        Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
    by_cases hpq : p ∣ 2 ^ f - 1
    · obtain ⟨E, Q, hEL, hEel, hEc, hQL, hQel, hQc, hpow⟩ :=
        uc22s218n_exists_pow_torus_inner hX2 hpp hp2 hpq h3 (by norm_num) h3f hp3
      exact ⟨E, Q, hEL, hEel, hEc, hQL.trans hLM, hQel, hQc, hpow⟩
    · have hpL := uc22s2114_pRank_le_one_of_rootLineShape hGA hL
        (uc22p218d_center_eq_bot_sp4 hX2) hf2 (Or.inr (Or.inl hX)) hpp hp2 hpq hpf
      exact uc22p218s_exists_pow_torus hLM hX2 hpp hp2 hpq h3 (by norm_num) h3f
        (by have := hSg.three_le p hp; omega)
  exact uc22s217u3a_false_of_sp D Ch hH c h3 h3n
    (uc22s218n_stronglyEmbedded_of_torus D hSg h614 hL hML hX2 hpp
      (h76 p hp hp2 (UC6S846.sp_of_mem_sig hSg hns hp)) h3 (by norm_num) h3f h3σ hEL hEel hEc
      hQM hQel hQc hpow)

theorem uc22s2114_false_of_isU4_three (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ}
    (hX : IsU4 (BarInf L) f) (hf : 2 ∣ f) (hn : 2 ∣ c.n) {p : ℕ} (hp : p ∈ D.sig)
    (hpf : ¬ p ∣ 2 ^ f + 1) : False := by
  have hf2 : 2 ≤ f := by
    have := (CFSG.Blueprint.LieModel.admissible hX).2.1
    omega
  have h3n : 3 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 3 ∣ 2 ^ 2 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have h3f : 3 ∣ 2 ^ f - 1 :=
    (by norm_num : 3 ∣ 2 ^ 2 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have hZ0 := uc22s2114_center_bar2_eq_bot_of_isU4_of_ne_one hGA hL hX (by omega)
  have hZ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Nat.card (center (Bar2 L)) := fun ℓ hℓ => by
    rw [hZ0, card_bot]
    exact hℓ.not_dvd_one
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  obtain ⟨T, hTc, hTE, -⟩ := uc22s218_u4_torus hX
  refine uc22s2114_false_of_torusFacts_three hSg h614 h76 hH c hL (torusFacts218_U4 hX) hTc hTE
    Nat.prime_three (by norm_num) h3f h3n
    (uc22s2114_u4_not_dvd_card_sylow hX Nat.prime_three (by norm_num) h3f)
    (hZ 3 Nat.prime_three) hp (hZ p hpp) ?_
  by_cases hpq : p ∣ 2 ^ f - 1
  · exact Or.inl hpq
  · exact Or.inr ⟨⟨hpq, hpf⟩, uc22s2114_pRank_le_one_of_rootLineShape hGA hL hZ0 hf2
      (Or.inl hX) hpp hp2 hpq hpf⟩

theorem uc22s2114_false_of_isU5_three (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ}
    (hX : IsU5 (BarInf L) f) (hf : 2 ∣ f) (hn : 4 ∣ c.n) : False := by
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have h15 : 15 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 15 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have h5σ : 5 ∉ D.sig :=
    uc22s2114_not_mem_sig hSg hns hH c (by norm_num) ((by norm_num : 5 ∣ 15).trans h15)
  have h3f : 3 ∣ 2 ^ f - 1 :=
    (by norm_num : 3 ∣ 2 ^ 2 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have h3f2 : 3 ∣ 2 ^ (2 * f) - 1 :=
    h3f.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left f 2))
  have hZ := card_center_bar2_dvd_of_isU5 hGA hL hX
  have hZ5 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 5 → ¬ ℓ ∣ Nat.card (center (Bar2 L)) := fun ℓ hℓ hℓ5 h =>
    hℓ5 ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1
      (h.trans (hZ.trans (Nat.gcd_dvd_left 5 _))))
  obtain ⟨T, hTc, hTE⟩ := uc22s218_u5_torus hX
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp5 : p ≠ 5 := fun h => h5σ (h ▸ hp)
  refine uc22s2114_false_of_torusFacts_three hSg h614 h76 hH c hL (torusFacts218_U5 hX) hTc hTE
    Nat.prime_three (by norm_num) ⟨h3f2, fun h => absurd h.1 (by norm_num)⟩
    ((by norm_num : 3 ∣ 15).trans h15)
    (uc22s2114_u5_not_dvd_card_sylow hX Nat.prime_three (by norm_num) (by norm_num) h3f)
    (hZ5 3 Nat.prime_three (by norm_num)) hp (hZ5 p hpp hp5) ?_
  by_cases hpq : p ∣ 2 ^ (2 * f) - 1
  · exact Or.inl ⟨hpq, fun h => hp5 h.1⟩
  · exact Or.inr ⟨hpq, uc22s2114_pRank_le_one_of_isU5 hGA hL hX hpp hp2 hpq⟩

theorem uc22s2114_false_of_isG2_three (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ}
    (hX : IsG2 (BarInf L) f) (hf : 4 ∣ f) (hn : 4 ∣ c.n) {p : ℕ} (hp : p ∈ D.sig)
    (hpf : ¬ p ∣ 2 ^ f + 1) : False := by
  have hf2 : 2 ≤ f := by
    have := (CFSG.Blueprint.LieModel.admissible hX).2.1
    omega
  have h5f : 5 ∣ 2 ^ f - 1 :=
    (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf)
  have h5n : 5 ∣ 2 ^ c.n - 1 :=
    (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)
  have hZ0 := center_bar2_eq_bot_of_isG2 hL hX (by omega)
  have hZ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ Nat.card (center (Bar2 L)) := fun ℓ hℓ => by
    rw [hZ0, card_bot]
    exact hℓ.not_dvd_one
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  obtain ⟨T, hTc, hTE⟩ := uc22s218_g2_torus hX
  refine uc22s2114_false_of_torusFacts_three hSg h614 h76 hH c hL (torusFacts218_G2 hX) hTc hTE
    Nat.prime_five (by norm_num) h5f h5n
    (uc22s2114_g2_not_dvd_card_sylow hX Nat.prime_five (by norm_num) (by norm_num) h5f)
    (hZ 5 Nat.prime_five) hp (hZ p hpp) ?_
  by_cases hpq : p ∣ 2 ^ f - 1
  · exact Or.inl hpq
  · exact Or.inr ⟨hpq, uc22s2114_pRank_le_one_of_rootLineShape hGA hL hZ0 hf2
      (Or.inr (Or.inr hX)) hpp hp2 hpq hpf⟩

end Table

end CFSG.LocalAnalysis.UniquenessCase.UC22
