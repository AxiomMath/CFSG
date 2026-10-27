module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GAbs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_exists_pair_of_abelian {L : Subgroup G} {T A B : Subgroup (BarInf L)}
    {p r : ℕ} (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hAT : A ≤ T)
    (hAe : IsElemAbelian r A) (hAc : Nat.card A = r ^ 2) (hBT : B ≤ T)
    (hBe : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) (hp : p.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L))
    (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ L ∧
      IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  obtain ⟨E₂, Q₂, hE₂, hE₂c, hQ₂, hQ₂c, hpow₂⟩ :=
    exists_pair_lift (CFSG.solvableRadical ↥L) hp hr hpr hpK hrK hAe hAc hBe hBc
      fun x hx => ⟨1, fun e he => by
        rw [pow_one, mul_inv_eq_iff_eq_mul]
        exact hTc x (hBT hx) e (hAT he)⟩
  refine ⟨E₂.map L.subtype, Q₂.map L.subtype, Subgroup.map_subtype_le E₂, hE₂.map _, ?_,
    Subgroup.map_subtype_le Q₂, hQ₂.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hE₂c]
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hQ₂c]
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hpow₂ q hq
    refine ⟨k, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    simpa using congrArg (fun z : ↥L => (z : G)) (hk e he)

theorem uc22s2114_false_of_torusFacts {Tor Out : ℕ → Prop} {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hF : TorusFacts218 (BarInf L) n Tor Out)
    {T : Subgroup (BarInf L)} (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hTE : ∀ ℓ : ℕ, ℓ.Prime → Tor ℓ →
      ∃ A : Subgroup (BarInf L), A ≤ T ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrT : Tor r) (hrn : r ∣ 2 ^ c.n - 1)
    (hY2 : ¬ r ∣ Nat.card (Sylow 2 (BarInf L))) (hrZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    {p : ℕ} (hp : p ∈ D.sig) (hpZ : ¬ p ∣ Nat.card (center (Bar2 L))) (hpTO : Tor p ∨ Out p) :
    False := by
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  have hrσ : r ∉ D.sig := uc22s2114_not_mem_sig hSg hns hH c hr hrn
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hpr : p ≠ r := fun h => hrσ (h ▸ hp)
  have hrK := not_dvd_card_solvableRadical hL.2.2 hr hr2 hrZ
  have hpK := not_dvd_card_solvableRadical hL.2.2 hpp hp2 hpZ
  obtain ⟨A, hAT, hAe, hAc⟩ := hTE r hr hrT
  have hrL : 2 ≤ CFSG.Open.pRank r L := by
    rw [pRank_eq_pRank_barInf hr hrK]
    exact CFSG.SectionRank.le_pRank hr.one_lt le_top hAe hAc
  have hML : D.M ≤ normalizer (L : Set G) := by
    by_contra hML
    obtain ⟨E, hEL, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hr hrL
    have := UC6S846.calCRankTwice D.M L hL hML r hr hr2 hrZ E hEL hEel 2 hEc
    exact hrσ (hSg.four_mem r hr hr2 (by omega))
  have : (L.subgroupOf D.M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hML
  obtain ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ : ∃ E Q : Subgroup G, E ≤ L ∧
      IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ D.M ∧ IsElemAbelian p Q ∧
        Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
    rcases hpTO with hpT | hpO
    · obtain ⟨B, hBT, hBe, hBc⟩ := hTE p hpp hpT
      obtain ⟨E, Q, hEL, hEel, hEc, hQL, hQel, hQc, hpow⟩ :=
        uc22s2114_exists_pair_of_abelian hTc hAT hAe hAc hBT hBe hBc hpp hr hpr hpK hrK
      exact ⟨E, Q, hEL, hEel, hEc, hQL.trans hLM, hQel, hQc, hpow⟩
    · have h1 := hF.pRank_le_two hpp hp2 hpO
      rw [← pRank_eq_pRank_barInf hpp hpK] at h1
      exact uc22s2114_exists_pair_of_out hLM hF hpp hp2 hpO hpK hr hr2 hY2 hrL hrK hpr
        (by have := h4 p hp; omega)
  exact uc22s217u3a_false_of_sp D Ch hH c hr hrn
    (uc22s2114_strongly_of_pair D hSg h614 hL hML hF hpp
      (h76 p hp hp2 (UC6S846.sp_of_mem_sig hSg hns hp)) hr hr2 hY2 hrK hrσ hEL hEel hEc hQM
      hQel hQc hpow)

end CFSG.LocalAnalysis.UniquenessCase.UC22
