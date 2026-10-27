module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RTheta
import CFSG.Quasithin.Background.A1cRankLemmas
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RThetaQ
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RCoprime
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RFiveCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

theorem OmegaModel.exists_subgroup_card_nine_two_le_pRank_five {W : Type} [CommGroup W]
    (S : OmegaModel W) (hK : Nat.card S.K = 4) (hΩ : Nat.card S.omega = 3600) {M : Type}
    [Group M] [Finite M] (π : M →* MulAut W) (hπ : π.range ≤ omegaNorm S)
    (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hker5 : ∀ A : Subgroup M, A ≤ π.ker → IsElemAbelian 5 A → Nat.card A ≤ 5)
    {F : Subgroup M} (hF : IsElemAbelian 3 F) (hFcard : Nat.card F = 3 ^ 3) {a : M}
    (haF : a ∈ F)
    (haω : π a ∉ S.omega) {F₅ : Subgroup M} (hF₅ : IsElemAbelian 5 F₅)
    (hF₅card : Nat.card F₅ = 5 ^ 3) :
    ∃ Q : Subgroup M, Q ≤ F ∧ Nat.card Q = 3 ^ 2 ∧
      2 ≤ CFSG.Open.pRank 5 (centralizer (Q : Set M)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite W :=
    Finite.of_injective (S.e : W → Multiplicative (OmI → S.K)) S.e.injective
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective
  have hΩ0 : S.omega = S.factor 0 ⊔ S.factor 1 :=
    (omega_eq_omega0_of_card S (by rw [hΩ, hK]; norm_num)).trans (factor_sup S).symm
  have hFker : F ⊓ π.ker = ⊥ := by
    have h3g : IsPGroup 3 ↥(F ⊓ π.ker) := hF.isPGroup.to_le inf_le_left
    have hdvd : Nat.card ↥(F ⊓ π.ker) ∣ Nat.card π.ker :=
      Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h3g
    have hkdvd : 3 ^ k ∣ Nat.card π.ker := hk ▸ hdvd
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exact h0
      · exact absurd (dvd_trans (dvd_pow_self 3 hpos.ne') hkdvd) hker3
    exact (F ⊓ π.ker).eq_bot_of_card_eq (by rw [hk, hk0, pow_zero])
  have hinjF : Function.Injective (π.domRestrict F) := by
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict]
    apply Subgroup.eq_bot_of_card_eq
    have hmap : (π.ker.subgroupOf F).map F.subtype = F ⊓ π.ker := by
      rw [Subgroup.subgroupOf_map_subtype, inf_comm]
    rw [hFker] at hmap
    rw [← Subgroup.card_map_of_injective (K := π.ker.subgroupOf F) (f := F.subtype)
      F.subtype_injective, hmap]
    simp
  have hEcard : Nat.card ↥(F.map π) = 3 ^ 3 := by
    have h1 : Nat.card ↥(F.map π) = Nat.card ↥F := by
      rw [← MonoidHom.domRestrict_range (K := F) (f := π)]
      exact (Nat.card_congr (MonoidHom.ofInjective (f := π.domRestrict F) hinjF).toEquiv).symm
    rw [h1, hFcard]
  have hEN : F.map π ≤ omegaNorm S := (Subgroup.map_le_range π F).trans hπ
  have hEel : IsElemAbelian 3 (F.map π) := hF.map π
  have haE : π a ∈ F.map π := Subgroup.mem_map_of_mem π haF
  obtain ⟨Q₀, hQ₀E, hQ₀card, hQ₀cent⟩ :=
    OmegaModel.exists_subgroup_card_nine_centralizer_factor S hK hΩ hEN hEel hEcard haE haω
  let Q : Subgroup M := F ⊓ Q₀.comap π
  have hQF : Q ≤ F := inf_le_left
  have hQmap : Q.map π = Q₀ := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact Subgroup.mem_comap.mp hx.2
    · intro y hy
      have hyE : y ∈ F.map π := hQ₀E hy
      obtain ⟨x, hxF, hx⟩ := Subgroup.mem_map.mp hyE
      rw [← hx]
      exact Subgroup.mem_map_of_mem π
        (Subgroup.mem_inf.mpr ⟨hxF, Subgroup.mem_comap.mpr (by rw [hx]; exact hy)⟩)
  have hQcard : Nat.card Q = 3 ^ 2 := by
    have hinjQ : Function.Injective (π.domRestrict Q) := by
      rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_domRestrict]
      apply Subgroup.eq_bot_of_card_eq
      have hmap : (π.ker.subgroupOf Q).map Q.subtype = Q ⊓ π.ker := by
        rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      have hbot : Q ⊓ π.ker = ⊥ := by
        refine le_bot_iff.mp ?_
        rw [← hFker]
        exact inf_le_inf hQF le_rfl
      rw [← Subgroup.card_map_of_injective (K := π.ker.subgroupOf Q) (f := Q.subtype)
        Q.subtype_injective, hmap, hbot]
      simp
    have h1 : Nat.card Q = Nat.card ↥(Q.map π) := by
      rw [← MonoidHom.domRestrict_range (K := Q) (f := π)]
      exact Nat.card_congr (MonoidHom.ofInjective (f := π.domRestrict Q) hinjQ).toEquiv
    rw [h1, hQmap, hQ₀card]
  have hrange : ∀ B : Subgroup (MulAut W), B ≤ π.range → IsElemAbelian 5 B →
      Nat.card B ≤ 5 ^ 2 := by
    intro B hBle hBel
    have hBN : B ≤ omegaNorm S := hBle.trans hπ
    have hBdvd : Nat.card B ∣ 5 ^ 2 := card_dvd_of_isPGroup_five S hK hBel.isPGroup hBN
    exact Nat.le_of_dvd (by norm_num) hBdvd
  have hL₁ : ∀ B : Subgroup (MulAut W), B ≤ S.factor 0 → IsElemAbelian 5 B →
      Nat.card B ≤ 5 := by
    intro B hBle hBel
    have hBdvd : Nat.card B ∣ 60 := by
      have h1 : Nat.card B ∣ Nat.card ↥(S.factor 0) := Subgroup.card_dvd_of_le hBle
      rw [card_factor S 0, hK] at h1
      norm_num at h1
      exact h1
    obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp hBel.isPGroup
    have hi1 : i ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ i := by omega
      have h25 : 5 ^ 2 ∣ 60 := (pow_dvd_pow 5 h2).trans (hi ▸ hBdvd)
      exact absurd h25 (by norm_num)
    calc Nat.card B = 5 ^ i := hi
      _ ≤ 5 ^ 1 := pow_le_pow_right' (by norm_num) hi1
      _ = 5 := by norm_num
  have hFL : F₅.map π ≤ S.factor 0 ⊔ S.factor 1 := by
    rw [← hΩ0]
    exact le_omega_of_isPGroup_five S hK hΩ (hF₅.map π).isPGroup
      ((Subgroup.map_le_range π F₅).trans hπ)
  have hAge : 5 ^ 2 ≤ Nat.card ↥(F₅ ⊓ (S.factor 1).comap π) :=
    card_inf_comap_ge_of_isElemAbelian_card_pow_three π (by norm_num) hF₅ hF₅card hker5
      hrange (factor_commute S (j := 0) (l := 1) (by decide)) (factor_inf_factor S) hL₁ hFL
  let A : Subgroup M := F₅ ⊓ (S.factor 1).comap π
  have hAle : A ≤ (S.factor 1).comap π := inf_le_right
  have hAel : IsElemAbelian 5 A := hF₅.mono inf_le_left
  have hAcard : 5 ^ 2 ≤ Nat.card A := hAge
  have hcyc : ∀ T : Subgroup M, T ≤ π.ker → IsPGroup 5 T → IsCyclic T := by
    intro T hTle hT5
    by_contra hnc
    obtain ⟨E₅, hE₅le, hE₅el, hE₅card⟩ :=
      CFSG.Quasithin.A1c.exists_isElemAbelian_card_sq (G := M) (p := 5) (by norm_num) hT5 hnc
    have hle : E₅ ≤ π.ker := hE₅le.trans hTle
    have h25 := hker5 E₅ hle hE₅el
    rw [hE₅card] at h25
    exact absurd h25 (by norm_num)
  have hQp : IsPGroup 3 Q := hF.isPGroup.to_le hQF
  have hQL : ∀ q ∈ Q, ∀ u ∈ S.factor 1, π q * u = u * π q := by
    intro q hq u hu
    exact hQ₀cent (π q) (Subgroup.mem_comap.mp hq.2) u hu
  obtain ⟨A', hA'L, hA'cent, hA'el, hA'card⟩ :=
    exists_isElemAbelian_le_centralizer_of_coprime_action π Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num) hQp hker3 hcyc hQL hAle hAel
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA'el.isPGroup
  have hk2' : 2 ≤ k := by
    have h1 : 5 ^ 2 ≤ 5 ^ k := by
      rw [← hk, hA'card]
      exact hAcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  exact ⟨Q, hQF, hQcard,
    le_trans hk2' (CFSG.SectionRank.le_pRank (by norm_num : 1 < 5) hA'cent hA'el hk)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
