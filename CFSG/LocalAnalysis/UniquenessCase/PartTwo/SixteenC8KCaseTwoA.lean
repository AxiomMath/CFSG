module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KE64
import CFSG.Adapters.StatedClassicalOrders
import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeElementLifting
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (Hbar9 img9 L9 Lbar9 IsSL2Cover Hyp91)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem c8k_opp_le (Y : Subgroup G) : Opp 3 Y ≤ Y :=
  (Subgroup.closure_le Y).mpr fun _ hz => hz.1

theorem c8k_opp_le_l9 {Y H : Subgroup G} (hYH : Y ≤ H) : Opp 3 Y ≤ L9 Y H := by
  intro x hx
  exact Subgroup.mem_iSup_of_mem (1 : ↥H) ⟨x, hx, by simp⟩

private theorem c8k_a_map_subgroupOf_inclusion {A Y H : Subgroup G} (hAY : A ≤ Y)
    (hYH : Y ≤ H) :
    (A.subgroupOf Y).map (Subgroup.inclusion hYH) = A.subgroupOf H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨(x : G), hAY hx⟩, hx, Subtype.ext rfl⟩

theorem c8k_shat_eq (D : Data G) {Y H : Subgroup G} (hY : Y = H ⊓ D.M) :
    Opp 3 (img9 H (H ⊓ D.M) ⊓ img9 H (L9 Y H)) = img9 H (Opp 3 Y) := by
  subst hY
  let π : ↥H →* Hbar9 H := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  have hYH : H ⊓ D.M ≤ H := inf_le_left
  apply le_antisymm
  ·
    change Subgroup.closure {x : Hbar9 H |
        x ∈ img9 H (H ⊓ D.M) ⊓ img9 H (L9 (H ⊓ D.M) H) ∧ ∃ k : ℕ, orderOf x = 3 ^ k} ≤
      img9 H (Opp 3 (H ⊓ D.M))
    rw [Subgroup.closure_le]
    rintro z ⟨hz, k, hk⟩
    have hzY : z ∈ ((H ⊓ D.M).subgroupOf H).map π := hz.1
    have hpow : (⟨z, hzY⟩ : ↥(((H ⊓ D.M).subgroupOf H).map π)) ^ (3 ^ k) = 1 := by
      apply Subtype.ext
      simpa using hk ▸ pow_orderOf_eq_one z
    obtain ⟨pre, hpre, i, hprepow⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.prime_power_element_lifts_surjective 3
        Nat.prime_three (π.subgroupMap ((H ⊓ D.M).subgroupOf H))
        (MonoidHom.subgroupMap_surjective π ((H ⊓ D.M).subgroupOf H)) ⟨z, hzY⟩ k hpow
    have hpreval : π (pre : ↥H) = z := by
      simpa using congrArg (fun x : ↥(((H ⊓ D.M).subgroupOf H).map π) => (x : Hbar9 H)) hpre
    have hprepow' : ((pre : ↥H) : G) ^ (3 ^ i) = 1 := by
      have := congrArg (fun x : ↥((H ⊓ D.M).subgroupOf H) => ((x : ↥H) : G)) hprepow
      simpa using this
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (orderOf_dvd_of_pow_eq_one hprepow')
    refine Subgroup.mem_map.mpr ⟨(pre : ↥H), ?_, hpreval⟩
    exact Subgroup.subset_closure ⟨pre.2, s, hs⟩
  ·
    intro z hz
    rw [img9] at hz
    rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
    have key : ∀ x : G, x ∈ Opp 3 (H ⊓ D.M) → ∀ hxH : x ∈ H,
        π ⟨x, hxH⟩ ∈ Opp 3 (img9 H (H ⊓ D.M) ⊓ img9 H (L9 (H ⊓ D.M) H)) := by
      intro x hx
      refine Subgroup.closure_induction (p := fun y _ => ∀ hyH : y ∈ H,
        π ⟨y, hyH⟩ ∈ Opp 3 (img9 H (H ⊓ D.M) ⊓ img9 H (L9 (H ⊓ D.M) H)))
        ?_ ?_ ?_ ?_ hx
      · rintro y ⟨hyY, j, hj⟩ hxH
        have hyOpp : y ∈ Opp 3 (H ⊓ D.M) := Subgroup.subset_closure ⟨hyY, j, hj⟩
        have hyl : y ∈ L9 (H ⊓ D.M) H := c8k_opp_le_l9 hYH hyOpp
        have hdvd : orderOf (π ⟨y, hxH⟩) ∣ 3 ^ j :=
          (orderOf_map_dvd π ⟨y, hxH⟩).trans (by simp [Subgroup.orderOf_mk, hj])
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
        refine Subgroup.subset_closure ⟨⟨?_, ?_⟩, i, hi⟩
        · exact Subgroup.mem_map.mpr ⟨⟨y, hxH⟩, hyY, rfl⟩
        · exact Subgroup.mem_map.mpr ⟨⟨y, hxH⟩, hyl, rfl⟩
      · intro hxH
        exact Subgroup.one_mem _
      · intro a b ha hb iha ihb hxH
        have haH : a ∈ H := hYH (c8k_opp_le (H ⊓ D.M) ha)
        have hbH : b ∈ H := hYH (c8k_opp_le (H ⊓ D.M) hb)
        have hmul : π ⟨a * b, hxH⟩ = π ⟨a, haH⟩ * π ⟨b, hbH⟩ := by
          rw [show (⟨a * b, hxH⟩ : ↥H) = ⟨a, haH⟩ * ⟨b, hbH⟩ from Subtype.ext rfl, map_mul]
        rw [hmul]
        exact Subgroup.mul_mem _ (iha haH) (ihb hbH)
      · intro a ha iha hxH
        have haH : a ∈ H := hYH (c8k_opp_le (H ⊓ D.M) ha)
        have hinv : π ⟨a⁻¹, hxH⟩ = (π ⟨a, haH⟩)⁻¹ := by
          rw [show (⟨a⁻¹, hxH⟩ : ↥H) = (⟨a, haH⟩)⁻¹ from Subtype.ext rfl, map_inv]
        rw [hinv]
        exact Subgroup.inv_mem _ (iha haH)
    exact key (w : G) hw w.2

private theorem c8k_a_card_sl2cover {Q : Type} [Group Q] {e : ℕ} (hS : IsSL2Cover Q 7 e) :
    Nat.card Q = 7 ^ e * (49 ^ e - 1) := by
  have hsc : CFSG.Open.StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 2 7 e :=
    hS.2.2.statedClassicalModel_of_ne_zero (by norm_num)
  have hcent : Nat.card Q = Nat.card (Q ⧸ Subgroup.center Q) * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hS.2.1]
  have hqodd : Odd (7 ^ e) := (show Odd 7 by norm_num).pow
  have h2 : 2 ∣ 7 ^ e - 1 := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  have h2sq : 2 ∣ (7 ^ e) ^ 2 - 1 :=
    dvd_trans (by norm_num : 2 ∣ 8) (Nat.eight_dvd_sq_sub_one_of_odd hqodd)
  have hquot : Nat.card (Q ⧸ Subgroup.center Q) = 7 ^ e * ((7 ^ e) ^ 2 - 1) / 2 := by
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hsc,
      Nat.gcd_eq_left h2]
    simp
  rw [hcent, hquot, Nat.div_mul_cancel (dvd_mul_of_dvd_right h2sq (7 ^ e))]
  have h49 : (7 ^ e) ^ 2 = 49 ^ e := by
    rw [show (49 : ℕ) = 7 ^ 2 by norm_num]
    conv_lhs => rw [← pow_mul]
    conv_rhs => rw [← pow_mul]
    rw [mul_comm e 2]
  rw [h49]

private theorem c8k_a_three_dvd_card_sl2cover {Q : Type} [Group Q] {e : ℕ}
    (hS : IsSL2Cover Q 7 e) : 3 ∣ Nat.card Q := by
  rw [c8k_a_card_sl2cover hS]
  exact dvd_mul_of_dvd_right
    (dvd_trans (by norm_num : 3 ∣ 48) (Nat.sub_one_dvd_pow_sub_one 49 e)) _

theorem c8k_cover_e_eq_one {Y H C : Subgroup G} (hYH : Y ≤ H) (hCY : C ≤ Y)
    (hC3 : ¬ 3 ∣ Nat.card C) (hP : C8P0 Y C) {e : ℕ} (he : 1 ≤ e)
    (hS : IsSL2Cover ↥(img9 H (Opp 3 Y)) 7 e) : e = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, instP, φ, hφs, hφk, hE64, -⟩ := hP
  letI : Group P := instP
  haveI : Finite P := Finite.of_surjective φ hφs
  obtain ⟨N, hNn, hN64, hL3⟩ := hE64
  haveI : N.Normal := hNn
  have hPcard : Nat.card P = 10752 := c8_e64_card hN64 hL3
  let π : ↥H →* Hbar9 H := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  let ψ : ↥Y →* Hbar9 H := π.comp (Subgroup.inclusion hYH)
  let X' : Subgroup ↥Y := (Opp 3 Y).subgroupOf Y
  let J : Subgroup ↥Y := ψ.ker
  let JC : Subgroup ↥Y := J ⊔ φ.ker
  let Z₀ : Subgroup (Hbar9 H) := (X' ⊓ JC).map ψ
  let Q : Subgroup (Hbar9 H) := img9 H (Opp 3 Y)
  have hX'map : X'.map ψ = Q := by
    change X'.map (π.comp (Subgroup.inclusion hYH)) = Q
    rw [← Subgroup.map_map (K := X') π (Subgroup.inclusion hYH),
      c8k_a_map_subgroupOf_inclusion (c8k_opp_le Y) hYH]
    rfl
  have hJle : J.map (Subgroup.inclusion hYH) ≤ CFSG.pPrimeCore 3 ↥H := by
    have hJ : J = (CFSG.pPrimeCore 3 ↥H).comap (Subgroup.inclusion hYH) := by
      change (π.comp (Subgroup.inclusion hYH)).ker = _
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [hJ]
    exact Subgroup.map_comap_le (Subgroup.inclusion hYH) (CFSG.pPrimeCore 3 ↥H)
  have hJcop : Nat.Coprime 3 (Nat.card J) := by
    have hcopH : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 ↥H)) :=
      CFSG.pPrimeCore_coprime_card
    have hdvd : Nat.card J ∣ Nat.card (CFSG.pPrimeCore 3 ↥H) := by
      rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hYH)]
      exact Subgroup.card_dvd_of_le hJle
    exact hcopH.coprime_dvd_right hdvd
  have hCKcop : Nat.Coprime 3 (Nat.card φ.ker) := by
    rw [hφk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCY).toEquiv]
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr hC3
  haveI hJnorm : J.Normal := MonoidHom.normal_ker ψ
  haveI hCKnorm : (φ.ker).Normal := MonoidHom.normal_ker φ
  haveI hJCnorm : JC.Normal := by
    change (J ⊔ φ.ker).Normal
    infer_instance
  have hJCle : JC ≤ CFSG.pPrimeCore 3 ↥Y := by
    change J ⊔ φ.ker ≤ _
    exact sup_le (le_sSup ⟨hJnorm, hJcop⟩) (le_sSup ⟨hCKnorm, hCKcop⟩)
  have h3JC : ¬ 3 ∣ Nat.card JC := by
    have hdvd : Nat.card JC ∣ Nat.card (CFSG.pPrimeCore 3 ↥Y) :=
      Subgroup.card_dvd_of_le hJCle
    exact (Nat.prime_three.coprime_iff_not_dvd).mp
      (CFSG.pPrimeCore_coprime_card.coprime_dvd_right hdvd)
  have h3Z₀ : ¬ 3 ∣ Nat.card Z₀ := by
    have hdvd₁ : Nat.card Z₀ ∣ Nat.card (X' ⊓ JC : Subgroup ↥Y) := by
      change Nat.card ((X' ⊓ JC).map ψ) ∣ Nat.card (X' ⊓ JC : Subgroup ↥Y)
      exact Subgroup.card_map_dvd (X' ⊓ JC) ψ
    have hdvd₂ : Nat.card (X' ⊓ JC : Subgroup ↥Y) ∣ Nat.card JC :=
      Subgroup.card_dvd_of_le inf_le_right
    exact fun h => h3JC (h.trans (hdvd₁.trans hdvd₂))
  have hZQ : Z₀ ≤ Q := by
    change (X' ⊓ JC).map ψ ≤ Q
    rw [← hX'map]
    exact Subgroup.map_mono inf_le_left
  haveI hZQnorm : (Z₀.subgroupOf Q).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hZQ]
    rintro h k hh hk
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp (show k ∈ X'.map ψ from by rwa [hX'map])
    refine Subgroup.mem_map.mpr ⟨b * a * b⁻¹, ⟨?_, ?_⟩, by simp [map_mul]⟩
    · exact X'.mul_mem (X'.mul_mem hb ha.1) (X'.inv_mem hb)
    · exact hJCnorm.conj_mem a ha.2 b
  have hZle : Nat.card Z₀ ≤ 2 := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hS.1 hZQnorm with htop | hcenter
    · exfalso
      have hcard : Nat.card Z₀ = Nat.card ↥Q := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv, htop,
          Subgroup.card_top]
      exact h3Z₀ (hcard.symm ▸ c8k_a_three_dvd_card_sl2cover hS)
    · have hle : Nat.card (Z₀.subgroupOf Q) ≤ Nat.card (Subgroup.center ↥Q) :=
        Subgroup.card_le_of_le hcenter
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv, hS.2.1] at hle
      exact hle
  have hZker : (X' ⊓ JC) ⊓ ψ.ker = X' ⊓ J := by
    change (X' ⊓ JC) ⊓ J = X' ⊓ J
    rw [inf_assoc, show JC ⊓ J = J from inf_eq_right.mpr le_sup_left]
  have hZrel : Nat.card Z₀ = (X' ⊓ J).relIndex (X' ⊓ JC) := by
    rw [show Z₀ = (X' ⊓ JC).map ψ from rfl,
      ← Subgroup.relIndex_ker (X' ⊓ JC) ψ, ← hZker,
      Subgroup.inf_relIndex_left (H := X' ⊓ JC) (K := J)]
  have hQrel : Nat.card Q = (X' ⊓ J).relIndex X' := by
    rw [show Q = X'.map ψ from hX'map.symm, ← Subgroup.relIndex_ker X' ψ,
      Subgroup.inf_relIndex_left (H := X') (K := J)]
  have hQeq : Nat.card Q = Nat.card Z₀ * (X' ⊓ JC).relIndex X' := by
    rw [hQrel, hZrel]
    exact (Subgroup.relIndex_mul_relIndex (X' ⊓ J) (X' ⊓ JC) X'
      (inf_le_inf_left X' le_sup_left) inf_le_left).symm
  have h5 : (X' ⊓ JC).relIndex X' = JC.relIndex (X' ⊔ JC) := by
    rw [Subgroup.inf_relIndex_left (H := X') (K := JC),
      Subgroup.relIndex_sup_right (H := X') (K := JC)]
  have hidx : (φ.ker).index = Nat.card P := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top]
  have h6 : JC.relIndex (X' ⊔ JC) ∣ Nat.card P := by
    rw [← hidx]
    exact (Subgroup.relIndex_dvd_index_of_normal (H := JC) (K := X' ⊔ JC)).trans
      (Subgroup.index_dvd_of_le (le_sup_right : φ.ker ≤ JC))
  have h6le : JC.relIndex (X' ⊔ JC) ≤ 10752 := by
    rw [hPcard] at h6
    exact Nat.le_of_dvd (by norm_num) h6
  have hQle : Nat.card Q ≤ 2 * 10752 := by
    rw [hQeq, h5]
    exact Nat.mul_le_mul hZle h6le
  have hQcard : Nat.card Q = 7 ^ e * (49 ^ e - 1) := c8k_a_card_sl2cover hS
  rw [hQcard] at hQle
  rcases eq_or_lt_of_le he with h | h
  · exact h.symm
  · exfalso
    have he2 : 2 ≤ e := by omega
    have h7 : 49 ≤ 7 ^ e := by
      calc 49 = 7 ^ 2 := by norm_num
        _ ≤ 7 ^ e := Nat.pow_le_pow_right (by norm_num) he2
    have h49 : 2400 ≤ 49 ^ e - 1 := by
      have hpow : 49 ^ 2 ≤ 49 ^ e := Nat.pow_le_pow_right (by norm_num) he2
      norm_num at hpow ⊢
      omega
    have hge : 117600 ≤ 7 ^ e * (49 ^ e - 1) := by
      have := Nat.mul_le_mul h7 h49
      norm_num at this
      exact this
    norm_num at hQle
    omega

theorem c8k_dorder_pprime {Γ : Type} [Group Γ] [Finite Γ] {d : Γ} (hd : orderOf d = 3) :
    orderOf (d : Γ ⧸ CFSG.pPrimeCore 3 Γ) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : orderOf (d : Γ ⧸ CFSG.pPrimeCore 3 Γ) ∣ 3 := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore 3 Γ)) d
    rw [hd] at h
    simpa using h
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · exfalso
    have hq : (d : Γ ⧸ CFSG.pPrimeCore 3 Γ) = 1 := orderOf_eq_one_iff.mp h1
    have hmem : d ∈ CFSG.pPrimeCore 3 Γ :=
      (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 Γ) d).mp hq
    have h3dvd : 3 ∣ Nat.card (CFSG.pPrimeCore 3 Γ) := by
      have h := Subgroup.orderOf_dvd_natCard (CFSG.pPrimeCore 3 Γ) hmem
      rwa [hd] at h
    exact (Nat.prime_three.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card h3dvd
  · exact h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
