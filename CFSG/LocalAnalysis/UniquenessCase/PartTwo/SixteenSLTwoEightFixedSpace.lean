module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3AA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.Vol2 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22
open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem s16gNatHom_eq_matHom :
    (s16gNatHom ι K : GL ι K →* MulAut (StdMod ι K)) = matHom := by
  ext g x
  rfl

theorem s16gNorm_eq_natNorm (Γ : Subgroup (GL ι K)) : s16gNorm Γ = natNorm Γ := by
  unfold s16gNorm natNorm
  rw [natImage_eq_map, s16gNatHom_eq_matHom]

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_mem_natImage_of_linSub_of_pow_eq_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {g : MulAut (StdMod (Fin 2) K)} (hg : g ∈ linSub)
    {p : ℕ} (hp : p.Prime) (hp7 : p ≠ 7) (hgp : g ^ p = 1) :
    g ∈ natImage (StatedSL 2 K) := by
  obtain ⟨B, hB⟩ := exists_matAut_of_mem_linSub hg
  have hBp : B ^ p = 1 := by
    apply matHom_injective
    rw [map_pow]
    rw [show matHom B = g from hB.symm, hgp, map_one]
  have hdet : B ∈ StatedSL 2 K := by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    have hdetpow : (Matrix.GeneralLinearGroup.det B) ^ p = 1 := by
      rw [← map_pow, hBp, map_one]
    have hcard : Nat.card Kˣ = 7 := by
      rw [Nat.card_units, hK]
    have hcop : Nat.Coprime p (Nat.card Kˣ) := by
      rw [hcard]
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (by
        intro hdvd
        exact hp7 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp hdvd))
    have hdetunit : Matrix.GeneralLinearGroup.det B = 1 :=
      (pow_eq_one_iff_of_coprime hcop).mp ⟨hdetpow, pow_card_eq_one'⟩
    have := congrArg Units.val hdetunit
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  rw [natImage_eq_map]
  exact Subgroup.mem_map.mpr ⟨B, hdet, hB.symm⟩

private theorem s168e3_fieldHom_eq_one_of_prime_ne_three {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {A : Type} [Group A] (ψ : A →* (K ≃+* K))
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {a : A} (ha : a ^ p = 1) : ψ a = 1 := by
  have hAut3 : Nat.card (K ≃+* K) = 3 := s16g_card_ringAut_eight hK
  have h1 : (ψ a) ^ p = 1 := by rw [← map_pow, ha, map_one]
  have hcop : Nat.Coprime p (Nat.card (K ≃+* K)) := by
    rw [hAut3]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (by
      intro hdvd
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd))
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨h1, pow_card_eq_one'⟩

private theorem s168e3_seven_mem_and_fixV_eq_bot_of_sl2_eight_realization
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [fieldK : Field K] [finiteK : Finite K]
    (hK8 : Nat.card K = 8)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) :
    7 ∈ D.sig ∧ fixV (lBar V₀ V hV L) = ⊥ := by
  classical
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let Γ : Subgroup (GL (Fin 2) K) := StatedSL 2 K
  have hHA : H ≤ A := by
    show lBar V₀ V hV L ≤ Mbar D.M V₀ V hV
    simpa only [lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hAn : A ≤ Subgroup.normalizer (H : Set (MulAut W)) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (lBar_conj_eq_of_s15_eq_one hs hg)
  have hcomm : commSub ⊤ H = ⊤ := by
    show commSub ⊤ (lBar V₀ V hV L) = ⊤
    simpa only [wTil, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hrealTop := s16g_realizes_top c.conc hs Γ hreal
  obtain ⟨π, hπ⟩ := hrealTop
  obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat Γ) hπ
  obtain ⟨ρ, hρinj, hρcoord, _hρcomp, hρmap, hρnorm⟩ :=
    exists_faithful_nat_hom_of_isCoord (W := W) (Γ := Γ) (A := A) (H := H)
      (π := π) (f := f) hHA hAn hf hcomm
  have hNormEq : s16gNorm Γ = natNorm Γ := s16gNorm_eq_natNorm Γ
  let ρN : A →* ↥(natNorm Γ) :=
    ρ.codRestrict (natNorm Γ) (fun a => by
      rw [← hNormEq]
      exact hρnorm a)
  have hΓ : HasScalarCommutant Γ :=
    hasScalarCommutant_statedSL (d := 2) (by norm_num)
  let ψ : A →* (K ≃+* K) := (fieldHom hΓ).comp ρN
  have hψ_iff : ∀ a : A, ψ a = 1 ↔ ρ a ∈ linSub := by
    intro a
    show fieldHom hΓ (ρN a) = 1 ↔ ρ a ∈ linSub
    rw [fieldHom_eq_one_iff]
    rfl
  have hψ_involution : ∀ a : A, a ^ 2 = 1 → ψ a = 1 := by
    intro a ha2
    exact s168e3_fieldHom_eq_one_of_prime_ne_three hK8 ψ Nat.prime_two (by norm_num) ha2
  have hψ_sig : ∀ (p : ℕ), p ∈ D.sig → p ≠ 7 → ∀ a : A, a ^ p = 1 → ψ a = 1 := by
    intro p hpσ hp7 a hap
    have hp : p.Prime := (D.sig_prime p hpσ).1
    by_cases hp3 : p = 3
    · have h3mem : 3 ∈ D.sig := hp3 ▸ hpσ
      have hAut3 : Nat.card (K ≃+* K) = 3 := s16g_card_ringAut_eight hK8
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card ψ.range
        (hp := ⟨by rw [hAut3]; exact Nat.prime_three⟩) with hbot | htop
      · have hmem : ψ a ∈ ψ.range := ⟨a, rfl⟩
        rw [hbot] at hmem
        simpa using hmem
      · exfalso
        have hidx : ψ.ker.index = 3 := by
          rw [Subgroup.index_ker, htop, Subgroup.card_top, hAut3]
        exact s16e_mbar_index_ne_three D c.std.h638 h3mem c.setting.hyp16 hV ψ.ker hidx
    · exact s168e3_fieldHom_eq_one_of_prime_ne_three hK8 ψ hp hp3 hap
  have h7mem : 7 ∈ D.sig := by
    obtain ⟨p, hpσ⟩ := c.std.hx.sig_nonempty
    by_contra hp7
    have hp : p.Prime := (D.sig_prime p hpσ).1
    have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
    have hpne7 : p ≠ 7 := by
      intro hp_eq
      exact hp7 (hp_eq ▸ hpσ)
    have h2le : 2 ≤ CFSG.Open.pRank p A := by
      simpa only [A] using c.two_le_pRank_mbar hpσ
    obtain ⟨E, hEA, hEab, hEcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (G := MulAut W)
        (p := p) (hp := ⟨hp⟩) (H := A) (k := 2) h2le
    have hEH : E ≤ H := by
      intro e he
      let a : A := ⟨e, hEA he⟩
      have hap : a ^ p = 1 := Subtype.ext (hEab.2 e he)
      have hψ : ψ a = 1 := hψ_sig p hpσ hpne7 a hap
      have hlin : ρ a ∈ linSub := (hψ_iff a).mp hψ
      have hρap : (ρ a) ^ p = 1 := by rw [← map_pow, hap, map_one]
      have hmem : ρ a ∈ natImage Γ :=
        s168e3_mem_natImage_of_linSub_of_pow_eq_one hK8 hlin hp hpne7 hρap
      have hmem' : ρ a ∈ Γ.map matHom := by
        simpa [Γ, natImage_eq_map] using hmem
      have hmap' : (H.subgroupOf A).map ρ = Γ.map matHom := by
        rw [hρmap, s16gNatHom_eq_matHom]
      have hmemmap : ρ a ∈ (H.subgroupOf A).map ρ := by
        rw [hmap']
        exact hmem'
      have haH : a ∈ H.subgroupOf A := (Subgroup.mem_map_iff_mem hρinj).mp hmemmap
      exact Subgroup.mem_subgroupOf.mp haH
    have h2leH : 2 ≤ CFSG.Open.pRank p H :=
      CFSG.SectionRank.le_pRank hp.one_lt hEH hEab (by simpa using hEcard)
    have hthinp : CFSG.Open.pRank p H ≤ 1 := by
      simpa only [H] using hthin p hp hp2
    omega
  have hm : MBarGT D.M V₀ V 2 := by
    have hex : ∃ τ ∈ Mbar D.M V₀ V hV, τ ^ 2 = 1 ∧ τ ≠ 1 := by
      obtain ⟨t, htA, ht2, ht1, -, -⟩ := c.conc
      exact ⟨t, htA, ht2, ht1⟩
    refine s16h_e3_mbar_of_rank D c.setting.hyp16.hyp125 (n := 2) ?_ hex
    intro τ hτA hτ2 hτ1
    let a : A := ⟨τ, hτA⟩
    have ha2 : a ^ 2 = 1 := Subtype.ext hτ2
    have hψ : ψ a = 1 := hψ_involution a ha2
    have hlin : ρ a ∈ linSub := (hψ_iff a).mp hψ
    have hsem : IsSemilinear (ρ a) (RingEquiv.refl K) := mem_linSub.mp hlin
    have hρa1 : ρ a ≠ 1 := by
      intro h
      apply hτ1
      have ha1 : a = 1 := hρinj (by rw [h, map_one])
      exact congrArg Subtype.val ha1
    have h3le : 3 ≤ rkIdx (fixV (Subgroup.zpowers (ρ a))) :=
      le_rkIdx_fixV_of_linear (n := 3) hK8 hsem hρa1
    have h3le' : 3 ≤ rk (commSub ⊤ (Subgroup.zpowers (ρ a))) := by
      rw [← commV_eq_commSub (Subgroup.zpowers (ρ a)), ← rkIdx_fixV_zpowers (ρ a)]
      exact h3le
    let β : W →* Multiplicative (Fin 2 → K) := hf.toHom
    have hβs : Function.Surjective β := by
      intro y
      obtain ⟨w, hw⟩ := hf.surj (Multiplicative.toAdd y)
      exact ⟨w, by
        show Multiplicative.ofAdd (f w) = y
        rw [hw]
        rfl⟩
    have hcommτ := s16_Mod_commSub_zpowers_map β hβs (t := τ) (t' := ρ a)
      (fun w => (hρcoord a w).symm)
    have hcarddvd : Nat.card ↥((commSub ⊤ (Subgroup.zpowers τ)).map β) ∣
        Nat.card ↥(commSub ⊤ (Subgroup.zpowers τ)) :=
      Subgroup.card_map_dvd _ _
    have hrkle : rk ↥((commSub ⊤ (Subgroup.zpowers τ)).map β) ≤
        rk ↥(commSub ⊤ (Subgroup.zpowers τ)) :=
      padicValNat_two_le_of_dvd Nat.card_pos.ne' hcarddvd
    have himg : rk ↥(commSub ⊤ (Subgroup.zpowers (ρ a))) =
        rk ↥((commSub ⊤ (Subgroup.zpowers τ)).map β) := by
      rw [hcommτ]
    have h3orig : 3 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers τ)) := by
      calc 3 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers (ρ a))) := h3le'
        _ = rk ↥((commSub ⊤ (Subgroup.zpowers τ)).map β) := himg
        _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers τ)) := hrkle
    have hcard : Nat.card ↥(commSub ⊤ (Subgroup.zpowers τ)) =
        2 ^ rk ↥(commSub ⊤ (Subgroup.zpowers τ)) :=
      card_eq_two_pow (s15_Infra_vtil_sq_eq_one V₀ V hV) _
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) h3orig
  exact ⟨h7mem, fixV_lBar_eq_bot_of_field_eight_at_three c hs hK8 (Or.inl hreal) h7mem hm⟩

theorem s168e3_seven_mem_and_fixV_eq_bot_of_sl2_eight_of_s_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (_hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) :
    7 ∈ D.sig ∧ fixV (lBar V₀ V hV L) = ⊥ := by
  obtain ⟨_hSL, K, hKf, hKfin, hKcard, hreal⟩ := hrow
  have hK8 : Nat.card K = 8 := by
    rw [hKcard]
    norm_num
  exact s168e3_seven_mem_and_fixV_eq_bot_of_sl2_eight_realization
    (K := K) (fieldK := hKf) (finiteK := hKfin) c hthin hs hK8 hreal

theorem s168e3_fixV_eq_bot_of_sl2_eight_of_s_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (_hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3) :
    fixV (lBar V₀ V hV L) = ⊥ :=
  (s168e3_seven_mem_and_fixV_eq_bot_of_sl2_eight_of_s_eq_one
    c _hcomp hthin hs hrow).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
