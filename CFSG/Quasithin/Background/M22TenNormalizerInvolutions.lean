module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenM22QuotientModule
public import CFSG.Quasithin.AppendixH.H14.MathieuStabilizerClasses

public section

namespace CFSG.Quasithin.M22TenNormalizer

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.AppendixH.H14

variable {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {t : MulAut W}

section Certs

private theorem mQuot_bounds
    (hW : ∀ w : W, w ^ 2 = 1) (hH : IsSpor ↥H .M22)
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (hdim : E3.mQuot (⊤ : Subgroup W) (fixV H) = 10)
    (htN : t ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    (3 ≤ E3.mQuot (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) (fixV H)) ∧
      ((∃ h0 ∈ H, ∀ h ∈ H, t * h * t⁻¹ = h0 * h * h0⁻¹) →
        E3.mQuot (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) (fixV H) = 4) ∧
      (rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3 →
        E3.mQuot (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) (fixV H) = 3 ∧
          ¬ ∃ h0 ∈ H, ∀ h ∈ H, t * h * t⁻¹ = h0 * h * h0⁻¹) := by
  classical
  have hq : CFSG.Open.IsQuasisimple ↥H := isQuasisimple_of_isSpor_m22 hH
  obtain ⟨Q, hQc, hQf, q0, ρ, hqsurj, hqker, hρinj, heq, hexp, hcardQ, hirrQ⟩ :=
    s16k_qm_quotMap (W := W) (H := H) hq hcomm hW
  have htZ : t ∈ stabSub (fixV H) :=
    (FixVLat.le_stabSub_fixV_of_le_normalizer
      (X := Subgroup.zpowers t) (K := H) (Subgroup.zpowers_le.mpr htN))
      (Subgroup.mem_zpowers t)
  have hφ : ∀ w : W, q0 w = 1 ↔ q0 (t w) = 1 := by
    intro w
    rw [hqker w, hqker (t w)]
    exact ((mem_stabSub).mp htZ w).symm
  obtain ⟨ψ, hψ⟩ := s16g_exists_induced_aut q0 hqsurj (φ := t) hφ
  have ht2' : t * t = 1 := by simpa [pow_two] using ht2
  have hψ2 : orderOf ψ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · ext v
      obtain ⟨w, rfl⟩ := hqsurj v
      rw [pow_two, MulAut.mul_apply, hψ, hψ]
      have ht2w : t (t w) = w := by
        have h1 : (t * t) w = (1 : MulAut W) w := by rw [ht2']
        simpa [MulAut.mul_apply] using h1
      rw [ht2w]
      rfl
    · intro hψ1
      exact ht1 (by
        have hcent : t ∈ Subgroup.centralizer (H : Set (MulAut W)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          have hmem : t * h * t⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp htN h).mp hh
          have hconj : ψ * ρ ⟨h, hh⟩ * ψ⁻¹ = ρ ⟨t * h * t⁻¹, hmem⟩ := by
            ext v
            obtain ⟨w, rfl⟩ := hqsurj v
            have hψinv : ψ⁻¹ (q0 w) = q0 (t⁻¹ w) := by
              apply ψ.injective
              rw [hψ]
              simp
            calc (ψ * ρ ⟨h, hh⟩ * ψ⁻¹) (q0 w)
                = ψ (ρ ⟨h, hh⟩ (q0 (t⁻¹ w))) := by
                  rw [MulAut.mul_apply, MulAut.mul_apply, hψinv]
              _ = ψ (q0 (((⟨h, hh⟩ : ↥H) : MulAut W) (t⁻¹ w))) := by rw [heq]
              _ = q0 (t (((⟨h, hh⟩ : ↥H) : MulAut W) (t⁻¹ w))) := hψ _
              _ = q0 ((t * h * t⁻¹) w) := by simp [MulAut.mul_apply]
              _ = ρ ⟨t * h * t⁻¹, hmem⟩ (q0 w) := heq ⟨t * h * t⁻¹, hmem⟩ w
          have hρeq : ρ ⟨h, hh⟩ = ρ ⟨t * h * t⁻¹, hmem⟩ := by
            rw [← hconj, hψ1]
            simp
          have hh' : h = t * h * t⁻¹ := congrArg Subtype.val (hρinj hρeq)
          calc h * t = (t * h * t⁻¹) * t := congrArg (fun x => x * t) hh'
            _ = t * h := by group
        have hcent_bot : Subgroup.centralizer (H : Set (MulAut W)) = ⊥ :=
          centralizer_eq_bot_of_m22_quotient_rank_ten hW hH hcomm hirr hdim
        rw [hcent_bot] at hcent
        exact Subgroup.mem_bot.mp hcent)
  have hspor : IsSpor ↥ρ.range .M22 := by
    obtain ⟨e⟩ := hH
    exact ⟨(MonoidHom.ofInjective hρinj).symm.trans e⟩
  have hclass : MathieuCode22 ρ.range ⊤ ⊥ ∨ MathieuCocode22 ρ.range ⊤ ⊥ := by
    refine mathieuSmallIrr22_holds (W := Q) (by intro w; rw [← sq]; exact hexp w) ρ.range
      hspor ?_ ?_
    · intro B hB
      exact hirrQ hirr B fun l b hb =>
        hB (ρ l) (MonoidHom.mem_range.mpr ⟨l, rfl⟩) b hb
    · rw [hcardQ, hdim]
      norm_num
  have hA_image : (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)).map q0 =
      commSub (⊤ : Subgroup Q) (Subgroup.zpowers ψ) := by
    have hcomp : q0.comp (commHom t) = (commHom ψ).comp q0 := by
      ext w
      simp only [MonoidHom.comp_apply, commHom_apply, map_mul, map_inv]
      rw [hψ]
    calc (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)).map q0
        = (commV (Subgroup.zpowers t)).map q0 := by rw [commV_eq_commSub]
      _ = ((⊤ : Subgroup W).map (commHom t)).map q0 := by rw [commV_zpowers_eq_map]
      _ = (⊤ : Subgroup W).map (q0.comp (commHom t)) := by rw [Subgroup.map_map]
      _ = (⊤ : Subgroup W).map ((commHom ψ).comp q0) := by rw [hcomp]
      _ = ((⊤ : Subgroup W).map q0).map (commHom ψ) := by rw [← Subgroup.map_map]
      _ = (⊤ : Subgroup Q).map (commHom ψ) := by
        rw [Subgroup.map_top_of_surjective _ hqsurj]
      _ = commV (Subgroup.zpowers ψ) := by rw [commV_zpowers_eq_map]
      _ = commSub (⊤ : Subgroup Q) (Subgroup.zpowers ψ) := by rw [commV_eq_commSub]
  have hZ_image : (fixV H).map q0 = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨z, hz, rfl⟩
    rw [Subgroup.mem_bot]
    exact (hqker z).mpr hz
  have hK_image : ((commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H)).map q0 =
      commSub (⊤ : Subgroup Q) (Subgroup.zpowers ψ) := by
    rw [Subgroup.map_sup, hZ_image, hA_image, sup_bot_eq]
  have hq_eq : E3.mQuot (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) (fixV H) =
      rkIdx (fixV (Subgroup.zpowers ψ)) := by
    have hcard_image : Nat.card ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) =
        Nat.card ↥(commSub (⊤ : Subgroup Q) (Subgroup.zpowers ψ)) * Nat.card ↥(fixV H) := by
      have h1 := B1More.card_map_mul_card_inf_ker
        (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) q0
      rw [hK_image] at h1
      have h2 : (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) ⊓ q0.ker = fixV H := by
        ext x
        constructor
        · rintro ⟨-, hx⟩
          exact (hqker x).mp hx
        · intro hx
          exact ⟨Subgroup.mem_sup_right hx, (hqker x).mpr hx⟩
      rw [h2] at h1
      exact h1.symm
    have hrel : (fixV H).relIndex
        (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) =
        Nat.card ↥(commSub (⊤ : Subgroup Q) (Subgroup.zpowers ψ)) := by
      have h1 := Subgroup.relIndex_mul_card
        (H := fixV H) (K := commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H)
      rw [inf_eq_left.mpr (le_sup_right : fixV H ≤
        commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H)] at h1
      have h2 : (fixV H).relIndex
          (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) * Nat.card ↥(fixV H) =
          Nat.card ↥(commSub (⊤ : Subgroup Q) (Subgroup.zpowers ψ)) * Nat.card ↥(fixV H) := by
        rw [← hcard_image]
        exact h1
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
    unfold E3.mQuot
    rw [hrel]
    change rk ↥(commSub (⊤ : Subgroup Q) (Subgroup.zpowers ψ)) =
      rkIdx (fixV (Subgroup.zpowers ψ))
    rw [← commV_eq_commSub, ← rkIdx_fixV_zpowers (V := Q) ψ]
  have hψconj : ∀ h : ↥H, ψ * ρ h * ψ⁻¹ =
      ρ ⟨t * (h : MulAut W) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN h).mp h.2⟩ := by
    intro h
    ext v
    obtain ⟨w, rfl⟩ := hqsurj v
    have hψinv : ψ⁻¹ (q0 w) = q0 (t⁻¹ w) := by
      apply ψ.injective
      rw [hψ]
      simp
    calc (ψ * ρ h * ψ⁻¹) (q0 w)
        = ψ (ρ h (q0 (t⁻¹ w))) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, hψinv]
      _ = ψ (q0 ((h : MulAut W) (t⁻¹ w))) := by rw [heq]
      _ = q0 (t ((h : MulAut W) (t⁻¹ w))) := hψ _
      _ = q0 ((t * (h : MulAut W) * t⁻¹) w) := by simp [MulAut.mul_apply]
      _ = ρ ⟨t * (h : MulAut W) * t⁻¹,
            (Subgroup.mem_normalizer_iff.mp htN h).mp h.2⟩ (q0 w) :=
          heq ⟨t * (h : MulAut W) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN h).mp h.2⟩ w
  have htNinv : t⁻¹ ∈ Subgroup.normalizer (H : Set (MulAut W)) :=
    (Subgroup.normalizer (H : Set (MulAut W))).inv_mem htN
  have hψinv_conj : ∀ h : ↥H, ψ⁻¹ * ρ h * ψ =
      ρ ⟨t⁻¹ * (h : MulAut W) * t,
        (Subgroup.mem_normalizer_iff.mp htNinv h).mp h.2⟩ := by
    intro h
    ext v
    obtain ⟨w, rfl⟩ := hqsurj v
    have hψinv' : ψ⁻¹ (q0 ((h : MulAut W) (t w))) =
        q0 (t⁻¹ ((h : MulAut W) (t w))) := by
      apply ψ.injective
      rw [hψ]
      simp
    calc (ψ⁻¹ * ρ h * ψ) (q0 w)
        = ψ⁻¹ (ρ h (q0 (t w))) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, hψ]
      _ = ψ⁻¹ (q0 ((h : MulAut W) (t w))) := by rw [heq]
      _ = q0 (t⁻¹ ((h : MulAut W) (t w))) := hψinv'
      _ = q0 ((t⁻¹ * (h : MulAut W) * t) w) := by simp [MulAut.mul_apply]
      _ = ρ ⟨t⁻¹ * (h : MulAut W) * t,
            (Subgroup.mem_normalizer_iff.mp htNinv h).mp h.2⟩ (q0 w) :=
          heq ⟨t⁻¹ * (h : MulAut W) * t, (Subgroup.mem_normalizer_iff.mp htNinv h).mp h.2⟩ w
  have hψN : ψ ∈ Subgroup.normalizer (ρ.range : Set (MulAut Q)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨h, rfl⟩ := hx
      exact ⟨⟨t * (h : MulAut W) * t⁻¹,
        (Subgroup.mem_normalizer_iff.mp htN h).mp h.2⟩, (hψconj h).symm⟩
    · intro hx
      obtain ⟨h, hh⟩ := hx
      have hx' : x = ψ⁻¹ * ρ h * ψ := by
        calc x = ψ⁻¹ * (ψ * x * ψ⁻¹) * ψ := by group
          _ = ψ⁻¹ * ρ h * ψ := by rw [← hh]
      rw [hx']
      exact ⟨⟨t⁻¹ * (h : MulAut W) * t,
        (Subgroup.mem_normalizer_iff.mp htNinv h).mp h.2⟩, (hψinv_conj h).symm⟩
  have h3 : 3 ≤ rkIdx (fixV (Subgroup.zpowers ψ)) := by
    let M : Subgroup (MulAut Q) := ρ.range ⊔ Subgroup.zpowers ψ
    have hLM : IsOver ρ.range M := by
      refine ⟨le_sup_left, sup_le ?_ ?_⟩
      · exact Subgroup.le_normalizer
      · rw [Subgroup.zpowers_le]
        exact hψN
    have hψM : ψ ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers ψ)
    rcases hclass with hcode | hcocode
    · exact code22_three_le_rkIdx hLM hcode hψM hψ2
    · exact cocode22_three_le_rkIdx hLM hcocode hψM hψ2
  have hfour_range : ∀ u : ↥ρ.range, orderOf u = 2 →
      rkIdx (fixV (Subgroup.zpowers (u : MulAut Q))) = 4 := by
    obtain ⟨t0, ht0mem, ht02, ht0rank⟩ : ∃ u ∈ ρ.range, orderOf u = 2 ∧
        rkIdx (fixV (Subgroup.zpowers u)) = 4 := by
      rcases hclass with hcode | hcocode
      · obtain ⟨e, he⟩ := code22_std hcode
        have hψinj : Function.Injective (rhoC10 mog22 mog22_le_mog22plus) := by
          intro a b hab
          have h := rhoC10_mog22plus_injective (a₁ := ⟨a, mog22_le_mog22plus a.2⟩)
            (a₂ := ⟨b, mog22_le_mog22plus b.2⟩) hab
          exact Subtype.ext
            (congrArg (fun x : ↥mog22plus => (x : Equiv.Perm (Fin 24))) h)
        obtain ⟨u, huL, hu2, hufix⟩ := exists_inv_of_arr_gen
          (n := 10) (Γ := mog22) (V := Q) (L := ρ.range)
          (ψ := rhoC10 mog22 mog22_le_mog22plus) hψinj actC10
          (fun σ a ha m => rhoC10_toW mog22 mog22_le_mog22plus σ ha m) actC10_lt
          inAutOK_m22InvolutionArr arr_involutive_m22 ⟨8, by norm_num⟩ (by decide +kernel)
          (fun σ hσ hσa => mem_mog22_of_arr hσ hσa
            outer_arrs_swap_zero_one.2.2.2.2.1 outer_arrs_swap_zero_one.2.2.2.2.2) he
        refine ⟨u, huL, hu2, ?_⟩
        rw [rkIdx_of_arr (P := fun m => actC10 m22InvolutionArr m == m)
          (fun m hm => (hufix m hm).trans beq_iff_eq.symm), card_fixed_actC10_m22,
          Nat.log_pow (by norm_num)]
      · obtain ⟨e, he⟩ := cocode22_std hcocode
        have hψinj : Function.Injective (rho10 mog22 mog22_le_mog22plus) := by
          intro a b hab
          have h := rho10_mog22plus_injective (a₁ := ⟨a, mog22_le_mog22plus a.2⟩)
            (a₂ := ⟨b, mog22_le_mog22plus b.2⟩) hab
          exact Subtype.ext
            (congrArg (fun x : ↥mog22plus => (x : Equiv.Perm (Fin 24))) h)
        obtain ⟨u, huL, hu2, hufix⟩ := exists_inv_of_arr_gen
          (n := 10) (Γ := mog22) (V := Q) (L := ρ.range)
          (ψ := rho10 mog22 mog22_le_mog22plus) hψinj act10
          (fun σ a ha m => rho10_toW mog22 mog22_le_mog22plus σ ha m) act10_lt
          inAutOK_m22InvolutionArr arr_involutive_m22 ⟨8, by norm_num⟩ (by decide +kernel)
          (fun σ hσ hσa => mem_mog22_of_arr hσ hσa
            outer_arrs_swap_zero_one.2.2.2.2.1 outer_arrs_swap_zero_one.2.2.2.2.2) he
        refine ⟨u, huL, hu2, ?_⟩
        rw [rkIdx_of_arr (P := fun m => act10 m22InvolutionArr m == m)
          (fun m hm => (hufix m hm).trans beq_iff_eq.symm), card_fixed_act10_m22,
          Nat.log_pow (by norm_num)]
    have hconj : ∀ u v : ↥ρ.range, orderOf u = 2 → orderOf v = 2 →
        ∃ c : ↥ρ.range, v = c * u * c⁻¹ := by
      intro u v hu hv
      obtain ⟨eH⟩ := hH
      let E : ↥ρ.range ≃* CFSG.Blueprint.NativeSporadic.M22 :=
        (MonoidHom.ofInjective hρinj).symm.trans eH
      obtain ⟨c, hc⟩ := m22_involutions_conj (E u) (E v) (by
        rw [E.orderOf_eq, hu]) (by
        rw [E.orderOf_eq, hv])
      refine ⟨E.symm c, ?_⟩
      apply E.injective
      simpa [map_mul, map_inv] using hc
    intro u hu2
    obtain ⟨c, hc⟩ := hconj ⟨t0, ht0mem⟩ u (by rw [Subgroup.orderOf_mk]; exact ht02) hu2
    have hc' : (u : MulAut Q) = (c : MulAut Q) * (t0 : MulAut Q) * (c : MulAut Q)⁻¹ := by
      simpa using congrArg (fun x : ↥ρ.range => (x : MulAut Q)) hc
    rw [hc', fixV_zpowers_conj]
    have hidx : rkIdx ((fixV (Subgroup.zpowers (t0 : MulAut Q))).map
        (c : MulAut Q).toMonoidHom) = rkIdx (fixV (Subgroup.zpowers (t0 : MulAut Q))) := by
      unfold rkIdx
      exact congrArg (padicValNat 2)
        (Subgroup.index_map_equiv (H := fixV (Subgroup.zpowers (t0 : MulAut Q)))
          (c : MulAut Q))
    rw [hidx, ht0rank]
  have hq_le : E3.mQuot (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) (fixV H) ≤
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
    rw [hq_eq, rkIdx_fixV_zpowers (V := Q) ψ, commV_eq_commSub, ← hA_image]
    have hr := rk_map_add_rk_inf_ker q0
      (commSub (⊤ : Subgroup W) (Subgroup.zpowers t))
    omega
  have hψ_range_of_inner :
      (∃ h0 ∈ H, ∀ h ∈ H, t * h * t⁻¹ = h0 * h * h0⁻¹) → ψ ∈ ρ.range := by
    intro hInner
    obtain ⟨h0, hh0, hconjH⟩ := hInner
    have hmem : t * (h0 : MulAut W)⁻¹ ∈ Subgroup.centralizer (H : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : (h0 : MulAut W)⁻¹ * h * h0 ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem hh0) hh) hh0
      have h1 := hconjH _ hh'
      have h2 : t * (h0 : MulAut W)⁻¹ * h * h0 = h * t := by
        calc t * (h0 : MulAut W)⁻¹ * h * h0
            = (t * ((h0 : MulAut W)⁻¹ * h * h0) * t⁻¹) * t := by group
          _ = h * t := by rw [h1]; group
      calc h * (t * (h0 : MulAut W)⁻¹) = (h * t) * (h0 : MulAut W)⁻¹ := by group
        _ = (t * (h0 : MulAut W)⁻¹ * h * h0) * (h0 : MulAut W)⁻¹ := by rw [← h2]
        _ = (t * (h0 : MulAut W)⁻¹) * h := by group
    have hcent_bot : Subgroup.centralizer (H : Set (MulAut W)) = ⊥ :=
      centralizer_eq_bot_of_m22_quotient_rank_ten hW hH hcomm hirr hdim
    have hu1 : t * (h0 : MulAut W)⁻¹ = 1 := by
      have hmem' := hmem
      rw [hcent_bot] at hmem'
      exact Subgroup.mem_bot.mp hmem'
    have ht_eq : t = (h0 : MulAut W) := by
      calc t = (t * (h0 : MulAut W)⁻¹) * (h0 : MulAut W) := by group
        _ = 1 * (h0 : MulAut W) := by rw [hu1]
        _ = (h0 : MulAut W) := one_mul _
    refine MonoidHom.mem_range.mpr ⟨⟨h0, hh0⟩, ?_⟩
    ext v
    obtain ⟨w, rfl⟩ := hqsurj v
    rw [hψ, ht_eq]
    exact (heq ⟨h0, hh0⟩ w).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hq_eq]
    exact h3
  · intro hInner
    rw [hq_eq]
    exact hfour_range ⟨ψ, hψ_range_of_inner hInner⟩ (by rw [Subgroup.orderOf_mk]; exact hψ2)
  · intro hrk
    have hq3 : E3.mQuot (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) (fixV H) = 3 := by
      apply le_antisymm
      · exact hq_le.trans hrk
      · rw [hq_eq]
        exact h3
    refine ⟨hq3, ?_⟩
    intro hInner
    have h4 : E3.mQuot (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) (fixV H) = 4 := by
      rw [hq_eq]
      exact hfour_range ⟨ψ, hψ_range_of_inner hInner⟩ (by rw [Subgroup.orderOf_mk]; exact hψ2)
    omega

end Certs

theorem mQuot_commSub_sup_fixV_eq_three_and_not_inner_of_rk_le_three
    (hW : ∀ w : W, w ^ 2 = 1) (hH : IsSpor ↥H .M22)
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (hdim : E3.mQuot (⊤ : Subgroup W) (fixV H) = 10)
    (htN : t ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3) :
    E3.mQuot (commSub (⊤ : Subgroup W) (Subgroup.zpowers t) ⊔ fixV H) (fixV H) = 3 ∧
      ¬ ∃ h0 ∈ H, ∀ h ∈ H, t * h * t⁻¹ = h0 * h * h0⁻¹ :=
  (mQuot_bounds hW hH hcomm hirr hdim htN ht2 ht1).2.2 hrk

end CFSG.Quasithin.M22TenNormalizer

end
