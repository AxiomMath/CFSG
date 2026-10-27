module

public import CFSG.Quasithin.AppendixH.H14.MathieuStabilizerClasses
public import CFSG.Quasithin.AppendixH.H14.AutM22InvolutionClasses
public import CFSG.Quasithin.AppendixH.H14.SectionRankEngine
public import CFSG.Quasithin.AppendixH.H14.MathieuModuleCoordinates

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.ASVolI.ChH

theorem rImg_zpowers {Γ : Subgroup S24} {V : Type*} [CommGroup V] (ρ : ↥Γ →* MulAut V) {z : S24}
    (hz : z ∈ Γ) : rImg ρ (Subgroup.zpowers z) = Subgroup.zpowers (ρ ⟨z, hz⟩) := by
  have hsub : (Subgroup.zpowers z).subgroupOf Γ = Subgroup.zpowers (⟨z, hz⟩ : ↥Γ) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg (fun x : ↥Γ => (x : S24)) hk⟩
  unfold rImg
  rw [hsub, MonoidHom.map_zpowers]

private theorem rho11_restrict_apply {Γ : Subgroup S24} (hΓ : Γ ≤ AutPerm) (γ : ↥Γ) (w : W11) :
    rho11 Γ hΓ γ w = rho11 AutPerm le_rfl ⟨γ, hΓ γ.2⟩ w := rfl

private theorem rhoC11_restrict_apply {Γ : Subgroup S24} (hΓ : Γ ≤ AutPerm) (γ : ↥Γ) (w : W11) :
    rhoC11 Γ hΓ γ w = rhoC11 AutPerm le_rfl ⟨γ, hΓ γ.2⟩ w := rfl

@[expose] def actSec11 (isCode : Bool) : Array ℕ → ℕ → ℕ :=
  if isCode then actC11 else act11

@[expose] def actSec10 (isCode : Bool) : Array ℕ → ℕ → ℕ :=
  if isCode then actC10 else act10

theorem count_fixed_octad (isCode : Bool) :
    ((List.range (2 ^ 11)).filter fun m => actSec11 isCode octadArr m == m).length = 2 ^ 7 := by
  cases isCode
  · simpa [actSec11] using card_fixed_act11_octad
  · simpa [actSec11] using card_fixed_actC11_octad

theorem count_fixed_fptFree (isCode : Bool) :
    ((List.range (2 ^ 11)).filter fun m => actSec11 isCode fptFreeArr m == m).length = 2 ^ 6 := by
  cases isCode
  · simpa [actSec11] using card_fixed_act11_fptFree
  · simpa [actSec11] using card_fixed_actC11_fptFree

theorem count_fixed_m22Involution (isCode : Bool) :
    ((List.range (2 ^ 10)).filter fun m => actSec10 isCode m22InvolutionArr m == m).length =
      2 ^ 6 := by
  cases isCode
  · simpa [actSec10] using card_fixed_act10_m22
  · simpa [actSec10] using card_fixed_actC10_m22

theorem count_fixed_outerFptFree (isCode : Bool) :
    ((List.range (2 ^ 10)).filter fun m => actSec10 isCode outerFptFreeArr m == m).length =
      2 ^ 5 := by
  cases isCode
  · simpa [actSec10] using card_fixed_act10_outerFptFree
  · simpa [actSec10] using card_fixed_actC10_outerFptFree

theorem count_fixed_outerOctad (isCode : Bool) :
    ((List.range (2 ^ 10)).filter fun m => actSec10 isCode outerOctadArr m == m).length =
      2 ^ 7 := by
  cases isCode
  · simpa [actSec10] using card_fixed_act10_outerOctad
  · simpa [actSec10] using card_fixed_actC10_outerOctad

theorem rkIdx_fixV_rImg_of_class_big (isCode : Bool) {d : ℕ} (hd : d ≠ 22) {a b : Fin 24}
    {Γ : Subgroup S24} (hΓ : Γ ≤ AutPerm) {V : Type*} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    (h : IsMathModule isCode d a b Γ ρ) {σ c s : S24} (hσ : σ ∈ Γ) (hc : c ∈ AutPerm)
    (hs : s ∈ AutPerm) (hσcs : σ = c * s * c⁻¹) {arr : Array ℕ} (harr : HasArr s arr) {k : ℕ}
    (hk : ((List.range (2 ^ 11)).filter fun m => actSec11 isCode arr m == m).length = 2 ^ k) :
    rkIdx (fixV (rImg ρ (Subgroup.zpowers σ))) = 11 - k := by
  rw [rImg_zpowers ρ hσ]
  cases isCode
  · obtain ⟨e, he⟩ := exists_equiv_cocode hd hΓ h
    refine rkIdx_fixV_zpowers_of_arr (Λ := AutPerm) (n := 11) (ρ₀ := rho11 AutPerm le_rfl)
      (act := act11) (hact := fun s arr harr m => rho11_toW AutPerm le_rfl s harr m)
      (hlt := fun arr m => act11_lt arr m) e (ρ ⟨σ, hσ⟩) ⟨σ, hΓ hσ⟩ ⟨c, hc⟩ ⟨s, hs⟩
      ?_ ?_ harr ?_
    · exact Subtype.ext (by simpa using hσcs)
    · intro v
      exact (he ⟨σ, hσ⟩ v).trans (rho11_restrict_apply hΓ ⟨σ, hσ⟩ (e v))
    · simpa [actSec11] using hk
  · obtain ⟨e, he⟩ := exists_equiv_code hd hΓ h
    refine rkIdx_fixV_zpowers_of_arr (Λ := AutPerm) (n := 11) (ρ₀ := rhoC11 AutPerm le_rfl)
      (act := actC11) (hact := fun s arr harr m => rhoC11_toW AutPerm le_rfl s harr m)
      (hlt := fun arr m => actC11_lt arr m) e (ρ ⟨σ, hσ⟩) ⟨σ, hΓ hσ⟩ ⟨c, hc⟩ ⟨s, hs⟩
      ?_ ?_ harr ?_
    · exact Subtype.ext (by simpa using hσcs)
    · intro v
      exact (he ⟨σ, hσ⟩ v).trans (rhoC11_restrict_apply hΓ ⟨σ, hσ⟩ (e v))
    · simpa [actSec11] using hk

theorem rkIdx_fixV_rImg_of_class_small (isCode : Bool) {a b : Fin 24} (hab : a ≠ b)
    {Γ : Subgroup S24} (hΓ : Γ ≤ M2ab a b) {V : Type*} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    (h : IsMathModule isCode 22 a b Γ ρ) {τ : S24} (hτ : τ ∈ AutPerm) (h0 : τ 0 = a)
    (h1 : τ 1 = b) {σ c s : S24} (hσ : σ ∈ Γ) (hc : c ∈ mog22plus) (hs : s ∈ mog22plus)
    (hσcs : τ⁻¹ * σ * τ = c * s * c⁻¹) {arr : Array ℕ} (harr : HasArr s arr) {k : ℕ}
    (hk : ((List.range (2 ^ 10)).filter fun m => actSec10 isCode arr m == m).length = 2 ^ k) :
    rkIdx (fixV (rImg ρ (Subgroup.zpowers σ))) = 10 - k := by
  rw [rImg_zpowers ρ hσ]
  have hγ : τ⁻¹ * σ * τ ∈ mog22plus := (mem_M2ab_iff_conj hab hτ h0 h1 σ).1 (hΓ hσ)
  cases isCode
  · obtain ⟨e, he⟩ := exists_equiv_cocode22 hab hτ h0 h1 hΓ h
    refine rkIdx_fixV_zpowers_of_arr (Λ := mog22plus) (n := 10) (ρ₀ := rho10 mog22plus le_rfl)
      (act := act10) (hact := fun s arr harr m => rho10_toW mog22plus le_rfl s harr m)
      (hlt := fun arr m => act10_lt arr m) e (ρ ⟨σ, hσ⟩) ⟨τ⁻¹ * σ * τ, hγ⟩ ⟨c, hc⟩ ⟨s, hs⟩
      ?_ ?_ harr ?_
    · exact Subtype.ext (by simpa using hσcs)
    · intro v
      exact he ⟨σ, hσ⟩ v hγ
    · simpa [actSec10] using hk
  · obtain ⟨e, he⟩ := exists_equiv_code22 hab hτ h0 h1 hΓ h
    refine rkIdx_fixV_zpowers_of_arr (Λ := mog22plus) (n := 10) (ρ₀ := rhoC10 mog22plus le_rfl)
      (act := actC10) (hact := fun s arr harr m => rhoC10_toW mog22plus le_rfl s harr m)
      (hlt := fun arr m => actC10_lt arr m) e (ρ ⟨σ, hσ⟩) ⟨τ⁻¹ * σ * τ, hγ⟩ ⟨c, hc⟩ ⟨s, hs⟩
      ?_ ?_ harr ?_
    · exact Subtype.ext (by simpa using hσcs)
    · intro v
      exact he ⟨σ, hσ⟩ v hγ
    · simpa [actSec10] using hk

section Certs


theorem rkIdx_fixV_involutions :
    ∀ (isCode : Bool) (d : ℕ), (d = 22 ∨ d = 23 ∨ d = 24) → ∀ a b : Fin 24, a ≠ b →
    ∀ Γ : Subgroup S24, Ld d a b ≤ Γ → Γ ≤ AutLd d a b →
    ∀ (V : Type) [CommGroup V] (ρ : ↥Γ →* MulAut V), IsMathModule isCode d a b Γ ρ →
      (∀ z ∈ Ld d a b, orderOf z = 2 → IsTwoCentralElt (Ld d a b) z →
        rkIdx (fixV (rImg ρ (Subgroup.zpowers z))) = 4) ∧
      (d = 24 → ∀ t ∈ M24g, orderOf t = 2 → ¬ IsTwoCentralElt M24g t →
        rkIdx (fixV (rImg ρ (Subgroup.zpowers t))) = 5) := by
  intro isCode d hd a b hab Γ hlo hhi V _ ρ h
  rcases hd with rfl | rfl | rfl
  · refine ⟨?_, fun h => absurd h (by norm_num)⟩
    intro z hz hz2 hzc
    obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a b hab
    have hx22 : τ⁻¹ * z * τ ∈ M22g 0 1 := (mem_M22g_iff_conj hτ hτ0 hτ1 z).1 hz
    have hx2 : orderOf (τ⁻¹ * z * τ) = 2 := by rw [orderOf_conj_inv_mul τ z, hz2]
    obtain ⟨σ₀, hσ₀mem, hσ₀arr, hσ₀2⟩ := exists_m22Involution
    have hσ₀22 : σ₀ ∈ M22g 0 1 := hσ₀mem
    obtain ⟨g, hg, hgconj⟩ := isConjIn_M22g 0 1 (by decide) hσ₀22 hx22 hσ₀2 hx2
    have hgplus : g ∈ mog22plus := mog22_le_mog22plus hg
    have hσ₀plus : σ₀ ∈ mog22plus := mog22_le_mog22plus hσ₀mem
    have h4 := rkIdx_fixV_rImg_of_class_small (isCode := isCode) (hab := hab) (hΓ := hhi) (h := h)
      (hτ := hτ) (h0 := hτ0) (h1 := hτ1) (hσ := hlo hz) (hc := hgplus) (hs := hσ₀plus)
      (hσcs := hgconj.symm) (harr := hσ₀arr) (k := 6) (hk := count_fixed_m22Involution isCode)
    simpa using h4
  · have hΓ : Γ ≤ AutPerm := fun x hx => (hhi hx).1
    refine ⟨?_, fun h => absurd h (by norm_num)⟩
    intro z hz hz2 hzc
    obtain ⟨hzM, hza⟩ := (CFSG.ASVolI.mem_M23g_iff a z).1 hz
    rcases involution_dichotomy hzM hz2 with ⟨-, ⟨c, hc, hzeq⟩, -, -⟩ | ⟨-, -, hfpf⟩
    · have h4 := rkIdx_fixV_rImg_of_class_big (isCode := isCode) (d := 23) (hd := by norm_num)
        (hΓ := hΓ) (h := h) (hσ := hlo hz) (hc := hc) (hs := involution2A_mem)
        (hσcs := hzeq) (harr := hasArr_involution2A) (k := 7) (hk := count_fixed_octad isCode)
      simpa using h4
    · exact absurd hza (hfpf a)
  · have hΓ : Γ ≤ AutPerm := hhi
    refine ⟨?_, ?_⟩
    · intro z hz hz2 hzc
      rcases involution_dichotomy hz hz2 with ⟨-, ⟨c, hc, hzeq⟩, -, -⟩ | ⟨hnc, -, -⟩
      · have h4 := rkIdx_fixV_rImg_of_class_big (isCode := isCode) (d := 24) (hd := by norm_num)
          (hΓ := hΓ) (h := h) (hσ := hlo hz) (hc := hc) (hs := involution2A_mem)
          (hσcs := hzeq) (harr := hasArr_involution2A) (k := 7) (hk := count_fixed_octad isCode)
        simpa using h4
      · exact absurd hzc hnc
    · intro _ t ht ht2 htnc
      rcases involution_dichotomy ht ht2 with ⟨h2c, -, -, -⟩ | ⟨-, ⟨c, hc, teq⟩, -⟩
      · exact absurd h2c htnc
      · have h5 := rkIdx_fixV_rImg_of_class_big (isCode := isCode) (d := 24) (hd := by norm_num)
          (hΓ := hΓ) (h := h) (hσ := hlo ht) (hc := hc) (hs := involution2B_mem)
          (hσcs := teq) (harr := hasArr_involution2B) (k := 6) (hk := count_fixed_fptFree isCode)
        simpa using h5

theorem rkIdx_fixV_outer_involutions (a b : Fin 24) (hab : a ≠ b) (isCode : Bool) (V : Type)
    [CommGroup V] (ρ : ↥(M2ab a b) →* MulAut V) (h : IsMathModule isCode 22 a b (M2ab a b) ρ) :
    ∀ i ∈ M2ab a b, i ∉ M22g a b → orderOf i = 2 →
      ((∀ x : Fin 24, i x ≠ x) → rkIdx (fixV (rImg ρ (Subgroup.zpowers i))) = 5) ∧
      ((∃ O : Finset (Fin 24), IsOctad O ∧ ¬ (a ∈ O ∧ b ∈ O) ∧ ∀ x, x ∈ O ↔ i x = x) →
        rkIdx (fixV (rImg ρ (Subgroup.zpowers i))) = 3) := by
  intro i hi hin hi2
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a b hab
  have hx_plus : τ⁻¹ * i * τ ∈ mog22plus := (mem_M2ab_iff_conj hab hτ hτ0 hτ1 i).1 hi
  have hx_n22 : τ⁻¹ * i * τ ∉ mog22 :=
    fun hh => hin ((mem_M22g_iff_conj hτ hτ0 hτ1 i).2 hh)
  have hx2 : orderOf (τ⁻¹ * i * τ) = 2 := by rw [orderOf_conj_inv_mul τ i, hi2]
  refine ⟨?_, ?_⟩
  · intro hfree
    have hxfree : ∀ x, (τ⁻¹ * i * τ) x ≠ x :=
      fun x hx => hfree (τ x) ((conj_apply_eq_self_iff τ i x).1 hx)
    obtain ⟨σ, hσp, hσn, hσarr, hσ2, hσff⟩ := exists_outerFptFree
    obtain ⟨c, hc, hceq⟩ := outer_fptFree_conj_base hσp hx_plus hσn hx_n22 hσ2 hx2 hσff hxfree
    have h5 := rkIdx_fixV_rImg_of_class_small (isCode := isCode) (hab := hab) (hΓ := le_rfl) (h := h)
      (hτ := hτ) (h0 := hτ0) (h1 := hτ1) (hσ := hi) (hc := hc) (hs := hσp)
      (hσcs := hceq.symm) (harr := hσarr) (k := 5) (hk := count_fixed_outerFptFree isCode)
    simpa using h5
  · rintro ⟨O, hO, -, hOfix⟩
    obtain ⟨y, hy⟩ := Finset.card_pos.1 (by rw [hO.1]; norm_num)
    have hiy : i y = y := (hOfix y).1 hy
    have hτy : τ (τ⁻¹ y) = y := Equiv.apply_symm_apply τ y
    have hxfix : ∃ x, (τ⁻¹ * i * τ) x = x :=
      ⟨τ⁻¹ y, (conj_apply_eq_self_iff τ i (τ⁻¹ y)).2 (by rw [hτy, hiy])⟩
    obtain ⟨σ, hσp, hσn, hσarr, hσ2, hσfix⟩ := exists_outerOctad
    obtain ⟨c, hc, hceq⟩ := outer_fixing_conj_base hσp hx_plus hσn hx_n22 hσ2 hx2 hσfix hxfix
    have h3 := rkIdx_fixV_rImg_of_class_small (isCode := isCode) (hab := hab) (hΓ := le_rfl) (h := h)
      (hτ := hτ) (h0 := hτ0) (h1 := hτ1) (hσ := hi) (hc := hc) (hs := hσp)
      (hσcs := hceq.symm) (harr := hσarr) (k := 7) (hk := count_fixed_outerOctad isCode)
    simpa using h3

end Certs

end CFSG.Quasithin.AppendixH.H14
