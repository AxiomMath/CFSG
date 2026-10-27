module

public import CFSG.Quasithin.Background.D36GluedFinal
public import CFSG.Quasithin.Background.B4L3Two

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem L3.d36_AS_act_centre :
    ∀ c : L3.Vec, c ≠ 0 → ∀ g ∈ L3.AS {0, c}, L3.act g c = c := by
  set_option maxRecDepth 100000 in decide +kernel

namespace L3Data

variable {Y : Type} [CommGroup Y] {L₀ : Subgroup (MulAut Y)} {U Z : Subgroup Y}
  (D : L3Data L₀ U Z)

theorem d36_comm_mem {c : L3.Vec} (hc : c ≠ 0) {γ : L3.Γ} (hγ : γ ∈ ASsub c hc) {u : Y}
    (hu : u ∈ U) : ∃ hw : D.rho γ u * u⁻¹ ∈ U,
      Multiplicative.toAdd (D.β ⟨D.rho γ u * u⁻¹, hw⟩) ∈ ({0, c} : Finset L3.Vec) := by
  have hmem : D.rho γ u ∈ U := D.inv_U _ (D.rho_mem γ) u hu
  have hw : D.rho γ u * u⁻¹ ∈ U := U.mul_mem hmem (U.inv_mem hu)
  refine ⟨hw, ?_⟩
  have key : D.β ⟨D.rho γ u * u⁻¹, hw⟩ = Multiplicative.ofAdd
      (L3.act γ (Multiplicative.toAdd (D.β ⟨u, hu⟩)) - Multiplicative.toAdd (D.β ⟨u, hu⟩)) :=
    D.β_comm γ ⟨u, hu⟩ hmem hw
  rw [key, toAdd_ofAdd]
  exact (Finset.mem_filter.mp (mem_ASsub.mp hγ)).2 _

theorem d36_comm_comm_mem {c : L3.Vec} (hc : c ≠ 0) {γ : L3.Γ} (hγ : γ ∈ ASsub c hc) {w : Y}
    (hw : w ∈ U) (hwc : Multiplicative.toAdd (D.β ⟨w, hw⟩) ∈ ({0, c} : Finset L3.Vec)) :
    D.rho γ w * w⁻¹ ∈ Z := by
  have hmem : D.rho γ w ∈ U := D.inv_U _ (D.rho_mem γ) w hw
  have hx : D.rho γ w * w⁻¹ ∈ U := U.mul_mem hmem (U.inv_mem hw)
  have hfix : L3.act γ (Multiplicative.toAdd (D.β ⟨w, hw⟩)) =
      Multiplicative.toAdd (D.β ⟨w, hw⟩) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwc
    rcases hwc with h0 | h0
    · rw [h0, L3.act_zero]
    · rw [h0]
      exact L3.d36_AS_act_centre c hc γ (mem_ASsub.mp hγ)
  have key : D.β ⟨D.rho γ w * w⁻¹, hx⟩ = Multiplicative.ofAdd
      (L3.act γ (Multiplicative.toAdd (D.β ⟨w, hw⟩)) - Multiplicative.toAdd (D.β ⟨w, hw⟩)) :=
    D.β_comm γ ⟨w, hw⟩ hmem hx
  have h1 : D.β ⟨D.rho γ w * w⁻¹, hx⟩ = 1 := by
    rw [key, hfix, sub_self]
    rfl
  exact (D.ker_β ⟨_, hx⟩).1 h1

theorem d36_centre_card {c : L3.Vec} (hc : c ≠ 0) :
    Nat.card ((ASsub c hc).map D.rho) = 4 := by
  rw [Subgroup.card_map_of_injective D.rho_injective, card_ASsub hc]

theorem d36_centre_le {c : L3.Vec} (hc : c ≠ 0) : (ASsub c hc).map D.rho ≤ L₀ := by
  rintro _ ⟨γ, -, rfl⟩
  exact D.rho_mem γ

theorem d36_centre_isElemAbelian2 {c : L3.Vec} (hc : c ≠ 0) :
    IsElemAbelian2 ((ASsub c hc).map D.rho) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, (L3.AS_elem c hc g (mem_ASsub.mp hg) h (mem_ASsub.mp hh)).1]
  · rintro _ ⟨g, hg, rfl⟩
    rw [pow_two, ← map_mul, (L3.AS_elem c hc g (mem_ASsub.mp hg) g (mem_ASsub.mp hg)).2,
      map_one]

theorem d36_centre_cubic [Finite Y] {U' : Subgroup Y} {c : L3.Vec} (hc : c ≠ 0) (hsup : U ⊔ U' = ⊤)
    (hU' : ∀ l ∈ L₀, ∀ u ∈ U', l u = u) (hZ : Z ≤ fixV L₀) :
    commSeries ((ASsub c hc).map D.rho) 3 = ⊥ := by
  apply commSeries_three_eq_bot_of_forall
  rintro _ ⟨γ₁, hγ₁, rfl⟩ _ ⟨γ₂, hγ₂, rfl⟩ _ ⟨γ₃, -, rfl⟩ y
  obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.mp (hsup ▸ Subgroup.mem_top y)
  have hy : D.rho γ₁ (u * u') * (u * u')⁻¹ = D.rho γ₁ u * u⁻¹ := by
    rw [map_mul, hU' _ (D.rho_mem γ₁) u' hu', mul_inv_rev]
    group
  rw [hy]
  obtain ⟨hw, hwc⟩ := D.d36_comm_mem hc hγ₁ hu
  have hz := D.d36_comm_comm_mem hc hγ₂ hw hwc
  exact hZ hz _ (D.rho_mem γ₃)

theorem d36_centre_lift (hY : ∀ y : Y, y ^ 2 = 1) {c : L3.Vec} (hc : c ≠ 0) (hZ : Z ≤ fixV L₀) :
    ∃ y ∈ U, y ∈ fixV ((ASsub c hc).map D.rho) ∧ y ∉ Z := by
  obtain ⟨x, hx⟩ := D.β_surj (Multiplicative.ofAdd c)
  have hEL := D.d36_centre_le hc
  have hEel := D.d36_centre_isElemAbelian2 hc
  have hcard := D.d36_centre_card hc
  have hne : ∃ r ∈ (ASsub c hc).map D.rho, r ≠ 1 := by
    have hEne : (ASsub c hc).map D.rho ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hcard
      omega
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have hxcomm : ∀ r ∈ (ASsub c hc).map D.rho, r ≠ 1 →
      ∃ z ∈ U, (r z * z⁻¹) * (x : Y)⁻¹ ∈ Z := by
    intro r hr hr1
    obtain ⟨γ, hγ, rfl⟩ := hr
    have hγ1 : γ ≠ 1 := fun h => hr1 (by rw [h, map_one])
    have hcim := L3.AS_cim c hc γ (mem_ASsub.mp hγ) hγ1
    have hcmem : c ∈ L3.cim γ := by rw [hcim]; simp
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hcmem
    obtain ⟨z, hz⟩ := D.β_surj (Multiplicative.ofAdd v)
    refine ⟨z, z.2, ?_⟩
    have hmem : D.rho γ (z : Y) ∈ U := D.inv_U _ (D.rho_mem γ) _ z.2
    have hw : D.rho γ (z : Y) * (z : Y)⁻¹ ∈ U := U.mul_mem hmem (U.inv_mem z.2)
    have hw' : D.rho γ (z : Y) * (z : Y)⁻¹ * (x : Y)⁻¹ ∈ U := U.mul_mem hw (U.inv_mem x.2)
    have key : D.β ⟨D.rho γ (z : Y) * (z : Y)⁻¹, hw⟩ = Multiplicative.ofAdd c := by
      have := D.β_comm γ z hmem hw
      rw [this, hz, toAdd_ofAdd, hv]
    have h1 : D.β ⟨D.rho γ (z : Y) * (z : Y)⁻¹ * (x : Y)⁻¹, hw'⟩ = 1 := by
      have e : (⟨D.rho γ (z : Y) * (z : Y)⁻¹ * (x : Y)⁻¹, hw'⟩ : ↥U) =
          ⟨D.rho γ (z : Y) * (z : Y)⁻¹, hw⟩ * x⁻¹ := rfl
      rw [e, map_mul, map_inv, key, hx]
      exact mul_inv_cancel _
    exact (D.ker_β ⟨_, hw'⟩).1 h1
  obtain ⟨y, hyU, hyx, hyfix⟩ := exists_fixed_of_commutators hY
    (R := (ASsub c hc).map D.rho) (fun r hr => by simpa [pow_two] using hEel.2 r hr) hne
    (D := Z) (U := U) (fun z hz e he => hZ hz e (hEL he))
    (fun r hr u hu => D.inv_U r (hEL hr) u hu) hxcomm
  refine ⟨y, hyU, hyfix, fun hyZ => ?_⟩
  have hxZ : (x : Y) ∈ Z := by
    have h1 := Z.mul_mem (Z.inv_mem hyx) hyZ
    have e : (y * (x : Y)⁻¹)⁻¹ * y = x := by group
    rwa [e] at h1
  have h0 := (D.ker_β x).2 hxZ
  rw [hx] at h0
  exact hc (Multiplicative.ofAdd.injective (h0.trans ofAdd_zero.symm))

end L3Data

section Glued

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace GluedSwap

theorem false_of_L3 (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) (hL₀X : L₀ ≤ X)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u)
    (hnat : BinaryNaturalSL L₀ U (U ⊓ fixV L₀) 3 1) : False := by
  obtain ⟨D⟩ := hnat.toL3Coord
  have hcU := D.card_U
  rw [card_eq_two_pow hY U, card_eq_two_pow hY (U ⊓ fixV L₀)] at hcU
  have hU3 : rk ↥U = rk ↥(U ⊓ fixV L₀) + 3 := by
    have : 2 ^ rk ↥U = 2 ^ (rk ↥(U ⊓ fixV L₀) + 3) := by rw [hcU, pow_add]; ring
    exact Nat.pow_right_injective (le_refl 2) this
  have hRel := h.diag_isElemAbelian2 hL₀ hdiag
  have hkR := h.rk_le_diagSub hdiag hRel
  have hR4 := D.elemAbelian_card_le_four glueDiagSub_le hRel
  have hk2 : rk ↥(glueDiagSub L₀ A U) ≤ 2 := by
    rw [card_eq_two_pow_of_isPGroup hRel.isPGroup] at hR4
    by_contra hcon
    push Not at hcon
    have h8 : 2 ^ 3 ≤ 2 ^ rk ↥(glueDiagSub L₀ A U) := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  obtain ⟨c, hc⟩ : ∃ c : L3.Vec, c ≠ 0 := ⟨fun _ => 1, by decide⟩
  have hEL := D.d36_centre_le hc
  have hEel := D.d36_centre_isElemAbelian2 hc
  have hEcard := D.d36_centre_card hc
  have hEne : (ASsub c hc).map D.rho ≠ ⊥ := fun he => by
    rw [he, Subgroup.card_bot] at hEcard
    omega
  have hE : IsA2 X ((ASsub c hc).map D.rho) := ⟨hEL.trans hL₀X, hEne, hEel⟩
  have hE3 := D.d36_centre_cubic hc h.pair.sup_eq hL₀ (inf_le_right : U ⊓ fixV L₀ ≤ fixV L₀)
  have hcmp := h.compare_cubic hE hE3 (fun e he u hu => hL₀ e (hEL he) u hu)
  have hrkE : rk ↥((ASsub c hc).map D.rho) = 2 := by
    have h1 := card_eq_two_pow_of_isPGroup hEel.isPGroup
    rw [hEcard] at h1
    have : 2 ^ rk ↥((ASsub c hc).map D.rho) = 2 ^ 2 := by omega
    exact Nat.pow_right_injective (le_refl 2) this
  rw [hrkE] at hcmp
  obtain ⟨y, hyU, hyfix, hyZ⟩ := D.d36_centre_lift hY hc (inf_le_right : U ⊓ fixV L₀ ≤ fixV L₀)
  have hlt : rk ↥(U ⊓ fixV L₀) < rk ↥(U ⊓ fixV ((ASsub c hc).map D.rho)) := by
    have hle : U ⊓ fixV L₀ ≤ U ⊓ fixV ((ASsub c hc).map D.rho) :=
      inf_le_inf_left U (fun z hz e he => hz e (hEL he))
    by_contra hcon
    push Not at hcon
    have heq := eq_of_le_of_rk_le hY hle hcon
    exact hyZ (heq ▸ ⟨hyU, hyfix⟩)
  have hDZ : U ⊓ U' ≤ U ⊓ fixV L₀ := le_inf inf_le_left (fun d hd l hl => hL₀ l hl d hd.2)
  have hdz := rk_mono hDZ
  obtain ⟨hs1, -, -⟩ := h.shape_B hY
  have hUh : rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ≤ rk ↥U :=
    rk_mono (commModSub_le _ _ _)
  have hF : rk ↥(U ⊓ fixV ((ASsub c hc).map D.rho)) ≤ rk ↥U := rk_mono inf_le_left
  have ht : rk ↥U - rk ↥(U ⊓ fixV ((ASsub c hc).map D.rho)) ≤ 2 := by omega
  have hk : rk ↥(A ⊓ stabSub U) ≤ 2 := by omega
  have hub : 3 ≤ rk ↥U - rk ↥(U ⊓ U') := by omega
  have h6 : (rk ↥(A ⊓ stabSub U) + 1) * (rk ↥U - rk ↥(U ⊓ fixV ((ASsub c hc).map D.rho))) ≤
      3 * 2 := Nat.mul_le_mul (by omega) ht
  omega

end GluedSwap

end Glued

theorem d36GluedDiagL3_of_L38 (hL38 : D3L38) : D36GluedDiagL3 := by
  intro W _ _ M Mp T L V t n hd A hA hQ hAU hdiag hn3 _ _
  exact (d36_gluedSwap hL38 n hA hQ hAU).false_of_L3 (d36_exp_VT n) (d36_L_le_X n)
    (d36_L_fix_Ut' hL38 n) hdiag hn3

end CFSG.Quasithin
