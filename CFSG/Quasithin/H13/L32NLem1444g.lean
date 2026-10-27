module

public import CFSG.Quasithin.H13.L32NLem1444f
public import CFSG.Quasithin.H13.L32NSet14

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L1444

variable {G : Type} [Group G] [Finite G]

namespace Setup3

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup3 G T L V V₂ g D Q₁ Q₂)
include S

theorem card_D : Nat.card D.V = 16 := by
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.V), S.dim, Nat.card_zmod]
  norm_num

theorem card_le_eight_of_comm {B : Subgroup G} (hBU : B ≤ fsuU T V)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) : Nat.card B ≤ 8 := by
  have hcard := D.card_eq_mul_range hBU
  rw [← L14323.card_hat_eq D hBU] at hcard
  have h1 := card_sq_le_of_isotropic D.nondegenerate (D.isotropic_hat hBU hBc)
  rw [S.card_D] at h1
  have h3 : Nat.card ↥(D.hat B) ≤ 4 := by
    by_contra h
    push Not at h
    have : 5 ^ 2 ≤ Nat.card ↥(D.hat B) ^ 2 := Nat.pow_le_pow_left h 2
    omega
  have h2 : Nat.card ↥(B ⊓ centerOf (fsuU T V)) ≤ 2 := by
    rw [← S.card2, ← S.zU]
    exact Subgroup.card_le_of_le inf_le_right
  rw [hcard]
  calc _ ≤ 2 * 4 := Nat.mul_le_mul h2 h3
    _ = 8 := by norm_num

theorem V₂_le_U : V₂ ≤ fsuU T V := S.plane.1.1.trans V_le_U

theorem card_hat_V₂ : Nat.card ↥(D.hat V₂) = 2 := by
  have h := D.card_eq_mul_range S.V₂_le_U
  rw [← L14323.card_hat_eq D S.V₂_le_U, S.plane.1.2.1] at h
  have hZ : V₂ ⊓ centerOf (fsuU T V) = fsuV1 T V := by
    rw [S.zU]
    exact inf_eq_right.mpr S.plane.2
  rw [hZ, S.card2] at h
  omega

theorem hat_W : D.hat (l32nW T V V₂) = D.B.orthogonal (D.hat V₂) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, ⟨⟨hwU, hwc⟩, -⟩, rfl⟩
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x hx => ?_
    have hle : D.hat V₂ ≤ LinearMap.ker (D.B.flip (D.π w)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨v, ⟨hv, hvU⟩, rfl⟩
      show D.B (D.π v) (D.π w) = 0
      rw [D.B_spec v hvU w hwU]
      have hvw := (Subgroup.mem_centralizer_iff.mp hwc) v hv
      calc v * w * v⁻¹ * w⁻¹ = (w * v) * v⁻¹ * w⁻¹ := by rw [hvw]
        _ = 1 := by group
    have := hle hx
    rw [LinearMap.mem_ker] at this
    exact this
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := D.π_surj x
    refine L128A.HatU.π_mem_hat D ⟨hu, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩ hu
    have hvU : v ∈ fsuU T V := S.V₂_le_U hv
    have h0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) (D.π v)
      (L128A.HatU.π_mem_hat D hv hvU)
    have h1 : v * u * v⁻¹ * u⁻¹ = 1 := (D.B_spec v hvU u hu).mp h0
    calc v * u = v * u * v⁻¹ * u⁻¹ * (u * v) := by group
      _ = u * v := by rw [h1, one_mul]

theorem card_W : Nat.card ↥(l32nW T V V₂) = 16 := by
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  have hWU : l32nW T V V₂ ≤ fsuU T V := inf_le_left
  have h := D.card_eq_mul_range hWU
  rw [← L14323.card_hat_eq D hWU, S.hat_W] at h
  have hZ : l32nW T V V₂ ⊓ centerOf (fsuU T V) = centerOf (fsuU T V) := by
    refine inf_eq_right.mpr fun x hx => ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hx.2 v (S.V₂_le_U hv))
  rw [hZ, S.zU, S.card2] at h
  have h1 : Module.finrank (ZMod 2) ↥(D.hat V₂) = 1 := by
    have h2 := L14323.card_submodule (D.hat V₂)
    rw [S.card_hat_V₂] at h2
    exact Nat.pow_right_injective le_rfl (h2.symm.trans (by norm_num))
  have hfr : Module.finrank (ZMod 2) ↥(D.B.orthogonal (D.hat V₂)) = 3 := by
    rw [LinearMap.BilinForm.finrank_orthogonal D.nondegenerate, S.dim, h1]
  have h3 := L14323.card_submodule (D.B.orthogonal (D.hat V₂))
  rw [hfr] at h3
  rw [h, h3]
  norm_num

omit [Finite G] S in
theorem card_conjugate (X : Subgroup G) (x : G) : Nat.card ↥(CFSG.conjugate X x) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective

theorem card_Wg16 : Nat.card ↥(CFSG.conjugate (l32nW T V V₂) g) = 16 := by
  rw [card_conjugate, S.card_W]

theorem inf_Wg : fsuU T V ⊓ CFSG.conjugate (l32nW T V V₂) g = V := by
  refine le_antisymm (fun x hx => ?_) (le_inf V_le_U S.V_le_Wg)
  rw [S.eq_E]
  exact ⟨⟨hx.1, Wg_le_cent S.g_normV₂ hx.2⟩, hx.2⟩

theorem Wg_inf_Q : CFSG.conjugate (l32nW T V V₂) g ⊓ pCoreOf 2 (l32nH T V) = V := by
  have h := card_eq_card_imageOTwoQuot_mul (l32nH T V) _ S.Wg_le_H
  rw [S.card_Wg16, S.card_Wg] at h
  have hle : V ≤ CFSG.conjugate (l32nW T V V₂) g ⊓ pCoreOf 2 (l32nH T V) :=
    le_inf S.V_le_Wg S.V_le_Q
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [S.card8]; omega)).symm

theorem Wg_le_normalizer : CFSG.conjugate (l32nW T V V₂) g ≤
    Subgroup.normalizer (fsuU T V : Set G) :=
  S.Wg_le_H.trans (L14332.l32nH_le_normalizer_fsuU T V)

theorem card_UWg : Nat.card ↥(fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g) = 64 := by
  have h := L32NSet14.card_sup_mul_card_inf S.Wg_le_normalizer
  rw [inf_comm, S.inf_Wg, S.card_Wg16, S.card32, S.card8, sup_comm] at h
  omega

theorem UWg_le_H : fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g ≤ l32nH T V :=
  sup_le S.U_le_H S.Wg_le_H

theorem card_le_two_mul {A : Subgroup G} (hA : A ≤ fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ fsuU T V) := by
  have hAN : A ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    hA.trans (S.UWg_le_H.trans (L14332.l32nH_le_normalizer_fsuU T V))
  have h := L32NSet14.card_sup_mul_card_inf hAN
  have hle : A ⊔ fsuU T V ≤ fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g := sup_le hA le_sup_left
  have h64 := Subgroup.card_le_of_le hle
  rw [S.card_UWg] at h64
  rw [S.card32] at h
  have h1 : Nat.card A * 32 ≤ 64 * Nat.card ↥(A ⊓ fsuU T V) := by
    calc Nat.card A * 32 = Nat.card ↥(A ⊔ fsuU T V) * Nat.card ↥(A ⊓ fsuU T V) := by
          rw [h]; norm_num
      _ ≤ 64 * Nat.card ↥(A ⊓ fsuU T V) := Nat.mul_le_mul_right _ h64
  omega

theorem card_le_eight_of_not_swap
    (hns : ∀ x ∈ CFSG.conjugate (l32nW T V V₂) g, x ∉ pCoreOf 2 (l32nH T V) →
      x ∈ Subgroup.normalizer (Q₁ : Set G) ∧ x ∈ Subgroup.normalizer (Q₂ : Set G))
    {A : Subgroup G} (hA : A ≤ fsuU T V ⊔ CFSG.conjugate (l32nW T V V₂) g)
    (helem : IsElemAbelian 2 A) : Nat.card A ≤ 8 := by
  by_contra hgt
  push Not at hgt
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (helem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← pow_two]; exact helem.2 a ha
  set B := A ⊓ fsuU T V with hBdef
  have hBU : B ≤ fsuU T V := inf_le_right
  have hB8 : Nat.card B ≤ 8 :=
    S.card_le_eight_of_comm hBU fun a ha b hb => hcomm a ha.1 b hb.1
  have hAB : Nat.card A ≤ 2 * Nat.card B := S.card_le_two_mul hA
  have hB4 : Nat.card ↥(D.hat B) = 4 := by
    have hcard := D.card_eq_mul_range hBU
    rw [← L14323.card_hat_eq D hBU] at hcard
    have h2 : Nat.card ↥(B ⊓ centerOf (fsuU T V)) ≤ 2 := by
      rw [← S.card2, ← S.zU]
      exact Subgroup.card_le_of_le inf_le_right
    have h1 := card_sq_le_of_isotropic D.nondegenerate
      (D.isotropic_hat hBU fun a ha b hb => hcomm a ha.1 b hb.1)
    rw [S.card_D] at h1
    have hpow := L14323.card_submodule (D.hat B)
    have hge : 3 ≤ Nat.card ↥(D.hat B) := by
      by_contra h
      push Not at h
      have : Nat.card B ≤ 2 * 2 := by
        rw [hcard]
        exact Nat.mul_le_mul h2 (by omega)
      omega
    rw [hpow] at hge h1 ⊢
    set k := Module.finrank (ZMod 2) ↥(D.hat B)
    have hk2 : 2 ≤ k := by
      by_contra h
      push Not at h
      interval_cases k <;> simp_all
    have hk3 : k ≤ 2 := by
      by_contra h
      push Not at h
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      have : (2 ^ 3) ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left this 2
      omega
    rw [show k = 2 by omega]
    norm_num
  obtain ⟨a, haA, haU⟩ : ∃ a ∈ A, a ∉ fsuU T V := by
    by_contra hall
    push Not at hall
    have hle : A ≤ B := fun x hx => ⟨hx, hall x hx⟩
    have := Subgroup.card_le_of_le hle
    omega
  have haUW := hA haA
  rw [← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ S.Wg_le_normalizer] at haUW
  obtain ⟨u, hu, w, hw, huw⟩ := haUW
  have huw' : u * w = a := huw
  have hwQ : w ∉ pCoreOf 2 (l32nH T V) := by
    intro hwQ
    have hwV : w ∈ V := by rw [← S.Wg_inf_Q]; exact ⟨hw, hwQ⟩
    exact haU (huw' ▸ (fsuU T V).mul_mem hu (V_le_U hwV))
  obtain ⟨hw₁, hw₂⟩ := hns w hw hwQ
  have huN : u ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    L14332.l32nH_le_normalizer_fsuU T V (S.U_le_H hu)
  have hwN := S.xN hw
  have hρu : D.ρ ⟨u, huN⟩ = 1 := S.rho_eq_one_of_mem_Q (S.U_le_Q hu) huN
  have hfix : ∀ v ∈ D.hat B, D.ρ ⟨w, hwN⟩ v = v := by
    have hgen : ∀ b ∈ B, D.ρ ⟨w, hwN⟩ (D.π b) = D.π b := by
      intro b hb
      have hab : a * b * a⁻¹ = b := by
        rw [hcomm a haA b hb.1]
        group
      have hmul : D.ρ ⟨u * w, (Subgroup.normalizer _).mul_mem huN hwN⟩ =
          D.ρ ⟨u, huN⟩ * D.ρ ⟨w, hwN⟩ := by
        rw [← map_mul]
        rfl
      have h1 := D.ρ_π ⟨u * w, (Subgroup.normalizer _).mul_mem huN hwN⟩ b hb.2
      rw [hmul, hρu, one_mul] at h1
      rw [h1]
      show D.π (u * w * b * (u * w)⁻¹) = D.π b
      rw [huw', hab]
    intro v hv
    have hspan : D.hat B ≤ LinearMap.ker ((D.ρ ⟨w, hwN⟩).toLinearMap - LinearMap.id) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨b, hb, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe,
        LinearMap.id_apply, sub_eq_zero]
      exact hgen b hb.1
    have := hspan hv
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_eq_zero] at this
  have hsqZ : ∀ a' ∈ B, ∀ b' : G, a'⁻¹ * b' ∈ centerOf (fsuU T V) → b' * b' = 1 := by
    intro a' ha' b' hab'
    have hb' : b' = a' * (a'⁻¹ * b') := by group
    have hζ : (a'⁻¹ * b') * (a'⁻¹ * b') = 1 := by
      rcases S.mem_center_iff.mp hab' with h | h <;> rw [h]
      · group
      · exact S.cfg.z_mul_self
    have hc : a' * (a'⁻¹ * b') = (a'⁻¹ * b') * a' :=
      Subgroup.mem_centralizer_iff.mp hab'.2 a' ha'.2
    rw [hb']
    calc a' * (a'⁻¹ * b') * (a' * (a'⁻¹ * b')) = a' * ((a'⁻¹ * b') * a') * (a'⁻¹ * b') := by
          group
      _ = a' * (a' * (a'⁻¹ * b')) * (a'⁻¹ * b') := by rw [← hc]
      _ = (a' * a') * ((a'⁻¹ * b') * (a'⁻¹ * b')) := by group
      _ = 1 := by rw [hsq a' ha'.1, hζ, one_mul]
  have hB1 : D.hat B ⊓ D.hat Q₁ = ⊥ := hat_inf_eq_bot fun a' ha' b' hb' _ hab' => by
    by_contra hb'Z
    exact S.sq_ne_one_of_mem_Q₁ hb' hb'Z (hsqZ a' ha' b' hab')
  have hB2 : D.hat B ⊓ D.hat Q₂ = ⊥ := hat_inf_eq_bot fun a' ha' b' hb' _ hab' => by
    by_contra hb'Z
    exact S.sq_ne_one_of_mem_Q₂ hb' hb'Z (hsqZ a' ha' b' hab')
  apply S.rho_x_ne hw hwQ
  refine LinearEquiv.ext fun v => ?_
  exact eq_of_trivial_on (S.sup_eq_top hB4 S.card_hat_Q₂ hB2)
    (by rw [sup_comm]; exact S.sup_eq_top hB4 S.card_hat_Q₁ hB1) S.hat_Q_inf
    (D.ρ ⟨w, hwN⟩).toLinearMap (fun _ hv => S.rho_x_Q₂ hw hw₂ hv)
    (fun _ hv => S.rho_x_Q₁ hw hw₁ hv) hfix v

end Setup3

end L1444

end CFSG.Quasithin.H13
