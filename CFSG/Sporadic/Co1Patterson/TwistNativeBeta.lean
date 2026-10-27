module

public import CFSG.Sporadic.Co1Patterson.TwistNativeCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight (ind bNat qNat transNat)

@[expose] noncomputable def betaLin : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  LinearMap.id + (q₀.polarBilin.flip (bv 17)).smulRight (bv 17)

theorem betaLin_apply (v : Fin 8 → ZMod 2) :
    betaLin v = v + QuadraticMap.polar q₀ v (bv 17) • bv 17 := rfl

theorem betaLin_bv (c : ℕ) : betaLin (bv c) = bv (transNat 17 c) := by
  rw [betaLin_apply, polar_q₀_bv, transNat]
  cases h : bNat c 17
  · simp [ind]
  · simp [ind, bv_xor]

set_option maxRecDepth 100000 in
theorem transNat_transNat : ∀ c < 256, transNat 17 (transNat 17 c) = c := by decide

set_option maxRecDepth 100000 in
theorem qNat_transNat : ∀ c < 256, qNat (transNat 17 c) = qNat c := by decide

theorem betaLin_betaLin (v : Fin 8 → ZMod 2) : betaLin (betaLin v) = v := by
  obtain ⟨c, hc, rfl⟩ := exists_bv v
  rw [betaLin_bv, betaLin_bv, transNat_transNat c hc]

theorem q₀_betaLin (v : Fin 8 → ZMod 2) : q₀ (betaLin v) = q₀ v := by
  obtain ⟨c, hc, rfl⟩ := exists_bv v
  rw [betaLin_bv, q₀_bv, q₀_bv, qNat_transNat c hc]

theorem bil₀_betaLin (u v : Fin 8 → ZMod 2) : bil₀ (betaLin u) (betaLin v) = bil₀ u v := by
  simp only [bil₀, QuadraticMap.polar]
  rw [← map_add, q₀_betaLin, q₀_betaLin, q₀_betaLin]

@[expose] noncomputable def betaE : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  LinearEquiv.ofInvolutive betaLin betaLin_betaLin

theorem hasCols_beta : HasCols betaLin betaCols := fun k hk => by
  rw [betaLin_bv, betaCols, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getElem_range]

@[expose] noncomputable def conjβ : L₀ ≃* L₀ := Bridge.omegaEquiv betaE fun v => q₀_betaLin v

theorem conjβ_apply (l : L₀) (v : Fin 8 → ZMod 2) :
    ((conjβ l : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) v =
      betaLin ((l : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (betaLin v)) := rfl

theorem conjβ_conjβ (l : L₀) : conjβ (conjβ l) = l := by
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  rw [conjβ_apply, conjβ_apply, betaLin_betaLin, betaLin_betaLin]

theorem hasCols_conjβ {l : L₀} {m : List ℕ}
    (h : HasCols ((l : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) m) :
    HasCols (((conjβ l : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
      (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (colsMul (colsMul betaCols m) betaCols) :=
  fun k hk => ((hasCols_beta.comp h).comp hasCols_beta) k hk

section Twist

variable {H : Type} [Group H] (S : ExtraspecialTypeSystem 8 L₀ L₀.subtype q₀ bil₀ H)

theorem phi_eq_one_of_conjβ {h : H} (hh : conjβ (S.φ h) = 1) : S.φ h = 1 :=
  conjβ.map_eq_one_iff.1 hh

theorem conjβ_eq_one_of_phi {h : H} (hh : S.φ h = 1) : conjβ (S.φ h) = 1 := by
  rw [hh, map_one]

@[expose] noncomputable def betaSystem : ExtraspecialTypeSystem 8 L₀ L₀.subtype q₀ bil₀ H where
  φ := conjβ.toMonoidHom.comp S.φ
  φ_surj := conjβ.surjective.comp S.φ_surj
  z := S.z
  vec h := betaLin (S.vec h)
  z_mul_self := S.z_mul_self
  z_ne_one := S.z_ne_one
  z_comm := S.z_comm
  φ_z := conjβ_eq_one_of_phi S S.φ_z
  vec_mul p q hp hq := by
    rw [S.vec_mul p q (phi_eq_one_of_conjβ S hp) (phi_eq_one_of_conjβ S hq), map_add]
  vec_eq_zero q hq := by
    change betaE (S.vec q) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact S.vec_eq_zero q (phi_eq_one_of_conjβ S hq)
  vec_conj c q hq := by
    change betaLin (S.vec (c * q * c⁻¹)) =
      betaLin (((S.φ c : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
        (betaLin (betaLin (S.vec q))))
    rw [betaLin_betaLin, S.vec_conj c q (phi_eq_one_of_conjβ S hq)]
    rfl
  vec_surj w := by
    obtain ⟨q, hq, hv⟩ := S.vec_surj (betaLin w)
    exact ⟨q, conjβ_eq_one_of_phi S hq, by
      rw [hv, betaLin_betaLin]⟩
  mul_self_eq_one_iff q hq := by
    rw [q₀_betaLin]
    exact S.mul_self_eq_one_iff q (phi_eq_one_of_conjβ S hq)
  mul_self_eq_z_iff q hq := by
    rw [q₀_betaLin]
    exact S.mul_self_eq_z_iff q (phi_eq_one_of_conjβ S hq)
  comm_eq_one_iff p q hp hq := by
    rw [bil₀_betaLin]
    exact S.comm_eq_one_iff p q (phi_eq_one_of_conjβ S hp) (phi_eq_one_of_conjβ S hq)
  comm_eq_z_iff p q hp hq := by
    rw [bil₀_betaLin]
    exact S.comm_eq_z_iff p q (phi_eq_one_of_conjβ S hp) (phi_eq_one_of_conjβ S hq)
  center_eq q hq hc :=
    S.center_eq q (phi_eq_one_of_conjβ S hq) fun p hp => hc p (conjβ_eq_one_of_phi S hp)

theorem betaSystem_φ (h : H) : (betaSystem S).φ h = conjβ (S.φ h) := rfl

end Twist


noncomputable abbrev typeSystemβ :
    ExtraspecialTypeSystem 8 L₀ L₀.subtype q₀ bil₀
      (centralizer ({aNC} : Set NativeSporadic.Co1)) :=
  betaSystem typeSystemC

theorem phi_h4pH : typeSystemC.φ h4pH = conjβ (typeSystemC.φ h4H) :=
  Subtype.ext (LinearEquiv.toLinearMap_injective
    (HasCols.ext hasCols_h4pH (hasCols_conjβ hasCols_h4H)))

theorem h4OK_parts :
    (∀ c < 256, Native.mul (Native.mul (twRow h4Idx) (yprodRow c))
        (Native.mul (twRow h4Idx) (yprodRow c)) ≠ Native.one ∧
      Native.mul (Native.mul (Native.mul (twRow h4Idx) (yprodRow c)) iotaARows)
        (Native.mul (Native.mul (twRow h4Idx) (yprodRow c)) iotaARows) ≠ Native.one) ∧
    Native.mul (twRow h4pIdx) (twRow h4pIdx) = Native.one := by
  have h := tw_h4_check
  simp only [h4OK, Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

theorem rep_h4H : MRep (twRow h4Idx) (centEmb h4H) := by
  rw [h4H, centEmb_twH elemsOK_parts.2.2.1.2]
  exact rep_twG h4Idx

theorem h4pH_mul_self : h4pH * h4pH = 1 := by
  have hrep : MRep (twRow h4pIdx) (centEmb h4pH) := by
    rw [h4pH, centEmb_twH elemsOK_parts.2.2.2.2]
    exact rep_twG h4pIdx
  apply centEmb_injective
  have h := hrep.mul hrep
  rw [h4OK_parts.2] at h
  rw [map_mul, map_one]
  exact h.eq MRep.one

theorem h4_coset_sq_ne_one {q : centralizer ({aNC} : Set NativeSporadic.Co1)}
    (hq : typeSystemC.φ q = 1) : (h4H * q) * (h4H * q) ≠ 1 := by
  obtain ⟨c, hcq⟩ : ∃ c, c = enc (typeSystemC.vec q) := ⟨_, rfl⟩
  have hc : c < 256 := hcq ▸ enc_lt (typeSystemC.vec q)
  have hz : centEmb typeSystemC.z = aG := centEmb_zM
  have hv4 : CFSG.Sporadic.Co1.InvNative.validRows (twRow h4Idx) = true :=
    dagOK_parts.2.2.2.2 h4Idx (by decide)
  have hvy := dagOK_parts.2.2.2.1 c hc
  intro h
  have he := congrArg centEmb h
  rw [map_one] at he
  rcases eq_yprodH_of_phi hq with h1 | h1 <;> rw [h1, ← hcq] at he
  · have hX := (rep_h4H.mul (rep_yprodG c)).mul (rep_h4H.mul (rep_yprodG c))
    refine (h4OK_parts.1 c hc).1 ((rows_eq_iff hX MRep.one ?_ validRows_one).2 ?_)
    · exact valid_mul (valid_mul hv4 hvy) (valid_mul hv4 hvy)
    · simpa only [map_mul, centEmb_yprodH] using he
  · have hX := ((rep_h4H.mul (rep_yprodG c)).mul rep_iotaA).mul
      ((rep_h4H.mul (rep_yprodG c)).mul rep_iotaA)
    refine (h4OK_parts.1 c hc).2 ((rows_eq_iff hX MRep.one ?_ validRows_one).2 ?_)
    · exact valid_mul (valid_mul (valid_mul hv4 hvy) dagOK_parts.2.1)
        (valid_mul (valid_mul hv4 hvy) dagOK_parts.2.1)
    · simp only [map_mul, centEmb_yprodH, hz, mul_assoc] at he ⊢
      exact he

theorem not_exists_compat : ¬ ∃ e : centralizer ({aNC} : Set NativeSporadic.Co1) ≃*
    centralizer ({aNC} : Set NativeSporadic.Co1), ∀ x, typeSystemβ.φ (e x) = typeSystemC.φ x := by
  rintro ⟨e, he⟩
  have h1 := he (e.symm h4pH)
  rw [MulEquiv.apply_symm_apply, betaSystem_φ, phi_h4pH, conjβ_conjβ] at h1
  have hq : typeSystemC.φ (h4H⁻¹ * e.symm h4pH) = 1 := by
    rw [map_mul, map_inv, ← h1, inv_mul_cancel]
  apply h4_coset_sq_ne_one hq
  rw [mul_inv_cancel_left, ← map_mul e.symm, h4pH_mul_self, map_one]

end CFSG.Sporadic.Co1Patterson.TwistNative
