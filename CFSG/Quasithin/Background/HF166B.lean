module

public import CFSG.Quasithin.Background.HF166
public import Certificates.Certificate7246

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem psiC24_mul_apply (a b : ↥AutPerm) (w : W11) :
    psiC24 (a * b) w = psiC24 a (psiC24 b w) := by
  rw [map_mul]
  rfl

theorem psiC24_inv_apply (a : ↥AutPerm) (w : W11) : psiC24 a⁻¹ (psiC24 a w) = w := by
  rw [← psiC24_mul_apply, inv_mul_cancel, map_one]
  rfl

theorem psiC24_apply_inv (a : ↥AutPerm) (w : W11) : psiC24 a (psiC24 a⁻¹ w) = w := by
  rw [← psiC24_mul_apply, mul_inv_cancel, map_one]
  rfl

theorem code24_h1606
    [Finite V] (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) {Y : Subgroup (MulAut V)}
    (hYM : Y ≤ M) (hY3 : Nat.card Y = 3) (hY6 : rkIdx (fixV Y) = 6) :
    M ⊓ centSub (fixV Y) = Y := by
  have : Finite (MulAut V) := finite_mulAut V
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).2 hno
    rw [hbot, Subgroup.card_bot] at hY3
    norm_num at hY3
  have hyo : orderOf y = 3 := by
    have hd : orderOf y ∣ 3 := by
      rw [← hY3]
      exact Subgroup.orderOf_dvd_natCard Y hyY
    rcases (Nat.dvd_prime (by norm_num)).1 hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hy1
    · exact h1
  have hYeq : Y = Subgroup.zpowers y := by
    symm
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hyY)
    rw [Nat.card_zpowers, hyo, hY3]
  subst hYeq
  obtain ⟨e, he⟩ := code24_std h
  have hMR : ∀ x ∈ M, congrHom e x ∈ psiC24.range := fun x hx =>
    map_le_of_normalizer hLM he normalizer_rhoC11_autPerm ((Subgroup.zpowers_le).2 hx)
      ⟨x, Subgroup.mem_zpowers x, rfl⟩
  set φ3 := T24s3.toSub AutPerm (T24s3.mem_autPerm (fun _ _ h => h) T24s3_ok.2.2) with hφ3
  have hsyl3 := card_T24sp (T := T24s3) (by norm_num : Nat.Prime 3) (n := 3) T24s3_ok.2.1
    (by norm_num : (244823040 : ℕ) = 3 ^ 3 * 9067520) (by norm_num)
  obtain ⟨g, s, -, hgs⟩ := exists_conj_elemModel psiC24 (rhoC11_injective _ _) φ3
    (T24s3.toSub_injective _ _) hsyl3 e (hMR y (hYM (Subgroup.mem_zpowers y))) hyo
  set e1 := twistEquiv e psiC24 g with he1
  have hy1 : ∀ v, e1 (y v) = psiC24 (φ3 s) (e1 v) := apply_of_congrHom_eq hgs
  have hact : ∀ m : ℕ, psiC24 (φ3 s) (toW 11 m) = toW 11 (actC11 (T24s3.arr s) m) :=
    fun m => rhoC11_toW AutPerm le_rfl _ (T24s3.hasArr_toSub _ _ s) m
  have hX1 : ∀ m < 2 ^ 11, (MaskCoords.ofEquiv e1).vm m ∈ fixV (Subgroup.zpowers y) ↔
      actC11 (T24s3.arr s) m = m := by
    intro m hm
    rw [mem_fixV_zpowers_iff, MaskCoords.ofEquiv_vm]
    have h1 : e1 (y (e1.symm (toW 11 m))) = toW 11 (actC11 (T24s3.arr s) m) := by
      rw [hy1, MulEquiv.apply_symm_apply, hact m]
    have h2 : y (e1.symm (toW 11 m)) = e1.symm (toW 11 (actC11 (T24s3.arr s) m)) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    rw [h2]
    constructor
    · intro h3
      exact toW_inj (actC11_lt _ _) hm (e1.symm.injective h3)
    · intro h3
      rw [h3]
  have hcard : Nat.card (fixV (Subgroup.zpowers y)) = (codeFixArr (T24s3.arr s)).length :=
    (MaskCoords.ofEquiv e1).card_eq _ _ fun m hm => (hX1 m hm).trans (by simp)
  have h32 : (codeFixArr (T24s3.arr s)).length = 2 ^ 5 := by
    have hr := (MaskCoords.ofEquiv e1).rkIdx_of_card hcard
    have hpow := card_eq_two_pow (MaskCoords.ofEquiv e1).sq_eq_one (fixV (Subgroup.zpowers y))
    rw [hcard] at hpow
    rw [hY6, hpow, Nat.log_pow (by norm_num)] at hr
    rw [hpow, show rk ↥(fixV (Subgroup.zpowers y)) = 5 by omega]
  obtain ⟨hA, -, hAok, hAconj⟩ := Certificates.certificate7246 s h32
  obtain ⟨σh, hσhA, hσh⟩ := exists_of_inAutOK hAok
  set a : ↥AutPerm := ⟨σh, hσhA⟩ with ha
  set σ0 : ↥AutPerm := a * φ3 s * a⁻¹ with hσ0def
  have h0 : HasArr (σ0 : Equiv.Perm (Fin 24)) s0Arr := by
    have hc : ∀ i < 24, hA[(T24s3.arr s)[i]!]! = s0Arr[hA[i]!]! := by
      intro i hi
      have := List.all_eq_true.1 hAconj i (List.mem_range.2 hi)
      simpa using this
    have hs : HasArr ((φ3 s : ↥AutPerm) : Equiv.Perm (Fin 24)) (T24s3.arr s) :=
      T24s3.hasArr_toSub _ _ s
    intro j
    have hj : σh (σh⁻¹ j) = j := by simp
    have hσ0j : (σ0 : Equiv.Perm (Fin 24)) j =
        σh ((φ3 s : Equiv.Perm (Fin 24)) (σh⁻¹ j)) := rfl
    rw [hσ0j, hσh, hs, hc _ (σh⁻¹ j).2, ← hσh (σh⁻¹ j), hj]
  have hσ0apply : ∀ w, psiC24 σ0 w = psiC24 a (psiC24 (φ3 s) (psiC24 a⁻¹ w)) := fun w => by
    rw [hσ0def, psiC24_mul_apply, psiC24_mul_apply]
  apply le_antisymm
  · rintro x ⟨hxM, hxC⟩
    obtain ⟨k, hk⟩ := hMR x hxM
    set k1 := g * k * g⁻¹ with hk1
    have hx0 : ∀ v, e (x v) = psiC24 k (e v) := apply_of_congrHom_eq hk.symm
    have hx1 : ∀ v, e1 (x v) = psiC24 k1 (e1 v) := by
      intro v
      show psiC24 g (e (x v)) = psiC24 (g * k * g⁻¹) (psiC24 g (e v))
      rw [hx0, psiC24_mul_apply, psiC24_mul_apply, psiC24_inv_apply]
    set σ := a * k1 * a⁻¹ with hσdef
    have hfixσ : ∀ w, psiC24 σ0 w = w → psiC24 σ w = w := by
      intro w hw
      set w' := psiC24 a⁻¹ w with hw'
      have hsw : psiC24 (φ3 s) w' = w' := by
        have := congrArg (psiC24 a⁻¹) ((hσ0apply w).symm.trans hw)
        rwa [psiC24_inv_apply] at this
      have hv : y (e1.symm w') = e1.symm w' := by
        apply e1.injective
        rw [hy1, MulEquiv.apply_symm_apply, hsw]
      have hxv : x (e1.symm w') = e1.symm w' :=
        mem_centSub.1 hxC _ (mem_fixV_zpowers_iff.2 hv)
      have hkw : psiC24 k1 w' = w' := by
        have := hx1 (e1.symm w')
        rw [hxv, MulEquiv.apply_symm_apply] at this
        exact this.symm
      rw [hσdef, psiC24_mul_apply, psiC24_mul_apply, ← hw', hkw, hw', psiC24_apply_inv]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_s0 h0 hfixσ)
    have hkj : k1 = (φ3 s) ^ j := by
      have h1 : a * k1 * a⁻¹ = a * (φ3 s) ^ j * a⁻¹ := by
        rw [← hσdef, ← hj, hσ0def, conj_zpow]
      calc k1 = a⁻¹ * (a * k1 * a⁻¹) * a := by group
        _ = a⁻¹ * (a * (φ3 s) ^ j * a⁻¹) * a := by rw [h1]
        _ = (φ3 s) ^ j := by group
    have hyj : ∀ v, e1 ((y ^ j) v) = psiC24 ((φ3 s) ^ j) (e1 v) :=
      apply_of_congrHom_eq ((map_zpow (congrHom e1) y j).trans
        ((congrArg (fun z => z ^ j) hgs).trans (map_zpow psiC24 (φ3 s) j).symm))
    refine Subgroup.mem_zpowers_iff.2 ⟨j, MulEquiv.ext fun v => e1.injective ?_⟩
    rw [hyj, hx1, hkj]
  · intro x hx
    exact ⟨hYM hx, mem_centSub.2 fun v hv => hv x hx⟩

end CFSG.Quasithin.H.Mathieu
