module

public import CFSG.SignalizerFunctorTheorem.NonLocal.AbelianLift
public import CFSG.GroupTheory.QuaternionAutPrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.SignalizerFunctorTheorem.NonLocal

variable {F V G : Type*} [Field F] [IsAlgClosed F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Group G]

theorem q8_eq_zQ_or_sq_eq_zQ {Q : Subgroup G} (eQ : ↥Q ≃* QuaternionGroup 2) {zQ : ↥Q}
    (hzQ : eQ zQ = QuaternionGroup.a 2) {h : ↥Q} (hh : h ≠ 1) :
    h = zQ ∨ h * h = zQ := by
  have hh' : eQ h ≠ 1 := by
    intro h1
    apply hh
    apply eQ.injective
    rw [h1, map_one]
  rcases CFSG.GroupTheory.quaternion_eq_a_two_or_sq_eq_a_two hh' with h' | h'
  · left
    apply eQ.injective
    rw [h', hzQ]
  · right
    apply eQ.injective
    rw [map_mul, ← pow_two, h', hzQ]

theorem eight_le_finrank_of_q8_inverts
    (ρ : G →* (V ≃ₗ[F] V))
    {E Q : Subgroup G} [Finite E]
    (hEab : IsMulCommutative E)
    (hEodd : Odd (Nat.card E))
    (hEchar : (Nat.card E : F) ≠ 0)
    (hEinj : ∀ e ∈ E, ρ e = 1 → e = 1)
    (eQ : ↥Q ≃* QuaternionGroup 2)
    (hQE : ∀ q ∈ Q, ∀ e ∈ E, q * e * q⁻¹ ∈ E)
    (zQ : ↥Q) (hzQ : eQ zQ = QuaternionGroup.a 2)
    (hinv : ∀ e ∈ E, (zQ : G) * e * (zQ : G)⁻¹ = e⁻¹)
    (hEne : E ≠ ⊥) :
    8 ≤ Module.finrank F V := by
  classical
  let ρEnd : G →* Module.End F V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp ρ
  obtain ⟨e₀, he₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
  let T : Module.End F V := ρEnd (e₀ : G) - 1
  have hT : T ≠ 0 := by
    intro hT0
    have h1 : ρEnd (e₀ : G) = 1 := sub_eq_zero.mp hT0
    have h2 : ρ (e₀ : G) = 1 := by
      ext v
      have := congrArg (fun f : Module.End F V => f v) h1
      simpa [ρEnd] using this
    exact he₀ne (Subtype.ext (hEinj (e₀ : G) e₀.2 h2))
  obtain ⟨χ, v, hχeig, hTv⟩ :=
    exists_jointEigenvector_apply_ne_zero ρEnd E hEab hEchar T hT
  have hv : v ≠ 0 := by
    rintro rfl
    exact hTv (map_zero T)
  have hχ : IsWeight ρEnd E χ := ⟨v, hv, hχeig⟩
  have hχnt : ∃ a : E, χ a ≠ 1 := by
    refine ⟨e₀, ?_⟩
    intro hχ0
    apply hTv
    have h1 : ρEnd (e₀ : G) v = v := by
      rw [hχeig e₀, hχ0, one_smul]
    simp [T, h1]
  let weightShift : (E → F) → ↥Q → E → F :=
    fun χ q e => χ ⟨((q⁻¹ : ↥Q) : G) * (e : G) * (((q⁻¹ : ↥Q) : G))⁻¹,
      hQE ((q⁻¹ : ↥Q) : G) (Q.inv_mem q.2) (e : G) e.2⟩
  have weightShift_isWeight : ∀ q : ↥Q, IsWeight ρEnd E (weightShift χ q) := by
    intro q
    refine ⟨ρEnd (q : G) v, ?_, ?_⟩
    · have hqv : (ρ (q : G)) v ≠ 0 :=
        (LinearEquiv.map_ne_zero_iff (ρ (q : G))).mpr hv
      simpa [ρEnd] using hqv
    · intro e
      let x : G := ((q⁻¹ : ↥Q) : G) * (e : G) * (((q⁻¹ : ↥Q) : G))⁻¹
      have hx : x ∈ E :=
        hQE ((q⁻¹ : ↥Q) : G) (Q.inv_mem q.2) (e : G) e.2
      have hgroup : (q : G) * x = (e : G) * (q : G) := by
        simp only [x, Subgroup.coe_inv]
        group
      have hmul : ρEnd (e : G) * ρEnd (q : G) = ρEnd (q : G) * ρEnd x := by
        rw [← map_mul, ← map_mul, hgroup]
      calc
        ρEnd (e : G) (ρEnd (q : G) v)
            = (ρEnd (e : G) * ρEnd (q : G)) v := (Module.End.mul_apply _ _ _).symm
        _ = (ρEnd (q : G) * ρEnd x) v := by rw [hmul]
        _ = ρEnd (q : G) (ρEnd x v) := Module.End.mul_apply _ _ _
        _ = ρEnd (q : G) (χ ⟨x, hx⟩ • v) := by rw [hχeig ⟨x, hx⟩]
        _ = χ ⟨x, hx⟩ • ρEnd (q : G) v := by rw [map_smul]
  let w : ↥Q → {χ : E → F // IsWeight ρEnd E χ} :=
    fun q => ⟨weightShift χ q, weightShift_isWeight q⟩
  have hw : Function.Injective w := by
    intro q1 q2 hq
    have hχeq : weightShift χ q1 = weightShift χ q2 := congrArg Subtype.val hq
    by_contra hne
    let h : ↥Q := q2⁻¹ * q1
    have hh1 : h ≠ 1 := by
      intro h1
      apply hne
      have h2 : (q2⁻¹ * q1 : ↥Q) = 1 := h1
      have := congrArg (fun x : ↥Q => q2 * x) h2
      simpa [mul_assoc] using this
    have hinv_h : ∀ a : E,
        χ ⟨(h : G) * (a : G) * (h : G)⁻¹,
          hQE (h : G) h.2 (a : G) a.2⟩ = χ a := by
      intro a
      let e : E := ⟨(q1 : G) * (a : G) * (q1 : G)⁻¹,
        hQE (q1 : G) q1.2 (a : G) a.2⟩
      have h1 := congrFun hχeq e
      have hL : χ ⟨((q1⁻¹ : ↥Q) : G) * (e : G) * (((q1⁻¹ : ↥Q) : G))⁻¹,
          hQE ((q1⁻¹ : ↥Q) : G) (Q.inv_mem q1.2) (e : G) e.2⟩ = χ a := by
        congr 1
        apply Subtype.ext
        simp only [e, Subgroup.coe_inv]
        group
      have hR : χ ⟨((q2⁻¹ : ↥Q) : G) * (e : G) * (((q2⁻¹ : ↥Q) : G))⁻¹,
          hQE ((q2⁻¹ : ↥Q) : G) (Q.inv_mem q2.2) (e : G) e.2⟩ =
          χ ⟨(h : G) * (a : G) * (h : G)⁻¹,
            hQE (h : G) h.2 (a : G) a.2⟩ := by
        congr 1
        apply Subtype.ext
        simp only [e, h, Subgroup.coe_inv, Subgroup.coe_mul]
        group
      exact ((hL.symm.trans h1).trans hR).symm
    have hinv_z : ∀ a : E,
        χ ⟨(zQ : G) * (a : G) * (zQ : G)⁻¹,
          hQE (zQ : G) zQ.2 (a : G) a.2⟩ = χ a := by
      intro a
      rcases q8_eq_zQ_or_sq_eq_zQ eQ hzQ hh1 with hz | hz
      · rw [← hz]
        exact hinv_h a
      · rw [← hz]
        have h1 : (⟨((h * h : ↥Q) : G) * (a : G) * (((h * h : ↥Q) : G))⁻¹,
            hQE ((h * h : ↥Q) : G) (Q.mul_mem h.2 h.2) (a : G) a.2⟩ : E) =
            ⟨(h : G) * ((h : G) * (a : G) * (h : G)⁻¹) * (h : G)⁻¹,
              hQE (h : G) h.2 ((h : G) * (a : G) * (h : G)⁻¹)
                (hQE (h : G) h.2 (a : G) a.2)⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          group
        rw [h1]
        rw [hinv_h ⟨(h : G) * (a : G) * (h : G)⁻¹,
          hQE (h : G) h.2 (a : G) a.2⟩]
        exact hinv_h a
    have hχinv : ∀ a : E, χ a = (χ a)⁻¹ := by
      intro a
      have hza : (⟨(zQ : G) * (a : G) * (zQ : G)⁻¹,
          hQE (zQ : G) zQ.2 (a : G) a.2⟩ : E) = a⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_inv]
        exact hinv (a : G) a.2
      calc
        χ a = χ ⟨(zQ : G) * (a : G) * (zQ : G)⁻¹,
            hQE (zQ : G) zQ.2 (a : G) a.2⟩ := (hinv_z a).symm
        _ = χ a⁻¹ := by rw [hza]
        _ = (χ a)⁻¹ := IsWeight.inv hχ a
    have hχsq : ∀ a : E, χ a * χ a = 1 := by
      intro a
      nth_rewrite 1 [hχinv a]
      exact inv_mul_cancel₀ (IsWeight.ne_zero hχ a)
    have hχone : ∀ a : E, χ a = 1 := by
      intro a
      have hodd : Odd (orderOf a) := by
        simpa only [Subgroup.orderOf_coe] using
          Odd.of_dvd_nat hEodd (Subgroup.orderOf_dvd_natCard E a.2)
      have hcop : Nat.Coprime 2 (orderOf a) := Nat.coprime_two_left.mpr hodd
      have hdvd2 : orderOf (χ a) ∣ 2 := by
        apply orderOf_dvd_of_pow_eq_one
        rw [pow_two]
        exact hχsq a
      have hpow : χ a ^ orderOf a = 1 := by
        have h := hχ.pow a (orderOf a)
        rw [pow_orderOf_eq_one, IsWeight.one hχ] at h
        exact h.symm
      have hdvdn : orderOf (χ a) ∣ orderOf a := orderOf_dvd_of_pow_eq_one hpow
      have hdvd1 : orderOf (χ a) ∣ 1 := by
        have := Nat.dvd_gcd hdvd2 hdvdn
        rwa [hcop.gcd_eq_one] at this
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
    obtain ⟨a, ha⟩ := hχnt
    exact ha (hχone a)
  have hcardQ : Nat.card ↥Q = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨hfinW, hcardW⟩ := finite_card_weights ρEnd E hEab
  have : Finite ↥Q := Finite.of_injective (eQ : ↥Q → QuaternionGroup 2) eQ.injective
  let : Finite {χ : E → F // IsWeight ρEnd E χ} := hfinW
  have hle : Nat.card ↥Q ≤ Nat.card {χ : E → F // IsWeight ρEnd E χ} :=
    Nat.card_le_card_of_injective w hw
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
