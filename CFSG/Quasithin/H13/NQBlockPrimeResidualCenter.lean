module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellPrime
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPrimeResidual
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup
open scoped commutatorElement

variable {E : Type*} [Group E]

@[expose] def omegaOneCenterOf (p : ℕ) (Q : Subgroup E) : Subgroup E :=
  closure {z | z ∈ Q ⊓ centralizer (Q : Set E) ∧ z ^ p = 1}

theorem omegaOneCenterOf_le (p : ℕ) (Q : Subgroup E) :
    omegaOneCenterOf p Q ≤ Q ⊓ centralizer (Q : Set E) :=
  closure_le _ |>.mpr fun _ hz => hz.1

theorem subset_omegaOneCenterOf {p : ℕ} {Q : Subgroup E} {z : E} (hzQ : z ∈ Q)
    (hzC : z ∈ centralizer (Q : Set E)) (hzp : z ^ p = 1) : z ∈ omegaOneCenterOf p Q :=
  subset_closure ⟨mem_inf.mpr ⟨hzQ, hzC⟩, hzp⟩

theorem pow_eq_one_of_mem_omegaOneCenterOf {p : ℕ} {Q : Subgroup E} {w : E}
    (hw : w ∈ omegaOneCenterOf p Q) : w ^ p = 1 := by
  have hcomm : ∀ a ∈ omegaOneCenterOf p Q, ∀ b ∈ omegaOneCenterOf p Q, a * b = b * a := by
    intro a ha b hb
    have ha' := omegaOneCenterOf_le p Q ha
    have hb' := omegaOneCenterOf_le p Q hb
    exact (mem_centralizer_iff.mp (mem_inf.mp hb').2 a (mem_inf.mp ha').1)
  induction hw using closure_induction with
  | mem z hz => exact hz.2
  | one => exact one_pow p
  | mul a b ha hb iha ihb =>
    rw [(Commute.mul_pow (hcomm a ha b hb) p), iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem conj_mem_omegaOneCenterOf {p : ℕ} {Q : Subgroup E} {g : E}
    (hg : g ∈ normalizer (Q : Set E)) {w : E} (hw : w ∈ omegaOneCenterOf p Q) :
    g * w * g⁻¹ ∈ omegaOneCenterOf p Q := by
  induction hw using closure_induction with
  | mem z hz =>
    obtain ⟨hzQC, hzp⟩ := hz
    obtain ⟨hzQ, hzC⟩ := mem_inf.mp hzQC
    refine subset_omegaOneCenterOf ((mem_normalizer_iff.mp hg z).mp hzQ) ?_ ?_
    · rw [mem_centralizer_iff]
      intro q hq
      have hq' : g⁻¹ * q * g ∈ Q := by
        have := (mem_normalizer_iff.mp hg (g⁻¹ * q * g)).mpr (by simpa [mul_assoc] using hq)
        exact this
      have h1 := mem_centralizer_iff.mp hzC _ hq'
      calc q * (g * z * g⁻¹) = g * ((g⁻¹ * q * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
        _ = g * z * g⁻¹ * q := by group
    · rw [conj_pow, hzp, mul_one, mul_inv_cancel]
  | one => simp
  | mul a b _ _ iha ihb =>
    have := mul_mem iha ihb
    simpa [mul_assoc] using this
  | inv a _ iha =>
    have := inv_mem iha
    simpa [mul_assoc] using this

theorem prime_residual_subnormal_core_center_action [Finite E] {p : ℕ} [hp : Fact p.Prime]
    {X R : Subgroup E} (hX : X.IsSubnormal)
    (hno : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient p X) [R.Normal] (hR : IsPGroup p R)
    (hQR : (CFSG.pCore p X).map X.subtype ≤ R) :
    ⁅omegaOneCenterOf p ((CFSG.pCore p X).map X.subtype), X⁆ = ⊥ ↔
      ⁅omegaOneCenterOf p R, X⁆ = ⊥ := by
  classical
  set Q := (CFSG.pCore p X).map X.subtype with hQdef
  set W := omegaOneCenterOf p Q with hWdef
  set U := omegaOneCenterOf p R with hUdef
  obtain ⟨hRX, hXRQ⟩ :=
    CFSG.QuasithinUnique.Setup.Campbell.prime_residual_subnormal_p_signalizer_action hX hno hR
      le_normalizer_of_normal
  rw [CFSG.QuasithinUnique.Setup.Campbell.pCoreOf_eq] at hXRQ
  have hNQ : normalizer (X : Set E) ≤ normalizer (Q : Set E) :=
    LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore p X)
  have hXNW : X ≤ normalizer (W : Set E) := fun x hx =>
    mem_normalizer_iff.mpr fun w =>
      ⟨fun hw => conj_mem_omegaOneCenterOf (hNQ (le_normalizer hx)) hw,
      fun hw => by
        have := conj_mem_omegaOneCenterOf (hNQ (le_normalizer (inv_mem hx))) hw
        simpa [mul_assoc] using this⟩
  have hRNW : R ≤ normalizer (W : Set E) := fun r hr =>
    mem_normalizer_iff.mpr fun w => ⟨fun hw => conj_mem_omegaOneCenterOf (hNQ (hRX hr)) hw,
      fun hw => by
        have := conj_mem_omegaOneCenterOf (hNQ (hRX (inv_mem hr))) hw
        simpa [mul_assoc] using this⟩
  have hWQ : ∀ w ∈ W, w ∈ Q ∧ ∀ q ∈ Q, q * w = w * q := fun w hw =>
    ⟨(mem_inf.mp (omegaOneCenterOf_le p Q hw)).1,
      mem_centralizer_iff.mp (mem_inf.mp (omegaOneCenterOf_le p Q hw)).2⟩
  have hUR : ∀ u ∈ U, u ∈ R ∧ ∀ r ∈ R, r * u = u * r := fun u hu =>
    ⟨(mem_inf.mp (omegaOneCenterOf_le p R hu)).1,
      mem_centralizer_iff.mp (mem_inf.mp (omegaOneCenterOf_le p R hu)).2⟩
  have hcommXR : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ * r⁻¹ ∈ Q := fun x hx r hr =>
    hXRQ (commutator_mem_commutator hx hr)
  have hWp : IsPGroup p W := by
    have hQp : IsPGroup p Q := CFSG.pCore_isPGroup.map _
    exact hQp.to_le fun w hw => (hWQ w hw).1
  have hUn : ∀ u ∈ U, ∀ g : E, g * u * g⁻¹ ∈ U := fun u hu g =>
    conj_mem_omegaOneCenterOf (by rw [normalizer_eq_top]; exact mem_top g) hu
  constructor
  ·
    intro hW
    have hxW : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ = w := by
      intro x hx w hw
      have h1 : ⁅w, x⁆ ∈ ⁅W, X⁆ := commutator_mem_commutator hw hx
      rw [hW, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      rw [← h1, mul_inv_cancel_right]
    rw [eq_bot_iff, commutator_le]
    intro u hu x hx
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have huR := (hUR u hu).1
    have hd : ∀ y ∈ X, u⁻¹ * (y * u * y⁻¹) = y * u * y⁻¹ * u⁻¹ := fun y _ =>
      (hUR (y * u * y⁻¹) (hUn u hu y)).2 u⁻¹ (inv_mem huR)
    have hmemW : ∀ y ∈ X, u⁻¹ * (y * u * y⁻¹) ∈ W := by
      intro y hy
      have hU' : u⁻¹ * (y * u * y⁻¹) ∈ U := mul_mem (inv_mem hu) (hUn u hu y)
      refine subset_omegaOneCenterOf ?_ ?_ (pow_eq_one_of_mem_omegaOneCenterOf hU')
      · rw [hd y hy]
        exact hcommXR y hy u huR
      · rw [mem_centralizer_iff]
        intro q hq
        exact (hUR _ hU').2 q (hQR hq)
    let f : X →* W :=
      { toFun := fun y => ⟨u⁻¹ * ((y : E) * u * (y : E)⁻¹), hmemW y y.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun y z => Subtype.ext (by
          have hz : (z : E) * u * (z : E)⁻¹ = u * (u⁻¹ * ((z : E) * u * (z : E)⁻¹)) := by group
          have hyz := hxW y y.2 _ (hmemW z z.2)
          change u⁻¹ * ((y : E) * z * u * ((y : E) * z)⁻¹) =
            u⁻¹ * ((y : E) * u * (y : E)⁻¹) * (u⁻¹ * ((z : E) * u * (z : E)⁻¹))
          calc u⁻¹ * ((y : E) * z * u * ((y : E) * z)⁻¹)
              = u⁻¹ * ((y : E) * ((z : E) * u * (z : E)⁻¹) * (y : E)⁻¹) := by group
            _ = u⁻¹ * ((y : E) * (u * (u⁻¹ * ((z : E) * u * (z : E)⁻¹))) * (y : E)⁻¹) := by
                rw [← hz]
            _ = u⁻¹ * ((y : E) * u * (y : E)⁻¹) *
                ((y : E) * (u⁻¹ * ((z : E) * u * (z : E)⁻¹)) * (y : E)⁻¹) := by group
            _ = u⁻¹ * ((y : E) * u * (y : E)⁻¹) * (u⁻¹ * ((z : E) * u * (z : E)⁻¹)) := by
                rw [hyz]) }
    have hker : f.ker = ⊤ := by
      refine hno f.ker ?_
      have hrange : IsPGroup p f.range := (hWp.to_subgroup _)
      exact hrange.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
    have h1 : f ⟨x, hx⟩ = 1 := by
      have : (⟨x, hx⟩ : X) ∈ f.ker := by
        rw [hker]
        exact mem_top _
      exact this
    have h2 : u⁻¹ * (x * u * x⁻¹) = 1 := congrArg Subtype.val h1
    have h3 : x * u * x⁻¹ = u := by
      rw [← mul_left_cancel_iff (a := u⁻¹), h2, inv_mul_cancel]
    calc u * x = x * u * x⁻¹ * x := by rw [h3]
      _ = x * u := by group
  ·
    intro hU
    have hxU : ∀ x ∈ X, ∀ v ∈ U, x * v * x⁻¹ = v := by
      intro x hx v hv
      have h1 : ⁅v, x⁆ ∈ ⁅U, X⁆ := commutator_mem_commutator hv hx
      rw [hU, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      rw [← h1, mul_inv_cancel_right]
    set α : X →* MulAut W := W.normalizerMonoidHom.comp (inclusion hXNW) with hα
    set β : R →* MulAut W := W.normalizerMonoidHom.comp (inclusion hRNW) with hβ
    have hαapp : ∀ (x : X) (w : W), ((α x w : W) : E) = (x : E) * w * (x : E)⁻¹ :=
      fun _ _ => rfl
    have hβapp : ∀ (r : R) (w : W), ((β r w : W) : E) = (r : E) * w * (r : E)⁻¹ :=
      fun _ _ => rfl
    have hcomm : ∀ x r, α x * β r = β r * α x := by
      intro x r
      refine MulEquiv.ext fun w => Subtype.ext ?_
      change ((α x (β r w) : W) : E) = ((β r (α x w) : W) : E)
      rw [hαapp, hβapp, hβapp, hαapp]
      have hv : (r : E) * ((x : E) * w * (x : E)⁻¹) * (r : E)⁻¹ ∈ W := by
        have h1 : (x : E) * w * (x : E)⁻¹ ∈ W := (mem_normalizer_iff.mp (hXNW x.2) w).mp w.2
        exact (mem_normalizer_iff.mp (hRNW r.2) _).mp h1
      have hc := (hWQ _ hv).2 _ (hcommXR x x.2 r r.2)
      calc (x : E) * ((r : E) * w * (r : E)⁻¹) * (x : E)⁻¹
          = ((x : E) * r * (x : E)⁻¹ * (r : E)⁻¹) *
              ((r : E) * ((x : E) * w * (x : E)⁻¹) * (r : E)⁻¹) *
              ((x : E) * r * (x : E)⁻¹ * (r : E)⁻¹)⁻¹ := by group
        _ = (r : E) * ((x : E) * w * (x : E)⁻¹) * (r : E)⁻¹ := by
            rw [hc, mul_inv_cancel_right]
    have hfix : ∀ (x : X) (v : W), (∀ r, β r v = v) → α x v = v := by
      intro x v hv
      have hvU : (v : E) ∈ U := by
        refine subset_omegaOneCenterOf (hQR (hWQ v v.2).1) ?_
          (pow_eq_one_of_mem_omegaOneCenterOf v.2)
        rw [mem_centralizer_iff]
        intro r hr
        have h1 := congrArg Subtype.val (hv ⟨r, hr⟩)
        rw [hβapp] at h1
        calc r * (v : E) = r * v * r⁻¹ * r := by group
          _ = v * r := by rw [h1]
      exact Subtype.ext (by rw [hαapp]; exact hxU x x.2 v hvU)
    have hall := (CFSG.ComponentClassification.OutcomeLocal.prime_residual_commuting_fixed_points
      hWp hno hR α β hcomm).mp hfix
    rw [eq_bot_iff, commutator_le]
    intro w hw x hx
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have h1 := congrArg Subtype.val (hall ⟨x, hx⟩ ⟨w, hw⟩)
    rw [hαapp] at h1
    calc w * x = x * w * x⁻¹ * x := by rw [h1]
      _ = x * w := by group

end CFSG.Quasithin.H13.NQBlock
