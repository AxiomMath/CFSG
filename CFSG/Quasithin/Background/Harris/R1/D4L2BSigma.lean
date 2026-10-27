module

public import CFSG.Quasithin.Background.Harris.R1.D4Q2Aut
public import CFSG.Quasithin.Background.Harris.R1.D4Klein

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.Quasithin.D4Hex

variable {G : Type*} [Group G]

theorem exists_s_action [Finite G] {Q : Subgroup G}
    (ε : ↥Q ≃* ↥Q2) {s T : G}
    (hKc : ∀ k ∈ Kc, (∀ q ∈ Q2, k * q = q * k) → k = 1)
    (hsQ : ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) (hTQ : ∀ q ∈ Q, T * q * T⁻¹ ∈ Q)
    (hT : ∀ q q' : ↥Q, (q' : G) = T * q * T⁻¹ → (ε q' : D) = zeD * (ε q : D) * zeD⁻¹)
    (hcomm : s * T = T * s) (hs3 : s * s * s = 1) (hnt : ∃ q ∈ Q, s * q * s⁻¹ ≠ q) :
    ∃ s' : G, (s' = s ∨ s' = s⁻¹) ∧ ∀ q q' : ↥Q, (q' : G) = s' * q * s'⁻¹ →
      (ε q' : D) = s0D * (ε q : D) * s0D⁻¹ := by
  let f : ↥Q →* ↥Q :=
    { toFun := fun q => ⟨s * q * s⁻¹, hsQ q q.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hfinj : Function.Injective f := by
    intro a b hab
    have h' : s * (a : G) * s⁻¹ = s * (b : G) * s⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  have : Finite ↥Q := inferInstance
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  let conjQ : ↥Q ≃* ↥Q := MulEquiv.ofBijective f hfbij
  have hconjQ : ∀ q : ↥Q, ((conjQ q : ↥Q) : G) = s * q * s⁻¹ := fun q => rfl
  let α : ↥Q2 ≃* ↥Q2 := ε.symm.trans (conjQ.trans ε)
  have hα_apply : ∀ x : ↥Q, (α (ε x) : D) = (ε (conjQ x) : D) := by
    intro x
    simp [α]
  have hα : ∀ (q : D) (hq : q ∈ Q2),
      (α ⟨zeD * q * zeD⁻¹, zeD_conj_mem hq⟩ : D) = zeD * (α ⟨q, hq⟩ : D) * zeD⁻¹ := by
    intro q2 hq2
    set x : ↥Q := ε.symm ⟨q2, hq2⟩ with hx
    have hεx : (ε x : D) = q2 := by simp [hx]
    have hxx' : (⟨zeD * q2 * zeD⁻¹, zeD_conj_mem hq2⟩ : ↥Q2) =
        ε ⟨T * x * T⁻¹, hTQ x x.2⟩ := by
      apply Subtype.ext
      rw [hT x ⟨T * x * T⁻¹, hTQ x x.2⟩ rfl, hεx]
    rw [hxx']
    have h1 : (α ⟨q2, hq2⟩ : D) = (ε (conjQ x) : D) := by
      rw [← hα_apply x]
      congr 2
      exact Subtype.ext hεx.symm
    rw [hα_apply, h1]
    have := hT (conjQ x) (conjQ ⟨T * x * T⁻¹, hTQ x x.2⟩) (by
      rw [hconjQ, hconjQ]
      show s * (T * (x : G) * T⁻¹) * s⁻¹ = T * (s * (x : G) * s⁻¹) * T⁻¹
      calc s * (T * (x : G) * T⁻¹) * s⁻¹ = (s * T) * x * (s * T)⁻¹ := by group
        _ = (T * s) * x * (T * s)⁻¹ := by rw [hcomm]
        _ = _ := by group)
    exact this
  obtain ⟨k, hk, hkα⟩ := exists_Kc_of_aut α hα
  have hact : ∀ x : ↥Q, (ε (conjQ x) : D) = k * (ε x : D) * k⁻¹ := by
    intro x
    rw [← hα_apply x]
    exact hkα _ (ε x).2
  have hk3 : k * k * k = 1 := by
    refine hKc _ (Kc.mul_mem (Kc.mul_mem hk hk) hk) fun q hq => ?_
    set x : ↥Q := ε.symm ⟨q, hq⟩ with hx
    have hεx : (ε x : D) = q := by simp [hx]
    have e1 := hact x
    have e2 := hact (conjQ x)
    have e3 := hact (conjQ (conjQ x))
    have h3 : (conjQ (conjQ (conjQ x)) : ↥Q) = x := by
      apply Subtype.ext
      rw [hconjQ, hconjQ, hconjQ]
      calc s * (s * (s * (x : G) * s⁻¹) * s⁻¹) * s⁻¹ = (s * s * s) * x * (s * s * s)⁻¹ := by group
        _ = x := by rw [hs3]; group
    rw [h3, e2, e1, hεx] at e3
    have : (q : D) * (k * k * k) = (k * k * k) * q := by
      calc (q : D) * (k * k * k) = (k * (k * (k * q * k⁻¹) * k⁻¹) * k⁻¹) * (k * k * k) := by
            rw [← e3]
        _ = (k * k * k) * q := by group
    exact this.symm
  have hk1 : k ≠ 1 := by
    intro hk1
    obtain ⟨q, hq, hne⟩ := hnt
    refine hne ?_
    have := hact ⟨q, hq⟩
    rw [hk1] at this
    simp only [one_mul, inv_one, mul_one] at this
    have h2 : conjQ ⟨q, hq⟩ = ⟨q, hq⟩ := ε.injective (Subtype.ext this)
    exact congrArg Subtype.val h2
  rcases Kc_eq_s0D_of_cube hk hk3 hk1 with rfl | rfl
  · refine ⟨s, Or.inl rfl, fun q q' hq' => ?_⟩
    have : q' = conjQ q := Subtype.ext hq'
    rw [this, hact]
  · refine ⟨s⁻¹, Or.inr rfl, fun q q' hq' => ?_⟩
    have hq : conjQ q' = q := by
      apply Subtype.ext
      rw [hconjQ, hq']
      group
    have := hact q'
    rw [hq] at this
    rw [this]
    group

theorem exists_adjust {V : Subgroup G} (h4 : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1) {s R0 : G}
    (hs : s ∈ Subgroup.normalizer (V : Set G)) (hR : R0 ∈ Subgroup.normalizer (V : Set G))
    (hs3 : s * s * s = 1) (hR2 : R0 * R0 = 1) {w : G} (hw : w ∈ V) (hsw : s * w * s⁻¹ ≠ w)
    (hc : R0 * s * R0⁻¹ * s ∈ V) :
    ∃ u ∈ V, (s * u) * (s * u) * (s * u) = 1 ∧ R0 * (s * u) * R0⁻¹ * (s * u) = 1 := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  have hRi : R0⁻¹ = R0 := inv_eq_of_mul_eq_one_right hR2
  have hsV : ∀ v ∈ V, s * v * s⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.mp hs v).mp hv
  have hhN : s⁻¹ * R0 ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) hR
  have hhV : ∀ v ∈ V, (s⁻¹ * R0) * v * (s⁻¹ * R0)⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hhN v).mp hv
  obtain ⟨w', hw'V, hw'⟩ : ∃ w' ∈ V, (s⁻¹ * R0) * w' * (s⁻¹ * R0)⁻¹ ≠ w' := by
    by_contra hcon
    push Not at hcon
    apply hsw
    have key : ∀ v ∈ V, R0 * v * R0⁻¹ = s * v * s⁻¹ := by
      intro v hv
      calc R0 * v * R0⁻¹ = s * ((s⁻¹ * R0) * v * (s⁻¹ * R0)⁻¹) * s⁻¹ := by group
        _ = s * v * s⁻¹ := by rw [hcon v hv]
    have hw1 : s * w * s⁻¹ ∈ V := hsV w hw
    have e1 : s * (s * w * s⁻¹) * s⁻¹ = w := by
      rw [← key _ hw1, ← key _ hw, hRi]
      calc R0 * (R0 * w * R0) * R0 = (R0 * R0) * w * (R0 * R0) := by group
        _ = w := by rw [hR2]; group
    calc s * w * s⁻¹ = s * (s * (s * w * s⁻¹) * s⁻¹) * s⁻¹ := by rw [e1]
      _ = (s * s * s) * w * (s * s * s)⁻¹ := by group
      _ = w := by rw [hs3]; group
  have hhc : (s⁻¹ * R0) * (R0 * s * R0⁻¹ * s) * (s⁻¹ * R0)⁻¹ = R0 * s * R0⁻¹ * s := by
    calc (s⁻¹ * R0) * (R0 * s * R0⁻¹ * s) * (s⁻¹ * R0)⁻¹ =
          s⁻¹ * (R0 * R0) * s * R0⁻¹ * s * R0⁻¹ * s := by group
      _ = R0⁻¹ * s * R0⁻¹ * s := by rw [hR2]; group
      _ = R0 * s * R0⁻¹ * s := by rw [hRi]
  obtain ⟨u, huV, hu⟩ := exists_mul_conj_eq h4 h2 hhV hw'V hw' hc hhc
  refine ⟨u, huV, cube_mul_eq_one h4 h2 hsV hs3 hw hsw huV, ?_⟩
  have hmV := hhV u huV
  have e : R0 * (s * u) * R0⁻¹ * (s * u) =
      (R0 * s * R0⁻¹ * s) * ((s⁻¹ * R0) * u * (s⁻¹ * R0)⁻¹) * u := by group
  rw [e, hu]
  calc u * ((s⁻¹ * R0) * u * (s⁻¹ * R0)⁻¹) * ((s⁻¹ * R0) * u * (s⁻¹ * R0)⁻¹) * u =
      u * (((s⁻¹ * R0) * u * (s⁻¹ * R0)⁻¹) * ((s⁻¹ * R0) * u * (s⁻¹ * R0)⁻¹)) * u := by group
    _ = 1 := by rw [h2 _ hmV, mul_one]; exact h2 u huV

end CFSG.Quasithin.Background.Harris.R1.D4Vert
