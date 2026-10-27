module

public import CFSG.Quasithin.Background.F918V2Defs2
public import CFSG.Quasithin.Background.F918V2Defs
public import CFSG.Quasithin.EmptyFaithful.S153ZK

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

section Abstract

variable {Q : Type*} [CommGroup Q] (A : Type*) [Group A] [MulDistribMulAction A Q]

@[expose] def V2fEqv {L L' : Subgroup Q} (φ : ↥L ≃* ↥L') : Prop :=
  ∀ (a : A) (l l' : ↥L), a • (l : Q) = (l' : Q) → a • ((φ l : ↥L') : Q) = ((φ l' : ↥L') : Q)

variable {A}

theorem V2fEqv.trans {L L' L'' : Subgroup Q} {φ : ↥L ≃* ↥L'} {ψ : ↥L' ≃* ↥L''}
    (hφ : V2fEqv A φ) (hψ : V2fEqv A ψ) : V2fEqv A (φ.trans ψ) :=
  fun a l l' h => hψ a (φ l) (φ l') (hφ a l l' h)

theorem V2fEqv.symm {L L' : Subgroup Q} {φ : ↥L ≃* ↥L'} (hL : XMod.IsInv A L)
    (hφ : V2fEqv A φ) : V2fEqv A φ.symm := by
  intro a l' l₂' hl
  have hx : a • ((φ.symm l' : ↥L) : Q) ∈ L := hL a _ (φ.symm l').2
  have h1 := hφ a (φ.symm l') ⟨a • ((φ.symm l' : ↥L) : Q), hx⟩ rfl
  rw [MulEquiv.apply_symm_apply] at h1
  have h3 : φ ⟨a • ((φ.symm l' : ↥L) : Q), hx⟩ = l₂' := Subtype.ext (h1.symm.trans hl)
  have h4 : (⟨a • ((φ.symm l' : ↥L) : Q), hx⟩ : ↥L) = φ.symm l₂' := by
    rw [← h3, MulEquiv.symm_apply_apply]
  exact congrArg Subtype.val h4

theorem v2f_inf_eq_bot {R P : Subgroup Q} (hR : XMod.IsIrr A R) (hP : XMod.IsIrr A P)
    (hne : R ≠ P) : R ⊓ P = ⊥ := by
  rcases hR.2.2 (R ⊓ P) (hR.1.inf hP.1) bot_le inf_le_left with h | h
  · exact h
  · exfalso
    have hRP : R ≤ P := fun x hx => by
      have : x ∈ R ⊓ P := by rw [h]; exact hx
      exact this.2
    rcases hP.2.2 R hR.1 bot_le hRP with h' | h'
    · exact hR.2.1.ne' h'
    · exact hne h'

theorem v2f_exists_mul_mem {P P' R : Subgroup Q} (hP : XMod.IsIrr A P) (hP' : XMod.IsInv A P')
    (hR : XMod.IsInv A R) (hR0 : R ≠ ⊥) (hRle : R ≤ P ⊔ P') (hRP' : R ⊓ P' = ⊥) :
    ∀ x ∈ P, ∃ y ∈ P', x * y ∈ R := by
  have hS : XMod.IsInv A ((R ⊔ P') ⊓ P) := (hR.sup hP').inf hP.1
  rcases hP.2.2 _ hS bot_le inf_le_right with h | h
  · exfalso
    apply hR0
    rw [Subgroup.eq_bot_iff_forall]
    intro r hr
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 (hRle hr)
    have hxS : x ∈ (R ⊔ P') ⊓ P := by
      refine ⟨?_, hx⟩
      rw [← mul_inv_cancel_right x y]
      exact Subgroup.mul_mem_sup hr (P'.inv_mem hy)
    rw [h, Subgroup.mem_bot] at hxS
    subst hxS
    have h2 : y ∈ R ⊓ P' := ⟨by simpa using hr, hy⟩
    rw [hRP', Subgroup.mem_bot] at h2
    simp [h2]
  · intro x hx
    have hx' : x ∈ (R ⊔ P') ⊓ P := by rw [h]; exact hx
    obtain ⟨r, hr, y, hy, hry⟩ := Subgroup.mem_sup.1 hx'.1
    refine ⟨y⁻¹, P'.inv_mem hy, ?_⟩
    have : x * y⁻¹ = r := by rw [← hry]; exact mul_inv_cancel_right r y
    rw [this]
    exact hr

theorem v2f_eq_right {P' R : Subgroup Q} (hRP' : R ⊓ P' = ⊥) {x y y' : Q} (hy : y ∈ P')
    (hy' : y' ∈ P') (h : x * y ∈ R) (h' : x * y' ∈ R) : y = y' := by
  have h1 : y / y' ∈ R ⊓ P' := by
    refine ⟨?_, P'.div_mem hy hy'⟩
    rw [← mul_div_mul_left_eq_div y y' x]
    exact R.div_mem h h'
  rw [hRP', Subgroup.mem_bot, div_eq_one] at h1
  exact h1

theorem v2f_eq_left {P R : Subgroup Q} (hRP : R ⊓ P = ⊥) {x x' y : Q} (hx : x ∈ P)
    (hx' : x' ∈ P) (h : x * y ∈ R) (h' : x' * y ∈ R) : x = x' := by
  have h1 : x / x' ∈ R ⊓ P := by
    refine ⟨?_, P.div_mem hx hx'⟩
    rw [← mul_div_mul_right_eq_div x x' y]
    exact R.div_mem h h'
  rw [hRP, Subgroup.mem_bot, div_eq_one] at h1
  exact h1

theorem v2f_exists_graph {P P' R : Subgroup Q} (hP : XMod.IsIrr A P) (hP' : XMod.IsIrr A P')
    (hR : XMod.IsInv A R) (hR0 : R ≠ ⊥) (hRle : R ≤ P ⊔ P')
    (hRP : R ⊓ P = ⊥) (hRP' : R ⊓ P' = ⊥) :
    ∃ θ : ↥P ≃* ↥P', V2fEqv A θ ∧ ∀ (x : ↥P) (y : ↥P'), (x : Q) * (y : Q) ∈ R ↔ θ x = y := by
  classical
  have hex : ∀ x : ↥P, ∃ y : ↥P', (x : Q) * (y : Q) ∈ R := fun x => by
    obtain ⟨y, hy, h⟩ := v2f_exists_mul_mem hP hP'.1 hR hR0 hRle hRP' x x.2
    exact ⟨⟨y, hy⟩, h⟩
  have hex' : ∀ y : ↥P', ∃ x : ↥P, (x : Q) * (y : Q) ∈ R := fun y => by
    obtain ⟨x, hx, h⟩ := v2f_exists_mul_mem hP' hP.1 hR hR0 (by rwa [sup_comm]) hRP y y.2
    exact ⟨⟨x, hx⟩, by rwa [mul_comm]⟩
  have huniq : ∀ (x : ↥P) (y y' : ↥P'), (x : Q) * (y : Q) ∈ R → (x : Q) * (y' : Q) ∈ R →
      y = y' := fun x y y' h h' => Subtype.ext (v2f_eq_right hRP' y.2 y'.2 h h')
  have huniq' : ∀ (x x' : ↥P) (y : ↥P'), (x : Q) * (y : Q) ∈ R → (x' : Q) * (y : Q) ∈ R →
      x = x' := fun x x' y h h' => Subtype.ext (v2f_eq_left hRP x.2 x'.2 h h')
  choose f hf using hex
  have hf_iff : ∀ (x : ↥P) (y : ↥P'), (x : Q) * (y : Q) ∈ R ↔ f x = y := fun x y =>
    ⟨fun h => huniq x _ _ (hf x) h, fun h => by rw [← h]; exact hf x⟩
  let fm : ↥P →* ↥P' :=
    { toFun := f
      map_one' := (hf_iff 1 1).1 (by simp)
      map_mul' := fun x₁ x₂ => (hf_iff _ _).1 (by
        have := R.mul_mem (hf x₁) (hf x₂)
        rw [mul_mul_mul_comm] at this
        exact this) }
  have hbij : Function.Bijective fm := by
    constructor
    · intro x₁ x₂ h
      have h1 : (x₁ : Q) * (f x₁ : Q) ∈ R := hf x₁
      have h2 : (x₂ : Q) * (f x₁ : Q) ∈ R := by
        have h' : f x₂ = f x₁ := h.symm
        have := hf x₂
        rwa [h'] at this
      exact huniq' x₁ x₂ _ h1 h2
    · intro y
      obtain ⟨x, hx⟩ := hex' y
      exact ⟨x, (hf_iff x y).1 hx⟩
  refine ⟨MulEquiv.ofBijective fm hbij, ?_, fun x y => hf_iff x y⟩
  intro a x x' hxx
  have h1 : (x : Q) * ((f x : ↥P') : Q) ∈ R := hf x
  have h2 : a • ((x : Q) * ((f x : ↥P') : Q)) ∈ R := hR a _ h1
  rw [smul_mul', hxx] at h2
  have h3 : a • ((f x : ↥P') : Q) ∈ P' := hP'.1 a _ (f x).2
  have h4 := huniq x' ⟨_, h3⟩ (f x') h2 (hf x')
  exact congrArg Subtype.val h4

theorem v2f_eq_of_le_sup {P P' R R' : Subgroup Q} (hP : XMod.IsIrr A P) (hP' : XMod.IsIrr A P')
    (hE : ∀ φ : ↥P ≃* ↥P, V2fEqv A φ → φ = MulEquiv.refl _)
    (hR : XMod.IsIrr A R) (hR' : XMod.IsIrr A R') (hRle : R ≤ P ⊔ P') (hR'le : R' ≤ P ⊔ P')
    (hRP : R ≠ P) (hRP' : R ≠ P') (hR'P : R' ≠ P) (hR'P' : R' ≠ P') : R = R' := by
  obtain ⟨θ, hθe, hθ⟩ := v2f_exists_graph hP hP' hR.1 hR.2.1.ne' hRle
    (v2f_inf_eq_bot hR hP hRP) (v2f_inf_eq_bot hR hP' hRP')
  obtain ⟨θ', hθ'e, hθ'⟩ := v2f_exists_graph hP hP' hR'.1 hR'.2.1.ne' hR'le
    (v2f_inf_eq_bot hR' hP hR'P) (v2f_inf_eq_bot hR' hP' hR'P')
  have h1 := hE (θ.trans θ'.symm) (hθe.trans (V2fEqv.symm hP.1 hθ'e))
  have h2 : ∀ x : ↥P, θ x = θ' x := fun x => by
    have := DFunLike.congr_fun h1 x
    simp only [MulEquiv.trans_apply, MulEquiv.refl_apply] at this
    exact (MulEquiv.symm_apply_eq θ').1 this
  have hle : R ≤ R' := by
    intro r hr
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 (hRle hr)
    have h3 := (hθ ⟨x, hx⟩ ⟨y, hy⟩).1 hr
    exact (hθ' ⟨x, hx⟩ ⟨y, hy⟩).2 ((h2 _).symm.trans h3)
  rcases hR'.2.2 R hR.1 bot_le hle with h | h
  · exact absurd h hR.2.1.ne'
  · exact h

end Abstract

section Single

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem v2f_iso_smul {Λ : Subgroup Γ} {c : Γ} (hc : ∀ l ∈ Λ, c * l = l * c) (R : Subgroup Q) :
    XMod.Iso ↥Λ R (c • R) := by
  refine ⟨XMod.smulEquiv c R, fun a x x' h => ?_⟩
  have h1 : (a : Γ) • c • (x : Q) = c • (a : Γ) • (x : Q) := by
    rw [smul_smul, smul_smul, hc a a.2]
  change (a : Γ) • c • (x : Q) = c • (x' : Q)
  rw [← h]
  exact h1

theorem v2f_mem_smul {Λ : Subgroup Γ} (hN : XMod.Normalizes ↥Λ Γ Q) {c : Γ}
    (hc : ∀ l ∈ Λ, c * l = l * c) {P R : Subgroup Q}
    (hR : XMod.IsIrr ↥Λ R ∧ XMod.Iso ↥Λ R P) :
    XMod.IsIrr ↥Λ (c • R) ∧ XMod.Iso ↥Λ (c • R) P :=
  ⟨isIrr_smul hN c hR.1, (XMod.Iso.symm hR.1.1 (v2f_iso_smul hc R)).trans hR.2⟩

theorem v2f_smul_eq_self {Λ : Subgroup Γ} {c : Γ} (hc : ∀ l ∈ Λ, c * l = l * c)
    {P R : Subgroup Q} (hE : EndUnitsTrivial Λ P) (hR : XMod.IsInv ↥Λ R)
    (hRP : XMod.Iso ↥Λ R P) (hcR : c • R = R) : ∀ x ∈ R, c • x = x := by
  obtain ⟨θ, hθ⟩ := hRP
  have hθ' : V2fEqv ↥Λ θ := hθ
  let cR : ↥R ≃* ↥R := (XMod.smulEquiv c R).trans (MulEquiv.subgroupCongr hcR)
  have hcR_eqv : V2fEqv ↥Λ cR := by
    intro a x x' h
    have h1 : (a : Γ) • c • (x : Q) = c • (a : Γ) • (x : Q) := by
      rw [smul_smul, smul_smul, hc a a.2]
    change (a : Γ) • c • (x : Q) = c • (x' : Q)
    rw [← h]
    exact h1
  have hφ : θ.symm.trans (cR.trans θ) = MulEquiv.refl _ :=
    hE _ ((V2fEqv.symm hR hθ').trans (hcR_eqv.trans hθ'))
  intro x hx
  have h1 := DFunLike.congr_fun hφ (θ ⟨x, hx⟩)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.refl_apply] at h1
  have h2 : cR ⟨x, hx⟩ = ⟨x, hx⟩ := θ.injective h1
  exact congrArg Subtype.val h2

theorem v2f_single_type {Λ : Subgroup Γ} (hN : XMod.Normalizes ↥Λ Γ Q) {P P' : Subgroup Q}
    (hP : XMod.IsIrr ↥Λ P) (hP' : XMod.IsIrr ↥Λ P') (hiso : XMod.Iso ↥Λ P' P)
    (hE : EndUnitsTrivial Λ P)
    (hall : ∀ R : Subgroup Q, XMod.IsIrr ↥Λ R → XMod.Iso ↥Λ R P → R ≤ P ⊔ P')
    {c : Γ} (hc : ∀ l ∈ Λ, c * l = l * c) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hcp : c ^ p = 1) : ∀ q ∈ P ⊔ P', c • q = q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set 𝒩 : Set (Subgroup Q) := {R | XMod.IsIrr ↥Λ R ∧ XMod.Iso ↥Λ R P} with h𝒩
  have hPN : P ∈ 𝒩 := ⟨hP, XMod.Iso.refl P⟩
  have hP'N : P' ∈ 𝒩 := ⟨hP', hiso⟩
  have hclos : ∀ R ∈ 𝒩, c • R ∈ 𝒩 := fun R hR => v2f_mem_smul hN hc hR
  obtain ⟨D, hD⟩ : ∃ D : Subgroup Q, ∀ R ∈ 𝒩, R = P ∨ R = P' ∨ R = D := by
    by_cases h : ∃ R₀ ∈ 𝒩, R₀ ≠ P ∧ R₀ ≠ P'
    · obtain ⟨R₀, hR₀, hR₀P, hR₀P'⟩ := h
      refine ⟨R₀, fun R hR => ?_⟩
      by_cases h1 : R = P
      · exact Or.inl h1
      by_cases h2 : R = P'
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr (v2f_eq_of_le_sup hP hP' hE hR.1 hR₀.1 (hall R hR.1 hR.2)
        (hall R₀ hR₀.1 hR₀.2) h1 h2 hR₀P hR₀P'))
    · refine ⟨P, fun R hR => ?_⟩
      by_cases h1 : R = P
      · exact Or.inl h1
      · refine Or.inr (Or.inl ?_)
        by_contra h2
        exact h ⟨R, hR, h1, h2⟩
  have hfix : ∀ R ∈ 𝒩, c • R = R := by
    intro R hR
    by_contra hne
    set f : Subgroup Q → Subgroup Q := fun S => c • S with hf
    have hper : Function.IsPeriodicPt f p R := by
      show f^[p] R = R
      rw [hf, smul_iterate, hcp]
      exact one_smul _ R
    have hmin : Function.minimalPeriod f R = p := Function.minimalPeriod_eq_prime hper hne
    have hmem : ∀ i : ℕ, f^[i] R ∈ 𝒩 := by
      intro i
      induction i with
      | zero => exact hR
      | succ i ih =>
        rw [Function.iterate_succ_apply']
        exact hclos _ ih
    have hinj : Set.InjOn (fun i => f^[i] R) (Finset.range p : Set ℕ) := by
      have := Function.iterate_injOn_Iio_minimalPeriod (f := f) (x := R)
      rw [hmin] at this
      simpa using this
    have hsub : (Finset.range p).image (fun i => f^[i] R) ⊆
        ({P, P', D} : Finset (Subgroup Q)) := by
      intro S hS
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hS
      rcases hD _ (hmem i) with h | h | h <;> simp [h]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Finset.card_range] at h1
    have h2 := Finset.card_le_three (a := P) (b := P') (c := D)
    omega
  have hall_fix : ∀ R ∈ 𝒩, ∀ x ∈ R, c • x = x := fun R hR =>
    v2f_smul_eq_self hc hE hR.1.1 hR.2 (hfix R hR)
  intro q hq
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hq
  rw [smul_mul', hall_fix P hPN x hx, hall_fix P' hP'N y hy]

end Single

section Headline

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

set_option linter.unusedVariables false in
theorem centralizer_prime_ge_five [Finite Γ] [Finite Q] {Λ T₀ : Subgroup Γ} {Vq : Subgroup Q}
    {t : Γ} (hD : TwoType Λ T₀ Vq t) {S₀ : Subgroup Q} (hS₀ : XMod.IsIrr ↥Λ S₀)
    (hS₀iso : XMod.Iso ↥Λ S₀ Vq) (hS₀d : Vq ⊓ S₀ = ⊥)
    (hdec : (Vq ⊔ S₀) ⊔ t • (Vq ⊔ S₀) = ⊤) (hdis : (Vq ⊔ S₀) ⊓ t • (Vq ⊔ S₀) = ⊥)
    (hall : ∀ R : Subgroup Q, XMod.IsIrr ↥Λ R → XMod.Iso ↥Λ R Vq → R ≤ Vq ⊔ S₀)
    (hE1 : EndUnitsTrivial Λ Vq) (hE2 : EndUnitsTrivial Λ (t • Vq))
    {c : Γ} (hc : ∀ l ∈ Λ, c * l = l * c) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hcp : c ^ p = 1) :
    ∀ q : Q, c • q = q := by
  have hN : XMod.Normalizes ↥Λ Γ Q := normalizes_whole Λ hD.normal
  have h0 := v2f_single_type hN hD.irr hS₀ hS₀iso hE1 hall hc hp hp5 hcp
  have hall' : ∀ R : Subgroup Q, XMod.IsIrr ↥Λ R → XMod.Iso ↥Λ R (t • Vq) →
      R ≤ t • Vq ⊔ t • S₀ := by
    intro R hR hRiso
    have h2 : XMod.Iso ↥Λ (t⁻¹ • R) (t⁻¹ • t • Vq) := XMod.iso_smul hN t⁻¹ hRiso
    rw [inv_smul_smul] at h2
    have h3 := hall _ (isIrr_smul hN t⁻¹ hR) h2
    have h4 : t • t⁻¹ • R ≤ t • (Vq ⊔ S₀) := Subgroup.pointwise_smul_le_pointwise_smul_iff.2 h3
    rwa [smul_inv_smul, Subgroup.smul_sup] at h4
  have h1 := v2f_single_type hN (isIrr_smul hN t hD.irr) (isIrr_smul hN t hS₀)
    (XMod.iso_smul hN t hS₀iso) hE2 hall' hc hp hp5 hcp
  intro q
  have hq : q ∈ (Vq ⊔ S₀) ⊔ t • (Vq ⊔ S₀) := by rw [hdec]; exact Subgroup.mem_top q
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hq
  rw [Subgroup.smul_sup] at hy
  rw [smul_mul', h0 x hx, h1 y hy]

end Headline

end CFSG.Quasithin.Z391
