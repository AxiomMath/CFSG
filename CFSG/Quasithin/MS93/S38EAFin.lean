module

public import CFSG.Quasithin.MS93.S38EAQ
public import CFSG.Quasithin.MS93.S38EASp

public section

namespace CFSG.Quasithin.MS93.S38EA

open CFSG.Quasithin CFSG.Quasithin.MS93.S38E
open scoped commutatorElement

variable {U₀ : Type} [Group U₀]

theorem sup_eq_top_of_card {Y : Type*} [CommGroup Y] [Finite Y] {A B : Subgroup Y}
    (hAB : A ⊓ B = ⊥) (hcard : Nat.card A * Nat.card B = Nat.card Y) : A ⊔ B = ⊤ := by
  let f : ↥A × ↥B → ↥(A ⊔ B) := fun p =>
    ⟨(p.1 : Y) * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (a : Y) * b = a' * b' := congrArg Subtype.val hab
    have h2 : (a' : Y)⁻¹ * a = b' * (b : Y)⁻¹ :=
      calc (a' : Y)⁻¹ * a = (a' : Y)⁻¹ * (a * b * (b : Y)⁻¹) := by rw [mul_inv_cancel_right]
        _ = (a' : Y)⁻¹ * (a' * b' * (b : Y)⁻¹) := by rw [h1]
        _ = b' * (b : Y)⁻¹ := by group
    have hA : (a' : Y)⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸
      B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hA
    have hB : b = b' := by
      apply Subtype.ext
      rw [← hA] at h1
      exact mul_left_cancel h1
    rw [show a = a' from Subtype.ext hA.symm, hB]
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hcard] at h1
  exact Subgroup.eq_top_of_le_card _ h1

variable {V G₀ Lt Tb Qa E : Subgroup U₀} {e : ℕ} (hS : EndSetup V G₀ Lt Tb Qa E e)
  (lam : ↥⁅V, V⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, V⁆, Tb⁆ → lam c = 1)

include hS in
theorem le_v0_sup_bSub (he : 2 ≤ e ∧ e ≤ 4) (h4 : (fixV (hS.eS lam hlam1)).index = 4)
    (hm0 : commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1) = ⊥) :
    V ≤ ⁅V, Lt⁆ ⊔ bSub V Lt := by
  have : Finite (hS.YM lam) := hS.finite_YM lam
  set K := hS.kY lam hlam1
  have hcard : Nat.card (commV K) * Nat.card (fixV K) = Nat.card (hS.YM lam) := by
    have := (yPairing hS.cls2 lam).card_mul_card_perp (commV K)
    rwa [Pairing.perp_commV_eq_fixV _ (hS.pairing_isInv_kY lam hlam1)] at this
  have htop := sup_eq_top_of_card hm0 hcard
  intro v hv
  have hmem : (QuotientGroup.mk (⟨v, hv⟩ : ↥V) : hS.YM lam) ∈ commV K ⊔ fixV K := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨w, hw, c, hc, hwc⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨x, hx, hxw⟩ := commV_le_map_v0 hS lam hlam1 hw
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
  have hxv : (QuotientGroup.mk (x⁻¹ * ⟨v, hv⟩) : hS.YM lam) = c := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [QuotientGroup.mk'_apply] at hxw
    rw [hxw, ← hwc, inv_mul_cancel_left]
  have hB := mem_bSub_of_fix hS lam hlam1 he h4 (x⁻¹ * ⟨v, hv⟩) (by rw [hxv]; exact hc)
  have e : v = (x : U₀) * ((x⁻¹ * ⟨v, hv⟩ : ↥V) : U₀) := by simp
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hB)

section Vb

variable {Vb : Subgroup U₀} (hVb : Vb ≤ V) (hTbVb : Tb ≤ Subgroup.normalizer (Vb : Set U₀))
  (hgen : ∀ K : Subgroup U₀, G₀ ≤ Subgroup.normalizer (K : Set U₀) → Vb ≤ K → V ≤ K)
include hVb hTbVb hgen

include hS in
theorem commutator_le_v0 (he : 2 ≤ e ∧ e ≤ 4) (h4 : (fixV (hS.eS lam hlam1)).index = 4)
    (hm0 : commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1) = ⊥) (hVbab : ⁅Vb, Vb⁆ = ⊥)
    {Z : Subgroup U₀} (hZ : Z ≤ Vb) : ⁅V, Z⁆ ≤ ⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ := by
  set V₀ := ⁅V, Lt⁆ with hV₀
  have hn0 := le_normalizer_v0 hS
  have hVB := le_v0_sup_bSub hS lam hlam1 he h4 hm0
  have hVVb := le_v0_sup hS hVb hTbVb hgen
  have hcB := commutator_v0_bSub hS
  have hu : ∀ u ∈ V₀, ∀ z ∈ V, ⁅u, z⁆ ∈ ⁅V₀, V₀⁆ := by
    intro u hu z hz
    have hz' : z ∈ ((V₀ ⊔ bSub V Lt : Subgroup U₀) : Set U₀) := hVB hz
    rw [Subgroup.coe_mul_of_right_le_normalizer_left V₀ _
      ((bSub_le.trans hS.v_le).trans hn0)] at hz'
    obtain ⟨a, ha, b, hb, rfl⟩ := hz'
    have hub : ⁅u, b⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hu hb
      rwa [hcB, Subgroup.mem_bot] at this
    have e : ⁅u, a * b⁆ = ⁅u, a⁆ * (a * ⁅u, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, hub, mul_one, mul_inv_cancel, mul_one]
    exact Subgroup.commutator_mem_commutator hu ha
  rw [Subgroup.commutator_le]
  intro v hv z hzZ
  have hv' : v ∈ ((V₀ ⊔ Vb : Subgroup U₀) : Set U₀) := hVVb hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left V₀ _ ((hVb.trans hS.v_le).trans hn0)] at hv'
  obtain ⟨u, hu', w, hw, rfl⟩ := hv'
  have hwz : ⁅w, z⁆ = 1 := by
    have := Subgroup.commutator_mem_commutator hw (hZ hzZ)
    rwa [hVbab, Subgroup.mem_bot] at this
  have e : ⁅u * w, z⁆ = (u * ⁅w, z⁆ * u⁻¹) * ⁅u, z⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, hwz, mul_one, mul_inv_cancel, one_mul]
  exact hu u hu' z (hVb (hZ hzZ))

include hS in
theorem card_commutator_le_two
    (hK : AlternatingNatural (hS.kS lam hlam1) ⊤ ⊥ 6) (he : 2 ≤ e ∧ e ≤ 4)
    (h4 : (fixV (hS.eS lam hlam1)).index = 4)
    (hm0 : commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1) = ⊥) (hVbab : ⁅Vb, Vb⁆ = ⊥)
    {Z : Subgroup U₀} (hZ : Z ≤ Vb) : Nat.card ↥⁅V, Z⁆ ≤ 2 := by
  have : Finite ↥G₀ := hS.finite
  have : Finite ↥⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ := Finite.of_injective _ (Subgroup.inclusion_injective
    ((Subgroup.commutator_mono hS.commV_le hS.commV_le).trans
      ((EndSetup.comm_le_self V).trans hS.v_le)))
  exact (Subgroup.card_le_of_le (commutator_le_v0 hS lam hlam1 hVb hTbVb hgen he h4 hm0
    hVbab hZ)).trans (card_comm_v0_le hS lam hlam1 hK he h4)

end Vb

end CFSG.Quasithin.MS93.S38EA
