module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4SzSylow
import CFSG.Quasithin.Recognition.Stroth.Str83RqSzModule
import CFSG.Quasithin.Recognition.Stroth.Str83RqTools
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexSz
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
public import CFSG.GroupTheory.CommutatorCentralizerIn

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Stroth.G5 CFSG.LieType.BorelTits
open CFSG.GH74.QTGen4.DSGen4
open CFSG.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem le_normalizer_of_commutative_sup {A A₂ : Subgroup G}
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x) :
    A₂ ≤ Subgroup.normalizer (A : Set G) := by
  have hfwd : ∀ y ∈ A₂, ∀ x ∈ A, y * x * y⁻¹ ∈ A := by
    intro y hy x hx
    have hcomm : y * x = x * y :=
      hAc y (Subgroup.mem_sup_right hy) x (Subgroup.mem_sup_left hx)
    have heq : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [hcomm]
        _ = x := by group
    rwa [heq]
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact hfwd y hy x hx
  · intro hx
    have := hfwd y⁻¹ (A₂.inv_mem hy) (y * x * y⁻¹) hx
    rwa [show y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ = x from by group] at this

private theorem card_eq_relIndex_sup_of_inf_eq_bot {H Q A A₂ : Subgroup G} (hHQ : H ⊓ Q = ⊥)
    (hH : H ≤ A ⊔ A₂) (hAA₂ : A ⊓ A₂ = Q)
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x) :
    Nat.card H = Q.relIndex (H ⊔ Q) := by
  have hQleA : Q ≤ A := hAA₂ ▸ inf_le_left
  have hconj : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := by
    intro h hh q hq
    have hcomm : h * q = q * h :=
      hAc h (hH hh) q (Subgroup.mem_sup_left (hQleA hq))
    have heq : h * q * h⁻¹ = q := by
      calc h * q * h⁻¹ = q * h * h⁻¹ := by rw [hcomm]
        _ = q := by group
    rwa [heq]
  have hHnorm : H ≤ Subgroup.normalizer (Q : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · exact hconj h hh q
    · intro hq
      have := hconj h⁻¹ (H.inv_mem hh) (h * q * h⁻¹) hq
      rwa [show h⁻¹ * (h * q * h⁻¹) * (h⁻¹)⁻¹ = q from by group] at this
  have h1 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex
    (H := Q) (K := H ⊔ Q) (le_sup_right : Q ≤ H ⊔ Q)
  have h2 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (A := H) (B := Q) hHnorm
  rw [hHQ, Subgroup.card_bot, mul_one] at h2
  have h3 : Nat.card H * Nat.card Q = Q.relIndex (H ⊔ Q) * Nat.card Q := by
    calc Nat.card H * Nat.card Q = Nat.card ↥(H ⊔ Q) := h2.symm
      _ = Nat.card Q * Q.relIndex (H ⊔ Q) := h1
      _ = Q.relIndex (H ⊔ Q) * Nat.card Q := mul_comm (Nat.card Q) _
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hQpos h3

theorem card_le_relIndex_mul_relIndex {H Q A A₂ : Subgroup G} (hHQ : H ⊓ Q = ⊥)
    (hH : H ≤ A ⊔ A₂) (hAA₂ : A ⊓ A₂ = Q)
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x) :
    Nat.card H ≤ Q.relIndex A * Q.relIndex A₂ := by
  have hQleA : Q ≤ A := hAA₂ ▸ inf_le_left
  have hA₂N : A₂ ≤ Subgroup.normalizer (A : Set G) := le_normalizer_of_commutative_sup hAc
  calc Nat.card H = Q.relIndex (H ⊔ Q) :=
        card_eq_relIndex_sup_of_inf_eq_bot hHQ hH hAA₂ hAc
    _ ≤ Q.relIndex (A ⊔ A₂) :=
      CFSG.QuasithinUnique.C5.relIndex_le_of_le (le_sup_right : Q ≤ H ⊔ Q)
        (sup_le hH (hQleA.trans le_sup_left))
    _ = Q.relIndex A * A.relIndex (A ⊔ A₂) :=
      (Subgroup.relIndex_mul_relIndex Q A (A ⊔ A₂) hQleA le_sup_left).symm
    _ = Q.relIndex A * Q.relIndex A₂ := by
      congr 1
      have h1 : A.relIndex (A₂ ⊔ A) = A.relIndex A₂ :=
        CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer
          (A := A₂) (B := A) hA₂N
      rw [sup_comm] at h1
      rw [h1, ← Subgroup.inf_relIndex_right (H := A) (K := A₂), hAA₂]

private def commutatorCentralizerMod (O : Subgroup G) (z : G) : Subgroup G where
  carrier := {t : G | t ∈ normalizer (O : Set G) ∧ ⁅z, t⁆ ∈ O}
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨Subgroup.mul_mem _ haN hbN, ?_⟩
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa [mul_assoc] using O.mul_mem ha ((Subgroup.mem_normalizer_iff.mp haN _).mp hb)
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    simp
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨Subgroup.inv_mem _ haN, ?_⟩
    rw [commutatorElement_inv_right]
    have haz : ⁅a, z⁆ ∈ O := by
      have h2 : ⁅z, a⁆⁻¹ ∈ O := O.inv_mem ha
      rwa [commutatorElement_inv] at h2
    simpa [mul_assoc] using
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp haz

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private def caseIICentralizer (L1 : Subgroup G) (S : Subgroup G) (k : G) : Subgroup G :=
  commutatorCentralizerIn (S ⊓ L1) (pCoreOf 2 L1) (Subgroup.zpowers k)
    (inf_le_right.trans (le_normalizer_pCoreOf 2 L1))

private theorem K_le_normalizer_of_map_conj {A A₂ : Subgroup G}
    (hKA : t.K ≤ normalizer (A : Set G))
    (hA₂ : A.map (MulAut.conj t.x₁).toMonoidHom = A₂) :
    t.K ≤ normalizer (A₂ : Set G) := by
  have hx₁K : t.x₁ ∈ normalizer (t.K : Set G) := t.track.x₁_norm
  have hfwd : ∀ h ∈ t.K, ∀ a₂ ∈ A.map (MulAut.conj t.x₁).toMonoidHom,
      h * a₂ * h⁻¹ ∈ A.map (MulAut.conj t.x₁).toMonoidHom := by
    intro h hh a₂ ha₂
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha₂
    have hh' : t.x₁⁻¹ * h * t.x₁ ∈ t.K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx₁K) h).mp hh
      simpa using this
    have hmem : (t.x₁⁻¹ * h * t.x₁) * a * (t.x₁⁻¹ * h * t.x₁)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hKA hh') a).mp ha
    refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
    show t.x₁ * ((t.x₁⁻¹ * h * t.x₁) * a * (t.x₁⁻¹ * h * t.x₁)⁻¹) * t.x₁⁻¹ =
      h * (t.x₁ * a * t.x₁⁻¹) * h⁻¹
    group
  rw [← hA₂]
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro a₂
  constructor
  · exact hfwd h hh a₂
  · intro hconj
    have := hfwd h⁻¹ (t.K.inv_mem hh) (h * a₂ * h⁻¹) hconj
    rwa [show h⁻¹ * (h * a₂ * h⁻¹) * (h⁻¹)⁻¹ = a₂ from by group] at this

private theorem caseII_Z1_le_A {Q A A₂ : Subgroup G} (hQleA : Q ≤ A)
    (hZ₁A : t.Zv 0 ≤ A ⊔ A₂) (hA₂NA : A₂ ≤ normalizer (A : Set G))
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x)
    (hD₂A : ∀ k ∈ t.D2, ∀ x ∈ A, k * x * k⁻¹ = x)
    (hD₂free : ∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ A₂, k * x * k⁻¹ * x⁻¹ ∈ Q → x ∈ Q)
    {k₀ : G} (hk₀ : k₀ ∈ t.D2) (hk₀ne : k₀ ≠ 1)
    (h : ∀ z ∈ t.Zv 0, ∀ k ∈ t.D2, k * z * k⁻¹ * z⁻¹ ∈ Q) :
    t.Zv 0 ≤ A := by
  intro z hz
  obtain ⟨a, ha, a₂, ha₂, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hA₂NA).mp (hZ₁A hz)
  have ha₂Q : a₂ ∈ Q := by
    refine hD₂free k₀ hk₀ hk₀ne a₂ ha₂ ?_
    have hcommz : k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹ ∈ Q := h (a * a₂) hz k₀ hk₀
    have hid : k₀ * a₂ * k₀⁻¹ * a₂⁻¹ =
        a⁻¹ * (k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹) * a := by
      rw [show k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹ =
          (k₀ * a * k₀⁻¹) * (k₀ * a₂ * k₀⁻¹) * a₂⁻¹ * a⁻¹ from by group]
      rw [hD₂A k₀ hk₀ a ha]
      group
    rw [hid]
    have hq : k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹ ∈ A := hQleA hcommz
    have hacomm : a⁻¹ * (k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹) * a =
        k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹ := by
      have h1 : a * (k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹) =
          (k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹) * a :=
        hAc a (Subgroup.mem_sup_left ha) _ (Subgroup.mem_sup_left hq)
      calc a⁻¹ * (k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹) * a =
          a⁻¹ * ((k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹) * a) := by group
        _ = a⁻¹ * (a * (k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹)) := by rw [h1]
        _ = k₀ * (a * a₂) * k₀⁻¹ * (a * a₂)⁻¹ := by group
    rw [hacomm]
    exact hcommz
  exact A.mul_mem ha (hQleA ha₂Q)

private theorem caseII_Z1_le_A₂ {A A₂ : Subgroup G} (hZ₁leA : t.Zv 0 ≤ A)
    (hA₂ : A.map (MulAut.conj t.x₁).toMonoidHom = A₂) :
    t.Zv 0 ≤ A₂ := by
  intro z hz
  have hx₁NZ : t.x₁ ∈ normalizer (t.Zv 0 : Set G) :=
    t.Gv_le_normalizer_Zv 0 t.x₁_mem_Gv_zero
  have hz' : t.x₁⁻¹ * z * t.x₁ ∈ t.Zv 0 := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx₁NZ) z).mp hz
    simpa using this
  have hmem : z ∈ A.map (MulAut.conj t.x₁).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨t.x₁⁻¹ * z * t.x₁, hZ₁leA hz', ?_⟩
    show t.x₁ * (t.x₁⁻¹ * z * t.x₁) * t.x₁⁻¹ = z
    group
  rwa [hA₂] at hmem

private theorem caseII_exists_commutator_not_mem {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {A A₂ : Subgroup G}
    (hZ₁Q : t.Zv 0 ⊓ pCoreOf 2 t.GT = ⊥) (hZ₁A : t.Zv 0 ≤ A ⊔ A₂)
    (hAA₂ : A ⊓ A₂ = pCoreOf 2 t.GT)
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x)
    (hA₂ : A.map (MulAut.conj t.x₁).toMonoidHom = A₂)
    (hA₂NA : A₂ ≤ normalizer (A : Set G))
    (hD₂A : ∀ k ∈ t.D2, ∀ x ∈ A, k * x * k⁻¹ = x)
    (hD₂free : ∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ A₂,
      k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 t.GT → x ∈ pCoreOf 2 t.GT) :
    ∃ z ∈ t.Zv 0, ∃ k ∈ t.D2, k * z * k⁻¹ * z⁻¹ ∉ pCoreOf 2 t.GT := by
  by_contra h
  push Not at h
  have hQleA : pCoreOf 2 t.GT ≤ A := by
    rw [← hAA₂]
    exact inf_le_left
  have hcardD2 : Nat.card t.D2 = 2 ^ f - 1 := t.card_D2 hfr
  have hpow4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  have hD2ne : t.D2 ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card t.D2 = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hcardD2] at h1
    omega
  obtain ⟨⟨k₀, hk₀D2⟩, hk₀ne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hD2ne
  have hk₀ne' : k₀ ≠ 1 := fun h1 => hk₀ne (Subtype.ext h1)
  have hZ₁leA : t.Zv 0 ≤ A :=
    t.caseII_Z1_le_A hQleA hZ₁A hA₂NA hAc hD₂A hD₂free hk₀D2 hk₀ne' h
  have hZ₁leA₂ : t.Zv 0 ≤ A₂ := t.caseII_Z1_le_A₂ hZ₁leA hA₂
  have hleQ : t.Zv 0 ≤ pCoreOf 2 t.GT := by
    rw [← hAA₂]
    exact le_inf hZ₁leA hZ₁leA₂
  have hbot : t.Zv 0 = ⊥ := by
    have h1 : t.Zv 0 ⊓ pCoreOf 2 t.GT = t.Zv 0 := inf_eq_left.mpr hleQ
    rw [h1] at hZ₁Q
    exact hZ₁Q
  exact t.Zv_ne_bot hfr.hF 0 hbot

private theorem caseII_commutator_mem_A₂ {A A₂ : Subgroup G}
    (hZ₁A : t.Zv 0 ≤ A ⊔ A₂)
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x)
    (hA₂NA : A₂ ≤ normalizer (A : Set G))
    (hK_A₂ : t.K ≤ normalizer (A₂ : Set G))
    (hD₂A : ∀ k ∈ t.D2, ∀ x ∈ A, k * x * k⁻¹ = x)
    {z₀ k₁ : G} (hz₀Z1 : z₀ ∈ t.Zv 0) (hk₁D2 : k₁ ∈ t.D2) :
    k₁ * z₀ * k₁⁻¹ * z₀⁻¹ ∈ A₂ := by
  have hk₁K : k₁ ∈ t.K := Subgroup.mem_sup_right hk₁D2
  obtain ⟨a₀, ha₀A, a₂₀, ha₂₀A₂, hz₀eq⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hA₂NA).mp (hZ₁A hz₀Z1)
  have hceq : k₁ * z₀ * k₁⁻¹ * z₀⁻¹ =
      a₀ * (k₁ * a₂₀ * k₁⁻¹ * a₂₀⁻¹) * a₀⁻¹ := by
    rw [hz₀eq]
    rw [show k₁ * (a₀ * a₂₀) * k₁⁻¹ * (a₀ * a₂₀)⁻¹ =
        (k₁ * a₀ * k₁⁻¹) * (k₁ * a₂₀ * k₁⁻¹) * a₂₀⁻¹ * a₀⁻¹ from by group]
    rw [hD₂A k₁ hk₁D2 a₀ ha₀A]
    group
  have hqA₂ : k₁ * a₂₀ * k₁⁻¹ * a₂₀⁻¹ ∈ A₂ := by
    have h1 : k₁ * a₂₀ * k₁⁻¹ ∈ A₂ :=
      (Subgroup.mem_normalizer_iff.mp (hK_A₂ hk₁K) a₂₀).mp ha₂₀A₂
    exact A₂.mul_mem h1 (A₂.inv_mem ha₂₀A₂)
  rw [hceq]
  have hcomm : a₀ * (k₁ * a₂₀ * k₁⁻¹ * a₂₀⁻¹) =
      (k₁ * a₂₀ * k₁⁻¹ * a₂₀⁻¹) * a₀ :=
    hAc a₀ (Subgroup.mem_sup_left ha₀A) _ (Subgroup.mem_sup_right hqA₂)
  have heq : a₀ * (k₁ * a₂₀ * k₁⁻¹ * a₂₀⁻¹) * a₀⁻¹ =
      k₁ * a₂₀ * k₁⁻¹ * a₂₀⁻¹ := by
    calc a₀ * (k₁ * a₂₀ * k₁⁻¹ * a₂₀⁻¹) * a₀⁻¹ =
        (k₁ * a₂₀ * k₁⁻¹ * a₂₀⁻¹) * a₀ * a₀⁻¹ := by rw [hcomm]
      _ = k₁ * a₂₀ * k₁⁻¹ * a₂₀⁻¹ := by group
  rw [heq]
  exact hqA₂

private theorem caseII_commutator_mem_inf_not_mem {A A₂ : Subgroup G}
    (hZ₁A : t.Zv 0 ≤ A ⊔ A₂)
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x)
    (hA₂NA : A₂ ≤ normalizer (A : Set G))
    (hK_A₂ : t.K ≤ normalizer (A₂ : Set G))
    (hK_Z₁ : t.K ≤ normalizer (t.Zv 0 : Set G))
    (hD₂A : ∀ k ∈ t.D2, ∀ x ∈ A, k * x * k⁻¹ = x)
    {z₀ k₁ : G} (hz₀Z1 : z₀ ∈ t.Zv 0) (hk₁D2 : k₁ ∈ t.D2)
    (hc₀ : k₁ * z₀ * k₁⁻¹ * z₀⁻¹ ∉ pCoreOf 2 t.GT) :
    ∃ c : G, c ∈ t.Zv 0 ∧ c ∈ A₂ ∧ c ∉ pCoreOf 2 t.GT := by
  have hk₁K : k₁ ∈ t.K := Subgroup.mem_sup_right hk₁D2
  have hcZ1 : k₁ * z₀ * k₁⁻¹ * z₀⁻¹ ∈ t.Zv 0 := by
    have hconj : k₁ * z₀ * k₁⁻¹ ∈ t.Zv 0 :=
      (Subgroup.mem_normalizer_iff.mp (hK_Z₁ hk₁K) z₀).mp hz₀Z1
    exact (t.Zv 0).mul_mem hconj ((t.Zv 0).inv_mem hz₀Z1)
  have hcA₂ : k₁ * z₀ * k₁⁻¹ * z₀⁻¹ ∈ A₂ :=
    t.caseII_commutator_mem_A₂ hZ₁A hAc hA₂NA hK_A₂ hD₂A hz₀Z1 hk₁D2
  exact ⟨_, hcZ1, hcA₂, hc₀⟩

private theorem caseII_A₂_le_sup_of_commutator {A A₂ : Subgroup G} {c : G}
    (hcZ : c ∈ t.Zv 0) (hcA₂ : c ∈ A₂) (hcQ : c ∉ pCoreOf 2 t.GT)
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x)
    (hK_A₂ : t.K ≤ normalizer (A₂ : Set G))
    (hK_Z₁ : t.K ≤ normalizer (t.Zv 0 : Set G))
    (hD₂trans : ∀ x ∈ A₂, x ∉ pCoreOf 2 t.GT → ∀ y ∈ A₂, y ∉ pCoreOf 2 t.GT →
      ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ pCoreOf 2 t.GT) :
    A₂ ≤ (t.Zv 0 ⊓ A₂) ⊔ pCoreOf 2 t.GT := by
  intro y hy
  by_cases hyQ : y ∈ pCoreOf 2 t.GT
  · exact Subgroup.mem_sup_right hyQ
  · obtain ⟨k, hkD2, hkcomm⟩ := hD₂trans c hcA₂ hcQ y hy hyQ
    have hkK : k ∈ t.K := Subgroup.mem_sup_right hkD2
    have hkcZ : k * c * k⁻¹ ∈ t.Zv 0 :=
      (Subgroup.mem_normalizer_iff.mp (hK_Z₁ hkK) c).mp hcZ
    have hkcA₂ : k * c * k⁻¹ ∈ A₂ :=
      (Subgroup.mem_normalizer_iff.mp (hK_A₂ hkK) c).mp hcA₂
    have hcomm : (k * c * k⁻¹) * y = y * (k * c * k⁻¹) :=
      hAc _ (Subgroup.mem_sup_right hkcA₂) y (Subgroup.mem_sup_right hy)
    have hyq : y = (k * c * k⁻¹) * (k * c * k⁻¹ * y⁻¹)⁻¹ := by
      calc y = (k * c * k⁻¹) * y * (k * c * k⁻¹)⁻¹ := by rw [hcomm]; group
        _ = (k * c * k⁻¹) * (k * c * k⁻¹ * y⁻¹)⁻¹ := by group
    rw [hyq]
    exact Subgroup.mul_mem_sup ⟨hkcZ, hkcA₂⟩ ((pCoreOf 2 t.GT).inv_mem hkcomm)

private theorem caseII_A_le_sup_of_A₂_le_sup {A A₂ : Subgroup G}
    (hA : A₂.map (MulAut.conj t.x₁).toMonoidHom = A)
    (hx₁Q : t.x₁ ∈ normalizer (pCoreOf 2 t.GT : Set G))
    (h : A₂ ≤ (t.Zv 0 ⊓ A₂) ⊔ pCoreOf 2 t.GT) :
    A ≤ (t.Zv 0 ⊓ A) ⊔ pCoreOf 2 t.GT := by
  have hmap := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) h
  rw [hA] at hmap
  have hZ₁map : (t.Zv 0).map (MulAut.conj t.x₁).toMonoidHom = t.Zv 0 := by
    simpa using t.map_Zv_x₁ 0
  have hQmap : (pCoreOf 2 t.GT).map (MulAut.conj t.x₁).toMonoidHom = pCoreOf 2 t.GT :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx₁Q
  have hR : ((t.Zv 0 ⊓ A₂) ⊔ pCoreOf 2 t.GT).map
      (MulAut.conj t.x₁).toMonoidHom = (t.Zv 0 ⊓ A) ⊔ pCoreOf 2 t.GT := by
    rw [Subgroup.map_sup, Subgroup.map_inf (t.Zv 0) A₂ (MulAut.conj t.x₁).toMonoidHom
      (MulAut.conj t.x₁).injective, hZ₁map, hA, hQmap]
  rwa [hR] at hmap

private theorem caseII_le_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {A A₂ : Subgroup G}
    (hZ₁Q : t.Zv 0 ⊓ pCoreOf 2 t.GT = ⊥) (hZ₁A : t.Zv 0 ≤ A ⊔ A₂)
    (hAA₂ : A ⊓ A₂ = pCoreOf 2 t.GT)
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x)
    (hA₂ : A.map (MulAut.conj t.x₁).toMonoidHom = A₂)
    (hA : A₂.map (MulAut.conj t.x₁).toMonoidHom = A)
    (hKA : t.K ≤ normalizer (A : Set G))
    (hD₂A : ∀ k ∈ t.D2, ∀ x ∈ A, k * x * k⁻¹ = x)
    (hD₂free : ∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ A₂,
      k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 t.GT → x ∈ pCoreOf 2 t.GT)
    (hD₂trans : ∀ x ∈ A₂, x ∉ pCoreOf 2 t.GT → ∀ y ∈ A₂, y ∉ pCoreOf 2 t.GT →
      ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ pCoreOf 2 t.GT) :
    A₂ ≤ (t.Zv 0 ⊓ A₂) ⊔ pCoreOf 2 t.GT ∧
      A ≤ (t.Zv 0 ⊓ A) ⊔ pCoreOf 2 t.GT := by
  have hA₂NA : A₂ ≤ normalizer (A : Set G) := le_normalizer_of_commutative_sup hAc
  have hK_A₂ : t.K ≤ normalizer (A₂ : Set G) := t.K_le_normalizer_of_map_conj hKA hA₂
  have hK_Z₁ : t.K ≤ normalizer (t.Zv 0 : Set G) := t.K_le_normalizer_Zv 0
  obtain ⟨z₀, hz₀Z1, k₁, hk₁D2, hc₀⟩ :=
    t.caseII_exists_commutator_not_mem hfr hZ₁Q hZ₁A hAA₂ hAc hA₂ hA₂NA hD₂A hD₂free
  obtain ⟨c, hcZ, hcA₂, hcQ⟩ :=
    t.caseII_commutator_mem_inf_not_mem hZ₁A hAc hA₂NA hK_A₂ hK_Z₁ hD₂A
      hz₀Z1 hk₁D2 hc₀
  have hA₂_le : A₂ ≤ (t.Zv 0 ⊓ A₂) ⊔ pCoreOf 2 t.GT :=
    t.caseII_A₂_le_sup_of_commutator hcZ hcA₂ hcQ hAc hK_A₂ hK_Z₁ hD₂trans
  exact ⟨hA₂_le, t.caseII_A_le_sup_of_A₂_le_sup hA
    t.x₁_mem_normalizer_pCoreOf_GT hA₂_le⟩

private theorem caseII_relIndex_A₂ {Q A A₂ : Subgroup G} {f : ℕ}
    (hAQ : Q.relIndex A = 2 ^ f) (hA₂ : A.map (MulAut.conj t.x₁).toMonoidHom = A₂)
    (hx₁Q : t.x₁ ∈ normalizer (Q : Set G)) :
    Q.relIndex A₂ = 2 ^ f := by
  have hQmap : Q.map (MulAut.conj t.x₁).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx₁Q
  have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj t.x₁).toMonoidHom)
    Q A (MulAut.conj t.x₁).injective
  rw [hQmap, hA₂, hAQ] at h
  exact h

private theorem caseII_elemsec_Z₁ : IsElemSec (⊥ : Subgroup G) (t.Zv 0) := by
  have hElem : IsElemAbelian 2 (t.Zv 0) := by
    rw [t.Zv_eq 0]
    exact CFSG.Quasithin.SmithC27.isElemAbelian_omegaOneCenterOf (t.Qv 0)
  refine ⟨bot_le, ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    have hcomm : x * y = y * x :=
      congrArg Subtype.val (hElem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [(commutatorElement_eq_one_iff_mul_comm).mpr hcomm]
    exact Subgroup.one_mem _
  · intro e he
    rw [show e ^ 2 = 1 from hElem.2 e he]
    exact Subgroup.one_mem _

private theorem caseII_L1_le_normalizer_Z₁ :
    L1 ≤ normalizer (t.Zv 0 : Set G) ⊓ normalizer (⊥ : Subgroup G) := by
  have hP1Z : P1 L1 L2 S ≤ normalizer (t.Zv 0 : Set G) := by
    rw [← t.Gv_zero]
    exact t.Gv_le_normalizer_Zv 0
  have hL1Z : L1 ≤ normalizer (t.Zv 0 : Set G) :=
    (le_sup_left : L1 ≤ P1 L1 L2 S).trans hP1Z
  refine le_inf hL1Z ?_
  rw [Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))]
  exact le_top

private theorem caseII_pCoreOf_centralizes_Z₁ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    ∀ p ∈ pCoreOf 2 L1, ∀ v ∈ t.Zv 0, ⁅p, v⁆ ∈ (⊥ : Subgroup G) := by
  intro p hp v hv
  have hpQ1 : p ∈ Q1 L1 L2 S := (Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1) hp
  have hpQ : p ∈ t.Qv 0 := by
    rw [t.Qv_zero]
    exact hpQ1
  have hpv : p * v = v * p :=
    ((Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer 0 hv)) p hpQ)
  rw [(commutatorElement_eq_one_iff_mul_comm).mpr hpv]
  exact Subgroup.one_mem _

private theorem caseII_pair_exists_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {A A₂ : Subgroup G}
    (hZ₁Q : t.Zv 0 ⊓ pCoreOf 2 t.GT = ⊥) (hZ₁A : t.Zv 0 ≤ A ⊔ A₂)
    (hAA₂ : A ⊓ A₂ = pCoreOf 2 t.GT)
    (hAQ : (pCoreOf 2 t.GT).relIndex A = 2 ^ f)
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x)
    (hA₂ : A.map (MulAut.conj t.x₁).toMonoidHom = A₂)
    (hsec : IsElemSec (⊥ : Subgroup G) (t.Zv 0))
    (hL : L1 ≤ normalizer (t.Zv 0 : Set G) ⊓ normalizer (⊥ : Subgroup G))
    (hQcent : ∀ p ∈ pCoreOf 2 L1, ∀ v ∈ t.Zv 0, ⁅p, v⁆ ∈ (⊥ : Subgroup G))
    (hnt : ∃ l ∈ L1, ∃ v ∈ t.Zv 0, ⁅l, v⁆ ≠ 1) :
    4 * (2 * a + 1) ≤ 2 * f := by
  have hnt' : ∃ l ∈ L1, ∃ v ∈ t.Zv 0, ⁅l, v⁆ ∉ (⊥ : Subgroup G) := by
    obtain ⟨l, hl, v, hv, hne⟩ := hnt
    exact ⟨l, hl, v, hv, fun h => hne (Subgroup.mem_bot.mp h)⟩
  have hkey := two_pow_le_relIndex_of_nontrivial_of_sz (L := L1) (V := t.Zv 0)
    (Z := ⊥) (a := a) hfr.ha hfr.hSz hsec hL hQcent hnt'
  rw [Subgroup.relIndex_bot_left] at hkey
  have hRQ : (pCoreOf 2 t.GT).relIndex A₂ = 2 ^ f :=
    t.caseII_relIndex_A₂ hAQ hA₂ t.x₁_mem_normalizer_pCoreOf_GT
  have hbound := card_le_relIndex_mul_relIndex (H := t.Zv 0) (Q := pCoreOf 2 t.GT)
    (A := A) (A₂ := A₂) hZ₁Q hZ₁A hAA₂ hAc
  rw [hAQ, hRQ] at hbound
  have h2 : 2 ^ (4 * (2 * a + 1)) ≤ 2 ^ f * 2 ^ f := hkey.trans hbound
  rw [← pow_add] at h2
  have h3 : 4 * (2 * a + 1) ≤ f + f :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega

private theorem caseII_no_pair_L1 {A X : Subgroup G} (hXdef : X = t.Zv 0 ⊓ A)
    (hL1cent : ∀ l ∈ L1, ∀ v ∈ t.Zv 0, l * v * l⁻¹ = v) :
    L1 ≤ (P1 L1 L2 S ⊓ normalizer (X : Set G)) ⊔ Q1 L1 L2 S := by
  refine le_sup_of_le_left (le_inf (le_sup_left : L1 ≤ P1 L1 L2 S) ?_)
  intro l hl
  rw [Subgroup.mem_normalizer_iff, hXdef]
  intro x
  constructor
  · intro hx
    have hxZ : x ∈ t.Zv 0 := hx.1
    have heq : l * x * l⁻¹ = x := hL1cent l hl x hxZ
    rwa [heq]
  · intro hx
    have hxZ : l * x * l⁻¹ ∈ t.Zv 0 := hx.1
    have heq : l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = l * x * l⁻¹ :=
      hL1cent l⁻¹ (L1.inv_mem hl) (l * x * l⁻¹) hxZ
    have hxe : x = l * x * l⁻¹ := by rw [← heq]; group
    rw [hxe]
    exact hx

private theorem caseII_no_pair_Lstar {A X Lstar : Subgroup G} (hXdef : X = t.Zv 0 ⊓ A)
    (hLA : ∀ l ∈ Lstar, ∀ x ∈ A, l * x * l⁻¹ = x) :
    Lstar ≤ normalizer (X : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff, hXdef]
  intro x
  constructor
  · intro hx
    have heq : l * x * l⁻¹ = x := hLA l hl x hx.2
    rwa [heq]
  · intro hx
    have heq : l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = l * x * l⁻¹ :=
      hLA l⁻¹ (Lstar.inv_mem hl) (l * x * l⁻¹) hx.2
    have hxe : x = l * x * l⁻¹ := by rw [← heq]; group
    rw [hxe]
    exact hx

private theorem caseII_no_pair_L2 {Lstar X : Subgroup G}
    (hLstar : Lstar ≤ L2 ⊔ t.Qv 1) (hL2 : L2 ≤ Lstar ⊔ t.Qv 1)
    (hstarN : Lstar ≤ normalizer (X : Set G)) :
    L2 ≤ (P2 L1 L2 S ⊓ normalizer (X : Set G)) ⊔ Q2 L1 L2 S := by
  have hLstar' : Lstar ≤ L2 ⊔ Q2 L1 L2 S := by simpa only [t.Qv_one] using hLstar
  have hL2' : L2 ≤ Lstar ⊔ Q2 L1 L2 S := by simpa only [t.Qv_one] using hL2
  have hLstarP2 : Lstar ≤ P2 L1 L2 S :=
    hLstar'.trans (sup_le (le_sup_left : L2 ≤ P2 L1 L2 S) (pCoreOf_le 2 (P2 L1 L2 S)))
  refine hL2'.trans (sup_le_sup ?_ le_rfl)
  exact le_inf hLstarP2 hstarN

private theorem caseII_false_of_centralizes {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {A A₂ Lstar : Subgroup G}
    (hAA₂ : A ⊓ A₂ = pCoreOf 2 t.GT)
    (hAQ : (pCoreOf 2 t.GT).relIndex A = 2 ^ f)
    (hZA : A ≤ (t.Zv 0 ⊓ A) ⊔ pCoreOf 2 t.GT)
    (hLstar : Lstar ≤ L2 ⊔ t.Qv 1) (hL2 : L2 ≤ Lstar ⊔ t.Qv 1)
    (hLA : ∀ l ∈ Lstar, ∀ x ∈ A, l * x * l⁻¹ = x)
    (hL1cent : ∀ l ∈ L1, ∀ v ∈ t.Zv 0, l * v * l⁻¹ = v) : False := by
  set X : Subgroup G := t.Zv 0 ⊓ A with hXdef
  have hXbigB : X ≤ bigB L1 L2 S := by
    rw [hXdef]
    intro x hx
    have hxQ1 : x ∈ Q1 L1 L2 S := by
      have h := t.Zv_le_Qv 0 hx.1
      rwa [t.Qv_zero] at h
    exact (le_sup_right : S ≤ bigB L1 L2 S) (Q1_le_S hfr.hF hxQ1)
  have h1 : L1 ≤ (P1 L1 L2 S ⊓ normalizer (X : Set G)) ⊔ Q1 L1 L2 S :=
    t.caseII_no_pair_L1 hXdef hL1cent
  have hstarN : Lstar ≤ normalizer (X : Set G) := t.caseII_no_pair_Lstar hXdef hLA
  have h2 : L2 ≤ (P2 L1 L2 S ⊓ normalizer (X : Set G)) ⊔ Q2 L1 L2 S :=
    t.caseII_no_pair_L2 hLstar hL2 hstarN
  have hF1 : Hyp111 L1 L2 S := hfr.hF.1
  have hXbot : X = ⊥ := eq_bot_of_le_bigB (X := X) hF1 hXbigB h1 h2
  have hAleQ : A ≤ pCoreOf 2 t.GT := by
    have h := hZA
    rw [hXbot, bot_sup_eq] at h
    exact h
  have hQleA : pCoreOf 2 t.GT ≤ A := by
    rw [← hAA₂]
    exact inf_le_left
  have hAeq : A = pCoreOf 2 t.GT := le_antisymm hAleQ hQleA
  have hone : (pCoreOf 2 t.GT).relIndex A = 1 := by
    rw [hAeq, Subgroup.relIndex_self]
  rw [hone] at hAQ
  have hgt : 1 < 2 ^ f := by
    calc 1 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  omega

private theorem caseII_four_mul_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {A A₂ Lstar : Subgroup G}
    (hZ₁Q : t.Zv 0 ⊓ pCoreOf 2 t.GT = ⊥) (hZ₁A : t.Zv 0 ≤ A ⊔ A₂)
    (hAA₂ : A ⊓ A₂ = pCoreOf 2 t.GT)
    (hAQ : (pCoreOf 2 t.GT).relIndex A = 2 ^ f)
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x)
    (hA₂ : A.map (MulAut.conj t.x₁).toMonoidHom = A₂)
    (hZA : A ≤ (t.Zv 0 ⊓ A) ⊔ pCoreOf 2 t.GT)
    (hLstar : Lstar ≤ L2 ⊔ t.Qv 1) (hL2 : L2 ≤ Lstar ⊔ t.Qv 1)
    (hLA : ∀ l ∈ Lstar, ∀ x ∈ A, l * x * l⁻¹ = x) : 4 * (2 * a + 1) ≤ 2 * f := by
  by_cases hnt : ∃ l ∈ L1, ∃ v ∈ t.Zv 0, ⁅l, v⁆ ≠ 1
  · exact t.caseII_pair_exists_le hfr hZ₁Q hZ₁A hAA₂ hAQ hAc hA₂
      t.caseII_elemsec_Z₁ t.caseII_L1_le_normalizer_Z₁
      (t.caseII_pCoreOf_centralizes_Z₁ hfr) hnt
  · push Not at hnt
    have hL1cent : ∀ l ∈ L1, ∀ v ∈ t.Zv 0, l * v * l⁻¹ = v := by
      intro l hl v hv
      have h1 : l * v = v * l := (commutatorElement_eq_one_iff_mul_comm).mp (hnt l hl v hv)
      calc l * v * l⁻¹ = v * l * l⁻¹ := by rw [h1]
        _ = v := by group
    exfalso
    exact t.caseII_false_of_centralizes hfr hAA₂ hAQ hZA hLstar hL2 hLA hL1cent

private theorem caseII_le_centralizer {A : Subgroup G} {k : G} (hk : k ∈ t.D2)
    (hD₂A : ∀ k ∈ t.D2, ∀ x ∈ A, k * x * k⁻¹ = x) :
    t.Zv 0 ⊓ A ≤ t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G) := by
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyk : y = k := by simpa using hy
  subst y
  have h1 := hD₂A k hk x hx.2
  calc k * x = (k * x * k⁻¹) * k := by group
    _ = x * k := by rw [h1]

private theorem caseII_L1_mem_normalizer_centralizer {C : Subgroup G} {k : G}
    (hCdef : C = t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G))
    (hkL : ∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ Q1 L1 L2 S) :
    ∀ l ∈ L1, ∀ x ∈ C, l * x * l⁻¹ ∈ C := by
  intro l hl x hx
  rw [hCdef] at hx ⊢
  have hL1Z : L1 ≤ normalizer (t.Zv 0 : Set G) := by
    have hP1Z : P1 L1 L2 S ≤ normalizer (t.Zv 0 : Set G) := by
      rw [← t.Gv_zero]
      exact t.Gv_le_normalizer_Zv 0
    exact (le_sup_left : L1 ≤ P1 L1 L2 S).trans hP1Z
  have hxZ : x ∈ t.Zv 0 := hx.1
  have hxk : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hx.2) k (by simp)
  have hlx : l * x * l⁻¹ ∈ t.Zv 0 := (Subgroup.mem_normalizer_iff.mp (hL1Z hl) x).mp hxZ
  refine Subgroup.mem_inf.mpr ⟨hlx, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyk : y = k := by simpa using hy
  subst y
  have hqQ : k * l * k⁻¹ * l⁻¹ ∈ t.Qv 0 := by
    rw [t.Qv_zero]
    exact hkL l hl
  have hqy : (k * l * k⁻¹ * l⁻¹) * (l * x * l⁻¹) =
      (l * x * l⁻¹) * (k * l * k⁻¹ * l⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer 0 hlx) _ hqQ
  have hkey : k * (l * x * l⁻¹) * k⁻¹ = l * x * l⁻¹ := by
    have h1 : k * l * k⁻¹ = (k * l * k⁻¹ * l⁻¹) * l := by group
    have h2 : k * x * k⁻¹ = x := by rw [hxk]; group
    calc k * (l * x * l⁻¹) * k⁻¹
        = (k * l * k⁻¹) * (k * x * k⁻¹) * (k * l * k⁻¹)⁻¹ := by group
      _ = (k * l * k⁻¹) * x * (k * l * k⁻¹)⁻¹ := by rw [h2]
      _ = ((k * l * k⁻¹ * l⁻¹) * l) * x * ((k * l * k⁻¹ * l⁻¹) * l)⁻¹ := by
            conv_lhs => rw [h1]
      _ = (k * l * k⁻¹ * l⁻¹) * (l * x * l⁻¹) * (k * l * k⁻¹ * l⁻¹)⁻¹ := by group
      _ = l * x * l⁻¹ := by rw [hqy]; group
  calc k * (l * x * l⁻¹) = (k * (l * x * l⁻¹) * k⁻¹) * k := by group
    _ = (l * x * l⁻¹) * k := by rw [hkey]

private theorem caseII_L1_le_normalizer_centralizer {C : Subgroup G} {k : G}
    (hCdef : C = t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G))
    (hkL : ∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ Q1 L1 L2 S) :
    L1 ≤ normalizer (C : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact t.caseII_L1_mem_normalizer_centralizer hCdef hkL l hl x
  · intro hx
    have := t.caseII_L1_mem_normalizer_centralizer hCdef hkL l⁻¹ (L1.inv_mem hl)
      (l * x * l⁻¹) hx
    rwa [show l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x from by group] at this

private theorem caseII_Q1_mem_normalizer_centralizer {C : Subgroup G} {k : G}
    (hCdef : C = t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G)) :
    ∀ q ∈ Q1 L1 L2 S, ∀ x ∈ C, q * x * q⁻¹ ∈ C := by
  intro q hq x hx
  rw [hCdef] at hx ⊢
  have hqQ : q ∈ t.Qv 0 := by
    rw [t.Qv_zero]
    exact hq
  have hqcomm : q * x = x * q :=
    Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer 0 hx.1) q hqQ
  have hconj : q * x * q⁻¹ = x := by
    calc q * x * q⁻¹ = x * q * q⁻¹ := by rw [hqcomm]
      _ = x := by group
  rwa [hconj]

private theorem caseII_Q1_le_normalizer_centralizer {C : Subgroup G} {k : G}
    (hCdef : C = t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G)) :
    Q1 L1 L2 S ≤ normalizer (C : Set G) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact t.caseII_Q1_mem_normalizer_centralizer hCdef q hq x
  · intro hx
    have := t.caseII_Q1_mem_normalizer_centralizer hCdef q⁻¹ ((Q1 L1 L2 S).inv_mem hq)
      (q * x * q⁻¹) hx
    rwa [show q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹ = x from by group] at this

private theorem caseII_K_mem_normalizer_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {C : Subgroup G} {k : G} (hk : k ∈ t.D2)
    (hCdef : C = t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G)) :
    ∀ h ∈ t.K, ∀ x ∈ C, h * x * h⁻¹ ∈ C := by
  intro h hh x hx
  rw [hCdef] at hx ⊢
  have hkK : k ∈ t.K := Subgroup.mem_sup_right hk
  have hxk : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hx.2) k (by simp)
  have hkh : k * h = h * k := t.K_comm hfr k hkK h hh
  have hh1 : h⁻¹ * k * h = k := by
    calc h⁻¹ * k * h = h⁻¹ * (k * h) := by group
      _ = h⁻¹ * (h * k) := by rw [hkh]
      _ = k := by group
  refine Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_normalizer_iff.mp (t.K_le_normalizer_Zv 0 hh) x).mp hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyk : y = k := by simpa using hy
  subst y
  have hkey : k * (h * x * h⁻¹) * k⁻¹ = h * x * h⁻¹ := by
    calc k * (h * x * h⁻¹) * k⁻¹ =
          h * (h⁻¹ * k * h) * x * (h⁻¹ * k * h)⁻¹ * h⁻¹ := by group
      _ = h * k * x * k⁻¹ * h⁻¹ := by rw [hh1]
      _ = h * (k * x) * k⁻¹ * h⁻¹ := by group
      _ = h * (x * k) * k⁻¹ * h⁻¹ := by rw [hxk]
      _ = h * x * k * k⁻¹ * h⁻¹ := by group
      _ = h * x * h⁻¹ := by group
  calc k * (h * x * h⁻¹) = (k * (h * x * h⁻¹) * k⁻¹) * k := by group
    _ = (h * x * h⁻¹) * k := by rw [hkey]

private theorem caseII_K_le_normalizer_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {C : Subgroup G} {k : G} (hk : k ∈ t.D2)
    (hCdef : C = t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G)) :
    t.K ≤ normalizer (C : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact t.caseII_K_mem_normalizer_centralizer hfr hk hCdef h hh x
  · intro hx
    have := t.caseII_K_mem_normalizer_centralizer hfr hk hCdef h⁻¹ (t.K.inv_mem hh)
      (h * x * h⁻¹) hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * (h⁻¹)⁻¹ = x from by group] at this

private theorem caseII_centralizer_map {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {k : G} (hk : k ∈ t.D2)
    (hkL : ∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ Q1 L1 L2 S) :
    (t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G)).map
      (MulAut.conj t.x₁).toMonoidHom =
        t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G) := by
  let C : Subgroup G := t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G)
  have hCdef : C = t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G) := rfl
  have hL1N := t.caseII_L1_le_normalizer_centralizer hCdef hkL
  have hQ1N := t.caseII_Q1_le_normalizer_centralizer hCdef
  have hKN := t.caseII_K_le_normalizer_centralizer hfr hk hCdef
  have hP1N : P1 L1 L2 S ≤ normalizer (C : Set G) :=
    (t.P1_le_sup hfr).trans (sup_le (sup_le hL1N hQ1N) hKN)
  have hx₁N : t.x₁ ∈ normalizer (C : Set G) :=
    hP1N (by rw [← t.Gv_zero]; exact t.x₁_mem_Gv_zero)
  change C.map (MulAut.conj t.x₁).toMonoidHom = C
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hx₁N

private theorem caseII_eq_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {A A₂ : Subgroup G}
    (hQA : pCoreOf 2 t.GT ≤ A) (hA₂Q : ¬ A₂ ≤ pCoreOf 2 t.GT)
    (hA₂ : A.map (MulAut.conj t.x₁).toMonoidHom = A₂)
    (hD₂A : ∀ k ∈ t.D2, ∀ x ∈ A, k * x * k⁻¹ = x)
    (hD₂free : ∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ A₂,
      k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 t.GT → x ∈ pCoreOf 2 t.GT)
    (hZA₂ : A₂ ≤ (t.Zv 0 ⊓ A₂) ⊔ pCoreOf 2 t.GT) {k : G} (hk : k ∈ t.D2)
    (hkL : ∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ Q1 L1 L2 S) : k = 1 := by
  let Q : Subgroup G := pCoreOf 2 t.GT
  let C : Subgroup G := t.Zv 0 ⊓ Subgroup.centralizer ({k} : Set G)
  have hCmap : C.map (MulAut.conj t.x₁).toMonoidHom = C :=
    t.caseII_centralizer_map hfr hk hkL
  have hCge : t.Zv 0 ⊓ A ≤ C := t.caseII_le_centralizer hk hD₂A
  have hZ₁map : (t.Zv 0).map (MulAut.conj t.x₁).toMonoidHom = t.Zv 0 := by
    simpa using t.map_Zv_x₁ 0
  have hZA₂C : t.Zv 0 ⊓ A₂ ≤ C := by
    have hmono := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) hCge
    rw [hCmap, Subgroup.map_inf (t.Zv 0) A (MulAut.conj t.x₁).toMonoidHom
      (MulAut.conj t.x₁).injective, hZ₁map, hA₂] at hmono
    exact hmono
  have hkQ : ∀ x ∈ Q, k * x * k⁻¹ = x := fun x hx => hD₂A k hk x (hQA hx)
  have hZ₂fix : t.Zv 0 ⊓ A₂ ≤ Subgroup.centralizer ({k} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzy : z = k := by simpa using hz
    subst z
    have h2 := hZA₂C hy
    have h1 : k * y = y * k := (Subgroup.mem_centralizer_iff.mp h2.2) k (by simp)
    exact h1
  have hQfix : Q ≤ Subgroup.centralizer ({k} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzy : z = k := by simpa using hz
    subst z
    have h2 := hkQ y hy
    calc k * y = (k * y * k⁻¹) * k := by group
      _ = y * k := by rw [h2]
  have hkA₂ : ∀ x ∈ A₂, k * x * k⁻¹ = x := by
    intro x hx
    have hxfix : x ∈ Subgroup.centralizer ({k} : Set G) :=
      (sup_le hZ₂fix hQfix) (hZA₂ hx)
    have h1 : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hxfix) k (by simp)
    calc k * x * k⁻¹ = x * k * k⁻¹ := by rw [h1]
      _ = x := by group
  by_cases hk1 : k = 1
  · exact hk1
  · exfalso
    obtain ⟨x, hxA₂, hxQ⟩ := Set.not_subset.mp hA₂Q
    have hcomm : k * x * k⁻¹ * x⁻¹ = 1 := by
      rw [hkA₂ x hxA₂]
      group
    exact hxQ (hD₂free k hk hk1 x hxA₂ (by rw [hcomm]; exact Q.one_mem))

private theorem caseII_D2_le_normalizer_L1 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.D2 ≤ normalizer (L1 : Set G) := by
  have hD2K : t.D2 ≤ t.K := le_sup_right
  have hKbigB : t.K ≤ bigB L1 L2 S := by
    rw [← t.sup_K_eq_bigB]
    exact le_sup_right
  exact (hD2K.trans hKbigB).trans (bigB_le_normalizer_of_hyp111 hfr.hF.1)

private theorem caseII_D2_le_normalizer_T {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.D2 ≤ normalizer (S ⊓ L1 : Set G) := by
  have hD2K : t.D2 ≤ t.K := le_sup_right
  have hKbigB : t.K ≤ bigB L1 L2 S := by
    rw [← t.sup_K_eq_bigB]
    exact le_sup_right
  have hD2S : t.D2 ≤ normalizer (S : Set G) := (hD2K.trans hKbigB).trans hfr.hN
  have hD2L1 : t.D2 ≤ normalizer (L1 : Set G) :=
    (hD2K.trans hKbigB).trans (bigB_le_normalizer_of_hyp111 hfr.hF.1)
  intro d hd
  exact CFSG.Quasithin.A4.mem_normalizer_inf (hD2S hd) (hD2L1 hd)

private theorem caseII_D1_conj_mem_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {k : G} (hk : k ∈ t.D2) :
    ∀ d ∈ t.D1, ∀ x ∈ caseIICentralizer L1 S k, d * x * d⁻¹ ∈ caseIICentralizer L1 S k := by
  have hXmem : ∀ y : G, y ∈ caseIICentralizer L1 S k ↔
      y ∈ S ⊓ L1 ∧ ∀ t ∈ Subgroup.zpowers k, ⁅y, t⁆ ∈ pCoreOf 2 L1 := by
    intro y
    simp only [caseIICentralizer]
    exact mem_commutatorCentralizerIn _
  have hkK : k ∈ t.K := Subgroup.mem_sup_right hk
  intro d hd x hx
  have hdB : d ∈ borelOf L1 S := t.hD1hall.1 hd
  have hdT : d ∈ normalizer (S ⊓ L1 : Set G) := hdB.2
  have hdO : d ∈ normalizer (pCoreOf 2 L1 : Set G) := (le_normalizer_pCoreOf 2 L1) hdB.1
  have hdk : d * k = k * d := t.K_comm hfr d (Subgroup.mem_sup_left hd) k hkK
  have hdt : ∀ n : ℤ, d⁻¹ * k ^ n * d = k ^ n := by
    intro n
    have h1 : d⁻¹ * k * d = k := by
      calc d⁻¹ * k * d = d⁻¹ * (k * d) := by group
        _ = d⁻¹ * (d * k) := by rw [← hdk]
        _ = k := by group
    have h2 := conj_zpow (a := d⁻¹) (b := k) (i := n)
    simpa [h1] using h2.symm
  obtain ⟨hxT, hxcond⟩ := (hXmem x).mp hx
  refine (hXmem (d * x * d⁻¹)).mpr
    ⟨(Subgroup.mem_normalizer_iff.mp hdT x).mp hxT, fun t ht => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hdt' : d * k ^ n * d⁻¹ = k ^ n := by
    calc d * k ^ n * d⁻¹ = d * (d⁻¹ * k ^ n * d) * d⁻¹ := by rw [hdt n]
      _ = k ^ n := by group
  have hconj := conjugate_commutatorElement (g₁ := x) (g₂ := k ^ n) (g₃ := d)
  rw [hdt'] at hconj
  rw [← hconj]
  exact (Subgroup.mem_normalizer_iff.mp hdO _).mp (hxcond (k ^ n) (Subgroup.zpow_mem_zpowers k n))

private theorem caseII_D1_le_normalizer_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {k : G} (hk : k ∈ t.D2) :
    t.D1 ≤ normalizer (caseIICentralizer L1 S k : Set G) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact t.caseII_D1_conj_mem_centralizer hfr hk d hd x
  · intro hx
    have := t.caseII_D1_conj_mem_centralizer hfr hk d⁻¹ (t.D1.inv_mem hd) (d * x * d⁻¹) hx
    rwa [show d⁻¹ * (d * x * d⁻¹) * (d⁻¹)⁻¹ = x from by group] at this

private theorem caseII_centralizer_not_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {k z : G} (hk : k ∈ t.D2) (hz : z ∈ S ⊓ L1)
    (hzO : z ∉ pCoreOf 2 L1) (hcomm : ⁅k, z⁆ ∈ pCoreOf 2 L1) :
    ¬ caseIICentralizer L1 S k ≤ pCoreOf 2 L1 := by
  intro hle
  have hXmem : ∀ y : G, y ∈ caseIICentralizer L1 S k ↔
      y ∈ S ⊓ L1 ∧ ∀ t ∈ Subgroup.zpowers k, ⁅y, t⁆ ∈ pCoreOf 2 L1 := by
    intro y
    simp only [caseIICentralizer]
    exact mem_commutatorCentralizerIn _
  have hkO : k ∈ normalizer (pCoreOf 2 L1 : Set G) :=
    (normalizer_le_normalizer_pCoreOf 2 L1) ((t.caseII_D2_le_normalizer_L1 hfr) hk)
  have hcomm' : ⁅z, k⁆ ∈ pCoreOf 2 L1 := by
    have h2 : ⁅k, z⁆⁻¹ ∈ pCoreOf 2 L1 := (pCoreOf 2 L1).inv_mem hcomm
    rwa [commutatorElement_inv] at h2
  have hkS : k ∈ commutatorCentralizerMod (pCoreOf 2 L1) z := ⟨hkO, hcomm'⟩
  have hzp : Subgroup.zpowers k ≤ commutatorCentralizerMod (pCoreOf 2 L1) z :=
    Subgroup.zpowers_le.mpr hkS
  have hzX : z ∈ caseIICentralizer L1 S k :=
    (hXmem z).mpr ⟨hz, fun t ht => (hzp ht).2⟩
  exact hzO (hle hzX)

private theorem caseII_centers_of_sq_mem {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {k : G} (hk : k ∈ t.D2)
    (hD1N : t.D1 ≤ normalizer (caseIICentralizer L1 S k : Set G))
    (hnotle : ¬ caseIICentralizer L1 S k ≤ pCoreOf 2 L1) :
    ∀ x ∈ S ⊓ L1, x * x ∈ pCoreOf 2 L1 → ⁅k, x⁆ ∈ pCoreOf 2 L1 := by
  have hXmem : ∀ y : G, y ∈ caseIICentralizer L1 S k ↔
      y ∈ S ⊓ L1 ∧ ∀ t ∈ Subgroup.zpowers k, ⁅y, t⁆ ∈ pCoreOf 2 L1 := by
    intro y
    simp only [caseIICentralizer]
    exact mem_commutatorCentralizerIn _
  have hXT : caseIICentralizer L1 S k ≤ S ⊓ L1 := fun y hy => ((hXmem y).mp hy).1
  have hT : IsSylowTwoOf (S ⊓ L1) L1 := hfr.hF.1.h1.sylow
  intro x hxT hxx
  have hxX : x ∈ caseIICentralizer L1 S k ⊔ pCoreOf 2 L1 :=
    mem_sup_pCoreOf_of_torus_of_sz (L := L1) (T := S ⊓ L1) (D := t.D1)
      (X := caseIICentralizer L1 S k) (a := a) hfr.ha hfr.hSz hT t.hD1hall hXT hD1N hnotle
      x hxT hxx
  have hXTO : caseIICentralizer L1 S k ≤ normalizer (pCoreOf 2 L1 : Set G) :=
    hXT.trans (inf_le_right.trans (le_normalizer_pCoreOf 2 L1))
  obtain ⟨a, haX, b, hbO, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hXTO).mp hxX
  have hkO : k ∈ normalizer (pCoreOf 2 L1 : Set G) :=
    (normalizer_le_normalizer_pCoreOf 2 L1) ((t.caseII_D2_le_normalizer_L1 hfr) hk)
  have hka : ⁅k, a⁆ ∈ pCoreOf 2 L1 := by
    have h1 : ⁅a, k⁆ ∈ pCoreOf 2 L1 := ((hXmem a).mp haX).2 k (Subgroup.mem_zpowers k)
    have h2 : ⁅a, k⁆⁻¹ ∈ pCoreOf 2 L1 := (pCoreOf 2 L1).inv_mem h1
    rwa [commutatorElement_inv] at h2
  have hkb : ⁅k, b⁆ ∈ pCoreOf 2 L1 := by
    rw [commutatorElement_def]
    exact (pCoreOf 2 L1).mul_mem
      ((Subgroup.mem_normalizer_iff.mp hkO b).mp hbO) ((pCoreOf 2 L1).inv_mem hbO)
  have hconj : a * ⁅k, b⁆ * a⁻¹ ∈ pCoreOf 2 L1 :=
    (Subgroup.mem_normalizer_iff.mp (hXTO haX) _).mp hkb
  rw [commutatorElement_mul_right_eq_mul_conj]
  simpa [mul_assoc] using (pCoreOf 2 L1).mul_mem hka hconj

private theorem caseII_commutator_eq_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hX₀ : ∀ k ∈ t.D2, (∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ Q1 L1 L2 S) → k = 1)
    {z k : G} (hz : z ∈ S ⊓ L1)
    (hzO : z ∉ pCoreOf 2 L1) (hk : k ∈ t.D2) (hcomm : ⁅k, z⁆ ∈ pCoreOf 2 L1) :
    k = 1 := by
  have hD1N := t.caseII_D1_le_normalizer_centralizer hfr hk
  have hnotle := t.caseII_centralizer_not_le hfr hk hz hzO hcomm
  have hcent := t.caseII_centers_of_sq_mem hfr hk hD1N hnotle
  have hT : IsSylowTwoOf (S ⊓ L1) L1 := hfr.hF.1.h1.sylow
  have hkL1 : k ∈ normalizer (L1 : Set G) := (t.caseII_D2_le_normalizer_L1 hfr) hk
  have hodd : Odd (orderOf k) :=
    t.hD2hall.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard t.D2 hk)
  have hall := commutator_mem_pCoreOf_of_odd_of_sz (L := L1) (T := S ⊓ L1) (a := a)
    hfr.ha hfr.hSz hT hkL1 hodd hcent
  have hkL : ∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ Q1 L1 L2 S := by
    intro l hl
    exact (Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1) (hall l hl)
  exact hX₀ k hk hkL

private theorem caseII_le_of_eq_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hX₀ : ∀ k ∈ t.D2, (∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ Q1 L1 L2 S) → k = 1) :
    f ≤ 2 * a + 1 := by
  obtain ⟨z, hzT, hzz, hzO⟩ :=
    exists_sq_mem_not_mem_pCoreOf_of_sz (L := L1) (T := S ⊓ L1) (a := a)
      hfr.ha hfr.hSz hfr.hF.1.h1.sylow
  have hfree : ∀ k ∈ t.D2, ⁅k, z⁆ ∈ pCoreOf 2 L1 → k = 1 :=
    fun k hk hcomm => t.caseII_commutator_eq_one hfr hX₀ hzT hzO hk hcomm
  have hcard := card_le_of_commutator_mem_imp_eq_one_of_sz (L := L1) (T := S ⊓ L1)
    (H := t.D2) (a := a) hfr.ha hfr.hSz hfr.hF.1.h1.sylow
    (t.caseII_D2_le_normalizer_T hfr) (t.caseII_D2_le_normalizer_L1 hfr) hzT hzz hzO hfree
  rw [t.card_D2 hfr] at hcard
  have h2 : 2 ^ f ≤ 2 ^ (2 * a + 1) :=
    (Nat.sub_le_sub_iff_right Nat.one_le_two_pow).mp hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2

theorem false_of_caseII {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {A A₂ Lstar : Subgroup G}
    (hZ₁Q : t.Zv 0 ⊓ pCoreOf 2 t.GT = ⊥) (hZ₁A : t.Zv 0 ≤ A ⊔ A₂)
    (hAA₂ : A ⊓ A₂ = pCoreOf 2 t.GT) (hAQ : (pCoreOf 2 t.GT).relIndex A = 2 ^ f)
    (hAc : ∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x)
    (hA₂ : A.map (MulAut.conj t.x₁).toMonoidHom = A₂)
    (hA : A₂.map (MulAut.conj t.x₁).toMonoidHom = A)
    (hKA : t.K ≤ normalizer (A : Set G))
    (hD₂A : ∀ k ∈ t.D2, ∀ x ∈ A, k * x * k⁻¹ = x)
    (hD₂free : ∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ A₂,
      k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 t.GT → x ∈ pCoreOf 2 t.GT)
    (hD₂trans : ∀ x ∈ A₂, x ∉ pCoreOf 2 t.GT → ∀ y ∈ A₂, y ∉ pCoreOf 2 t.GT →
      ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ pCoreOf 2 t.GT)
    (hLstar : Lstar ≤ L2 ⊔ t.Qv 1) (hL2 : L2 ≤ Lstar ⊔ t.Qv 1)
    (hLA : ∀ l ∈ Lstar, ∀ x ∈ A, l * x * l⁻¹ = x) : False := by
  let Q : Subgroup G := pCoreOf 2 t.GT
  have hQA : Q ≤ A := by
    change pCoreOf 2 t.GT ≤ A
    rw [← hAA₂]
    exact inf_le_left
  have hx₁Q : t.x₁ ∈ normalizer (Q : Set G) := t.x₁_mem_normalizer_pCoreOf_GT
  have hA₂Q : ¬ A₂ ≤ Q := by
    intro hle
    have hA₂eq : A₂ = Q := le_antisymm hle (by
      change pCoreOf 2 t.GT ≤ A₂
      rw [← hAA₂]
      exact inf_le_right)
    have hmapQ : Q.map (MulAut.conj t.x₁).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hx₁Q
    have hAeq : A = Q := by
      rw [← hA, hA₂eq, hmapQ]
    have hone : Q.relIndex A = 1 := by rw [hAeq, Subgroup.relIndex_self]
    rw [hone] at hAQ
    have hgt : 1 < 2 ^ f := by
      calc 1 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
    omega
  obtain ⟨hZA₂, hZA⟩ :=
    t.caseII_le_sup hfr hZ₁Q hZ₁A hAA₂ hAc hA₂ hA hKA hD₂A hD₂free hD₂trans
  have hc := t.caseII_four_mul_le hfr hZ₁Q hZ₁A hAA₂ hAQ hAc hA₂ hZA hLstar hL2 hLA
  have hd : ∀ k ∈ t.D2, (∀ l ∈ L1, k * l * k⁻¹ * l⁻¹ ∈ Q1 L1 L2 S) → k = 1 :=
    fun k hk hkL => t.caseII_eq_one hfr hQA hA₂Q hA₂ hD₂A hD₂free hZA₂ hk hkL
  have he := t.caseII_le_of_eq_one hfr hd
  omega

end Track

end CFSG.Quasithin.Stroth.Rq

end
