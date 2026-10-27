module

public import CFSG.Quasithin.Recognition.Kleidman.F204.O2T

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.OrderReductions.FrattiniAutomorphisms CFSG
  CFSG.QuasithinUnique.A5.Delta5

open scoped IsMulCommutative commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X Z : Subgroup G}

abbrev PhiG (L1 L2 S : Subgroup G) : Subgroup G := (frattini ↥(Q1 L1 L2 S)).map (Q1 L1 L2 S).subtype

section Frat

variable (F : Frame L1 L2 S D X)
include F

theorem conj_PhiG {g w : G} (hg : g ∈ P1 L1 L2 S) (hw : w ∈ PhiG L1 L2 S) :
    g * w * g⁻¹ ∈ PhiG L1 L2 S := by
  obtain ⟨φ, hφ, rfl⟩ := hw
  let σ : MulAut ↥(Q1 L1 L2 S) :=
    (Q1 L1 L2 S).normalizerMonoidHom (Subgroup.inclusion (P1_le_normalizer_Q1 L1 L2 S) ⟨g, hg⟩)
  have hfix := (inferInstance : (frattini ↥(Q1 L1 L2 S)).Characteristic).fixed σ
  have h1 : σ φ ∈ frattini ↥(Q1 L1 L2 S) := by
    have : φ ∈ (frattini ↥(Q1 L1 L2 S)).comap σ.toMonoidHom := by rw [hfix]; exact hφ
    exact this
  exact ⟨σ φ, h1, rfl⟩

theorem PhiG_le_Q2 {w : G} (hw : w ∈ PhiG L1 L2 S) : w ∈ Q2 L1 L2 S := by
  obtain ⟨φ, hφ, rfl⟩ := hw
  exact frattini_le_R0Q F hφ

theorem normalizer_PhiG {g : G} (hg : g ∈ P1 L1 L2 S) :
    g ∈ Subgroup.normalizer ((PhiG L1 L2 S : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_PhiG F hg hh, fun hh => ?_⟩
  have := conj_PhiG F ((P1 L1 L2 S).inv_mem hg) hh
  simpa [mul_assoc] using this

end Frat

section FratMain

variable (hZ : ZData L1 L2 S Z) {a x0 : G} (ha : a ∈ Frame.Z2 L1 L2 S Z) (haQ : a ∉ Q1 L1 L2 S)
  (hx0 : x0 ∈ X) (hx05 : x0 ^ 5 = 1) (F : Frame L1 L2 S D X)
include F hZ ha haQ hx0 hx05

theorem x0_centralizes_frattini {w : G} (hw : w ∈ PhiG L1 L2 S) : x0 * w * x0⁻¹ = w := by
  have hx0P : x0 ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx0
  have haS : a ∈ S := F.Q2_le_S (F.Z2_le_Q2 hZ ha)
  have haa : a * a = 1 := F.Z2_sq hZ a ha
  obtain ⟨q, hq, hrel⟩ := F.inv_of_involution haS (by rw [haa]; exact (Q1 L1 L2 S).one_mem) haQ hx0
  have hq'Q : x0 * q * x0⁻¹ ∈ Q1 L1 L2 S := x0_conj_Q1 F hx0 hq
  set q' := x0 * q * x0⁻¹ with hq'
  set a1 := x0 * a * x0⁻¹ with ha1
  have hcentA : ∀ w ∈ PhiG L1 L2 S, a * w = w * a := fun w hw =>
    F.Z2_comm hZ a ha w (PhiG_le_Q2 F hw)
  have hcentA1 : ∀ w ∈ PhiG L1 L2 S, a1 * w = w * a1 := by
    intro w hw
    have hw' : x0⁻¹ * w * (x0⁻¹)⁻¹ ∈ PhiG L1 L2 S :=
      conj_PhiG F ((P1 L1 L2 S).inv_mem hx0P) hw
    have hc := hcentA _ hw'
    simp only [inv_inv] at hc
    calc a1 * w = x0 * (a * (x0⁻¹ * w * x0)) * x0⁻¹ := by rw [ha1]; group
      _ = x0 * ((x0⁻¹ * w * x0) * a) * x0⁻¹ := by rw [hc]
      _ = w * a1 := by rw [ha1]; group
  have hx2 : x0⁻¹ * x0⁻¹ = a * a1⁻¹ * q'⁻¹ := by
    have h1 : a * a1⁻¹ * q'⁻¹ = (a * x0 * a⁻¹) * q⁻¹ * x0⁻¹ := by rw [ha1, hq']; group
    rw [h1, hrel]; group
  have hclaim : ∀ w ∈ PhiG L1 L2 S,
      (x0⁻¹ * x0⁻¹) * w * (x0⁻¹ * x0⁻¹)⁻¹ = q'⁻¹ * w * (q'⁻¹)⁻¹ := by
    intro w hw
    have hq'P : q'⁻¹ ∈ P1 L1 L2 S := (P1 L1 L2 S).inv_mem (Q1_mem_P1 hq'Q)
    have hw'' : q'⁻¹ * w * (q'⁻¹)⁻¹ ∈ PhiG L1 L2 S := conj_PhiG F hq'P hw
    set w'' := q'⁻¹ * w * (q'⁻¹)⁻¹ with hw''def
    have h1 : a1⁻¹ * w'' * a1 = w'' := by
      rw [mul_assoc, ← hcentA1 w'' hw'', ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : a * w'' * a⁻¹ = w'' := by
      rw [hcentA w'' hw'']; group
    rw [hx2]
    calc a * a1⁻¹ * q'⁻¹ * w * (a * a1⁻¹ * q'⁻¹)⁻¹
        = a * (a1⁻¹ * (q'⁻¹ * w * (q'⁻¹)⁻¹) * a1) * a⁻¹ := by group
      _ = w'' := by rw [← hw''def, h1, h2]
  have hg1P : (x0⁻¹ * x0⁻¹) ∈ P1 L1 L2 S :=
    (P1 L1 L2 S).mul_mem ((P1 L1 L2 S).inv_mem hx0P) ((P1 L1 L2 S).inv_mem hx0P)
  have hg2P : q'⁻¹ ∈ P1 L1 L2 S := (P1 L1 L2 S).inv_mem (Q1_mem_P1 hq'Q)
  set e1 := (PhiG L1 L2 S).normalizerMonoidHom
    (⟨x0⁻¹ * x0⁻¹, normalizer_PhiG F hg1P⟩ :
      Subgroup.normalizer ((PhiG L1 L2 S : Subgroup G) : Set G)) with he1
  set e2 := (PhiG L1 L2 S).normalizerMonoidHom
    (⟨q'⁻¹, normalizer_PhiG F hg2P⟩ :
      Subgroup.normalizer ((PhiG L1 L2 S : Subgroup G) : Set G)) with he2
  have he12 : e1 = e2 := by
    refine MulEquiv.ext fun w => Subtype.ext ?_
    show (x0⁻¹ * x0⁻¹) * (w : G) * (x0⁻¹ * x0⁻¹)⁻¹ = q'⁻¹ * (w : G) * (q'⁻¹)⁻¹
    exact hclaim w w.2
  have he15 : e1 ^ 5 = 1 := by
    rw [he1, ← map_pow]
    have : (⟨x0⁻¹ * x0⁻¹, normalizer_PhiG F hg1P⟩ :
        Subgroup.normalizer ((PhiG L1 L2 S : Subgroup G) : Set G)) ^ 5 = 1 := by
      apply Subtype.ext
      show (x0⁻¹ * x0⁻¹) ^ 5 = 1
      rw [(Commute.refl x0⁻¹).mul_pow, inv_pow, hx05]
      simp
    rw [this, map_one]
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (P1 L1 L2 S) (⟨q', hq'Q⟩ : ↥(Q1 L1 L2 S))
  have hk' : q' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have he2k : e2 ^ 2 ^ k = 1 := by
    rw [he2, ← map_pow]
    have : (⟨q'⁻¹, normalizer_PhiG F hg2P⟩ :
        Subgroup.normalizer ((PhiG L1 L2 S : Subgroup G) : Set G)) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      show (q'⁻¹) ^ 2 ^ k = 1
      rw [inv_pow, hk', inv_one]
    rw [this, map_one]
  have hg : Nat.gcd 5 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  have he1k : e1 ^ 2 ^ k = 1 := by rw [he12]; exact he2k
  have he1one : e1 = 1 := by
    have := pow_gcd_eq_one.mpr ⟨he15, he1k⟩
    rw [hg, pow_one] at this
    exact this
  have hc : ∀ v ∈ PhiG L1 L2 S, (x0⁻¹ * x0⁻¹) * v * (x0⁻¹ * x0⁻¹)⁻¹ = v := by
    intro v hv
    have h1 : e1 ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [he1one]; rfl
    exact congrArg Subtype.val h1
  have hgg : (x0⁻¹ * x0⁻¹) * (x0⁻¹ * x0⁻¹) = x0 := by
    have : (x0⁻¹ * x0⁻¹) * (x0⁻¹ * x0⁻¹) = (x0 ^ 5)⁻¹ * x0 := by group
    rw [this, hx05]; simp
  have hcw := hc w hw
  have hcw2 := hc _ (conj_PhiG F hg1P hw)
  calc x0 * w * x0⁻¹ = ((x0⁻¹ * x0⁻¹) * (x0⁻¹ * x0⁻¹)) * w *
        ((x0⁻¹ * x0⁻¹) * (x0⁻¹ * x0⁻¹))⁻¹ := by rw [hgg]
    _ = (x0⁻¹ * x0⁻¹) * ((x0⁻¹ * x0⁻¹) * w * (x0⁻¹ * x0⁻¹)⁻¹) * (x0⁻¹ * x0⁻¹)⁻¹ := by group
    _ = w := by rw [hcw, hcw]

end FratMain

end CFSG.Quasithin.Kleidman.F204
