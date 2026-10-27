module

public import CFSG.RankThree.GF2n.Stroth80.Sec57Defs
public import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnOrbit
import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

theorem exists_statedSL_mulVec_eq {K : Type} [Field K] {m : ℕ} (hm : 2 ≤ m) {x y : Fin m → K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : GL (Fin m) K, g ∈ StatedSL m K ∧ (g : Matrix (Fin m) (Fin m) K) *ᵥ y = x := by
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.exists_SL_mulVec_eq hm hy hx
  refine ⟨SpecialLinearGroup.toGL g, ?_, hg⟩
  rw [statedSL_eq_range_toGL]
  exact MonoidHom.mem_range.mpr ⟨g, rfl⟩

section Step1

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem caseA_conj_eq_inv_mul (t y : G) : y * t * y⁻¹ = ⁅t, y⁆⁻¹ * t := by
  rw [commutatorElement_def]
  group

theorem caseA_conj_of_mem_H0 {r : G} (hr : r ∈ H0 M Z) {z : G} (hz : z ∈ Z) :
    r * z * r⁻¹ = z := by
  have h := Subgroup.mem_centralizer_iff.mp hr.2 z hz
  rw [← h]
  group

theorem caseA_conj_pair {t a₁ a₂ w₁ w₂ : G} {Z Q : Subgroup G}
    (hcen : ∀ x ∈ Q, ∀ z ∈ Z, x * z = z * x) (hZQ : ∀ z ∈ Z, z ∈ Q)
    (htc : ∀ z ∈ Z, t * z = z * t) (hw₁ : w₁ ∈ Q) (hw₂ : w₂ ∈ Q)
    (ha₁ : a₁ ∈ Z) (ha₂ : a₂ ∈ Z) (e₁ : w₁ * t * w₁⁻¹ = a₁⁻¹ * t)
    (e₂ : w₂ * t * w₂⁻¹ = a₂⁻¹ * t) :
    w₁⁻¹ * w₂ * t * (w₁⁻¹ * w₂)⁻¹ = t * (a₁ * a₂⁻¹) := by
  have hc1 : w₁⁻¹ * a₁⁻¹ = a₁⁻¹ * w₁⁻¹ := hcen w₁⁻¹ (Q.inv_mem hw₁) a₁⁻¹ (Z.inv_mem ha₁)
  have hc2 : w₁⁻¹ * a₂⁻¹ = a₂⁻¹ * w₁⁻¹ := hcen w₁⁻¹ (Q.inv_mem hw₁) a₂⁻¹ (Z.inv_mem ha₂)
  have X₁ : w₁⁻¹ * t * w₁ = a₁ * t := by
    have h1 : t = a₁⁻¹ * (w₁⁻¹ * t * w₁) := by
      calc t = w₁⁻¹ * (w₁ * t * w₁⁻¹) * w₁ := by group
        _ = w₁⁻¹ * (a₁⁻¹ * t) * w₁ := by rw [e₁]
        _ = a₁⁻¹ * (w₁⁻¹ * t * w₁) := by
          rw [← mul_assoc, hc1]
          group
    calc w₁⁻¹ * t * w₁ = a₁ * (a₁⁻¹ * (w₁⁻¹ * t * w₁)) := by group
      _ = a₁ * t := by rw [← h1]
  calc w₁⁻¹ * w₂ * t * (w₁⁻¹ * w₂)⁻¹ = w₁⁻¹ * (w₂ * t * w₂⁻¹) * w₁ := by group
    _ = w₁⁻¹ * (a₂⁻¹ * t) * w₁ := by rw [e₂]
    _ = a₂⁻¹ * (w₁⁻¹ * t * w₁) := by
      rw [← mul_assoc, hc2]
      group
    _ = a₂⁻¹ * (a₁ * t) := by rw [X₁]
    _ = (a₂⁻¹ * a₁) * t := by rw [mul_assoc]
    _ = t * (a₂⁻¹ * a₁) := (htc _ (Z.mul_mem (Z.inv_mem ha₂) ha₁)).symm
    _ = t * (a₁ * a₂⁻¹) := by rw [hcen a₁ (hZQ a₁ ha₁) a₂⁻¹ (Z.inv_mem ha₂)]

theorem caseA_comm_eq {t r y y₃ u a a₃ : G} {Z Q : Subgroup G}
    (hcen : ∀ x ∈ Q, ∀ z ∈ Z, x * z = z * x) (htc : ∀ z ∈ Z, t * z = z * t)
    (hrZ : ∀ z ∈ Z, r * z * r⁻¹ = z) (ha : a ∈ Z) (ha₃ : a₃ ∈ Z)
    (e_y : y * t * y⁻¹ = a⁻¹ * t) (e_y₃ : y₃ * t * y₃⁻¹ = a₃⁻¹ * t)
    (hy₃ : y = r * y₃ * r⁻¹) (hrt : r * t * r⁻¹ = t * u) :
    ⁅y, u⁆ = a * a₃⁻¹ := by
  have E1 : y * (r * t * r⁻¹) * y⁻¹ = (a⁻¹ * t) * (y * u * y⁻¹) := by
    rw [hrt, ← e_y]
    group
  have E2 : y * (r * t * r⁻¹) * y⁻¹ = a₃⁻¹ * (t * u) := by
    calc y * (r * t * r⁻¹) * y⁻¹ = r * (y₃ * t * y₃⁻¹) * r⁻¹ := by
          rw [hy₃]
          group
      _ = r * (a₃⁻¹ * t) * r⁻¹ := by rw [e_y₃]
      _ = (r * a₃⁻¹ * r⁻¹) * (r * t * r⁻¹) := by group
      _ = a₃⁻¹ * (t * u) := by rw [hrZ a₃⁻¹ (Z.inv_mem ha₃), hrt]
  have E : (a⁻¹ * t) * (y * u * y⁻¹) = a₃⁻¹ * (t * u) := E1.symm.trans E2
  have hcZ : a * a₃⁻¹ ∈ Z := Z.mul_mem ha (Z.inv_mem ha₃)
  have hX : y * u * y⁻¹ = a * a₃⁻¹ * u := by
    have h2 : t * (y * u * y⁻¹) = t * (a * a₃⁻¹ * u) := by
      calc t * (y * u * y⁻¹) = a * ((a⁻¹ * t) * (y * u * y⁻¹)) := by group
        _ = a * (a₃⁻¹ * (t * u)) := by rw [E]
        _ = (a * a₃⁻¹) * t * u := by group
        _ = t * (a * a₃⁻¹) * u := by rw [← htc _ hcZ]
        _ = t * (a * a₃⁻¹ * u) := by group
    exact mul_left_cancel h2
  rw [commutatorElement_def, hX]
  group

theorem caseA_conj (hc : Ctx M Q Z B) {n : ℕ} {t : G} (h : Sec5Hyp hc n t) (hA : CaseA Q Z t) :
    ∀ r ∈ Rt M (LB M Q B) t, ∃ y ∈ Q, ∃ w ∈ Z, r * t * r⁻¹ = y * t * y⁻¹ * w := by
  intro r hr
  obtain ⟨z₀, hz₀Z, hz₀⟩ := hA
  have ht : t ∈ LB M Q B := h.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hQt := hc.conj_mem_Q_of_mem_M htM
  have hZQ : ∀ z ∈ Z, z ∈ Q := fun z hz => hc.Z_le_Q hz
  have hcen : ∀ x ∈ Q, ∀ z ∈ Z, x * z = z * x :=
    fun x hx z hz => (hc.hyp.toHyp79.V_central hz hx).symm
  have htZ : ∀ z ∈ Z, t * z * t⁻¹ = z := fun z hz => hc.LB_centralizes_Z ht z hz
  have htc : ∀ z ∈ Z, t * z = z * t := fun z hz => by
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [htZ z hz]
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hrH : r ∈ H0 M Z := hc.Rt_le_H0 t hr
  have hrZ : ∀ z ∈ Z, r * z * r⁻¹ = z := fun z hz => caseA_conj_of_mem_H0 hrH hz
  have hrZ' : ∀ z ∈ Z, r⁻¹ * z * r = z := fun z hz => by
    have h1 := caseA_conj_of_mem_H0 ((H0 M Z).inv_mem hrH) hz
    simpa using h1
  have hd : ⁅r, t⁆ ∈ Q := hc.Rt_comm_mem_Q hr
  obtain ⟨u, hu_def⟩ : ∃ u : G, u = t⁻¹ * ⁅r, t⁆ * t := ⟨_, rfl⟩
  have huQ : u ∈ Q := by
    rw [hu_def]
    exact hQt.2 _ hd
  have hrt : r * t * r⁻¹ = t * u := by
    rw [hu_def, commutatorElement_def]
    group
  have hK3 : ∀ y ∈ Q, ⁅t, y⁆ ∈ Z → r⁻¹ * y * r ∈ Q ∧ ⁅t, r⁻¹ * y * r⁆ ∈ Z := by
    intro y hy hty
    have hy3Q : r⁻¹ * y * r ∈ Q := by
      have := (hc.conj_mem_Q_of_mem_M (M.inv_mem hrM)).1 y hy
      rwa [inv_inv] at this
    refine ⟨hy3Q, ?_⟩
    have hyt : ⁅y, t⁆ ∈ Z := by
      rw [← commutatorElement_inv]
      exact Z.inv_mem hty
    have hcomm := hc.comm_conj_mem_Z htM (M.inv_mem hrM) (by rw [inv_inv]; exact hd) hy
    simp only [inv_inv] at hcomm
    rw [hrZ' _ hyt] at hcomm
    have h3 : ⁅r⁻¹ * y * r, t⁆ ∈ Z := by
      have := Z.mul_mem hcomm hyt
      rwa [mul_assoc, inv_mul_cancel, mul_one] at this
    rw [← commutatorElement_inv]
    exact Z.inv_mem h3
  obtain ⟨m, γ, M₀, T, Rg, hTπ, hTB, -, -⟩ := hc.exists_model_LB ht
  have hγinv : ∀ b ∈ Z, γ b⁻¹ = -γ b := by
    intro b hb
    have h1 := Rg.add b hb b⁻¹ (Z.inv_mem hb)
    rw [mul_inv_cancel, Rg.one] at h1
    linear_combination -h1
  have hγinj : ∀ a ∈ Z, ∀ b ∈ Z, γ a = γ b → a = b := by
    intro a ha b hb hab
    have h1 : γ (a * b⁻¹) = 0 := by
      rw [Rg.add a ha b⁻¹ (Z.inv_mem hb), hγinv b hb, hab]
      ring
    exact mul_inv_eq_one.mp (Rg.inj (a * b⁻¹) (Z.mul_mem ha (Z.inv_mem hb)) h1)
  have hB0 : ∀ f : M₀.E, T f = f → M₀.B f (M₀.π u) = 0 := by
    intro f hf
    by_contra hne
    have hTe : T ((γ z₀ * (M₀.B f (M₀.π u))⁻¹) • f) = (γ z₀ * (M₀.B f (M₀.π u))⁻¹) • f := by
      rw [map_smul, hf]
    have hBe : M₀.B ((γ z₀ * (M₀.B f (M₀.π u))⁻¹) • f) (M₀.π u) = γ z₀ := by
      rw [LinearMap.BilinForm.smul_left, mul_assoc, inv_mul_cancel₀ hne, mul_one]
    obtain ⟨y₂, hy₂Q, hy₂⟩ := M₀.π_surj ((γ z₀ * (M₀.B f (M₀.π u))⁻¹) • f)
    have hy₂Z : ⁅t, y₂⁆ ∈ Z :=
      (comm_mem_iff_fix hQt.1 hTπ hy₂Q).mpr (by rw [hy₂]; exact hTe)
    have hγy : γ ⁅y₂, u⁆ = γ z₀ := by
      rw [M₀.comm_eq y₂ hy₂Q u huQ, hy₂, hBe]
    have hz : ⁅y₂, u⁆ = z₀ := hγinj _ (M₀.comm_mem y₂ hy₂Q u huQ) z₀ hz₀Z hγy
    obtain ⟨hy3Q, hy3Z⟩ := hK3 y₂ hy₂Q hy₂Z
    have hK := caseA_comm_eq (t := t) (r := r) (y := y₂) (y₃ := r⁻¹ * y₂ * r) (u := u)
      (a := ⁅t, y₂⁆) (a₃ := ⁅t, r⁻¹ * y₂ * r⁆) hcen htc hrZ hy₂Z hy3Z
      (caseA_conj_eq_inv_mul t y₂) (caseA_conj_eq_inv_mul t _) (by group) hrt
    have hpair := caseA_conj_pair (t := t) (a₁ := ⁅t, y₂⁆) (a₂ := ⁅t, r⁻¹ * y₂ * r⁆)
      (w₁ := y₂) (w₂ := r⁻¹ * y₂ * r) hcen hZQ htc hy₂Q hy3Q hy₂Z hy3Z
      (caseA_conj_eq_inv_mul t y₂) (caseA_conj_eq_inv_mul t _)
    apply hz₀ (y₂⁻¹ * (r⁻¹ * y₂ * r)) (Q.mul_mem (Q.inv_mem hy₂Q) hy3Q)
    rw [hpair, ← hK, hz]
  have hF1 : M₀.π u ∈ LinearMap.range ((T : M₀.E →ₗ[GaloisField 2 m] M₀.E) - 1) := by
    rw [Tim79.QuadModel.mem_range_sub_one_iff' hTB]
    intro f hf
    rw [Tim79.QuadModel.B_comm, hB0 f hf, neg_zero]
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hF1
  obtain ⟨y₀, hy₀Q, hxy⟩ := M₀.π_surj x
  rw [← hxy] at hx
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe] at hx
  have hc0Q : ⁅t, y₀⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (hQt.1 y₀ hy₀Q) (Q.inv_mem hy₀Q)
  have hπc0 : M₀.π ⁅t, y₀⁆ = M₀.π u := by
    rw [commutatorElement_def, M₀.π_mul _ (hQt.1 y₀ hy₀Q) _ (Q.inv_mem hy₀Q), M₀.pi_inv hy₀Q,
      hTπ y₀ hy₀Q, ← hx, sub_eq_add_neg]
  obtain ⟨z, hzZ, hz_def⟩ : ∃ z ∈ Z, u = ⁅t, y₀⁆ * z :=
    ⟨⁅t, y₀⁆⁻¹ * u, (M₀.pi_eq_iff hc0Q huQ).mp hπc0, by group⟩
  have hsQ : t * t ∈ Q := by
    have h1 := hc.sq_mem_Q_of_mem_LB ht
    rwa [pow_two] at h1
  obtain ⟨g, hg⟩ : ∃ g : G, g = y₀ * t * y₀⁻¹ := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : G, κ = (t * t)⁻¹ * (y₀ * (t * t) * y₀⁻¹) := ⟨_, rfl⟩
  have hκZ : κ ∈ Z := by
    have h1 := hc.hyp.toHyp79.comm_mem_V (Q.inv_mem hsQ) hy₀Q
    have e : κ = ⁅(t * t)⁻¹, y₀⁆ := by
      rw [hκ, commutatorElement_def, inv_inv]
      group
    rw [e]
    exact h1
  have hgZ : ∀ z ∈ Z, g * z = z * g := by
    intro z hz
    have h1 : y₀⁻¹ * z = z * y₀⁻¹ := hcen y₀⁻¹ (Q.inv_mem hy₀Q) z hz
    have h2 : y₀ * z = z * y₀ := hcen y₀ hy₀Q z hz
    calc g * z = y₀ * t * (y₀⁻¹ * z) := by
          rw [hg]
          group
      _ = y₀ * t * (z * y₀⁻¹) := by rw [h1]
      _ = y₀ * (z * t) * y₀⁻¹ := by
          rw [← htc z hz]
          group
      _ = (y₀ * z) * t * y₀⁻¹ := by group
      _ = (z * y₀) * t * y₀⁻¹ := by rw [h2]
      _ = z * g := by
          rw [hg]
          group
  have hI1 : g * g = (t * t) * κ := by
    rw [hκ, hg]
    group
  have hgκ : g * κ = κ * g := hgZ κ hκZ
  have hfin : r * t * r⁻¹ = g * (κ⁻¹ * z) := by
    have ht2 : t * t = g * g * κ⁻¹ := by
      rw [hI1]
      group
    have hgκ' : g * κ⁻¹ * g⁻¹ = κ⁻¹ := by
      have e : g * κ⁻¹ = κ⁻¹ * g := by
        calc g * κ⁻¹ = κ⁻¹ * (κ * g) * κ⁻¹ := by group
          _ = κ⁻¹ * (g * κ) * κ⁻¹ := by rw [← hgκ]
          _ = κ⁻¹ * g := by group
      rw [e]
      group
    calc r * t * r⁻¹ = t * (⁅t, y₀⁆ * z) := by rw [hrt, hz_def]
      _ = (t * t) * (g⁻¹ * z) := by
          rw [hg, commutatorElement_def]
          group
      _ = g * g * κ⁻¹ * (g⁻¹ * z) := by rw [ht2]
      _ = g * (g * κ⁻¹ * g⁻¹) * z := by group
      _ = g * κ⁻¹ * z := by rw [hgκ']
      _ = g * (κ⁻¹ * z) := by group
  exact ⟨y₀, hy₀Q, κ⁻¹ * z, Z.mul_mem (Z.inv_mem hκZ) hzZ, by rw [hfin, hg]⟩

end Step1

section Step2

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem caseA_inv_conj_of {t a z : G} {Z : Subgroup G} (haZ : ∀ x ∈ Z, a * x * a⁻¹ = x)
    (hz : z ∈ Z) (h : a * t * a⁻¹ = t * z) : a⁻¹ * t * a = t * z⁻¹ := by
  have hza : a * z = z * a := by
    calc a * z = (a * z * a⁻¹) * a := by group
      _ = z * a := by rw [haZ z hz]
  have h1 : a⁻¹ * z * a = z := by
    calc a⁻¹ * z * a = a⁻¹ * (z * a) := by group
      _ = a⁻¹ * (a * z) := by rw [hza]
      _ = z := by group
  have h2 : a⁻¹ * (t * z) * a = t := by
    rw [← h]
    group
  have h3 : (a⁻¹ * t * a) * z = t := by
    calc (a⁻¹ * t * a) * z = (a⁻¹ * t * a) * (a⁻¹ * z * a) := by rw [h1]
      _ = a⁻¹ * (t * z) * a := by group
      _ = t := h2
  calc a⁻¹ * t * a = (a⁻¹ * t * a) * z * z⁻¹ := by group
    _ = t * z⁻¹ := by rw [h3]

theorem caseA_comm_centralizes {t c₁ c₂ w₁ w₂ : G} {Z : Subgroup G}
    (hZ₁ : ∀ x ∈ Z, c₁ * x * c₁⁻¹ = x) (hZ₂ : ∀ x ∈ Z, c₂ * x * c₂⁻¹ = x)
    (hw₁ : w₁ ∈ Z) (hw₂ : w₂ ∈ Z) (hcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (e₁ : c₁ * t * c₁⁻¹ = t * w₁) (e₂ : c₂ * t * c₂⁻¹ = t * w₂) :
    ⁅c₁, c₂⁆ * t = t * ⁅c₁, c₂⁆ := by
  have hZ12 : ∀ x ∈ Z, (c₁ * c₂) * x * (c₁ * c₂)⁻¹ = x := fun x hx => by
    calc (c₁ * c₂) * x * (c₁ * c₂)⁻¹ = c₁ * (c₂ * x * c₂⁻¹) * c₁⁻¹ := by group
      _ = c₁ * x * c₁⁻¹ := by rw [hZ₂ x hx]
      _ = x := hZ₁ x hx
  have hZ21 : ∀ x ∈ Z, (c₂ * c₁) * x * (c₂ * c₁)⁻¹ = x := fun x hx => by
    calc (c₂ * c₁) * x * (c₂ * c₁)⁻¹ = c₂ * (c₁ * x * c₁⁻¹) * c₂⁻¹ := by group
      _ = c₂ * x * c₂⁻¹ := by rw [hZ₁ x hx]
      _ = x := hZ₂ x hx
  have hz : w₁ * w₂ ∈ Z := Z.mul_mem hw₁ hw₂
  have ha : (c₁ * c₂) * t * (c₁ * c₂)⁻¹ = t * (w₁ * w₂) := by
    calc (c₁ * c₂) * t * (c₁ * c₂)⁻¹ = c₁ * (c₂ * t * c₂⁻¹) * c₁⁻¹ := by group
      _ = c₁ * (t * w₂) * c₁⁻¹ := by rw [e₂]
      _ = (c₁ * t * c₁⁻¹) * (c₁ * w₂ * c₁⁻¹) := by group
      _ = (t * w₁) * w₂ := by rw [e₁, hZ₁ w₂ hw₂]
      _ = t * (w₁ * w₂) := by group
  have hb : (c₂ * c₁) * t * (c₂ * c₁)⁻¹ = t * (w₁ * w₂) := by
    calc (c₂ * c₁) * t * (c₂ * c₁)⁻¹ = c₂ * (c₁ * t * c₁⁻¹) * c₂⁻¹ := by group
      _ = c₂ * (t * w₁) * c₂⁻¹ := by rw [e₁]
      _ = (c₂ * t * c₂⁻¹) * (c₂ * w₁ * c₂⁻¹) := by group
      _ = (t * w₂) * w₁ := by rw [e₂, hZ₂ w₁ hw₁]
      _ = t * (w₁ * w₂) := by rw [mul_assoc, hcomm w₂ hw₂ w₁ hw₁]
  have ib := caseA_inv_conj_of hZ21 hz hb
  have hat : (c₁ * c₂) * t = t * (w₁ * w₂) * (c₁ * c₂) := by
    calc (c₁ * c₂) * t = ((c₁ * c₂) * t * (c₁ * c₂)⁻¹) * (c₁ * c₂) := by group
      _ = t * (w₁ * w₂) * (c₁ * c₂) := by rw [ha]
  have haz : (c₁ * c₂) * (w₁ * w₂) = (w₁ * w₂) * (c₁ * c₂) := by
    calc (c₁ * c₂) * (w₁ * w₂) = ((c₁ * c₂) * (w₁ * w₂) * (c₁ * c₂)⁻¹) * (c₁ * c₂) := by group
      _ = (w₁ * w₂) * (c₁ * c₂) := by rw [hZ12 _ hz]
  have key : (c₁ * c₂) * (t * (w₁ * w₂)⁻¹) = t * (c₁ * c₂) := by
    calc (c₁ * c₂) * (t * (w₁ * w₂)⁻¹) = ((c₁ * c₂) * t) * (w₁ * w₂)⁻¹ := by group
      _ = (t * (w₁ * w₂) * (c₁ * c₂)) * (w₁ * w₂)⁻¹ := by rw [hat]
      _ = t * ((c₁ * c₂) * (w₁ * w₂)) * (w₁ * w₂)⁻¹ := by
          rw [haz]
          group
      _ = t * (c₁ * c₂) := by group
  have hk : ⁅c₁, c₂⁆ = (c₁ * c₂) * (c₂ * c₁)⁻¹ := by
    rw [commutatorElement_def]
    group
  calc ⁅c₁, c₂⁆ * t = (c₁ * c₂) * (c₂ * c₁)⁻¹ * t := by rw [hk]
    _ = (c₁ * c₂) * ((c₂ * c₁)⁻¹ * t * (c₂ * c₁)) * (c₂ * c₁)⁻¹ := by group
    _ = (c₁ * c₂) * (t * (w₁ * w₂)⁻¹) * (c₂ * c₁)⁻¹ := by rw [ib]
    _ = (t * (c₁ * c₂)) * (c₂ * c₁)⁻¹ := by rw [key]
    _ = t * ⁅c₁, c₂⁆ := by
          rw [hk]
          group

theorem statedSL_le_of_commutator {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (hK : 4 ≤ Nat.card K) (H : Subgroup (GL (Fin m) K))
    (hcomm : ∀ g₁ ∈ StatedSL m K, ∀ g₂ ∈ StatedSL m K, ⁅g₁, g₂⁆ ∈ H) :
    StatedSL m K ≤ H := by
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin m) K) := by
    obtain ⟨s, hs⟩ := CFSG.LinearGroups.exists_finset_card_eq_four hK
    exact CFSG.LinearGroups.special_linear_isPerfect hm (Or.inr ⟨s, hs⟩)
  have hle : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin m) K)), ⊤⁆ ≤
      H.comap (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K) := by
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    rw [Subgroup.mem_comap, map_commutatorElement]
    apply hcomm
    · rw [statedSL_eq_range_toGL]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    · rw [statedSL_eq_range_toGL]
      exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  have htop : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin m) K)), ⊤⁆ = ⊤ :=
    Group.isPerfect_def.mp hperf
  rw [htop] at hle
  intro g hg
  rw [statedSL_eq_range_toGL] at hg
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
  exact Subgroup.mem_comap.mp (hle (Subgroup.mem_top x))

theorem caseA_conj_P (hc : Ctx M Q Z B) {t c b : G} (hcM : c ∈ M) (hct : c * t = t * c)
    (hb : b ∈ Q ⊓ QB (Subgroup.zpowers t)) : c * b * c⁻¹ ∈ Q ⊓ QB (Subgroup.zpowers t) := by
  have hzc : conjSubgroup c (Subgroup.zpowers t) = Subgroup.zpowers t := by
    show Subgroup.map (MulAut.conj c).toMonoidHom (Subgroup.zpowers t) = _
    rw [MonoidHom.map_zpowers]
    congr 1
    show c * t * c⁻¹ = t
    rw [hct]
    group
  have hQBc : conjSubgroup c (QB (Subgroup.zpowers t)) = QB (Subgroup.zpowers t) := by
    rw [← QB_conj, hzc]
  have hPc : conjSubgroup c (Q ⊓ QB (Subgroup.zpowers t)) = Q ⊓ QB (Subgroup.zpowers t) := by
    rw [conjSubgroup_inf, hc.conj_Q_eq hcM, hQBc]
  have h1 : c * b * c⁻¹ ∈ conjSubgroup c (Q ⊓ QB (Subgroup.zpowers t)) := by
    rw [mem_conjSubgroup, show c⁻¹ * (c * b * c⁻¹) * c = b by group]
    exact hb
  rwa [hPc] at h1

theorem caseA_cover (hc : Ctx M Q Z B) {n : ℕ} {t : G} (h : Sec5Hyp hc n t) (hA : CaseA Q Z t)
    {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 2 ≤ m) (hK : 4 ≤ Nat.card K)
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m) K) (hφr : φ.range = StatedSL m K)
    (hφk : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)) :
    ∀ g ∈ StatedSL m K, ∃ c : ↥(Rt M (LB M Q B) t), (c : G) * t = t * (c : G) ∧ φ c = g := by
  have hcen : ∀ x ∈ Q, ∀ z ∈ Z, x * z = z * x :=
    fun x hx z hz => (hc.hyp.toHyp79.V_central hz hx).symm
  have hZQ : ∀ z ∈ Z, z ∈ Q := fun z hz => hc.Z_le_Q hz
  have commZ : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy => hcen x (hZQ x hx) y hy
  have htc : ∀ z ∈ Z, t * z = z * t := fun z hz => by
    have := hc.LB_centralizes_Z h.mem z hz
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [this]
  have hQR : Q ≤ Rt M (LB M Q B) t := by
    have h1 := conjSubgroup_le_Rt (M := M) (L := LB M Q B) (t := t) (m := 1) M.one_mem
      (by rw [conjSubgroup_one]; exact h.mem)
    rw [conjSubgroup_one] at h1
    exact le_trans (le_sup_left : Q ≤ LB M Q B) h1
  have hQk : ∀ y ∈ Q, ∀ hy : y ∈ Rt M (LB M Q B) t, φ ⟨y, hy⟩ = 1 := by
    intro y hyQ hyR
    have hyCN : y ∈ hc.CN t :=
      ⟨hyR, fun v hv => hc.hyp.toHyp79.comm_mem_V hyQ (hc.Vt_le_Q t hv)⟩
    have hker : (⟨y, hyR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := by
      rw [hφk]
      exact Subgroup.mem_subgroupOf.mpr hyCN
    exact MonoidHom.mem_ker.mp hker
  have hcR : ∀ c : ↥(Rt M (LB M Q B) t), ∀ z ∈ Z, (c : G) * z * (c : G)⁻¹ = z :=
    fun c z hz => caseA_conj_of_mem_H0 (hc.Rt_le_H0 t c.2) hz
  have hred : ∀ r : ↥(Rt M (LB M Q B) t), ∃ c : ↥(Rt M (LB M Q B) t),
      (∃ w ∈ Z, (c : G) * t * (c : G)⁻¹ = t * w) ∧ φ c = φ r := by
    intro r
    obtain ⟨y, hyQ, w, hwZ, hr⟩ := caseA_conj hc h hA (r : G) r.2
    have hyR : y⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem (hQR hyQ)
    have hyw : y⁻¹ * w * y = w := by
      rw [hcen y⁻¹ (Q.inv_mem hyQ) w hwZ]
      group
    refine ⟨⟨y⁻¹, hyR⟩ * r, ⟨w, hwZ, ?_⟩, ?_⟩
    · show (y⁻¹ * (r : G)) * t * (y⁻¹ * (r : G))⁻¹ = t * w
      calc (y⁻¹ * (r : G)) * t * (y⁻¹ * (r : G))⁻¹ = y⁻¹ * ((r : G) * t * (r : G)⁻¹) * y := by
            group
        _ = y⁻¹ * (y * t * y⁻¹ * w) * y := by rw [hr]
        _ = t * (y⁻¹ * w * y) := by group
        _ = t * w := by rw [hyw]
    · rw [MonoidHom.map_mul, hQk y⁻¹ (Q.inv_mem hyQ) hyR, one_mul]
  have hcomm : ∀ g₁ ∈ StatedSL m K, ∀ g₂ ∈ StatedSL m K,
      ⁅g₁, g₂⁆ ∈ ((Subgroup.centralizer {t}).subgroupOf (Rt M (LB M Q B) t)).map φ := by
    intro g₁ hg₁ g₂ hg₂
    rw [← hφr] at hg₁ hg₂
    obtain ⟨r₁, rfl⟩ := MonoidHom.mem_range.mp hg₁
    obtain ⟨r₂, rfl⟩ := MonoidHom.mem_range.mp hg₂
    obtain ⟨c₁, ⟨w₁, hw₁Z, e₁⟩, hφ₁⟩ := hred r₁
    obtain ⟨c₂, ⟨w₂, hw₂Z, e₂⟩, hφ₂⟩ := hred r₂
    rw [← hφ₁, ← hφ₂]
    refine Subgroup.mem_map.mpr ⟨⁅c₁, c₂⁆, ?_, map_commutatorElement φ c₁ c₂⟩
    rw [Subgroup.mem_subgroupOf]
    have hk := caseA_comm_centralizes (t := t) (c₁ := (c₁ : G)) (c₂ := (c₂ : G))
      (hcR c₁) (hcR c₂) hw₁Z hw₂Z commZ e₁ e₂
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hk.symm
  have hcov := statedSL_le_of_commutator hm hK _ hcomm
  intro g hg
  obtain ⟨c, hcK, hcg⟩ := Subgroup.mem_map.mp (hcov hg)
  refine ⟨c, ?_, hcg⟩
  have hc' := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hcK) t
    (Set.mem_singleton t)
  exact hc'.symm

end Step2

section Step3

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth_5_7_caseA (hc : Ctx M Q Z B) {n : ℕ} {t : G} (h : Sec5Hyp hc n t)
    (hSL : SLNat hc t) (hBt : B ≤ QB (Subgroup.zpowers t)) (hA : CaseA Q Z t) :
    Vt M (LB M Q B) B Z t ≤ (Q ⊓ QB (Subgroup.zpowers t)) ⊔ Z := by
  obtain ⟨K, _, _, hK, m, hm, φ, hrange, hker, hRN, hZn, ψ, hψ⟩ := hSL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact hc.hyp.q4
  have hBZ : ∃ b ∈ B, b ∉ Z := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := hc.conj
    exact hc.ne (Subgroup.eq_of_le_of_card_ge (fun x hx => hcon x hx)
      (by rw [hg, card_conjSubgroup]))
  obtain ⟨b, hbB, hbZ⟩ := hBZ
  have hbV : b ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt h.mem hbB
  have hbP : b ∈ Q ⊓ QB (Subgroup.zpowers t) := ⟨hc.le hbB, hBt hbB⟩
  have hvec0 : ∀ x : ↥(Vt M (LB M Q B) B Z t),
      Multiplicative.toAdd (ψ (QuotientGroup.mk x)) = 0 ↔ (x : G) ∈ Z := by
    intro x
    rw [toAdd_eq_zero, ← map_one ψ, ψ.injective.eq_iff, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  have hyne : Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨b, hbV⟩)) ≠ 0 :=
    fun hh => hbZ ((hvec0 _).mp hh)
  intro v hv
  by_cases hvZ : v ∈ Z
  · exact Subgroup.mem_sup_right hvZ
  have hxne : Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨v, hv⟩)) ≠ 0 :=
    fun hh => hvZ ((hvec0 _).mp hh)
  obtain ⟨g, hgSL, hgy⟩ := exists_statedSL_mulVec_eq hm hxne hyne
  obtain ⟨c, hcomm, hcg⟩ := caseA_cover hc h hA hm hK4 φ hrange hker g hgSL
  have hwV : (c : G) * b * (c : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hRN c.2) b).mp hbV
  have hsec := hψ c ⟨b, hbV⟩ ⟨(c : G) * b * (c : G)⁻¹, hwV⟩ rfl
  rw [hcg, hgy] at hsec
  have hmk := ψ.injective (Multiplicative.toAdd.injective hsec)
  have hwv := (QuotientGroup.eq).mp hmk
  have hwP : (c : G) * b * (c : G)⁻¹ ∈ Q ⊓ QB (Subgroup.zpowers t) :=
    caseA_conj_P hc (hc.Rt_le_M t c.2) hcomm hbP
  have hz : ((c : G) * b * (c : G)⁻¹)⁻¹ * v ∈ Z := Subgroup.mem_subgroupOf.mp hwv
  have key : ((c : G) * b * (c : G)⁻¹) * (((c : G) * b * (c : G)⁻¹)⁻¹ * v) = v := by
    group
  have hmem := Subgroup.mul_mem _ (Subgroup.mem_sup_left hwP) (Subgroup.mem_sup_right hz)
  rwa [key] at hmem

end Step3

end CFSG.RankThree.GF2n.Stroth80
