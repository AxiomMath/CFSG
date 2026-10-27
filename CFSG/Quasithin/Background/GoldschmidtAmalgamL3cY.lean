module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cZ4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D]

theorem swap_prod {a b d κ κ' κ'' : D} (ha : a * a = 1) (hb : b * b = 1) (hd : d * d = 1)
    (hκ : a * b * a * b = κ) (hκ' : b * d * b * d = κ') (hκ'' : d * a * d * a = κ'')
    (hκa : κ * a = a * κ) (hκ'a : κ' * a = a * κ') (hκ''b : κ'' * b = b * κ'')
    (hprod : κ'' * κ * κ' = 1) : b * d * a * b = a * d := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have e1 : d * a = κ'' * (a * d) := by
    calc d * a = (d * a * d * a) * a⁻¹ * d⁻¹ := by group
      _ = κ'' * (a * d) := by rw [hκ'', hai, hdi, mul_assoc]
  have e2 : b * a = κ * (a * b) := by
    calc b * a = a⁻¹ * (a * b * a * b) * b⁻¹ := by group
      _ = a * κ * b := by rw [hκ, hai, hbi]
      _ = κ * (a * b) := by rw [← hκa]; group
  have e3 : b * d * b = κ' * d := by
    calc b * d * b = (b * d * b * d) * d⁻¹ := by group
      _ = κ' * d := by rw [hκ', hdi]
  calc b * d * a * b = b * (d * a) * b := by group
    _ = b * (κ'' * (a * d)) * b := by rw [e1]
    _ = (b * κ'') * (a * d) * b := by group
    _ = (κ'' * b) * (a * d) * b := by rw [← hκ''b]
    _ = κ'' * (b * a) * d * b := by group
    _ = κ'' * (κ * (a * b)) * d * b := by rw [e2]
    _ = κ'' * κ * a * (b * d * b) := by group
    _ = κ'' * κ * a * (κ' * d) := by rw [e3]
    _ = κ'' * κ * (a * κ') * d := by group
    _ = κ'' * κ * (κ' * a) * d := by rw [← hκ'a]
    _ = (κ'' * κ * κ') * (a * d) := by group
    _ = a * d := by rw [hprod, one_mul]

section Main

variable {A B : Subgroup D} {z : D} {V : Subgroup D}
variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.coset_mul_mem {Y : Subgroup D} (hVY : V ≤ Y) {p q v v' : D}
    (hq : q ∈ pCoreOf 2 A) (hpq : p * q ∈ Y) (hv : v ∈ V) (hv' : v' ∈ V) :
    (p * v) * (q * v') ∈ Y := by
  have e : p * v * (q * v') = (p * q) * (v * v') := by
    calc p * v * (q * v') = p * (v * q) * v' := by group
      _ = p * (q * v) * v' := by rw [g.V_comm_QA hv hq]
      _ = (p * q) * (v * v') := by group
  rw [e]
  exact Y.mul_mem hpq (hVY (V.mul_mem hv hv'))

theorem Gen3.pair_mem_Y (hU : Nat.card (conjClosure V B) = 8) {y : D} (hyA : y ∈ A)
    (hy3 : orderOf y = 3) {e₁ e₂ : D} (he₁ : e₁ = y * a₁ * y⁻¹) (he₂ : e₂ = y * e₁ * y⁻¹)
    (he₁Q : e₁ ∈ pCoreOf 2 A) (he₂Q : e₂ ∈ pCoreOf 2 A) {Y : Subgroup D} (hVY : V ≤ Y)
    (h01 : a₁ * e₁ ∈ Y) (h02 : a₁ * e₂ ∈ Y) (h10 : e₁ * a₁ ∈ Y) (h12 : e₁ * e₂ ∈ Y)
    (h20 : e₂ * a₁ ∈ Y) (h21 : e₂ * e₁ ∈ Y) {h₁ h₂ : D} (hh₁ : h₁ ∈ A) (hh₂ : h₂ ∈ A)
    (hne : conjSub h₁ (conjClosure V B) ≠ conjSub h₂ (conjClosure V B)) {w₁ w₂ : D}
    (hw₁ : w₁ ∈ conjSub h₁ (conjClosure V B)) (hw₁V : w₁ ∉ V)
    (hw₂ : w₂ ∈ conjSub h₂ (conjClosure V B)) (hw₂V : w₂ ∉ V) : w₁ * w₂ ∈ Y := by
  have ha₁Q : a₁ ∈ pCoreOf 2 A := g.hyp.conjClosure_le_pCoreOf_left g.a₁_mem_U
  have typ : ∀ {h : D}, h ∈ A → ∀ {w : D}, w ∈ conjSub h (conjClosure V B) → w ∉ V →
      (conjSub h (conjClosure V B) = conjClosure V B ∧ ∃ v ∈ V, w = a₁ * v) ∨
      (conjSub h (conjClosure V B) = conjSub y (conjClosure V B) ∧ ∃ v ∈ V, w = e₁ * v) ∨
      (conjSub h (conjClosure V B) = conjSub (y * y) (conjClosure V B) ∧
        ∃ v ∈ V, w = e₂ * v) := by
    intro h hh w hw hwV
    rcases g.conj_cases hyA hy3 hh with hc | hc | hc
    · left
      refine ⟨hc, ?_⟩
      rw [hc] at hw
      rcases g.mem_U_cases hU hw with hmem | ⟨v, hv, hveq⟩
      · exact absurd hmem hwV
      · exact ⟨v, hv, by rw [hveq]; exact g.V_comm_QA hv ha₁Q⟩
    · right; left
      refine ⟨hc, ?_⟩
      rw [hc] at hw
      obtain ⟨v, hv, hveq⟩ := g.conj_elem hU hyA hw hwV
      exact ⟨v, hv, by rw [hveq, he₁]⟩
    · right; right
      refine ⟨hc, ?_⟩
      rw [hc] at hw
      obtain ⟨v, hv, hveq⟩ := g.conj_elem hU (A.mul_mem hyA hyA) hw hwV
      refine ⟨v, hv, ?_⟩
      have : y * y * a₁ * (y * y)⁻¹ = e₂ := by rw [he₂, he₁]; group
      rw [hveq, this]
  rcases typ hh₁ hw₁ hw₁V with ⟨c1, v1, hv1, rfl⟩ | ⟨c1, v1, hv1, rfl⟩ | ⟨c1, v1, hv1, rfl⟩
  · rcases typ hh₂ hw₂ hw₂V with ⟨c2, v2, hv2, rfl⟩ | ⟨c2, v2, hv2, rfl⟩ | ⟨c2, v2, hv2, rfl⟩
    · exact absurd (c1.trans c2.symm) hne
    · exact g.coset_mul_mem hVY he₁Q h01 hv1 hv2
    · exact g.coset_mul_mem hVY he₂Q h02 hv1 hv2
  · rcases typ hh₂ hw₂ hw₂V with ⟨c2, v2, hv2, rfl⟩ | ⟨c2, v2, hv2, rfl⟩ | ⟨c2, v2, hv2, rfl⟩
    · exact g.coset_mul_mem hVY ha₁Q h10 hv1 hv2
    · exact absurd (c1.trans c2.symm) hne
    · exact g.coset_mul_mem hVY he₂Q h12 hv1 hv2
  · rcases typ hh₂ hw₂ hw₂V with ⟨c2, v2, hv2, rfl⟩ | ⟨c2, v2, hv2, rfl⟩ | ⟨c2, v2, hv2, rfl⟩
    · exact g.coset_mul_mem hVY ha₁Q h20 hv1 hv2
    · exact g.coset_mul_mem hVY he₁Q h21 hv1 hv2
    · exact absurd (c1.trans c2.symm) hne

end Main

section MainY

variable {A B : Subgroup D} {z : D} {V : Subgroup D}
variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.exists_Y (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 64)
    {y : D} (hyA : y ∈ A) (hy3 : orderOf y = 3) :
    ∃ Y : Subgroup D, Y ≤ pCoreOf 2 A ∧ V ≤ Y ∧ Nat.card ↥Y = 16 ∧
      A ≤ Subgroup.normalizer (Y : Set D) ∧
      Nonempty (↥Y ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  have hcube : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this
  obtain ⟨e₁, he₁⟩ : ∃ e₁, e₁ = y * a₁ * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = y * e₁ * y⁻¹ := ⟨_, rfl⟩
  have he₃ : y * e₂ * y⁻¹ = a₁ := by
    rw [he₂, he₁]
    calc y * (y * (y * a₁ * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * a₁ * (y * y * y)⁻¹ := by group
      _ = a₁ := by rw [hcube]; group
  have ha₁Q : a₁ ∈ pCoreOf 2 A := g.hyp.conjClosure_le_pCoreOf_left g.a₁_mem_U
  have he₁Q : e₁ ∈ pCoreOf 2 A := by rw [he₁]; exact conj_mem_pCoreOf_left hyA ha₁Q
  have he₂Q : e₂ ∈ pCoreOf 2 A := by rw [he₂]; exact conj_mem_pCoreOf_left hyA he₁Q
  have h11 : a₁ * a₁ = 1 := g.a₁_sq
  have h22 : e₁ * e₁ = 1 := by
    rw [he₁]
    calc y * a₁ * y⁻¹ * (y * a₁ * y⁻¹) = y * (a₁ * a₁) * y⁻¹ := by group
      _ = 1 := by rw [h11]; group
  have h33 : e₂ * e₂ = 1 := by
    rw [he₂]
    calc y * e₁ * y⁻¹ * (y * e₁ * y⁻¹) = y * (e₁ * e₁) * y⁻¹ := by group
      _ = 1 := by rw [h22]; group
  have hi1 : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right h11
  have hi2 : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right h22
  have hi3 : e₂⁻¹ = e₂ := inv_eq_of_mul_eq_one_right h33
  have ha₁V : a₁ ∉ V := g.a₁_not_mem_V
  have he₁V : e₁ ∉ V := by
    rw [he₁]; exact fun h => ha₁V ((g.conj_mem_V_iff hyA).mp h)
  have he₂V : e₂ ∉ V := by
    rw [he₂]; exact fun h => he₁V ((g.conj_mem_V_iff hyA).mp h)
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = a₁ * e₁ * a₁ * e₁ := ⟨_, rfl⟩
  obtain ⟨κ', hκ'⟩ : ∃ κ', κ' = e₁ * e₂ * e₁ * e₂ := ⟨_, rfl⟩
  obtain ⟨κ'', hκ''⟩ : ∃ κ'', κ'' = e₂ * a₁ * e₂ * a₁ := ⟨_, rfl⟩
  have hκV : κ ∈ V := by
    have := g.hyp.commutator_mem_V_of_pCoreOf_left hU g.a₁_mem_U he₁Q
    rw [hi1, hi2] at this
    rwa [hκ]
  have hκ'e : κ' = y * κ * y⁻¹ := by
    rw [hκ', hκ, he₂, he₁]; group
  have hκ''e : κ'' = y * κ' * y⁻¹ := by
    calc κ'' = e₂ * a₁ * e₂ * a₁ := hκ''
      _ = (y * e₁ * y⁻¹) * (y * e₂ * y⁻¹) * (y * e₁ * y⁻¹) * (y * e₂ * y⁻¹) := by
        rw [← he₂, he₃]
      _ = y * κ' * y⁻¹ := by rw [hκ']; group
  have hκ'V : κ' ∈ V := by rw [hκ'e]; exact g.conj_mem_V hyA hκV
  have hκ''V : κ'' ∈ V := by rw [hκ''e]; exact g.conj_mem_V hyA hκ'V
  have hκ1 : κ ≠ 1 := by
    intro hκ1
    have h1 : a₁ * e₁ * a₁ * e₁ = 1 := by rw [← hκ]; exact hκ1
    have h2 : (a₁ * e₁)⁻¹ = a₁ * e₁ :=
      inv_eq_of_mul_eq_one_right (by simpa [mul_assoc] using h1)
    have hcomm : a₁ * e₁ = e₁ * a₁ := by
      calc a₁ * e₁ = (a₁ * e₁)⁻¹ := h2.symm
        _ = e₁⁻¹ * a₁⁻¹ := mul_inv_rev _ _
        _ = e₁ * a₁ := by rw [hi1, hi2]
    have hcU : ∀ u ∈ conjClosure V B, u * e₁ = e₁ * u := by
      intro u hu
      rcases g.mem_U_cases hU hu with huV | ⟨v, hv, rfl⟩
      · exact g.V_comm_QA huV he₁Q
      · calc v * a₁ * e₁ = v * (a₁ * e₁) := by group
          _ = v * (e₁ * a₁) := by rw [hcomm]
          _ = (v * e₁) * a₁ := by group
          _ = (e₁ * v) * a₁ := by rw [g.V_comm_QA hv he₁Q]
          _ = e₁ * (v * a₁) := by group
    have he₁U := g.mem_U_of_comm_QA hU hT he₁Q hcU
    have he₁y : e₁ ∈ conjSub y (conjClosure V B) := by
      rw [mem_conjSub]
      have : y⁻¹ * e₁ * y = a₁ := by rw [he₁]; group
      rw [this]; exact g.a₁_mem_U
    exact he₁V (g.hyp.inf_conjSub_conjClosure_le hU hyA hy3 ⟨he₁U, he₁y⟩)
  have hκ'1 : κ' ≠ 1 := by
    intro h
    apply hκ1
    rw [hκ'e] at h
    calc κ = y⁻¹ * (y * κ * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  have hκne : κ' ≠ κ := by rw [hκ'e]; exact g.conj_ne_of_ne_one hyA hy3 hκV hκ1
  have hprod : κ'' * κ * κ' = 1 := by
    have h1 := g.orbit_prod hyA hy3 hκV
    rw [← hκ'e, ← hκ''e] at h1
    have hc3 : κ'' * (κ * κ') = (κ * κ') * κ'' :=
      g.U_comm (le_conjClosure V B hκ''V) (le_conjClosure V B (V.mul_mem hκV hκ'V))
    calc κ'' * κ * κ' = κ'' * (κ * κ') := by group
      _ = (κ * κ') * κ'' := hc3
      _ = 1 := h1
  have hκκ : κ * κ = 1 := g.V_sq hκV
  have hκ'κ' : κ' * κ' = 1 := g.V_sq hκ'V
  have hswap : e₁ * e₂ * a₁ * e₁ = a₁ * e₂ :=
    swap_prod h11 h22 h33 hκ.symm hκ'.symm hκ''.symm (g.V_comm_QA hκV ha₁Q)
      (g.V_comm_QA hκ'V ha₁Q) (g.V_comm_QA hκ''V he₁Q) hprod
  have hcc' : (a₁ * e₁) * (e₁ * e₂) = (e₁ * e₂) * (a₁ * e₁) := by
    calc (a₁ * e₁) * (e₁ * e₂) = a₁ * (e₁ * e₁) * e₂ := by group
      _ = a₁ * e₂ := by rw [h22, mul_one]
      _ = e₁ * e₂ * a₁ * e₁ := hswap.symm
      _ = (e₁ * e₂) * (a₁ * e₁) := by group
  have hc2 : (a₁ * e₁) * (a₁ * e₁) = κ := by rw [hκ]; group
  have hc'2 : (e₁ * e₂) * (e₁ * e₂) = κ' := by rw [hκ']; group
  obtain ⟨hcard, hiso⟩ := nonempty_mulEquiv_of_commuting_order_four hc2 hc'2 hκκ hκ'κ' hκ1 hκ'1
    hκne.symm hcc'
  have hcY : a₁ * e₁ ∈ Subgroup.zpowers (a₁ * e₁) ⊔ Subgroup.zpowers (e₁ * e₂) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hc'Y : e₁ * e₂ ∈ Subgroup.zpowers (a₁ * e₁) ⊔ Subgroup.zpowers (e₁ * e₂) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  set Y : Subgroup D := Subgroup.zpowers (a₁ * e₁) ⊔ Subgroup.zpowers (e₁ * e₂) with hYdef
  have hκY : κ ∈ Y := by rw [← hc2]; exact Y.mul_mem hcY hcY
  have hκ'Y : κ' ∈ Y := by rw [← hc'2]; exact Y.mul_mem hc'Y hc'Y
  have hVY : V ≤ Y :=
    (le_sup_zpowers_of_card_four g.hyp.natural.card_eq hκV hκ'V hκκ hκ1 hκ'1 hκne).trans
      (sup_le (Subgroup.zpowers_le.mpr hκY) (Subgroup.zpowers_le.mpr hκ'Y))
  have h01 : a₁ * e₁ ∈ Y := hcY
  have h12 : e₁ * e₂ ∈ Y := hc'Y
  have h02 : a₁ * e₂ ∈ Y := by
    have : a₁ * e₂ = (a₁ * e₁) * (e₁ * e₂) := by
      calc a₁ * e₂ = a₁ * (e₁ * e₁) * e₂ := by rw [h22, mul_one]
        _ = (a₁ * e₁) * (e₁ * e₂) := by group
    rw [this]; exact Y.mul_mem hcY hc'Y
  have h10 : e₁ * a₁ ∈ Y := by
    have : e₁ * a₁ = (a₁ * e₁)⁻¹ := by rw [mul_inv_rev, hi1, hi2]
    rw [this]; exact Y.inv_mem hcY
  have h21 : e₂ * e₁ ∈ Y := by
    have : e₂ * e₁ = (e₁ * e₂)⁻¹ := by rw [mul_inv_rev, hi2, hi3]
    rw [this]; exact Y.inv_mem hc'Y
  have h20 : e₂ * a₁ ∈ Y := by
    have : e₂ * a₁ = (a₁ * e₂)⁻¹ := by rw [mul_inv_rev, hi1, hi3]
    rw [this]; exact Y.inv_mem h02
  have hYQ : Y ≤ pCoreOf 2 A :=
    sup_le (Subgroup.zpowers_le.mpr ((pCoreOf 2 A).mul_mem ha₁Q he₁Q))
      (Subgroup.zpowers_le.mpr ((pCoreOf 2 A).mul_mem he₁Q he₂Q))
  have hnorm : A ≤ Subgroup.normalizer (Y : Set D) := by
    refine le_normalizer_of_conj_mem fun h hh w hw => ?_
    have hle : Y ≤ Y.comap (MulAut.conj h).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · show (MulAut.conj h) (a₁ * e₁) ∈ Y
        rw [MulAut.conj_apply]
        have e : h * (a₁ * e₁) * h⁻¹ = (h * a₁ * h⁻¹) * (h * e₁ * h⁻¹) := by group
        rw [e]
        have e' : h * e₁ * h⁻¹ = (h * y) * a₁ * (h * y)⁻¹ := by rw [he₁]; group
        refine g.pair_mem_Y hU hyA hy3 he₁ he₂ he₁Q he₂Q hVY h01 h02 h10 h12 h20 h21 hh
          (A.mul_mem hh hyA) ?_ (mul_mem_conjSub g.a₁_mem_U)
          (fun hv => ha₁V ((g.conj_mem_V_iff hh).mp hv)) ?_
          (fun hv => he₁V ((g.conj_mem_V_iff hh).mp hv))
        · intro heq
          rw [conjSub_mul] at heq
          exact g.conjSub_ne hyA hy3 ((conjSub_inj h).mp heq).symm
        · rw [e']; exact mul_mem_conjSub g.a₁_mem_U
      · show (MulAut.conj h) (e₁ * e₂) ∈ Y
        rw [MulAut.conj_apply]
        have e : h * (e₁ * e₂) * h⁻¹ = (h * e₁ * h⁻¹) * (h * e₂ * h⁻¹) := by group
        rw [e]
        have e' : h * e₁ * h⁻¹ = (h * y) * a₁ * (h * y)⁻¹ := by rw [he₁]; group
        have e'' : h * e₂ * h⁻¹ = ((h * y) * y) * a₁ * ((h * y) * y)⁻¹ := by
          rw [he₂, he₁]; group
        refine g.pair_mem_Y hU hyA hy3 he₁ he₂ he₁Q he₂Q hVY h01 h02 h10 h12 h20 h21
          (A.mul_mem hh hyA) (A.mul_mem (A.mul_mem hh hyA) hyA) ?_ ?_
          (fun hv => he₁V ((g.conj_mem_V_iff hh).mp hv)) ?_
          (fun hv => he₂V ((g.conj_mem_V_iff hh).mp hv))
        · intro heq
          rw [conjSub_mul (h * y)] at heq
          exact g.conjSub_ne hyA hy3 ((conjSub_inj (h * y)).mp heq).symm
        · rw [e']; exact mul_mem_conjSub g.a₁_mem_U
        · rw [e'']; exact mul_mem_conjSub g.a₁_mem_U
    exact hle hw
  exact ⟨Y, hYQ, hVY, hcard, hnorm, hiso⟩

end MainY

end GoldAmL3c

end F6

end CFSG.Quasithin
