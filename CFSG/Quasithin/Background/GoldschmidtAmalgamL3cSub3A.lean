module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutSub
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cY

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem perm3_conj_inv : ∀ a b : Equiv.Perm (Fin 3), a ≠ 1 → a * a = 1 → b ≠ 1 →
    b * b * b = 1 → a * b * a⁻¹ * b = 1 := by
  decide

theorem conj_inv_mem_of_vertex [Finite D] {H T : Subgroup D} (hv : Vertex H T) {w t : D}
    (hw : orderOf w = 3) (hwH : w ∈ H) (htT : t ∈ T) (htQ : t ∉ pCoreOf 2 H) :
    t * w * t⁻¹ * w ∈ pCoreOf 2 H := by
  obtain ⟨π, -, hπk⟩ := hv.exists_hom
  have htH : t ∈ H := hv.T_le htT
  have hw3 : w * w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw, pow_three'] at this
  have hsq : t * t ∈ pCoreOf 2 H := by
    have := GoldAmN.sq_mem_of_relIndex_two hv.pCoreOf_le
      (le_normalizer_of_relIndex_two' hv.pCoreOf_le hv.relIndex_pCoreOf_T)
      hv.relIndex_pCoreOf_T htT
    simpa [pow_two] using this
  have hwQ : w ∉ pCoreOf 2 H := fun h => hv.not_mem_of_orderOf hw (hv.pCoreOf_le h)
  have h1 : π ⟨t, htH⟩ ≠ 1 := fun h => htQ ((hπk ⟨t, htH⟩).mp h)
  have h2 : π ⟨t, htH⟩ * π ⟨t, htH⟩ = 1 := by
    rw [← map_mul]
    exact (hπk _).mpr hsq
  have h3 : π ⟨w, hwH⟩ ≠ 1 := fun h => hwQ ((hπk ⟨w, hwH⟩).mp h)
  have h4 : π ⟨w, hwH⟩ * π ⟨w, hwH⟩ * π ⟨w, hwH⟩ = 1 := by
    rw [← map_mul, ← map_mul]
    exact (hπk _).mpr (by simpa using hw3 ▸ (pCoreOf 2 H).one_mem)
  have key := perm3_conj_inv _ _ h1 h2 h3 h4
  have hmemH : t * w * t⁻¹ * w ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem htH hwH) (H.inv_mem htH)) hwH
  refine (hπk ⟨t * w * t⁻¹ * w, hmemH⟩).mp ?_
  have e : (⟨t * w * t⁻¹ * w, hmemH⟩ : ↥H) = ⟨t, htH⟩ * ⟨w, hwH⟩ * ⟨t, htH⟩⁻¹ * ⟨w, hwH⟩ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv]
  exact key

structure YDat (A : Subgroup D) (V : Subgroup D) (a₁ y e₁ e₂ : D) (Y : Subgroup D) : Prop where
  he₁ : e₁ = y * a₁ * y⁻¹
  he₂ : e₂ = y * e₁ * y⁻¹
  he₃ : y * e₂ * y⁻¹ = a₁
  e₁_mem : e₁ ∈ pCoreOf 2 A
  e₂_mem : e₂ ∈ pCoreOf 2 A
  e₁_sq : e₁ * e₁ = 1
  e₂_sq : e₂ * e₂ = 1
  e₁_not_mem : e₁ ∉ V
  e₂_not_mem : e₂ ∉ V
  κ₁_ne : a₁ * e₁ * a₁ * e₁ ≠ 1
  κ₃_ne : a₁ * e₂ * a₁ * e₂ ≠ 1
  κ_ne : a₁ * e₁ * a₁ * e₁ ≠ a₁ * e₂ * a₁ * e₂
  κ₂_ne : e₁ * e₂ * e₁ * e₂ ≠ 1
  Y_def : Y = Subgroup.zpowers (a₁ * e₁) ⊔ Subgroup.zpowers (e₁ * e₂)
  Y_le : Y ≤ pCoreOf 2 A
  V_le : V ≤ Y
  card : Nat.card ↥Y = 16
  norm : A ≤ Subgroup.normalizer (Y : Set D)
  comm : ∀ p ∈ Y, ∀ q ∈ Y, p * q = q * p
  c₁_mem : a₁ * e₁ ∈ Y
  c₂_mem : e₁ * e₂ ∈ Y
  noncomm : a₁ * e₁ ≠ e₁ * a₁
  c₁_sq : (a₁ * e₁) * (a₁ * e₁) ∈ V
  c₂_sq : (e₁ * e₂) * (e₁ * e₂) ∈ V

section YD

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.exists_yDat (hU : Nat.card (conjClosure V B) = 8) {y : D} (hyA : y ∈ A)
    (hy3 : orderOf y = 3)
    (hKU : ∀ q ∈ pCoreOf 2 A, q ∈ conjSub y (conjClosure V B) →
      (∀ u ∈ conjClosure V B, u * q = q * u) → q ∈ V) :
    ∃ e₁ e₂ Y, YDat A V a₁ y e₁ e₂ Y := by
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
    have he₁y : e₁ ∈ conjSub y (conjClosure V B) := by
      rw [mem_conjSub]
      have : y⁻¹ * e₁ * y = a₁ := by rw [he₁]; group
      rw [this]; exact g.a₁_mem_U
    exact he₁V (hKU e₁ he₁Q he₁y hcU)
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
  have hle : ∀ S : Subgroup D, a₁ ∈ S → y ∈ S → Y ≤ S := by
    intro S ha₁S hyS
    have he₁S : e₁ ∈ S := by
      rw [he₁]; exact S.mul_mem (S.mul_mem hyS ha₁S) (S.inv_mem hyS)
    have he₂S : e₂ ∈ S := by
      rw [he₂]; exact S.mul_mem (S.mul_mem hyS he₁S) (S.inv_mem hyS)
    exact sup_le (Subgroup.zpowers_le.mpr (S.mul_mem ha₁S he₁S))
      (Subgroup.zpowers_le.mpr (S.mul_mem he₁S he₂S))
  have hncomm : a₁ * e₁ ≠ e₁ * a₁ := by
    intro hc
    apply hκ1
    calc κ = a₁ * e₁ * (a₁ * e₁) := by rw [hκ]; group
      _ = a₁ * e₁ * (e₁ * a₁) := by rw [← hc]
      _ = a₁ * (e₁ * e₁) * a₁ := by group
      _ = 1 := by rw [h22, mul_one, h11]

  have hκ''ne : κ'' ≠ 1 := by
    intro h
    apply hκ'1
    rw [hκ''e] at h
    calc κ' = y⁻¹ * (y * κ' * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  have hκ3 : a₁ * e₂ * a₁ * e₂ = κ'' := by
    have h1 : a₁ * e₂ * a₁ * e₂ = (e₂ * a₁ * e₂ * a₁)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hi1, hi3]; group
    rw [h1, ← hκ'']
    exact inv_eq_of_mul_eq_one_right (g.V_sq hκ''V)
  have hκ''κ : κ'' ≠ κ := by
    intro h
    apply g.conj_ne_of_ne_one hyA hy3 hκV hκ1
    have e : y * κ'' * y⁻¹ = κ := by
      rw [hκ''e, hκ'e]
      calc y * (y * (y * κ * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * κ * (y * y * y)⁻¹ := by group
        _ = κ := by rw [hcube]; group
    rw [h] at e
    exact e
  have hcomm : ∀ p ∈ Y, ∀ q ∈ Y, p * q = q * p := by
    obtain ⟨e⟩ := hiso
    intro p hp q hq
    have := mul_comm (e ⟨p, hp⟩) (e ⟨q, hq⟩)
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (e.injective this)
  have hc₁sq : (a₁ * e₁) * (a₁ * e₁) ∈ V := by rw [hc2]; exact hκV
  have hc₂sq : (e₁ * e₂) * (e₁ * e₂) ∈ V := by rw [hc'2]; exact hκ'V
  refine ⟨e₁, e₂, Y, ⟨he₁, he₂, he₃, he₁Q, he₂Q, h22, h33, he₁V, he₂V, ?_, ?_, ?_, ?_, hYdef,
    hYQ, hVY, hcard, hnorm, hcomm, hcY, hc'Y, ?_, hc₁sq, hc₂sq⟩⟩
  · rw [← hκ]; exact hκ1
  · rw [hκ3]; exact hκ''ne
  · rw [hκ3, ← hκ]; exact fun h => hκ''κ h.symm
  · rw [← hκ']; exact hκ'1
  · exact hncomm

end YD

end GoldAmL3c

end F6

end CFSG.Quasithin
