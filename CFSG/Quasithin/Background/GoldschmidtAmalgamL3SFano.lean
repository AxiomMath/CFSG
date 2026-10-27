module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SNbr
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RInj

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

omit [Finite D] in
theorem mul_self_eq_one_of_mem_Zv {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) {c : D}
    (hc : c ∈ Zv z v) : c * c = 1 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [Zv_smul_γ₁ h.normalizes_zpowers, mem_conjSub] at hc
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hz : z * z = 1 := by rw [← pow_two]; exact h.natural.z_sq
  have h2 : (g : D)⁻¹ * c * g * ((g : D)⁻¹ * c * g) = 1 := by
    rw [← hm]
    rcases zpow_eq_one_or_self h.natural.z_sq m with e | e <;> rw [e]
    · simp
    · exact hz
  have e : c * c = (g : D) * ((g : D)⁻¹ * c * g * ((g : D)⁻¹ * c * g)) * (g : D)⁻¹ := by group
  rw [e, h2]
  group

theorem mem_sup_of_mem_Zv {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) {c : D}
    (hc : c ∈ Zv z v) : c ∈ A ⊔ B := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [Zv_smul_γ₁ h.normalizes_zpowers, mem_conjSub] at hc
  have hzT : z ∈ A ⊓ B :=
    (h.natural.le_pCoreOf.trans h.gold.pCoreOf_left_le) h.natural.z_mem_V
  have hzG : z ∈ A ⊔ B := (le_sup_left : A ≤ A ⊔ B) hzT.1
  have hc' : (g : D)⁻¹ * c * g ∈ A ⊔ B := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [← hm]
    exact (A ⊔ B).zpow_mem hzG m
  have e : c = g * ((g : D)⁻¹ * c * g) * (g : D)⁻¹ := by group
  rw [e]
  exact (A ⊔ B).mul_mem ((A ⊔ B).mul_mem g.2 hc') ((A ⊔ B).inv_mem g.2)

theorem eq_of_mem_Zv {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) {c c' : D}
    (hc : c ∈ Zv z v) (hc' : c' ∈ Zv z v) (h1 : c ≠ 1) (h1' : c' ≠ 1) : c = c' := by
  have hsq := h.mul_self_eq_one_of_mem_Zv hv hc
  have hord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) h1
  have hzp : Subgroup.zpowers c = Zv z v :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc) (by
      rw [Nat.card_zpowers, hord, h.card_Zv hv])
  have hc'z : c' ∈ Subgroup.zpowers c := hzp ▸ hc'
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hc'z
  have hc2 : c ^ 2 = 1 := by rw [pow_two]; exact hsq
  rcases zpow_eq_one_or_self hc2 m with e | e
  · exact absurd (hm ▸ e) h1'
  · exact (hm ▸ e).symm

omit [Finite D] in
theorem conj_eq_of_mem_stab_Zv {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) {g c : D}
    (hg : g ∈ stab v) (hc : c ∈ Zv z v) : g * c * g⁻¹ = c := by
  obtain ⟨k, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [stab_smul, stab_γ₁ (le_sup_right : B ≤ A ⊔ B), mem_conjSub] at hg
  rw [Zv_smul_γ₁ h.normalizes_zpowers, mem_conjSub] at hc
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hzc : ((k : D)⁻¹ * g * k) * z ^ m * ((k : D)⁻¹ * g * k)⁻¹ = z ^ m := by
    have := conj_zpow (a := (k : D)⁻¹ * g * k) (b := z) (i := m)
    rw [h.central _ hg] at this
    exact this.symm
  have e1 : g * c * g⁻¹ = k * (((k : D)⁻¹ * g * k) * ((k : D)⁻¹ * c * k) *
      ((k : D)⁻¹ * g * k)⁻¹) * (k : D)⁻¹ := by group
  rw [e1, ← hm, hzc, hm]
  group

theorem mul_mem_Zv_third {u v₁ v₂ v₃ : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (h1 : (graph (A ⊔ B) A B).Adj u v₁) (h2 : (graph (A ⊔ B) A B).Adj u v₂)
    (h3 : (graph (A ⊔ B) A B).Adj u v₃) (n12 : v₁ ≠ v₂) (n13 : v₁ ≠ v₃) (n23 : v₂ ≠ v₃)
    {c₁ c₂ : D} (hc₁ : c₁ ∈ Zv z v₁) (hc₂ : c₂ ∈ Zv z v₂) (e₁ : c₁ ≠ 1) (e₂ : c₂ ≠ 1) :
    c₁ * c₂ ∈ Zv z v₃ := by
  have ht1 : vtype v₁ = true := vtype_eq_true_of_adj h1 hu
  have ht2 : vtype v₂ = true := vtype_eq_true_of_adj h2 hu
  have hmem : c₁ * c₂ ∈ Vv V u :=
    (Vv V u).mul_mem (h.Zv_le_Vv h1 hu hc₁) (h.Zv_le_Vv h2 hu hc₂)
  have hne1 : c₁ * c₂ ≠ 1 := by
    intro e
    have hc₂' : c₂ = c₁ := mul_left_cancel (e.trans (h.mul_self_eq_one_of_mem_Zv ht1 hc₁).symm)
    exact n12 (h.eq_of_Zv_eq hu h1 h2 (h.Zv_eq_of_mem ht1 ht2 hc₁ (hc₂' ▸ hc₂) e₁))
  obtain ⟨v, hv, hcv⟩ := h.exists_adj_mem_Zv hu hmem hne1
  by_cases hv1 : v = v₁
  · exfalso
    have : c₂ ∈ Zv z v₁ := by
      have := (Zv z v₁).mul_mem ((Zv z v₁).inv_mem hc₁) (hv1 ▸ hcv)
      simpa using this
    exact n12 (h.eq_of_Zv_eq hu h1 h2 (h.Zv_eq_of_mem ht1 ht2 this hc₂ e₂))
  by_cases hv2 : v = v₂
  · exfalso
    have : c₁ ∈ Zv z v₂ := by
      have := (Zv z v₂).mul_mem (hv2 ▸ hcv) ((Zv z v₂).inv_mem hc₂)
      simpa using this
    exact n12 (h.eq_of_Zv_eq hu h1 h2 (h.Zv_eq_of_mem ht1 ht2 hc₁ this e₁))
  by_cases hv3 : v = v₃
  · rw [← hv3]
    exact hcv
  · exact (h.nbr_four h1 h2 h3 hv n12 n13 (Ne.symm hv1) n23 (Ne.symm hv2) (Ne.symm hv3)).elim

theorem not_mem_Vv_of_mem_Zv {β a a' y : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (h1 : (graph (A ⊔ B) A B).Adj β a) (h2 : (graph (A ⊔ B) A B).Adj β a') (n : a ≠ a')
    (hy : (graph (A ⊔ B) A B).Adj a y) (m : y ≠ β) {t : D} (ht : t ∈ Zv z y) (e : t ≠ 1) :
    t ∉ Vv V a' := by
  intro hta'
  have ha : vtype a = false := vtype_eq_false_of_adj h1 hβ
  have hyt : vtype y = true := vtype_eq_true_of_adj hy ha
  have hta : t ∈ Vv V a := h.Zv_le_Vv hy ha ht
  have hz : t ∈ Zv z β := h.mem_Zv_of_mem_Vv_of_mem_Vv hβ h1 h2 n hta hta'
  exact m (h.eq_of_Zv_eq ha hy h1.symm (h.Zv_eq_of_mem hyt hβ ht hz e))

theorem fano_prod (hU : Nat.card (conjClosure V B) = 8)
    {β a₁ a₂ a₃ y₁ y₂ y₃ : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (h1 : (graph (A ⊔ B) A B).Adj β a₁) (h2 : (graph (A ⊔ B) A B).Adj β a₂)
    (h3 : (graph (A ⊔ B) A B).Adj β a₃) (n12 : a₁ ≠ a₂) (n13 : a₁ ≠ a₃) (n23 : a₂ ≠ a₃)
    (hy₁ : (graph (A ⊔ B) A B).Adj a₁ y₁) (hy₂ : (graph (A ⊔ B) A B).Adj a₂ y₂)
    (hy₃ : (graph (A ⊔ B) A B).Adj a₃ y₃) (m₁ : y₁ ≠ β) (m₂ : y₂ ≠ β) (m₃ : y₃ ≠ β)
    {t₁ t₂ t₃ : D} (ht₁ : t₁ ∈ Zv z y₁) (ht₂ : t₂ ∈ Zv z y₂) (ht₃ : t₃ ∈ Zv z y₃)
    (e₁ : t₁ ≠ 1) (e₂ : t₂ ≠ 1) (e₃ : t₃ ≠ 1) : t₁ * t₂ * t₃ ∈ Zv z β := by
  have ha₁ : vtype a₁ = false := vtype_eq_false_of_adj h1 hβ
  have ha₂ : vtype a₂ = false := vtype_eq_false_of_adj h2 hβ
  have ha₃ : vtype a₃ = false := vtype_eq_false_of_adj h3 hβ
  have hyt₂ : vtype y₂ = true := vtype_eq_true_of_adj hy₂ ha₂
  have hyt₃ : vtype y₃ = true := vtype_eq_true_of_adj hy₃ ha₃
  have hV₁ : Vv V a₁ ≤ Vv V β := Vv_le_Vv_of_adj h1.symm ha₁
  have hV₂ : Vv V a₂ ≤ Vv V β := Vv_le_Vv_of_adj h2.symm ha₂
  have hV₃ : Vv V a₃ ≤ Vv V β := Vv_le_Vv_of_adj h3.symm ha₃
  have ht₁V : t₁ ∈ Vv V a₁ := h.Zv_le_Vv hy₁ ha₁ ht₁
  have ht₂V : t₂ ∈ Vv V a₂ := h.Zv_le_Vv hy₂ ha₂ ht₂
  have hn13 : t₁ ∉ Vv V a₃ := h.not_mem_Vv_of_mem_Zv hβ h1 h3 n13 hy₁ m₁ ht₁ e₁
  have hn23 : t₂ ∉ Vv V a₃ := h.not_mem_Vv_of_mem_Zv hβ h2 h3 n23 hy₂ m₂ ht₂ e₂
  have hn21 : t₂ ∉ Vv V a₁ := h.not_mem_Vv_of_mem_Zv hβ h2 h1 (Ne.symm n12) hy₂ m₂ ht₂ e₂
  have hW : (Vv V a₃).relIndex (Vv V β) = 2 := by
    have h8 := Subgroup.relIndex_mul_card (Vv V a₃) (Vv V β)
    rw [inf_of_le_left hV₃, h.card_Vv_A ha₃, h.card_Vv_B hU hβ] at h8
    omega
  have hprod : t₁ * t₂ ∈ Vv V a₃ := by
    have := mul_inv_mem_of_relIndex_eq_two hW (hV₁ ht₁V) ((Vv V β).inv_mem (hV₂ ht₂V)) hn13
      (fun hh => hn23 (by simpa using (Vv V a₃).inv_mem hh))
    simpa using this
  have hne1 : t₁ * t₂ ≠ 1 := by
    intro e
    have : t₂ = t₁⁻¹ := eq_inv_of_mul_eq_one_right e
    exact hn21 (this ▸ (Vv V a₁).inv_mem ht₁V)
  obtain ⟨v, hv, hcv⟩ := h.exists_adj_mem_Zv ha₃ hprod hne1
  by_cases hvβ : v = β
  · exfalso
    rw [hvβ] at hcv
    have : t₂ ∈ Vv V a₁ := by
      have h0 : t₁⁻¹ * (t₁ * t₂) ∈ Vv V a₁ := (Vv V a₁).mul_mem ((Vv V a₁).inv_mem ht₁V)
        (h.Zv_le_Vv h1.symm ha₁ hcv)
      simpa using h0
    exact hn21 this
  by_cases hv3 : v = y₃
  · rw [hv3] at hcv
    have : t₁ * t₂ = t₃ := h.eq_of_mem_Zv hyt₃ hcv ht₃ (by
      intro e
      exact hne1 e) e₃
    rw [this, h.mul_self_eq_one_of_mem_Zv hyt₃ ht₃]
    exact (Zv z β).one_mem
  · exact h.mul_mem_Zv_third ha₃ hv hy₃ h3.symm hv3 hvβ m₃ hcv ht₃ hne1 e₃

theorem conj_label_eq {a s y : CosetGeom (A ⊔ B) A B} (ha : vtype a = false)
    (has : (graph (A ⊔ B) A B).Adj a s) (hay : (graph (A ⊔ B) A B).Adj a y) (hys : y ≠ s)
    {σ : ↥(A ⊔ B)} (hσa : σ • a = a) (hσs : σ • s = s) (hσy : σ • y ≠ y) {t ζ : D}
    (ht : t ∈ Zv z y) (hζ : ζ ∈ Zv z s) (e : t ≠ 1) (eζ : ζ ≠ 1) :
    (σ : D) * t * (σ : D)⁻¹ = t * ζ := by
  have hst : vtype s = true := vtype_eq_true_of_adj has ha
  have hyt : vtype y = true := vtype_eq_true_of_adj hay ha
  have hσy' : (graph (A ⊔ B) A B).Adj a (σ • y) := by
    have := (smul_adj σ).mpr hay
    rwa [hσa] at this
  have hσyt : vtype (σ • y) = true := vtype_eq_true_of_adj hσy' ha
  have hmem : (σ : D) * t * (σ : D)⁻¹ ∈ Zv z (σ • y) := by
    rw [Zv_smul h.normalizes_zpowers]
    exact mul_mem_conjSub ht
  have hne : (σ : D) * t * (σ : D)⁻¹ ≠ 1 := by
    intro e1
    have : t = 1 := by
      have e2 : t = (σ : D)⁻¹ * ((σ : D) * t * (σ : D)⁻¹) * σ := by group
      rw [e2, e1]
      group
    exact e this
  have hσys : σ • y ≠ s := fun e1 => hys (by
    have := smul_left_cancel σ (e1.trans hσs.symm)
    exact this)
  have hprod : t * ((σ : D) * t * (σ : D)⁻¹) ∈ Zv z s :=
    h.mul_mem_Zv_third ha hay hσy' has (Ne.symm hσy) hys hσys ht hmem e hne
  have hprod1 : t * ((σ : D) * t * (σ : D)⁻¹) ≠ 1 := by
    intro e1
    have h1 : (σ : D) * t * (σ : D)⁻¹ = t := by
      have := h.mul_self_eq_one_of_mem_Zv hyt ht
      exact mul_left_cancel (e1.trans this.symm)
    have hzz : Zv z y = Zv z (σ • y) := h.Zv_eq_of_mem hyt hσyt ht (h1 ▸ hmem) e
    exact hσy (h.eq_of_Zv_eq ha hay hσy' hzz).symm
  have hζeq : t * ((σ : D) * t * (σ : D)⁻¹) = ζ := h.eq_of_mem_Zv hst hprod hζ hprod1 eζ
  have hsq := h.mul_self_eq_one_of_mem_Zv hyt ht
  calc (σ : D) * t * (σ : D)⁻¹ = t⁻¹ * (t * ((σ : D) * t * (σ : D)⁻¹)) := by group
    _ = t⁻¹ * ζ := by rw [hζeq]
    _ = t * ζ := by rw [inv_eq_of_mul_eq_one_right hsq]

omit [Finite D] h in
theorem exists_moved_nbr {s a : CosetGeom (A ⊔ B) A B} (hsa : (graph (A ⊔ B) A B).Adj s a)
    {σ : D} (hσ : σ ∈ ballStab 1 s) (hσa : σ ∉ ballStab 1 a) :
    ∃ y, (graph (A ⊔ B) A B).Adj a y ∧ y ≠ s ∧ σ ∉ stab y := by
  have hσs : σ ∈ stab s := ballStab_le_stab 1 s hσ
  have hσa' : σ ∈ stab a := mem_ballStab.mp hσ a (by
    rw [dist_le_one_iff rfl]; right; exact hsa)
  rw [mem_ballStab] at hσa
  push Not at hσa
  obtain ⟨δ, hδ, hσδ⟩ := hσa
  rw [dist_le_one_iff rfl] at hδ
  rcases hδ with rfl | hδ
  · exact absurd hσa' hσδ
  · refine ⟨δ, hδ, ?_, hσδ⟩
    rintro rfl
    exact hσδ hσs

theorem card_ballStab_inf_edge {u v : CosetGeom (A ⊔ B) A B}
    (huv : (graph (A ⊔ B) A B).Adj u v) (hu : vtype u = false) :
    Nat.card ↥(ballStab 1 u ⊓ ballStab 1 v) = Nat.card ↥(pCoreOf 2 A ⊓ pCoreOf 2 B) := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv hu
  rw [ballStab_smul, ballStab_smul, ballStab_one_γ₀_eq_pCoreOf h.gold,
    ballStab_one_γ₁_eq_pCoreOf h.gold, ← conjSub_inf]
  exact card_conjSub _ _

theorem not_ballStab_inf_le (hU : Nat.card (conjClosure V B) = 8) {s₁ s₂ s₃ : CosetGeom (A ⊔ B) A B}
    (hs₂ : vtype s₂ = true) (h12 : (graph (A ⊔ B) A B).Adj s₁ s₂)
    (h23 : (graph (A ⊔ B) A B).Adj s₂ s₃) (n13 : s₁ ≠ s₃) :
    ¬ ballStab 1 s₁ ⊓ ballStab 1 s₂ ≤ ballStab 1 s₃ := by
  intro hle
  have hs₁ : vtype s₁ = false := vtype_eq_false_of_adj h12.symm hs₂
  have hs₃ : vtype s₃ = false := vtype_eq_false_of_adj h23 hs₂
  obtain ⟨x, hx, hxs₁, hxs₃⟩ := h.exists_third (w := s₂) n13
  have hxt : vtype x = false := vtype_eq_false_of_adj hx hs₂
  have hR : ballStab 1 s₁ ⊓ ballStab 1 s₂ = ballStab 1 s₃ ⊓ ballStab 1 s₂ := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact le_inf hle inf_le_right
    · exact ((h.card_ballStab_inf_edge h23.symm hs₃).trans
        (h.card_ballStab_inf_edge h12 hs₁).symm).le
  have hp₁ : ¬ ballStab 1 s₂ ≤ ballStab 1 s₁ := h.not_ballStab_le_of_right h12 hs₁
  have hpx : ¬ ballStab 1 s₂ ≤ ballStab 1 x := h.not_ballStab_le_of_right hx.symm hxt
  obtain ⟨σ, hσQ, hσ1, hσx⟩ : ∃ σ ∈ ballStab 1 s₂, σ ∉ ballStab 1 s₁ ∧ σ ∉ ballStab 1 x := by
    obtain ⟨a, haQ, ha1⟩ := IsConcreteLE.not_le_iff_exists.mp hp₁
    obtain ⟨b, hbQ, hbx⟩ := IsConcreteLE.not_le_iff_exists.mp hpx
    by_cases hax : a ∈ ballStab 1 x
    · by_cases hb1 : b ∈ ballStab 1 s₁
      · refine ⟨a * b, (ballStab 1 s₂).mul_mem haQ hbQ, ?_, ?_⟩
        · intro hab
          apply ha1
          have := (ballStab 1 s₁).mul_mem hab ((ballStab 1 s₁).inv_mem hb1)
          simpa using this
        · intro hab
          apply hbx
          have := (ballStab 1 x).mul_mem ((ballStab 1 x).inv_mem hax) hab
          simpa using this
      · exact ⟨b, hbQ, hb1, hbx⟩
    · exact ⟨a, haQ, ha1, hax⟩
  have hσ3 : σ ∉ ballStab 1 s₃ := fun hh => hσ1 (by
    have : σ ∈ ballStab 1 s₃ ⊓ ballStab 1 s₂ := ⟨hh, hσQ⟩
    rw [← hR] at this
    exact this.1)
  have hσG : σ ∈ A ⊔ B := stab_le s₂ (ballStab_le_stab 1 s₂ hσQ)
  let g : ↥(A ⊔ B) := ⟨σ, hσG⟩
  have hfix : ∀ w, (graph (A ⊔ B) A B).Adj s₂ w → g • w = w := fun w hw =>
    smul_eq_of_mem_stab (mem_ballStab.mp hσQ w (by rw [dist_le_one_iff rfl]; right; exact hw))
  have hg2 : g • s₂ = s₂ := smul_eq_of_mem_stab (ballStab_le_stab 1 s₂ hσQ)
  obtain ⟨y₁, hy₁, hy₁s, hσy₁⟩ := exists_moved_nbr h12.symm hσQ hσ1
  obtain ⟨y₂, hy₂, hy₂s, hσy₂⟩ := exists_moved_nbr h23 hσQ hσ3
  obtain ⟨y₃, hy₃, hy₃s, hσy₃⟩ := exists_moved_nbr hx hσQ hσx
  have hyt₁ : vtype y₁ = true := vtype_eq_true_of_adj hy₁ hs₁
  have hyt₂ : vtype y₂ = true := vtype_eq_true_of_adj hy₂ hs₃
  have hyt₃ : vtype y₃ = true := vtype_eq_true_of_adj hy₃ hxt
  obtain ⟨t₁, ht₁, e₁⟩ := h.exists_ne_one_mem_Zv hyt₁
  obtain ⟨t₂, ht₂, e₂⟩ := h.exists_ne_one_mem_Zv hyt₂
  obtain ⟨t₃, ht₃, e₃⟩ := h.exists_ne_one_mem_Zv hyt₃
  obtain ⟨ζ, hζ, eζ⟩ := h.exists_ne_one_mem_Zv hs₂
  have hc₁ := h.conj_label_eq hs₁ h12 hy₁ hy₁s (hfix s₁ h12.symm) hg2
    (fun e => hσy₁ (mem_stab_of_smul_eq e)) ht₁ hζ e₁ eζ
  have hc₂ := h.conj_label_eq hs₃ h23.symm hy₂ hy₂s (hfix s₃ h23) hg2
    (fun e => hσy₂ (mem_stab_of_smul_eq e)) ht₂ hζ e₂ eζ
  have hc₃ := h.conj_label_eq hxt hx.symm hy₃ hy₃s (hfix x hx) hg2
    (fun e => hσy₃ (mem_stab_of_smul_eq e)) ht₃ hζ e₃ eζ
  have hcomm : ∀ {a y : CosetGeom (A ⊔ B) A B} {t : D}, vtype a = false →
      (graph (A ⊔ B) A B).Adj a s₂ → (graph (A ⊔ B) A B).Adj a y → t ∈ Zv z y →
      ζ * t = t * ζ := by
    intro a y t hat has hay ht
    have hyt : vtype y = true := vtype_eq_true_of_adj hay hat
    have hd : CosetGeom.dist a y ≤ critDist (A ⊔ B) A B V := by
      have := h.three_le_critDist
      rw [(dist_eq_one_iff_adj.mpr hay : CosetGeom.dist a y = 1)]
      omega
    have hζy : ζ ∈ stab y :=
      h.Vv_le_stab_A rfl hat hd (h.Zv_le_Vv has hat hζ)
    exact mul_inv_eq_iff_eq_mul.mp (h.conj_eq_of_mem_stab_Zv hyt hζy ht)
  have hcm₁ := hcomm hs₁ h12 hy₁ ht₁
  have hcm₂ := hcomm hs₃ h23.symm hy₂ ht₂
  have hcm₃ := hcomm hxt hx.symm hy₃ ht₃
  have hfano : t₁ * t₂ * t₃ ∈ Zv z s₂ :=
    h.fano_prod hU hs₂ h12.symm h23 hx n13 (Ne.symm hxs₁) (Ne.symm hxs₃) hy₁ hy₂ hy₃ hy₁s hy₂s
      hy₃s ht₁ ht₂ ht₃ e₁ e₂ e₃
  have hfixp : (σ : D) * (t₁ * t₂ * t₃) * (σ : D)⁻¹ = t₁ * t₂ * t₃ :=
    h.conj_eq_of_mem_stab_Zv hs₂ (ballStab_le_stab 1 s₂ hσQ) hfano
  have hζζ : ζ * ζ = 1 := h.mul_self_eq_one_of_mem_Zv hs₂ hζ
  have hcalc : (σ : D) * (t₁ * t₂ * t₃) * (σ : D)⁻¹ = t₁ * t₂ * t₃ * ζ := by
    calc (σ : D) * (t₁ * t₂ * t₃) * (σ : D)⁻¹
        = ((σ : D) * t₁ * (σ : D)⁻¹) * ((σ : D) * t₂ * (σ : D)⁻¹) *
          ((σ : D) * t₃ * (σ : D)⁻¹) := by group
      _ = (t₁ * ζ) * (t₂ * ζ) * (t₃ * ζ) := by rw [hc₁, hc₂, hc₃]
      _ = t₁ * (ζ * t₂) * ζ * t₃ * ζ := by group
      _ = t₁ * (t₂ * ζ) * ζ * t₃ * ζ := by rw [hcm₂]
      _ = t₁ * t₂ * (ζ * ζ) * t₃ * ζ := by group
      _ = t₁ * t₂ * t₃ * ζ := by rw [hζζ]; group
  have : t₁ * t₂ * t₃ * ζ = t₁ * t₂ * t₃ * 1 := by rw [← hcalc, hfixp, mul_one]
  exact eζ (mul_left_cancel this)

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
