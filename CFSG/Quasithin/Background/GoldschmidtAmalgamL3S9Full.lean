module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3S9Cls
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZI2Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SArc
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WTwoGood
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3S9Dim

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem hF_of_swapProp (hSw : SwapProp A B) :
    ∀ s₁ s₂ s₃ : CosetGeom (A ⊔ B) A B, vtype s₂ = true →
      (graph (A ⊔ B) A B).Adj s₁ s₂ → (graph (A ⊔ B) A B).Adj s₂ s₃ → s₁ ≠ s₃ →
        ¬ ballStab 1 s₁ ⊓ ballStab 1 s₂ ≤ ballStab 1 s₃ := by
  intro s₁ s₂ s₃ hs₂ h12 h23 h13 hle
  have hs₁ : vtype s₁ = false := vtype_eq_false_of_adj h12.symm hs₂
  obtain ⟨g, hgv, hgu, hgw⟩ := hSw h12 hs₁ h23 (Ne.symm h13)
  exact hgw (hle ⟨hgu, hgv⟩)

theorem exists_mul_of_mem_sup_of_commute {H K : Subgroup D} (hHK : ∀ k ∈ K, ∀ h ∈ H, k * h = h * k)
    {x : D} (hx : x ∈ H ⊔ K) : ∃ k ∈ K, ∃ h ∈ H, x = k * h := by
  let S : Subgroup D :=
    { carrier := {x | ∃ k ∈ K, ∃ h ∈ H, x = k * h}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, h₁, hh₁, rfl⟩ ⟨k₂, hk₂, h₂, hh₂, rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, h₁ * h₂, H.mul_mem hh₁ hh₂, ?_⟩
        have hc : h₁ * k₂ = k₂ * h₁ := (hHK k₂ hk₂ h₁ hh₁).symm
        calc k₁ * h₁ * (k₂ * h₂) = k₁ * (h₁ * k₂) * h₂ := by group
          _ = k₁ * (k₂ * h₁) * h₂ := by rw [hc]
          _ = k₁ * k₂ * (h₁ * h₂) := by group
      one_mem' := ⟨1, K.one_mem, 1, H.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, h, hh, rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, h⁻¹, H.inv_mem hh, ?_⟩
        have hc : k⁻¹ * h⁻¹ = h⁻¹ * k⁻¹ := hHK k⁻¹ (K.inv_mem hk) h⁻¹ (H.inv_mem hh)
        calc (k * h)⁻¹ = h⁻¹ * k⁻¹ := by group
          _ = k⁻¹ * h⁻¹ := hc.symm }
  have hKS : K ≤ S := fun k hk => ⟨k, hk, 1, H.one_mem, by simp⟩
  have hHS : H ≤ S := fun h hh => ⟨1, K.one_mem, h, hh, by simp⟩
  exact (sup_le hHS hKS) hx

namespace OddCritG

theorem walk4_end {m : ℕ}
    {p : ℕ → CosetGeom (A ⊔ B) A B} (c : OddCritG V m p) :
    Walk4 A B (p (m - 3)) (p (m - 2)) (p (m - 1)) (p m) (p (m + 1)) := by
  have hm := c.six_le
  obtain ⟨r, hr⟩ := c.even
  refine
    { type_one := c.vtype_odd (by omega) ⟨r - 2, by omega⟩
      adj01 := ?_
      adj12 := ?_
      adj23 := ?_
      adj34 := c.adj le_rfl
      ne02 := c.ne (by omega) (by omega)
      ne13 := c.ne (by omega) (by omega)
      ne24 := c.ne (by omega) le_rfl }
  · have := c.adj (i := m - 3) (by omega)
    rwa [show m - 3 + 1 = m - 2 by omega] at this
  · have := c.adj (i := m - 2) (by omega)
    rwa [show m - 2 + 1 = m - 1 by omega] at this
  · have := c.adj (i := m - 1) (by omega)
    rwa [show m - 1 + 1 = m by omega] at this

end OddCritG

namespace GoldHyp3

variable [Finite D] (h : GoldHyp3 A B z V)

include h

theorem inf_Vv_le_Vv_of_involution {b : ℕ} (hb : critDist (A ⊔ B) A B V = b) (hb5 : 5 ≤ b)
    (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hSw : SwapProp A B) {t a β a' t' : CosetGeom (A ⊔ B) A B} (hs : Walk4 A B t a β a' t')
    {x₀ : D} (hx₀a' : x₀ ∈ ballStab 1 a') (hx₀t : x₀ ∈ stab t) (hx₀t' : x₀ ∈ stab t')
    (hx₀n : x₀ ∉ ballStab 1 t') (hx₀sq : x₀ * x₀ = 1) :
    Vv V t ⊓ Vv V t' ≤ Vv V β := by
  have ha : vtype a = false := vtype_eq_false_of_adj hs.adj01 hs.type_one
  have hβ : vtype β = true := vtype_eq_true_of_adj hs.adj12 ha
  have ha' : vtype a' = false := vtype_eq_false_of_adj hs.adj23 hβ
  have ht' : vtype t' = true := vtype_eq_true_of_adj hs.adj34 ha'
  have hF := hF_of_swapProp hSw
  have hsr : Walk4 A B t' a' β a t :=
    { type_one := ht'
      adj01 := hs.adj34.symm
      adj12 := hs.adj23.symm
      adj23 := hs.adj12.symm
      adj34 := hs.adj01.symm
      ne02 := Ne.symm hs.ne24
      ne13 := Ne.symm hs.ne13
      ne24 := Ne.symm hs.ne02 }
  obtain ⟨g, hg0, hg1, hg2, hg3, hg4⟩ := Walk4.exists_smul h hF hs hsr
  have hX4 : Nat.card ↥(Vv V t ⊓ Vv V t') ≤ 4 :=
    h.card_inf_Vv_le_four hU hI1 (hF a β a' hβ hs.adj12 hs.adj23 hs.ne13) hβ hs.adj12.symm
      hs.adj23 hs.ne13 hs.adj01.symm hs.adj34 hs.ne02 (Ne.symm hs.ne24)
  have hXa' : Vv V t ⊓ Vv V t' ≤ Vv V a' ⊔ Theta z V a' t' :=
    h.inf_Vv_le_sup_Theta hU hβ hs.adj12.symm hs.adj23 hs.adj01.symm hs.adj34
      (Ne.symm hs.ne24) hX4 hx₀a' hx₀t hx₀t' hx₀n hx₀sq
  have hXa : Vv V t ⊓ Vv V t' ≤ Vv V a ⊔ Theta z V a t := by
    have hconj : conjSub (g : D) (Vv V t ⊓ Vv V t') = Vv V t ⊓ Vv V t' := by
      rw [conjSub_inf, ← Vv_smul h.natural.reduced.2.1, ← Vv_smul h.natural.reduced.2.1, hg0, hg4,
        inf_comm]
    have hconj2 : conjSub (g : D) (Vv V a' ⊔ Theta z V a' t') = Vv V a ⊔ Theta z V a t := by
      rw [conjSub_sup, ← Vv_smul h.natural.reduced.2.1, ← h.Theta_smul, hg3, hg4]
    intro x hx
    have hx' : x ∈ conjSub (g : D) (Vv V t ⊓ Vv V t') := by rw [hconj]; exact hx
    rw [mem_conjSub] at hx'
    have := hXa' hx'
    rw [← mem_conjSub, hconj2] at this
    exact this
  by_contra hnle
  obtain ⟨c, hcX, hcU⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hab : IsElemAbelian 2 (Vv V t) := h.isElemAbelian_Vv_B hs.type_one
  have hab' : IsElemAbelian 2 (Vv V t') := h.isElemAbelian_Vv_B ht'
  have hΘt : Theta z V a t ≤ Vv V t := h.Theta_le_Vv ha hs.adj01.symm
  have hVat : Vv V a ≤ Vv V t := Vv_le_Vv_of_adj hs.adj01.symm ha
  have hΘt' : Theta z V a' t' ≤ Vv V t' := h.Theta_le_Vv ha' hs.adj34
  have hVa't' : Vv V a' ≤ Vv V t' := Vv_le_Vv_of_adj hs.adj34 ha'
  obtain ⟨θ₁, hθ₁, v₁, hv₁, hc₁⟩ := exists_mul_of_mem_sup_of_commute (fun k hk w hw =>
    isElemAbelian_comm hab (hΘt hk) (hVat hw)) (hXa hcX)
  obtain ⟨θ₂, hθ₂, v₂, hv₂, hc₂⟩ := exists_mul_of_mem_sup_of_commute (fun k hk w hw =>
    isElemAbelian_comm hab' (hΘt' hk) (hVa't' hw)) (hXa' hcX)
  have hv₁β : v₁ ∈ Vv V β := Vv_le_Vv_of_adj hs.adj12 ha hv₁
  have hv₂β : v₂ ∈ Vv V β := Vv_le_Vv_of_adj hs.adj23.symm ha' hv₂
  have hθ₁U : θ₁ ∉ Vv V β := fun hm => hcU (by
    rw [hc₁]
    exact (Vv V β).mul_mem hm hv₁β)
  have hθθ : θ₁⁻¹ * θ₂ ∈ Vv V β := by
    have e : θ₁⁻¹ * θ₂ = v₁ * v₂⁻¹ := by
      have h1 : θ₁ = c * v₁⁻¹ := by rw [hc₁]; group
      have h2 : θ₂ = c * v₂⁻¹ := by rw [hc₂]; group
      rw [h1, h2]
      group
    rw [e]
    exact (Vv V β).mul_mem hv₁β ((Vv V β).inv_mem hv₂β)
  exact h.false_of_pair_class hb hb5 hU hI1 hSw hβ hs.adj12.symm hs.adj23 hs.ne13 hs.adj01.symm
    hs.adj34 (Ne.symm hs.ne02) hs.ne24 hθ₁ hθ₂ hθ₁U hθθ

theorem inf_Vv_le_Vv_end {m : ℕ} {p : ℕ → CosetGeom (A ⊔ B) A B} (c : OddCritG V m p)
    (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hSw : SwapProp A B) :
    Vv V (p (m - 3)) ⊓ Vv V (p (m + 1)) ≤ Vv V (p (m - 1)) := by
  have hm := c.six_le
  have hb := c.crit_eq
  have h0 : vtype (p 0) = false := c.vtype_zero
  obtain ⟨x₀, hx₀V, hx₀Q⟩ := IsConcreteLE.not_le_iff_exists.1 (c.crit' h)
  have hdm : CosetGeom.dist (p 0) (p m) + 1 ≤ m + 1 := by
    rw [c.dist_eq (Nat.zero_le _) (by omega)]
    omega
  have hx₀m : x₀ ∈ ballStab 1 (p m) := h.Vv_le_ballStab_one_of_dist hb h0 hdm hx₀V
  have hx₀t' : x₀ ∈ stab (p (m + 1)) :=
    h.Vv_le_stab_A hb h0 (by rw [c.dist_eq (Nat.zero_le _) le_rfl]; omega) hx₀V
  have hx₀t : x₀ ∈ stab (p (m - 3)) :=
    h.Vv_le_stab_A hb h0 (by rw [c.dist_eq (Nat.zero_le _) (by omega)]; omega) hx₀V
  have hVab : IsElemAbelian 2 V := h.natural.reduced.2.2.1
  have hx₀sq : x₀ * x₀ = 1 := by
    have := hVab.2 x₀ (by rw [← c.Vv_zero h]; exact hx₀V)
    rwa [pow_two] at this
  exact h.inf_Vv_le_Vv_of_involution hb (by omega) hU hI1 hSw c.walk4_end hx₀m hx₀t hx₀t' hx₀Q
    hx₀sq

theorem I2aProp_of_odd (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hSw : SwapProp A B) {b : ℕ} (hb : critDist (A ⊔ B) A B V = b) (hb7 : 7 ≤ b)
    (hodd : Odd b) : I2aProp A B V := by
  obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
  obtain ⟨p, hp0, hgeo, hnle⟩ := h.exists_crit_geodesic hb
  have hme : Even m := by
    obtain ⟨j, hj⟩ := hodd
    exact ⟨j, by omega⟩
  have c : OddCritG V m p := ⟨hb, by omega, hme, hp0, hgeo, hnle⟩
  have hend := h.inf_Vv_le_Vv_end c hU hI1 hSw
  have hF := hF_of_swapProp hSw
  intro β a a' t t' hβ hβa hβa' haa' hat ha't' htβ ht'β x hx
  have ha : vtype a = false := vtype_eq_false_of_adj hβa hβ
  have ha' : vtype a' = false := vtype_eq_false_of_adj hβa' hβ
  have hs : Walk4 A B t a β a' t' :=
    { type_one := vtype_eq_true_of_adj hat ha
      adj01 := hat.symm
      adj12 := hβa.symm
      adj23 := hβa'
      adj34 := ha't'
      ne02 := htβ
      ne13 := haa'
      ne24 := Ne.symm ht'β }
  obtain ⟨g, hg0, hg1, hg2, hg3, hg4⟩ := Walk4.exists_smul h hF c.walk4_end hs
  have hconj : conjSub (g : D) (Vv V (p (m - 3)) ⊓ Vv V (p (m + 1))) = Vv V t ⊓ Vv V t' := by
    rw [conjSub_inf, ← Vv_smul h.natural.reduced.2.1, ← Vv_smul h.natural.reduced.2.1, hg0, hg4]
  have hx' : x ∈ conjSub (g : D) (Vv V (p (m - 3)) ⊓ Vv V (p (m + 1))) := by
    rw [hconj]
    exact hx
  rw [mem_conjSub] at hx'
  have h1 := hend hx'
  have h2 : x ∈ conjSub (g : D) (Vv V (p (m - 1))) := by
    rw [mem_conjSub]
    exact h1
  rwa [← Vv_smul h.natural.reduced.2.1, hg2] at h2

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
