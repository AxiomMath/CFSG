module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.Quasithin.H13.Ch8312

variable {Γ : Type*} [Group Γ]

abbrev dl (g u : Γ) : Γ := g * u * g⁻¹ * u⁻¹

theorem dl_mul (g h u : Γ) : dl (g * h) u = g * dl h u * g⁻¹ * dl g u := by
  simp only [dl]
  group

theorem dl_inv (g u : Γ) : dl g⁻¹ u = g⁻¹ * (dl g u)⁻¹ * g := by
  simp only [dl]
  group

theorem dl_conj (k g u : Γ) : dl (k * g * k⁻¹) (k * u * k⁻¹) = k * dl g u * k⁻¹ := by
  simp only [dl]
  group

theorem dl_mul_right (g u v : Γ) : dl g (u * v) = dl g u * (u * dl g v * u⁻¹) := by
  simp only [dl]
  group

theorem comm_of_mem_center {z : Γ} (hz : z ∈ Subgroup.center Γ) (g : Γ) : g * z = z * g :=
  Subgroup.mem_center_iff.mp hz g

theorem conj_eq_of_mem_center {z : Γ} (hz : z ∈ Subgroup.center Γ) (g : Γ) : g * z * g⁻¹ = z := by
  rw [comm_of_mem_center hz g, mul_inv_cancel_right]

theorem dl_mem_of_mem_sup {Q K₁ K₂ : Subgroup Γ} (hQ : Q.Normal)
    (h12 : ∀ k₁ ∈ K₁, ∀ k₂ ∈ K₂, dl k₁ k₂ ∈ Q) :
    ∀ x ∈ K₁ ⊔ Q, ∀ y ∈ K₂ ⊔ Q, dl x y ∈ Q := by
  let S₁ : Subgroup Γ :=
    { carrier := {x | ∀ y ∈ K₂, dl x y ∈ Q}
      mul_mem' := fun {x x'} hx hx' y hy => by
        rw [dl_mul]
        exact Q.mul_mem (hQ.conj_mem _ (hx' y hy) x) (hx y hy)
      one_mem' := fun y _ => by simp [dl]
      inv_mem' := fun {x} hx y hy => by
        rw [dl_inv]
        have := hQ.conj_mem _ (Q.inv_mem (hx y hy)) x⁻¹
        simpa using this }
  have h1 : K₁ ⊔ Q ≤ S₁ := sup_le (fun x hx y hy => h12 x hx y hy) fun q hq y _ => by
    simp only [dl]
    have := hQ.conj_mem _ (Q.inv_mem hq) y
    simpa [mul_assoc] using Q.mul_mem hq this
  intro x hx
  let S₂ : Subgroup Γ :=
    { carrier := {y | dl x y ∈ Q}
      mul_mem' := fun {y y'} hy hy' => by
        show dl x (y * y') ∈ Q
        rw [dl_mul_right]
        exact Q.mul_mem hy (hQ.conj_mem _ hy' y)
      one_mem' := by simp [dl]
      inv_mem' := fun {y} hy => by
        show dl x y⁻¹ ∈ Q
        have h := dl_mul_right x y y⁻¹
        rw [mul_inv_cancel] at h
        have h0 : dl x (1 : Γ) = 1 := by simp [dl]
        rw [h0] at h
        have e : y * dl x y⁻¹ * y⁻¹ = (dl x y)⁻¹ := by
          rw [← mul_left_cancel_iff (a := dl x y), mul_inv_cancel, ← h]
        have h2 : y * dl x y⁻¹ * y⁻¹ ∈ Q := by rw [e]; exact Q.inv_mem hy
        have h3 := hQ.conj_mem _ h2 y⁻¹
        simpa [mul_assoc] using h3 }
  have h2 : K₂ ⊔ Q ≤ S₂ := sup_le (fun y hy => h1 hx y hy) fun q hq => by
    show x * q * x⁻¹ * q⁻¹ ∈ Q
    exact Q.mul_mem (hQ.conj_mem _ hq x) (Q.inv_mem hq)
  exact fun y hy => h2 hy

theorem comm_comm_mem_of_quadratic {U Q K₁ K₂ A B Z : Subgroup Γ}
    (hZc : Z ≤ Subgroup.center Γ) (hZU : Z ≤ U) (hU : U.Normal) (hQ : Q.Normal)
    (hQU : ∀ q ∈ Q, ∀ u ∈ U, dl q u ∈ Z) (h12 : ∀ k₁ ∈ K₁, ∀ k₂ ∈ K₂, dl k₁ k₂ ∈ Q)
    (hA : A ≤ K₁ ⊔ Q) (hB : B ≤ K₂ ⊔ Q)
    (hAB : ∀ u ∈ U, ∀ a ∈ A, ∀ b ∈ B, dl b (dl a u) ∈ Z)
    (hS₁ : ∀ S : Subgroup Γ, Q ≤ S → S ≤ K₁ ⊔ Q → K₁ ≤ Subgroup.normalizer (S : Set Γ) →
      S = Q ∨ S = K₁ ⊔ Q)
    (hS₂ : ∀ S : Subgroup Γ, Q ≤ S → S ≤ K₂ ⊔ Q → K₂ ≤ Subgroup.normalizer (S : Set Γ) →
      S = Q ∨ S = K₂ ⊔ Q)
    (hAQ : ¬ A ≤ Q) (hBQ : ¬ B ≤ Q) :
    ∀ u ∈ U, ∀ g₁ ∈ K₁ ⊔ Q, ∀ g₂ ∈ K₂ ⊔ Q, dl g₂ (dl g₁ u) ∈ Z := by
  have hc := dl_mem_of_mem_sup hQ h12
  have hc' := dl_mem_of_mem_sup hQ fun k₂ hk₂ k₁ hk₁ => by
    have := Q.inv_mem (h12 k₁ hk₁ k₂ hk₂)
    simp only [dl] at this ⊢
    simpa [mul_assoc] using this
  have hdlU : ∀ g : Γ, ∀ u ∈ U, dl g u ∈ U := fun g u hu =>
    U.mul_mem (hU.conj_mem u hu g) (U.inv_mem hu)
  have hdlZ : ∀ g : Γ, ∀ z ∈ Z, dl g z = 1 := fun g z hz => by
    simp only [dl]
    rw [conj_eq_of_mem_center (hZc hz) g, mul_inv_cancel]
  let CB : Subgroup Γ :=
    { carrier := {w | w ∈ U ∧ ∀ b ∈ B, dl b w ∈ Z}
      mul_mem' := fun {w w'} hw hw' => ⟨U.mul_mem hw.1 hw'.1, fun b hb => by
        rw [dl_mul_right, conj_eq_of_mem_center (hZc (hw'.2 b hb)) w]
        exact Z.mul_mem (hw.2 b hb) (hw'.2 b hb)⟩
      one_mem' := ⟨U.one_mem, fun b _ => by simp [dl, Z.one_mem]⟩
      inv_mem' := fun {w} hw => ⟨U.inv_mem hw.1, fun b hb => by
        have h := dl_mul_right b w w⁻¹
        rw [mul_inv_cancel] at h
        have h0 : dl b (1 : Γ) = 1 := by simp [dl]
        rw [h0] at h
        have e : w * dl b w⁻¹ * w⁻¹ = (dl b w)⁻¹ := by
          rw [← mul_left_cancel_iff (a := dl b w), mul_inv_cancel, ← h]
        have h2 : w * dl b w⁻¹ * w⁻¹ ∈ Z := by rw [e]; exact Z.inv_mem (hw.2 b hb)
        have h3 : w⁻¹ * (w * dl b w⁻¹ * w⁻¹) * w⁻¹⁻¹ ∈ Z := by
          rw [conj_eq_of_mem_center (hZc h2) w⁻¹]
          exact h2
        simpa [mul_assoc] using h3⟩ }
  have hZCB : Z ≤ CB := fun z hz => ⟨hZU hz, fun b _ => by rw [hdlZ b z hz]; exact Z.one_mem⟩
  have hnCB : ∀ g ∈ K₁ ⊔ Q, ∀ w ∈ CB, g * w * g⁻¹ ∈ CB := by
    intro g hg w hw
    refine ⟨hU.conj_mem w hw.1 g, fun b hb => ?_⟩
    have hb' : g⁻¹ * b * g = b * dl b⁻¹ g⁻¹ := by simp only [dl]; group
    have hq : dl b⁻¹ g⁻¹ ∈ Q := by
      have h1 := hc g⁻¹ ((K₁ ⊔ Q).inv_mem hg) b⁻¹ ((K₂ ⊔ Q).inv_mem (hB hb))
      have e : dl b⁻¹ g⁻¹ = (dl g⁻¹ b⁻¹)⁻¹ := by simp only [dl]; group
      rw [e]
      exact Q.inv_mem h1
    have e : dl b (g * w * g⁻¹) = g * dl (g⁻¹ * b * g) w * g⁻¹ := by
      simp only [dl]
      group
    rw [e, hb', dl_mul, conj_eq_of_mem_center (hZc (hQU _ hq w hw.1)) b,
      conj_eq_of_mem_center (hZc (Z.mul_mem (hQU _ hq w hw.1) (hw.2 b hb))) g]
    exact Z.mul_mem (hQU _ hq w hw.1) (hw.2 b hb)
  let S : Subgroup Γ :=
    { carrier := {g | g ∈ K₁ ⊔ Q ∧ ∀ u ∈ U, dl g u ∈ CB}
      mul_mem' := fun {g h} hg hh => ⟨(K₁ ⊔ Q).mul_mem hg.1 hh.1, fun u hu => by
        rw [dl_mul]
        exact CB.mul_mem (hnCB g hg.1 _ (hh.2 u hu)) (hg.2 u hu)⟩
      one_mem' := ⟨(K₁ ⊔ Q).one_mem, fun u hu => by
        simp only [dl, one_mul, inv_one, mul_one, mul_inv_cancel]
        exact CB.one_mem⟩
      inv_mem' := fun {g} hg => ⟨(K₁ ⊔ Q).inv_mem hg.1, fun u hu => by
        rw [dl_inv]
        have := hnCB g⁻¹ ((K₁ ⊔ Q).inv_mem hg.1) _ (CB.inv_mem (hg.2 u hu))
        simpa using this⟩ }
  have hQS : Q ≤ S := fun q hq =>
    ⟨Subgroup.mem_sup_right hq, fun u hu => hZCB (hQU q hq u hu)⟩
  have hAS : A ≤ S := fun a ha =>
    ⟨hA ha, fun u hu => ⟨hdlU a u hu, fun b hb => hAB u hu a ha b hb⟩⟩
  have hK₁S : K₁ ≤ Subgroup.normalizer (S : Set Γ) := by
    intro k hk
    have key : ∀ k ∈ K₁, ∀ g ∈ S, k * g * k⁻¹ ∈ S := by
      intro k hk g hg
      refine ⟨(K₁ ⊔ Q).mul_mem ((K₁ ⊔ Q).mul_mem (Subgroup.mem_sup_left hk) hg.1)
        ((K₁ ⊔ Q).inv_mem (Subgroup.mem_sup_left hk)), fun u hu => ?_⟩
      have e : u = k * (k⁻¹ * u * k) * k⁻¹ := by group
      rw [e, dl_conj]
      exact hnCB k (Subgroup.mem_sup_left hk) _
        (hg.2 _ (by simpa using hU.conj_mem u hu k⁻¹))
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => key k hk g hg, fun hg => ?_⟩
    have := key k⁻¹ (K₁.inv_mem hk) _ hg
    simpa [mul_assoc] using this
  have hS : S = K₁ ⊔ Q := by
    rcases hS₁ S hQS (fun g hg => hg.1) hK₁S with h | h
    · exact absurd (hAS.trans h.le) hAQ
    · exact h
  have step1 : ∀ g₁ ∈ K₁ ⊔ Q, ∀ u ∈ U, dl g₁ u ∈ CB := fun g₁ hg₁ u hu => by
    have : g₁ ∈ S := by rw [hS]; exact hg₁
    exact this.2 u hu
  let D : Subgroup Γ := CB
  let R : Subgroup Γ :=
    { carrier := {g | g ∈ K₂ ⊔ Q ∧ ∀ k₁ ∈ K₁ ⊔ Q, ∀ u ∈ U, ∀ k₂ ∈ K₂ ⊔ Q,
        dl g (k₂ * dl k₁ u * k₂⁻¹) ∈ Z}
      mul_mem' := fun {g h} hg hh => ⟨(K₂ ⊔ Q).mul_mem hg.1 hh.1, fun k₁ hk₁ u hu k₂ hk₂ => by
        rw [dl_mul, conj_eq_of_mem_center (hZc (hh.2 k₁ hk₁ u hu k₂ hk₂)) g]
        exact Z.mul_mem (hh.2 k₁ hk₁ u hu k₂ hk₂) (hg.2 k₁ hk₁ u hu k₂ hk₂)⟩
      one_mem' := ⟨(K₂ ⊔ Q).one_mem, fun k₁ _ u _ k₂ _ => by
        show dl 1 _ ∈ Z
        simp only [dl, one_mul, inv_one, mul_one, mul_inv_cancel]
        exact Z.one_mem⟩
      inv_mem' := fun {g} hg => ⟨(K₂ ⊔ Q).inv_mem hg.1, fun k₁ hk₁ u hu k₂ hk₂ => by
        show dl g⁻¹ _ ∈ Z
        have h1 := conj_eq_of_mem_center (hZc (Z.inv_mem (hg.2 k₁ hk₁ u hu k₂ hk₂))) g⁻¹
        rw [inv_inv] at h1
        rw [dl_inv, h1]
        exact Z.inv_mem (hg.2 k₁ hk₁ u hu k₂ hk₂)⟩ }
  have _hD : D = CB := rfl
  have hconjCB : ∀ k₁ ∈ K₁ ⊔ Q, ∀ u ∈ U, ∀ g ∈ K₂ ⊔ Q, g * dl k₁ u * g⁻¹ ∈ CB := by
    intro k₁ hk₁ u hu g hg
    have hq : dl g k₁ ∈ Q := hc' g hg k₁ hk₁
    have e1 : g * k₁ * g⁻¹ = dl g k₁ * k₁ := by simp only [dl]; group
    have e : g * dl k₁ u * g⁻¹ = dl (dl g k₁ * k₁) (g * u * g⁻¹) := by
      rw [← e1, dl_conj]
    rw [e, dl_mul]
    have hu' : g * u * g⁻¹ ∈ U := hU.conj_mem u hu g
    have hx : dl k₁ (g * u * g⁻¹) ∈ CB := step1 k₁ hk₁ _ hu'
    have e2 : dl g k₁ * dl k₁ (g * u * g⁻¹) * (dl g k₁)⁻¹ =
        dl (dl g k₁) (dl k₁ (g * u * g⁻¹)) * dl k₁ (g * u * g⁻¹) := by
      simp only [dl]; group
    rw [e2]
    exact CB.mul_mem (CB.mul_mem (hZCB (hQU _ hq _ hx.1)) hx) (hZCB (hQU _ hq _ hu'))
  have hQR : Q ≤ R := fun q hq => ⟨Subgroup.mem_sup_right hq, fun k₁ hk₁ u hu k₂ hk₂ =>
    hQU q hq _ (hconjCB k₁ hk₁ u hu k₂ hk₂).1⟩
  have hBR : B ≤ R := fun b hb => ⟨hB hb, fun k₁ hk₁ u hu k₂ hk₂ =>
    (hconjCB k₁ hk₁ u hu k₂ hk₂).2 b hb⟩
  have hK₂R : K₂ ≤ Subgroup.normalizer (R : Set Γ) := by
    have key : ∀ k ∈ K₂, ∀ g ∈ R, k * g * k⁻¹ ∈ R := by
      intro k hk g hg
      refine ⟨(K₂ ⊔ Q).mul_mem ((K₂ ⊔ Q).mul_mem (Subgroup.mem_sup_left hk) hg.1)
        ((K₂ ⊔ Q).inv_mem (Subgroup.mem_sup_left hk)), fun k₁ hk₁ u hu k₂ hk₂ => ?_⟩
      have e : k₂ * dl k₁ u * k₂⁻¹ = k * ((k⁻¹ * k₂) * dl k₁ u * (k⁻¹ * k₂)⁻¹) * k⁻¹ := by
        group
      rw [e, dl_conj, conj_eq_of_mem_center (hZc (hg.2 k₁ hk₁ u hu _ ((K₂ ⊔ Q).mul_mem
        ((K₂ ⊔ Q).inv_mem (Subgroup.mem_sup_left hk)) hk₂))) k]
      exact hg.2 k₁ hk₁ u hu _ ((K₂ ⊔ Q).mul_mem ((K₂ ⊔ Q).inv_mem (Subgroup.mem_sup_left hk)) hk₂)
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => key k hk g hg, fun hg => ?_⟩
    have := key k⁻¹ (K₂.inv_mem hk) _ hg
    simpa [mul_assoc] using this
  have hR : R = K₂ ⊔ Q := by
    rcases hS₂ R hQR (fun g hg => hg.1) hK₂R with h | h
    · exact absurd (hBR.trans h.le) hBQ
    · exact h
  intro u hu k₁ hk₁ k₂ hk₂
  have hk₂R : k₂ ∈ R := by rw [hR]; exact hk₂
  have := hk₂R.2 k₁ hk₁ u hu 1 (K₂ ⊔ Q).one_mem
  simpa using this

section Ambient

variable {G : Type*} [Group G]

theorem subgroupOf_map_subtype' {H : Subgroup G} (S' : Subgroup ↥H) :
    (S'.map H.subtype).subgroupOf H = S' := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [Subtype.ext hyx] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem dl_mem_of_mem_sup' {H Q K₁ K₂ : Subgroup G} (hQH : Q ≤ H) (hK₁H : K₁ ≤ H) (hK₂H : K₂ ≤ H)
    (hQn : H ≤ Subgroup.normalizer (Q : Set G)) (h12 : ∀ k₁ ∈ K₁, ∀ k₂ ∈ K₂, dl k₁ k₂ ∈ Q) :
    ∀ x ∈ K₁ ⊔ Q, ∀ y ∈ K₂ ⊔ Q, dl x y ∈ Q := by
  have key := dl_mem_of_mem_sup (Γ := ↥H) (Q := Q.subgroupOf H) (K₁ := K₁.subgroupOf H)
    (K₂ := K₂.subgroupOf H) ((Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hQn)
    (fun k₁ hk₁ k₂ hk₂ => Subgroup.mem_subgroupOf.mpr (h12 _ (Subgroup.mem_subgroupOf.mp hk₁) _
      (Subgroup.mem_subgroupOf.mp hk₂)))
  intro x hx y hy
  have hxH : x ∈ H := sup_le hK₁H hQH hx
  have hyH : y ∈ H := sup_le hK₂H hQH hy
  have h := key ⟨x, hxH⟩ (by
      rw [← Subgroup.subgroupOf_sup hK₁H hQH]
      exact Subgroup.mem_subgroupOf.mpr hx) ⟨y, hyH⟩ (by
      rw [← Subgroup.subgroupOf_sup hK₂H hQH]
      exact Subgroup.mem_subgroupOf.mpr hy)
  exact Subgroup.mem_subgroupOf.mp h

theorem comm_comm_mem_of_quadratic' {H U Q K₁ K₂ A B Z : Subgroup G}
    (hZc : H ≤ Subgroup.centralizer (Z : Set G)) (hZU : Z ≤ U) (hUH : U ≤ H) (hQH : Q ≤ H)
    (hK₁H : K₁ ≤ H) (hK₂H : K₂ ≤ H) (hAH : A ≤ H) (hBH : B ≤ H)
    (hUn : H ≤ Subgroup.normalizer (U : Set G)) (hQn : H ≤ Subgroup.normalizer (Q : Set G))
    (hQU : ∀ q ∈ Q, ∀ u ∈ U, dl q u ∈ Z) (h12 : ∀ k₁ ∈ K₁, ∀ k₂ ∈ K₂, dl k₁ k₂ ∈ Q)
    (hA : A ≤ K₁ ⊔ Q) (hB : B ≤ K₂ ⊔ Q)
    (hAB : ∀ u ∈ U, ∀ a ∈ A, ∀ b ∈ B, dl b (dl a u) ∈ Z)
    (hS₁ : ∀ S : Subgroup G, Q ≤ S → S ≤ K₁ ⊔ Q → K₁ ≤ Subgroup.normalizer (S : Set G) →
      S = Q ∨ S = K₁ ⊔ Q)
    (hS₂ : ∀ S : Subgroup G, Q ≤ S → S ≤ K₂ ⊔ Q → K₂ ≤ Subgroup.normalizer (S : Set G) →
      S = Q ∨ S = K₂ ⊔ Q)
    (hAQ : ¬ A ≤ Q) (hBQ : ¬ B ≤ Q) :
    ∀ u ∈ U, ∀ g₁ ∈ K₁ ⊔ Q, ∀ g₂ ∈ K₂ ⊔ Q, dl g₂ (dl g₁ u) ∈ Z := by
  have hZH : Z ≤ H := hZU.trans hUH
  have hsup₁ : (K₁ ⊔ Q).subgroupOf H = K₁.subgroupOf H ⊔ Q.subgroupOf H :=
    Subgroup.subgroupOf_sup hK₁H hQH
  have hsup₂ : (K₂ ⊔ Q).subgroupOf H = K₂.subgroupOf H ⊔ Q.subgroupOf H :=
    Subgroup.subgroupOf_sup hK₂H hQH
  have hS : ∀ K : Subgroup G, K ≤ H → (∀ S : Subgroup G, Q ≤ S → S ≤ K ⊔ Q →
      K ≤ Subgroup.normalizer (S : Set G) → S = Q ∨ S = K ⊔ Q) →
      ∀ S' : Subgroup ↥H, Q.subgroupOf H ≤ S' → S' ≤ K.subgroupOf H ⊔ Q.subgroupOf H →
        K.subgroupOf H ≤ Subgroup.normalizer (S' : Set ↥H) →
        S' = Q.subgroupOf H ∨ S' = K.subgroupOf H ⊔ Q.subgroupOf H := by
    intro K hKH hSK S' hQS hSK' hKS
    rw [← Subgroup.subgroupOf_sup hKH hQH] at hSK' ⊢
    set S := S'.map H.subtype with hSdef
    have hQS' : Q ≤ S := fun q hq => ⟨⟨q, hQH hq⟩, hQS (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
    have hSK'' : S ≤ K ⊔ Q := by
      rintro _ ⟨s, hs, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hSK' hs)
    have hKS' : K ≤ Subgroup.normalizer (S : Set G) := by
      intro k hk
      have key : ∀ k ∈ K, ∀ x ∈ S, k * x * k⁻¹ ∈ S := by
        rintro k hk _ ⟨s, hs, rfl⟩
        have hk' : (⟨k, hKH hk⟩ : ↥H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.mpr hk
        exact ⟨_, (Subgroup.mem_normalizer_iff.mp (hKS hk') s).mp hs, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
      have := key k⁻¹ (K.inv_mem hk) _ hx
      simpa [mul_assoc] using this
    rcases hSK S hQS' hSK'' hKS' with h | h
    · left
      rw [← subgroupOf_map_subtype' S', ← hSdef, h]
    · right
      rw [← subgroupOf_map_subtype' S', ← hSdef, h]
  have key := comm_comm_mem_of_quadratic (Γ := ↥H) (U := U.subgroupOf H) (Q := Q.subgroupOf H)
    (K₁ := K₁.subgroupOf H) (K₂ := K₂.subgroupOf H) (A := A.subgroupOf H) (B := B.subgroupOf H)
    (Z := Z.subgroupOf H)
    (fun x hx => Subgroup.mem_center_iff.mpr fun g => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hZc g.2) x (Subgroup.mem_subgroupOf.mp hx)).symm)
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hZU (Subgroup.mem_subgroupOf.mp hx)))
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hUn)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hQn)
    (fun q hq u hu => Subgroup.mem_subgroupOf.mpr (hQU _ (Subgroup.mem_subgroupOf.mp hq) _
      (Subgroup.mem_subgroupOf.mp hu)))
    (fun k₁ hk₁ k₂ hk₂ => Subgroup.mem_subgroupOf.mpr (h12 _ (Subgroup.mem_subgroupOf.mp hk₁) _
      (Subgroup.mem_subgroupOf.mp hk₂)))
    (fun x hx => by
      rw [← hsup₁]
      exact Subgroup.mem_subgroupOf.mpr (hA (Subgroup.mem_subgroupOf.mp hx)))
    (fun x hx => by
      rw [← hsup₂]
      exact Subgroup.mem_subgroupOf.mpr (hB (Subgroup.mem_subgroupOf.mp hx)))
    (fun u hu a ha b hb => Subgroup.mem_subgroupOf.mpr (hAB _ (Subgroup.mem_subgroupOf.mp hu) _
      (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb)))
    (hS K₁ hK₁H hS₁) (hS K₂ hK₂H hS₂)
    (fun h => hAQ fun a ha => Subgroup.mem_subgroupOf.mp
      (h (Subgroup.mem_subgroupOf.mpr (show ((⟨a, hAH ha⟩ : ↥H) : G) ∈ A from ha))))
    (fun h => hBQ fun b hb => Subgroup.mem_subgroupOf.mp
      (h (Subgroup.mem_subgroupOf.mpr (show ((⟨b, hBH hb⟩ : ↥H) : G) ∈ B from hb))))
  intro u hu g₁ hg₁ g₂ hg₂
  have hg₁H : g₁ ∈ H := sup_le hK₁H hQH hg₁
  have hg₂H : g₂ ∈ H := sup_le hK₂H hQH hg₂
  have h := key ⟨u, hUH hu⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨g₁, hg₁H⟩
    (by rw [← hsup₁]; exact Subgroup.mem_subgroupOf.mpr hg₁) ⟨g₂, hg₂H⟩
    (by rw [← hsup₂]; exact Subgroup.mem_subgroupOf.mpr hg₂)
  exact Subgroup.mem_subgroupOf.mp h

end Ambient

end CFSG.Quasithin.H13.Ch8312
