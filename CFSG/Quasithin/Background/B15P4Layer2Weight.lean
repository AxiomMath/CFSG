module

import all CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Background.B1Basic
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Quasithin.B15P4

variable {V : Type*} [CommGroup V]

theorem cv_eq (v : V) (a : MulAut V) : B1.cv v a = a v * v⁻¹ := by
  unfold B1.cv
  rfl

@[expose] noncomputable def wt (B : Subgroup (MulAut V)) : ℕ :=
  Nat.card B * Nat.card (fixV B)

theorem wt_pos [Finite V] (B : Subgroup (MulAut V)) : 0 < wt B :=
  Nat.mul_pos Nat.card_pos Nat.card_pos

theorem wt_le_of_isFFStarOffender {X A B : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (hB : B ≤ A) : wt B ≤ wt A :=
  hA.card_le hB

theorem wt_bot [Finite V] : wt (⊥ : Subgroup (MulAut V)) = Nat.card V := by
  unfold wt
  rw [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, one_mul]

theorem fixV_sup (B₁ B₂ : Subgroup (MulAut V)) : fixV (B₁ ⊔ B₂) = fixV B₁ ⊓ fixV B₂ :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq B₁ B₂

theorem wt_mul_wt_le [Finite V] {A B₁ B₂ : Subgroup (MulAut V)}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (h₁ : B₁ ≤ A) (h₂ : B₂ ≤ A) :
    wt B₁ * wt B₂ ≤ wt (B₁ ⊓ B₂) * wt (B₁ ⊔ B₂) := by
  have e1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B₁ B₂
    (fun x hx y hy => hc x (h₁ hx) y (h₂ hy))).1
  have e2 := card_sup_mul_card_inf (fixV B₁) (fixV B₂)
  rw [← fixV_sup] at e2
  have e3 : Nat.card ↥(fixV B₁ ⊔ fixV B₂) ≤ Nat.card ↥(fixV (B₁ ⊓ B₂)) :=
    Subgroup.card_le_of_le (sup_le (B1.fixV_le_fixV inf_le_left) (B1.fixV_le_fixV inf_le_right))
  unfold wt
  calc Nat.card B₁ * Nat.card (fixV B₁) * (Nat.card B₂ * Nat.card (fixV B₂))
      = (Nat.card B₁ * Nat.card B₂) * (Nat.card (fixV B₁) * Nat.card (fixV B₂)) := by ring
    _ = (Nat.card ↥(B₁ ⊔ B₂) * Nat.card ↥(B₁ ⊓ B₂)) *
        (Nat.card ↥(fixV B₁ ⊔ fixV B₂) * Nat.card ↥(fixV (B₁ ⊔ B₂))) := by rw [e1, e2]
    _ ≤ (Nat.card ↥(B₁ ⊔ B₂) * Nat.card ↥(B₁ ⊓ B₂)) *
        (Nat.card ↥(fixV (B₁ ⊓ B₂)) * Nat.card ↥(fixV (B₁ ⊔ B₂))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ e3)
    _ = Nat.card ↥(B₁ ⊓ B₂) * Nat.card ↥(fixV (B₁ ⊓ B₂)) *
        (Nat.card ↥(B₁ ⊔ B₂) * Nat.card ↥(fixV (B₁ ⊔ B₂))) := by ring

theorem wt_inf_eq [Finite V] {X A B₁ B₂ : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (h₁ : B₁ ≤ A) (h₂ : B₂ ≤ A) (e₁ : wt B₁ = wt A) (e₂ : wt B₂ = wt A) :
    wt (B₁ ⊓ B₂) = wt A := by
  have h := wt_mul_wt_le hA.2.2.1.1 h₁ h₂
  have hle : wt (B₁ ⊔ B₂) ≤ wt A := wt_le_of_isFFStarOffender hA (sup_le h₁ h₂)
  refine le_antisymm (wt_le_of_isFFStarOffender hA (inf_le_left.trans h₁)) ?_
  rw [e₁, e₂] at h
  have h2 : wt A * wt A ≤ wt (B₁ ⊓ B₂) * wt A := h.trans (Nat.mul_le_mul_left _ hle)
  exact Nat.le_of_mul_le_mul_right h2 (wt_pos A)

theorem wt_Bv [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) (v : V) :
    wt (B1.Bv A v) = wt A :=
  le_antisymm (wt_le_of_isFFStarOffender hA (B1.Bv_le A v)) (B1.card_mul_le_Bv hA.2.2.1.1 v)

@[expose] def A2sub (A : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  A ⊓ ⨅ v : V, B1.Bv A v

theorem A2sub_le (A : Subgroup (MulAut V)) : A2sub A ≤ A := inf_le_left

theorem mem_A2sub {A : Subgroup (MulAut V)} {b : MulAut V} :
    b ∈ A2sub A ↔ b ∈ A ∧ ∀ v : V, B1.cv v b ∈ fixV A := by
  unfold A2sub
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, B1.mem_Bv]
  constructor
  · rintro ⟨hb, h⟩
    exact ⟨hb, fun v => (h v).2⟩
  · rintro ⟨hb, h⟩
    exact ⟨hb, fun v => ⟨hb, h v⟩⟩

theorem A2sub_fix_comm {A : Subgroup (MulAut V)} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {b : MulAut V} (hb : b ∈ A2sub A) {a : MulAut V} (ha : a ∈ A) (v : V) :
    b (a v * v⁻¹) = a v * v⁻¹ := by
  obtain ⟨hbA, hbv⟩ := mem_A2sub.1 hb
  have hcv : a (B1.cv v b) = B1.cv v b := hbv v a ha
  have hab : b (a v) = a (b v) := by
    have := congrArg (fun t : MulAut V => t v) (hc b hbA a ha)
    simpa only [MulAut.mul_apply] using this
  rw [cv_eq] at hcv
  have e : b v = (b v * v⁻¹) * v := by simp
  have h1 : a (b v) = (b v * v⁻¹) * a v := by
    conv_lhs => rw [e]
    rw [map_mul, hcv]
  rw [map_mul, map_inv, hab, h1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem isElemAbelian2_A2sub {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) :
    IsElemAbelian2 (A2sub A) :=
  ⟨fun a ha b hb => hA.1 a (A2sub_le A ha) b (A2sub_le A hb),
    fun a ha => hA.2 a (A2sub_le A ha)⟩

theorem isQuadratic_A2sub {A : Subgroup (MulAut V)} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    IsQuadratic (A2sub A) := by
  unfold IsQuadratic commV
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩ b hb
  exact A2sub_fix_comm hc hb (A2sub_le A hx) v

theorem wt_inf_Bv_finset [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (S : Finset V) : wt (A ⊓ ⨅ v ∈ S, B1.Bv A v) = wt A := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert v S hvS ih =>
    have hset : A ⊓ ⨅ w ∈ insert v S, B1.Bv A w = (A ⊓ ⨅ w ∈ S, B1.Bv A w) ⊓ B1.Bv A v := by
      rw [Finset.iInf_insert]
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [hset]
    exact wt_inf_eq hA inf_le_left (B1.Bv_le A v) ih (wt_Bv hA v)

theorem wt_A2sub [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    wt (A2sub A) = wt A := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have h := wt_inf_Bv_finset hA Finset.univ
  simpa [A2sub] using h

theorem isFFStarOffender_A2sub [Finite V] {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (hne : A2sub A ≠ ⊥) : IsFFStarOffender X (A2sub A) :=
  ⟨(A2sub_le A).trans hA.1, hne, isElemAbelian2_A2sub hA.2.2.1, fun B hB => by
    have h1 : wt B ≤ wt A := wt_le_of_isFFStarOffender hA (hB.trans (A2sub_le A))
    show wt B ≤ wt (A2sub A)
    rw [wt_A2sub hA]
    exact h1⟩

theorem A2sub_ne_bot_of_lt [Finite V] {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (hlt : Nat.card V < Nat.card A * Nat.card (fixV A)) : A2sub A ≠ ⊥ := by
  intro h
  have h1 := wt_A2sub hA
  rw [h, wt_bot] at h1
  unfold wt at h1
  omega

end CFSG.Quasithin.B15P4
