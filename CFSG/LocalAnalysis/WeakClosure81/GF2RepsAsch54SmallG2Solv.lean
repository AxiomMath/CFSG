module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import Mathlib.GroupTheory.Solvable

import CFSG.GH74.Generic.BProg.B2.GenLocG2OuterShape
import CFSG.GH74.GLS.LU.Local.SL2Pure

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80G2

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab (Shape mem_sup_of_commute mem_zpowers_of_sq)
open CFSG.GH74.Generic.BProg.B2.GenLocG2OuterShape (mem_E_or neg_one_ne_one₁)
open scoped MatrixGroups commutatorElement

theorem shape_commutator_mem_sup {K : Type} [Group K] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (S : Shape K F₁ F₂) (x y : K) : ⁅x, y⁆ ∈ S.I₁ ⊔ S.I₂ := by
  have := S.normal₁
  have := S.normal₂
  have hJ : (S.I₁ ⊔ S.I₂).Normal := Subgroup.sup_normal S.I₁ S.I₂
  rcases mem_E_or S x with hx | hx
  · have h1 : y * x⁻¹ * y⁻¹ ∈ S.I₁ ⊔ S.I₂ := hJ.conj_mem _ (inv_mem hx) y
    have h2 : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact mul_mem hx h1
  · rcases mem_E_or S y with hy | hy
    · rw [commutatorElement_def]
      exact mul_mem (hJ.conj_mem _ hy x) (inv_mem hy)
    · have h1 : S.t⁻¹ * ((y * S.t) * (x * S.t)⁻¹) * S.t⁻¹⁻¹ ∈ S.I₁ ⊔ S.I₂ :=
        hJ.conj_mem _ (mul_mem hy (inv_mem hx)) S.t⁻¹
      have h2 : ⁅x, y⁆ =
          (x * S.t) * (S.t⁻¹ * ((y * S.t) * (x * S.t)⁻¹) * S.t⁻¹⁻¹) * (y * S.t)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [h2]
      exact mul_mem (mul_mem hx h1) (inv_mem hy)

theorem shape_commute_of_centralizer₁ {K : Type} [Group K] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (S : Shape K F₁ F₂) {a x y : K} (ha : a ∈ S.I₁) (haa : a * a = S.z) (hx : x ∈ S.I₁)
    (hy : y ∈ S.I₁) (hxa : x * a = a * x) (hya : y * a = a * y) : x * y = y * x := by
  have hsq : S.e₁ ⟨a, ha⟩ * S.e₁ ⟨a, ha⟩ = -1 := by
    rw [← map_mul, show (⟨a, ha⟩ : ↥S.I₁) * ⟨a, ha⟩ = ⟨S.z, S.z_mem₁⟩ from Subtype.ext haa,
      S.e₁_z]
  have hnc : S.e₁ ⟨a, ha⟩ ∉ Subgroup.center SL(2, F₁) := fun hc =>
    neg_one_ne_one₁ S
      (hsq.symm.trans (CFSG.GH74.GLS.IVK.Lifted.sq_eq_one_of_mem_center_sl2 hc))
  have key : ∀ w : K, ∀ hw : w ∈ S.I₁, w * a = a * w →
      S.e₁ ⟨w, hw⟩ * S.e₁ ⟨a, ha⟩ = S.e₁ ⟨a, ha⟩ * S.e₁ ⟨w, hw⟩ := fun w hw hwa => by
    rw [← map_mul, ← map_mul]
    exact congrArg S.e₁ (Subtype.ext hwa)
  have h := CFSG.GH74.GLS.LU.Local.sl2_commute_of_centralizer hnc (key x hx hxa) (key y hy hya)
  rw [← map_mul, ← map_mul] at h
  exact congrArg Subtype.val (S.e₁.injective h)

theorem shape_commute_of_centralizer₂ {K : Type} [Group K] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (S : Shape K F₁ F₂) {a x y : K} (ha : a ∈ S.I₂) (haa : a * a = S.z) (hx : x ∈ S.I₂)
    (hy : y ∈ S.I₂) (hxa : x * a = a * x) (hya : y * a = a * y) : x * y = y * x :=
  shape_commute_of_centralizer₁ S.swap ha haa hx hy hxa hya

theorem shape_conj_mul_cases {K : Type} [Group K] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (S : Shape K F₁ F₂) {a b x : K} (ha : a ∈ S.I₁) (hb : b ∈ S.I₂) (haa : a * a = S.z)
    (hx : x * (a * b) = (a * b) * x) : x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹ := by
  have n₁ := S.normal₁
  have n₂ := S.normal₂
  have ha' : x * a * x⁻¹ ∈ S.I₁ := n₁.conj_mem a ha x
  have hb' : x * b * x⁻¹ ∈ S.I₂ := n₂.conj_mem b hb x
  have hab : (x * a * x⁻¹) * (x * b * x⁻¹) = a * b := by
    calc (x * a * x⁻¹) * (x * b * x⁻¹) = x * (a * b) * x⁻¹ := by group
      _ = (a * b) * x * x⁻¹ := by rw [hx]
      _ = a * b := by group
  have hw : a⁻¹ * (x * a * x⁻¹) = b * (x * b * x⁻¹)⁻¹ := by
    calc a⁻¹ * (x * a * x⁻¹)
        = a⁻¹ * ((x * a * x⁻¹) * (x * b * x⁻¹)) * (x * b * x⁻¹)⁻¹ := by group
      _ = b * (x * b * x⁻¹)⁻¹ := by rw [hab]; group
  have hmem : a⁻¹ * (x * a * x⁻¹) ∈ Subgroup.zpowers S.z := by
    rw [← S.inter]
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha) ha', ?_⟩
    rw [hw]
    exact mul_mem hb (inv_mem hb')
  rcases mem_zpowers_of_sq S.z_sq hmem with h | h
  · left
    calc x * a * x⁻¹ = a * (a⁻¹ * (x * a * x⁻¹)) := by group
      _ = a := by rw [h, mul_one]
  · right
    have hz : a * (a * S.z) = 1 := by rw [← mul_assoc, haa, S.z_sq]
    calc x * a * x⁻¹ = a * (a⁻¹ * (x * a * x⁻¹)) := by group
      _ = a * S.z := by rw [h]
      _ = a⁻¹ := eq_inv_of_mul_eq_one_right hz

private theorem conj_swap_of_cases {G : Type} [Group G] {a u v : G}
    (hu : u * a * u⁻¹ = a ∨ u * a * u⁻¹ = a⁻¹) (hv : v * a * v⁻¹ = a ∨ v * a * v⁻¹ = a⁻¹) :
    u * (v * a * v⁻¹) * u⁻¹ = v * (u * a * u⁻¹) * v⁻¹ := by
  have inv : ∀ g c : G, g * c⁻¹ * g⁻¹ = (g * c * g⁻¹)⁻¹ := fun g c => by group
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp only [inv, hu, hv, inv_inv]

private theorem commutator_commute_of_cases {G : Type} [Group G] {a x y : G}
    (hx : x⁻¹ * a * x⁻¹⁻¹ = a ∨ x⁻¹ * a * x⁻¹⁻¹ = a⁻¹)
    (hy : y⁻¹ * a * y⁻¹⁻¹ = a ∨ y⁻¹ * a * y⁻¹⁻¹ = a⁻¹) : ⁅x, y⁆ * a = a * ⁅x, y⁆ := by
  have h := conj_swap_of_cases hx hy
  have h2 : ⁅x, y⁆ * a * ⁅x, y⁆⁻¹ = a := by
    calc ⁅x, y⁆ * a * ⁅x, y⁆⁻¹
        = (x * y) * (x⁻¹ * (y⁻¹ * a * y⁻¹⁻¹) * x⁻¹⁻¹) * (x * y)⁻¹ := by
          rw [commutatorElement_def]; group
      _ = (x * y) * (y⁻¹ * (x⁻¹ * a * x⁻¹⁻¹) * y⁻¹⁻¹) * (x * y)⁻¹ := by rw [h]
      _ = a := by group
  calc ⁅x, y⁆ * a = (⁅x, y⁆ * a * ⁅x, y⁆⁻¹) * ⁅x, y⁆ := by rw [inv_mul_cancel_right]
    _ = a * ⁅x, y⁆ := by rw [h2]

theorem shape_commutator_commute {K : Type} [Group K] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (S : Shape K F₁ F₂) {a b x y : K} (ha : a ∈ S.I₁) (hb : b ∈ S.I₂) (haa : a * a = S.z)
    (hx : x * (a * b) = (a * b) * x) (hy : y * (a * b) = (a * b) * y) :
    ⁅x, y⁆ * a = a * ⁅x, y⁆ := by
  have hcent : ∀ w : K, w * (a * b) = (a * b) * w → w⁻¹ * (a * b) = (a * b) * w⁻¹ :=
    fun w hw => Subgroup.mem_centralizer_singleton_iff.1
      (inv_mem (Subgroup.mem_centralizer_singleton_iff.2 hw))
  exact commutator_commute_of_cases (shape_conj_mul_cases S ha hb haa (hcent x hx))
    (shape_conj_mul_cases S ha hb haa (hcent y hy))

theorem shape_commute_of_commute_mul {K : Type} [Group K] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (S : Shape K F₁ F₂) {a b g h : K} (ha : a ∈ S.I₁) (hb : b ∈ S.I₂) (haa : a * a = S.z)
    (hbb : b * b = S.z) (hg : g ∈ S.I₁ ⊔ S.I₂) (hh : h ∈ S.I₁ ⊔ S.I₂)
    (hga : g * a = a * g) (hha : h * a = a * h) (hgab : g * (a * b) = (a * b) * g)
    (hhab : h * (a * b) = (a * b) * h) : g * h = h * g := by
  have hcb : ∀ w : K, w * a = a * w → w * (a * b) = (a * b) * w → w * b = b * w := by
    intro w hwa hwab
    refine mul_left_cancel (a := a) ?_
    calc a * (w * b) = (a * w) * b := by rw [mul_assoc]
      _ = (w * a) * b := by rw [hwa]
      _ = w * (a * b) := by rw [mul_assoc]
      _ = (a * b) * w := hwab
      _ = a * (b * w) := by rw [mul_assoc]
  have key₁ : ∀ x y : K, x ∈ S.I₁ → y ∈ S.I₂ → x * y * a = a * (x * y) → x * a = a * x := by
    intro x y hx hy hxy
    refine mul_right_cancel (b := y) ?_
    calc x * a * y = x * (a * y) := by rw [mul_assoc]
      _ = x * (y * a) := by rw [S.comm a ha y hy]
      _ = x * y * a := by rw [mul_assoc]
      _ = a * (x * y) := hxy
      _ = a * x * y := by rw [mul_assoc]
  have key₂ : ∀ x y : K, x ∈ S.I₁ → y ∈ S.I₂ → x * y * b = b * (x * y) → y * b = b * y := by
    intro x y hx hy hxy
    refine mul_left_cancel (a := x) ?_
    calc x * (y * b) = x * y * b := by rw [mul_assoc]
      _ = b * (x * y) := hxy
      _ = (b * x) * y := by rw [mul_assoc]
      _ = (x * b) * y := by rw [S.comm x hx b hb]
      _ = x * (b * y) := by rw [mul_assoc]
  obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := mem_sup_of_commute S.comm hg
  obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := mem_sup_of_commute S.comm hh
  have c₁ : Commute x₁ x₂ := shape_commute_of_centralizer₁ S ha haa hx₁ hx₂
    (key₁ x₁ y₁ hx₁ hy₁ hga) (key₁ x₂ y₂ hx₂ hy₂ hha)
  have c₂ : Commute y₁ y₂ := shape_commute_of_centralizer₂ S hb hbb hy₁ hy₂
    (key₂ x₁ y₁ hx₁ hy₁ (hcb _ hga hgab)) (key₂ x₂ y₂ hx₂ hy₂ (hcb _ hha hhab))
  have c₃ : Commute x₁ y₂ := S.comm x₁ hx₁ y₂ hy₂
  have c₄ : Commute y₁ x₂ := (S.comm x₂ hx₂ y₁ hy₁).symm
  exact ((c₁.mul_right c₃).mul_left (c₄.mul_right c₂)).eq

theorem shape_isSolvable_centralizer_mul {K : Type} [Group K] {F₁ F₂ : Type}
    [Field F₁] [Field F₂] (S : Shape K F₁ F₂) {a b : K}
    (ha : a ∈ S.I₁) (hb : b ∈ S.I₂) (haa : a * a = S.z) (hbb : b * b = S.z) :
    Group.IsSolvable ↥(Subgroup.centralizer ({a * b} : Set K)) := by
  set H : Subgroup K := Subgroup.centralizer ({a * b} : Set K)
  set P : Subgroup K := Subgroup.centralizer ({a} : Set K) ⊓ (S.I₁ ⊔ S.I₂)
  have h1 : derivedSeries ↥H 1 ≤ P.comap H.subtype := by
    rw [derivedSeries_succ, derivedSeries_zero]
    refine Subgroup.commutator_le.2 fun x _ y _ => ?_
    have hx : (x : K) * (a * b) = (a * b) * x := Subgroup.mem_centralizer_singleton_iff.1 x.2
    have hy : (y : K) * (a * b) = (a * b) * y := Subgroup.mem_centralizer_singleton_iff.1 y.2
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
      (shape_commutator_commute S ha hb haa hx hy), shape_commutator_mem_sup S x y⟩
  refine (Group.isSolvable_def _).2 ⟨2, ?_⟩
  rw [derivedSeries_succ, eq_bot_iff]
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  have hx' := Subgroup.mem_inf.1 (Subgroup.mem_comap.1 (h1 hx))
  have hy' := Subgroup.mem_inf.1 (Subgroup.mem_comap.1 (h1 hy))
  exact Subtype.ext (shape_commute_of_commute_mul S ha hb haa hbb hx'.2 hy'.2
    (Subgroup.mem_centralizer_singleton_iff.1 hx'.1)
    (Subgroup.mem_centralizer_singleton_iff.1 hy'.1)
    (Subgroup.mem_centralizer_singleton_iff.1 x.2) (Subgroup.mem_centralizer_singleton_iff.1 y.2))

end CFSG.LocalAnalysis.WeakClosure81.Asch80G2

end
