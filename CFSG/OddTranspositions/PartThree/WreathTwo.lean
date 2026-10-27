module

public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import Mathlib.GroupTheory.Index
import TauCeti.Data.Fin.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddTranspositions.PartThree

open SemidirectProduct
open CFSG.Timmesfeld.Bridge.Asc72

private theorem exists_mul_of_mem_sup {Y : Type*} [Group Y] {S₁ S₂ : Subgroup Y}
    (hc : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) {x : Y} (hx : x ∈ S₁ ⊔ S₂) :
    ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, x = x₁ * x₂ := by
  let H : Subgroup Y :=
    { carrier := {x | ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, x = x₁ * x₂}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, a₂, ha₂, rfl⟩ ⟨c₁, hc₁, c₂, hc₂, rfl⟩
        refine ⟨a₁ * c₁, S₁.mul_mem ha₁ hc₁, a₂ * c₂, S₂.mul_mem ha₂ hc₂, ?_⟩
        calc a₁ * a₂ * (c₁ * c₂) = a₁ * (a₂ * c₁) * c₂ := by group
          _ = a₁ * (c₁ * a₂) * c₂ := by rw [hc c₁ hc₁ a₂ ha₂]
          _ = a₁ * c₁ * (a₂ * c₂) := by group
      one_mem' := ⟨1, S₁.one_mem, 1, S₂.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a₁, ha₁, a₂, ha₂, rfl⟩
        refine ⟨a₁⁻¹, S₁.inv_mem ha₁, a₂⁻¹, S₂.inv_mem ha₂, ?_⟩
        rw [mul_inv_rev]
        exact (hc _ (S₁.inv_mem ha₁) _ (S₂.inv_mem ha₂)).symm }
  have hle : S₁ ⊔ S₂ ≤ H :=
    sup_le (fun y hy => ⟨y, hy, 1, S₂.one_mem, (mul_one y).symm⟩)
      (fun y hy => ⟨1, S₁.one_mem, y, hy, (one_mul y).symm⟩)
  exact hle hx

private theorem swap01_ne_one : (Equiv.swap (0 : Fin 2) 1) ≠ 1 := by
  intro h
  have h0 : (1 : Fin 2) = 0 := by
    simpa using congrArg (fun σ : Equiv.Perm (Fin 2) => σ (0 : Fin 2)) h
  exact absurd h0 (by decide)

private theorem conj_sq_swap {Y : Type*} [Group Y] {r x y : Y} (hr : r * r = 1) :
    r * (x * (r * y * r⁻¹)) * r⁻¹ = (r * x * r⁻¹) * y := by
  rw [inv_eq_of_mul_eq_one_right hr]
  calc r * (x * (r * y * r)) * r = r * x * r * y * (r * r) := by group
    _ = (r * x * r) * y := by rw [hr]; group

private theorem conj_sq_swap_one {Y : Type*} [Group Y] {r y : Y} (hr : r * r = 1) :
    r * (r * y * r⁻¹) * r⁻¹ = y :=
  by simpa using conj_sq_swap (x := 1) (y := y) hr

theorem exists_mulEquiv_wreathTwo {L Y : Type*} [Group L] [Group Y] {A B : Subgroup Y}
    (α : L ≃* A) (hinf : A ⊓ B = ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hindex : (A ⊔ B).index = 2) {r : Y} (hr : r * r = 1) (hrN : r ∉ A ⊔ B)
    (hswap : A.map (MulAut.conj r).toMonoidHom = B) :
    ∃ Ψ : ((Fin 2 → L) ⋊[CFSG.Timmesfeld.Bridge.Asc72.permAct (Fin 2) L]
        Equiv.Perm (Fin 2)) ≃* Y,
      Ψ (SemidirectProduct.inr (Equiv.swap 0 1)) = r := by
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have conjB : ∀ a ∈ A, r * a * r⁻¹ ∈ B := by
    intro a ha
    have h := Subgroup.mem_map_of_mem (MulAut.conj r).toMonoidHom ha
    rw [hswap] at h
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  have conjA : ∀ b ∈ B, r * b * r⁻¹ ∈ A := by
    intro b hb
    rw [← hswap] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [show (MulAut.conj r).toMonoidHom a = r * a * r⁻¹ by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply], conj_sq_swap_one hr]
    exact ha
  have hcommY : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb => (hcomm a ha b hb).eq
  let αY : L →* Y := A.subtype.comp α.toMonoidHom
  have αY_symm : ∀ x : A, αY (α.symm x) = (x : Y) := by
    intro x
    show ((α (α.symm x) : A) : Y) = (x : Y)
    simp
  let gg : (Fin 2 → L) → Y := fun f => αY (f 0) * (r * αY (f 1) * r⁻¹)
  have hgg : ∀ f h : Fin 2 → L, gg (f * h) = gg f * gg h := by
    intro f h
    have hb : r * αY (f 1) * r⁻¹ ∈ B := conjB (α (f 1)) (α (f 1)).2
    have ha : αY (h 0) ∈ A := (α (h 0)).2
    change αY ((f * h) 0) * (r * αY ((f * h) 1) * r⁻¹)
      = (αY (f 0) * (r * αY (f 1) * r⁻¹)) * (αY (h 0) * (r * αY (h 1) * r⁻¹))
    simp only [Pi.mul_apply, map_mul]
    rw [show r * (αY (f 1) * αY (h 1)) * r⁻¹
          = (r * αY (f 1) * r⁻¹) * (r * αY (h 1) * r⁻¹) by group]
    exact (hcomm (αY (h 0)) ha (r * αY (f 1) * r⁻¹) hb).mul_mul_mul_comm
      (αY (f 0)) (r * αY (h 1) * r⁻¹)
  let g : (Fin 2 → L) →* Y := MonoidHom.mk' gg hgg
  have g_apply : ∀ f : Fin 2 → L, g f = αY (f 0) * (r * αY (f 1) * r⁻¹) := fun _ => rfl
  let ssFun : Equiv.Perm (Fin 2) → Y := fun σ => if σ = 1 then 1 else r
  have hss : ∀ σ τ : Equiv.Perm (Fin 2), ssFun (σ * τ) = ssFun σ * ssFun τ := by
    intro σ τ
    change (if σ * τ = 1 then (1 : Y) else r)
      = (if σ = 1 then 1 else r) * (if τ = 1 then 1 else r)
    rcases TauCeti.perm_fin_two_eq_one_or_swap σ with rfl | rfl <;>
      rcases TauCeti.perm_fin_two_eq_one_or_swap τ with rfl | rfl <;>
      simp [swap01_ne_one, Equiv.swap_swap (0 : Fin 2) 1, hr]
  let ss : Equiv.Perm (Fin 2) →* Y := MonoidHom.mk' ssFun hss
  have ss_apply : ∀ σ : Equiv.Perm (Fin 2), ss σ = if σ = 1 then 1 else r := fun _ => rfl
  have hcompat : ∀ σ : Equiv.Perm (Fin 2),
      g.comp (permAct (Fin 2) L σ).toMonoidHom
        = (MulAut.conj (ss σ)).toMonoidHom.comp g := by
    intro σ
    ext f
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    rcases TauCeti.perm_fin_two_eq_one_or_swap σ with rfl | rfl
    · change g ((permAct (Fin 2) L) 1 f) = (MulAut.conj (ss 1)) (g f)
      simp [MulAut.conj_apply]
    · change g ((permAct (Fin 2) L) (Equiv.swap 0 1) f)
          = (MulAut.conj (ss (Equiv.swap 0 1))) (g f)
      rw [show (permAct (Fin 2) L) (Equiv.swap 0 1) f
            = fun i => f (Equiv.swap 0 1 i) from by ext i; rfl]
      simp only [g_apply, ss_apply, if_neg swap01_ne_one, MulAut.conj_apply,
        Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [conj_sq_swap hr]
      exact hcomm (αY (f 1)) (α (f 1)).2 (r * αY (f 0) * r⁻¹)
        (conjB (α (f 0)) (α (f 0)).2)
  let F : ((Fin 2 → L) ⋊[CFSG.Timmesfeld.Bridge.Asc72.permAct (Fin 2) L]
      Equiv.Perm (Fin 2)) →* Y := SemidirectProduct.lift g ss hcompat
  have F_apply : ∀ (f : Fin 2 → L) (σ : Equiv.Perm (Fin 2)),
      F ⟨f, σ⟩ = αY (f 0) * (r * αY (f 1) * r⁻¹) * (if σ = 1 then 1 else r) := by
    intro f σ
    change g f * ss σ = αY (f 0) * (r * αY (f 1) * r⁻¹) * (if σ = 1 then 1 else r)
    rw [g_apply, ss_apply]
  have hker : ∀ x : ((Fin 2 → L) ⋊[CFSG.Timmesfeld.Bridge.Asc72.permAct (Fin 2) L]
      Equiv.Perm (Fin 2)), F x = 1 → x = 1 := by
    intro x hx
    obtain ⟨f, σ⟩ := x
    rw [F_apply] at hx
    rcases TauCeti.perm_fin_two_eq_one_or_swap σ with rfl | rfl
    · rw [if_pos rfl, mul_one] at hx
      have ha_mem : αY (f 0) ∈ A := (α (f 0)).2
      have hb_mem : r * αY (f 1) * r⁻¹ ∈ B := conjB (α (f 1)) (α (f 1)).2
      have ha_eq : αY (f 0) = (r * αY (f 1) * r⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hx
      have haB : αY (f 0) ∈ B := by
        rw [ha_eq]
        exact B.inv_mem hb_mem
      have ha_bot : αY (f 0) ∈ A ⊓ B := ⟨ha_mem, haB⟩
      rw [hinf, Subgroup.mem_bot] at ha_bot
      have hb_eq : r * αY (f 1) * r⁻¹ = 1 := by
        rw [ha_bot, one_mul] at hx
        exact hx
      have hf0 : f 0 = 1 := by
        apply α.injective
        rw [map_one]
        exact Subtype.ext ha_bot
      have hf1 : f 1 = 1 := by
        apply α.injective
        rw [map_one]
        apply Subtype.ext
        show (α (f 1) : Y) = 1
        calc (α (f 1) : Y) = r⁻¹ * (r * (α (f 1) : Y) * r⁻¹) * r := by group
          _ = r⁻¹ * 1 * r := by rw [show r * (α (f 1) : Y) * r⁻¹ = 1 from hb_eq]
          _ = 1 := by group
      have hf : f = 1 := by
        funext i
        fin_cases i <;> assumption
      subst hf
      rfl
    · rw [if_neg swap01_ne_one] at hx
      have hggmem : αY (f 0) * (r * αY (f 1) * r⁻¹) ∈ A ⊔ B :=
        Subgroup.mul_mem_sup (α (f 0)).2 (conjB (α (f 1)) (α (f 1)).2)
      have hr_mem : r ∈ A ⊔ B := by
        rw [eq_inv_of_mul_eq_one_right hx]
        exact (A ⊔ B).inv_mem hggmem
      exact absurd hr_mem hrN
  have hinj : Function.Injective F := by
    intro x y hxy
    have h1 : F (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hker (x * y⁻¹) h1)
  have hsurj : Function.Surjective F := by
    intro y
    have hzσ : ∃ z ∈ A ⊔ B, ∃ σ : Equiv.Perm (Fin 2),
        y = z * (if σ = 1 then 1 else r) := by
      by_cases hy : y ∈ A ⊔ B
      · exact ⟨y, hy, 1, by simp⟩
      · refine ⟨y * r, ?_, Equiv.swap 0 1,
          by rw [if_neg swap01_ne_one, mul_assoc, hr, mul_one]⟩
        rw [Subgroup.mul_mem_iff_of_index_two hindex]
        exact ⟨fun hyP => absurd hyP hy, fun hrP => absurd hrP hrN⟩
    obtain ⟨z, hz, σ, hyz⟩ := hzσ
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcommY hz
    let fL0 : L := α.symm ⟨a, ha⟩
    let fL1 : L := α.symm ⟨r * b * r⁻¹, conjA b hb⟩
    let f : Fin 2 → L := fun i => if i = 0 then fL0 else fL1
    have hf0 : f 0 = fL0 := by
      dsimp only [f]
      rw [if_pos rfl]
    have hf1 : f 1 = fL1 := by
      dsimp only [f]
      rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    have hα0 : αY (f 0) = a := by
      rw [hf0, αY_symm]
    have hα1 : r * αY (f 1) * r⁻¹ = b := by
      rw [hf1, αY_symm, conj_sq_swap_one hr]
    refine ⟨⟨f, σ⟩, ?_⟩
    rw [F_apply, hα0, hα1]
    exact hyz.symm
  refine ⟨MulEquiv.ofBijective F ⟨hinj, hsurj⟩, ?_⟩
  change SemidirectProduct.lift g ss hcompat
      (SemidirectProduct.inr (Equiv.swap 0 1)) = r
  rw [SemidirectProduct.lift_inr, ss_apply, if_neg swap01_ne_one]

end CFSG.OddTranspositions.PartThree
