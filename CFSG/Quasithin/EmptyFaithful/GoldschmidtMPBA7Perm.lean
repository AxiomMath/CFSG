module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Perm
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations

public section

set_option maxRecDepth 100000

namespace CFSG.Quasithin.C58NS.MPB

open Equiv CFSG.QuasithinUnique.L246A7

local notation "A₇" => alternatingGroup (Fin 7)

theorem exists_perm_of_endo {Λ : Type*} [Group Λ] (α : Λ →* A₇) (hα : Function.Surjective α)
    (τ : Λ →* Λ) (hτ : Function.Surjective τ) (hk : ∀ x ∈ α.ker, τ x ∈ α.ker) :
    ∃ π : Perm (Fin 7), ∀ l : Λ,
      ((α (τ l) : A₇) : Perm (Fin 7)) = π * (α l : Perm (Fin 7)) * π⁻¹ := by
  let σ₀ : A₇ →* A₇ :=
    α.liftOfRightInverse (Function.surjInv hα) (Function.rightInverse_surjInv hα)
      ⟨α.comp τ, fun x hx => MonoidHom.mem_ker.mpr (hk x hx)⟩
  have hσ₀ : ∀ l, σ₀ (α l) = α (τ l) := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ l
  have hsurj : Function.Surjective σ₀ := fun y => by
    obtain ⟨l, hl⟩ := hα.comp hτ y
    exact ⟨α l, by rw [hσ₀]; exact hl⟩
  have hinj : Function.Injective σ₀ := Finite.injective_iff_surjective.2 hsurj
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 (MulEquiv.ofBijective σ₀ ⟨hinj, hsurj⟩)
  refine ⟨π, fun l => ?_⟩
  have h := congrArg (fun φ : MulAut A₇ => ((φ (α l) : A₇) : Perm (Fin 7))) hπ
  simp only [MulAut.conjNormal_apply] at h
  rw [← hσ₀ l]
  exact h.symm

@[expose] def PB : Subgroup (Perm (Fin 7)) where
  carrier := {a | ∀ i : Fin 7, 4 ≤ i.val ↔ 4 ≤ (a i).val}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb i => by
    rw [hb i]
    exact ha (b i)
  inv_mem' := fun {a} ha i => by
    have h := ha (a⁻¹ i)
    simpa using h.symm

@[expose] def Y2 : Subgroup A₇ := PB.subgroupOf A₇

@[expose] def Y1 : Subgroup A₇ := S6A

theorem mem_Y1 {a : A₇} : a ∈ Y1 ↔ (a : Perm (Fin 7)) 6 = 6 := Iff.rfl

theorem pres_mem_PB : ∀ π : Perm (Fin 7), π 6 = 6 → ((π 4 = 4 ∧ π 5 = 5) ∨ (π 4 = 5 ∧ π 5 = 4)) →
    ∀ i : Fin 7, (4 ≤ i.val ↔ 4 ≤ (π i).val) := by decide +kernel

theorem g1_mem_PB : g1 ∈ PB := by
  intro i
  revert i
  decide +kernel

theorem g2_mem_PB : g2 ∈ PB := by
  intro i
  revert i
  decide +kernel

theorem cc_mem_PB : cc ∈ PB := by
  intro i
  revert i
  decide +kernel

theorem Pstd_le_PB : Pstd ≤ PB :=
  sup_le (Subgroup.zpowers_le.2 g1_mem_PB) (Subgroup.zpowers_le.2 g2_mem_PB)

theorem P0_le_Y1 : Pstd.subgroupOf A₇ ≤ Y1 := fun _ hx => Pstd_le_S6 hx

theorem P0_le_Y2 : Pstd.subgroupOf A₇ ≤ Y2 := fun _ hx => Pstd_le_PB hx

theorem conj_mem_Y1 {π : Perm (Fin 7)} (h6 : π 6 = 6) {a : Perm (Fin 7)} (ha : a ∈ S6) :
    π * a * π⁻¹ ∈ S6 :=
  S6.mul_mem (S6.mul_mem (show π ∈ S6 from h6) ha) (S6.inv_mem (show π ∈ S6 from h6))

theorem conj_mem_Y2 {π : Perm (Fin 7)} (h6 : π 6 = 6)
    (h45 : (π 4 = 4 ∧ π 5 = 5) ∨ (π 4 = 5 ∧ π 5 = 4)) {a : Perm (Fin 7)} (ha : a ∈ PB) :
    π * a * π⁻¹ ∈ PB := by
  have hπ : π ∈ PB := pres_mem_PB π h6 h45
  exact PB.mul_mem (PB.mul_mem hπ ha) (PB.inv_mem hπ)

theorem ccA_mem_Y2 : ccA ∈ Y2 := cc_mem_PB

theorem Y1_sup_Y2 : Y1 ⊔ Y2 = ⊤ :=
  eq_top_iff.2 (S6A_sup_zpowers_ccA ▸ sup_le_sup_left (Subgroup.zpowers_le.2 ccA_mem_Y2) _)

theorem Y1_ne_top : Y1 ≠ ⊤ := fun h => by
  have : ccA ∈ Y1 := h ▸ Subgroup.mem_top _
  have h6 : cc 6 = 6 := this
  rw [cc_apply6] at h6
  exact absurd h6 (by decide)

@[expose] def tc : Perm (Fin 7) := c[3, 4, 0]

theorem tc_sign : Perm.sign tc = 1 := by decide +kernel

theorem Y2_ne_top : Y2 ≠ ⊤ := fun h => by
  have h1 : (⟨tc, Perm.mem_alternatingGroup.2 tc_sign⟩ : A₇) ∈ Y2 := h ▸ Subgroup.mem_top _
  have h2 : ∀ i : Fin 7, 4 ≤ i.val ↔ 4 ≤ (tc i).val := h1
  have h3 := h2 3
  revert h3
  decide +kernel

end CFSG.Quasithin.C58NS.MPB
