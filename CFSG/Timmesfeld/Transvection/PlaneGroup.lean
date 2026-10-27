module

public import CFSG.Timmesfeld.Transvection.FrameBasic

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

@[expose] def planeOf (Δ : Set (Subgroup G)) (A B C : Subgroup G) : Set (Subgroup G) :=
  {D | D ∈ Δ ∧ ∀ X ∈ Δ, Commuting X A → Commuting X B → Commuting X C → Commuting X D}

@[expose] def planeGroup (Δ : Set (Subgroup G)) (A B C : Subgroup G) : Subgroup G :=
  ⨆ D ∈ planeOf Δ A B C, D

variable {A B C D : Subgroup G}

theorem left_mem_planeOf (hA : A ∈ Δ) : A ∈ planeOf Δ A B C :=
  ⟨hA, fun _ _ h _ _ => h⟩

theorem mid_mem_planeOf (hB : B ∈ Δ) : B ∈ planeOf Δ A B C :=
  ⟨hB, fun _ _ _ h _ => h⟩

theorem right_mem_planeOf (hC : C ∈ Δ) : C ∈ planeOf Δ A B C :=
  ⟨hC, fun _ _ _ _ h => h⟩

theorem le_planeGroup (hD : D ∈ planeOf Δ A B C) : D ≤ planeGroup Δ A B C :=
  le_iSup₂_of_le D hD le_rfl

theorem lineOf_subset_planeOf {D' : Subgroup G} (hD : D ∈ planeOf Δ A B C)
    (hD' : D' ∈ planeOf Δ A B C) : lineOf Δ D D' ⊆ planeOf Δ A B C :=
  fun _ hE => ⟨hE.1, fun X hX hXA hXB hXC =>
    hE.2 X hX (hD.2 X hX hXA hXB hXC) (hD'.2 X hX hXA hXB hXC)⟩

theorem lineGroup_le_planeGroup {D D' : Subgroup G} (hD : D ∈ planeOf Δ A B C)
    (hD' : D' ∈ planeOf Δ A B C) : (⨆ E ∈ lineOf Δ D D', E) ≤ planeGroup Δ A B C :=
  iSup₂_le fun _ hE => le_planeGroup (lineOf_subset_planeOf hD hD' hE)

theorem planeOf_subset_of_mem {A' B' C' : Subgroup G} (hA' : A' ∈ planeOf Δ A B C)
    (hB' : B' ∈ planeOf Δ A B C) (hC' : C' ∈ planeOf Δ A B C) :
    planeOf Δ A' B' C' ⊆ planeOf Δ A B C :=
  fun _ hE => ⟨hE.1, fun X hX hXA hXB hXC =>
    hE.2 X hX (hA'.2 X hX hXA hXB hXC) (hB'.2 X hX hXA hXB hXC) (hC'.2 X hX hXA hXB hXC)⟩

section Commuting

variable (hΔ : IsRootClass Δ) (hA : A ∈ Δ) (hB : B ∈ Δ) (hC : C ∈ Δ) (hAB : Commuting A B)
  (hAC : Commuting A C) (hBC : Commuting B C)
include hΔ hA hB hC hAB hAC hBC

theorem commuting_left_mid_right_of_mem_planeOf (hD : D ∈ planeOf Δ A B C) :
    Commuting D A ∧ Commuting D B ∧ Commuting D C :=
  ⟨(hD.2 A hA (hΔ.commuting_self hA) hAB hAC).symm,
    (hD.2 B hB hAB.symm (hΔ.commuting_self hB) hBC).symm,
    (hD.2 C hC hAC.symm hBC.symm (hΔ.commuting_self hC)).symm⟩

theorem commuting_of_mem_planeOf {D' : Subgroup G} (hD : D ∈ planeOf Δ A B C)
    (hD' : D' ∈ planeOf Δ A B C) : Commuting D D' := by
  obtain ⟨h1, h2, h3⟩ := commuting_left_mid_right_of_mem_planeOf hΔ hA hB hC hAB hAC hBC hD
  exact hD'.2 D hD.1 h1 h2 h3

theorem commute_of_mem_planeGroup {x y : G} (hx : x ∈ planeGroup Δ A B C)
    (hy : y ∈ planeGroup Δ A B C) : Commute x y := by
  have h1 : ∀ D' ∈ planeOf Δ A B C, Commuting D' (planeGroup Δ A B C) := fun D' hD' =>
    commuting_iff_le_centralizer.2 (iSup₂_le fun D hD => commuting_iff_le_centralizer.1
      (commuting_of_mem_planeOf hΔ hA hB hC hAB hAC hBC hD' hD))
  have h2 : Commuting (planeGroup Δ A B C) (planeGroup Δ A B C) :=
    commuting_iff_le_centralizer.2 (iSup₂_le fun D' hD' =>
      commuting_iff_le_centralizer.1 (h1 D' hD').symm)
  exact h2 x hx y hy

theorem mul_self_of_mem_planeGroup {x : G} (hx : x ∈ planeGroup Δ A B C) : x * x = 1 := by
  let H : Subgroup G :=
    { carrier := {x | x ∈ planeGroup Δ A B C ∧ x * x = 1}
      mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by
              rw [(commute_of_mem_planeGroup hΔ hA hB hC hAB hAC hBC hy.1 hx.1).eq]
          _ = x * x * (y * y) := by group
          _ = 1 := by rw [hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨Subgroup.one_mem _, mul_one 1⟩
      inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by rw [← mul_inv_rev, hx.2, inv_one]⟩ }
  have hle : planeGroup Δ A B C ≤ H := iSup₂_le fun D hD y hy =>
    ⟨le_planeGroup hD hy, hΔ.mul_self D hD.1 y hy⟩
  exact (hle hx).2

end Commuting

theorem conjSub_mem_planeOf (hΔ : IsRootClass Δ) (hD : D ∈ planeOf Δ A B C) (g : G) :
    conjSub D g ∈ planeOf Δ (conjSub A g) (conjSub B g) (conjSub C g) := by
  refine ⟨hΔ.conjSub_mem hD.1 g, fun X hX hXA hXB hXC => ?_⟩
  have hY : conjSub (conjSub X g⁻¹) g = X := by
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  rw [← hY] at hXA hXB hXC ⊢
  rw [Aux.commuting_conjSub_iff] at hXA hXB hXC ⊢
  exact hD.2 _ (hΔ.conjSub_mem hX g⁻¹) hXA hXB hXC

theorem image_conjSub_planeOf (hΔ : IsRootClass Δ) (g : G) :
    (fun D => conjSub D g) '' planeOf Δ A B C =
      planeOf Δ (conjSub A g) (conjSub B g) (conjSub C g) := by
  refine Set.Subset.antisymm ?_ fun E hE => ?_
  · rintro _ ⟨D, hD, rfl⟩
    exact conjSub_mem_planeOf hΔ hD g
  · have h := conjSub_mem_planeOf hΔ hE g⁻¹
    simp only [Aux.conjSub_conjSub_inv] at h
    refine ⟨conjSub E g⁻¹, h, ?_⟩
    simp only [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_iSup_mem (𝒮 : Set (Subgroup G)) (g : G) :
    conjSub (⨆ D ∈ 𝒮, D) g = ⨆ E ∈ (fun D => conjSub D g) '' 𝒮, E := by
  rw [iSup_image]
  simp only [conjSub, Subgroup.map_iSup]

section Normalize

variable [Finite G]

theorem image_conjSub_planeOf_eq (hΔ : IsRootClass Δ) {y : G}
    (hA : conjSub A y ∈ planeOf Δ A B C) (hB : conjSub B y ∈ planeOf Δ A B C)
    (hC : conjSub C y ∈ planeOf Δ A B C) :
    (fun D => conjSub D y) '' planeOf Δ A B C = planeOf Δ A B C := by
  have hsub : (fun D => conjSub D y) '' planeOf Δ A B C ⊆ planeOf Δ A B C := by
    rw [image_conjSub_planeOf hΔ y]
    exact planeOf_subset_of_mem hA hB hC
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ (conjSub_injective y)]

theorem conjSub_planeGroup_eq (hΔ : IsRootClass Δ) {y : G}
    (hA : conjSub A y ∈ planeOf Δ A B C) (hB : conjSub B y ∈ planeOf Δ A B C)
    (hC : conjSub C y ∈ planeOf Δ A B C) :
    conjSub (planeGroup Δ A B C) y = planeGroup Δ A B C := by
  rw [planeGroup, conjSub_iSup_mem, image_conjSub_planeOf_eq hΔ hA hB hC]

theorem conjSub_planeGroup_eq_of_fix (hΔ : IsRootClass Δ) (hA : A ∈ Δ) (hC : C ∈ Δ) {y : G}
    (hyA : conjSub A y = A) (hyC : conjSub C y = C) (hB : conjSub B y ∈ planeOf Δ A B C) :
    conjSub (planeGroup Δ A B C) y = planeGroup Δ A B C :=
  conjSub_planeGroup_eq hΔ (by rw [hyA]; exact left_mem_planeOf hA) hB
    (by rw [hyC]; exact right_mem_planeOf hC)

end Normalize

section Trace

variable [Finite G] (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ) (hml : MeetsLines Δ)
include hΔ hpts hml

theorem mem_lineOf_of_mem_planeOf {A' B' C' : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hC : C ∈ Δ) (hA' : A' ∈ Δ) (hB' : B' ∈ Δ) (hC' : C' ∈ Δ) (hAB : Commuting A B)
    (hAC : Commuting A C) (hBC : Commuting B C) (hAC' : A ≠ C) (hA'C : Commuting A' C)
    (hB'A : Commuting B' A) (hB'C : Commuting B' C)
    (hres : ∀ X ∈ planeOf Δ A B C, Commuting X A' → Commuting X B' → Commuting X C' → False)
    (hD : D ∈ planeOf Δ A B C) (hDB' : Commuting D B') : D ∈ lineOf Δ A C := by
  by_contra hDl
  have hAπ : A ∈ planeOf Δ A B C := left_mem_planeOf hA
  have hCπ : C ∈ planeOf Δ A B C := right_mem_planeOf hC
  have hcomm := fun {E E' : Subgroup G} (hE : E ∈ planeOf Δ A B C)
    (hE' : E' ∈ planeOf Δ A B C) => commuting_of_mem_planeOf hΔ.root hA hB hC hAB hAC hBC hE hE'
  have hAD : A ≠ D := fun h => hDl (h ▸ left_mem_lineOf hA)
  obtain ⟨D₁, hD₁, hA'D₁⟩ := hml A hA D hD.1 hAD (hcomm hAπ hD) A' hA'
  have hD₁π : D₁ ∈ planeOf Δ A B C := lineOf_subset_planeOf hAπ hD hD₁
  have hD₁C : D₁ ≠ C := by
    rintro rfl
    have h := lineOf_eq_of_mem_of_ne hΔ hpts hA hD.1 hAD (hcomm hAπ hD) hD₁ (Ne.symm hAC')
    exact hDl (h ▸ right_mem_lineOf hD.1)
  obtain ⟨D₂, hD₂, hC'D₂⟩ := hml D₁ hD₁.1 C hC hD₁C (hcomm hD₁π hCπ) C' hC'
  have hD₂π : D₂ ∈ planeOf Δ A B C := lineOf_subset_planeOf hD₁π hCπ hD₂
  have hB'D₁ : Commuting B' D₁ := hD₁.2 B' hB' hB'A hDB'.symm
  exact hres D₂ hD₂π (hD₂.2 A' hA' hA'D₁ hA'C).symm (hD₂.2 B' hB' hB'D₁ hB'C).symm hC'D₂.symm

end Trace

namespace IsFrame

variable {r : ℕ} {P Q : Fin r → Subgroup G}

variable (hF : IsFrame Δ P Q)
  (hmax : ∀ X ∈ Δ, ¬ ∀ l, Commuting X (P l) ∧ Commuting X (Q l))
  [Finite G] (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
  (hml : MeetsLines Δ) {i j k : Fin r} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
include hF hmax hΔ hpts hml hij hik hjk

theorem mem_lineOf_of_mem_planeOf {D : Subgroup G} (hD : D ∈ planeOf Δ (Q i) (P j) (P k))
    (hDQ : Commuting D (Q j)) : D ∈ lineOf Δ (Q i) (P k) := by
  refine Transvection.mem_lineOf_of_mem_planeOf hΔ hpts hml (hF.memQ i) (hF.memP j) (hF.memP k)
    (hF.memP i) (hF.memQ j) (hF.memQ k) (hF.commuting_QP hij) (hF.commuting_QP hik)
    (hF.commuting_PP hjk) (hF.Q_ne_P hik) (hF.commuting_PP hik) (hF.commuting_QQ hij.symm)
    (hF.commuting_QP hjk) (fun X hX hXP hXQ hXQ' => ?_) hD hDQ
  obtain ⟨h1, h2, h3⟩ := commuting_left_mid_right_of_mem_planeOf hΔ.root (hF.memQ i)
    (hF.memP j) (hF.memP k) (hF.commuting_QP hij) (hF.commuting_QP hik) (hF.commuting_PP hjk) hX
  refine hmax X hX.1 fun l => ?_
  by_cases hli : l = i
  · subst hli
    exact ⟨hXP, h1⟩
  by_cases hlj : l = j
  · subst hlj
    exact ⟨h2, hXQ⟩
  by_cases hlk : l = k
  · subst hlk
    exact ⟨h3, hXQ'⟩
  exact ⟨(hX.2 (P l) (hF.memP l) (hF.commuting_PQ hli) (hF.commuting_PP hlj)
      (hF.commuting_PP hlk)).symm,
    (hX.2 (Q l) (hF.memQ l) (hF.commuting_QQ hli) (hF.commuting_QP hlj)
      (hF.commuting_QP hlk)).symm⟩

end IsFrame

end CFSG.Timmesfeld.Transvection
