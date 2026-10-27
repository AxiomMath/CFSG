module

public import CFSG.Timmesfeld.Transvection.LineSpan

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

@[expose] def lineGroup (Δ : Set (Subgroup G)) (A B : Subgroup G) : Subgroup G :=
  ⨆ C ∈ lineOf Δ A B, C

@[expose] def lineStab (Δ : Set (Subgroup G)) (A B : Subgroup G) : Subgroup G where
  carrier := {g | ∀ C : Subgroup G, conjSub C g ∈ lineOf Δ A B ↔ C ∈ lineOf Δ A B}
  mul_mem' {g h} hg hh C := by
    rw [conjSub_mul]
    exact (hg _).trans (hh C)
  one_mem' C := by rw [conjSub_one]
  inv_mem' {g} hg C := by
    have := hg (conjSub C g⁻¹)
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at this
    exact this.symm

@[expose] def shortRootGroup (Δ : Set (Subgroup G)) (P Q P' Q' : Subgroup G) : Subgroup G :=
  lineGroup Δ P P' ⊓ lineStab Δ Q P' ⊓ lineStab Δ P Q'

theorem mem_lineStab_iff {A B : Subgroup G} {g : G} :
    g ∈ lineStab Δ A B ↔ ∀ C : Subgroup G, conjSub C g ∈ lineOf Δ A B ↔ C ∈ lineOf Δ A B :=
  Iff.rfl

theorem le_lineGroup {A B C : Subgroup G} (hC : C ∈ lineOf Δ A B) : C ≤ lineGroup Δ A B :=
  le_iSup₂_of_le C hC le_rfl

theorem lineOf_comm (A B : Subgroup G) : lineOf Δ A B = lineOf Δ B A := by
  ext D
  simp only [lineOf, Set.mem_ofPred_eq]
  exact and_congr_right fun _ => forall₂_congr fun _ _ => forall_comm

theorem lineGroup_comm (A B : Subgroup G) : lineGroup Δ A B = lineGroup Δ B A := by
  rw [lineGroup, lineGroup, lineOf_comm]

theorem lineStab_comm (A B : Subgroup G) : lineStab Δ A B = lineStab Δ B A := by
  ext g
  rw [mem_lineStab_iff, mem_lineStab_iff, lineOf_comm]

section Abelian

variable (hΔ : IsTransvectionClass Δ) {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
  (hAB : Commuting A B)
include hΔ hA hB hAB

theorem commuting_of_mem_lineOf_of_mem_lineOf {C C' : Subgroup G} (hC : C ∈ lineOf Δ A B)
    (hC' : C' ∈ lineOf Δ A B) : Commuting C C' := by
  obtain ⟨hAC, hBC⟩ := commuting_of_mem_lineOf' hΔ hA hB hAB hC
  exact hC'.2 C hC.1 hAC.symm hBC.symm

theorem commute_of_mem_lineGroup {x y : G} (hx : x ∈ lineGroup Δ A B)
    (hy : y ∈ lineGroup Δ A B) : Commute x y := by
  have hle : lineGroup Δ A B ≤ Subgroup.centralizer (lineGroup Δ A B : Set G) := by
    refine iSup₂_le fun C hC => ?_
    refine commuting_iff_le_centralizer.1 (Commuting.symm ?_)
    exact commuting_iff_le_centralizer.2 (iSup₂_le fun C' hC' => commuting_iff_le_centralizer.1
      (commuting_of_mem_lineOf_of_mem_lineOf hΔ hA hB hAB hC hC'))
  exact Subgroup.mem_centralizer_iff.1 (hle hy) x hx

theorem mul_self_of_mem_lineGroup {x : G} (hx : x ∈ lineGroup Δ A B) : x * x = 1 := by
  let H : Subgroup G :=
    { carrier := {x | x ∈ lineGroup Δ A B ∧ x * x = 1}
      mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, by
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by
              rw [(commute_of_mem_lineGroup hΔ hA hB hAB hy.1 hx.1).eq]
          _ = x * x * (y * y) := by group
          _ = 1 := by rw [hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨Subgroup.one_mem _, mul_one 1⟩
      inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by rw [← mul_inv_rev, hx.2, inv_one]⟩ }
  have hle : lineGroup Δ A B ≤ H := iSup₂_le fun C hC y hy =>
    ⟨le_lineGroup hC hy, hΔ.root.mul_self C hC.1 y hy⟩
  exact (hle hx).2

theorem conjSub_eq_of_le_lineGroup {g : G} (hg : g ∈ lineGroup Δ A B) {C : Subgroup G}
    (hC : C ≤ lineGroup Δ A B) : conjSub C g = C :=
  conjSub_of_forall_commute fun _ hc => commute_of_mem_lineGroup hΔ hA hB hAB hg (hC hc)

theorem lineGroup_le_lineStab : lineGroup Δ A B ≤ lineStab Δ A B := by
  intro g hg C
  constructor
  · intro hCg
    have h1 := conjSub_eq_of_le_lineGroup hΔ hA hB hAB (Subgroup.inv_mem _ hg)
      (le_lineGroup hCg)
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at h1
    rw [h1]
    exact hCg
  · intro hC
    rw [conjSub_eq_of_le_lineGroup hΔ hA hB hAB hg (le_lineGroup hC)]
    exact hC

end Abelian

theorem mem_lineStab_of_mapsTo [Finite G] {A B : Subgroup G} {g : G}
    (h : ∀ C ∈ lineOf Δ A B, conjSub C g ∈ lineOf Δ A B) : g ∈ lineStab Δ A B := by
  intro C
  refine ⟨fun hC => ?_, fun hC => h C hC⟩
  let f : lineOf Δ A B → lineOf Δ A B := fun D => ⟨conjSub D.1 g, h D.1 D.2⟩
  have hf : Function.Injective f := fun D D' hDD' =>
    Subtype.ext (conjSub_injective g (congrArg Subtype.val hDD'))
  obtain ⟨D, hD⟩ := (Finite.injective_iff_surjective.1 hf) ⟨conjSub C g, hC⟩
  have hDC : D.1 = C := conjSub_injective g (congrArg Subtype.val hD)
  exact hDC ▸ D.2

section Conj

variable (hR : IsRootClass Δ)
include hR

theorem conjSub_mem_lineOf_conjSub {A B D : Subgroup G} (hD : D ∈ lineOf Δ A B) (g : G) :
    conjSub D g ∈ lineOf Δ (conjSub A g) (conjSub B g) := by
  refine ⟨hR.conjSub_mem hD.1 g, fun W hW hWA hWB => ?_⟩
  have hW' : conjSub (conjSub W g⁻¹) g = W := by rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  have h1 : Commuting (conjSub W g⁻¹) A := by
    have := hWA.conjSub g⁻¹
    rwa [Aux.conjSub_conjSub_inv] at this
  have h2 : Commuting (conjSub W g⁻¹) B := by
    have := hWB.conjSub g⁻¹
    rwa [Aux.conjSub_conjSub_inv] at this
  have h3 := (hD.2 _ (hR.conjSub_mem hW g⁻¹) h1 h2).conjSub g
  rwa [hW'] at h3

theorem conjSub_mem_lineOf_conjSub_iff {A B D : Subgroup G} (g : G) :
    conjSub D g ∈ lineOf Δ (conjSub A g) (conjSub B g) ↔ D ∈ lineOf Δ A B := by
  refine ⟨fun h => ?_, fun h => conjSub_mem_lineOf_conjSub hR h g⟩
  have := conjSub_mem_lineOf_conjSub hR h g⁻¹
  rwa [Aux.conjSub_conjSub_inv, Aux.conjSub_conjSub_inv, Aux.conjSub_conjSub_inv] at this

theorem mem_lineOf_conjSub_iff {A B C : Subgroup G} (g : G) :
    C ∈ lineOf Δ (conjSub A g) (conjSub B g) ↔ conjSub C g⁻¹ ∈ lineOf Δ A B := by
  have := conjSub_mem_lineOf_conjSub_iff hR (A := A) (B := B) (D := conjSub C g⁻¹) g
  rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this

theorem lineGroup_conjSub (A B : Subgroup G) (g : G) :
    lineGroup Δ (conjSub A g) (conjSub B g) = conjSub (lineGroup Δ A B) g := by
  refine le_antisymm (iSup₂_le fun C hC => ?_) ?_
  · have hC' := (mem_lineOf_conjSub_iff hR g).1 hC
    have : C = conjSub (conjSub C g⁻¹) g := by rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
    rw [this]
    exact Subgroup.map_mono (le_lineGroup hC')
  · refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun C hC => ?_)
    exact Subgroup.map_le_iff_le_comap.1 (le_lineGroup (conjSub_mem_lineOf_conjSub hR hC g))

theorem lineStab_conjSub (A B : Subgroup G) (g : G) :
    lineStab Δ (conjSub A g) (conjSub B g) = conjSub (lineStab Δ A B) g := by
  ext x
  rw [mem_conjSub, mem_lineStab_iff, mem_lineStab_iff]
  constructor
  · intro h C
    have := h (conjSub C g)
    rw [conjSub_mem_lineOf_conjSub_iff hR, ← conjSub_mul,
      show x * g = g * (g⁻¹ * x * g) by group, conjSub_mul,
      conjSub_mem_lineOf_conjSub_iff hR] at this
    exact this
  · intro h C
    rw [mem_lineOf_conjSub_iff hR, mem_lineOf_conjSub_iff hR, ← conjSub_mul,
      show g⁻¹ * x = (g⁻¹ * x * g) * g⁻¹ by group, conjSub_mul]
    exact h _

theorem shortRootGroup_conjSub (P Q P' Q' : Subgroup G) (g : G) :
    shortRootGroup Δ (conjSub P g) (conjSub Q g) (conjSub P' g) (conjSub Q' g) =
      conjSub (shortRootGroup Δ P Q P' Q') g := by
  rw [shortRootGroup, shortRootGroup, lineGroup_conjSub hR, lineStab_conjSub hR,
    lineStab_conjSub hR, conjSub, conjSub, conjSub, conjSub,
    ← Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
    ← Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective]

theorem mem_lineStab_of_commute {A B : Subgroup G} {g : G} (hgA : ∀ a ∈ A, Commute g a)
    (hgB : ∀ b ∈ B, Commute g b) : g ∈ lineStab Δ A B := by
  intro C
  have h := conjSub_mem_lineOf_conjSub_iff hR (A := A) (B := B) (D := C) g
  rwa [conjSub_of_forall_commute hgA, conjSub_of_forall_commute hgB] at h

end Conj

section Endpoint

variable {A B C D : Subgroup G} (hC : C ∈ Δ) (hD : D ∈ Δ) (hAC : Commuting A C)
  (hAD : Commuting A D) (hBC : Commuting B C) (hBD : Commuting B D)
include hC hD hAC hAD hBC hBD

theorem commuting_of_commuting_ends {P Q : Subgroup G} (hP : P ∈ lineOf Δ A B)
    (hQ : Q ∈ lineOf Δ C D) : Commuting P Q :=
  hQ.2 P hP.1 (hP.2 C hC hAC.symm hBC.symm).symm (hP.2 D hD hAD.symm hBD.symm).symm

theorem commuting_lineGroup : Commuting (lineGroup Δ A B) (lineGroup Δ C D) := by
  refine commuting_iff_le_centralizer.2 (iSup₂_le fun Q hQ => ?_)
  refine commuting_iff_le_centralizer.1 (Commuting.symm ?_)
  exact commuting_iff_le_centralizer.2 (iSup₂_le fun P hP => commuting_iff_le_centralizer.1
    (commuting_of_commuting_ends hC hD hAC hAD hBC hBD hP hQ).symm)

end Endpoint

end CFSG.Timmesfeld.Transvection
