module

public import CFSG.Timmesfeld.ARS.CaseBSlope

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType.Universal Matrix

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

variable (Ψ) in
noncomputable abbrev pi13 [CharP F 2] : G := Ψ (pm (Equiv.swap 1 3))

variable (R Ψ) in
@[expose] noncomputable def xN [Finite F] [CharP F 2] (ι : (Fin 1 → F) → G) (t : F) : G :=
  pi13 Ψ * xU R Ψ ι t * (pi13 Ψ)⁻¹

variable (R Ψ) in
@[expose] noncomputable def xN' [Finite F] [CharP F 2] (ι : (Fin 1 → F) → G) (t : F) : G :=
  pi13 Ψ * xU' R Ψ ι t * (pi13 Ψ)⁻¹

section Pi

variable [CharP F 2]

theorem pi13_inv : (pi13 Ψ)⁻¹ = pi13 Ψ := inv_eq_of_mul_eq_one_left pm13_mul_self

theorem pi13_conj_xs {i j : Fin 4} (hij : i ≠ j) (s : F) :
    pi13 Ψ * xs Ψ hij s * (pi13 Ψ)⁻¹ = xs Ψ ((Equiv.swap 1 3).injective.ne hij) s :=
  pm13_conj_xs hij s

end Pi

section Relations

variable [CharP F 2] [Finite F] (h : Hyp G R) (hS : Skel R Ψ) (hP : PtHyp R Ψ)
  {ι : (Fin 1 → F) → G} (hι : LinParamU R Ψ 1 ι)
include h hS hP hι

omit hP in
theorem xN_eq_Lc (t : F) : xN R Ψ ι t = Lc R Ψ (xU R Ψ ι t) :=
  (Lc_eq_conj_pm13 h hS (xU_mem hι t)).symm

omit hP in
theorem xN_mem (t : F) : xN R Ψ ι t ∈ hid R Ψ := by
  rw [xN_eq_Lc h hS hι]
  exact Lc_mem h hS (xU_mem hι t)

omit h hS hP in
theorem xN_add (s t : F) : xN R Ψ ι (s + t) = xN R Ψ ι s * xN R Ψ ι t := by
  rw [xN, xN, xN, xU_add hι]
  group

omit h hS hP in
theorem xN'_add (s t : F) : xN' R Ψ ι (s + t) = xN' R Ψ ι s * xN' R Ψ ι t := by
  rw [xN', xN', xN', xU'_add hι]
  group

theorem commutator_13_xU (s t : F) :
    ⁅xs Ψ ne13 s, xU R Ψ ι t⁆ = xs Ψ ne02 (s * t) * xN R Ψ ι (s ^ 2 * t) := by
  rw [commutator_xs13_xU h hS hι hP, xN_eq_Lc h hS hι]

omit [CharP F 2] [Finite F] h hS hP hι in
theorem commute_13_02 (s t : F) : Commute (xs Ψ ne13 s) (xs Ψ ne02 t) :=
  commuting_xg (Ψ := Ψ) ne13 ne02 (by decide) (by decide) _ (xs_mem _ _) _ (xs_mem _ _)

omit hP in
theorem commute_13_xN (s t : F) : Commute (xs Ψ ne13 s) (xN R Ψ ι t) :=
  (commuting_hid_13 h hS _ (xN_mem h hS hι t) _ (xs_mem _ _)).symm

omit hP in
theorem commute_xU_02 (s t : F) : Commute (xU R Ψ ι s) (xs Ψ ne02 t) :=
  commute_of_mem_hU_of_mem_02 h hS (xU_mem hι s) (xs_mem _ _)

omit hP in
theorem commute_xU_xN (s t : F) : Commute (xU R Ψ ι s) (xN R Ψ ι t) := by
  rw [xN_eq_Lc h hS hι]
  exact commute_xU_Lc h hS hι s t

omit hP in
theorem commute_02_xN (s t : F) : Commute (xs Ψ ne02 s) (xN R Ψ ι t) :=
  (commuting_hid_02 h hS _ (xN_mem h hS hι t) _ (xs_mem _ _)).symm

omit h hS hP hι in
theorem pi13_conj_xU (t : F) : pi13 Ψ * xU R Ψ ι t * (pi13 Ψ)⁻¹ = xN R Ψ ι t := rfl

omit h hS hP hι in
theorem pi13_conj_xN (t : F) : pi13 Ψ * xN R Ψ ι t * (pi13 Ψ)⁻¹ = xU R Ψ ι t := by
  rw [xN, pi13_inv]
  calc pi13 Ψ * (pi13 Ψ * xU R Ψ ι t * pi13 Ψ) * pi13 Ψ =
      (pi13 Ψ * pi13 Ψ) * xU R Ψ ι t * (pi13 Ψ * pi13 Ψ) := by group
    _ = xU R Ψ ι t := by rw [pm13_mul_self]; group

omit h hS hP hι in
theorem pi13_conj_xU' (t : F) : pi13 Ψ * xU' R Ψ ι t * (pi13 Ψ)⁻¹ = xN' R Ψ ι t := rfl

omit h hS hP hι in
theorem pi13_conj_xN' (t : F) : pi13 Ψ * xN' R Ψ ι t * (pi13 Ψ)⁻¹ = xU' R Ψ ι t := by
  rw [xN', pi13_inv]
  calc pi13 Ψ * (pi13 Ψ * xU' R Ψ ι t * pi13 Ψ) * pi13 Ψ =
      (pi13 Ψ * pi13 Ψ) * xU' R Ψ ι t * (pi13 Ψ * pi13 Ψ) := by group
    _ = xU' R Ψ ι t := by rw [pm13_mul_self]; group

omit h hS hP hι in
theorem piT_conj_xU (t : F) : piT Ψ * xU R Ψ ι t * (piT Ψ)⁻¹ = xU' R Ψ ι t := rfl

omit h hS hP hι in
theorem piT_conj_xU' (t : F) : piT Ψ * xU' R Ψ ι t * (piT Ψ)⁻¹ = xU R Ψ ι t := by
  rw [xU', piT_inv]
  calc piT Ψ * (piT Ψ * xU R Ψ ι t * piT Ψ) * piT Ψ =
      (piT Ψ * piT Ψ) * xU R Ψ ι t * (piT Ψ * piT Ψ) := by group
    _ = xU R Ψ ι t := by rw [piT_mul_self]; group

omit hP in
theorem piT_conj_xN (t : F) : piT Ψ * xN R Ψ ι t * (piT Ψ)⁻¹ = xN R Ψ ι t :=
  piT_conj_hid h hS (xN_mem h hS hι t)

omit hP in
theorem pmT₀_conj_xU' (t : F) :
    Ψ (pm σT₀) * xU' R Ψ ι t * (Ψ (pm σT₀))⁻¹ = xU' R Ψ ι t := by
  have hST := hS.perm σT
  have hu := xU'_mem h hι t
  have hc : ∀ {a b : Fin 4} (hab : a ≠ b), (a = 0 ∨ a = 3 ∨ b = 1 ∨ b = 2) →
      Commuting (hU R (perm Ψ σT)) (xg Ψ (σT a) (σT b)) := fun {a b} hab hcond => by
    rw [← xg_perm]
    exact commuting_hU h hST hab hcond
  have hle : xg Ψ 0 3 ⊔ xg Ψ 3 0 ⊔ (xg Ψ 1 2 ⊔ xg Ψ 2 1) ≤
      Subgroup.centralizer {xU' R Ψ ι t} := by
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_) <;> intro x hx <;>
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact (hc (a := 1) (b := 2) (by decide) (by decide) _ hu x hx).symm
    · exact (hc (a := 2) (b := 1) (by decide) (by decide) _ hu x hx).symm
    · exact (hc (a := 0) (b := 3) (by decide) (by decide) _ hu x hx).symm
    · exact (hc (a := 3) (b := 0) (by decide) (by decide) _ hu x hx).symm
  have hmem : Ψ (pm σT₀) ∈ xg Ψ 0 3 ⊔ xg Ψ 3 0 ⊔ (xg Ψ 1 2 ⊔ xg Ψ 2 1) := by
    rw [← pm_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (pm_swap_mem_sup ne03))
      (Subgroup.mem_sup_right (pm_swap_mem_sup ne12))
  rw [Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)]
  group

omit hP in
theorem piT_conj_xN' (t : F) : piT Ψ * xN' R Ψ ι t * (piT Ψ)⁻¹ = xN' R Ψ ι t := by
  have e : piT Ψ * pi13 Ψ = pi13 Ψ * Ψ (pm σT₀) := by
    rw [← map_mul, ← map_mul, pm_mul, pm_mul]
    congr 2
    decide
  rw [xN']
  calc piT Ψ * (pi13 Ψ * xU' R Ψ ι t * (pi13 Ψ)⁻¹) * (piT Ψ)⁻¹ =
      (piT Ψ * pi13 Ψ) * xU' R Ψ ι t * (piT Ψ * pi13 Ψ)⁻¹ := by group
    _ = pi13 Ψ * (Ψ (pm σT₀) * xU' R Ψ ι t * (Ψ (pm σT₀))⁻¹) * (pi13 Ψ)⁻¹ := by
        rw [e]
        group
    _ = pi13 Ψ * xU' R Ψ ι t * (pi13 Ψ)⁻¹ := by rw [pmT₀_conj_xU' h hS hι t]

end Relations

end CaseB

end CFSG.Timmesfeld.ARS
