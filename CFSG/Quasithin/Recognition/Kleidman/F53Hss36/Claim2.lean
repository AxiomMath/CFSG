module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.VecStab
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Defs

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem Wnn_le_Qv_of_Zv_le (hZ : Zv α' ≤ Vn β) {ℓ δ : Geo H M} (hℓ : ℓ ∈ nbrs α')
    (hδ : δ ∈ nbrs ℓ) (hne : δ ≠ α') (hd : dist β δ + 3 ≤ bMin H M) : Wnn β ≤ Qv ℓ := by
  have hvℓ : vtype ℓ = true := vtype_true_of_mem_nbrs_false hℓ C.vtype_alpha'
  have hvδ : vtype δ = false := vtype_false_of_mem_nbrs_true hδ hvℓ
  have hℓδ : ℓ ∈ nbrs δ := mem_nbrs_comm hδ
  have hα'ℓ : α' ∈ nbrs ℓ := mem_nbrs_comm hℓ
  have hWδ : Wnn β ≤ stab δ := C.Wnn_le_stab_of_dist C.vtype_beta (by omega)
  have hWc : Wnn β ≤ Subgroup.centralizer (Zv α' : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (C.Wnn_le_centralizer_Vn C.vtype_beta hx) y
      (hZ hy)
  obtain ⟨hzmem, hz1, hzonly⟩ := C.zgen_spec' C.vtype_alpha'
  set z := zgen α' with hzdef
  have hzℓ : z ∈ Zv ℓ := C.Zv_le_Zv_of_mem_nbrs hvℓ hα'ℓ hzmem
  have hzC : z ∉ F53B3.Cv δ := by
    intro hzC
    have hzδ : z ∈ Zv δ := by
      rw [← C.Zv_inf_Cv_eq hvδ hℓδ]; exact ⟨hzℓ, hzC⟩
    obtain ⟨hδm, hδ1, hδonly⟩ := C.zgen_spec' hvδ
    have e1 : z = zgen δ := (hδonly z hzδ).resolve_left hz1
    apply C.Zv_ne_of_mem_nbrs hvℓ hδ hα'ℓ hne
    ext x
    constructor
    · intro hx
      rcases hδonly x hx with h | h
      · rw [h]; exact one_mem _
      · rw [h, ← e1]; exact hzmem
    · intro hx
      rcases hzonly x hx with h | h
      · rw [h]; exact one_mem _
      · rw [h, e1]; exact hδm
  have hWℓ : Wnn β ≤ stab ℓ := fun x hx =>
    C.mem_stab_of_comm_mem_Cv hvδ hℓδ hzℓ hzC (hWδ hx) (by
      have h1 : x * z = z * x := ((Subgroup.mem_centralizer_iff.mp (hWc hx)) z hzmem).symm
      rw [h1]; simp)
  have hsup := (C.Zv_sup_eq_and_inf_eq_bot hvℓ hδ hα'ℓ hne).1
  have hWcℓ : Wnn β ≤ Subgroup.centralizer (Zv ℓ : Set G) := by
    have hZℓle : Zv ℓ ≤ Subgroup.centralizer (Wnn β : Set G) := by
      rw [← hsup]
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact Subgroup.mem_centralizer_iff.mp
          (C.Zv_le_center hvδ hy).2 x (hWδ hx)
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_centralizer_iff.mp (hWc hx) y hy).symm
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hZℓle hy) x hx).symm
  rw [← CFSG.Quasithin.F53.centralizer_Zv_eq_Qv_of_bAt C.hA (C.bAt_eq_of_true hvℓ)]
  exact le_inf hWℓ hWcℓ

theorem claim2 (P : CritPath α β α') (hZ : Zv α' ≤ Vn β) : Wnn β ≤ Qv (P.p (bMin H M - 1)) := by
  have hb := C.hb5
  have hg := P.isGeodesic
  have e1 : P.p (bMin H M - 1) ∈ nbrs α' := by
    have := hg.mem_nbrs_pred (i := bMin H M - 1) (by omega)
    rwa [show bMin H M - 1 + 1 = bMin H M by omega, P.p_b] at this
  have e2 : P.p (bMin H M - 2) ∈ nbrs (P.p (bMin H M - 1)) := by
    have := hg.mem_nbrs_pred (i := bMin H M - 2) (by omega)
    rwa [show bMin H M - 2 + 1 = bMin H M - 1 by omega] at this
  have e3 : P.p (bMin H M - 2) ≠ α' := by
    intro h
    have := hg.dist_of_le (i := bMin H M - 2) (j := bMin H M) (by omega) le_rfl
    rw [h, P.p_b, CosetGeom.dist_self] at this
    omega
  have e4 : dist β (P.p (bMin H M - 2)) + 3 ≤ bMin H M := by
    have := hg.dist_of_le (i := 1) (j := bMin H M - 2) (by omega) (by omega)
    rw [P.p_one] at this
    omega
  exact C.Wnn_le_Qv_of_Zv_le hZ e1 e2 e3 e4

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
