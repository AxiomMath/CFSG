module

public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinHeld
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SemisimpleCentralizers.Held

theorem linCentComp_block {N : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (g : GL (Fin N) K) (hg : Odd (orderOf g))
    (C : Subgroup (GL (Fin N) K))
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({g} : Set (GL (Fin N) K))))
    (hCSL : C ≤ LargeEvenSLGroup (Fin N) K)
    (J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K)))
    (hJ : J = (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))) :
    ∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Finite E), 2 ≤ a ∧
      Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL a E)) := by
  classical
  have hord : (orderOf g : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    exact (Nat.not_even_iff_odd.mpr hg) (even_iff_two_dvd.mpr h)
  have hM : CFSG.Open.IsComponentOf C
      (Subgroup.centralizer ({g} : Set (GL (Fin N) K)) ⊓ StatedSL N K) := by
    have hM1 := (CFSG.Assembly.isComponentOf_iff_open).1
      (hC.of_le_of_le (le_inf hC.1 hCSL) inf_le_left)
    rwa [CFSG.Assembly.largeEvenSLGroup_eq_statedSL N] at hM1
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨φ⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.held_linear_components_gl
      SLComponentsTrivial_holds g hord C hM
  have hperf : commutator ↥C = ⊤ := hC.2.2.1
  let πCSL : ↥C →* ↥(LargeEvenSLGroup (Fin N) K) := Subgroup.inclusion hCSL
  let πC : ↥C →* ↥J :=
    { toFun := fun c => ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (πCSL c), by
        rw [hJ]
        exact Subgroup.mem_map.mpr ⟨πCSL c, Subgroup.mem_subgroupOf.mpr c.2, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp }
  have hπC_surj : Function.Surjective πC := by
    rintro ⟨j, hj⟩
    have hj' : j ∈ (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
        (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) := by
      rw [← hJ]; exact hj
    obtain ⟨y, hy, hyj⟩ := Subgroup.mem_map.mp hj'
    refine ⟨⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    change LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)
      (πCSL ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩) = j
    have hpc : πCSL ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩ = y := Subtype.ext rfl
    rw [hpc]
    exact hyj
  have hπC_ker : πC.ker ≤ Subgroup.center ↥C := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hc' : πCSL c ∈ (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker := by
      rw [MonoidHom.mem_ker]
      simpa [πC] using congrArg Subtype.val hc
    have hker : ∀ H : Subgroup (GL (Fin N) K), H = StatedSL N K →
        (LargeEvenProjMk H).ker ≤ Subgroup.center ↥H := by
      rintro H rfl
      exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center
    have hcen := hker _ (CFSG.Assembly.largeEvenSLGroup_eq_statedSL N) hc'
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro d
    apply Subtype.ext
    show (πCSL d : GL (Fin N) K) * (πCSL c : GL (Fin N) K) =
      (πCSL c : GL (Fin N) K) * (πCSL d : GL (Fin N) K)
    exact congrArg Subtype.val (hcen (πCSL d))
  obtain ⟨eC⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hperf πC hπC_surj hπC_ker
  exact ⟨a, E, hEf, hEalg, hEfin, ha, ⟨eC.trans φ⟩⟩

end CFSG.StandardType

end
