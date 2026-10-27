module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeGeometry
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeCoverFrame
import CFSG.Quasithin.Vol2.KGFactC31NoM22FusBurnside
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import CFSG.GroupTheory.PGroup.LtInfNormalizer
import CFSG.LinearAlgebra.F3ConnectedPairingScalar
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem mem_axis_of_eq_smul_single {d : SylowThreeData G}
    {e : Multiplicative (Fin 3 → ZMod 3) ≃* d.AA}
    (haxis : ∀ i : Fin 3, (d.A i).subgroupOf d.AA =
      Subgroup.zpowers (e (Multiplicative.ofAdd (Pi.single i 1))))
    (j : Fin 3) (v : Fin 3 → ZMod 3)
    (hv : v = (v j) • (Pi.single j 1 : Fin 3 → ZMod 3)) :
    e (Multiplicative.ofAdd v) ∈ (d.A j).subgroupOf d.AA := by
  rw [hv, haxis j]
  have hsm : (v j) • (Pi.single j 1 : Fin 3 → ZMod 3) =
      (v j).val • (Pi.single j 1 : Fin 3 → ZMod 3) := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3) (v j).val (Pi.single j 1),
      ZMod.natCast_zmod_val]
  rw [hsm, ofAdd_nsmul, map_pow]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

private theorem inf_plane_eq_axis {d : SylowThreeData G}
    {e : Multiplicative (Fin 3 → ZMod 3) ≃* d.AA}
    (haxis : ∀ i : Fin 3, (d.A i).subgroupOf d.AA =
      Subgroup.zpowers (e (Multiplicative.ofAdd (Pi.single i 1))))
    (hplane : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      ∀ v : Fin 3 → ZMod 3,
        e (Multiplicative.ofAdd v) ∈
            (d.A i).subgroupOf d.AA ⊔ (d.A j).subgroupOf d.AA ↔ v k = 0)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((d.A i).subgroupOf d.AA ⊔ (d.A j).subgroupOf d.AA) ⊓
      ((d.A j).subgroupOf d.AA ⊔ (d.A k).subgroupOf d.AA) =
      (d.A j).subgroupOf d.AA := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨v, rfl⟩ : ∃ v : Fin 3 → ZMod 3, e (Multiplicative.ofAdd v) = z := by
      obtain ⟨w, hw⟩ := e.surjective z
      exact ⟨Multiplicative.toAdd w, by simpa using hw⟩
    have hvk : v k = 0 := (hplane i j k hij hik hjk v).mp hz1
    have hvi : v i = 0 :=
      (hplane j k i hjk hij.symm hik.symm v).mp hz2
    have hcover : ∀ s : Fin 3, s = i ∨ s = j ∨ s = k := by
      intro s
      by_contra h
      push Not at h
      have h4 : s.val ≠ i.val := fun hh => h.1 (Fin.ext hh)
      have h5 : s.val ≠ j.val := fun hh => h.2.1 (Fin.ext hh)
      have h6 : s.val ≠ k.val := fun hh => h.2.2 (Fin.ext hh)
      have h1 : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
      have h2 : i.val ≠ k.val := fun hh => hik (Fin.ext hh)
      have h3 : j.val ≠ k.val := fun hh => hjk (Fin.ext hh)
      have hi := i.isLt; have hj := j.isLt; have hk := k.isLt; have hs := s.isLt
      omega
    have hv : v = (v j) • (Pi.single j 1 : Fin 3 → ZMod 3) := by
      funext s
      rcases hcover s with h | h | h
      · subst s; simp [hij, hvi]
      · subst s; simp
      · subst s
        have hkj : k ≠ j := hjk.symm
        simp [hkj, hvk]
    exact mem_axis_of_eq_smul_single haxis j v hv
  · intro z hz
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_sup_right hz, Subgroup.mem_sup_left hz⟩

private theorem inf_plane_eq_axis_G {d : SylowThreeData G}
    {e : Multiplicative (Fin 3 → ZMod 3) ≃* d.AA}
    (hA : ∀ t : Fin 3, d.A t ≤ d.AA)
    (haxis : ∀ i : Fin 3, (d.A i).subgroupOf d.AA =
      Subgroup.zpowers (e (Multiplicative.ofAdd (Pi.single i 1))))
    (hplane : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      ∀ v : Fin 3 → ZMod 3,
        e (Multiplicative.ofAdd v) ∈
            (d.A i).subgroupOf d.AA ⊔ (d.A j).subgroupOf d.AA ↔ v k = 0)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (d.A i ⊔ d.A j) ⊓ (d.A j ⊔ d.A k) = d.A j := by
  have h := inf_plane_eq_axis haxis hplane hij hik hjk
  have h' : ((d.A i ⊔ d.A j).subgroupOf d.AA) ⊓
      ((d.A j ⊔ d.A k).subgroupOf d.AA) = (d.A j).subgroupOf d.AA := by
    simpa [Subgroup.subgroupOf_sup (hA i) (hA j),
      Subgroup.subgroupOf_sup (hA j) (hA k)] using h
  have hG := congrArg (fun H : Subgroup d.AA => H.map d.AA.subtype) h'
  rwa [Subgroup.map_inf _ _ _ d.AA.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le (sup_le (hA i) (hA j)),
    Subgroup.map_subgroupOf_eq_of_le (sup_le (hA j) (hA k)),
    Subgroup.map_subgroupOf_eq_of_le (hA j)] at hG

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
