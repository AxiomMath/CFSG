module

public import CFSG.Monster.B.Short.ShortStab
public import CFSG.Monster.B.Short.Transitivity

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Short

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Griess CFSG.Monster.ScalarKernel
  CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.Visible

theorem exists_latHom_eq_uL {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    ∃ g : latticeO, latHom g ⟨u, hu.1⟩ = uL := by
  obtain ⟨p, hp⟩ := exists_Pvis_of_short ⟨u, hu, rfl⟩ classOf_vMinus_mem_shortSet
  have hm := latVec_mem_minVecs p.1.2 hu
  have hcl : classOf (vMinus 0 1) = classOf (latVec (mat p.1.2) u) :=
    ((classOf_latVec p.1.2 hu.1).trans hp).symm
  rcases (classOf_eq_iff vMinus_zero_one_mem hm).1 hcl with h | h
  · exact ⟨p.1.2, Subtype.ext h⟩
  · refine ⟨p.1.2 * negOneO, ?_⟩
    have h' : latHom p.1.2 ⟨u, hu.1⟩ = -uL := Subtype.ext h
    rw [latHom_mul, h', latHom_negOneO, neg_neg]

theorem KvAct_injective {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    Function.Injective (KvAct (classOf u)) := by
  obtain ⟨g₂, hg₂⟩ := exists_latHom_eq_uL hu
  exact KvAct_injective_of_transport hu g₂ hg₂

theorem lattice_short_stabilizer_22_faithful
    {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    classOf u ≠ 0 ∧ qL (classOf u) = 0 ∧
    (QuadraticMap.polarBilin (qW (classOf u) (qL_classOf_minVecs hu))).Nondegenerate ∧
    Module.finrank (ZMod 2) (Wv (classOf u)) = 22 ∧
    (∀ x : vPerpL (classOf u),
      qW (classOf u) (qL_classOf_minVecs hu) (Submodule.Quotient.mk x) = qL (x : L2)) ∧
    Function.Injective (KvAct (classOf u)) ∧
    Function.Bijective (stabRes hu.1) ∧ Nonempty (OLstab u ≃* Kstab (classOf u)) :=
  ⟨classOf_ne_zero_of_mem_minVecs hu, qL_classOf_minVecs hu,
    polarBilin_qW_nondegenerate (classOf_ne_zero_of_mem_minVecs hu) (qL_classOf_minVecs hu),
    finrank_Wv (classOf_ne_zero_of_mem_minVecs hu), fun x => qW_mk _ _ x, KvAct_injective hu,
    ⟨stabRes_injective hu, stabRes_surjective hu⟩, ⟨stabResEquiv hu⟩⟩

end CFSG.Monster.B.Short
