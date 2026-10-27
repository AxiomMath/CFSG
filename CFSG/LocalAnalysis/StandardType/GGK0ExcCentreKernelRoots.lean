module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem PA2a_vanishes_on_kernelRoots
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (b : Fin ρ.tau.rank → Omegaˣ) (t : Fin ρ.row.diagram.marks.length → ZMod p)
    (ht : ∀ i, rootChar b (ρ.nodeMap (Pi.single i 1)) = ρ.zeta ^ (t i).val)
    (hz : ∀ i, ρ.row.s.getD i.val 0 = 0 → t i = 0) :
    ∀ γ ∈ kernelRoots (rootCharHom ρ.a), rootChar b γ = 1 := by
  have hzsmul : ∀ (k : ℤ) (v : Fin ρ.tau.rank → ℤ),
      rootChar b (k • v) = (rootChar b v) ^ k := by
    intro k v
    simp only [rootChar, Pi.smul_apply, zsmul_eq_mul]
    rw [Finset.prod_congr rfl (fun i _ => by rw [mul_comm, zpow_mul])]
    exact Finset.prod_zpow (fun i => b i ^ v i) Finset.univ k
  let K : Submodule ℤ (Fin ρ.tau.rank → ℤ) :=
    { carrier := {v | rootChar b v = 1}
      zero_mem' := rootChar_zero b
      add_mem' := by
        intro u v hu hv
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        rw [rootChar_add, hu, hv, one_mul]
      smul_mem' := by
        intro k v hv
        simp only [Set.mem_setOf_eq] at hv ⊢
        rw [hzsmul, hv, one_zpow] }
  have hK : Submodule.span ℤ {v | ∃ i : Fin ρ.row.diagram.marks.length,
      ρ.row.s.getD i.val 0 = 0 ∧ v = ρ.nodeMap (Pi.single i 1)} ≤ K := by
    rw [Submodule.span_le]
    rintro v ⟨i, hi, rfl⟩
    change rootChar b (ρ.nodeMap (Pi.single i 1)) = 1
    simp [ht i, hz i hi]
  intro γ hγ
  have hspan : γ ∈ Submodule.span ℤ (kernelRoots (rootCharHom ρ.a)) := Submodule.subset_span hγ
  rw [ρ.kernel_span_eq] at hspan
  exact hK hspan

end CFSG.StandardType.GGK0ExcCentreU

end
