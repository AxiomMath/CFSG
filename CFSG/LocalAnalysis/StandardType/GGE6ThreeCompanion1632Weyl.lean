module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632Lang
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCentralizer

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma ltrb1g1_relIndex_eq_card {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (K ⧸ H.subgroupOf K) = H.relIndex K := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]

private lemma ltrb1g1_closure_rootDiagUnit_eq_torusGroup {Omega : Type} [Field Omega]
    [IsAlgClosed Omega] [CharP Omega 2]
    (τ : Tag) :
    Subgroup.closure (Set.range (fun b : Fin τ.rank → Omegaˣ => rootDiagUnit τ b)) =
      torusGroup τ Omega := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    exact rootDiagUnit_mem_torusGroup (τ := τ) b
  · intro g hg
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (τ := τ) hg
    exact Subgroup.subset_closure ⟨l, rfl⟩

theorem weylIndexAt_holds
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : WeylIndexAt ρ := by
  have hclosure := ltrb1g1_closure_rootDiagUnit_eq_torusGroup (Omega := Omega) ρ.tau
  have hM : connectedCentralizer ρ = toralRootGroup ρ.tau Omega ρ.a := by
    unfold connectedCentralizer toralRootGroup
    rw [hclosure]
    have hker : kernelRoots (rootCharHom ρ.a) = rootCharKernel ρ.a := rfl
    rw [hker]
  have hX : geomCentralizer ρ = toralCentralizer ρ.tau Omega ρ.a := rfl
  obtain ⟨_, _, _, _, φ, hsurj, hφ⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient ρ.tau Omega ρ.a
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro q hq
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker] at hq
    have h1 : (⟨canonicalRep (coxeterSystem ρ.tau) Omega (w : WeylGroup ρ.tau),
        canonicalRep_mem_toralCentralizer w.2⟩ :
        toralCentralizer ρ.tau Omega ρ.a) ∈
        (toralRootGroup ρ.tau Omega ρ.a).subgroupOf (toralCentralizer ρ.tau Omega ρ.a) := by
      rw [← QuotientGroup.eq_one_iff]
      rw [hφ w] at hq
      exact hq
    have hmem : canonicalRep (coxeterSystem ρ.tau) Omega (w : WeylGroup ρ.tau) ∈
        toralRootGroup ρ.tau Omega ρ.a := Subgroup.mem_subgroupOf.1 h1
    have hw : (w : WeylGroup ρ.tau) ∈ kernelReflectionGroup ρ.a :=
      CFSG.HardMathSupport.Timmesfeld.Steinberg.mem_kernelReflectionGroup_of_canonicalRep_mem_gen
        hmem
    exact (QuotientGroup.eq_one_iff w).2 (Subgroup.mem_subgroupOf.2 hw)
  have hcard : Nat.card (rootCharStabilizerSubgroup ρ.a ⧸
        (kernelReflectionGroup ρ.a).subgroupOf (rootCharStabilizerSubgroup ρ.a)) =
      Nat.card (toralCentralizer ρ.tau Omega ρ.a ⧸
        (toralRootGroup ρ.tau Omega ρ.a).subgroupOf (toralCentralizer ρ.tau Omega ρ.a)) :=
    Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)
  unfold WeylIndexAt
  rw [hM, hX]
  rw [← ltrb1g1_relIndex_eq_card (toralRootGroup ρ.tau Omega ρ.a)
        (toralCentralizer ρ.tau Omega ρ.a),
      ← ltrb1g1_relIndex_eq_card (kernelReflectionGroup ρ.a) (rootCharStabilizerSubgroup ρ.a)]
  exact hcard.symm

end CFSG.StandardType.S2MathAs1E6Companion1625

end
