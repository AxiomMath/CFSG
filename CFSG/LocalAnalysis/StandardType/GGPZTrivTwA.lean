module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosure
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGPZTrivTwTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggPZ_automizer_twA
    {G : Type} [Group G] [Finite G] {p l n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {J EJ : Subgroup G} (hl : 2 ≤ l) (hpq : p ∣ 2 ^ n + 1) (hpl : p ∣ l + 3)
    (hJ : GGHasLabel ⟨.twA, l, n⟩ (↥J ⧸ Subgroup.center ↥J)) (hJq : IsQuasisimple ↥J)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J)) (hEJ : EJ ≤ J) (hE : IsElemAbelian p EJ)
    (hcard : Nat.card ↥EJ = p ^ l) :
    ∃ f : Equiv.Perm (Fin (l + 1)) →* MulAut ↥EJ, ggAutomizer J EJ ≤ f.range := by
  obtain ⟨θ, hθinj, hθrange, hθnorm⟩ := ggPZ_twA_torus hp2 hl hpq hpl hJ hJq hZ hEJ hE hcard
  let ι : ↥(UCoord.sumZero (l + 1) p) ≃* ↥EJ :=
    (MonoidHom.ofInjective hθinj).trans (MulEquiv.subgroupCongr hθrange)
  have hι : ∀ f, ((ι f : ↥EJ) : G) = θ f := fun _ => rfl
  refine ⟨(MulAut.congr ι).toMonoidHom.comp (UCoord.permAutVHom (d := l + 1) (p := p)), ?_⟩
  intro φ hφ
  obtain ⟨g, hgJ, hgN, hg⟩ := mem_ggAutomizer_iff.mp hφ
  obtain ⟨π, hπ⟩ := hθnorm g hgJ hgN
  refine ⟨π, ?_⟩
  refine MulEquiv.ext fun b => Subtype.ext ?_
  obtain ⟨f, rfl⟩ := ι.surjective b
  show ((MulAut.congr ι (UCoord.permAutV π) (ι f) : ↥EJ) : G) = ((φ (ι f) : ↥EJ) : G)
  rw [hg, hι, hπ f]
  simp [MulAut.congr_apply, MulEquiv.symm_apply_apply, hι]


end CFSG.StandardType

end
