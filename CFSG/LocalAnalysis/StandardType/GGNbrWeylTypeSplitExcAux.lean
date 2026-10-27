module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBRowF4CoreAux
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.RankThree.CentralCover Multiplicative

theorem ggWTSX_weylTypeW_of_card_lt {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hX : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
      Nat.card X < p ^ 3) :
    GGTorusWeylTypeW p r R I := by
  classical
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, -⟩ := hA
  exfalso
  have hXA : IsElemAbelian p (TypeA.inducedSub ψ A) := TypeA.isElemAbelian_inducedSub hψ hAe
  have hXI : ((TypeA.inducedSub ψ A : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact TypeA.induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (TypeA.inducedSub ψ A) = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  have hlt := hX _ hXI hXA
  rw [hcardX] at hlt
  omega

theorem ggWTSX_frame_base
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hrange : (chevTorus τ ζ hζ).range = TableBExc.torusPow τ K p)
    (hinj : Function.Injective (chevTorus τ ζ hζ)) :
    GGTorusCoordFrame p (chevTorus τ ζ hζ) (coxeterMatrix (isFiniteType_cartan τ)) := by
  have hχ : ggTorusInduced (chevTorus τ ζ hζ) =
      (ExcWeylOuter.torusMulAut τ p).range :=
    ExcWeylOuter.ggTorusInduced_chevTorus hsymm ζ hζ hrange hinj
  let e : (coxeterMatrix (isFiniteType_cartan τ)).Group ≃*
      ↥(ggTorusInduced (chevTorus τ ζ hζ)) :=
    (MonoidHom.ofInjective (ExcWeylOuter.torusMulAut_injective (τ := τ) hp2)).trans
      (MulEquiv.subgroupCongr hχ.symm)
  refine ⟨fun i => ExcWeylOuter.torusMulAut τ p (simple τ i), ?_, e, ?_⟩
  · intro i
    change ExcWeylOuter.torusMulAut τ p (simple τ i) ∈
      NbrTableBExc.ggTorusInvolSet p (chevTorus τ ζ hζ)
    rw [ExcWeylOuter.torusMulAut_simple hsymm i]
    refine ⟨by rw [pow_two, torusReflAut_mul_self],
      card_fix_torusReflAut Fact.out hp2 _ _ _, ?_⟩
    refine ⟨⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩, fun f => ?_⟩
    have h1 := weylElt_conj_chevTorus (K := K) ζ hζ i (toAdd f)
    rw [ofAdd_toAdd] at h1
    rw [← ofAdd_toAdd f]
    rw [torusReflAut_apply]
    exact h1
  · intro i
    rfl

end CFSG.StandardType

end
