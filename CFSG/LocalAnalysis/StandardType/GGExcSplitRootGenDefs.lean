module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedCells

public section

namespace CFSG.StandardType.ExcSplitRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three Multiplicative

variable {τ : Tag} {K : Type} [Field K] {p : ℕ}

section Torus

variable [NeZero p]

@[expose] noncomputable def excTorusHom
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K where
  toFun x := ⟨rootDiagUnit τ (zetaVec ζ hζ (toAdd x)),
    CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup (hfullp _ fun i => by
      rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow])⟩
  map_one' := by
    apply Subtype.ext
    change rootDiagUnit τ (zetaVec ζ hζ 0) = 1
    have h0 : zetaVec (τ := τ) ζ hζ 0 = 1 := by
      funext i
      simp only [zetaVec, Pi.zero_apply, ofAdd_zero, map_one, Pi.one_apply]
    rw [h0]
    exact rootDiagUnit_one
  map_mul' x y := by
    apply Subtype.ext
    change rootDiagUnit τ (zetaVec ζ hζ (toAdd x + toAdd y)) =
      rootDiagUnit τ (zetaVec ζ hζ (toAdd x)) * rootDiagUnit τ (zetaVec ζ hζ (toAdd y))
    rw [← rootDiagUnit_mul]
    congr 1
    funext i
    simp only [zetaVec, Pi.add_apply, Pi.mul_apply, ofAdd_add, map_mul]

theorem coe_excTorusHom
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (x : Multiplicative (Fin τ.rank → ZMod p)) :
    ((excTorusHom hfullp hζ x : adjointGroup τ K) : ModGL τ K) =
      rootDiagUnit τ (zetaVec ζ hζ (toAdd x)) :=
  rfl

end Torus

section Weyl


@[expose] noncomputable def excWeyl (α : {α : Fin τ.rank → ℤ // IsRoot τ α}) :
    adjointGroup τ K :=
  ⟨rootWeylOne τ K α.1, sup_le (rootSubgroup_le_adjointGroup α.1)
    (rootSubgroup_le_adjointGroup (-α.1)) (rootWeylOne_spec α.2).1⟩

end Weyl

@[expose] noncomputable def excRefl (α : Fin τ.rank → ℤ) :
    (Fin τ.rank → ZMod p) → Fin τ.rank → ZMod p :=
  adAct τ p (rootReflection α)

@[expose] noncomputable def excComp
    (α : Fin τ.rank → ℤ) : Subgroup (adjointGroup τ K) :=
  (rootSpan τ K {α, -α}).subgroupOf (adjointGroup τ K)

end CFSG.StandardType.ExcSplitRootGen

end
