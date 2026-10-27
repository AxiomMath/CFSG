module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycMInput
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicModelToral
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley

theorem largeEvenSplit_of_untwisted {p n : ℕ} {tag : LargeEvenLieTag}
    (hu : LargeEvenUntwisted tag) (hs : p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3)) (r : ℕ) :
    LargeEvenSplit p ⟨tag, r, n⟩ :=
  hs.elim (fun h => Or.inl ⟨hu, h⟩) fun h => Or.inr (Or.inr (Or.inr h))

section Adj


theorem ggLayerLieTwo_adjointGroup_of_recipe {τ : Tag} {n p : ℕ}
    (hall : ∀ Q : LargeEvenRawCont, LargeEvenRecipeChevalley τ.cartan (2 ^ n) false Q →
      LargeEvenRecipeChevalley τ.cartan (2 ^ n) false fun R _ I F =>
        Q R I F ∧ ∀ φ ∈ I, LayerCycM.GGLayerLieTwo p φ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ n) (h : adjointGroup τ K) :
    LayerCycM.GGLayerLieTwo p (MulAut.conj h) := by
  have hQ : LargeEvenRecipeChevalley τ.cartan (2 ^ n) false
      (fun R _ I _ => Nonempty (R ≃* adjointGroup τ K) ∧ ∀ r : R, MulAut.conj r ∈ I) :=
    ⟨K, inferInstance, inferInstance, hK, ⟨TableBExc.recipeEquiv τ K⟩,
      fun r => conj_mem_largeEvenChevIDImage _ _ _ r⟩
  obtain ⟨K', i1, i2, hK', ⟨⟨e⟩, hinn⟩, hP⟩ := hall _ hQ
  have hφ : ∀ l : adjointGroup τ K, e.symm.toMonoidHom (MulAut.conj h l) =
      MulAut.conj (e.symm h) (e.symm.toMonoidHom l) := fun l => by
    simp [MulAut.conj_apply]
  exact LayerCycM.GGLayerLieTwo.of_central_surjective e.symm.toMonoidHom e.symm.surjective
    (fun x hx => by
      have hx1 : x = 1 := e.symm.injective (by simpa using MonoidHom.mem_ker.mp hx)
      rw [hx1]
      exact Subgroup.one_mem _) hφ (LayerCycM.ne_one_of_injective e.symm.injective hφ)
    (hP _ (hinn _))

theorem ggExcAdjLayerCycNonToralInput_of_recipe (hG : CFSG.Open.GriessAllModelsStatement)
    {τ : Tag} {n₀ b : ℕ}
    (hall : ∀ (n p : ℕ), n₀ ≤ n → p.Prime → p ≠ 2 → (p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3)) →
      ∀ Q : LargeEvenRawCont, LargeEvenRecipeChevalley τ.cartan (2 ^ n) false Q →
        LargeEvenRecipeChevalley τ.cartan (2 ^ n) false fun R _ I F =>
          Q R I F ∧ ∀ φ ∈ I, LayerCycM.GGLayerLieTwo p φ) :
    GGExcAdjLayerCycNonToralInput τ n₀ b := by
  intro K _ _ n hn hK p hp hp2 hs _ x _ _
  haveI : Finite (adjointGroup τ K) := CFSG.LieType.Chevalley.generated_group_finite τ K
  exact LayerCycM.ggModelLayerCyclic_of_layerLieTwo hG hp hp2
    (ggLayerLieTwo_adjointGroup_of_recipe (hall n p hn hp hp2 hs) K hK x)

theorem ggE6AdjLayerCycNonToralInput_of_recipe (hG : CFSG.Open.GriessAllModelsStatement)
    (hall : ∀ (n p : ℕ), 1 ≤ n → p.Prime → p ≠ 2 → (p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3)) →
      ∀ Q : LargeEvenRawCont, LargeEvenRecipeChevalley Tag.E6.cartan (2 ^ n) false Q →
        LargeEvenRecipeChevalley Tag.E6.cartan (2 ^ n) false fun R _ I F =>
          Q R I F ∧ ∀ φ ∈ I, LayerCycM.GGLayerLieTwo p φ) :
    GGE6AdjLayerCycNonToralInput := by
  intro K _ _ n hn hK p hp hp2 hs _ _ x _ _
  haveI : Finite (adjointGroup .E6 K) := CFSG.LieType.Chevalley.generated_group_finite .E6 K
  exact LayerCycM.ggModelLayerCyclic_of_layerLieTwo hG hp hp2
    (ggLayerLieTwo_adjointGroup_of_recipe (hall n p hn hp hp2 hs) K hK x)

theorem ggExcAdjLayerCycNonToralInput_G2_of_lieLayer (hG : CFSG.Open.GriessAllModelsStatement)
    (h : GGLieLayerInputOn fun lab => lab.tag = .G2) :
    GGExcAdjLayerCycNonToralInput .G2 2 5 :=
  ggExcAdjLayerCycNonToralInput_of_recipe hG fun n p hn hp hp2 hs Q hQ => by
    have hlab : LargeEvenInLambda2 ⟨.G2, 0, n⟩ := ⟨by show 1 ≤ n; omega, rfl, hn⟩
    have hsp : LargeEvenSplit p ⟨.G2, 0, n⟩ :=
      largeEvenSplit_of_untwisted (tag := .G2) trivial hs 0
    exact h p ⟨.G2, 0, n⟩ hp hp2 hlab hsp rfl Q hQ

theorem ggExcAdjLayerCycNonToralInput_F4_of_lieLayer (hG : CFSG.Open.GriessAllModelsStatement)
    (h : GGLieLayerInputOn fun lab => lab.tag = .F4) :
    GGExcAdjLayerCycNonToralInput .F4 1 5 :=
  ggExcAdjLayerCycNonToralInput_of_recipe hG fun n p hn hp hp2 hs Q hQ => by
    have hlab : LargeEvenInLambda2 ⟨.F4, 0, n⟩ := ⟨hn, rfl⟩
    have hsp : LargeEvenSplit p ⟨.F4, 0, n⟩ :=
      largeEvenSplit_of_untwisted (tag := .F4) trivial hs 0
    exact h p ⟨.F4, 0, n⟩ hp hp2 hlab hsp rfl Q hQ

theorem ggExcAdjLayerCycNonToralInput_E7_of_lieLayer (hG : CFSG.Open.GriessAllModelsStatement)
    (h : GGLieLayerInputOn fun lab => lab.tag = .E7) :
    GGExcAdjLayerCycNonToralInput .E7 1 11 :=
  ggExcAdjLayerCycNonToralInput_of_recipe hG fun n p hn hp hp2 hs Q hQ => by
    have hlab : LargeEvenInLambda2 ⟨.E7, 0, n⟩ := ⟨hn, rfl⟩
    have hsp : LargeEvenSplit p ⟨.E7, 0, n⟩ :=
      largeEvenSplit_of_untwisted (tag := .E7) trivial hs 0
    exact h p ⟨.E7, 0, n⟩ hp hp2 hlab hsp rfl Q hQ

theorem ggExcAdjLayerCycNonToralInput_E8_of_lieLayer (hG : CFSG.Open.GriessAllModelsStatement)
    (h : GGLieLayerInputOn fun lab => lab.tag = .E8) :
    GGExcAdjLayerCycNonToralInput .E8 1 11 :=
  ggExcAdjLayerCycNonToralInput_of_recipe hG fun n p hn hp hp2 hs Q hQ => by
    have hlab : LargeEvenInLambda2 ⟨.E8, 0, n⟩ := ⟨hn, rfl⟩
    have hsp : LargeEvenSplit p ⟨.E8, 0, n⟩ :=
      largeEvenSplit_of_untwisted (tag := .E8) trivial hs 0
    exact h p ⟨.E8, 0, n⟩ hp hp2 hlab hsp rfl Q hQ

theorem ggE6AdjLayerCycNonToralInput_of_lieLayer (hG : CFSG.Open.GriessAllModelsStatement)
    (h : GGLieLayerInputOn fun lab => lab.tag = .E6) : GGE6AdjLayerCycNonToralInput :=
  ggE6AdjLayerCycNonToralInput_of_recipe hG fun n p hn hp hp2 hs Q hQ => by
    have hlab : LargeEvenInLambda2 ⟨.E6, 0, n⟩ := ⟨hn, rfl⟩
    have hsp : LargeEvenSplit p ⟨.E6, 0, n⟩ :=
      largeEvenSplit_of_untwisted (tag := .E6) trivial hs 0
    exact h p ⟨.E6, 0, n⟩ hp hp2 hlab hsp rfl Q hQ

end Adj

end CFSG.StandardType

end
