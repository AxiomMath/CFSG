module

import CFSG.RankThree.PartOne.BRANCH.RankTri
import CFSG.RankThree.PartOne.KF.ClsD4Torus
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.N143X
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.BRANCH

theorem triality_split_bound_five
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) (h3 : 2 ^ f % 3 = 1)
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hE : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 3 ^ (1 + 2) := by
  classical
  have hodd : Odd (Nat.card K - 1) := by
    rw [hK, ← pow_mul]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hQ2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨hC, hTor, -⟩ := triality_both_orientations_exact_finite_order 2 f Nat.prime_two hf K
    hK 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)
  have hle1 : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := graphFixedRootTorus_le _ _ _
  let T : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
  let eT : T ≃* graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    Subgroup.subgroupOfEquivOfLe hle1
  let f₀ : (Fin TwistTag.D4.tag.rank → Kˣ) →* ModGL TwistTag.D4.tag K :=
    (torusGroup TwistTag.D4.tag K).subtype.comp (torusCoordHom TwistTag.D4.tag K)
  have hf₀ : Function.Injective f₀ := coordHom_injective_D4 hodd
  have hcompat : graphFixedRootTorus TwistTag.D4 K σ.toRingHom =
      (compatSubgroup (t := TwistTag.D4) σ.toRingHom).map f₀ :=
    graphFixedRootTorus_eq_compatTorus σ.surjective
  let eC : (compatSubgroup (t := TwistTag.D4) σ.toRingHom) ≃*
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    ((compatSubgroup (t := TwistTag.D4) σ.toRingHom).equivMapOfInjective f₀ hf₀).trans
      (MulEquiv.subgroupCongr hcompat.symm)
  let proj : (compatSubgroup (t := TwistTag.D4) σ.toRingHom) →* (Fin 2 → Kˣ) :=
    { toFun := fun c => ![c.1 (d4i 0), c.1 (d4i 2)]
      map_one' := by
        ext i
        fin_cases i <;> rfl
      map_mul' := fun a b => by
        ext i
        fin_cases i <;> rfl }
  have hproj : Function.Injective proj := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have h0 : c.1 (d4i 0) = 1 := congrFun hc 0
    have h2 : c.1 (d4i 2) = 1 := congrFun hc 1
    have hperm0 : TwistTag.D4.perm (d4i 0) = d4i 1 := by decide
    have hperm1 : TwistTag.D4.perm (d4i 1) = d4i 3 := by decide
    have h1 : c.1 (d4i 1) = 1 := by
      have := (mem_compatSubgroup σ.toRingHom).1 c.2 (d4i 0)
      rw [hperm0, h0, map_units_eq_pow hσ, one_pow] at this
      exact this
    have h3' : c.1 (d4i 3) = 1 := by
      have := (mem_compatSubgroup σ.toRingHom).1 c.2 (d4i 1)
      rw [hperm1, h1, map_units_eq_pow hσ, one_pow] at this
      exact this
    refine Subtype.ext (funext fun i => ?_)
    rcases d4i_cases i with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3'
  let ψ : T →* (Fin 2 → Kˣ) := proj.comp (eC.symm.toMonoidHom.comp eT.toMonoidHom)
  have hψ : Function.Injective ψ :=
    hproj.comp (eC.symm.injective.comp eT.injective)
  have hTcard : Nat.card T = ((2 ^ f) ^ 3 - 1) * (2 ^ f - 1) := by
    rw [Nat.card_congr eT.toEquiv]
    exact hTor
  have hidx : ¬ 3 ^ (1 + 1) ∣ T.index := by
    have hmul := T.index_mul_card
    rw [hTcard, hC] at hmul
    have := not_nine_dvd_triality_split hQ2 h3 (by rw [mul_comm]; exact hmul)
    simpa using this
  exact card_le_of_torus Nat.prime_three ψ hψ hidx hE

theorem card_le_triality_three
    {X : Type} [Group X] [Finite X] {f : ℕ} (hX : ChevalleyExceptionalModel X .trialityD4 2 f)
    {E : Subgroup X} (hE : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 3 ^ 3 := by
  have hf : 1 ≤ f := hX.1.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf hX.2
  have hK' : Nat.card K = (2 ^ f) ^ 3 := hK
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv X e.toEquiv
  have hE3 : ∀ x ∈ E.map e.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hE y hy, map_one]
  have hcard' : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective e.injective
  rw [← hcard']
  rcases BRANCH.two_pow_mod_three f with ⟨h3, -⟩ | ⟨h3, -⟩
  · simpa using triality_split_bound_five hf K hK' σ (fun c => hσ c) h3 hE3
  · simpa using triality_twisted_bound hf K hK' σ hσ h3 hE3

theorem false_triality_three_five
    {X : Type} [Group X] [Finite X] {f : ℕ} (hX : ChevalleyExceptionalModel X .trialityD4 2 f)
    {E : Subgroup X} (hE : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 5) : False := by
  have hb := card_le_triality_three hX
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) x hx)
  rw [hcard] at hb
  norm_num at hb

end CFSG.RankThree.PartOne.F106
