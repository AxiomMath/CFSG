module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTwE6PlaneEnnola
import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit
import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplit
import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoRootSL2
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LeviCatalogueCentralizer
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootQ1

public section

namespace CFSG.StandardType.TwE6NormThree

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree


theorem exists_fixed_involution_twE6 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {X : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hX : IsElemAbelian 3 X)
    (hXI : (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
    (hX4 : 3 ^ 4 ≤ Nat.card X)
    (hXU : ∃ U : Subgroup (TwE6Delta.RecipeR K n), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U) :
    ∃ u : TwE6Delta.RecipeR K n, u * u = 1 ∧ u ≠ 1 ∧ ∀ φ ∈ X, φ u = u := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨U, hU, hU2, hUX⟩ := hXU
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj hn hK
  have hXr : X ≤ (TwE6Transport.recipeConj σ ε).range := fun φ hφ => (hε φ).2 (hXI hφ)
  have hAI := TwE6Transport.recipeMat_le σ ε X
  have hA := TwE6Transport.isElemAbelian_recipeMat σ ε hn hK hσ hX
  have hA4 : 3 ^ 4 ≤ Nat.card (TwE6Transport.recipeMat σ ε X) := by
    rw [TwE6Transport.card_recipeMat σ ε hn hK hσ hXr]; exact hX4
  have hAU := TwE6Transport.twNormTwo_recipeMat σ ε hU hU2 hUX
  obtain ⟨D, hc, hv⟩ := TwE6FieldCore.exists_twLangData_ennola hK hσ h3 hAI hA hA4 hAU
  obtain ⟨α, hα, hαD⟩ := TwE6RootKill.rootKill_of_ennolaKill_weylKill
      (TwE6RootKill.ennolaKill_of_steps TwE6RootKill.leviSplitStep_holds
          TwE6RootKill.ennolaSplitStep_holds) TwE6RootKill.weylKill_holds K σ (2 ^ n) hK hσ (ringChar.eq K 2) 3
    Nat.prime_three h3 _ hAI hA (by rw [if_pos rfl]; exact hA4) hAU D
  obtain ⟨Y, Ym, ⟨g, hY, -⟩, hS⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner.exists_longRootPair_of_negDatum
      (2 ^ n) K σ hK hσ (by rw [ringChar.eq K 2]; norm_num) D.Fr D.hFr D.v D.g0 D.hg0C D.hg0 hα
      (hv α)
  obtain ⟨f, hf, hfi⟩ : ∃ f : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag (AlgebraicClosure K),
      (∀ y, f y = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) y * D.g0) ∧
        Function.Injective f :=
    ⟨(MulAut.conj D.g0⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K (AlgebraicClosure K))),
      fun y => by simp [MulAut.conj_apply],
      (MulAut.conj D.g0⁻¹).injective.comp (baseChangeGL_injective _)⟩
  have hcomm : ∀ u ∈ Y, ∀ y ∈ TwE6Transport.recipeMat σ ε X,
      Commute (u : ModGL TwistTag.E6.tag K) y := by
    intro u hu y hy
    obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.1 ((hS u).1 (Subgroup.subset_closure (Or.inl hu)))
    obtain ⟨a, ha, haα⟩ := hαD y hy
    have hfz : f u = z := by
      rw [hf, ← hzu]
      simp [MulAut.conj_apply, mul_assoc]
    have hfy : rootDiagUnit TwistTag.E6.tag a = f y := by
      rw [ha, hc, hf, one_mul, inv_one, mul_one]
    have hneg : rootChar a (-α) = 1 := by
      have h := rootChar_sub a 0 α
      rwa [zero_sub, rootChar_zero, haα, inv_one, one_mul] at h
    have hza := Subgroup.mem_centralizer_iff.1 (rootSpan_le_centralizer_rootDiagUnit a
      (S := {α, -α}) (by rintro β (rfl | rfl); exacts [⟨hα, haα⟩, ⟨IsRoot.neg hα, hneg⟩]) hz) _
      (Set.mem_singleton _)
    show (u : ModGL TwistTag.E6.tag K) * y = y * u
    apply hfi
    rw [map_mul, map_mul, hfz, ← hfy]
    exact hza.symm
  have hY2 : IsPGroup 2 Y := by
    have h := (TwE6LongRoot.isPGroup_twE6RootSubgroup σ e6HighestRoot).map
      (MulAut.conj g).toMonoidHom
    rwa [ringChar.eq K 2, ← hY] at h
  have hY1 : Y ≠ ⊥ := by
    rw [hY, Ne, Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj g).toMonoidHom) _
      (MulAut.conj g).injective]
    exact (twE6RootSubgroup_ne_bot σ).1
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2
    (hY2.card_eq_or_dvd.resolve_left fun h => hY1 (Subgroup.card_eq_one.1 h))
  have hw2 : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rwa [hw, pow_two] at h
  have hw1 : w ≠ 1 := fun h => by
    rw [h, orderOf_one] at hw
    exact absurd hw (by norm_num)
  refine ⟨ε (w : twistedE6RootGroup K σ), ?_, fun h => hw1 (Subtype.ext ?_), fun φ hφ => ?_⟩
  · rw [← map_mul ε, ← Subgroup.coe_mul, hw2, Subgroup.coe_one, map_one]
  · exact (map_eq_one_iff ε ε.injective).1 h
  · exact TwE6Transport.apply_eq_of_forall_commute_recipeMat σ ε hXr (w : twistedE6RootGroup K σ).2
      (fun y hy => hcomm w w.2 y hy) hφ

end CFSG.StandardType.TwE6NormThree

end
