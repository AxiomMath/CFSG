module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDTablePDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.SpTwoLocalRankLower
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxElem
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7Three
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7E8Five
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley


theorem ggQTwoDE7SU6Cof_holds : GGQTwoDE7SU6Cof := by
  intro X _ _ A Ab σ J n hd _hk _hJ hX hn
  obtain ⟨⟨hcore, hflat, -, hrank, hnum, hsc, -, hmarked⟩, -⟩ := hd
  obtain ⟨hperf, lab', hΛ', hraw⟩ := hmarked
  have hΛ : LargeEvenInLambda2 (⟨.E7, 0, 1⟩ : LargeEvenLabel) := ⟨le_rfl, rfl⟩
  have hlab' : GGHasLabel lab' (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun θ _ => ⟨θ⟩)) hraw
  have hiso := ggLabelRigidInput_holds lab' ⟨.E7, 0, 1⟩ (X ⧸ Subgroup.center X) hΛ' hΛ hlab' hX
  have hrawX := largeEvenRawDatum_of_ggLabelIso hiso hraw
  obtain ⟨K, _, _, hK, -, -, θ, -, -, hInd⟩ := hrawX
  have hK2 : Nat.card K = 2 ^ 1 := hK
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK2
  let ψ : X →* TableBExc.RecipeGroup .E7 K :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    exact ⟨x, by change θ (QuotientGroup.mk' (Subgroup.center X) x) = r; rw [hx, hq]⟩
  have hker : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff x).mp (θ.injective (hx.trans (map_one θ).symm))
  have hAI : ∀ a ∈ A, ∃ φ ∈ TableBExc.RecipeID .E7 K, ∀ l : X, φ (ψ l) = ψ (a l) := by
    intro a ha
    refine ⟨ggInducedAut θ a, hInd a ha, fun l => ?_⟩
    change ggInducedAut θ a (θ (l : X ⧸ Subgroup.center X)) =
      θ ((a l : X) : X ⧸ Subgroup.center X)
    exact ggInducedAut_apply θ a l
  have hcp : GGCenterPrime 3 (TableBExc.RecipeGroup .E7 K) :=
    ExcSplitL.ggCenterPrime_recipe_E7 le_rfl hK2 Nat.prime_three (by decide)
  have hcpX : ¬ 3 ∣ Nat.card (Subgroup.center X) := hcp X ψ hψ hker hperf
  obtain ⟨U, E₀, hU, hU2, hEU, hE₀, hcard₀, -⟩ :=
    TableBExcTwo.ggTorusLift_E7Two (K := K) X ψ hψ hker hperf
  have h6 : 6 ≤ LargeEvenTwoLocalRank 3 X :=
    SpRank.le_largeEvenTwoLocalRank_of_normalizes (MonoidHom.id X) Function.injective_id
      Nat.prime_three hE₀ hcard₀ hU hU2 hEU
  obtain ⟨m, hm, hmle⟩ := hrank
  rw [if_neg hcpX, add_zero] at hmle
  have : Finite (MulAut X) := Finite.of_injective (fun f : MulAut X => (f : X → X))
    (fun f g h => MulEquiv.ext (congrFun h))
  have hAb : 3 ^ 6 ≤ Nat.card Ab := by
    rw [hm]
    exact Nat.pow_le_pow_right (by norm_num) (h6.trans hmle)
  have hAbA : Nat.card Ab ≤ Nat.card A := Subgroup.card_le_of_le hflat.1
  have hA6 : Nat.card A ≤ 3 ^ 6 := by
    have h := hnum.1
    rw [hn] at h
    omega
  obtain ⟨Λ, -, -, -, -, hE, hcardE, hscE⟩ :=
    TwE6TB.exists_innerModel Nat.prime_three (TableBExc.center_recipeGroup_eq_bot .E7 K)
      (fun _ hβ _ => TableBExc.idImage_subset_inn_E7 K hβ) hcp ψ hψ hker hperf hcore.1 hAI hsc
  let φR := TableBExc.recipeEquiv .E7 K
  let E' : Subgroup (adjointGroup .E7 K) := (A.comap Λ).map φR.toMonoidHom
  have hE' : CFSG.Open.IsElemAbelian 3 E' := hE.map φR.toMonoidHom
  have hcardE' : Nat.card E' = Nat.card A := by
    rw [← hcardE]
    exact Subgroup.card_map_of_injective φR.injective
  have hscE' : ∀ x ∈ Subgroup.centralizer (E' : Set (adjointGroup .E7 K)), x ^ 3 = 1 →
      x ∈ E' := by
    intro x hx hx3
    refine ⟨φR.symm x, hscE (φR.symm x) (fun e he => ?_) ?_, φR.apply_symm_apply x⟩
    · have hc := Subgroup.mem_centralizer_iff.mp hx (φR e) ⟨e, he, rfl⟩
      apply φR.injective
      rw [map_mul, map_mul, φR.apply_symm_apply]
      exact hc.symm
    · rw [← map_pow, hx3, map_one]
  have h7 := ExcFramesHalf.ggExcHalfMaxElemInput_E7 ExcFramesHalf.bigElemAbelianToralBar_E7_three
    ExcFramesHalf.bigElemAbelianToralBar_E7_five K 3 Nat.prime_three (by decide)
    (by rw [hK2]; norm_num) (Or.inl rfl) E' hE' (by rw [hcardE']; exact hAb.trans hAbA) hscE'
  rw [hcardE'] at h7
  have h77 : (3 : ℕ) ^ Tag.E7.rank = 3 ^ 7 := rfl
  rw [h77] at h7
  have : (3 : ℕ) ^ 7 ≤ 3 ^ 6 := h7.trans hA6
  norm_num at this

end CFSG.StandardType

end
