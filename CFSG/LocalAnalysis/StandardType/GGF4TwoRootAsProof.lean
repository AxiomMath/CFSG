module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcSmall
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsParabolic
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsSylow

public section

namespace CFSG.StandardType.F4RootAs

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
  CFSG.LieType.Ree CFSG.StandardType.TableBF4TwoInputs

theorem ggEndNodeRootAs_of_root {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGEndNodeRoot p r R I) : GGEndNodeRootAs p r R I := by
  intro L' _ _ ψ hψ hker hperf A _ hA _ _ _ hAI hr h3 hα _
  exact h L' ψ hψ hker hperf A hA hAI hr h3 hα

section Adjoint

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem rootInv_mem_highestRootRankOne :
    TableBF4Two.rootInv K ∈ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) := by
  rw [Subgroup.mem_subgroupOf, highestRootRankOne_eq_rootSL2R, ← range_rootSL2_rootR]
  exact ⟨uSL 1, by rw [TableBF4Two.rootInv, TableBF4Two.coe_rho]; rfl⟩

theorem mem_C3Levi_of_commute_nodeElt (hK : Nat.card K = 2) {w : adjointGroup .F4 K}
    (hw : w * nodeElt K = nodeElt K * w) (hw2 : w ^ 2 = 1) : w ∈ C3Levi K := by
  have hX := centralizer_nonsplit zpowers_nodeElt_le (Subgroup.isCyclic_zpowers _)
    (card_zpowers_nodeElt hK)
  have hwC :
      w ∈ Subgroup.centralizer (Subgroup.zpowers (nodeElt K) : Set (adjointGroup .F4 K)) := by
    rw [← centralizer_singleton_eq_zpowers, Subgroup.mem_centralizer_singleton_iff]
    exact hw
  obtain ⟨y, hy, d, hd, rfl⟩ := exists_mul_of_mem_centralizer_nonsplit zpowers_nodeElt_le
    (Subgroup.isCyclic_zpowers _) (card_zpowers_nodeElt hK) hwC
  have hyd : Commute y d := (Subgroup.mem_centralizer_iff.1 (hX.2.2 hy) d hd).symm
  have h2 : y ^ 2 * d ^ 2 = 1 := by
    rw [← hyd.mul_pow]
    exact hw2
  have hy2D : y ^ 2 ∈ C3Levi K := by
    rw [eq_inv_of_mul_eq_one_left h2]
    exact inv_mem (pow_mem hd 2)
  have hy2 : y ^ 2 = 1 := Subgroup.disjoint_def.1 hX.2.1 (pow_mem hy 2) hy2D
  have hy3 : y ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, nodeElt_pow_three,
      one_zpow]
  have hy1 : y = 1 := by
    calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
      _ = 1 := by rw [hy3, hy2, inv_one, mul_one]
  rw [hy1, one_mul]
  exact hd

theorem exists_endNodeRoot_of_le_map_C3Levi (hK : Nat.card K = 2)
    (γ : adjointGroup .F4 K ≃* adjointGroup .F4 K) {A : Subgroup (adjointGroup .F4 K)}
    (hAD : A ≤ (C3Levi K).map γ.toMonoidHom) (hA : IsElemAbelian 3 A)
    (h27 : 3 ^ 3 ≤ Nat.card A) :
    ∃ t, TableBOrth.IsEndNode A t ∧
      GGBigLayer (LargeEvenLayer (Subgroup.centralizer ({t} : Set (adjointGroup .F4 K)))) ∧
      ∃ U : Subgroup (adjointGroup .F4 K),
        U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set (adjointGroup .F4 K))) ∧ U ≠ ⊥ ∧
          IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set (adjointGroup .F4 K)) := by
  have hD : ∀ a ∈ A, γ.symm a ∈ C3Levi K := by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := hAD ha
    simpa using hd
  set A' := A.map γ.symm.toMonoidHom with hA'
  have hA'D : A' ≤ C3Levi K := by
    rintro _ ⟨a, ha, rfl⟩
    exact hD a ha
  have hA'c : 3 ^ 3 ≤ Nat.card A' := by
    rw [hA', Subgroup.card_map_of_injective γ.symm.injective]
    exact h27
  obtain ⟨h, hh⟩ :=
    exists_conj_nodeElt_mem_of_le_C3Levi hK hA'D (TableB.isElemAbelian_map hA _) hA'c
  set α : adjointGroup .F4 K ≃* adjointGroup .F4 K := (MulAut.conj h).trans γ with hα
  have hαA : α (nodeElt K) ∈ A := by
    obtain ⟨a, ha, hae⟩ := hh
    have e : α (nodeElt K) = a := by
      show γ (h * nodeElt K * h⁻¹) = a
      rw [← hae]
      simp
    rw [e]
    exact ha
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨ht1, ht2, ht3, ht4⟩ := endNodeAt_of_mulEquiv hK α hAc hαA
  have hlay : LargeEvenLayer (Subgroup.centralizer ({α (nodeElt K)} : Set (adjointGroup .F4 K))) =
      (C3Levi K).map α.toMonoidHom := by
    rw [← TableBSymp.map_centralizer_singleton, largeEvenLayer_map_of_injective _ α.injective,
      (layer_centralizer_nodeElt hK).1]
  have hcomm : ∀ d ∈ C3Levi K, TableBF4Two.rootInv K * d = d * TableBF4Two.rootInv K :=
    fun d hd => commute_of_mem_highestRootRankOne_of_mem_C3Levi rootInv_mem_highestRootRankOne hd
  have hu2 : TableBF4Two.rootInv K * TableBF4Two.rootInv K = 1 := by
    rw [← pow_two]
    exact TableBF4Two.rootInv_sq
  have hw : h⁻¹ * TableBF4Two.rootInv K * h ∈ C3Levi K := by
    have hc := hcomm _ (hA'D hh)
    refine mem_C3Levi_of_commute_nodeElt hK ?_ ?_
    · calc h⁻¹ * TableBF4Two.rootInv K * h * nodeElt K
          = h⁻¹ * (TableBF4Two.rootInv K * (h * nodeElt K * h⁻¹)) * h := by group
        _ = h⁻¹ * (h * nodeElt K * h⁻¹ * TableBF4Two.rootInv K) * h := by rw [hc]
        _ = nodeElt K * (h⁻¹ * TableBF4Two.rootInv K * h) := by group
    · calc (h⁻¹ * TableBF4Two.rootInv K * h) ^ 2
          = h⁻¹ * (TableBF4Two.rootInv K * TableBF4Two.rootInv K) * h := by rw [pow_two]; group
        _ = 1 := by rw [hu2]; group
  have hγu : γ (TableBF4Two.rootInv K) ∈ (C3Levi K).map α.toMonoidHom := by
    refine ⟨h⁻¹ * TableBF4Two.rootInv K * h, hw, ?_⟩
    show γ (h * (h⁻¹ * TableBF4Two.rootInv K * h) * h⁻¹) = γ (TableBF4Two.rootInv K)
    congr 1
    group
  have hv1 : γ (TableBF4Two.rootInv K) ≠ 1 := fun h1 =>
    TableBF4Two.rootInv_ne_one (γ.injective (h1.trans (map_one γ).symm))
  have hv2 : γ (TableBF4Two.rootInv K) ^ 2 = 1 := by
    rw [← map_pow, TableBF4Two.rootInv_sq, map_one]
  refine ⟨α (nodeElt K), ⟨ht1, ht2, ht3, ht4⟩, Or.inr ?_,
    Subgroup.zpowers (γ (TableBF4Two.rootInv K)), ?_, Subgroup.zpowers_ne_bot.2 hv1, ?_, ?_⟩
  · rw [hlay, Subgroup.card_map_of_injective α.injective, card_C3Levi_two hK]
    norm_num
  · rw [hlay]
    exact Subgroup.zpowers_le.2 hγu
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1, pow_one])
  · intro a ha
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [← centralizer_singleton_eq_zpowers, Subgroup.mem_centralizer_singleton_iff]
    have e := congrArg γ (hcomm _ (hD a ha))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at e
    exact e.symm

theorem ggEndNodeRootEltBig_adjointF4Two (hK : Nat.card K = 2) :
    GGEndNodeRootEltBig 3 3 (adjointGroup .F4 K) := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  intro A hA _ h27 hloc
  obtain ⟨V, hV, hV2, hAV⟩ := hloc
  have hAp : IsPGroup 3 A := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hA.2 _ x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_le_C3Levi_or_B3Levi hK hV hV2 hAV hAp h27
  have hγ : ∃ γ : adjointGroup .F4 K ≃* adjointGroup .F4 K,
      A ≤ (C3Levi K).map γ.toMonoidHom := by
    rcases hg with hC | hB
    · exact ⟨(MulAut.conj g).symm, fun a ha =>
        ⟨MulAut.conj g a, hC ⟨a, ha, rfl⟩, (MulAut.conj g).symm_apply_apply a⟩⟩
    · refine ⟨(graphAutF4 K).trans (MulAut.conj g).symm, fun a ha => ?_⟩
      have h1 := hB ⟨a, ha, rfl⟩
      rw [← map_graphAutF4_C3Levi] at h1
      obtain ⟨d, hd, hde⟩ := h1
      refine ⟨d, hd, ?_⟩
      show (MulAut.conj g).symm (graphAutF4 K d) = a
      rw [show graphAutF4 K d = MulAut.conj g a from hde]
      exact (MulAut.conj g).symm_apply_apply a
  obtain ⟨γ, hγA⟩ := hγ
  obtain ⟨t, hend, hbig, U, hUL, hU1, hU2, hAU⟩ :=
    exists_endNodeRoot_of_le_map_C3Levi hK γ hγA hA h27
  exact ⟨t, hend, fun _ => hbig, U, hUL, hU1, hU2, hAU⟩

theorem ggEndNodeRoot_F4Two (hK : Nat.card K = 2) :
    GGEndNodeRoot 3 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) :=
  ggEndNodeRoot_of_eltBig ggIE_outdiagPrime_F4Two (TableBF4.center_recipeGroup_eq_bot K)
    (ggEndNodeRootEltBig_of_mulEquiv (TableBF4.recipeEquiv K).symm
      (ggEndNodeRootEltBig_adjointF4Two hK))

end Adjoint

section Main


theorem ggF4TwoRootAsInput_holds : GGF4TwoRootAsInput := by
  intro K _ _ hK
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  exact ggEndNodeRootAs_of_root (ggEndNodeRoot_F4Two hK)

end Main

end CFSG.StandardType.F4RootAs
