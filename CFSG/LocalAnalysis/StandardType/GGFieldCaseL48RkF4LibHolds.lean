module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48RkF4Facts
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoEndNode
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OuterTwoExceptional
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc
import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsEndNode
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SeitzReduction.F4Pilot

private theorem ggL48_isElemAbelian_range {A J : Type*} [Group A] [Group J] (Φ : A →* J)
    (hcomm : ∀ x y : A, x * y = y * x) (hexp : ∀ x : A, x ^ 3 = 1) :
    IsElemAbelian 3 Φ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, hcomm x y]
  · intro z hz
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hz
    rw [← map_pow, hexp x, map_one]

private theorem ggL48_zmod_three_pow_three (a : Multiplicative (ZMod 3)) : a ^ 3 = 1 := by
  have h3 : ∀ y : ZMod 3, 3 • y = 0 := by decide
  rw [← ofAdd_toAdd a, ← ofAdd_nsmul, h3, ofAdd_zero]

theorem ggF4TwoCentre_holds :
    GGF4TwoCentre := by
  intro R _ _ hR L' _ _ θ hperf
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc.exists_mulEquiv_adjointGroup hR
  set ψ : L' →* TableBF4.RecipeGroup K :=
    (((TableBF4.recipeEquiv K).symm.toMonoidHom.comp e.toMonoidHom).comp θ.toMonoidHom).comp
      (QuotientGroup.mk' (Subgroup.center L')) with hψ
  have hker : ψ.ker = Subgroup.center L' := by
    rw [hψ]
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center L'))
      (((TableBF4.recipeEquiv K).symm.toMonoidHom.comp e.toMonoidHom).comp θ.toMonoidHom)
      (((TableBF4.recipeEquiv K).symm.injective.comp e.injective).comp θ.injective),
      QuotientGroup.ker_mk']
  have hsurj : Function.Surjective ψ := by
    rw [hψ]
    exact (((TableBF4.recipeEquiv K).symm.surjective.comp e.surjective).comp θ.surjective).comp
      (QuotientGroup.mk'_surjective (Subgroup.center L'))
  have h := TableBF4Two.center_eq_ker_card_le_two (K := K) hK (ψ := ψ) hsurj hker.le hperf
  rw [h.1]
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hcases : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 2 := by omega
  rcases hcases with hh | hh <;> rw [hh] <;> norm_num

theorem ggF4TwoOutTwo_holds :
    GGF4TwoOutTwo := by
  intro R _ _ hR T _ hdisj
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc.exists_mulEquiv_adjointGroup hR
  obtain ⟨hfin, hle2⟩ := SeitzReduction.SeitzQ2.card_outer_le_two_of_mulEquiv_F4_two hK e
  haveI : Finite (Outer R) := hfin
  set φ : T →* Outer R := (QuotientGroup.mk' (inner R)).comp T.subtype with hφ
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    exact Subtype.ext (hdisj x.1 x.2 hx)
  exact (Nat.card_le_card_of_injective φ hinj).trans hle2

theorem ggF4TwoRankFour_holds :
    GGF4TwoRankFour := by
  intro R _ _ hR
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc.exists_mulEquiv_adjointGroup hR
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime (p := 2) (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Finite (adjointGroup .F4 K) := Subtype.finite
  set E : Subgroup (adjointGroup .F4 K) := (TableBF4Two.torus3 K).range with hE
  have hEea : IsElemAbelian 3 E := by
    rw [hE]
    exact ggL48_isElemAbelian_range (TableBF4Two.torus3 K) (fun x y => mul_comm x y)
      (fun x => by funext i; exact ggL48_zmod_three_pow_three (x i))
  have hEcard : Nat.card E = 3 ^ 3 := by
    rw [hE]
    exact TableBF4TwoInputs.card_range_torus3
  have hEle : E ≤ C3Levi K := by
    rw [hE]
    exact TableBF4TwoInputs.range_torus3_le_C3Levi
  have hX := centralizer_nonsplit TableBF4TwoInputs.zpowers_nodeElt_le
    (Subgroup.isCyclic_zpowers _) (TableBF4TwoInputs.card_zpowers_nodeElt hK)
  have hzE : TableBF4TwoInputs.nodeElt K ∉ E := fun hmem =>
    TableBF4TwoInputs.nodeElt_ne_one
      (Subgroup.disjoint_def.1 hX.2.1 (Subgroup.mem_zpowers _) (hEle hmem))
  have hz : ∀ x ∈ E, x * TableBF4TwoInputs.nodeElt K = TableBF4TwoInputs.nodeElt K * x :=
    fun x hx => Subgroup.mem_centralizer_iff.1
      (hX.2.2 (Subgroup.mem_zpowers (TableBF4TwoInputs.nodeElt K))) x (hEle hx)
  obtain ⟨hA₀ea, hA₀card⟩ := isElemAbelian_sup_zpowers_of_card (G := adjointGroup .F4 K)
    (E := E) (k := 3) (z := TableBF4TwoInputs.nodeElt K) Nat.prime_three hEea hEcard
    TableBF4TwoInputs.nodeElt_pow_three hzE hz
  refine ⟨(E ⊔ Subgroup.zpowers (TableBF4TwoInputs.nodeElt K)).map e.symm.toMonoidHom,
    TableB.isElemAbelian_map hA₀ea e.symm.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hA₀card]

theorem ggF4TwoInvolutionCommutes_holds :
    GGF4TwoInvolutionCommutes := by
  intro R _ _ hR
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc.exists_mulEquiv_adjointGroup hR
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime (p := 2) (by rw [← Nat.card_eq_fintype_card, hK])
  have hcomm : Commute (TableBF4Two.torusGen K 0) (TableBF4Two.rootInv K) :=
    TableBF4Two.commute_rho (TableBF4Two.castSucc_ne_three 0) (uSL 1 * vSL 1) (uSL 1)
  refine ⟨e.symm (TableBF4Two.torusGen K 0), ?_, ?_, e.symm (TableBF4Two.rootInv K), ?_, ?_, ?_⟩
  · rw [← map_pow, TableBF4Two.torusGen_pow_three, map_one]
  · intro h
    exact TableBF4Two.torusGen_ne_one 0
      (e.symm.injective (h.trans (map_one e.symm).symm))
  · rw [← map_pow, TableBF4Two.rootInv_sq, map_one]
  · intro h
    exact TableBF4Two.rootInv_ne_one (e.symm.injective (h.trans (map_one e.symm).symm))
  · simpa only [map_mul] using congrArg (fun x => e.symm x) hcomm.eq

end CFSG.StandardType

end
