module

public import CFSG.RankThree.PartOne.FOC.OuterLayer
public import CFSG.RankThree.PartOne.TCF.TitsFixed

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.Sec66T (innerAut fixSub fixSubEquiv)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)


theorem outerComp_ree {a p : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime) (hp5 : 5 ≤ p) :
    OuterComp p ↥(ReeTag.F4.reeGamma K a) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  refine outerComp_of_fixed_simple_layer ?_
  intro β hβp hβinn
  have hβ1 : β ≠ 1 := fun h => hβinn (h ▸ Subgroup.one_mem _)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β'⟩, hxβ, -⟩ := hNF β
  have hΨβ : Ψ ⟨x, β'⟩ = β := by rw [hΨ x β']; exact hxβ.symm
  let Θ : MulAut (ReeTag.F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘβ : Θ β = β' := by
    show SemidirectProduct.rightHom (Ψ.symm β) = β'
    rw [← hΨβ, MulEquiv.symm_apply_apply]
    rfl
  have hβ'p : β' ^ p = 1 := by
    rw [← hΘβ, ← map_pow, hβp, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := by
    rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ'1 : β' ≠ 1 := by
    intro h
    apply hβinn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβ'ord : orderOf β' = p := orderOf_eq_prime hβ'p hβ'1
  obtain ⟨g, hg⟩ := RF4.largeReeFieldAutCoset a ha K hK p hp hp5 β' hβ'ord β hβp ⟨x, hxβ⟩
  have hcg : MulAut.congr (MulAut.conj g)⁻¹ β = ReeTag.F4.reeGammaFieldAut K a β' := by
    have : (MulAut.conj g)⁻¹ * β * ((MulAut.conj g)⁻¹)⁻¹ =
        ReeTag.F4.reeGammaFieldAut K a β' := by
      rw [hg]
      group
    exact this
  obtain ⟨b, -, hbcard, hchar, ⟨eC⟩⟩ := Sec66T.reeF4_fixed_data ha hK hp (by omega) hβ'ord
  have : Finite (fixSubfield β') := Subtype.finite
  let ε : ↥(fixSub β) ≃* ReeTag.F4.reeGamma (fixSubfield β') b :=
    ((fixSubEquiv (MulAut.conj g)⁻¹ β).trans (MulEquiv.subgroupCongr (by rw [hcg]))).trans eC
  by_cases hb : 1 ≤ b
  ·
    obtain ⟨-, hcommu, -, -⟩ := ReeTag.ree_generic_fixed_group_perfect ReeTag.F4 b hb
      (fixSubfield β') hbcard
    have hsimple := Sec66T.isSimpleGroup_reeGamma_F4' hb hbcard
    have hsF : IsSimpleGroup ↥(fixSub β) := ε.isSimpleGroup
    have hnab : ∃ u v : ReeTag.F4.reeGamma (fixSubfield β') b, u * v ≠ v * u :=
      Sec66T.exists_noncomm_of_perfect hcommu
    obtain ⟨u, v, huv⟩ := hnab
    refine ⟨⊤, Subgroup.topEquiv.isSimpleGroup, ?_, le_top, fun y _ => Subgroup.mem_top y⟩
    refine ⟨⟨ε.symm u, Subgroup.mem_top _⟩, ⟨ε.symm v, Subgroup.mem_top _⟩, fun h => huv ?_⟩
    apply ε.symm.injective
    rw [map_mul, map_mul]
    exact congrArg Subtype.val h
  ·
    have hb0 : b = 0 := by omega
    subst hb0
    have hk2 : Nat.card (fixSubfield β') = 2 := by simpa using hbcard
    obtain ⟨eN, hodd, -⟩ := TCF.tits_of_fixed hk2 ε
    have hsN : IsSimpleGroup ↥(commutator ↥(fixSub β)) := by
      have := Sporadic.Schreier.Tits.titsD_simple
      exact eN.isSimpleGroup
    have hnc : ∃ u v : ↥(commutator ↥(fixSub β)), u * v ≠ v * u := by
      by_contra hcon
      push Not at hcon
      have : IsSimpleGroup ↥(commutator ↥(fixSub β)) := hsN
      let _ : CommGroup ↥(commutator ↥(fixSub β)) :=
        { (inferInstance : Group ↥(commutator ↥(fixSub β))) with mul_comm := hcon }
      have hpr := IsSimpleGroup.prime_card (α := ↥(commutator ↥(fixSub β)))
      rw [Nat.card_congr eN.toEquiv, Sporadic.Schreier.Tits.card_titsD] at hpr
      exact absurd hpr (by norm_num)
    exact ⟨commutator ↥(fixSub β), hsN, hnc, le_rfl,
      fun y hy => hodd y p (hp.odd_of_ne_two (by omega)) hy⟩

end CFSG.RankThree.PartOne.FOC
