module

public import CFSG.RankThree.PartOne.F106.OddRadRadical
public import CFSG.RankThree.PartOne.KLR.Final
public import CFSG.RankThree.PartOne.TCF.TitsFixed
public import CFSG.RankThree.PartOne.F106.OddRadTools

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.Sec66T (innerAut fixSub fixSubEquiv)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

set_option linter.unusedSectionVars false

theorem oddRad_ree_inner {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = 5) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual
      ↥(Subgroup.centralizer ({x} : Set (ReeTag.F4.reeGamma K a)))))) := by
  exact odd_card_radical_residual_of_solvable_normal fun V hV hs =>
    KLR.largeReeSolvOdd a ha K hK 5 (by norm_num) (by norm_num) x hx V hV hs

theorem oddRadConcl_ree_outer {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : MulAut ↥(ReeTag.F4.reeGamma K a)) (hβ : orderOf β = 5)
    (hβinn : β ∉ innerAut ↥(ReeTag.F4.reeGamma K a)) :
    OddRadConcl ↥(ReeTag.F4.reeGamma K a) β := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  have : Fact (5 : ℕ).Prime := ⟨hp⟩
  have hβp : β ^ 5 = 1 := by
    have := pow_orderOf_eq_one β
    rwa [hβ] at this
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β'⟩, hxβ, -⟩ := hNF β
  have hΨβ : Ψ ⟨x, β'⟩ = β := by rw [hΨ x β']; exact hxβ.symm
  let Θ : MulAut (ReeTag.F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘβ : Θ β = β' := by
    show SemidirectProduct.rightHom (Ψ.symm β) = β'
    rw [← hΨβ, MulEquiv.symm_apply_apply]
    rfl
  have hβ'p : β' ^ 5 = 1 := by rw [← hΘβ, ← map_pow, hβp, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := by
    rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ'1 : β' ≠ 1 := by
    intro h
    apply hβinn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβ'ord : orderOf β' = 5 := orderOf_eq_prime hβ'p hβ'1
  obtain ⟨g, hg⟩ := RF4.largeReeFieldAutCoset a ha K hK 5 hp le_rfl β' hβ'ord β hβp ⟨x, hxβ⟩
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
  unfold OddRadConcl
  change Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(fixSub β))))
  by_cases hb : 1 ≤ b
  · obtain ⟨-, hcommu, -, -⟩ := ReeTag.ree_generic_fixed_group_perfect ReeTag.F4 b hb
      (fixSubfield β') hbcard
    have hsimple := Sec66T.isSimpleGroup_reeGamma_F4' hb hbcard
    have hnab : ∃ u v : ReeTag.F4.reeGamma (fixSubfield β') b, u * v ≠ v * u :=
      Sec66T.exists_noncomm_of_perfect hcommu
    rw [card_solvableRadical_perfectResidual_eq ε, card_radical_residual_of_simple_nonabelian hnab]
    exact odd_one
  · have hb0 : b = 0 := by omega
    subst hb0
    have hk2 : Nat.card (fixSubfield β') = 2 := by simpa using hbcard
    obtain ⟨eN, -, -⟩ := TCF.tits_of_fixed hk2 ε
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
    have := hsN
    rw [card_radical_residual_of_simple_commutator hsN (isPerfect_of_simple_nonabelian hnc)]
    exact odd_one

theorem oddRadConcl_ree {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : MulAut ↥(ReeTag.F4.reeGamma K a)) (hβ : orderOf β = 5) :
    OddRadConcl ↥(ReeTag.F4.reeGamma K a) β := by
  classical
  by_cases hinn : β ∈ innerAut ↥(ReeTag.F4.reeGamma K a)
  · obtain ⟨t, rfl⟩ := hinn
    have hsimple := Sec66T.isSimpleGroup_reeGamma_F4' ha hK
    obtain ⟨-, hcommu, -, -⟩ := ReeTag.ree_generic_fixed_group_perfect ReeTag.F4 a ha K hK
    have hnab : ∃ u v : ReeTag.F4.reeGamma K a, u * v ≠ v * u :=
      Sec66T.exists_noncomm_of_perfect hcommu
    have hZ := center_eq_bot_of_simple_nonabelian hnab
    have htord : orderOf t = 5 := by rw [← orderOf_conj_eq hZ t]; exact hβ
    unfold OddRadConcl
    rw [eqLocus_conj_eq_centralizer t]
    exact oddRad_ree_inner ha hK t htord
  · exact oddRadConcl_ree_outer ha hK β hβ hinn

theorem oddRadAt_smallModel_twistedF4 : OddRadAt (SmallModel .twistedF4) := by
  intro T _ _ _ hS β hβ
  obtain ⟨n, f, hadm, hM, -⟩ := hS
  obtain ⟨-, hRT⟩ := Sec66T.lieModel_twistedF4_iff.mp hM
  obtain ⟨hadm', a, hfa, hmodel⟩ := hRT
  have hf3 : 3 ≤ f := hadm'.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  have hX := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier T 2 f ⟨hadm', a, hfa, hmodel⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hX.2.2.2.2.2 a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  exact oddRadConcl_of_mulEquiv E (fun β' hβ' => oddRadConcl_ree ha hK' β' hβ') β hβ

end CFSG.RankThree.PartOne.F106
