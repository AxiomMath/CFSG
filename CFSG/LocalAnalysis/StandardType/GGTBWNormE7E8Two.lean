module

public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGTBWNormSpSix
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLowRank
public import CFSG.LocalAnalysis.StandardType.GGTBWNormSmall
public import CFSG.LocalAnalysis.StandardType.GGTBWNormClassical
public import CFSG.LocalAnalysis.StandardType.GGTBWNormSymplectic
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearNonsplit
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearSplit
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearPrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearTwicePrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearThreePrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearFourPrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearNineThree
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearThreeShears
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearW5
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryTwicePrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6Split
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6Five
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6ThreeLabel
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE7Plus
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitarySplit
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryNonsplit
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitarySingular
public import CFSG.LocalAnalysis.StandardType.GGTBWNormTwE6
public import CFSG.LocalAnalysis.StandardType.GGTBWNormOrth
public import CFSG.LocalAnalysis.StandardType.GGTBWNormOrthFour
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8Four
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6Relative
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8Split
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8Five
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8QuarticFive
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE7Split
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE7Cyclotomic
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8Plus
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8PowerMap
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8PhiThree
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8Three
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE7ThreeToral
public import CFSG.LocalAnalysis.StandardType.GGTBWNormExcRankTwo
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8FivePlus
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryThreePrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6PhiThree
public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearFrob
public import CFSG.LocalAnalysis.StandardType.GGTBWNormFormFrob
public import CFSG.LocalAnalysis.StandardType.GGTBWNormTwE6PhiSix
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryFrob
public import CFSG.LocalAnalysis.StandardType.GGTBWNormOrthPhiFour
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryFourPrime
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryAllShears
public import CFSG.LocalAnalysis.StandardType.GGTBWNormUnitaryPhiFour
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.Mathlib.GroupTheory.PerfectCentralAut
public import CFSG.LocalAnalysis.StandardType.GGRawTorusPClassical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem forall_mulAut_eq_conj_adjoint_E7_E8_two {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∀ β : MulAut (adjointGroup τ K), ∃ g : adjointGroup τ K, β = MulAut.conj g := by
  intro β
  have hK' : Nat.card K = 2 ^ 1 := by simpa using hK
  obtain ⟨⟨g, σ⟩, h, -⟩ :=
    (even_E7_E8_exact_inner_field_automorphism_normal_form (by omega) K hK' τ hτ).1 β
  have hσ : σ = RingEquiv.refl K := by
    ext x
    exact ringEquiv_eq_refl_of_card_two hK σ x
  subst hσ
  refine ⟨g, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have hmap : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (x : ModGL τ K) =
      (x : ModGL τ K) := by
    exact Units.ext (CFSG.LieType.Chevalley.entrywise_id _)
  simpa only [hmap, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h x

theorem forall_mulAut_eq_conj_of_equiv_E7_E8_two {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {R : Type} [Group R] (e : R ≃* adjointGroup τ K)
    {L : Type} [Group L] (ψ : L →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤) :
    ∀ α : MulAut L, ∃ l : L, α = MulAut.conj l := by
  have hR : ∀ β : MulAut R, ∃ r : R, β = MulAut.conj r := by
    intro β
    obtain ⟨g, hg⟩ := forall_mulAut_eq_conj_adjoint_E7_E8_two hτ hK (MulAut.congr e β)
    refine ⟨e.symm g, ?_⟩
    apply (MulAut.congr e).injective
    have hconj : MulAut.congr e (MulAut.conj (e.symm g)) = MulAut.conj g := by
      apply MulEquiv.ext
      intro x
      simp [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply]
    rw [hconj]
    exact hg
  have hZ : Subgroup.center R = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro r hr
    apply e.injective
    have heZ : e r ∈ Subgroup.center (adjointGroup τ K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨r', rfl⟩ := e.surjective g
      simpa only [← map_mul] using congrArg e (Subgroup.mem_center_iff.mp hr r')
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at heZ
    simpa using heZ
  exact CFSG.forall_mulAut_eq_conj_of_forall_mulAut_eq_conj hperf ψ hψ hker hZ hR

theorem ggTorusWNormSC_recipe_E7_E8_two {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {p : ℕ} :
    GGTorusWNormSC p (TableBExc.RecipeGroup τ K) (TableBExc.RecipeID τ K) := by
  apply ggTorusWNormSC_of_forall_mulAut_eq_conj
  intro L _ _ ψ hψ hker hperf
  exact forall_mulAut_eq_conj_of_equiv_E7_E8_two hτ hK (TableBExc.recipeEquiv τ K)
    ψ hψ hker hperf

theorem largeEvenLabelAll_wnorm_E7_E8_two {lab : LargeEvenLabel}
    (hτ : lab.tag = .E7 ∨ lab.tag = .E8) (hn : lab.n = 1) {p : ℕ} :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, rank, n⟩
  dsimp only at hτ hn ⊢
  subst hn
  rcases hτ with rfl | rfl
  · intro Q hQ
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_recipe_E7_E8_two (Or.inl rfl) (by simpa using hK)
  · intro Q hQ
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_recipe_E7_E8_two (Or.inr rfl) (by simpa using hK)



theorem ggTBWNormLabelFull_of_rest (h : GGTBWNormLabelRest) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      ¬ GGTBWExcl lab → ¬ (lab.tag = .E8 ∧ p = 3) → ¬ (lab.tag = .E6 ∧ p = 3) →
      ¬ (lab.tag = .E7 ∧ p = 3) → lab.tag ≠ .twE6 →
        LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  intro p hp hp2 lab hlab hexcl he8p3 he6p3 he7p3 htw6
  by_cases hw3split : GGTBWNormW3SplitLabel p lab
  · exact largeEvenLabelAll_wnorm_linear_w3 hw3split
  by_cases hlin9 : lab.tag = .A ∧ p = 3 ∧ lab.rank + 1 = 9 ∧ 3 ∣ 2 ^ lab.n - 1
  · rcases hlin9 with ⟨ht, rfl, hd, hq⟩
    exact largeEvenLabelAll_wnorm_linear_nine_three ht hd hq
  by_cases htwo : (lab.tag = .E7 ∨ lab.tag = .E8) ∧ lab.n = 1
  · exact largeEvenLabelAll_wnorm_E7_E8_two htwo.1 htwo.2
  · by_cases hsp : (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ lab.n = 1
    · exact largeEvenLabelAll_wnorm_symplectic_two hsp.1 hsp.2.1 hsp.2.2
    · by_cases hlow : (lab.tag = .A ∧ lab.rank ≤ 2) ∨
        ((lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 2)
      · exact largeEvenLabelAll_wnorm_low_rank hlab hlow hp hp2
      · by_cases hsmall : GGTableBNbrInnerNineSmallLabel p lab
        · exact largeEvenLabelAll_wnorm_nineSmall hp hp2 hlab hsmall
        · by_cases hcl : GGTableBNbrInnerNineClassicalLabel p lab
          · exact largeEvenLabelAll_wnorm_nineClassical hp hp2 hlab hcl
          · by_cases hspt : (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
                (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
            · exact largeEvenLabelAll_wnorm_symplectic hp hp2 hspt.1 hspt.2.1 hspt.2.2
            · by_cases hln : (lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧
                  3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1
              · exact largeEvenLabelAll_wnorm_linear_nonsplit hp hp2 hlab.1 hln.1 hln.2.1 hln.2.2
              · by_cases hE6 : lab.tag = .E6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1
                · by_cases hpFive : p = 5
                  · subst p
                    exact E6WNorm.largeEvenLabelAll_wnorm_E6_five hE6.1 hE6.2.2
                  · have hpSix : p ≠ 6 := by
                      rintro rfl
                      exact (by decide : ¬ Nat.Prime 6) hp
                    exact E6WNorm.largeEvenLabelAll_wnorm_E6_split hp (by omega) hE6.1 hE6.2.2
                · by_cases hus : (lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
                      3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1
                  · exact largeEvenLabelAll_wnorm_unitary_split hp hp2 hlab.1 hus.1 hus.2.1 hus.2.2
                  · by_cases htwE6 : lab.tag = .twE6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n + 1
                    · exact TwE6WNorm.largeEvenLabelAll_wnorm_twE6_of_ge_five hp htwE6.2.1 htwE6.1 hlab.1 htwE6.2.2
                    · by_cases hun : (lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
                          3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.rank + 1
                      · exact largeEvenLabelAll_wnorm_unitary_nonsplit hp hp2 hlab.1 hun.1
                          hun.2.1 hun.2.2.1 hun.2.2.2
                      · by_cases htri : lab.tag = .triD4
                        · exact largeEvenLabelAll_wnorm_triality hp hp2 hlab htri
                        · by_cases hos : GGOrthSignedLabel p lab
                          · exact largeEvenLabelAll_wnorm_orth_signed hp hp2 hos
                          · by_cases hrelBoth :
                                (lab.tag = .twE6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1) ∨
                                (lab.tag = .E6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n + 1)
                            · rcases hrelBoth with hrel | hrel
                              · exact largeEvenLabelAll_wnorm_twE6_relative hp hrel.2.1 hlab
                                  hrel.1 hrel.2.2
                              · exact largeEvenLabelAll_wnorm_E6_relative hp hrel.2.1 hlab
                                  hrel.1 hrel.2.2
                            · have hrel : ¬ (lab.tag = .twE6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1) :=
                                fun h => hrelBoth (Or.inl h)
                              have hrelE6 : ¬ (lab.tag = .E6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n + 1) :=
                                fun h => hrelBoth (Or.inr h)
                              by_cases hls : (lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧
                                    3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ lab.rank + 1
                              · exact largeEvenLabelAll_wnorm_linear_split hp hp2 hls.1
                                  hls.2.1 hls.2.2.1 hls.2.2.2
                              · by_cases heo : GGOrthEvenOddLabel p lab
                                · exact largeEvenLabelAll_wnorm_orth_evenOdd hp hp2 heo
                                · by_cases hunp : lab.tag = .twA ∧ 5 ≤ p ∧
                                      lab.rank + 1 = p ∧ p ∣ 2 ^ lab.n + 1
                                  · exact largeEvenLabelAll_wnorm_unitary_singular_prime hp
                                      hunp.2.1 hlab.1 hunp.1 hunp.2.2.1 hunp.2.2.2
                                  · by_cases hlnp : lab.tag = .A ∧ 5 ≤ p ∧
                                        lab.rank + 1 = p ∧ p ∣ 2 ^ lab.n - 1
                                    · exact largeEvenLabelAll_wnorm_linear_singular_prime hp
                                        hlnp.2.1 hlnp.1 hlnp.2.2.1 hlnp.2.2.2
                                    · by_cases he8 : lab.tag = .E8 ∧ 7 ≤ p ∧ p ∣ 2 ^ lab.n - 1
                                      · exact E8WNorm.largeEvenLabelAll_wnorm_E8_split hp he8.2.1
                                          he8.1 he8.2.2
                                      · by_cases hE7 : lab.tag = .E7 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1
                                        · exact E7WNorm.largeEvenLabelAll_wnorm_E7_split hp
                                            hE7.2.1 hlab hE7.1 hE7.2.2
                                        · by_cases he8p : lab.tag = .E8 ∧ 7 ≤ p ∧ p ∣ 2 ^ lab.n + 1
                                          · exact E8PlusWNorm.largeEvenLabelAll_wnorm_E8_plus hp
                                              he8p.2.1 he8p.1 he8p.2.2
                                          · by_cases hE7p :
                                                lab.tag = .E7 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n + 1
                                            · exact largeEvenLabelAll_wnorm_E7_plus hE7p.1 hp
                                                hE7p.2.1 hE7p.2.2
                                            · by_cases he8q5 : lab.tag = .E8 ∧ p = 5 ∧
                                                  5 ∣ (2 ^ lab.n) ^ 2 + 1
                                              · rcases he8q5 with ⟨htag, hp5, h5⟩
                                                subst p
                                                exact E8WNorm.largeEvenLabelAll_wnorm_E8_quartic_five htag h5
                                              · by_cases hRee : lab.tag = .twF4
                                                · exact largeEvenLabelAll_wnorm_largeRee hp hp2 hlab hRee
                                                · by_cases hvac :
                                                      (lab.tag = .E8 ∧ ¬ p ∣ (2 ^ lab.n) ^ 4 - 1 ∧
                                                        ¬ p ∣ (2 ^ lab.n) ^ 6 - 1) ∨
                                                      (lab.tag = .E7 ∧ ¬ p ∣ (2 ^ lab.n) ^ 6 - 1) ∨
                                                      (lab.tag = .E6 ∧ ¬ p ∣ (2 ^ lab.n) ^ 2 - 1 ∧
                                                        ¬ p ∣ (2 ^ lab.n) ^ 3 - 1) ∨
                                                      (lab.tag = .twE6 ∧ ¬ p ∣ (2 ^ lab.n) ^ 2 - 1 ∧
                                                        ¬ p ∣ (2 ^ lab.n) ^ 3 + 1)
                                                  · exact ExcRankTwoWNorm.largeEvenLabelAll_wnorm_exc_rankTwo
                                                      hp hp2 hlab hvac
                                                  · by_cases hee : lab.tag = .D ∧ 6 ≤ lab.rank ∧
                                                        Even lab.rank ∧
                                                        (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
                                                    · exact largeEvenLabelAll_wnorm_orth_evenEven
                                                        hp hp2 hee
                                                    by_cases hd4 : lab.tag = .D ∧ lab.rank = 4 ∧
                                                        (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
                                                    · exact largeEvenLabelAll_wnorm_orth_four
                                                        hp hp2 hd4
                                                    by_cases hl2p : lab.tag = .A ∧
                                                        lab.rank + 1 = 2 * p ∧ p ∣ 2 ^ lab.n - 1
                                                    · exact largeEvenLabelAll_wnorm_linear_twice_prime
                                                        hp hp2 hl2p.1 hl2p.2.1 hl2p.2.2
                                                    by_cases hu2p : lab.tag = .twA ∧
                                                        lab.rank + 1 = 2 * p ∧ p ∣ 2 ^ lab.n + 1
                                                    · exact largeEvenLabelAll_wnorm_unitary_twice_prime
                                                        hp hp2 hlab.1 hu2p.1 hu2p.2.1 hu2p.2.2
                                                    by_cases he8six : lab.tag = .E8 ∧ p ≠ 3 ∧
                                                        p ∣ (2 ^ lab.n) ^ 2 - 2 ^ lab.n + 1
                                                    · exact E8PowerWNorm.largeEvenLabelAll_wnorm_E8_six
                                                        hp hp2 he8six.2.1 hlab he8six.1 he8six.2.2
                                                    by_cases he8q : lab.tag = .E8 ∧ 7 ≤ p ∧
                                                        p ∣ (2 ^ lab.n) ^ 2 + 1
                                                    · exact largeEvenLabelAll_wnorm_E8_four
                                                        hp he8q.2.1 he8q.1 he8q.2.2
                                                    by_cases he6t : lab.tag = .E6 ∧ 7 ≤ p ∧
                                                        p ∣ (2 ^ lab.n) ^ 2 + 2 ^ lab.n + 1
                                                    · exact
                                                        E6PhiThree.largeEvenLabelAll_wnorm_E6_phi3
                                                          hp he6t.2.1 he6t.1 he6t.2.2
                                                    by_cases he8three : lab.tag = .E8 ∧ p ≠ 3 ∧
                                                        p ∣ (2 ^ lab.n) ^ 2 + 2 ^ lab.n + 1
                                                    · exact E8PhiThreeWNorm.largeEvenLabelAll_wnorm_E8_phiThree
                                                        hp hp2 he8three.2.1 he8three.1 he8three.2.2
                                                    by_cases hlf : (lab.tag = .A ∨
                                                        (lab.tag = .D ∧ lab.rank = 3)) ∧
                                                        3 ≤ lab.rank ∧ ¬ p ∣ (2 ^ lab.n) ^ 2 - 1
                                                    · exact largeEvenLabelAll_wnorm_linear_frob
                                                        hp hp2 hlf.1 hlf.2.1 hlf.2.2
                                                    by_cases he8five : lab.tag = .E8 ∧ p = 5 ∧ 5 ∣ 2 ^ lab.n - 1
                                                    · rcases he8five with ⟨htag, hp5, h5⟩
                                                      subst p
                                                      exact E8WNorm.largeEvenLabelAll_wnorm_E8_five_split htag h5
                                                    by_cases he7cyc : lab.tag = .E7 ∧ 5 ≤ p ∧
                                                        p ∣ (2 ^ lab.n) ^ 6 - 1 ∧
                                                        ¬ p ∣ (2 ^ lab.n) ^ 2 - 1
                                                    · exact E7Cyclotomic.largeEvenLabelAll_wnorm_E7_cyclotomic
                                                        he7cyc.1 hp he7cyc.2.1 he7cyc.2.2.1 he7cyc.2.2.2
                                                    by_cases he8f : lab.tag = .E8 ∧ p = 5 ∧ 5 ∣ 2 ^ lab.n + 1
                                                    · rcases he8f with ⟨htag, hp5, h5⟩
                                                      subst p
                                                      exact E8FivePlusWNorm.largeEvenLabelAll_wnorm_E8_five_plus htag h5
                                                    by_cases hspf : (lab.tag = .B ∨
                                                        lab.tag = .C) ∧ 3 ≤ lab.rank ∧
                                                        ¬ p ∣ (2 ^ lab.n) ^ 2 - 1
                                                    · exact largeEvenLabelAll_wnorm_sp_frob
                                                        hp hp2 hspf.1 hspf.2.1 hspf.2.2
                                                    by_cases horf : (lab.tag = .D ∨
                                                        lab.tag = .twD) ∧ 4 ≤ lab.rank ∧
                                                        ¬ p ∣ (2 ^ lab.n) ^ 2 - 1
                                                    · exact largeEvenLabelAll_wnorm_orth_phi4
                                                        hp hp2 horf.1 horf.2.1 horf.2.2
                                                    by_cases htw6 : lab.tag = .twE6 ∧ 7 ≤ p ∧
                                                        p ∣ (2 ^ lab.n) ^ 2 - 2 ^ lab.n + 1
                                                    · exact
                                                        TwE6PhiSix.largeEvenLabelAll_wnorm_twE6_phi6
                                                          hp htw6.2.1 htw6.1 hlab.1 htw6.2.2
                                                    by_cases hunf : (lab.tag = .twA ∨
                                                        (lab.tag = .twD ∧ lab.rank = 3)) ∧
                                                        3 ≤ lab.rank ∧ ¬ p ∣ (2 ^ lab.n) ^ 2 - 1
                                                    · exact largeEvenLabelAll_wnorm_unitary_phi4
                                                        hp hp2 hlab.1 hunf.1 hunf.2.1 hunf.2.2
                                                    by_cases hu4p : lab.tag = .twA ∧ 5 ≤ p ∧
                                                        lab.rank + 1 = 4 * p ∧ p ∣ 2 ^ lab.n + 1
                                                    · exact largeEvenLabelAll_wnorm_unitary_four_prime
                                                        hp hu4p.2.1 hu4p.1 hu4p.2.2.1 hu4p.2.2.2
                                                    by_cases hlin3p : lab.tag = .A ∧ 5 ≤ p ∧ lab.rank + 1 = 3 * p ∧ p ∣ 2 ^ lab.n - 1
                                                    · exact largeEvenLabelAll_wnorm_linear_three_prime hp hlin3p.2.1
                                                        hlin3p.1 hlin3p.2.2.1 hlin3p.2.2.2
                                                    by_cases hw5 : GGTBWNormW5UnitLabel p lab
                                                    · exact largeEvenLabelAll_wnorm_unitary_w5 hp hw5
                                                    by_cases hw3 : GGTBWNormW3UnitLabel p lab
                                                    · exact largeEvenLabelAll_wnorm_unitary_w3 hp hw3
                                                    by_cases hu3p : lab.tag = .twA ∧ 5 ≤ p ∧
                                                        lab.rank + 1 = 3 * p ∧ p ∣ 2 ^ lab.n + 1
                                                    · exact largeEvenLabelAll_wnorm_unitary_three_prime
                                                        hp hu3p.2.1 hu3p.1 hu3p.2.2.1 hu3p.2.2.2
                                                    by_cases hu9t : lab.tag = .twA ∧ p = 3 ∧
                                                        lab.rank + 1 = 9 ∧ p ∣ 2 ^ lab.n + 1
                                                    · exact largeEvenLabelAll_wnorm_unitary_nine_three
                                                        hu9t.2.1 hu9t.1 hu9t.2.2.1 hu9t.2.2.2
                                                    by_cases hw5s : GGTBWNormW5SplitLabel p lab
                                                    · exact largeEvenLabelAll_wnorm_linear_w5 hp hw5s
                                                    by_cases hlin4p : GGTBWNormW4SplitLabel p lab
                                                    · exact largeEvenLabelAll_wnorm_linear_four_prime
                                                        hp hlin4p.2.1 hlin4p.1 hlin4p.2.2.1 hlin4p.2.2.2
                                                    apply h p hp hp2 lab hlab hexcl <;> assumption

theorem ggTBWNormLabelInput_of_rest (h : GGTBWNormLabelRest) : GGTBWNormLabelInput := by
  intro p hp hp2 lab hlab hexcl htw6
  by_cases he8p3 : lab.tag = .E8 ∧ p = 3
  · obtain ⟨htag, rfl⟩ := he8p3
    exact E8ThreeWNorm.largeEvenLabelAll_wnormLift_E8_three hlab htag
  by_cases he6p3 : lab.tag = .E6 ∧ p = 3
  · obtain ⟨htag, rfl⟩ := he6p3
    exact E6ThreeWNorm.largeEvenLabelAll_wnormLift_E6_three hlab htag
  by_cases he7p3 : lab.tag = .E7 ∧ p = 3
  · obtain ⟨htag, rfl⟩ := he7p3
    exact E7ThreeToral.largeEvenLabelAll_wnormLift_E7_three hlab htag
  exact largeEvenLabelAll_wnorm_toLift
    (ggTBWNormLabelFull_of_rest h p hp hp2 lab hlab hexcl he8p3 he6p3 he7p3 htw6)

end CFSG.StandardType
