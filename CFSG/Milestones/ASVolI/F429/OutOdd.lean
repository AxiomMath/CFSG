module

public import CFSG.Milestones.ASVolI.F429.bC3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

section Generic

theorem burnsideF429_index_dvd_card_outer {E : Type} [Group E] [Finite E] {Gp : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥) :
    Gp.index ∣ Nat.card (Outer ↥Gp) := by
  set α : E →* MulAut ↥Gp := MulAut.conjNormal with hα
  have hαinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hcg : g ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun φ : MulAut ↥Gp => ((φ ⟨x, hx⟩ : ↥Gp) : E)) (MonoidHom.mem_ker.1 hg)
      simp only [hα, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hc] at hcg
    exact hcg
  have hG : Gp.map α = inner ↥Gp := by
    ext φ
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, MulEquiv.ext fun x => Subtype.ext (by
        simp [hα, MulAut.conjNormal_apply, MulAut.conj_apply])⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, MulEquiv.ext fun x => Subtype.ext (by
        simp [hα, MulAut.conjNormal_apply, MulAut.conj_apply])⟩
  have h1 : (Gp.map α).relIndex ((⊤ : Subgroup E).map α) = Gp.index := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ hαinj, Subgroup.relIndex_top_right]
  rw [← h1, hG]
  have h2 : (inner ↥Gp).relIndex ((⊤ : Subgroup E).map α) ∣ (inner ↥Gp).index :=
    Subgroup.relIndex_dvd_index_of_le (hG ▸ Subgroup.map_mono le_top)
  exact h2

theorem burnsideF429_odd_index_of_outer {E : Type} [Group E] [Finite E] {Gp : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥) (hodd : Odd (Nat.card (Outer ↥Gp))) :
    Odd Gp.index :=
  Odd.of_dvd_nat hodd (burnsideF429_index_dvd_card_outer hc)

theorem burnsideF429_card_outer_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Outer G) = Nat.card (Outer H) :=
  Nat.card_congr (equivalence e).toEquiv

theorem burnsideF429_card_outer_of_theta {C K : Type} [Group C] [Field K]
    (Θ : MulAut C →* (K ≃+* K)) (hsurj : Function.Surjective Θ)
    (hker : Θ.ker = (MulAut.conj : C →* MulAut C).range) :
    Nat.card (Outer C) = Nat.card (K ≃+* K) := by
  have hinner : inner C = Θ.ker := by rw [hker]; rfl
  have e2 : Outer C ≃* (K ≃+* K) :=
    (QuotientGroup.quotientMulEquivOfEq hinner).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  exact Nat.card_congr e2.toEquiv

end Generic

section Kinds


variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_card_outer_G2 (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    Nat.card (Outer ↥Gp) = f := by
  obtain ⟨K, fK, finK, cK, hK, Ψ, -, -⟩ := burnsideF429b_G2_chart hyp.toHypF_4_4g
  obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K hK
  rw [← burnsideF429_card_outer_eq Ψ]
  rw [show Nat.card (Outer (H13.F431.G2.C K)) = Nat.card (K ≃+* K) from
    burnsideF429_card_outer_of_theta Θ hsurj hker]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality 2 f
      Nat.prime_two (by omega) K hK
  exact hcard

theorem burnsideF429_card_outer_D4tw (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) :
    Nat.card (Outer ↥Gp) = 3 * f := by
  obtain ⟨K, fK, finK, cK, σ, -, hf, hK, hσ, Ψ, -, -⟩ := burnsideF429b_D4_chart hyp.toHypF_4_4g
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, -, hcardAut, -⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hf K hK σ hσ
  rw [← burnsideF429_card_outer_eq Ψ, burnsideF429_card_outer_of_theta Θ hsurj hker, hcardAut]

theorem burnsideF429_card_outer_F4tw (hyp : HypF_4_4 .F4tw 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    Nat.card (Outer ↥Gp) = f := by
  obtain ⟨a, K, fK, finK, charK, hscope, hfa, marking, -, -⟩ := burnsideF4g_chart_F4tw hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  have ha : 1 ≤ a := by omega
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hscope
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  obtain ⟨Φ, -⟩ := burnsideF4gF4Inv_exists_iso ha hK marking
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_full_inner_field_automorphism_normal_form
      a ha K hK
  rw [← burnsideF429_card_outer_eq Φ, hfa]
  exact hcard

end Kinds

end CFSG.ASVolI
