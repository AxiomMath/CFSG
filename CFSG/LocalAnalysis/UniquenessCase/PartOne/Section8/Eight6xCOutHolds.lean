module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCStar
import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalCoprime
import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor fieldActorHom
  even_triality_exact_automorphism_normal_form odd_triality_exact_automorphism_normal_form)
open CFSG.LocalAnalysis.ComponentInitial
  (finite_field_automorphism_fixed_field_cardinality finite_field_prime_power_characteristic)
open CFSG.RankThree.PartTwo.KFacts (coe_g2FieldHom g2FieldHom g2_automorphism_normal_form)

private theorem k1513a_coset_dichotomy {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [IsCyclic (G ⧸ N)] (φ α : G) (hφ : orderOf (QuotientGroup.mk' N φ) = 3) (hαN : α ∉ N)
    (hα3 : α ^ 3 ∈ N) : ∃ n : N, α = n * φ ∨ α = n * φ ^ 2 := by
  have hx3 : (QuotientGroup.mk' N α) ^ 3 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hα3
  have : Finite (Subgroup.zpowers (QuotientGroup.mk' N α)) :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hx3⟩)
  have hle : Subgroup.zpowers (QuotientGroup.mk' N α) ≤
      Subgroup.zpowers (QuotientGroup.mk' N φ) := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hφ]
    exact orderOf_dvd_of_pow_eq_one hx3
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers _))
  have hj' := zpow_mod_orderOf (QuotientGroup.mk' N φ) j
  rw [hφ, hj] at hj'
  have hdiv : ∀ m : ℕ, (QuotientGroup.mk' N φ) ^ m = QuotientGroup.mk' N α → α / φ ^ m ∈ N :=
    fun m hm => (QuotientGroup.eq_iff_div_mem (N := N)).mp (by
      simpa [QuotientGroup.mk'_apply, map_pow] using hm.symm)
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
  · exact absurd (by simpa using hdiv 0 (by simpa [h] using hj')) hαN
  · exact ⟨⟨α / φ ^ 1, hdiv 1 (by simpa [h] using hj')⟩, Or.inl (by simp)⟩
  · exact ⟨⟨α / φ ^ 2, hdiv 2 (by simpa [h] using hj')⟩, Or.inr (by simp)⟩

private theorem k1513a_outer_coset_dichotomy {L : Type*} [Group L] [IsCyclic (Outer L)]
    (φ α : MulAut L) (hφ : orderOf (φ : Outer L) = 3) (hαN : α ∉ inner L)
    (hα3 : α ^ 3 ∈ inner L) :
    ∃ g : L, α = MulAut.conj g * φ ∨ α = MulAut.conj g * φ ^ 2 := by
  obtain ⟨⟨_, g, rfl⟩, h | h⟩ := k1513a_coset_dichotomy (inner L) φ α hφ hαN hα3
  · exact ⟨g, Or.inl h⟩
  · exact ⟨g, Or.inr h⟩

private theorem k1513a_orderOf_outer_eq_three {L : Type*} [Group L] {φ : MulAut L}
    (hout : φ ∉ inner L) (h3 : φ ^ 3 ∈ inner L) : orderOf (φ : Outer L) = 3 :=
  orderOf_eq_prime (by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 h3)
    fun h => hout ((QuotientGroup.eq_one_iff _).1 h)

private theorem k1513a_outOrderThree {L : Type} [Group L] [IsCyclic (Outer L)] {φ : MulAut L}
    (hout : φ ∉ inner L) (h3 : φ ^ 3 ∈ inner L) : OutOrderThree L φ := by
  intro α hα hα3
  exact k1513a_outer_coset_dichotomy φ α (k1513a_orderOf_outer_eq_three hout h3) hα hα3

private theorem k1513a_orderOf_frobenius_pow {K : Type} [Field K] [Finite K] {p n : ℕ}
    (hp : p.Prime) (hn : 1 ≤ n) (hK : Nat.card K = p ^ (3 * n)) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (p ^ n)) : orderOf σ = 3 := by
  obtain ⟨F, hF, hord, -⟩ := finite_field_automorphism_fixed_field_cardinality hp (by omega) hK
  have hpow : ∀ (m : ℕ) (c : K), (F ^ m) c = c ^ (p ^ m) := fun m => by
    induction m with
    | zero => intro c; simp
    | succ m ih =>
      intro c
      rw [pow_succ, RingAut.mul_apply, hF, ih, ← pow_mul, pow_succ, mul_comm p]
  have hσF : σ = F ^ n := RingEquiv.ext fun c => by rw [hσ, hpow]
  rw [hσF, orderOf_pow_of_dvd (by omega) (hord ▸ Dvd.intro_left 3 rfl), hord]
  exact Nat.mul_div_cancel 3 hn

theorem outTrialityInput_holds :
    OutTrialityInput := by
  intro p f K _ _ σ hp _ hf hK hσ
  obtain ⟨Θ, hΘ, hker, hcyc⟩ : ∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      (K ≃+* K), (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
        Θ.ker = inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧ IsCyclic (K ≃+* K) := by
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨-, -, ⟨Θ, h1, -, h3, -⟩, h4, -⟩ :=
        even_triality_exact_automorphism_normal_form hf K hK σ hσ
      exact ⟨Θ, h1, h3, h4⟩
    · obtain ⟨-, -, ⟨Θ, h1, -, h3, -⟩, h4, -⟩ :=
        odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
      exact ⟨Θ, h1, h3, h4⟩
  have := GL83.I713.isCyclic_outer_of_ker_eq_inner Θ hker
  have hσ3 : orderOf σ = 3 :=
    k1513a_orderOf_frobenius_pow hp hf (by rw [hK, ← pow_mul, mul_comm]) hσ
  have hΘσ : Θ (fieldActor σ σ) = σ := hΘ _ 1 σ (by rw [map_one, one_mul])
  refine k1513a_outOrderThree ?_ ?_
  · intro h
    rw [← hker, MonoidHom.mem_ker, hΘσ] at h
    rw [h, orderOf_one] at hσ3
    omega
  · have h3 : σ ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hσ3)
    have h := map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
    rw [h3, map_one] at h
    rw [show fieldActor σ σ ^ 3 = 1 from h.symm]
    exact one_mem _

theorem lieOutCyclicInput_holds :
    LieOutCyclicInput := by
  refine ⟨fun K _ _ p f hK _ => ?_, fun K _ _ p f hK => ?_, fun K _ _ f hK => ?_⟩
  · obtain ⟨⟨hp, hf, -, h3⟩, hm⟩ := hK.chevalleyExceptionalModel (by decide)
    exact GL83.I713.isCyclic_outer_of_untwistedModel_G2 hp hf h3 hm
  · obtain ⟨⟨hp, hf, -⟩, hm⟩ := hK.chevalleyExceptionalModel (by decide)
    exact GL83.I713.isCyclic_outer_of_trialityModel hp hf hm
  · exact (large_Ree_model_field_outer_group_and_inner_involutions K 2 f
      (hK.reeTitsModel (by decide)).2).2.2.2.1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
