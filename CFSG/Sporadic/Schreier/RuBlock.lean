module

public import CFSG.LieType.Ree.LargeReeInvolutionComponentFree
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LocalAnalysis.ComponentInitial.IsotypicRepeatedPrimes
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.Sporadic.RuSchreier

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem card_dvd_of_isComponentOf_centralizer
    {s : Equiv.Perm (Fin 4060)} (hsP : s ∈ ruP)
    (hs : orderOf s = 2) {B : Subgroup (Equiv.Perm (Fin 4060))}
    (hB : CFSG.Assembly.IsComponentOf B (ruP ⊓ centralizer {s})) : Nat.card B ∣ 116480 := by
  have hmem : s ∈ ({t | t ∈ ruP ∧ orderOf t = 2} : Set _) := ⟨hsP, hs⟩
  rw [CTUC_Ru_two_involution_classes_and_seed_relations.2.2.2.2.2.1] at hmem
  rcases hmem with ⟨g, hg, hgs⟩ | ⟨g, hg, hgs⟩
  ·
    exfalso
    subst hgs
    refine LieType.Ree.LargeReeInvolution.not_isComponentOf_conj (Γ := ruP) (x := g⁻¹)
      (r := ruZ) (inv_mem hg) (by simp [mul_assoc]) (N := ruJ) ?_ isPGroup_ruJ ?_ ?_ B hB
    · rw [← ruC_eq_centralizer]
      exact ruJ_leC
    · intro c hc n hn
      rw [← ruC_eq_centralizer] at hc
      have hnorm := ruJ_normal.conj_mem ⟨n, ruJ_leC hn⟩ hn ⟨c, hc⟩
      exact hnorm
    · intro c hc hcomm
      rw [← ruC_eq_centralizer] at hc
      exact ruCentralizer_J (mem_inf.2 ⟨hc, mem_centralizer_iff.2 fun n hn => (hcomm n hn).symm⟩)
  ·
    have hconj : ruP ⊓ centralizer {s} = ruL.map (MulAut.conj g).toMonoidHom := by
      rw [← ruCentralizer_a, Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
        map_conj_centralizer_singleton, hgs]
      congr 1
      ext x
      constructor
      · intro hx
        refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
        exact mul_mem (mul_mem (inv_mem hg) hx) hg
      · rintro ⟨y, hy, rfl⟩
        exact mul_mem (mul_mem hg hy) (inv_mem hg)
    calc Nat.card B ∣ Nat.card (ruP ⊓ centralizer {s} : Subgroup _) := card_dvd_of_le hB.1
      _ = Nat.card ruL := by
          rw [hconj]
          exact Nat.card_congr (ruL.equivMapOfInjective _ (MulAut.conj g).injective).symm.toEquiv
      _ = 116480 := CTUC_Ru_explicit_commuting_subgroup_odd_normal_exclusion.2.1

theorem commuting_block_ru_overgroup_exclusion
    {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.Ru) := by
  classical
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  have hKL : ∀ K ∈ block J, K ≤ L := fun K hK => (le_blockGroup hK).trans hML
  set f : L ⧸ center L ≃* ruP := e.trans ruEquivP
  set φ : L ⧸ center L →* Equiv.Perm (Fin 4060) := ruP.subtype.comp f.toMonoidHom
  have hφ : Function.Injective φ := ruP.subtype_injective.comp f.injective
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centerQuotientImage L K₂) 2
    (even_iff_two_dvd.1 (hπKq K₂ hK₂).2)
  obtain ⟨t, htK, ht2, -⟩ := exists_involution_lift_of_odd_center hodd u.2
    (by rw [Subgroup.orderOf_coe, hu])
  obtain ⟨hπt, hcompK⟩ := hloc K₁ hK₁ K₂ hK₂ hne t htK ht2
  set v := QuotientGroup.mk' (center L) t
  have hcent : (centralizer ({v} : Set (L ⧸ center L))).map φ = ruP ⊓ centralizer {φ v} := by
    rw [← Subgroup.map_map, map_centralizer_singleton_mulEquiv, map_subtype_centralizer_singleton]
    rfl
  have hB := isComponentOf_map_of_injective hcompK φ hφ
  rw [hcent] at hB
  have hv2 : orderOf (φ v) = 2 := by rw [orderOf_injective φ hφ, hπt]
  have hdvd := card_dvd_of_isComponentOf_centralizer (f v).2 hv2 hB
  rw [← Nat.card_congr ((centerQuotientImage L K₁).equivMapOfInjective φ hφ).toEquiv] at hdvd
  set S := Nat.card (centerQuotientImage L K₁ ⧸ center (centerQuotientImage L K₁))
  have hS₁ : S = Nat.card (J ⧸ center J) := card_centerQuotientImage_block hq hK₁ (hKL K₁ hK₁)
  have hS₂ : Nat.card (centerQuotientImage L K₂ ⧸ center (centerQuotientImage L K₂)) = S := by
    rw [hS₁]
    exact card_centerQuotientImage_block hq hK₂ (hKL K₂ hK₂)
  have hSdvd : S ∣ 116480 := by
    refine Dvd.dvd.trans ?_ hdvd
    exact ⟨Nat.card (center (centerQuotientImage L K₁)),
      (card_eq_card_quotient_mul_card_subgroup _)⟩
  have hsq : S ^ 2 ∣ 145926144000 := by
    have h := card_quotient_center_sq_dvd (hcomm K₁ hK₁ K₂ hK₂ hne).2
      (bot_le : (⊥ : Subgroup (L ⧸ center L)) ≤ center (L ⧸ center L)) hS₂.symm
    rw [Nat.card_congr QuotientGroup.quotientBot.toEquiv, Nat.card_congr f.toEquiv,
      card_ruP'] at h
    exact h
  have h7 : ¬ 7 ∣ S := fun h7 => by
    have := (pow_dvd_pow_of_dvd h7 2).trans hsq
    norm_num at this
  have h13 : ¬ 13 ∣ S := fun h13 => by
    have := (pow_dvd_pow_of_dvd h13 2).trans hsq
    norm_num at this
  have hcop : Nat.Coprime S 91 := by
    rw [show (91 : ℕ) = 7 * 13 by norm_num]
    exact Nat.Coprime.mul_right
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).2 h7).symm
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 13)).2 h13).symm
  have hS1280 : S ∣ 1280 :=
    hcop.dvd_of_dvd_mul_left (by rw [show (91 : ℕ) * 1280 = 116480 by norm_num]; exact hSdvd)
  have h3 : 3 ≤ S.primeFactors.card :=
    three_le_card_primeFactors_of_isQuasisimple (hπKq K₁ hK₁).1
  have hle : S.primeFactors ⊆ (1280 : ℕ).primeFactors :=
    Nat.primeFactors_mono hS1280 (by norm_num)
  have h1280 : (1280 : ℕ).primeFactors = {2, 5} := by
    rw [show (1280 : ℕ) = 2 ^ 8 * 5 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors (by norm_num)]
    rfl
  have := Finset.card_le_card hle
  rw [h1280] at this
  have h2 : ({2, 5} : Finset ℕ).card = 2 := by decide
  omega

end CFSG.Sporadic.RuSchreier
