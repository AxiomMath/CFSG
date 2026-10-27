module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S6b
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mulEquiv_of_surjective {P W₁ W₂ : Type} [Group P] [Group W₁] [Group W₂]
    [IsSimpleGroup W₁] [IsSimpleGroup W₂] (h₁ : ∃ a b : W₁, a * b ≠ b * a)
    (h₂ : ∃ a b : W₂, a * b ≠ b * a) (f₁ : P →* W₁) (f₂ : P →* W₂)
    (hf₁ : Function.Surjective f₁) (hf₂ : Function.Surjective f₂)
    (hk₁ : Group.IsSolvable ↥f₁.ker) (hk₂ : Group.IsSolvable ↥f₂.ker) : Nonempty (W₁ ≃* W₂) := by
  have key : ∀ {V₁ V₂ : Type} [Group V₁] [Group V₂] [IsSimpleGroup V₂],
      (∃ a b : V₂, a * b ≠ b * a) → ∀ (g₁ : P →* V₁) (g₂ : P →* V₂),
      Function.Surjective g₂ → Group.IsSolvable ↥g₁.ker → g₁.ker ≤ g₂.ker := by
    intro V₁ V₂ _ _ _ hnab g₁ g₂ hg₂ hk
    have hn : (g₁.ker.map g₂).Normal := (MonoidHom.normal_ker g₁).map g₂ hg₂
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (g₁.ker.map g₂) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hs : Group.IsSolvable ↥(g₁.ker.map g₂) :=
        Group.isSolvable_of_surjective (g₂.subgroupMap_surjective g₁.ker)
      rw [h] at hs
      have hs' : Group.IsSolvable V₂ :=
        Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup V₂) ≃* V₂).toMonoidHom)
          Subgroup.topEquiv.surjective
      exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hs') a b)
  have heq : f₁.ker = f₂.ker := le_antisymm (key h₂ f₁ f₂ hf₂ hk₁) (key h₁ f₂ f₁ hf₁ hk₂)
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁).symm.trans
    (QuotientGroup.quotientMulEquivOfEq heq)).trans
      (QuotientGroup.quotientKerEquivOfSurjective f₂ hf₂)⟩

theorem isL2_of_mulEquiv {W W' : Type} [Group W] [Group W'] (e : W' ≃* W) {p f : ℕ}
    (h : F6.IsL2 p f W) : F6.IsL2 p f W' := by
  obtain ⟨hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, hK, hKf, hcard, ⟨e.trans e'⟩⟩

theorem isSLEps3_of_mulEquiv {W W' : Type} [Group W] [Group W'] (e : W' ≃* W) {p : ℕ}
    (h : F6.IsSLEps3 p W) : F6.IsSLEps3 p W' := by
  obtain ⟨hp, K, hK, hKf, h⟩ := h
  refine ⟨hp, K, hK, hKf, ?_⟩
  rcases h with ⟨h1, h2, ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩⟩ | ⟨h1, h2, ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩⟩
  · exact Or.inl ⟨h1, h2, Or.inl ⟨e.trans e'⟩⟩
  · exact Or.inl ⟨h1, h2, Or.inr ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨h1, h2, Or.inl ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨h1, h2, Or.inr ⟨e.trans e'⟩⟩

theorem rest_cases (hIF : F6.InspF618Rest)
    (hA6 : ∀ (Q : Type) [Group Q] [Finite Q], (IsAlt 6 Q ∨ F6.IsL2 3 2 Q) → AutOddNormCent Q)
    (hA7 : ∀ (Q : Type) [Group Q] [Finite Q], IsAlt 7 Q → AutOddNormCent Q)
    (hM12 : ∀ (Q : Type) [Group Q] [Finite Q], F6.IsM12 Q → AutOddNormCent Q)
    (hL2Sq : ∀ p : ℕ, p.Prime → 3 < p → ∀ (Q : Type) [Group Q] [Finite Q], IsPSL 2 p 2 Q →
      AutOddNormCent Q)
    (hL2p : FactAutOddL2pPlus) (hL3 : FactAutL3Eps) {Q : Type} [Group Q] [Finite Q]
    {H₁ H₂ : Subgroup Q} (h : F6.IsF618CaseRestCat H₁ H₂) {W' : Type} [Group W'] [Finite W']
    [IsSimpleGroup W']
    (e : W' ≃* (↥(perfectCore (⊤ : Subgroup Q)) ⧸
      Subgroup.center ↥(perfectCore (⊤ : Subgroup Q)))) :
    AutOddNormCent W' ∨
      ((F6.IsF618CaseThree H₁ H₂ ∨ F6.IsF618CaseFour H₁ H₂ ∨ F6.IsF618CaseFive H₁ H₂) ∧
        ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧ F6.IsL2 p 1 W') := by
  obtain ⟨-, h345, h6, h7, h8, h9, h1011, h1213⟩ := hIF Q H₁ H₂
  have hsq : ∀ p : ℕ, p.Prime → p ≠ 2 → F6.IsL2 p 2 W' → AutOddNormCent W' := by
    intro p hp hp2 hL
    rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | hp3
    · exact hA6 W' (Or.inr hL)
    · exact hL2Sq p hp hp3 W' hL
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨p, hp, hp24, hL⟩ := h345 (Or.inl h)
    exact Or.inr ⟨Or.inl h, p, hp, hp24, isL2_of_mulEquiv e hL⟩
  · obtain ⟨p, hp, hp24, hL⟩ := h345 (Or.inr (Or.inl h))
    exact Or.inr ⟨Or.inr (Or.inl h), p, hp, hp24, isL2_of_mulEquiv e hL⟩
  · obtain ⟨p, hp, hp24, hL⟩ := h345 (Or.inr (Or.inr h))
    exact Or.inr ⟨Or.inr (Or.inr h), p, hp, hp24, isL2_of_mulEquiv e hL⟩
  · left
    rcases h6 h with ⟨⟨e'⟩⟩ | ⟨p, f, hp, hf1, hf2, hpf, hL⟩
    · exact hA6 W' (Or.inl ⟨e.trans e'⟩)
    · have hL' := isL2_of_mulEquiv e hL
      have hp2 : p ≠ 2 := by
        rintro rfl
        rcases (show f = 1 ∨ f = 2 by omega) with rfl | rfl <;> norm_num at hpf
      rcases (show f = 1 ∨ f = 2 by omega) with rfl | rfl
      · exact hL2p p hp (by rw [pow_one] at hpf; omega) W' hL'
      · exact hsq p hp hp2 hL'
  · left
    obtain ⟨e'⟩ := h7 h
    exact hA7 W' ⟨e.trans e'⟩
  · left
    rcases h8 h with ⟨⟨e'⟩⟩ | ⟨p, hp, hp8, hL⟩
    · exact hA6 W' (Or.inl ⟨e.trans e'⟩)
    · exact hsq p hp (by rintro rfl; omega) (isL2_of_mulEquiv e hL)
  · left
    rcases h9 h with ⟨⟨e'⟩⟩ | ⟨p, hp, hp24, hL⟩
    · exact hA7 W' ⟨e.trans e'⟩
    · exact hsq p hp (by rintro rfl; omega) (isL2_of_mulEquiv e hL)
  · left
    obtain ⟨p, -, hS⟩ := h1011 (Or.inl h)
    exact hL3 W' inferInstance (Or.inl ⟨p, isSLEps3_of_mulEquiv e hS⟩)
  · left
    obtain ⟨p, -, hS⟩ := h1011 (Or.inr h)
    exact hL3 W' inferInstance (Or.inl ⟨p, isSLEps3_of_mulEquiv e hS⟩)
  · left
    obtain ⟨e'⟩ := h1213 (Or.inl h)
    exact hM12 W' ⟨e.trans e'⟩
  · left
    obtain ⟨e'⟩ := h1213 (Or.inr h)
    exact hM12 W' ⟨e.trans e'⟩

omit [Finite G] in
theorem card_star {B N L : Subgroup G} [(N.subgroupOf B).Normal] (hLB : L ≤ B) :
    Nat.card ↥(star B N L) = N.relIndex L := by
  unfold star
  rw [← Subgroup.relIndex_ker (K := L.subgroupOf B) (f := QuotientGroup.mk' (N.subgroupOf B)),
    QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hLB]

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem star_eq_top (hL2o : FactAutL2pOuter) (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] {K : Subgroup G} (hK : K ∈ cComp (X ⊔ T ⊔ D))
    (hBK : X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G)) (hKB₀ : ¬ K ≤ B₀) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (hL : F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ K)) : star (X ⊔ T ⊔ D) B₀ K = ⊤ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hinj, hφK, hS⟩ := H.exists_conj hA hB hK hBK hKB₀
  have hInn : (MulAut.conj : ↥(star (X ⊔ T ⊔ D) B₀ K) →* MulAut ↥(star (X ⊔ T ⊔ D) B₀ K)).range ≤
      φ.range := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, hφK n⟩
  have hAne : φ.range ≠
      (MulAut.conj : ↥(star (X ⊔ T ⊔ D) B₀ K) →* MulAut ↥(star (X ⊔ T ⊔ D) B₀ K)).range := by
    intro h
    apply hne
    rw [eq_top_iff]
    intro q _
    have h1 : φ q ∈ (MulAut.conj : ↥(star (X ⊔ T ⊔ D) B₀ K) →*
        MulAut ↥(star (X ⊔ T ⊔ D) B₀ K)).range := by
      rw [← h]
      exact ⟨q, rfl⟩
    obtain ⟨k, hk⟩ := h1
    rw [← hφK k] at hk
    rw [← hinj hk]
    exact k.2
  have hN := hL2o p hp hp3 hp8 _ hL φ.range _ hInn hAne hS
  refine H.false_of_oddNorm_comm hB fun q hq hoq s _ => ?_
  have hqS : φ q ∈ (star (X ⊔ T ⊔ D) B₀ T).map φ :=
    hN ⟨Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ hq), ⟨q, rfl⟩⟩
  obtain ⟨t, ht, htq⟩ := hqS
  have hqt : q = t := (hinj htq).symm
  have hT2 := (H.isSylowTwoOf_star_T (B₀ := B₀)).2.1
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have h1 : q ^ 2 ^ k = 1 := by
    rw [hqt]
    simpa using congrArg Subtype.val hk
  have hq1 : q = 1 := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    rcases i with _ | i
    · rw [pow_zero] at hi
      exact orderOf_eq_one_iff.mp hi
    · exfalso
      obtain ⟨m, hm⟩ := hoq
      rw [hi, pow_succ] at hm
      omega
  rw [hq1, one_mul, mul_one]

theorem exists_caseFour (hF : F6.TheoremF618Cat) (hIF : F6.InspF618Rest)
    (hIW : InspWalter3320) (hA21 : AsA21SQTKSection) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hA : AS_A_1_31)
    (h312 : Vol2Native.A312ForSQTKCat) (hI : InspA312F618)
    (hA6 : ∀ (Q : Type) [Group Q] [Finite Q], (IsAlt 6 Q ∨ F6.IsL2 3 2 Q) → AutOddNormCent Q)
    (hA7 : ∀ (Q : Type) [Group Q] [Finite Q], IsAlt 7 Q → AutOddNormCent Q)
    (hM12 : ∀ (Q : Type) [Group Q] [Finite Q], F6.IsM12 Q → AutOddNormCent Q)
    (hL2Sq : ∀ p : ℕ, p.Prime → 3 < p → ∀ (Q : Type) [Group Q] [Finite Q], IsPSL 2 p 2 Q →
      AutOddNormCent Q)
    (hL2p : FactAutOddL2pPlus) (hL3 : FactAutL3Eps) (hL2o : FactAutL2pOuter)
    (hL2s : FactL2pSylowFour) (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    ∃ g ∈ D, g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) ∧
      (F6.IsF618CaseFour (plus (gZero X T g) (X ⊔ T))
          (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∨
        F6.IsF618CaseFour (plus (gZero X T g) (conjByElt g (X ⊔ T)))
          (plus (gZero X T g) (X ⊔ T))) ∧
      ∃ K ∈ cComp (X ⊔ T ⊔ D), perfectCore (gZero X T g) ≤ K ∧
        X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G) ∧ ¬ K ≤ B₀ ∧
        star (X ⊔ T ⊔ D) B₀ K = ⊤ ∧
        ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
          F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ K) := by
  obtain ⟨g, hg, hgR, hrest, hK₀, K, hK, hK₀K, hBK, hKB₀⟩ :=
    H.exists_K hF hIF hIW hA21 h37 h38 h39 hA hB
  have hstar := H.star_perfectCore_eq hIF h312 hI hA hB hg hgR hrest hK₀ hK hK₀K hBK hKB₀
  have hY := H.le_commutator_sup hA hB
  obtain ⟨hsimp, hnab⟩ := H.isSimpleGroup_star hB hY hK hBK hKB₀
  have hgX := H.not_mem_normalizer_X hg hgR
  have hs := (H.isGoldschmidtTripleIn hg hgX).isSolvable_pPrimeCore
  have hq : CFSG.IsQuasisimple ↥(perfectCore (⊤ : Subgroup
      (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g)))) := by
    rcases hrest with h | h
    · exact (hIF _ _ _).1 h
    · exact (hIF _ _ _).1 h
  have := hq.2.1
  obtain ⟨β, hβs, hβk⟩ := exists_hom_perfectCore_quot hs
  have hK₀B : perfectCore (gZero X T g) ≤ X ⊔ T ⊔ D := (perfectCore_le _).trans (gZero_le hg)
  let κ₀ : ↥(perfectCore (gZero X T g)) →* ↥(star (X ⊔ T ⊔ D) B₀ (perfectCore (gZero X T g))) :=
    ((QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))).subgroupMap _).comp
      (Subgroup.subgroupOfEquivOfLe hK₀B).symm.toMonoidHom
  let κ : ↥(perfectCore (gZero X T g)) →* ↥(star (X ⊔ T ⊔ D) B₀ K) :=
    (MulEquiv.subgroupCongr hstar).toMonoidHom.comp κ₀
  have hκs : Function.Surjective κ :=
    (MulEquiv.subgroupCongr hstar).surjective.comp
      ((MonoidHom.subgroupMap_surjective _ _).comp
        (Subgroup.subgroupOfEquivOfLe hK₀B).symm.surjective)
  have hκk : Group.IsSolvable ↥κ.ker := by
    have hs₀ := H.isSolvable_B₀ hB
    let ι : ↥κ.ker →* ↥B₀ :=
      ((perfectCore (gZero X T g)).subtype.comp κ.ker.subtype).codRestrict B₀ fun k => by
        have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp k.2)
        exact (mk_eq_one_iff (hK₀B (k : ↥(perfectCore (gZero X T g))).2)).mp h1
    have hι : Function.Injective ι := by
      intro a b hab
      have h1 : ((ι a : ↥B₀) : G) = ((ι b : ↥B₀) : G) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact Group.isSolvable_of_isSolvable_injective hι
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective hnab hq.2.2 κ β hκs hβs hκk hβk
  have hdich : AutOddNormCent ↥(star (X ⊔ T ⊔ D) B₀ K) ∨
      (((F6.IsF618CaseThree (plus (gZero X T g) (X ⊔ T))
            (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∨
          F6.IsF618CaseFour (plus (gZero X T g) (X ⊔ T))
            (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∨
          F6.IsF618CaseFive (plus (gZero X T g) (X ⊔ T))
            (plus (gZero X T g) (conjByElt g (X ⊔ T)))) ∨
        (F6.IsF618CaseThree (plus (gZero X T g) (conjByElt g (X ⊔ T)))
            (plus (gZero X T g) (X ⊔ T)) ∨
          F6.IsF618CaseFour (plus (gZero X T g) (conjByElt g (X ⊔ T)))
            (plus (gZero X T g) (X ⊔ T)) ∨
          F6.IsF618CaseFive (plus (gZero X T g) (conjByElt g (X ⊔ T)))
            (plus (gZero X T g) (X ⊔ T)))) ∧
        ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
          F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ K)) := by
    rcases hrest with h | h
    · rcases rest_cases hIF hA6 hA7 hM12 hL2Sq hL2p hL3 h e with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨Or.inl h1, h2⟩
    · rcases rest_cases hIF hA6 hA7 hM12 hL2Sq hL2p hL3 h e with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨Or.inr h1, h2⟩
  rcases hdich with hodd | ⟨hcase, p, hp, hp24, hL⟩
  · exact absurd hodd (H.not_autOddNormCent hA hB hK hBK hKB₀)
  have hp3 : 3 < p := by omega
  have hp8 : p % 8 = 3 ∨ p % 8 = 5 := by omega
  have htop := H.star_eq_top hL2o hA hB hK hBK hKB₀ hp hp3 hp8 hL
  refine ⟨g, hg, hgR, ?_, K, hK, hK₀K, hBK, hKB₀, htop, p, hp, hp24, hL⟩
  have hT4 : Nat.card ↥(star (X ⊔ T ⊔ D) B₀ T) = 4 := by
    have hsyl := H.isSylowTwoOf_star_T (B₀ := B₀)
    have hTK : star (X ⊔ T ⊔ D) B₀ T ≤ star (X ⊔ T ⊔ D) B₀ K := htop ▸ le_top
    have hsyl' : IsSylowTwoOf ((star (X ⊔ T ⊔ D) B₀ T).subgroupOf (star (X ⊔ T ⊔ D) B₀ K)) ⊤ := by
      refine ⟨le_top, hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm, fun h2 => ?_⟩
      apply hsyl.2.2
      have h3 : (((star (X ⊔ T ⊔ D) B₀ T).subgroupOf (star (X ⊔ T ⊔ D) B₀ K)).subgroupOf
          ⊤).index = (star (X ⊔ T ⊔ D) B₀ T).relIndex (star (X ⊔ T ⊔ D) B₀ K) :=
        Subgroup.relIndex_top_right _
      rw [h3, htop] at h2
      exact h2
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv]
    exact hL2s p hp hp8 _ hL _ hsyl'
  have hTle : Nat.card ↥(plus (gZero X T g) T) ≤ 4 := by
    rw [H.card_plus_T hg hgR, ← hT4, card_star (le_sup_right.trans le_sup_left)]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
    have hT₀G : T ⊓ B₀ ≤ pCoreOf 2 (gZero X T g) := by
      rw [hT₀]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf H.isSylowTwoOf_B).trans
          (le_sup_right.trans le_sup_left))
        ((gZero_le hg).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    rw [← Subgroup.inf_relIndex_right (H := B₀) (K := T), inf_comm]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_of_le_left (L := T) hT₀G)
  have h8 : ∀ {A₁ A₂ : Subgroup (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g))},
      Nonempty (↥(A₁ ⊓ A₂) ≃* DihedralGroup 4) → Nat.card ↥(A₁ ⊓ A₂) = 8 := by
    intro A₁ A₂ ⟨e'⟩
    rw [Nat.card_congr e'.toEquiv, DihedralGroup.nat_card]
  obtain ⟨hinf, -, -, -⟩ := H.f618 hF hg hgR
  have hT' : (X ⊔ T).subgroupOf (gZero X T g) ⊓ (conjByElt g (X ⊔ T)).subgroupOf (gZero X T g) =
      T.subgroupOf (gZero X T g) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [← Subgroup.mem_inf, H.inf_conj_eq hg hgX]
  have hTeq : plus (gZero X T g) (X ⊔ T) ⊓ plus (gZero X T g) (conjByElt g (X ⊔ T)) =
      plus (gZero X T g) T := by
    rw [hinf, hT']
  have hD8 : Nonempty (↥(plus (gZero X T g) (X ⊔ T) ⊓
      plus (gZero X T g) (conjByElt g (X ⊔ T))) ≃* DihedralGroup 4) → False := fun h => by
    have h1 := h8 h
    rw [hTeq] at h1
    omega
  have hD8' : Nonempty (↥(plus (gZero X T g) (conjByElt g (X ⊔ T)) ⊓
      plus (gZero X T g) (X ⊔ T)) ≃* DihedralGroup 4) → False := fun h => by
    rw [inf_comm] at h
    exact hD8 h
  rcases hcase with (h | h | h) | (h | h | h)
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hD, -⟩ := h
    exact absurd hD hD8
  · exact Or.inl h
  · obtain ⟨-, hD, -⟩ := h
    exact absurd hD hD8
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hD, -⟩ := h
    exact absurd hD hD8'
  · exact Or.inr h
  · obtain ⟨-, hD, -⟩ := h
    exact absurd hD hD8'

end Hyp3320

end S3320

end CFSG.Quasithin.H13
