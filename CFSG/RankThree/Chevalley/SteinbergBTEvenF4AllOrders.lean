module

public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree SteinbergBT
open CFSG.ComponentClassification.UnbalancedCatalog (mem_zpowers_of_fixed)

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem entrywiseAdjointAut_mul_finiteExceptionalAut_F4 (σ : K ≃+* K) :
    entrywiseAdjointAut ReeTag.F4.tag σ * ReeTag.F4.finiteExceptionalAut K =
      ReeTag.F4.finiteExceptionalAut K * entrywiseAdjointAut ReeTag.F4.tag σ := by
  refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
  · show (entrywiseAdjointAut ReeTag.F4.tag σ * ReeTag.F4.finiteExceptionalAut K) (xElement i c) =
      (ReeTag.F4.finiteExceptionalAut K * entrywiseAdjointAut ReeTag.F4.tag σ) (xElement i c)
    rw [MulAut.mul_apply, MulAut.mul_apply, ReeTag.finiteExceptionalAut_xElement,
      entrywiseAdjointAut_xElement, entrywiseAdjointAut_xElement,
      ReeTag.finiteExceptionalAut_xElement, map_pow]
  · show (entrywiseAdjointAut ReeTag.F4.tag σ * ReeTag.F4.finiteExceptionalAut K) (yElement i c) =
      (ReeTag.F4.finiteExceptionalAut K * entrywiseAdjointAut ReeTag.F4.tag σ) (yElement i c)
    rw [MulAut.mul_apply, MulAut.mul_apply, ReeTag.finiteExceptionalAut_yElement,
      entrywiseAdjointAut_yElement, entrywiseAdjointAut_yElement,
      ReeTag.finiteExceptionalAut_yElement, map_pow]

theorem even_F4_canonical_field_centralizer_all_orders {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) :
    ((entrywiseAdjointAut ReeTag.F4.tag σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (adjointGroup ReeTag.F4.tag K).subtype = fixedFieldImage ReeTag.F4.tag σ ∧
      fixedFieldImage ReeTag.F4.tag σ ≤ adjointGroup ReeTag.F4.tag K ∧
      IsSimpleGroup (fixedFieldImage ReeTag.F4.tag σ) ∧
      (¬∀ a b : fixedFieldImage ReeTag.F4.tag σ, a * b = b * a) ∧
      (∃ ι : ↥((fixedFieldImage ReeTag.F4.tag σ).subgroupOf (adjointGroup ReeTag.F4.tag K)) ≃*
          ↥(((fixedFieldImage ReeTag.F4.tag σ).subgroupOf
            (adjointGroup ReeTag.F4.tag K)).map MulAut.conj),
        ∀ j, (ι j : MulAut (adjointGroup ReeTag.F4.tag K)) =
          MulAut.conj (j : adjointGroup ReeTag.F4.tag K)) ∧
      (∀ β ∈ Subgroup.centralizer {entrywiseAdjointAut ReeTag.F4.tag σ},
        ∃! ga : adjointGroup ReeTag.F4.tag K × ℕ, ga.2 < 2 * f ∧
          (ga.1 : ModGL ReeTag.F4.tag K) ∈ fixedFieldImage ReeTag.F4.tag σ ∧
          β = MulAut.conj ga.1 * ReeTag.F4.finiteExceptionalAut K ^ ga.2) ∧
      (∀ g : adjointGroup ReeTag.F4.tag K,
        (g : ModGL ReeTag.F4.tag K) ∈ fixedFieldImage ReeTag.F4.tag σ → ∀ a : ℕ,
        MulAut.conj g * ReeTag.F4.finiteExceptionalAut K ^ a ∈
          Subgroup.centralizer {entrywiseAdjointAut ReeTag.F4.tag σ}) ∧
      ((fixedFieldImage ReeTag.F4.tag σ).subgroupOf (adjointGroup ReeTag.F4.tag K)).map
          MulAut.conj ≤ Subgroup.centralizer {entrywiseAdjointAut ReeTag.F4.tag σ} ∧
      ((((fixedFieldImage ReeTag.F4.tag σ).subgroupOf
          (adjointGroup ReeTag.F4.tag K)).map MulAut.conj).subgroupOf
        (Subgroup.centralizer {entrywiseAdjointAut ReeTag.F4.tag σ})).Normal ∧
      Subgroup.centralizer {entrywiseAdjointAut ReeTag.F4.tag σ} ⊓
          Subgroup.centralizer ((((fixedFieldImage ReeTag.F4.tag σ).subgroupOf
            (adjointGroup ReeTag.F4.tag K)).map MulAut.conj :
              Subgroup (MulAut (adjointGroup ReeTag.F4.tag K))) :
                Set (MulAut (adjointGroup ReeTag.F4.tag K))) =
        Subgroup.zpowers (entrywiseAdjointAut ReeTag.F4.tag σ) ∧
      Nat.card (Subgroup.zpowers (entrywiseAdjointAut ReeTag.F4.tag σ)) = orderOf σ := by
  have hchar : ringChar K = 2 := ringChar.eq K ReeTag.F4.prime
  set C := adjointGroup ReeTag.F4.tag K
  set φ := ReeTag.F4.finiteExceptionalAut K with hφ
  set δ := entrywiseAdjointAut ReeTag.F4.tag σ with hδ
  set J := fixedFieldImage ReeTag.F4.tag σ with hJ
  have hZ : Subgroup.center C = ⊥ := center_adjointGroup_eq_bot
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hrank : 0 < ReeTag.F4.tag.rank := by decide
  obtain ⟨hdvd, hk⟩ := card_fixSubfield Nat.prime_two hf hK σ
  set d := f / orderOf σ with hd'
  have hd : 1 ≤ d :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (Nat.pos_of_dvd_of_pos hdvd (by omega))
  have : CharP (fixSubfield σ) ReeTag.F4.prime := inferInstance
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (τ := ReeTag.F4.tag)
    (Or.inr (Or.inl rfl)) hchar σ
  have hJC : J ≤ C := fun j hj => (fixedFieldImage_le hj).1
  have hmemJ : ∀ g : C, (g : ModGL ReeTag.F4.tag K) ∈ J ↔ δ g = g := by
    intro g
    refine (Subgroup.ext_iff.1 hΓJ (g : ModGL ReeTag.F4.tag K)).symm.trans ?_
    rw [mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨hordk, hNFk, -⟩ := even_F4_exact_automorphism_normal_form hd (fixSubfield σ) hk
  have hconjδ : ∀ (g : C) (a : ℕ), δ * (MulAut.conj g * φ ^ a) =
      MulAut.conj (δ g) * φ ^ a * δ := fun g a => by
    have hcomm : δ * φ ^ a = φ ^ a * δ :=
      (Commute.pow_right (entrywiseAdjointAut_mul_finiteExceptionalAut_F4 σ) a).eq
    rw [← mul_assoc, mulAut_mul_conj, mul_assoc, hcomm, ← mul_assoc]
  have hcentJ : ∀ (g : C) (a : ℕ), MulAut.conj g * φ ^ a ∈ Subgroup.centralizer {δ} ↔
      (g : ModGL ReeTag.F4.tag K) ∈ J := by
    intro g a
    rw [Subgroup.mem_centralizer_singleton_iff, hmemJ, hconjδ]
    constructor
    · intro h
      exact hinj (mul_right_cancel (mul_right_cancel h.symm))
    · intro h
      rw [h]
  have hNδ : ((J.subgroupOf C).map MulAut.conj) ≤ Subgroup.centralizer {δ} := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, mulAut_mul_conj,
      (hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
  have hZk : Subgroup.center (adjointGroup ReeTag.F4.tag (fixSubfield σ)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hmodel : ChevalleyExceptionalModel J .F4 2 d :=
    ⟨⟨Nat.prime_two, hd, rfl⟩, fixSubfield σ, inferInstance, inferInstance, hk,
      ⟨(fixedFieldImageEquiv σ).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot).symm⟩⟩
  have hsimple : IsSimpleGroup J := (CFSG.LieType.Simplicity.fam_f4_simplicity _ 2 d hmodel).2
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  refine ⟨?_, hJC, hsimple, not_commute_fixedFieldImage hrank σ,
    ⟨(J.subgroupOf C).equivMapOfInjective _ hinj, fun j => rfl⟩, fun β hβ => ?_,
    fun g hg a => (hcentJ g a).2 hg, hNδ, ⟨fun n hn g => ?_⟩, le_antisymm (fun β hβ => ?_) ?_,
    by rw [Nat.card_zpowers, orderOf_entrywiseAdjointAut hrank σ]⟩
  ·
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hmemJ g).2 hg
    · intro hx
      exact ⟨⟨x, hJC hx⟩, (hmemJ _).1 hx, rfl⟩
  ·
    obtain ⟨⟨g, a⟩, hga, huniq⟩ := hNF β
    have hgJ : (g : ModGL ReeTag.F4.tag K) ∈ J := (hcentJ g a).1 (hga ▸ hβ)
    refine ⟨(g, a), ⟨a.isLt, hgJ, hga⟩, fun q hq => ?_⟩
    obtain ⟨hq2, -, hqβ⟩ := hq
    have h := huniq (q.1, ⟨q.2, hq2⟩) hqβ
    have h1 : q.1 = g := congrArg Prod.fst h
    have h2 : q.2 = (a : ℕ) := congrArg (fun x => (x.2 : ℕ)) h
    exact Prod.ext h1 h2
  ·
    obtain ⟨j, hj, hjn⟩ := Subgroup.mem_subgroupOf.1 hn
    rw [SetLike.mem_coe] at hj
    have hgδ : δ * (g : MulAut C) = g * δ :=
      Subgroup.mem_centralizer_iff.1 g.2 δ (Set.mem_singleton δ)
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut C) j, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmemJ]
      calc δ ((g : MulAut C) j) = (δ * (g : MulAut C)) j := rfl
        _ = (g * δ : MulAut C) j := by rw [hgδ]
        _ = (g : MulAut C) (δ j) := rfl
        _ = (g : MulAut C) j := by rw [(hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hjn]
      exact (mulAut_mul_conj_mul_inv _ _).symm
  ·
    obtain ⟨hβδ, hβN⟩ := Subgroup.mem_inf.1 hβ
    obtain ⟨⟨g, a⟩, hga, -⟩ := hNF β
    dsimp only at hga
    have hgJ : (g : ModGL ReeTag.F4.tag K) ∈ J := (hcentJ g a).1 (hga ▸ hβδ)
    have hfix : ∀ x : C, (x : ModGL ReeTag.F4.tag K) ∈ J → β x = x := by
      intro x hx
      have hn : MulAut.conj x ∈ (J.subgroupOf C).map MulAut.conj :=
        ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      have h1 : MulAut.conj x * β = β * MulAut.conj x :=
        Subgroup.mem_centralizer_iff.1 hβN _ hn
      have h2 : MulAut.conj (β x) = MulAut.conj x := by
        rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
      exact hinj h2
    obtain ⟨g', rfl⟩ := (mem_fixedFieldImage_iff_exists σ g).1 hgJ
    set φk := ReeTag.F4.finiteExceptionalAut (fixSubfield σ)
    have hidk : MulAut.conj g' * φk ^ (a : ℕ) = 1 := by
      refine MulEquiv.ext fun y => fixedFieldInclusion_injective σ ?_
      have h1 := hfix (fixedFieldInclusion σ y) ⟨y, y.2, rfl⟩
      rw [hga, MulAut.mul_apply, finiteExceptionalAut_pow_fixedFieldInclusion σ (a : ℕ) y,
        MulAut.conj_apply] at h1
      rw [MulAut.one_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
      exact h1
    have hmod : φk ^ ((a : ℕ) % (2 * d)) = φk ^ (a : ℕ) := by
      have h := pow_mod_orderOf φk (a : ℕ)
      rwa [hordk] at h
    obtain ⟨q, -, hq⟩ := hNFk 1
    have h1 := hq (1, ⟨0, by omega⟩) (by simp)
    have h2 := hq (g', ⟨(a : ℕ) % (2 * d), Nat.mod_lt _ (by omega)⟩) (by
      show 1 = MulAut.conj g' * φk ^ ((a : ℕ) % (2 * d))
      rw [hmod, hidk])
    have h3 := h2.trans h1.symm
    have hg'1 : g' = 1 := congrArg Prod.fst h3
    have ha0 : (a : ℕ) % (2 * d) = 0 := congrArg (fun x => (x.2 : ℕ)) h3
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero ha0
    subst hg'1
    rw [hga, map_one, map_one, one_mul, ht, mul_assoc, finiteExceptionalAut_pow_two_mul]
    have hfrpow : ∀ c, (fr ^ (d * t)) c = c ^ 2 ^ (d * t) :=
      ringAut_pow_apply_of_frobenius hfr (d * t)
    rw [← entrywiseAdjointAut_eq_finiteFrobeniusAut_pow hfrpow]
    have hmem : fr ^ (d * t) ∈ Subgroup.zpowers σ := mem_zpowers_of_fixed fun c hc => by
      have hc' : c ^ 2 ^ d = c := pow_card_eq_self_of_mem hk hc
      have key : ∀ n : ℕ, c ^ (2 ^ d) ^ n = c := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, pow_mul, ih, hc']
      rw [hfrpow, pow_mul]
      exact key t
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← hn]
    exact Subgroup.mem_zpowers_iff.2
      ⟨n, (map_zpow (entrywiseAdjointAutHom (τ := ReeTag.F4.tag)) σ n).symm⟩
  ·
    refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
      fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
        fun n hn => (Subgroup.mem_centralizer_iff.1 (hNδ hn) δ (Set.mem_singleton δ)).symm⟩)

end CFSG.RankThree.Chevalley
