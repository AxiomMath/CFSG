module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsSep
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

variable (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime]

@[expose] noncomputable def stdPinnedLargeRee : PinnedAut (F4.reeGamma K a) where
  inndiag := (MulAut.conj : F4.reeGamma K a →* MulAut (F4.reeGamma K a)).range
  inn_le := le_rfl
  field := (F4.reeGammaFieldAutHom K a).range
  graph := ∅

variable {a K}

section NormalForm

variable (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
include ha hK

theorem largeRee_automorphism_normal_form :
    (∀ α : MulAut (F4.reeGamma K a), ∃ (x : F4.reeGamma K a) (β : K ≃+* K),
      α = MulAut.conj x * F4.reeGammaFieldAut K a β) ∧
    ∀ β : K ≃+* K, IsInnerAut (F4.reeGammaFieldAut K a β) → β = 1 := by
  obtain ⟨-, hNF, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  have hone : F4.reeGammaFieldAut K a 1 = 1 := by
    rw [← reeGammaFieldAutHom_apply, map_one]
  refine ⟨fun α => ?_, fun β hβ => ?_⟩
  · obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α
    exact ⟨x, β, hxβ⟩
  · obtain ⟨x, hx⟩ := hβ
    obtain ⟨p, -, huniq⟩ := hNF (F4.reeGammaFieldAut K a β)
    have h1 := huniq (1, β) (by dsimp only; rw [map_one, one_mul])
    have h2 := huniq (x, 1) (by dsimp only; rw [hone, mul_one, hx])
    exact congrArg Prod.snd (h1.trans h2.symm)

theorem stdPinnedLargeRee_stable : (stdPinnedLargeRee a K).Stable := by
  obtain ⟨hdec, -⟩ := largeRee_automorphism_normal_form ha hK
  have hcomm : ∀ σ τ : K ≃+* K, F4.reeGammaFieldAut K a σ * F4.reeGammaFieldAut K a τ =
      F4.reeGammaFieldAut K a τ * F4.reeGammaFieldAut K a σ := fun σ τ => by
    rw [← reeGammaFieldAutHom_apply, ← reeGammaFieldAutHom_apply, ← map_mul, ← map_mul,
      CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]
  refine ⟨⟨fun d hd α => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hd
    exact ⟨α y, (mul_mulAutConj_mul_inv α y).symm⟩
  · rintro α _ ⟨τ, rfl⟩ h1
    obtain ⟨g, σ, rfl⟩ := hdec α
    refine ⟨F4.reeGammaFieldAutHom K a τ, ⟨τ, rfl⟩, h1, MulAut.conj g, ⟨g, rfl⟩, ?_⟩
    rw [reeGammaFieldAutHom_apply]
    calc MulAut.conj g * F4.reeGammaFieldAut K a σ * F4.reeGammaFieldAut K a τ *
          (MulAut.conj g * F4.reeGammaFieldAut K a σ)⁻¹ =
        MulAut.conj g * (F4.reeGammaFieldAut K a σ * F4.reeGammaFieldAut K a τ) *
          (F4.reeGammaFieldAut K a σ)⁻¹ * (MulAut.conj g)⁻¹ := by group
      _ = MulAut.conj g * F4.reeGammaFieldAut K a τ * (MulAut.conj g)⁻¹ := by
          rw [hcomm]; group
  · rintro α γ hγ
    exact absurd hγ (Set.notMem_empty γ)
  · rintro α γ φ hγ
    exact absurd hγ (Set.notMem_empty γ)

theorem stdPinnedLargeRee_separated : (stdPinnedLargeRee a K).Separated := by
  obtain ⟨-, hfaith⟩ := largeRee_automorphism_normal_form ha hK
  refine PinnedAut.Separated.of_graph_eq_empty _ rfl ?_ ?_
  · rintro φ - _ ⟨g, rfl⟩
    exact ⟨φ g, (mul_mulAutConj_mul_inv φ g).symm⟩
  · rintro _ ⟨σ, rfl⟩ hmem
    rw [reeGammaFieldAutHom_apply] at hmem ⊢
    rw [hfaith σ hmem, ← reeGammaFieldAutHom_apply, map_one]

theorem largeRee_order_three_inFieldCoset {α : MulAut (F4.reeGamma K a)} (hα : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) :
    ∃ β : K ≃+* K, orderOf β = 3 ∧ IsInnerAut (α * (F4.reeGammaFieldAut K a β)⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdec, hfaith⟩ := largeRee_automorphism_normal_form ha hK
  obtain ⟨x, β, rfl⟩ := hdec α
  set I := (MulAut.conj : F4.reeGamma K a →* MulAut (F4.reeGamma K a)).range with hI
  have hIn : I.Normal := ⟨fun d hd γ => by
    obtain ⟨y, rfl⟩ := hd
    exact ⟨γ y, (mul_mulAutConj_mul_inv γ y).symm⟩⟩
  have hxI : MulAut.conj x ∈ I := ⟨x, rfl⟩
  have hβ1 : β ≠ 1 := by
    rintro rfl
    rw [← reeGammaFieldAutHom_apply, map_one, mul_one] at hout
    exact hout hxI
  have hβ3I : F4.reeGammaFieldAut K a β ^ 3 ∈ I := by
    have hmk : ((MulAut.conj x * F4.reeGammaFieldAut K a β : MulAut (F4.reeGamma K a)) :
        MulAut (F4.reeGamma K a) ⧸ I) =
        ((F4.reeGammaFieldAut K a β : MulAut (F4.reeGamma K a)) :
          MulAut (F4.reeGamma K a) ⧸ I) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hxI, one_mul]
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hmk, ← QuotientGroup.mk_pow, hα,
      QuotientGroup.mk_one]
  have hβ3 : β ^ 3 = 1 := by
    apply hfaith
    rw [← reeGammaFieldAutHom_apply, map_pow, reeGammaFieldAutHom_apply]
    exact hβ3I
  refine ⟨β, orderOf_eq_prime hβ3 hβ1, ?_⟩
  rw [mul_inv_cancel_right]
  exact hxI

variable (a K) in
@[expose] def LargeReeOrderThreeFieldConj : Prop :=
  ∀ β : K ≃+* K, orderOf β = 3 → ∀ α : MulAut (F4.reeGamma K a), α ^ 3 = 1 →
    IsInnerAut (α * (F4.reeGammaFieldAut K a β)⁻¹) →
      ∃ x : F4.reeGamma K a,
        α = MulAut.conj x * F4.reeGammaFieldAut K a β * (MulAut.conj x)⁻¹

theorem isField_largeRee_of_pow_three_eq_one (hLang : LargeReeOrderThreeFieldConj a K)
    {α : MulAut (F4.reeGamma K a)} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (stdPinnedLargeRee a K).IsField α := by
  obtain ⟨-, hfaith⟩ := largeRee_automorphism_normal_form ha hK
  obtain ⟨β, hβ, hcoset⟩ := largeRee_order_three_inFieldCoset ha hK hα hout
  obtain ⟨x, hx⟩ := hLang β hβ α hα hcoset
  refine ⟨F4.reeGammaFieldAutHom K a β, ⟨β, rfl⟩, fun h1 => ?_, MulAut.conj x, ⟨x, rfl⟩, ?_⟩
  · have h2 := hfaith β (by rw [← reeGammaFieldAutHom_apply, h1]; exact ⟨1, map_one _⟩)
    rw [h2, orderOf_one] at hβ
    omega
  · rw [reeGammaFieldAutHom_apply]
    exact hx

end NormalForm

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (a K) in
@[expose] def InducesKindLargeRee (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* F4.reeGamma K a,
    InducesKind L (stdPinnedLargeRee a K) e x k

variable (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
include ha hK

theorem inducesKindLargeRee_iff (e : L ⧸ aschbacherSolvableCore 3 L ≃* F4.reeGamma K a) (x : G)
    (k : AutKind) :
    InducesKindLargeRee a K L x k ↔ InducesKind L (stdPinnedLargeRee a K) e x k := by
  constructor
  · rintro ⟨e', h⟩
    exact (inducesKind_iff_of_stable L (stdPinnedLargeRee_stable ha hK) e' e x k).1 h
  · intro h
    exact ⟨e, h⟩

theorem inducesKindLargeRee_unique {x : G} {k₁ k₂ : AutKind}
    (h₁ : InducesKindLargeRee a K L x k₁) (h₂ : InducesKindLargeRee a K L x k₂) : k₁ = k₂ := by
  obtain ⟨e, h₁⟩ := h₁
  exact InducesKind.unique L (stdPinnedLargeRee_separated ha hK) h₁
    ((inducesKindLargeRee_iff L ha hK e x k₂).mp h₂)

theorem inducesKindLargeRee_field (hLang : LargeReeOrderThreeFieldConj a K) {x : G}
    (hx3 : x ^ 3 = 1) (hout : InducesOuterTheta x L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* F4.reeGamma K a) :
    InducesKindLargeRee a K L x .field := by
  obtain ⟨hx, -⟩ := id hout
  exact ⟨e, hx, isField_largeRee_of_pow_three_eq_one ha hK hLang
    (inducedAutHom_pow_eq_one L e hx hx3) ((not_isInnerAut_inducedAutHom_iff L e hx).mpr hout)⟩

theorem InducesKindLargeRee.inducesOuterTheta {x : G} {k : AutKind}
    (h : InducesKindLargeRee a K L x k) (hk : k ≠ .inner) : InducesOuterTheta x L := by
  obtain ⟨e, h⟩ := h
  exact InducesKind.inducesOuterTheta L (stdPinnedLargeRee_separated ha hK) h hk

end Induced

end CFSG.RankThree.PartTwo.KFacts
