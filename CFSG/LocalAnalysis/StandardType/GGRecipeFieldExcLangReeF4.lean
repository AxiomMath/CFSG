module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangSz
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.RankThree.PartOne.RF4.Descent
public import CFSG.LieType.Ree.ReeGenericPerfect
public import CFSG.LieType.Ree.SmallReeModelSchreier

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

namespace RecipeExcLang

set_option linter.unusedSectionVars false


@[expose] def TwF4ConjOn (K : Type) [Field K] (a : ℕ) (S : (Fin 4 → ℤ) → Prop) (p : ℕ) :
    Prop :=
  GGRawFieldConj p (LargeEvenCenterQuot (MarkChev.twF4H S a K))
    (markIDImage S K (MarkChev.twF4H S a K))
    (RecipeFieldExcInn.markFieldImage S K (MarkChev.twF4H S a K))

theorem TwF4ConjOn.of_eq {K : Type} [Field K] {a : ℕ} {S S' : (Fin 4 → ℤ) → Prop} {p : ℕ}
    (hS : S = S') (h : TwF4ConjOn K a S p) : TwF4ConjOn K a S' p :=
  hS ▸ h

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem ggRawFieldConj_reeGamma [CharP K ReeTag.F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) :
    GGRawFieldConj p (LargeEvenCenterQuot (ReeTag.F4.reeGamma K a))
      (markIDImage (IsRoot ReeTag.F4.tag) K (ReeTag.F4.reeGamma K a))
      (RecipeFieldExcInn.markFieldImage (IsRoot ReeTag.F4.tag) K (ReeTag.F4.reeGamma K a)) := by
  intro _ _ u hu f _ huf hpow
  have hZ := ReeTag.large_Ree_fixed_group_center_trivial a K hK
  set e := centerQuotEquivOfBot hZ with he
  set Ψ := MulAut.congr e with hΨ
  have hInn : ∀ y, (MulAut.conj y : MulAut (LargeEvenCenterQuot (ReeTag.F4.reeGamma K a))) ∈
      markIDImage (IsRoot ReeTag.F4.tag) K (ReeTag.F4.reeGamma K a) :=
    fun y => Subgroup.subset_closure (Or.inl ⟨y, rfl⟩)
  have hΨconj : ∀ y, Ψ (MulAut.conj (e.symm y)) = MulAut.conj y := fun y => by
    rw [hΨ, mulAut_congr_conj, MulEquiv.apply_symm_apply]
  set x := Ψ (u * f) with hx
  have hxp : x ^ p = 1 := by rw [hx, ← map_pow, hpow, map_one]
  have hxinn : ∀ y, x ≠ MulAut.conj y := by
    intro y hy
    apply huf
    have : u * f = MulAut.conj (e.symm y) := Ψ.injective (by rw [← hx, hy, hΨconj])
    rw [this]
    exact hInn _
  obtain ⟨hfield, huniq, ⟨Ψ', hΨ'⟩, -⟩ :=
    large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨y, β⟩, hyβ, -⟩ := huniq x
  simp only at hyβ
  have hΨ'x : Ψ' ⟨y, β⟩ = x := by rw [hΨ', hyβ]
  have hβp : β ^ p = 1 := by
    have h1 : Ψ' (⟨y, β⟩ ^ p) = 1 := by rw [map_pow, hΨ'x, hxp]
    have h2 : (⟨y, β⟩ : ReeTag.F4.reeGamma K a ⋊[ReeTag.F4.reeGammaFieldAutHom K a] (K ≃+* K)) ^ p =
        1 := Ψ'.injective (by rw [h1, map_one])
    have h3 := congrArg SemidirectProduct.rightHom h2
    rwa [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at h3
  have hβ1 : β ≠ 1 := by
    rintro rfl
    apply hxinn y
    have h1 : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := by
      rw [← ReeTag.reeGammaFieldAutHom_apply, map_one]
    rw [hyβ, h1, mul_one]
  have : Fact p.Prime := ⟨hp⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ :=
    CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp β hβord x hxp ⟨y, hyβ⟩
  refine ⟨Ψ.symm (ReeTag.F4.reeGammaFieldAut K a β), ⟨β, fun h h' hrel => ?_⟩,
    MulAut.conj (e.symm g), hInn _, ?_, ?_⟩
  ·
    rw [hΨ, congr_symm_apply_mk hZ]
    congr 1
    refine Subtype.ext (Units.ext ?_)
    rw [(hfield β).1 h]
    exact hrel.symm
  ·
    have hφ : ReeTag.F4.reeGammaFieldAut K a β = Ψ' ⟨1, β⟩ := by rw [hΨ', map_one, one_mul]
    rw [MulEquiv.orderOf_eq, hφ, MulEquiv.orderOf_eq]
    have hinr : (⟨1, β⟩ : ReeTag.F4.reeGamma K a ⋊[ReeTag.F4.reeGammaFieldAutHom K a]
        (K ≃+* K)) = SemidirectProduct.inr β := rfl
    rw [hinr, orderOf_injective SemidirectProduct.inr SemidirectProduct.inr_injective, hβord]
  ·
    apply Ψ.injective
    rw [← hx, hg, map_mul, map_mul, map_inv, hΨconj, MulEquiv.apply_symm_apply]

theorem commutator_self_eq_of_commutator_eq_top {G : Type*} [Group G] {H : Subgroup G}
    (h : _root_.commutator H = ⊤) : ⁅H, H⁆ = H := by
  have h1 : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h1, ← Subgroup.map_commutator, ← commutator_def, h]

theorem twF4ConjOn_isRoot [CharP K ReeTag.F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) : TwF4ConjOn K a (IsRoot .F4) p := by
  unfold TwF4ConjOn
  have h2 : ReeTag.F4.reeGamma K a = reeFixedGroup Tag.F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) :=
    ReeTag.reeGamma_eq_reeFixedGroup
  have h3 := commutator_self_eq_of_commutator_eq_top
    (ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) ha hK)
  have h4 : ⁅reeFixedGroup Tag.F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)), reeFixedGroup Tag.F4 K reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))⁆ =
      ⁅ReeTag.F4.reeGamma K a, ReeTag.F4.reeGamma K a⁆ := by
    rw [h2]
    rfl
  have hH : MarkChev.twF4H (IsRoot .F4) a K = ReeTag.F4.reeGamma K a :=
    (twF4H_eq_commutator K a).trans (h4.trans h3)
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot .F4) K), H = ReeTag.F4.reeGamma K a →
      GGRawFieldConj p (LargeEvenCenterQuot H) (markIDImage (IsRoot .F4) K H)
        (RecipeFieldExcInn.markFieldImage (IsRoot .F4) K H) from key _ hH
  intro H hH'
  subst hH'
  exact ggRawFieldConj_reeGamma ha hK hp

theorem ggRawFieldConj_twF4 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) :
    GGRawFieldConj p (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K _)
      (LargeEvenChevFieldImage LargeEvenCartanF4 K _) := by
  have : CharP K ReeTag.F4.prime := charP_two_of_card hK
  have h := (twF4ConjOn_isRoot ha hK hp).of_eq (largeEvenIsRoot_eq_isRoot .F4).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL LargeEvenCartanF4 K),
      H = MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K →
      GGRawFieldConj p (LargeEvenCenterQuot H) (LargeEvenChevIDImage LargeEvenCartanF4 K H)
        (LargeEvenChevFieldImage LargeEvenCartanF4 K H) from
    key _ (largeEvenTwF4H_eq a K)
  intro H hH
  subst hH
  rw [largeEvenChevIDImage_eq]
  exact h

end RecipeExcLang

open RecipeExcLang

theorem ggRawFieldConjOn_twF4 :
    GGRawFieldConjOn fun _ lab => lab.tag = .twF4 := by
  intro p hp _ lab hlab ht Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  dsimp only [LargeEvenRawDatum] at h ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggRawFieldConj_twF4 (by omega) hK hp⟩

end CFSG.StandardType
