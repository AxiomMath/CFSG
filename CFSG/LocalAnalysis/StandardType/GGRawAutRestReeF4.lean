module

public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangReeF4
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree RecipeExcLang
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

namespace RawAutReeF4

@[expose] def TwF4AutOn (K : Type) [Field K] (a : ℕ) (S : (Fin 4 → ℤ) → Prop) : Prop :=
  Subgroup.center (MarkChev.twF4H S a K) = ⊥ ∧
    (∀ (σ : K ≃+* K) (h : MarkChev.twF4H S a K), ∃ h' : MarkChev.twF4H S a K,
      ((h' : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
        MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _)) ∧
    (∀ (σ : K ≃+* K) (g : MarkChev.GLS S K), g ∈ MarkChev.twF4H S a K →
      (∀ h : MarkChev.twF4H S a K,
        MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _) =
          ((g * h * g⁻¹ : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K))) → σ = 1) ∧
    ∀ α : MulAut (MarkChev.twF4H S a K), ∃ g ∈ MarkChev.twF4H S a K, ∃ σ : K ≃+* K,
      ∀ h : MarkChev.twF4H S a K,
        ((α h : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
          (g : Module.End K (MarkChev.Space S K)) *
            MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _) *
              ((g⁻¹ : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K))

theorem TwF4AutOn.of_eq {K : Type} [Field K] {a : ℕ} {S S' : (Fin 4 → ℤ) → Prop}
    (hS : S = S') (h : TwF4AutOn K a S) : TwF4AutOn K a S' :=
  hS ▸ h


variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem twF4AutOn_isRoot [CharP K ReeTag.F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : TwF4AutOn K a (IsRoot .F4) := by
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
  have hZ := ReeTag.large_Ree_fixed_group_center_trivial a K hK
  obtain ⟨hfield, huniq, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  unfold TwF4AutOn
  rw [hH]
  refine ⟨hZ, fun σ h => ⟨ReeTag.F4.reeGammaFieldAut K a σ h, ?_⟩, fun σ g hg hrel => ?_,
    fun α => ?_⟩
  · rw [(hfield σ).1 h]
    rfl
  · have hfc : ReeTag.F4.reeGammaFieldAut K a σ =
        MulAut.conj (⟨g, hg⟩ : ReeTag.F4.reeGamma K a) := by
      refine MulEquiv.ext fun h => Subtype.ext (Units.ext ?_)
      rw [(hfield σ).1 h, MulAut.conj_apply]
      exact hrel h
    have h1 : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := by
      rw [← ReeTag.reeGammaFieldAutHom_apply, map_one]
    obtain ⟨_, -, huq⟩ := huniq (ReeTag.F4.reeGammaFieldAut K a σ)
    have e1 := huq (1, σ) (by dsimp only; rw [map_one, one_mul])
    have e2 := huq (⟨g, hg⟩, 1) (by dsimp only; rw [h1, mul_one, hfc])
    have := congrArg Prod.snd (e1.trans e2.symm)
    exact this
  · obtain ⟨⟨y, β⟩, hyβ, -⟩ := huniq α
    refine ⟨y.1, y.2, β, fun h => ?_⟩
    simp only at hyβ
    subst hyβ
    have e := (hfield β).1 h
    calc _ = (((y : ModGL ReeTag.F4.tag K) * ((ReeTag.F4.reeGammaFieldAut K a β h :
          ReeTag.F4.reeGamma K a) : ModGL ReeTag.F4.tag K) * (y : ModGL ReeTag.F4.tag K)⁻¹ :
            ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) := rfl
      _ = _ := by
        rw [e]
        rfl

theorem twF4AutOn_largeEven [CharP K ReeTag.F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : TwF4AutOn K a (LargeEvenIsRoot LargeEvenCartanF4) :=
  (twF4AutOn_isRoot ha hK).of_eq
    (show IsRoot .F4 = LargeEvenIsRoot LargeEvenCartanF4 from (largeEvenIsRoot_eq_isRoot .F4).symm)

theorem exists_conj_mul_field_twF4 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (φ : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))) :
    ∃ u ∈ LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K),
      ∃ f ∈ Subgroup.closure (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)),
        φ = u * f := by
  have : CharP K ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨hZ, -, -, hnf⟩ := twF4AutOn_largeEven ha hK
  suffices key : ∀ H : Subgroup (LargeEvenChevGL LargeEvenCartanF4 K),
      H = MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K →
      ∀ φ : MulAut (LargeEvenCenterQuot H), ∃ u ∈ LargeEvenChevIDImage LargeEvenCartanF4 K H,
        ∃ f ∈ Subgroup.closure (LargeEvenChevFieldImage LargeEvenCartanF4 K H), φ = u * f from
    key _ (largeEvenTwF4H_eq a K) φ
  intro H hH φ
  subst hH
  obtain ⟨g, hg, σ, hσ⟩ := hnf (MulAut.congr (centerQuotEquivOfBot hZ) φ)
  refine ⟨MulAut.conj (LargeEvenCenterMk _ ⟨g, hg⟩), conj_mem_chevIDImage _ _,
    (MulAut.conj (LargeEvenCenterMk _ ⟨g, hg⟩))⁻¹ * φ,
    Subgroup.subset_closure ⟨σ, fun h h' hh' => ?_⟩, (mul_inv_cancel_left _ φ).symm⟩
  rw [MulAut.mul_apply, congr_centerQuotEquivOfBot_mk hZ φ h, MulAut.conj_inv_apply, ← map_inv,
    ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, hσ h,
    hh']
  calc ((g⁻¹ : LargeEvenChevGL LargeEvenCartanF4 K) :
        Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) *
        ((g : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) *
          MarkChev.entrywise (LargeEvenIsRoot LargeEvenCartanF4) K σ (map_zero σ)
            ((h : LargeEvenChevGL LargeEvenCartanF4 K) :
              Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) *
          ((g⁻¹ : LargeEvenChevGL LargeEvenCartanF4 K) :
            Module.End K (LargeEvenChevModule LargeEvenCartanF4 K))) *
        (g : Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
      ((g⁻¹ : LargeEvenChevGL LargeEvenCartanF4 K) :
          Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) * g *
        MarkChev.entrywise (LargeEvenIsRoot LargeEvenCartanF4) K σ (map_zero σ)
          ((h : LargeEvenChevGL LargeEvenCartanF4 K) :
            Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) *
        (((g⁻¹ : LargeEvenChevGL LargeEvenCartanF4 K) :
          Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) * g) := by
        simp only [mul_assoc]
    _ = _ := by
        rw [Units.inv_mul, one_mul, mul_one]
        rfl

theorem ggRawInnField_twF4_of_diag (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hD : GGDiagRealizedInput LargeEvenCartanF4 K (LargeEvenTwF4H a K)) {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) := by
  have : CharP K ReeTag.F4.prime := charP_two_of_card hK
  have hsub := chevIDImage_subset_inn hD
  obtain ⟨hZ, hstab, hkey, -⟩ := twF4AutOn_largeEven ha hK
  suffices key : ∀ H : Subgroup (LargeEvenChevGL LargeEvenCartanF4 K),
      H = MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K →
      LargeEvenChevIDImage LargeEvenCartanF4 K H ⊆
        (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range →
      GGRawInnField p (LargeEvenCenterQuot H) (LargeEvenChevIDImage LargeEvenCartanF4 K H)
        (LargeEvenChevFieldImage LargeEvenCartanF4 K H) from
    key _ (largeEvenTwF4H_eq a K) hsub
  intro H hH hsub
  subst hH
  refine ggRawInnField_of_subgroup hp
    (Subgroup.closure (LargeEvenInnSet _ ∪ LargeEvenChevDiagImage LargeEvenCartanF4 K _)) rfl
    (conj_mem_chevIDImage _) fun φ hφ hφI => ?_
  obtain ⟨σ, hσ⟩ := hφ
  obtain ⟨y, hy⟩ := hsub hφI
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hmk : Function.Injective (LargeEvenCenterMk
      (MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
  have hrel : ∀ h : MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K,
      MarkChev.entrywise (LargeEvenIsRoot LargeEvenCartanF4) K σ (map_zero σ)
          ((h : LargeEvenChevGL LargeEvenCartanF4 K) :
            Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) =
        (((g : LargeEvenChevGL LargeEvenCartanF4 K) * h *
            (g : LargeEvenChevGL LargeEvenCartanF4 K)⁻¹ : LargeEvenChevGL LargeEvenCartanF4 K) :
          Module.End K (LargeEvenChevModule LargeEvenCartanF4 K)) := by
    intro h
    obtain ⟨h', hh'⟩ := hstab σ h
    have e1 := hσ h h' hh'
    have e2 : φ (LargeEvenCenterMk _ h) = LargeEvenCenterMk _ (g * h * g⁻¹) := by
      rw [← hy]
      exact conj_mk_centerQuot g h
    have e3 := hmk (e1.symm.trans e2)
    rw [← hh', e3]
    rfl
  have hσ1 := hkey σ g g.2 hrel
  subst hσ1
  ext z
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨h', hh'⟩ := hstab 1 h
  have e1 := hσ h h' hh'
  rw [MulAut.one_apply]
  change φ (LargeEvenCenterMk _ h) = LargeEvenCenterMk _ h
  rw [e1]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [hh']
  exact largeEvenEntrywise_of_forall_eq _ (fun x => rfl) _

end RawAutReeF4

open RawAutReeF4

section Labels


theorem ggOddAutOn_twF4 : GGOddAutOn fun lab => lab.tag = .twF4 := by
  intro p lab _ _ hlab ht _ Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  try dsimp only at hK hQK ⊢
  exact ⟨K, inferInstance, inferInstance, hK, hQK, fun _ _ =>
    RawAut.ggOddAutInnField_of_forall (exists_conj_mul_field_twF4 (by omega) hK)⟩

theorem ggRawInnFieldOn_twF4_of_diag (hF4 : GGTwistedF4DiagInput) :
    GGRawInnFieldOn fun lab => lab.tag = .twF4 := by
  intro p hp _ lab hlab ht Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQK, fun hs hna => ?_⟩
  exact ggRawInnField_twF4_of_diag (by omega) hK (hF4 _ (by omega) K hK hs) hp.one_lt.ne' hs hna

end Labels

end CFSG.StandardType

end
