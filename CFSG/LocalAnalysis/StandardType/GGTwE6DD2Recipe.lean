module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGSmallKGInputsTwE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeTorality
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeInn

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TwE6DD2


section Transport

variable {K : Type} [Field K]

section Kappa

variable {n : ℕ} {σ : K →+* K}
  (T : ↥(graphFixedRootGroup TwistTag.E6 K σ) ≃* ↥(SmallKG.twH K n))
  (hZ : Subgroup.center ↥(SmallKG.twH K n) = ⊥)
  (e : Module.End K (RootModule TwistTag.E6.tag K) ≃*
    Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K))
  (hT : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ),
    ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
        Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
      e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)))
  (he : ∀ b : Fin TwistTag.E6.tag.rank → Kˣ,
    e (rootDiag b) = LargeEvenDiagMap TwistTag.E6.tag.cartan K b)

include hT he in
theorem recipeKappa_diag_mem {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : b ∈ SmallKG.compatParam K σ) :
    SmallKG.recipeKappa T hZ
        ⟨rootDiagUnit TwistTag.E6.tag b, 1, one_mem _, b, hb, (one_mul _).symm⟩ ∈
      LargeEvenChevDiagImage TwistTag.E6.tag.cartan K (SmallKG.twH K n) := by
  have hrel : ∀ g g' : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      ((T g' : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) *
          LargeEvenDiagMap TwistTag.E6.tag.cartan K b =
        LargeEvenDiagMap TwistTag.E6.tag.cartan K b *
          ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
            Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) ↔
      (g' : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b =
        rootDiagUnit TwistTag.E6.tag b * g := by
    intro g g'
    rw [hT, hT, ← he, ← map_mul, ← map_mul, e.injective.eq_iff, Units.ext_iff, Units.val_mul,
      Units.val_mul]
    rfl
  have hN := rootDiagUnit_mem_normalizer_graphFixedRootGroup (t := TwistTag.E6) (σ := σ) hb
  refine ⟨b, fun h => ?_, fun h' => ?_, fun h h' hr => ?_⟩
  · have hm := (Subgroup.mem_normalizer_iff.1 hN
      ((T.symm h : ↥(graphFixedRootGroup TwistTag.E6 K σ)) : ModGL TwistTag.E6.tag K)).1
      (T.symm h).2
    refine ⟨T ⟨_, hm⟩, ?_⟩
    have h1 := (hrel (T.symm h) ⟨_, hm⟩).2 (by
      change rootDiagUnit TwistTag.E6.tag b * (T.symm h : ModGL TwistTag.E6.tag K) *
          (rootDiagUnit TwistTag.E6.tag b)⁻¹ * rootDiagUnit TwistTag.E6.tag b =
        rootDiagUnit TwistTag.E6.tag b * (T.symm h : ModGL TwistTag.E6.tag K)
      group)
    rwa [T.apply_symm_apply] at h1
  · have hm := (Subgroup.mem_normalizer_iff.1 (inv_mem hN)
      ((T.symm h' : ↥(graphFixedRootGroup TwistTag.E6 K σ)) : ModGL TwistTag.E6.tag K)).1
      (T.symm h').2
    rw [inv_inv] at hm
    refine ⟨T ⟨_, hm⟩, ?_⟩
    have h1 := (hrel ⟨_, hm⟩ (T.symm h')).2 (by
      change (T.symm h' : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b =
        rootDiagUnit TwistTag.E6.tag b * ((rootDiagUnit TwistTag.E6.tag b)⁻¹ *
          (T.symm h' : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b)
      group)
    rwa [T.apply_symm_apply] at h1
  · obtain ⟨g, rfl⟩ := T.surjective h
    obtain ⟨g', rfl⟩ := T.surjective h'
    have hg' := (hrel g g').1 hr
    rw [← SmallKG.recipeEquiv_apply T hZ g, ← SmallKG.recipeEquiv_apply T hZ g',
      SmallKG.recipeKappa_apply]
    congr 1
    apply Subtype.ext
    change rootDiagUnit TwistTag.E6.tag b * (g : ModGL TwistTag.E6.tag K) *
      (rootDiagUnit TwistTag.E6.tag b)⁻¹ = g'
    rw [← hg', mul_inv_cancel_right]

include hT he in
theorem recipeKappa_mem_recipeI (x : ↥(SmallKG.compatHat K σ)) :
    SmallKG.recipeKappa T hZ x ∈
      LargeEvenChevIDImage TwistTag.E6.tag.cartan K (SmallKG.twH K n) := by
  obtain ⟨x, h, hh, b, hb, rfl⟩ := x
  have hx : (⟨h * rootDiagUnit TwistTag.E6.tag b, h, hh, b, hb, rfl⟩ :
      ↥(SmallKG.compatHat K σ)) =
      ⟨h, h, hh, 1, one_mem _, by rw [rootDiagUnit_one, mul_one]⟩ *
        ⟨rootDiagUnit TwistTag.E6.tag b, 1, one_mem _, b, hb, (one_mul _).symm⟩ :=
    Subtype.ext rfl
  have h1 : SmallKG.recipeKappa T hZ ⟨h, h, hh, 1, one_mem _, by rw [rootDiagUnit_one, mul_one]⟩ =
      MulAut.conj (SmallKG.recipeEquiv T hZ ⟨h, hh⟩) :=
    TwE6D3.recipeKappa_of_mem T hZ ⟨h, hh⟩ _
  rw [hx, map_mul, h1]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
    (Subgroup.subset_closure (Or.inr (recipeKappa_diag_mem T hZ e hT he hb)))

end Kappa

variable [Finite K]

theorem compatHat_le_twInndiag (σ : K ≃+* K) :
    SmallKG.compatHat K σ.toRingHom ≤ RecipeExcLang.twInndiagGroup K σ := by
  rintro _ ⟨h, hh, b, hb, rfl⟩
  exact mul_mem (RecipeExcLang.graphFixedRootGroup_le_twInndiag σ hh)
    (RecipeExcLang.rootDiagUnit_mem_twInndiag hb)

theorem twInndiag_le_compatHat (σ : K ≃+* K) :
    RecipeExcLang.twInndiagGroup K σ ≤ SmallKG.compatHat K σ.toRingHom := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x (hx | ⟨b, hb, rfl⟩)
  · exact ⟨x, hx, 1, one_mem _, by rw [rootDiagUnit_one, mul_one]⟩
  · exact ⟨1, one_mem _, b, hb, (one_mul _).symm⟩

theorem congr_symm_recipeKappa {n : ℕ} (σ : K ≃+* K)
    (T : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* ↥(SmallKG.twH K n))
    (hZ : Subgroup.center ↥(SmallKG.twH K n) = ⊥) (x : ↥(SmallKG.compatHat K σ.toRingHom)) :
    (MulAut.congr (SmallKG.recipeEquiv T hZ)).symm (SmallKG.recipeKappa T hZ x) =
      RecipeExcLang.twConj K σ ⟨x, compatHat_le_twInndiag σ x.2⟩ := by
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    SmallKG.recipeKappa_apply, MulEquiv.symm_apply_apply]
  exact Subtype.ext rfl

end Transport

theorem exists_recipeEquiv {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ∃ ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n,
      ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
        MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ n := hσ
  obtain ⟨e, T₀, hT₀, he⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) n σ.toRingHom hσ'
  have hΓ :=
    (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ').2.2.1
  have hZ : Subgroup.center ↥(SmallKG.twH K n) = ⊥ := TwE6Delta.center_recipeH_eq_bot hn hK
  set T : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* ↥(SmallKG.twH K n) :=
    (MulEquiv.subgroupCongr hΓ.symm).trans T₀ with hTdef
  have hT : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
        e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) :=
    fun g => hT₀ _
  refine ⟨SmallKG.recipeEquiv T hZ, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨m, hm⟩ := SmallKG.recipeI_subset_range T hZ e hT he hx
    refine ⟨⟨m, compatHat_le_twInndiag σ m.2⟩, ?_⟩
    rw [← congr_symm_recipeKappa σ T hZ m, hm]
    exact (MulAut.congr (SmallKG.recipeEquiv T hZ)).symm_apply_apply x
  · obtain ⟨w, rfl⟩ := hx
    have hw := twInndiag_le_compatHat σ w.2
    have h1 := recipeKappa_mem_recipeI T hZ e hT he ⟨w, hw⟩
    rw [(MulEquiv.symm_apply_eq _).1 (congr_symm_recipeKappa σ T hZ ⟨w, hw⟩)] at h1
    exact h1

theorem exists_cubeTorus_recipe
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) {X : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
    (hX : IsElemAbelian 3 X)
    (hXI : (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
    (h5 : 3 ^ 5 ≤ Nat.card X) :
    ∃ Y : Subgroup (MulAut (TwE6Delta.RecipeR K n)), X ≤ Y ∧ IsElemAbelian 3 Y ∧
      (Y : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n ∧
      Nat.card Y = 3 ^ 6 ∧
      (9 ∣ 2 ^ n + 1 →
        Y ≤ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range ∧
        ∃ W : Subgroup (MulAut (TwE6Delta.RecipeR K n)),
          (∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) ∧ (∀ w ∈ W, w ^ 9 = 1) ∧
          ∀ y ∈ Y, ∃ w ∈ W, w ^ 3 = y) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨ε, hε⟩ := exists_recipeEquiv hn hK σ hσ
  set Φ := MulAut.congr ε with hΦ
  have hS : IsElemAbelian 3 (X.map Φ.symm.toMonoidHom) := TableB.isElemAbelian_map hX _
  have hScard : Nat.card (X.map Φ.symm.toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective (fun a b h => Φ.symm.injective h)
  have hSI : X.map Φ.symm.toMonoidHom ≤ (RecipeExcLang.twConj K σ).range := by
    rintro _ ⟨x, hx, rfl⟩
    refine (hε _).1 ?_
    change Φ (Φ.symm x) ∈ _
    rw [MulEquiv.apply_symm_apply]
    exact hXI hx
  obtain ⟨Y₀, hSY₀, hY₀tw, hY₀, hY₀c, h9₀⟩ :=
    exists_cubeTorus hn hK σ hσ h3 hS hSI (by rw [hScard]; exact h5)
  refine ⟨Y₀.map Φ.toMonoidHom, fun x hx => ⟨Φ.symm x, hSY₀ ⟨x, hx, rfl⟩,
    Φ.apply_symm_apply x⟩, TableB.isElemAbelian_map hY₀ _, ?_, ?_, fun h9 => ?_⟩
  · rintro _ ⟨y₀, hy₀, rfl⟩
    exact (hε y₀).2 (hY₀tw hy₀)
  · exact (Subgroup.card_map_of_injective (f := Φ.toMonoidHom)
      (fun a b h => Φ.injective h)).trans hY₀c
  · obtain ⟨hY₀inn, W₀, hW₀, hW₀9, hY₀W₀⟩ := h9₀ h9
    refine ⟨?_, W₀.map Φ.toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨y₀, hy₀, rfl⟩
      obtain ⟨c, rfl⟩ := hY₀inn hy₀
      refine ⟨ε c, ?_⟩
      ext r
      change ε c * r * (ε c)⁻¹ = ε (c * ε.symm r * c⁻¹)
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
      rw [← map_mul Φ.toMonoidHom, ← map_mul Φ.toMonoidHom, hW₀ w hw w' hw']
    · rintro _ ⟨w, hw, rfl⟩
      rw [← map_pow Φ.toMonoidHom, hW₀9 w hw, map_one]
    · rintro _ ⟨y₀, hy₀, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hY₀W₀ y₀ hy₀
      exact ⟨Φ.toMonoidHom w, ⟨w, hw, rfl⟩, (map_pow Φ.toMonoidHom w 3).symm⟩

end TwE6DD2

namespace TwE6D3

theorem rankFiveInn_holds :
    RankFiveInnInput := by
  intro K _ _ n hn hK h9 X hX hXI h5
  obtain ⟨Y, hXY, -, -, -, hY⟩ :=
    TwE6DD2.exists_cubeTorus_recipe hn hK ((by norm_num : 3 ∣ 9).trans h9) hX hXI h5
  exact hXY.trans (hY h9).1

end TwE6D3

end CFSG.StandardType
