module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdE6Core
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace MpStdE6

section Range

variable {F : Type} [Field F] {G : Type*} [Group G] (ψ : ↥(e6Data_valid.minGroup F) →* G)

@[expose] noncomputable def rangeProj :
    ↥(e6Data_valid.minGroup F) →* ↥ψ.range ⧸ Subgroup.center ↥ψ.range :=
  (QuotientGroup.mk' _).comp ψ.rangeRestrict

theorem rangeProj_surjective : Function.Surjective (rangeProj ψ) :=
  (QuotientGroup.mk'_surjective _).comp ψ.rangeRestrict_surjective

theorem ker_rangeProj (hker : ψ.ker ≤ Subgroup.center _) :
    (rangeProj ψ).ker = Subgroup.center ↥(e6Data_valid.minGroup F) := by
  have hperf : commutator ↥(e6Data_valid.minGroup F) = ⊤ :=
    Group.isPerfect_def.mp (isPerfect_e6 F)
  ext u
  rw [MonoidHom.mem_ker]
  show (QuotientGroup.mk (ψ.rangeRestrict u) : ↥ψ.range ⧸ Subgroup.center ↥ψ.range) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  refine ⟨InnerDiagA.mem_center_of_rangeRestrict_mem_center hperf ψ hker, fun hu => ?_⟩
  rw [Subgroup.mem_center_iff]
  intro l
  obtain ⟨s, rfl⟩ := ψ.rangeRestrict_surjective l
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]

end Range

section Std

variable {F : Type} [Field F] [Finite F] {K : Type} [Field K] [Finite K] (σ : F ≃+* K)
  (T : adjointGroup .E6 K ≃* ↥(LargeEvenChevH (LargeEvenCartanE 6) K false))

theorem center_chevH_eq_bot :
    Subgroup.center ↥(LargeEvenChevH (LargeEvenCartanE 6) K false) = ⊥ := by
  obtain ⟨T, -, -⟩ := InnerDiagE6.exists_largeEvenChevEquiv (τ := .E6) (K := K)
  exact InnerDiagE6.center_eq_bot_of_mulEquiv T center_adjointGroup_eq_bot

@[expose] noncomputable def stdHom :
    ↥(e6Data_valid.minGroup F) →* ↥(LargeEvenChevH (LargeEvenCartanE 6) K false) :=
  T.toMonoidHom.comp ((adjEquiv σ .E6).toMonoidHom.comp (e6Isogeny F))

omit [Finite K]
  in
theorem stdHom_apply (u : ↥(e6Data_valid.minGroup F)) :
    stdHom σ T u = T (adjEquiv σ .E6 (e6Isogeny F u)) :=
  rfl

@[expose] noncomputable def stdProj :
    ↥(e6Data_valid.minGroup F) →* LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false) :=
  (LargeEvenCenterMk _).comp (stdHom σ T)

omit [Finite K]
  in
theorem stdProj_surjective : Function.Surjective (stdProj σ T) :=
  (QuotientGroup.mk'_surjective _).comp (T.surjective.comp ((adjEquiv σ .E6).surjective.comp
    (e6Isogeny_surjective F)))

theorem ker_e6Isogeny_eq_center :
    (e6Isogeny F).ker = Subgroup.center ↥(e6Data_valid.minGroup F) := by
  refine le_antisymm (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center F)
    fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hzc : e6Isogeny F z ∈ Subgroup.center (adjointGroup .E6 F) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨y, rfl⟩ := e6Isogeny_surjective F x
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [center_adjointGroup_eq_bot] at hzc
  exact hzc

theorem ker_stdProj :
    (stdProj σ T).ker = Subgroup.center ↥(e6Data_valid.minGroup F) := by
  rw [← ker_e6Isogeny_eq_center]
  ext u
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  show (QuotientGroup.mk (stdHom σ T u) :
    LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, center_chevH_eq_bot, Subgroup.mem_bot, stdHom_apply]
  constructor
  · intro h
    have h1 : adjEquiv σ .E6 (e6Isogeny F u) = 1 := T.injective (h.trans (map_one T).symm)
    exact (adjEquiv σ .E6).injective (h1.trans (map_one _).symm)
  · intro h
    rw [h, map_one, map_one]

variable {G : Type*} [Group G] (ψ : ↥(e6Data_valid.minGroup F) →* G)

@[expose] noncomputable def stdEquiv (hker : ψ.ker ≤ Subgroup.center _) :
    ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃*
      LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false) :=
  (QuotientGroup.quotientKerEquivOfSurjective (rangeProj ψ) (rangeProj_surjective ψ)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      ((ker_rangeProj ψ hker).trans (ker_stdProj σ T).symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (stdProj σ T) (stdProj_surjective σ T)))

theorem stdEquiv_rangeProj (hker : ψ.ker ≤ Subgroup.center _) (u : ↥(e6Data_valid.minGroup F)) :
    stdEquiv σ T ψ hker (rangeProj ψ u) = stdProj σ T u := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective (rangeProj ψ)
      (rangeProj_surjective ψ)).symm (rangeProj ψ u) =
      (u : ↥(e6Data_valid.minGroup F) ⧸ (rangeProj ψ).ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  simp only [stdEquiv, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end Std

section Act

variable {F : Type} [Field F] [Finite F] {K : Type} [Field K] [Finite K] (σ : F ≃+* K)
  (T : adjointGroup .E6 K ≃* ↥(LargeEvenChevH (LargeEvenCartanE 6) K false))

@[expose] noncomputable def xiEquiv :
    LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false) ≃* adjointGroup .E6 F :=
  (centerQuotEquivOfBot center_chevH_eq_bot).trans (T.symm.trans (adjEquiv σ .E6).symm)

theorem xiEquiv_stdProj (u : ↥(e6Data_valid.minGroup F)) :
    xiEquiv σ T (stdProj σ T u) = e6Isogeny F u := by
  show (adjEquiv σ .E6).symm (T.symm (centerQuotEquivOfBot center_chevH_eq_bot
    (LargeEvenCenterMk _ (stdHom σ T u)))) = _
  rw [centerQuotEquivOfBot_mk, stdHom_apply, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply]

omit [Finite F]
  in
theorem xiEquiv_symm_apply (x : adjointGroup .E6 F) :
    (xiEquiv σ T).symm x = LargeEvenCenterMk _ (T (adjEquiv σ .E6 x)) := by
  rw [MulEquiv.symm_apply_eq]
  show x = (adjEquiv σ .E6).symm (T.symm (centerQuotEquivOfBot center_chevH_eq_bot
    (LargeEvenCenterMk _ (T (adjEquiv σ .E6 x)))))
  rw [centerQuotEquivOfBot_mk, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

variable (hTx : ∀ (i : Fin (Tag.rank .E6)) (c : K),
      ((T (xElement i c) : LargeEvenChevGL (LargeEvenCartanE 6) K) :
        Module.End K (LargeEvenChevModule (LargeEvenCartanE 6) K)) =
          LargeEvenXOp (LargeEvenCartanE 6) K i c)
  (hTy : ∀ (i : Fin (Tag.rank .E6)) (c : K),
      ((T (yElement i c) : LargeEvenChevGL (LargeEvenCartanE 6) K) :
        Module.End K (LargeEvenChevModule (LargeEvenCartanE 6) K)) =
          LargeEvenYOp (LargeEvenCartanE 6) K i c)

omit [Finite F]
  in
include hTx hTy in
theorem ggInndiag_le :
    ggInndiag (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
        (LargeEvenChevIDImage (LargeEvenCartanE 6) K
          (LargeEvenChevH (LargeEvenCartanE 6) K false)) ≤
      ((diagAdj .E6 F).map (adjointGroup .E6 F).normalizerMonoidHom).comap
        (MulAut.congr (xiEquiv σ T)).toMonoidHom := by
  have hInn : ∀ r, MulAut.conj r ∈
      ((diagAdj .E6 F).map (adjointGroup .E6 F).normalizerMonoidHom).comap
        (MulAut.congr (xiEquiv σ T)).toMonoidHom := by
    intro r
    refine ⟨⟨(xiEquiv σ T r : ModGL .E6 F), Subgroup.le_normalizer (xiEquiv σ T r).2⟩,
      ⟨xiEquiv σ T r, (xiEquiv σ T r).2, 1, by rw [rootDiagUnit_one, mul_one]⟩,
      MulEquiv.ext fun x => Subtype.ext ?_⟩
    show (xiEquiv σ T r : ModGL .E6 F) * x * (xiEquiv σ T r : ModGL .E6 F)⁻¹ =
      ((xiEquiv σ T (r * (xiEquiv σ T).symm x * r⁻¹) : adjointGroup .E6 F) : ModGL .E6 F)
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  have hDiag : ∀ φ ∈ LargeEvenChevDiagImage (LargeEvenCartanE 6) K
      (LargeEvenChevH (LargeEvenCartanE 6) K false), φ ∈
      ((diagAdj .E6 F).map (adjointGroup .E6 F).normalizerMonoidHom).comap
        (MulAut.congr (xiEquiv σ T)).toMonoidHom := by
    rintro φ ⟨a, -, -, hφ⟩
    set a' : Fin (Tag.rank .E6) → Fˣ := fun i => Units.map σ.symm.toRingHom.toMonoidHom (a i)
      with ha'
    have haa : (fun i => Units.map σ.toRingHom.toMonoidHom (a' i)) = a := by
      funext i
      apply Units.ext
      simp [ha']
    refine ⟨⟨rootDiagUnit .E6 a', rootDiagUnit_mem_normalizer a'⟩,
      ⟨1, one_mem _, a', by rw [one_mul]⟩, MulEquiv.ext fun x => ?_⟩
    set y : adjointGroup .E6 F :=
      ⟨rootDiagUnit .E6 a' * (x : ModGL .E6 F) * (rootDiagUnit .E6 a')⁻¹,
        conj_rootDiag_mem a' x.2⟩ with hy
    have hyx : (adjointGroup .E6 F).normalizerMonoidHom
        ⟨rootDiagUnit .E6 a', rootDiagUnit_mem_normalizer a'⟩ x = y := rfl
    have hadj : adjEquiv σ .E6 y = ⟨rootDiagUnit .E6 a * (adjEquiv σ .E6 x : ModGL .E6 K) *
        (rootDiagUnit .E6 a)⁻¹, conj_rootDiag_mem (t := .E6) a (adjEquiv σ .E6 x).2⟩ := by
      apply Subtype.ext
      rw [coe_adjEquiv, hy]
      show baseChangeGL σ.toRingHom (rootDiagUnit .E6 a' * (x : ModGL .E6 F) *
        (rootDiagUnit .E6 a')⁻¹) = _
      rw [baseChangeGL_conj_rootDiag, haa]
      rfl
    have hT : ((T (adjEquiv σ .E6 y) : ↥(LargeEvenChevH (LargeEvenCartanE 6) K false)) :
        LargeEvenChevGL (LargeEvenCartanE 6) K) =
        TableB.diagHom (LargeEvenCartanE 6) K a * T (adjEquiv σ .E6 x) *
          (TableB.diagHom (LargeEvenCartanE 6) K a)⁻¹ := by
      rw [hadj]
      exact transfer_conj_rootDiag .E6 T hTx hTy a (adjEquiv σ .E6 x)
    have hrel : ((T (adjEquiv σ .E6 y) : LargeEvenChevGL (LargeEvenCartanE 6) K) :
        Module.End K (LargeEvenChevModule (LargeEvenCartanE 6) K)) *
          LargeEvenDiagMap (LargeEvenCartanE 6) K a =
        LargeEvenDiagMap (LargeEvenCartanE 6) K a *
          ((T (adjEquiv σ .E6 x) : LargeEvenChevGL (LargeEvenCartanE 6) K) :
            Module.End K (LargeEvenChevModule (LargeEvenCartanE 6) K)) := by
      rw [hT]
      show ((TableB.diagHom (LargeEvenCartanE 6) K a * T (adjEquiv σ .E6 x) *
          (TableB.diagHom (LargeEvenCartanE 6) K a)⁻¹ * TableB.diagHom (LargeEvenCartanE 6) K a :
            LargeEvenChevGL (LargeEvenCartanE 6) K) :
          Module.End K (LargeEvenChevModule (LargeEvenCartanE 6) K)) =
        ((TableB.diagHom (LargeEvenCartanE 6) K a * T (adjEquiv σ .E6 x) :
            LargeEvenChevGL (LargeEvenCartanE 6) K) :
          Module.End K (LargeEvenChevModule (LargeEvenCartanE 6) K))
      rw [inv_mul_cancel_right]
    have h1 := hφ (T (adjEquiv σ .E6 x)) (T (adjEquiv σ .E6 y)) hrel
    rw [hyx]
    show y = xiEquiv σ T (φ ((xiEquiv σ T).symm x))
    rw [xiEquiv_symm_apply, h1]
    show y = (adjEquiv σ .E6).symm (T.symm (centerQuotEquivOfBot center_chevH_eq_bot
      (LargeEvenCenterMk _ (T (adjEquiv σ .E6 y)))))
    rw [centerQuotEquivOfBot_mk, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  refine sup_le ?_ ((Subgroup.closure_le _).mpr ?_)
  · rintro _ ⟨r, rfl⟩
    exact hInn r
  · intro φ hφ
    refine (Subgroup.closure_le _).mpr ?_ hφ
    rintro ψ' (⟨r, rfl⟩ | hψ')
    · exact hInn r
    · exact hDiag ψ' hψ'

end Act

section Rev

variable {F : Type} [Field F] [Finite F] [CharP F 2] {K : Type} [Field K] [Finite K]
  (σ : F ≃+* K) (T : adjointGroup .E6 K ≃* ↥(LargeEvenChevH (LargeEvenCartanE 6) K false))
  (hTx : ∀ (i : Fin (Tag.rank .E6)) (c : K),
      ((T (xElement i c) : LargeEvenChevGL (LargeEvenCartanE 6) K) :
        Module.End K (LargeEvenChevModule (LargeEvenCartanE 6) K)) =
          LargeEvenXOp (LargeEvenCartanE 6) K i c)
  (hTy : ∀ (i : Fin (Tag.rank .E6)) (c : K),
      ((T (yElement i c) : LargeEvenChevGL (LargeEvenCartanE 6) K) :
        Module.End K (LargeEvenChevModule (LargeEvenCartanE 6) K)) =
          LargeEvenYOp (LargeEvenCartanE 6) K i c)

include hTx hTy in
theorem ggRevProp_stdEquiv {G : Type*} [Group G] (ψ : ↥(e6Data_valid.minGroup F) →* G)
    (hker : ψ.ker ≤ Subgroup.center _) :
    GGRevProp (e6Datum F) ψ ψ.range
      (ggInndiag (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
        (LargeEvenChevIDImage (LargeEvenCartanE 6) K
          (LargeEvenChevH (LargeEvenCartanE 6) K false)))
      (stdEquiv σ T ψ hker) := by
  rintro c hc ⟨φ, hφ, hind⟩
  obtain ⟨y, ⟨g, hg, a, hy⟩, hκ⟩ := ggInndiag_le σ T hTx hTy hφ
  obtain ⟨a₀, ha₀⟩ := e6Isogeny_surjective F ⟨g, hg⟩
  have ha₀' : ((e6Isogeny F a₀ : adjointGroup .E6 F) : ModGL .E6 F) = g := by rw [ha₀]
  have hodd : Odd (Nat.card (e6Isogeny F).ker) := by
    have h := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker F (p := 2)
    exact Nat.not_even_iff_odd.mp fun he => h (even_iff_two_dvd.mp he)
  have hinv : ∀ δ ∈ (e6Datum F).roots, ∀ z ∈ (e6Datum F).rootGroup δ, z * z = 1 := by
    intro δ _ z hz
    obtain ⟨t, rfl⟩ := (e6Data_valid.mem_rootGroup F).mp hz
    rw [← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]
  refine ggPsiInnerDiag_of_conj_diag (e6Datum F)
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center F) hodd hinv a
    (fun δ hδ => RootDetectExc.hdiag_E6 F δ hδ a) hc a₀ fun y₁ y₂ h12 => ?_
  have h1 := hind (ψ.rangeRestrict y₁) (ψ.rangeRestrict y₂) h12
  change φ (stdEquiv σ T ψ hker (rangeProj ψ y₁)) = stdEquiv σ T ψ hker (rangeProj ψ y₂) at h1
  rw [stdEquiv_rangeProj, stdEquiv_rangeProj] at h1
  have h2 : (MulAut.congr (xiEquiv σ T)).toMonoidHom φ (e6Isogeny F y₁) = e6Isogeny F y₂ := by
    show xiEquiv σ T (φ ((xiEquiv σ T).symm (e6Isogeny F y₁))) = e6Isogeny F y₂
    rw [← xiEquiv_stdProj σ T y₁, MulEquiv.symm_apply_apply, h1, xiEquiv_stdProj]
  rw [← hκ] at h2
  have h3 := congrArg Subtype.val h2
  rw [← h3, ha₀']
  show (y : ModGL .E6 F) * ((e6Isogeny F y₁ : adjointGroup .E6 F) : ModGL .E6 F) *
    (y : ModGL .E6 F)⁻¹ = _
  rw [hy]
  group

include σ hTx hTy in
theorem exists_stdEquiv_revProp {G : Type*} [Group G] (ψ : ↥(e6Data_valid.minGroup F) →* G)
    (hker : ψ.ker ≤ Subgroup.center _) :
    ∃ θ₀ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃*
        LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false),
      GGRevProp (e6Datum F) ψ ψ.range
        (ggInndiag (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
          (LargeEvenChevIDImage (LargeEvenCartanE 6) K
            (LargeEvenChevH (LargeEvenCartanE 6) K false))) θ₀ :=
  ⟨_, ggRevProp_stdEquiv σ T hTx hTy ψ hker⟩

end Rev

end MpStdE6

section Input

theorem ggInnerDiagStdE6_holds : GGInnerDiagStdE6 := by
  intro G _ _ f ψ hadm _ hker K _ _ hK
  have hf : 1 ≤ f := hadm.2.1
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 f)
  have hcard : Fintype.card (GaloisField 2 f) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hK]
  obtain ⟨T, hTx, hTy⟩ := InnerDiagE6.exists_largeEvenChevEquiv (τ := .E6) (K := K)
  exact MpStdE6.exists_stdEquiv_revProp (FiniteField.ringEquivOfCardEq hcard) T hTx hTy ψ hker

end Input

end CFSG.StandardType
