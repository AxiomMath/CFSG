module

public import CFSG.Quasithin.Background.StabTransport
public import CFSG.Quasithin.Background.ElemAbTransport
public import CFSG.Quasithin.Background.HDefs
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.Quasithin

namespace H

open CFSG.Open

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem mQuot_bot_eq_rk {G : Type*} [Group G] (A : Subgroup G) : E3.mQuot A ⊥ = rk ↥A := by
  unfold E3.mQuot rk
  rw [Subgroup.relIndex_bot_left]

abbrev congrHom (e : V ≃* W) : MulAut V →* MulAut W := (MulAut.congr e).toMonoidHom

theorem congrHom_injective (e : V ≃* W) : Function.Injective (congrHom e) :=
  (MulAut.congr e).injective

theorem congrHom_apply (e : V ≃* W) (x : MulAut V) (w : W) :
    congrHom e x w = e (x (e.symm w)) := rfl

theorem exists_eq_map_congrHom (e : V ≃* W) {X : Subgroup (MulAut V)}
    {B : Subgroup (MulAut W)} (hB : B ≤ X.map (congrHom e)) :
    ∃ B₀ : Subgroup (MulAut V), B₀ ≤ X ∧ B₀.map (congrHom e) = B := by
  refine ⟨B.comap (congrHom e), ?_, Subgroup.map_comap_eq_self
    (hB.trans (Subgroup.map_le_range _ _))⟩
  have := Subgroup.comap_mono (f := congrHom e) hB
  rwa [Subgroup.comap_map_eq_self_of_injective (congrHom_injective e)] at this

theorem map_congrHom_le_iff (e : V ≃* W) {A B : Subgroup (MulAut V)} :
    A.map (congrHom e) ≤ B.map (congrHom e) ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective (congrHom_injective e)

theorem map_congrHom_inj (e : V ≃* W) {A B : Subgroup (MulAut V)} :
    A.map (congrHom e) = B.map (congrHom e) ↔ A = B :=
  (Subgroup.map_injective (congrHom_injective e)).eq_iff

theorem fixV_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) :
    fixV (X.map (congrHom e)) = (fixV X).map e.toMonoidHom :=
  E3.fixV_map_congr e X

theorem rkIdx_fixV_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) :
    rkIdx (fixV (X.map (congrHom e))) = rkIdx (fixV X) := by
  rw [fixV_map_congrHom, E3.rkIdx_map_equiv]

theorem centSub_map_congrHom (e : V ≃* W) (U : Subgroup V) :
    (centSub U).map (congrHom e) = centSub (U.map e.toMonoidHom) :=
  (CFSG.Quasithin.StabLat.centSub_map_equiv e U).symm

theorem inf_centSub_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) (U : Subgroup V) :
    (X ⊓ centSub U).map (congrHom e) = X.map (congrHom e) ⊓ centSub (U.map e.toMonoidHom) := by
  rw [Subgroup.map_inf _ _ _ (congrHom_injective e), centSub_map_congrHom]

theorem card_map_congrHom (e : V ≃* W) (A : Subgroup (MulAut V)) :
    Nat.card ↥(A.map (congrHom e)) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (congrHom_injective e)

theorem rk_map_congrHom (e : V ≃* W) (A : Subgroup (MulAut V)) :
    rk ↥(A.map (congrHom e)) = rk ↥A := by
  unfold rk
  rw [card_map_congrHom]

theorem isElemAbelian2_map_congrHom (e : V ≃* W) {A : Subgroup (MulAut V)} :
    IsElemAbelian2 (A.map (congrHom e)) ↔ IsElemAbelian2 A :=
  CFSG.Quasithin.FixVLat.isElemAbelian2_map_iff_of_injective (congrHom_injective e)

theorem isA2_map_congrHom (e : V ≃* W) {X A : Subgroup (MulAut V)} :
    IsA2 (X.map (congrHom e)) (A.map (congrHom e)) ↔ IsA2 X A := by
  unfold IsA2
  rw [map_congrHom_le_iff, isElemAbelian2_map_congrHom, ne_eq, ne_eq,
    Subgroup.map_eq_bot_iff_of_injective _ (congrHom_injective e)]

theorem mQuot_map_congrHom (e : V ≃* W) (A B : Subgroup (MulAut V)) :
    E3.mQuot (A.map (congrHom e)) (B.map (congrHom e)) = E3.mQuot A B := by
  unfold E3.mQuot
  rw [Subgroup.relIndex_map_map_of_injective _ _ (congrHom_injective e)]

theorem map_mem_aSet_iff (e : V ≃* W) {k : ℕ} {X A : Subgroup (MulAut V)} :
    A.map (congrHom e) ∈ E3.aSet k (X.map (congrHom e)) ↔ A ∈ E3.aSet k X := by
  unfold E3.aSet
  simp only [Set.mem_ofPred_eq]
  rw [map_congrHom_le_iff, ne_eq, Subgroup.map_eq_bot_iff_of_injective _ (congrHom_injective e),
    isElemAbelian2_map_congrHom]
  refine and_congr_right fun hAX => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h B hB hm
    have h1 := h (B.map (congrHom e)) ((map_congrHom_le_iff e).mpr hB)
      (by rwa [mQuot_map_congrHom])
    rw [fixV_map_congrHom, fixV_map_congrHom] at h1
    exact Subgroup.map_injective e.injective h1
  · intro h B hB hm
    obtain ⟨B₀, -, rfl⟩ := exists_eq_map_congrHom e (hB.trans (Subgroup.map_mono hAX))
    have hB₀ : B₀ ≤ A := (map_congrHom_le_iff e).mp hB
    rw [mQuot_map_congrHom] at hm
    rw [fixV_map_congrHom, fixV_map_congrHom, h B₀ hB₀ hm]

theorem aSet_nonempty_map_congrHom (e : V ≃* W) {k : ℕ} {X : Subgroup (MulAut V)} :
    (E3.aSet k (X.map (congrHom e))).Nonempty ↔ (E3.aSet k X).Nonempty := by
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨B₀, -, rfl⟩ := exists_eq_map_congrHom e hB.1
    exact ⟨B₀, (map_mem_aSet_iff e).mp hB⟩
  · rintro ⟨A, hA⟩
    exact ⟨_, (map_mem_aSet_iff e).mpr hA⟩

theorem aParam_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) :
    E3.aParam (X.map (congrHom e)) = E3.aParam X := by
  unfold E3.aParam
  rw [card_map_congrHom]
  split_ifs
  · congr 1
    ext k
    simp only [Set.mem_ofPred_eq, aSet_nonempty_map_congrHom]
  · rfl

theorem mParam_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) :
    E3.mParam (X.map (congrHom e)) = E3.mParam X :=
  E3.mParam_map_congr e X

theorem isPGroup_map_congrHom (e : V ≃* W) {X : Subgroup (MulAut V)} :
    IsPGroup 2 ↥(X.map (congrHom e)) ↔ IsPGroup 2 ↥X :=
  ⟨fun h => h.of_equiv (X.equivMapOfInjective _ (congrHom_injective e)).symm,
    fun h => h.of_equiv (X.equivMapOfInjective _ (congrHom_injective e))⟩

theorem pRank_two_map_congrHom [Finite V] [Finite W] (e : V ≃* W) (X : Subgroup (MulAut V)) :
    CFSG.Open.pRank 2 (X.map (congrHom e)) = CFSG.Open.pRank 2 X := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  have : Finite (MulAut W) := MulEquiv.finite_left
  exact pRank_two_map_of_injective _ (congrHom_injective e) X

theorem rkIdx_map_mulEquiv (e : V ≃* W) (U : Subgroup V) :
    rkIdx (U.map e.toMonoidHom) = rkIdx U :=
  E3.rkIdx_map_equiv e U

theorem map_mulEquiv_eq_top_iff (e : V ≃* W) {U : Subgroup V} :
    U.map e.toMonoidHom = ⊤ ↔ U = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro v _
    have : e v ∈ U.map e.toMonoidHom := by rw [h]; trivial
    obtain ⟨u, hu, huv⟩ := this
    rw [← e.injective huv]
    exact hu
  · rintro rfl
    rw [eq_top_iff]
    intro w _
    exact ⟨e.symm w, trivial, by simp⟩

theorem exists_eq_map_mulEquiv (e : V ≃* W) (U' : Subgroup W) :
    ∃ U : Subgroup V, U.map e.toMonoidHom = U' :=
  ⟨U'.map e.symm.toMonoidHom, by
    rw [Subgroup.map_map]
    convert Subgroup.map_id U'
    ext w
    simp⟩

theorem betaH_map_congrHom [Finite V] (e : V ≃* W) (X : Subgroup (MulAut V)) :
    betaH (X.map (congrHom e)) = betaH X := by
  have : Finite W := Finite.of_equiv V e.toEquiv
  have : Finite (MulAut V) := MulEquiv.finite_left
  have : Finite (MulAut W) := MulEquiv.finite_left
  apply le_antisymm
  · rw [le_betaH_iff]
    intro U hU hres
    have h := (le_betaH_iff (M := X.map (congrHom e))).mp le_rfl (U.map e.toMonoidHom)
      (by rwa [ne_eq, map_mulEquiv_eq_top_iff]) (by
        rw [ne_eq, twoResidual_eq_bot_iff] at hres ⊢
        rwa [← inf_centSub_map_congrHom, isPGroup_map_congrHom])
    rwa [rkIdx_map_mulEquiv] at h
  · rw [le_betaH_iff]
    intro U' hU' hres
    obtain ⟨U, rfl⟩ := exists_eq_map_mulEquiv e U'
    have h := (le_betaH_iff (M := X)).mp le_rfl U (by rwa [ne_eq, map_mulEquiv_eq_top_iff] at hU')
      (by
        rw [ne_eq, twoResidual_eq_bot_iff] at hres ⊢
        rwa [← inf_centSub_map_congrHom, isPGroup_map_congrHom] at hres)
    rwa [rkIdx_map_mulEquiv]

theorem alphaSet_map_congrHom [Finite V] [Finite W] (e : V ≃* W) (X : Subgroup (MulAut V)) :
    alphaSet (X.map (congrHom e)) = alphaSet X := by
  ext k
  simp only [alphaSet, Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨U', hU', hk, hkr⟩
    obtain ⟨U, rfl⟩ := exists_eq_map_mulEquiv e U'
    refine ⟨U, by rwa [ne_eq, map_mulEquiv_eq_top_iff] at hU', by rwa [rkIdx_map_mulEquiv] at hk,
      ?_⟩
    rwa [← inf_centSub_map_congrHom, pRank_two_map_congrHom] at hkr
  · rintro ⟨U, hU, hk, hkr⟩
    refine ⟨U.map e.toMonoidHom, by rwa [ne_eq, map_mulEquiv_eq_top_iff], by
      rwa [rkIdx_map_mulEquiv], ?_⟩
    rwa [← inf_centSub_map_congrHom, pRank_two_map_congrHom]

theorem alphaH_map_congrHom [Finite V] [Finite W] (e : V ≃* W) (X : Subgroup (MulAut V)) :
    alphaH (X.map (congrHom e)) = alphaH X := by
  unfold alphaH
  rw [alphaSet_map_congrHom]

theorem isFOneOffender_map_congrHom (e : V ≃* W) {X A : Subgroup (MulAut V)} :
    IsFOneOffender (X.map (congrHom e)) (A.map (congrHom e)) ↔ IsFOneOffender X A := by
  unfold IsFOneOffender
  rw [isA2_map_congrHom, rkIdx_fixV_map_congrHom, rk_map_congrHom]

theorem isFOneModule_map_congrHom (e : V ≃* W) {X : Subgroup (MulAut V)} :
    IsFOneModule (X.map (congrHom e)) ↔ IsFOneModule X := by
  constructor
  · rintro ⟨A', hA'⟩
    obtain ⟨A, -, rfl⟩ := exists_eq_map_congrHom e hA'.1.1
    exact ⟨A, (isFOneOffender_map_congrHom e).mp hA'⟩
  · rintro ⟨A, hA⟩
    exact ⟨_, (isFOneOffender_map_congrHom e).mpr hA⟩

theorem hypBang_map_congrHom (e : V ≃* W) {X : Subgroup (MulAut V)} :
    HypBang (X.map (congrHom e)) ↔ HypBang X := by
  let φ : ↥X ≃* ↥(X.map (congrHom e)) := X.equivMapOfInjective _ (congrHom_injective e)
  constructor
  · rintro ⟨Y, _, _, hY, ψ, hψ⟩
    exact ⟨Y, _, _, hY, φ.symm.toMonoidHom.comp ψ, φ.symm.surjective.comp hψ⟩
  · rintro ⟨Y, _, _, hY, ψ, hψ⟩
    exact ⟨Y, _, _, hY, φ.toMonoidHom.comp ψ, φ.surjective.comp hψ⟩

end H

end CFSG.Quasithin
