module

public import CFSG.Milestones.ASVolI.B1

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement

@[expose] def B_7_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G A : Subgroup (MulAut V), IsFFStarOffender G A →
      ∀ W : Subgroup V, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → commSub W A ≠ ⊥ →
        IsFFStarOffender (autSub G W) (autSub A W) ∧
        (IsFFStarMin G A →
          IsFFStarMin (autSub G W) (autSub A W) ∧
          (rk (autSub A W) = rkIdx (fixV (autSub A W)) →
            W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥) ∧
          (¬ IsStrongFFStarOffender (autSub G W) (autSub A W) →
            rk (autSub A W) = rkIdx (fixV (autSub A W)))) ∧
        (rk (autSub A W) = rkIdx (fixV (autSub A W)) →
          (A ⊓ centSub W = ⊥ ∧ W ⊔ fixV A = ⊤) ∨
          (IsFFStarOffender G (A ⊓ centSub W) ∧ FFLe G (A ⊓ centSub W) A))

section BurnsideB7a

private theorem burnsideB7a_rk_eq_rkIdx_of_not_strong {V : Type*} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} (hA : CFSG.Quasithin.IsFFStarMin X A)
    {W : Subgroup V} (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) (hWA : CFSG.Quasithin.commSub W A ≠ ⊥)
    (hns : ¬ CFSG.Quasithin.IsStrongFFStarOffender (CFSG.Quasithin.autSub X W)
      (CFSG.Quasithin.autSub A W)) :
    CFSG.Quasithin.rk (CFSG.Quasithin.autSub A W) =
      CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV (CFSG.Quasithin.autSub A W)) := by
  have hAut := CFSG.Quasithin.B7_1_1 hA.1 hW hWA
  have hW2 := CFSG.Quasithin.B1.sq_eq_one_sub hV W
  have hr1 : CFSG.Quasithin.rAV (CFSG.Quasithin.autSub A W) ≤ 1 :=
    CFSG.Quasithin.B1_4_1 hW2 hAut
  have hr2 : ¬ CFSG.Quasithin.rAV (CFSG.Quasithin.autSub A W) < 1 :=
    fun h => hns ⟨hAut, h⟩
  exact CFSG.Quasithin.B1.rk_eq_rkIdx_of_rAV_eq_one hAut.isA2 (le_antisymm hr1 (not_lt.1 hr2))

private theorem burnsideB7a_allTwoChiefFactorsCentral {G : Type*} [Group G] [Finite G] {X :
    Subgroup G}
    (h : CFSG.ASVolI.ChB.TwoChiefFactorsCentral X) :
    CFSG.Quasithin.AllTwoChiefFactorsCentral X := by
  intro A B hAB
  obtain ⟨hBA, hAX, hXA, hXB, hmin, h2⟩ := hAB
  have hBX : B ≤ X := hBA.le.trans hAX
  have hnA : (A.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).2 hXA
  have hnB : (B.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBX).2 hXB
  have hnJ : ∀ J : Subgroup G, B ≤ J → J ≤ A → (J.subgroupOf X).Normal → J = B ∨ J = A := by
    intro J hBJ hJA hJn
    have hXJ : X ≤ Subgroup.normalizer (J : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hJA.trans hAX)).1 hJn
    by_contra hne
    push_neg at hne
    exact hmin J (lt_of_le_of_ne hBJ (Ne.symm hne.1)) (lt_of_le_of_ne hJA hne.2) hXJ
  have hrel : ∃ k : ℕ, B.relIndex A = 2 ^ k :=
    CFSG.Quasithin.B6.exists_relIndex_eq_two_pow (hAX.trans hXB) h2
  exact h B A hBA hAX hnB hnA hnJ hrel

private theorem burnsideB7a_oTwoUpper_eq_of_twoResidual {G : Type*} [Group G] [Finite G] {H :
    Subgroup G}
    (h : CFSG.Quasithin.twoResidual H = H) : CFSG.Quasithin.oTwoUpper H = H := by
  have h1 : CFSG.Quasithin.twoResidual H ≤ CFSG.Quasithin.oTwoUpper H :=
    CFSG.Quasithin.twoResidual_le_of_isTwoQuotient (CFSG.Quasithin.oTwoUpper_le H)
      (CFSG.Quasithin.le_normalizer_oTwoUpper H)
      (fun y hy => CFSG.Quasithin.exists_pow_mem_oTwoUpper H hy)
  rw [h] at h1
  exact le_antisymm (CFSG.Quasithin.oTwoUpper_le H) h1

end BurnsideB7a

theorem as_B_7_1 : B_7_1 := by
  intro V _ _ hV G A hA W hW hWA
  exact ⟨CFSG.Quasithin.B7_1_1 hA hW hWA,
    fun hmin => ⟨CFSG.Quasithin.B7_1_2_min hmin hW hWA,
      fun hm => (CFSG.Quasithin.B7_1_2_faithful hV hmin hW hWA hm).symm,
      fun hns => burnsideB7a_rk_eq_rkIdx_of_not_strong hV hmin hW hWA hns⟩,
    fun hm => CFSG.Quasithin.B7_1_3 hV hA hW hWA hm⟩

@[expose] def B_7_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G A : Subgroup (MulAut V), IsFFStarOffender G A →
      ∀ H : Subgroup (MulAut V), H ≠ ⊥ → H ≤ G → twoResidual H = H → ⁅H, A⁆ = H →
        TwoChiefFactorsCentral H →
        (∀ a ∈ A, commSub (commSub ⊤ (Subgroup.zpowers a)) A = ⊥ →
          ∀ I ∈ IrrPlus H ⊤, I.map a.toMonoidHom = I) ∧
        (IsFFStarMin G A → ∀ a ∈ A, ∀ I ∈ IrrPlus H ⊤, I.map a.toMonoidHom = I)

theorem as_B_7_2 : B_7_2 := by
  intro V _ _ hV G A hA H _hH0 _hHG hH hHA hCF
  have hoT : CFSG.Quasithin.oTwoUpper H = H := burnsideB7a_oTwoUpper_eq_of_twoResidual hH
  have hAll : CFSG.Quasithin.AllTwoChiefFactorsCentral H :=
    burnsideB7a_allTwoChiefFactorsCentral hCF
  refine ⟨fun a ha hz I hI => ?_, fun hmin => ?_⟩
  · refine CFSG.Quasithin.B7_2_1 hV hA hoT hHA hAll ha ?_ hI
    rw [CFSG.Quasithin.commV_eq_commSub]
    exact hz
  · exact CFSG.Quasithin.B7_2_2 hV hmin hoT hHA hAll

end CFSG.ASVolI
