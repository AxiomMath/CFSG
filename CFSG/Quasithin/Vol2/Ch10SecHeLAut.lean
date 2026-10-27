module

public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Aut
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight

public section

namespace CFSG.Quasithin.Vol2.Ch10.HeL

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem he_not_comm :
    ¬ ∀ a b : NativeSporadic.Carrier .He, a * b = b * a := by
  intro h
  have : IsMulCommutative (NativeSporadic.Carrier .He) := ⟨⟨h⟩⟩
  have hs : IsSimpleGroup (NativeSporadic.Carrier .He) := CFSG.Sporadic.He.isSimpleGroup_He
  have hp := Group.is_simple_iff_prime_card.mp hs
  rw [show Nat.card (NativeSporadic.Carrier .He) = 4030387200 from CFSG.Sporadic.He.card_He]
    at hp
  norm_num at hp

theorem isSimpleGroup_O2Q {K : Subgroup G}
    (e : O2Q K ≃* NativeSporadic.Carrier .He) : IsSimpleGroup (O2Q K) :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e

theorem isQuasisimple_O2Q {K : Subgroup G}
    (e : O2Q K ≃* NativeSporadic.Carrier .He) : CFSG.IsQuasisimple (O2Q K) := by
  have hs := isSimpleGroup_O2Q e
  have hnc : ¬ ∀ a b : O2Q K, a * b = b * a := fun h => he_not_comm fun a b => by
    apply e.symm.injective
    rw [map_mul, map_mul, h]
  have hc : Subgroup.center (O2Q K) = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (O2Q K)) with h | h
    · exact h
    · exfalso
      apply hnc
      intro a b
      have hb : b ∈ Subgroup.center (O2Q K) := by
        rw [h]
        exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hb a
  set φ : O2Q K ⧸ Subgroup.center (O2Q K) ≃* O2Q K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot with hφ
  refine ⟨⟨?_⟩, @MulEquiv.isSimpleGroup _ _ _ _ hs φ, ?_⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator (O2Q K)) with h | h
    · exfalso
      apply hnc
      intro a b
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top a)) b
        (Subgroup.mem_top b)).symm
    · exact h
  · by_contra h
    simp only [not_exists, not_not] at h
    apply hnc
    intro a b
    have h1 := congrArg φ (h (φ.symm a) (φ.symm b))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1

theorem conjClosure_eq {K T : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    conjClosure K T = K :=
  le_antisymm (conjClosure_le fun _t ht z hz =>
    (Subgroup.mem_normalizer_iff.mp (hTK ht) z).mp hz) (le_conjClosure K T)

theorem isSubnormal_sup {K T : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    IsSubnormal K (K ⊔ T) :=
  IsSubnormal.step le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTK))
    (IsSubnormal.refl _)

theorem le_normalizer_conjClosure_K {K T W : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hKW : K ≤ Subgroup.normalizer (W : Set G)) :
    K ≤ Subgroup.normalizer (conjClosure W T : Set G) := by
  have key : ∀ a ∈ K, ∀ y ∈ conjClosure W T, a * y * a⁻¹ ∈ conjClosure W T := by
    intro a ha
    have hsup : conjClosure W T ≤ (conjClosure W T).comap (MulAut.conj a).toMonoidHom := by
      refine conjClosure_le fun x hx w hw => ?_
      show a * (x * w * x⁻¹) * a⁻¹ ∈ conjClosure W T
      have ha' : x⁻¹ * a * x ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (hTK (T.inv_mem hx)) a).mp ha
        simpa using this
      have h2 : (x⁻¹ * a * x) * w * (x⁻¹ * a * x)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hKW ha') w).mp hw
      have h3 := mem_conjClosure hx h2
      have e : x * ((x⁻¹ * a * x) * w * (x⁻¹ * a * x)⁻¹) * x⁻¹ = a * (x * w * x⁻¹) * a⁻¹ := by
        group
      rwa [e] at h3
    exact fun y hy => hsup hy
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => key a ha y hy, fun hy => by simpa [mul_assoc] using key a⁻¹ (inv_mem ha) _ hy⟩

theorem not_le_centralizer_of_isIrrPlusIn {X A Y I : Subgroup G} (hI : IsIrrPlusIn X A Y I) :
    ¬ X ≤ Subgroup.centralizer (I : Set G) := by
  intro hXC
  apply hI.2.2.2.2.1.ne
  refine le_antisymm inf_le_left (le_inf le_rfl fun v hv => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact ((Subgroup.mem_centralizer_iff.mp (hXC hx)) v hv).symm

variable [Finite G]

theorem conjClosure_le_reducedAggregate {K T W : Subgroup G}
    (hW : W ≤ reducedAggregate (K ⊔ T)) : conjClosure W T ≤ reducedAggregate (K ⊔ T) :=
  conjClosure_le fun _t ht w hw =>
    (Subgroup.mem_normalizer_iff.mp
      (Lem3228.le_normalizer_reducedAggregate' _ (le_sup_right (a := K) ht)) w).mp (hW hw)

theorem pCoreOf_le_centralizer {K T W : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hW : W ≤ reducedAggregate (K ⊔ T)) : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (A4.pCoreOf_le_of_subnormal 2 (isSubnormal_sup hTK)).trans
    ((reducedAggregate_props _).2.2.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hW)))

theorem card_autOn_eq {K T W : Subgroup G}
    (e : O2Q K ≃* NativeSporadic.Carrier .He) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) (hW : W ≤ reducedAggregate (K ⊔ T))
    (hne : ¬ K ≤ Subgroup.centralizer (W : Set G)) :
    Nat.card ↥(autOn K W) = 4030387200 := by
  obtain ⟨e'⟩ := nonempty_autOn_equiv_O2Q (isSimpleGroup_O2Q e) hKW
    (pCoreOf_le_centralizer hTK hW) hne
  rw [Nat.card_congr (e'.trans e).toEquiv]
  exact CFSG.Sporadic.He.card_He

omit [Finite G] in
theorem isFFModule_congr {W W' K K' : Subgroup G} (hW : W = W') (hK : K = K')
    [IsMulCommutative ↥W] [IsMulCommutative ↥W'] :
    IsFFModule (V := ↥W) (Subgroup.normalizer ((autOn K W : Set (MulAut ↥W)))) ↔
      IsFFModule (V := ↥W') (Subgroup.normalizer ((autOn K' W' : Set (MulAut ↥W')))) := by
  subst hW hK
  rfl

theorem isFFModule_of_isFFStarOffender {V : Type*} [CommGroup V] {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) : IsFFModule X :=
  CFSG.Quasithin.IsFFStarOffender.isFFModule hA

end CFSG.Quasithin.Vol2.Ch10.HeL
