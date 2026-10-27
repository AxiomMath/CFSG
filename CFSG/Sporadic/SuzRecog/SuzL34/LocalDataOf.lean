module

public import CFSG.Sporadic.SuzRecog.SuzL34.Bridge
public import CFSG.Sporadic.SuzRecog.SuzL34.LocalData
public import CFSG.Sporadic.SuzRecog.LocalRFusion

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34

open Subgroup CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzRecog.SuzL34Cert CFSG.Sporadic.SuzOddCore CFSG.Open
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.ABGLocalTools CFSG.LargeExtraspecial

section Certificates


private theorem fixedCard_eq_fiftyFour_or_fortyTwo (u : ↥(invE 1)) (hu : orderOf u = 2) :
    fixedCard ((u : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 54 ∨
      fixedCard ((u : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 42 := by
  obtain ⟨i, hi, hc⟩ := LocalR.exists_isConj_lambda u hu
  have hfix : fixedCard ((u : ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
      fixedCard ((LocalR.lambdaElt i : ↥(invE 1)) : Equiv.Perm (Fin 1782)) := by
    rw [fixedCard_eq_card_filter, fixedCard_eq_card_filter]
    obtain ⟨c, hc'⟩ := isConj_iff.mp hc
    rw [← hc']
    exact (LocalR.card_fixed_conj_coe (invE 1) u c).symm
  have hlam : fixedCard ((LocalR.lambdaElt i : ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
      LocalR.lambdaFixed[i]! := by
    rw [fixedCard_eq_card_filter]
    exact LocalR.card_fixed_lambda hi
  rw [hfix, hlam]
  interval_cases i <;> simp [LocalR.lambdaFixed]

theorem exists_localData {G : Type} [Group G] [Finite G]
    (S : CFSG.LargeExtraspecial.Setting G) (hw : S.width = 3)
    (hE : ¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16)
    (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) :
    Nonempty (LocalData G S.z) := by
  obtain ⟨σ⟩ := nonempty_mulEquiv_invE S hw hE hΩ hNWC
  refine ⟨LocalData.mk σ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · have h := LocalR.map_zM S σ
    have h2 : ((LocalR.t1Elt : ↥(invE 1)) : Equiv.Perm (Fin 1782)) =
        permC 1782 tTab := by
      change suzInv 1 = permC 1782 tTab
      rw [← permC_tTab]
    calc ((σ ⟨S.z, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(invE 1)) :
          Equiv.Perm (Fin 1782)) = ((σ S.zM : ↥(invE 1)) : Equiv.Perm (Fin 1782)) := rfl
      _ = ((LocalR.t1Elt : ↥(invE 1)) : Equiv.Perm (Fin 1782)) :=
        congrArg Subtype.val h
      _ = permC 1782 tTab := h2
  · intro t ht2 ht1
    have htord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
    have hσord : orderOf (σ t) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact htord
    have hnot : ¬ IsConj (t : G) S.z ↔ IsConj (σ t) LocalR.lambda4 :=
      LocalR.not_isConj_iff S hw hΩ hNWC σ t htord
    have hlam : IsConj (σ t) LocalR.lambda4 ↔
        (Finset.univ.filter fun x : Fin 1782 =>
          ((σ t : ↥(invE 1)) : Equiv.Perm (Fin 1782)) x = x).card = 42 :=
      LocalR.isConj_lambda4_iff (σ t) hσord
    have hnf : ¬ IsConj (t : G) S.z ↔
        fixedCard ((σ t : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 42 := by
      rw [hnot, hlam, fixedCard_eq_card_filter]
    have hclass := fixedCard_eq_fiftyFour_or_fortyTwo (σ t) hσord
    constructor
    · intro hconj
      by_contra hf54
      have hf42 : fixedCard ((σ t : ↥(invE 1)) : Equiv.Perm (Fin 1782)) = 42 := by
        rcases hclass with h | h
        · exact absurd h hf54
        · exact h
      exact (hnf.mpr hf42) hconj
    · intro hf54
      by_contra hnc
      have hf42 := hnf.mp hnc
      omega
  · intro t ht2 ht1
    have htord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
    have hσord : orderOf (σ t) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact htord
    have hnot : ¬ IsConj (t : G) S.z ↔ IsConj (σ t) LocalR.lambda4 :=
      LocalR.not_isConj_iff S hw hΩ hNWC σ t htord
    have hlam : IsConj (σ t) LocalR.lambda4 ↔
        (Finset.univ.filter fun x : Fin 1782 =>
          ((σ t : ↥(invE 1)) : Equiv.Perm (Fin 1782)) x = x).card = 42 :=
      LocalR.isConj_lambda4_iff (σ t) hσord
    rw [hnot, hlam, fixedCard_eq_card_filter]
  · intro t htM ht2 ht1 hnc
    have htord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
    exact (LocalR.nonCentralSylow S hw hΩ hNWC σ t htM htord hnc).1
  · intro t htM ht2 ht1 hnc
    have htord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
    exact (LocalR.nonCentralSylow S hw hΩ hNWC σ t htM htord hnc).2
  · intro t r ht2 ht1 hr2 hr1 hnt hnr
    have htord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
    have hrord : orderOf r = 2 := orderOf_eq_prime (by rwa [pow_two]) hr1
    have h1 : IsConj (σ t) LocalR.lambda4 :=
      (LocalR.not_isConj_iff S hw hΩ hNWC σ t htord).mp hnt
    have h2 : IsConj (σ r) LocalR.lambda4 :=
      (LocalR.not_isConj_iff S hw hΩ hNWC σ r hrord).mp hnr
    obtain ⟨c, hc⟩ := isConj_iff.mp (h1.trans h2.symm)
    refine isConj_iff.mpr ⟨σ.symm c, ?_⟩
    apply σ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc
  · exact card_invE (i := 1) (by norm_num)
  · intro d hd
    exact C1Model.decPerm_mem (d := d) hd
  · simpa [Model.w0, C1Model.w0T] using C1Model.w0_mem_invE
  · simpa [Model.w0, C1Model.w0T] using C1Model.w0_mul_self
  · simpa [Model.w0, C1Model.w0T] using C1Model.w0_ne_one
  · rw [tabSubgroup_v0Tabs]
    rfl
  · rw [tabSubgroup_t0Tabs, tabSubgroup_v0Tabs]
    exact C1Model.T0_le_V0
  · rw [tabSubgroup_c0Tabs, tabSubgroup_t0Tabs,
      tabSubgroup_v0Tabs, C1Model.C0, C1Model.CT0, C1Model.V0]
    ac_rfl
  · rw [tabSubgroup_ct0Tabs, tabSubgroup_t0Tabs]
    rfl
  · rw [tabSubgroup_t0Tabs]
    exact C1Model.card_T0

end Certificates

end CFSG.Sporadic.SuzRecog.SuzL34
