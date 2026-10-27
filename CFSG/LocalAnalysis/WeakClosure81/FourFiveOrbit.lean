module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveComp
public import CFSG.Quasithin.EmptyFaithful.E111RComp
public import CFSG.Quasithin.EmptyFaithful.E22NParam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N Subgroup

variable {Q : Type} [Group Q] [Finite Q]

theorem fourFive_orbit_le {T N J X : Subgroup Q} (hN : FourFiveNMN N) (hJ : IsComponentOf J N)
    (hX : X = ⨆ t ∈ T, conjSub t J) : X ≤ N := by
  rw [hX]
  exact iSup₂_le fun t _ => (fourFive_nmn_component_conj hN hJ t).1

theorem fourFive_le_orbit {T J X : Subgroup Q} (hX : X = ⨆ t ∈ T, conjSub t J) : J ≤ X := by
  rw [hX]
  calc J = conjSub 1 J := (conjSub_one J).symm
    _ ≤ ⨆ t ∈ T, conjSub t J := le_iSup₂_of_le 1 T.one_mem le_rfl

theorem fourFive_le_normalizer_orbit {T J X : Subgroup Q} (hX : X = ⨆ t ∈ T, conjSub t J) :
    T ≤ Subgroup.normalizer (X : Set Q) := by
  intro s hs
  refine E111R.mem_normalizer_of_conjSub_le ?_ ?_
  · rw [hX, E111R.conjSub_iSup₂]
    refine iSup₂_le fun t ht => ?_
    rw [← conjSub_mul]
    exact le_iSup₂_of_le (s * t) (T.mul_mem hs ht) le_rfl
  · rw [hX, E111R.conjSub_iSup₂]
    refine iSup₂_le fun t ht => ?_
    rw [← conjSub_mul]
    exact le_iSup₂_of_le (s⁻¹ * t) (T.mul_mem (T.inv_mem hs) ht) le_rfl

private theorem fourFive_orbit_le_normalizer_conj {T N J X : Subgroup Q} (hN : FourFiveNMN N)
    (hJ : IsComponentOf J N) (hX : X = ⨆ t ∈ T, conjSub t J) (t : Q) :
    X ≤ Subgroup.normalizer (conjSub t J : Set Q) := by
  rw [hX]
  refine iSup₂_le fun s _ => ?_
  have hs : IsComponentOf (conjSub s J) N := fourFive_nmn_component_conj hN hJ s
  have ht : IsComponentOf (conjSub t J) N := fourFive_nmn_component_conj hN hJ t
  by_cases hEq : conjSub s J = conjSub t J
  · rw [hEq]
    exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (fourFive_nmn_components_commute hN hs ht hEq)).trans
      (Subgroup.centralizer_le_normalizer (conjSub t J : Set Q))

private theorem fourFive_conjSub_le_orbit {T J X : Subgroup Q}
    (hX : X = ⨆ t ∈ T, conjSub t J) {t : Q} (ht : t ∈ T) : conjSub t J ≤ X := by
  rw [hX]
  exact le_iSup₂_of_le (f := fun s (_ : s ∈ T) => conjSub s J) t ht le_rfl

theorem fourFive_orbit_isComp {T N J X : Subgroup Q} (hN : FourFiveNMN N)
    (hJ : IsComponentOf J N) (hX : X = ⨆ t ∈ T, conjSub t J) : E111R.IsComp X J := by
  obtain ⟨hsimple, hnonab⟩ := fourFive_nmn_component_simple hN hJ
  have hJX : J ≤ X := fourFive_le_orbit hX
  refine ⟨hJX, ?_, hsimple, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJX]
    have h := fourFive_orbit_le_normalizer_conj hN hJ hX 1
    rwa [conjSub_one] at h
  · by_contra h
    exact hnonab (IsMulCommutative.of_comm fun a b => by
      by_contra hab
      exact h ⟨a, b, hab⟩)

theorem fourFive_orbit_nonabelian {T N J X : Subgroup Q} (hN : FourFiveNMN N)
    (hJ : IsComponentOf J N) (hX : X = ⨆ t ∈ T, conjSub t J) : ¬ IsMulCommutative X := by
  obtain ⟨a, b, hab⟩ := (fourFive_orbit_isComp hN hJ hX).nonabelian
  intro h
  refine hab (Subtype.ext ?_)
  have hc := h.is_comm.comm (⟨a, fourFive_le_orbit hX a.2⟩ : ↥X)
    ⟨b, fourFive_le_orbit hX b.2⟩
  simpa using congrArg Subtype.val hc

theorem fourFive_orbit_inf_centralizer {T N J X : Subgroup Q} (hN : FourFiveNMN N)
    (hJ : IsComponentOf J N) (hX : X = ⨆ t ∈ T, conjSub t J) :
    X ⊓ Subgroup.centralizer (X : Set Q) = ⊥ := by
  haveI hNn : N.Normal := hN.normal
  have hNcent : N ⊓ Subgroup.centralizer (N : Set Q) = ⊥ := by
    have hnormal : (N ⊓ Subgroup.centralizer (N : Set Q)).Normal := inferInstance
    rcases hN.minimal _ hnormal inf_le_left with h | h
    · exact h
    · exfalso
      refine hN.nonabelian (IsMulCommutative.of_comm fun a b => ?_)
      have hcent : N ≤ Subgroup.centralizer (N : Set Q) := h.symm.le.trans inf_le_right
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent a.2) b b.2).symm
  rw [eq_bot_iff]
  intro z hz
  have hzX : z ∈ X := hz.1
  have hzcent : z ∈ Subgroup.centralizer (X : Set Q) := hz.2
  have hzN : z ∈ N := fourFive_orbit_le hN hJ hX hzX
  have hcomp : ∀ J' : Subgroup Q, IsComponentOf J' N →
      J' ≤ Subgroup.centralizer ({z} : Set Q) := by
    intro J' hJ'
    by_cases hmem : ∃ t ∈ T, conjSub t J = J'
    · obtain ⟨t, ht, rfl⟩ := hmem
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzcent y (fourFive_conjSub_le_orbit hX ht hy)
    · have hle : X ≤ Subgroup.centralizer (J' : Set Q) := by
        rw [hX]
        refine iSup₂_le fun t ht => ?_
        have ht' : IsComponentOf (conjSub t J) N := fourFive_nmn_component_conj hN hJ t
        have hne : conjSub t J ≠ J' := fun h => hmem ⟨t, ht, h⟩
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (fourFive_nmn_components_commute hN ht' hJ' hne)
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hle hzX) y hy
  have hNle : N ≤ Subgroup.centralizer ({z} : Set Q) :=
    (fourFive_nmn_components_sup hN).symm.le.trans (iSup₂_le hcomp)
  have hzNcent : z ∈ Subgroup.centralizer (N : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hNle hy) z rfl).symm
  have hzbot : z ∈ N ⊓ Subgroup.centralizer (N : Set Q) := ⟨hzN, hzNcent⟩
  rw [hNcent] at hzbot
  exact Subgroup.mem_bot.mp hzbot

theorem fourFive_orbit_minimal {T N J X U : Subgroup Q} (hN : FourFiveNMN N)
    (hJ : IsComponentOf J N) (hX : X = ⨆ t ∈ T, conjSub t J) (hU : U = X ⊔ T)
    {K : Subgroup Q} (hKX : K ≤ X) (hK : (K.subgroupOf U).Normal) : K = ⊥ ∨ K = X := by
  have hXU : X ≤ U := hU ▸ le_sup_left
  have hKU : K ≤ U := hKX.trans hXU
  have hUnorm : U ≤ Subgroup.normalizer (K : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKU).mp hK
  have hXnorm : X ≤ Subgroup.normalizer (K : Set Q) := hXU.trans hUnorm
  have hTnorm : T ≤ Subgroup.normalizer (K : Set Q) := (hU ▸ le_sup_right).trans hUnorm
  have hdisj : ∀ t ∈ T, K ⊓ conjSub t J = ⊥ ∨ K ⊓ conjSub t J = conjSub t J := by
    intro t ht
    have hcomp : IsComponentOf (conjSub t J) N := fourFive_nmn_component_conj hN hJ t
    have hsimple : IsSimpleGroup ↥(conjSub t J) :=
      (fourFive_nmn_component_simple hN hcomp).1
    have hnormK : conjSub t J ≤ Subgroup.normalizer (K : Set Q) :=
      (fourFive_conjSub_le_orbit hX ht).trans hXnorm
    have hKn : (K.subgroupOf (conjSub t J)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
      exact (le_inf hnormK Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    haveI := hsimple
    haveI := hKn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf (conjSub t J)) with h | h
    · left
      exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
    · right
      exact inf_eq_right.mpr (Subgroup.subgroupOf_eq_top.mp h)
  by_cases hbot : ∀ t ∈ T, K ⊓ conjSub t J = ⊥
  ·
    left
    have hKcent : K ≤ Subgroup.centralizer (X : Set Q) := by
      rw [Subgroup.le_centralizer_iff, hX]
      refine iSup₂_le fun t ht => ?_
      intro y hy k hk
      have hJtX : conjSub t J ≤ X := fourFive_conjSub_le_orbit hX ht
      have hyU : y ∈ U := hXU (hJtX hy)
      have hyK : y * k * y⁻¹ ∈ K :=
        (Subgroup.le_normalizer_iff.mp hUnorm) y hyU k hk
      have hkY : k * y * k⁻¹ ∈ conjSub t J :=
        (Subgroup.le_normalizer_iff.mp (fourFive_orbit_le_normalizer_conj hN hJ hX t)) k
          (hKX hk) y hy
      have hcommK : k * y * k⁻¹ * y⁻¹ ∈ K := by
        simpa [mul_assoc] using K.mul_mem hk (K.inv_mem hyK)
      have hcommJ : k * y * k⁻¹ * y⁻¹ ∈ conjSub t J :=
        (conjSub t J).mul_mem hkY ((conjSub t J).inv_mem hy)
      have h1 : k * y * k⁻¹ * y⁻¹ = 1 := by
        have hmem : k * y * k⁻¹ * y⁻¹ ∈ K ⊓ conjSub t J := ⟨hcommK, hcommJ⟩
        rw [hbot t ht] at hmem
        exact Subgroup.mem_bot.mp hmem
      calc k * y = (k * y * k⁻¹ * y⁻¹) * (y * k) := by group
        _ = y * k := by rw [h1, one_mul]
    have hle : K ≤ X ⊓ Subgroup.centralizer (X : Set Q) := le_inf hKX hKcent
    rw [fourFive_orbit_inf_centralizer hN hJ hX] at hle
    exact le_bot_iff.mp hle
  ·
    right
    obtain ⟨t₀, ht₀T, ht₀ne⟩ : ∃ t₀ ∈ T, K ⊓ conjSub t₀ J ≠ ⊥ := by
      by_contra hcon
      apply hbot
      intro t ht
      by_contra hne
      exact hcon ⟨t, ht, hne⟩
    have ht₀ : conjSub t₀ J ≤ K := by
      rcases hdisj t₀ ht₀T with h | h
      · exact absurd h ht₀ne
      · exact inf_eq_right.mp h
    refine le_antisymm hKX ?_
    rw [hX]
    refine iSup₂_le fun s hs => ?_
    have hst : s * t₀⁻¹ ∈ T := T.mul_mem hs (T.inv_mem ht₀T)
    have hconj : conjSub s J = conjSub (s * t₀⁻¹) (conjSub t₀ J) := by
      rw [← conjSub_mul]
      congr 1
      group
    rw [hconj]
    calc conjSub (s * t₀⁻¹) (conjSub t₀ J) ≤ conjSub (s * t₀⁻¹) K :=
          conjSub_mono _ ht₀
      _ = K := E111R.conjSub_eq_of_mem_normalizer (hTnorm hst)

end CFSG.LocalAnalysis.WeakClosure81
