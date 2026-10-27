module

public import CFSG.Quasithin.EmptyFaithful.S1565L2
public import CFSG.Quasithin.EmptyFaithful.S1565B
public import CFSG.Quasithin.EmptyFaithful.S1565H

public section

namespace CFSG.Quasithin.S1565

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Plumb

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
theorem normal_K₀_subgroupOf (hF : HypF918 T V L V₁ Vp H K) :
    ((conjClosure K T).subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hF.K₀_le_H).mpr hF.K₀_normal

omit [Finite G] in
theorem isPGroup_quotient_K₀ (hF : HypF918 T V L V₁ Vp H K) (hHK : H = K ⊔ T)
    [hN : ((conjClosure K T).subgroupOf H).Normal] :
    IsPGroup 2 (↥H ⧸ (conjClosure K T).subgroupOf H) := by
  have hsup : T ⊔ conjClosure K T = H := by
    refine le_antisymm (sup_le hF.T_le_H hF.K₀_le_H) ?_
    rw [hHK]
    exact sup_le (le_sup_of_le_right (le_conjClosure K T)) le_sup_left
  have hNT : T ≤ Subgroup.normalizer (conjClosure K T : Set G) := le_normalizer_conjClosure K T
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right T (conjClosure K T) hNT
  rw [hsup] at hcoe
  have hT2 : IsPGroup 2 ↥T := hF.sylow_H.2.1
  have hT2' : IsPGroup 2 ↥(T.subgroupOf H) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hF.T_le_H).symm
  refine hT2'.of_surjective ((QuotientGroup.mk' ((conjClosure K T).subgroupOf H)).comp
    (T.subgroupOf H).subtype) ?_
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hxH : (x : G) ∈ (T : Set G) * (conjClosure K T : Set G) := by
    rw [← hcoe]
    exact x.2
  obtain ⟨t, ht, k, hk, hxtk⟩ := hxH
  refine ⟨⟨⟨t, hF.T_le_H ht⟩, Subgroup.mem_subgroupOf.mpr ht⟩, ?_⟩
  show QuotientGroup.mk' ((conjClosure K T).subgroupOf H) ⟨t, hF.T_le_H ht⟩ =
    QuotientGroup.mk' ((conjClosure K T).subgroupOf H) x
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  refine Subgroup.mem_subgroupOf.mpr ?_
  have : ((⟨t, hF.T_le_H ht⟩ : ↥H)⁻¹ * x : ↥H) = ⟨k, hF.K₀_le_H hk⟩ := by
    apply Subtype.ext
    simp [← hxtk]
  rw [this]
  exact hk

theorem chiefFreeBelow15365_of_odd_element (hF : HypF918 T V L V₁ Vp H K) (hHK : H = K ⊔ T)
    [hFact : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)))] (M I : Subgroup G)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (t₀ : ↥H) (ht₀ : (t₀ : G) ∈ M) {m : ℕ}
    (hodd : Odd m)
    (hfm : ∀ w ∈ subM V₁ (conjClosure Vp H) (conjClosure I H),
      ((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) t₀) ^ m) w = w)
    (hgood : ∀ w ∈ subM V₁ (conjClosure Vp H) (conjClosure I H),
      actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) t₀ w * w⁻¹ ∈
        fixModSub (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
          ((conjClosure K T).subgroupOf H) ⊥ →
      w ∈ fixModSub (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
          ((conjClosure K T).subgroupOf H) ⊥) :
    ChiefFreeBelow15365 hF M I := by
  have hNnorm := normal_K₀_subgroupOf hF
  have hHU := le_normalizer_conjClosure Vp H
  set φ := actH hF.H_le_normalizer_V₁ hHU with hφ
  set N : Subgroup ↥H := (conjClosure K T).subgroupOf H with hNdef
  set J : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)) :=
    subM V₁ (conjClosure Vp H) (conjClosure I H) with hJdef
  have hW2 : ∀ w : ↥(tildeOf V₁ (conjClosure Vp H)), w ^ 2 = 1 := fun w => by
    apply Subtype.ext
    have := (Fact.out : IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))).2
      (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) w.2
    simpa using this
  have hIU' : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hJinv : InvSub φ J := by
    intro x w hw
    have hst := (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
      (hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)) hHU
      (hV₁I.trans (le_conjClosure I H)) hIU' x).mpr (le_normalizer_conjClosure I H x.2)
    exact (hst w).2 hw
  have hbot : InvSub φ (⊥ : Subgroup ↥(tildeOf V₁ (conjClosure Vp H))) := by
    intro x a ha
    rw [Subgroup.mem_bot] at ha ⊢
    rw [ha]
    exact map_one _
  have hFixInv : InvSub φ (fixModSub φ N ⊥) := invSub_fixModSub φ hNnorm hbot
  have hCinv : InvSub φ (J ⊓ fixModSub φ N ⊥) := ucf_invSub_inf hJinv hFixInv
  have hNC : ∀ n ∈ N, ∀ c ∈ J ⊓ fixModSub φ N ⊥, φ n c = c := by
    intro n hn c hc
    have := hc.2 n hn
    rw [Subgroup.mem_bot] at this
    exact mul_inv_eq_one.mp this
  have hB : t₀ ∈ (H ⊓ M).subgroupOf H := Subgroup.mem_subgroupOf.mpr ⟨t₀.2, ht₀⟩
  show ChiefFreeBelow φ ((H ⊓ M).subgroupOf H) J
  exact chiefFreeBelow_of_odd_element φ hW2 N (isPGroup_quotient_K₀ hF hHK) hCinv hNC
    ((H ⊓ M).subgroupOf H) hB hodd J hfm fun w hw hC => ⟨hw, hgood w hw hC.2⟩

end Plumb



end CFSG.Quasithin.S1565
