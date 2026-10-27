module

public import CFSG.Quasithin.EmptyFaithful.S1565I
public import CFSG.Quasithin.EmptyFaithful.S1565F
public import CFSG.Quasithin.EmptyFaithful.S1565B

public section

namespace CFSG.Quasithin.S1565

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Module

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem sq_eq_one_tilde (hF : HypF918 T V L V₁ Vp H K) :
    ∀ w : ↥(tildeOf V₁ (conjClosure Vp H)), w ^ 2 = 1 := fun w => by
  have := factElem hF (le_conjClosure Vp H)
  apply Subtype.ext
  have := (Fact.out : IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))).2
    (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) w.2
  simpa using this

omit [Finite G] in
theorem odd_index_inf (hF : HypF918 T V L V₁ Vp H K) {M : Subgroup G} (hTM : T ≤ H ⊓ M) :
    Odd ((H ⊓ M).subgroupOf H).index := by
  have hdvd : ((H ⊓ M).subgroupOf H).index ∣ (T.subgroupOf H).index :=
    Subgroup.index_dvd_of_le (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hTM (Subgroup.mem_subgroupOf.mp hx)))
  by_contra h
  rw [Nat.not_odd_iff_even] at h
  exact hF.sylow_H.2.2 ((even_iff_two_dvd.mp h).trans hdvd)

theorem fixProp_J_top_of_layer (hF : HypF918 T V L V₁ Vp H K) (hHK : H = K ⊔ T) (M I : Subgroup G)
    (hTM : T ≤ H ⊓ M) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hI : IsIrrPlusTilde V₁ (conjClosure K T) I) (hnf : NoFixedLayer15365 hF M I) :
    haveI := factElem hF (le_conjClosure Vp H)
    FixProp (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
      ((H ⊓ M).subgroupOf H) (subM V₁ (conjClosure Vp H) (conjClosure I H)) ⊤ := by
  have hFact := factElem hF (le_conjClosure Vp H)
  have hHU := le_normalizer_conjClosure Vp H
  have hK₀n : ((conjClosure K T).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hF.K₀_le_H).mpr hF.K₀_normal
  have hdec : ∀ x : ↥H, ∃ t ∈ T.subgroupOf H, ∃ k ∈ (conjClosure K T).subgroupOf H, x = t * k := by
    intro x
    have hsup : T ⊔ conjClosure K T = H := by
      refine le_antisymm (sup_le hF.T_le_H hF.K₀_le_H) ?_
      rw [hHK]
      exact sup_le (le_sup_of_le_right (le_conjClosure K T)) le_sup_left
    have hN : T ≤ Subgroup.normalizer (conjClosure K T : Set G) := le_normalizer_conjClosure K T
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right T (conjClosure K T) hN
    rw [hsup] at hcoe
    have hxH : (x : G) ∈ (T : Set G) * (conjClosure K T : Set G) := by
      rw [← hcoe]
      exact x.2
    obtain ⟨t, ht, k, hk, hxtk⟩ := hxH
    refine ⟨⟨t, hF.T_le_H ht⟩, Subgroup.mem_subgroupOf.mpr ht, ⟨k, hF.K₀_le_H hk⟩,
      Subgroup.mem_subgroupOf.mpr hk, Subtype.ext hxtk.symm⟩
  have hJU : subM V₁ (conjClosure Vp H) (conjClosure I H) ≤
      subM V₁ (conjClosure Vp H) ⁅conjClosure Vp H, conjClosure K T⁆ := by
    have h1 := hF.tilde_commutator_conjClosure hIU hI
    have h2 : tildeOf V₁ (conjClosure I H) ≤ tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆ := by
      rw [← h1]
      exact secImg_mono (Subgroup.commutator_mono (conjClosure_le_conjClosure_U hIU le_rfl) le_rfl)
    intro w hw
    exact mem_subM_iff.2 (h2 (mem_subM_iff.1 hw))
  refine fixProp_of_noFixed_layer _ (sq_eq_one_tilde hF) _ _ _ hK₀n (odd_index_inf hF hTM)
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hTM (Subgroup.mem_subgroupOf.mp hx))) hdec
    (invSub_subM_conjClosure hF hV₁I hIU) (invSub_subM_commutator hF) hJU
    (fun k hk w => actH_comm_mem_commutator hF (Subgroup.mem_subgroupOf.mp hk) w) hnf

@[expose] def FixPropBotTop15365 (hF : HypF918 T V L V₁ Vp H K) (M : Subgroup G) : Prop :=
  haveI := factElem hF (le_conjClosure Vp H)
  FixProp (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
    ((H ⊓ M).subgroupOf H) (⊥ : Subgroup ↥(tildeOf V₁ (conjClosure Vp H))) ⊤

theorem false_of_fixProp_bot_top (hF : HypF918 T V L V₁ Vp H K) (M : Subgroup G)
    (hfp : FixPropBotTop15365 hF M)
    (hMZ : ∀ a ∈ Vp, ∀ b ∈ H ⊓ M, a * b * a⁻¹ * b⁻¹ ∈ V₁) : False := by
  have hFact := factElem hF (le_conjClosure Vp H)
  have htriv : ∀ x : ↥H,
      actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) x = 1 := by
    refine actH_trivial_of_fixed_gens hF fun a ha x => ?_
    have hBfix : ∀ s ∈ (H ⊓ M).subgroupOf H,
        actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) s
            (modMk (hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)) a
              (le_conjClosure Vp H ha)) *
          (modMk (hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)) a
            (le_conjClosure Vp H ha))⁻¹ ∈ (⊥ : Subgroup ↥(tildeOf V₁ (conjClosure Vp H))) := by
      intro s hs
      rw [actH_fix_of_comm hF ha (hMZ a ha s (Subgroup.mem_subgroupOf.mp hs)), mul_inv_cancel]
      exact Subgroup.one_mem _
    have := hfp _ trivial hBfix x trivial
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp this)
  have hKQ : K ≤ pCoreOf 2 H := fun k hk =>
    mem_pCoreOf_of_actH_eq_one hF (x := ⟨k, le_of_mem_cComp hF.K_cComp hk⟩) (htriv _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : IsPGroup 2 ↥K := (pCoreOf_isPGroup 2 H).to_le hKQ
  have : Group.IsNilpotent ↥K := hKp.isNilpotent
  exact not_isSolvable_of_mem_cComp hF.K_cComp inferInstance

theorem false_of_layer_inputs (hF : HypF918 T V L V₁ Vp H K) (hHK : H = K ⊔ T) (M I : Subgroup G)
    (hTM : T ≤ H ⊓ M) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hI : IsIrrPlusTilde V₁ (conjClosure K T) I) (hBelow : ChiefFreeBelow15365 hF M I)
    (hnf : NoFixedLayer15365 hF M I) (hMZ : ∀ a ∈ Vp, ∀ b ∈ H ⊓ M, a * b * a⁻¹ * b⁻¹ ∈ V₁) :
    False := by
  have hFact := factElem hF (le_conjClosure Vp H)
  refine false_of_fixProp_bot_top hF M ?_ hMZ
  show FixProp _ _ _ _
  have hJinv := invSub_subM_conjClosure hF hV₁I hIU
  have hbot : InvSub (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
      (⊥ : Subgroup ↥(tildeOf V₁ (conjClosure Vp H))) := by
    intro x a ha
    rw [Subgroup.mem_bot] at ha ⊢
    rw [ha]
    exact map_one _
  have h1 : FixProp (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
      ((H ⊓ M).subgroupOf H) ⊥ (subM V₁ (conjClosure Vp H) (conjClosure I H)) :=
    fixProp_of_interval _ (sq_eq_one_tilde hF) _ (odd_index_inf hF hTM) hJinv ⊥ hbot bot_le
      (fun A₁ A₂ _ hA₂ hp => hBelow A₁ A₂ hA₂ hp)
  have h2 := fixProp_J_top_of_layer hF hHK M I hTM hV₁I hIU hI hnf
  exact fixProp_compose _ (sq_eq_one_tilde hF) _ (odd_index_inf hF hTM) hbot bot_le h1 h2

end Module

end CFSG.Quasithin.S1565
