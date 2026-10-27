module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem propN_mono {M V : Subgroup G} {P Q : Subgroup G → Prop} {n m : ℕ}
    (hPQ : ∀ Z : Subgroup G, P Z → Q Z) (hnm : n ≤ m) :
    propN P n M V ⊆ propN Q m M V := by
  rintro U ⟨hUV, t, ht, hk, W, hWV, hWn, hUW, hWt, hP⟩
  exact ⟨hUV, t, ht, hk, W, hWV, hWn.trans hnm, hUW, hWt, hPQ (commElt W t) hP⟩

private theorem propB_imp_propD {M Z : Subgroup G} (h : PropB M Z) : PropD M Z := by
  intro z hz hzC
  apply h
  refine (Subgroup.centralizer_le ?_).trans hzC
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact hz

theorem betaN_anti {M V : Subgroup G} {n m : ℕ} (hnm : n ≤ m) :
    betaN m M V ≤ betaN n M V := by
  unfold betaN
  refine le_iInf fun U => le_iInf fun hU => ?_
  exact (iInf_le (fun U => ⨅ (_ : U ∈ calBn m M V), (E3.mQuot V U : ℕ∞)) U).trans
    (iInf_le (fun _ : U ∈ calBn m M V => (E3.mQuot V U : ℕ∞))
      (propN_mono (P := PropB M) (Q := PropB M) (fun _ h => h) hnm (by simpa only [calBn] using hU)))

theorem gammaN_anti {M V : Subgroup G} {n m : ℕ} (hnm : n ≤ m) :
    gammaN m M V ≤ gammaN n M V := by
  unfold gammaN
  refine le_iInf fun U => le_iInf fun hU => ?_
  exact (iInf_le (fun U => ⨅ (_ : U ∈ calCn m M V), (E3.mQuot V U : ℕ∞)) U).trans
    (iInf_le (fun _ : U ∈ calCn m M V => (E3.mQuot V U : ℕ∞))
      (by simpa only [calCn] using
        propN_mono (P := PropC M) (Q := PropC M) (fun _ h => h) hnm (by simpa only [calCn] using hU)))

theorem deltaN_anti {M V : Subgroup G} {n m : ℕ} (hnm : n ≤ m) :
    deltaN m M V ≤ deltaN n M V := by
  unfold deltaN
  refine le_iInf fun U => le_iInf fun hU => ?_
  exact (iInf_le (fun U => ⨅ (_ : U ∈ calDn m M V), (E3.mQuot V U : ℕ∞)) U).trans
    (iInf_le (fun _ : U ∈ calDn m M V => (E3.mQuot V U : ℕ∞))
      (by simpa only [calDn] using
        propN_mono (P := PropD M) (Q := PropD M) (fun _ h => h) hnm (by simpa only [calDn] using hU)))

theorem deltaN_le_betaN {M V : Subgroup G} (n : ℕ) : deltaN n M V ≤ betaN n M V := by
  unfold deltaN betaN
  refine le_iInf fun U => le_iInf fun hU => ?_
  exact (iInf_le (fun U => ⨅ (_ : U ∈ calDn n M V), (E3.mQuot V U : ℕ∞)) U).trans
    (iInf_le (fun _ : U ∈ calDn n M V => (E3.mQuot V U : ℕ∞))
      (propN_mono (P := PropB M) (Q := PropD M) (fun Z h => propB_imp_propD h) le_rfl
        (by simpa only [calBn] using hU)))

private theorem mParam_autI_le_mQuot_of_mem_propN {V M : Subgroup G}
    (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (P : Subgroup G → Prop) (n : ℕ) {U : Subgroup G} (hU : U ∈ propN P n M V) :
    (E3.mParam (autI hV M) : ℕ∞) ≤ (E3.mQuot V U : ℕ∞) := by
  obtain ⟨hUV, t, ht, hk, W, hWV, hWn, hUW, hWt, _hP⟩ := hU
  obtain ⟨htM, htC⟩ := ht
  have hN : t ∈ Subgroup.normalizer (V : Set G) := hM htM
  have hφmem : convI hV ⟨t, hN⟩ ∈ autI hV (Subgroup.zpowers t) :=
    convI_mem_autI hV (Subgroup.mem_zpowers t) hN
  have hφ_ne : convI hV ⟨t, hN⟩ ≠ 1 := by
    intro h
    have htCV : t ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV ⟨t, hN⟩).1 h
    have hVle : V ≤ Subgroup.centralizer ({t} : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ((Subgroup.mem_centralizer_iff.1 htCV) v hv).symm
    exact hWt (hWV.trans hVle)
  obtain ⟨k, hk⟩ := hk
  have hKpg : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hKN : Subgroup.zpowers t ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.zpowers_le.2 htM).trans hM
  have hAp : IsPGroup 2 (autI hV (Subgroup.zpowers t)) := E3.isPGroup_autI hV hKN hKpg
  have hA1 : autI hV (Subgroup.zpowers t) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hφmem
    exact hφ_ne (Subgroup.mem_bot.1 hφmem)
  have hAle : autI hV (Subgroup.zpowers t) ≤ autI hV M :=
    autI_mono hV (Subgroup.zpowers_le.2 htM)
  have h1 : E3.mParam (autI hV M) ≤ rkIdx (fixV (autI hV (Subgroup.zpowers t))) :=
    E3.mParam_le_rkIdx_fixV hAle hAp hA1
  have h2 : rkIdx (fixV (autI hV (Subgroup.zpowers t))) =
      E3.mQuot V (V ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) :=
    E3.rkIdx_fixV_autI hV hKN
  have hUC : U ≤ Subgroup.centralizer (Subgroup.zpowers t : Set G) :=
    Subgroup.le_centralizer_iff.2 (Subgroup.zpowers_le.2 htC)
  have hUinf : U ≤ V ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G) := le_inf hUV hUC
  have h3 : E3.mQuot V (V ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) ≤ E3.mQuot V U :=
    E3.mQuot_mono hUinf
  exact ENat.natCast_le_natCast.2 (h1.trans (h2.trans_le h3))

private theorem mParam_autI_le_iInf_propN {V M : Subgroup G}
    (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (P : Subgroup G → Prop) (n : ℕ) :
    (E3.mParam (autI hV M) : ℕ∞) ≤ ⨅ U ∈ propN P n M V, (E3.mQuot V U : ℕ∞) :=
  le_iInf fun U => le_iInf fun hU => mParam_autI_le_mQuot_of_mem_propN hV hM P n hU

theorem mParam_autI_le_betaN {V M : Subgroup G}
    (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G)) (n : ℕ) :
    (E3.mParam (autI hV M) : ℕ∞) ≤ betaN n M V := by
  simpa only [betaN, calBn] using mParam_autI_le_iInf_propN hV hM (PropB M) n

private theorem autI_eq_autI_top_of_normalizer_eq {V M : Subgroup G}
    (hV : IsElemAbelian 2 V) (hM : Subgroup.normalizer (V : Set G) = M) :
    autI hV M = autI hV ⊤ := by
  rw [← hM]
  unfold autI
  rw [Subgroup.subgroupOf_self, Subgroup.top_subgroupOf]

theorem mParam_autI_top_le_betaN {V M : Subgroup G}
    (hV : IsElemAbelian 2 V) (hN : Subgroup.normalizer (V : Set G) = M) (n : ℕ) :
    (E3.mParam (autI hV ⊤) : ℕ∞) ≤ betaN n M V := by
  rw [← autI_eq_autI_top_of_normalizer_eq hV hN]
  exact mParam_autI_le_betaN hV (le_of_eq hN.symm) n

end CFSG.LocalAnalysis.WeakClosure81
