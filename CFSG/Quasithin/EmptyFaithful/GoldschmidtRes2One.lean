module

public import CFSG.Quasithin.EmptyFaithful.S152NBasic
public import CFSG.Quasithin.EmptyFaithful.SBc12Aut
public import CFSG.Quasithin.EmptyFaithful.S151b13Three
public import CFSG.Quasithin.Background.D216Sub
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2D11

public section

namespace CFSG.Quasithin.Gap6R2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T Mc M K N : Subgroup G}

theorem relIndex_le_of_card_autI_le {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTN : T ≤ Subgroup.normalizer (V : Set G)) {k : ℕ}
    (hk : ∀ E : Subgroup (MulAut (IntMod V hV)), E ≤ autI hV T → IsElemAbelian2 E →
      Nat.card E ≤ k) :
    ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ k := fun A hAT hAe =>
  (SBc12.relIndex_inf_centralizer_le_card_autI hV (K := A) le_rfl (hAT.trans hTN)).trans
    (hk _ (autI_mono hV hAT) (isElemAbelian2_autI hV hAe (hAT.trans hTN)))

theorem NonBorelK.not_le_kerIn (hK : NonBorelK T Mc M K N) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVK : ¬ V ≤ pCoreOf 2 K) : ¬ V ≤ kerIn N K := fun hle =>
  hVK (hK.minParabolic.le_pCoreOf_of_isPGroup_of_le_kerIn (B6.isPGroup_of_isElemAbelian hV) hle)

theorem NonBorelK.hyp28 (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M)
    (h15 : Lemma1515Concl T Mc M) (hK : NonBorelK T Mc M K N) (hVK : ¬ V154 T Mc M ≤ pCoreOf 2 K)
    (hL3 : V154 T Mc M ≤ pCoreOf 2 N) : E2.Hyp28 K T N (V154 T Mc M) := by
  have hsq : IsSQTKSub K := isSQTKSub_of_inH h.qtke h.simple h.nonabelian (hK.inH h)
  exact
    { minParabolic := hK.minParabolic
      sqtk := ⟨hsq.2, hsq.1⟩
      le_T := (V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ h hMf.1.1).2
      normal_T := hMf.1.1.2.trans (le_normalizer_V154 T Mc M)
      elem := h15.reduced.2.2.1
      le_pCoreOf := hL3
      not_le_kerIn := hK.not_le_kerIn h15.reduced.2.2.1 hVK }

theorem NonBorelK.outcome1_false_solvable (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M)
    (hCE : IsCE1513 T M) (h15 : Lemma1515Concl T Mc M) (hK : NonBorelK T Mc M K N)
    (hVK : ¬ V154 T Mc M ≤ pCoreOf 2 K) (hsolv : Group.IsSolvable K)
    (hq : qhatOn M (V154 T Mc M) = 2) : False := by
  have hs : Setting152 T Mc M := ⟨h, hMf, hCE⟩
  have hel : IsElemAbelian 2 (V154 T Mc M) := h15.reduced.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    hMf.1.1.2.trans (le_normalizer_V154 T Mc M)
  have hVT : V154 T Mc M ≤ T := (V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ h hMf.1.1).2
  have hchar : CharTwo K := charTwo_of_inH' h.qtke h.sylow (hK.inH h)
  have h1 := E2_15_of_isSolvable hel hK.minParabolic hsolv hchar hVT hTV
    (hK.not_le_kerIn hel hVK)
  have hKM : K ⊓ Subgroup.normalizer (V154 T Mc M : Set G) ≤ M := by
    rw [S152N.normalizer_V154_eq hs]
    exact inf_le_right
  have hAle : autI hel K ≤ autI hel M := SBc12.autI_le_of_inf_normalizer_le hel hKM
  have h2 : qhatOf (autI hel M) ≤ qhatOf (autI hel K) := kq_le_kq_of_le216 hAle 3
  have h3 : qhatOf (autI hel M) = ((2 : ℚ) : WithTop ℚ) := by
    rw [← qhatOn_eq_qhatOf151b hel, hq]
    norm_cast
  exact absurd (lt_of_le_of_lt (h3 ▸ h2) h1) (lt_irrefl _)

theorem NonBorelK.false_of_autOn_eq (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M)
    (h15 : Lemma1515Concl T Mc M) (hK : NonBorelK T Mc M K N)
    (hJT : autOn (thompsonJi T 1) (V154 T Mc M) = autOn T (V154 T Mc M)) : False := by
  have hel : IsElemAbelian 2 (V154 T Mc M) := h15.reduced.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    hMf.1.1.2.trans (le_normalizer_V154 T Mc M)
  have hVT : V154 T Mc M ≤ T := (V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ h hMf.1.1).2
  have hWZ : vE T Mc M ≤ quasithinOmegaOneCenter T := by
    intro w hw
    refine Subgroup.subset_closure ⟨⟨hVT hw.1, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩,
      hel.2 w hw.1⟩
    have hmem : conjAct (V154 T Mc M) ⟨t, hTV ht⟩ ∈ autOn T (V154 T Mc M) :=
      Subgroup.mem_map.mpr ⟨⟨t, hTV ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    rw [← hJT] at hmem
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmem
    have hyJ : (y : G) ∈ thompsonJi T 1 := Subgroup.mem_subgroupOf.mp hy
    have h1 := congrArg (fun φ => ((φ ⟨w, hw.1⟩ : V154 T Mc M) : G)) hye
    simp only [conjAct, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion] at h1
    have h2 : (y : G) * w = w * y := Subgroup.mem_centralizer_iff.mp hw.2 _ hyJ
    have h3 : (y : G) * w * (y : G)⁻¹ = w := by rw [h2]; group
    rw [h3] at h1
    calc t * w = (t * w * t⁻¹) * t := by group
      _ = w * t := by rw [← h1]
  exact hK.not_oTwoUpper_le ((oTwoUpper_le K).trans
    (hK.le_centralizer.trans (Subgroup.centralizer_le hWZ)))

end CFSG.Quasithin.Gap6R2
