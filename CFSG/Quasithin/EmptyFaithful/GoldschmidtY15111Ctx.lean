module

public import CFSG.Quasithin.Background.C1PackS15212Six
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.SBc12Aut
public import CFSG.Quasithin.EmptyFaithful.SBc12Hyp
public import CFSG.Quasithin.EmptyFaithful.SBc12Qhat
public import CFSG.Quasithin.Vol2.Ch3nE2

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

structure Ctx15111 (T Mc M H : Subgroup G) : Prop where
  hyp28 : E2.Hyp28 H T (H ⊓ M) (V154 T Mc M)
  chartwo : CharTwo H
  q32 : qhatOf (autI hyp28.elem H) = (((3 : ℚ) / 2 : ℚ) : WithTop ℚ)
  res : twoResidual (H ⊓ M) ≤ Subgroup.centralizer (V154 T Mc M : Set G)
  v16 : Nat.card (V154 T Mc M) = 2 ^ 4
  om : IsOmegaFourPlusOn M (V154 T Mc M)
  normalizer_eq : Subgroup.normalizer (V154 T Mc M : Set G) = M

theorem ctx15111 (h158 : StageLemma1518) (h159 : StageLemma1519) (h215 : E215)
    {T Mc M H : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hCE : IsCE1513 T M) (hH : IsHStar T M H) (hV : ¬ V154 T Mc M ≤ pCoreOf 2 H) :
    Ctx15111 T Mc M H := by
  have hs : Setting152 T Mc M := ⟨hq, hM, hCE⟩
  have h19 : Lemma1519Concl T Mc M := h159 G T Mc M hq hM hCE
  have hhyp : HypE28 H T (H ⊓ M) (V154 T Mc M) := SBc12.hypE28_of_hstar hs h19 hH hV
  have hyp28 : E2.Hyp28 H T (H ⊓ M) (V154 T Mc M) := Ch3n.hyp28_of_hypE28 hhyp
  have hchar : CharTwo H := charTwo_of_inH' hq.qtke hq.sylow hH.1
  have hTI : IsTISetIn (V154 T Mc M) (H ⊓ M) := SBc12.isTISetIn_of_hstar hs hH
  have hel : IsElemAbelian 2 (V154 T Mc M) := hhyp.elemAbelian
  have hNV : Subgroup.normalizer (V154 T Mc M : Set G) = M := S152N.normalizer_V154_eq hs
  have hTM : T ≤ M := hs.mf.1.1.2
  have hTH : T ≤ H := hH.1.1
  have h215' : qhatInt H (V154 T Mc M) hel < ((2 : ℚ) : WithTop ℚ) :=
    h215 G H T (H ⊓ M) (V154 T Mc M) hhyp hchar hTI
  have hfour : oTwoUpper (H ⊓ M) ≤ Subgroup.centralizer (V154 T Mc M : Set G) := h19.four H hH
  have hHM : H ⊓ Subgroup.normalizer (V154 T Mc M : Set G) ≤ M := by
    rw [hNV]; exact inf_le_right
  have hAle : autI hel H ≤ autI hel M := SBc12.autI_le_of_inf_normalizer_le hel hHM
  have hAp : IsPGroup 2 ↥(autI hel H) := by
    refine SBc12.isPGroup_autI hel fun x hx => ?_
    have hxM : x ∈ M := by
      have := hx.2
      rwa [hNV] at this
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (H ⊓ M) (x := x) ⟨hx.1, hxM⟩
    exact ⟨k, hfour hk⟩
  rcases h158 G T Mc M hq hM hCE with ⟨hqa, -⟩ | ⟨hc3, hqb, -⟩
  · exfalso
    have h1 : qhatOf (autI hel M) ≤ qhatOf (autI hel H) := kq_le_kq_of_le216 hAle 3
    have h2 : qhatOf (autI hel M) = ((2 : ℚ) : WithTop ℚ) := by
      simp only [qhatOn, hel, ↓reduceDIte] at hqa
      exact hqa
    have h3 : qhatOf (autI hel H) < ((2 : ℚ) : WithTop ℚ) := h215'
    exact absurd (lt_of_le_of_lt (h2 ▸ h1) h3) (lt_irrefl _)
  · obtain ⟨hV16, -, hOm⟩ := hc3
    have hcardM : Nat.card ↥(autI hel M) = 36 := C1Pack12.card_autOn_of_isOmegaFourPlusOn hOm
    have hcardA : Nat.card ↥(autI hel H) ≤ 4 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hdvd : Nat.card ↥(autI hel H) ∣ 36 := hcardM ▸ Subgroup.card_dvd_of_le hAle
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hAp
      rw [hk] at hdvd ⊢
      by_contra hcon
      have hk3 : 3 ≤ k := by
        by_contra hk2
        have : k ≤ 2 := by omega
        have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
        omega
      have h8 : 8 ∣ 2 ^ k := by
        have : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 hk3
        simpa using this
      have : 8 ∣ 36 := h8.trans hdvd
      omega
    have hqm : qhatOf (autI hel M) = (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) := by
      simp only [qhatOn, hel, ↓reduceDIte] at hqb
      exact hqb
    have hq32 : qhatOf (autI hel H) = (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) :=
      SBc12.qhatOf_eq_three_halves hAle hcardA hqm h215'
    have hres : twoResidual (H ⊓ M) ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
      rw [F6.twoResidual_eq_oTwoUpper]
      exact hfour
    have hV16' : Nat.card (V154 T Mc M) = 2 ^ 4 := by rw [hV16]; norm_num
    exact ⟨hyp28, hchar, hq32, hres, hV16', hOm, hNV⟩

end Y15111

end CFSG.Quasithin
