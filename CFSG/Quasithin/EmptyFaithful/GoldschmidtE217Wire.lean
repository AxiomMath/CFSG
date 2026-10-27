module

public import CFSG.Quasithin.EmptyFaithful.S152He13C
public import CFSG.Quasithin.Background.C1PackS15212Six
public import CFSG.Quasithin.Background.E2SeventeenCore
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.S151b111
public import CFSG.Quasithin.EmptyFaithful.SBc12Aut
public import CFSG.Quasithin.EmptyFaithful.SBc12Hyp
public import CFSG.Quasithin.EmptyFaithful.SBc12Qhat
public import CFSG.Quasithin.Vol2.Ch3nE2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace E2

@[expose] def E217ConclOne {Γ : Type} [Group Γ] (H V : Subgroup Γ) : Prop :=
  ∃ D : Subgroup Γ, D ≤ conjClosure V H ∧ conjClosure V H ≤ Subgroup.normalizer (D : Set Γ) ∧
    IsExtraspecialPlus 2 D ∧
    ∃ φ : ↥(conjClosure V H) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
      φ.ker = D.subgroupOf (conjClosure V H)

@[expose] def E217NonsolvableNarrow : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : Hyp28 H T M V), CharTwo H →
    IsTISetIn V M → qhatOf (autI h.elem H) = (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) →
    twoResidual M ≤ Subgroup.centralizer (V : Set Γ) → Nat.card V = 2 ^ 4 →
    ¬ Group.IsSolvable H → (T ⊓ Subgroup.centralizer (V : Set Γ)).relIndex T < 8 →
      E217ConclOne H V

end E2

namespace E217Wire

open SBc12

variable {G : Type} [Group G] [Finite G] {T Mc M H : Subgroup G}

theorem stageLemma15111One_of_inputs_narrow (h158 : StageLemma1518) (h159 : StageLemma1519)
    (h215 : E215) (hE217 : E2.E217NonsolvableNarrow) (hY : Input15111Y) : StageLemma15111One := by
  intro G _ _ T Mc M hq hM hCE H hH
  by_contra hV
  have hs : Setting152 T Mc M := ⟨hq, hM, hCE⟩
  have h19 : Lemma1519Concl T Mc M := h159 G T Mc M hq hM hCE
  have hhyp : HypE28 H T (H ⊓ M) (V154 T Mc M) := hypE28_of_hstar hs h19 hH hV
  have hyp28 : E2.Hyp28 H T (H ⊓ M) (V154 T Mc M) := Ch3n.hyp28_of_hypE28 hhyp
  have hchar : CharTwo H := charTwo_of_inH' hq.qtke hq.sylow hH.1
  have hTI : IsTISetIn (V154 T Mc M) (H ⊓ M) := isTISetIn_of_hstar hs hH
  have hel : IsElemAbelian 2 (V154 T Mc M) := hhyp.elemAbelian
  have hNV : Subgroup.normalizer (V154 T Mc M : Set G) = M := S152N.normalizer_V154_eq hs
  have hTM : T ≤ M := hs.mf.1.1.2
  have hTH : T ≤ H := hH.1.1
  have h215' : qhatInt H (V154 T Mc M) hel < ((2 : ℚ) : WithTop ℚ) :=
    h215 G H T (H ⊓ M) (V154 T Mc M) hhyp hchar hTI
  have hfour : oTwoUpper (H ⊓ M) ≤ Subgroup.centralizer (V154 T Mc M : Set G) := h19.four H hH
  have hHM : H ⊓ Subgroup.normalizer (V154 T Mc M : Set G) ≤ M := by
    rw [hNV]; exact inf_le_right
  have hAle : autI hel H ≤ autI hel M := autI_le_of_inf_normalizer_le hel hHM
  have hAp : IsPGroup 2 ↥(autI hel H) := by
    refine isPGroup_autI hel fun x hx => ?_
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
      qhatOf_eq_three_halves hAle hcardA hqm h215'
    have hres : twoResidual (H ⊓ M) ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
      rw [F6.twoResidual_eq_oTwoUpper]
      exact hfour
    have hV16' : Nat.card (V154 T Mc M) = 2 ^ 4 := by rw [hV16]; norm_num
    have hTN : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := by rw [hNV]; exact hTM
    have hlt : (T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)).relIndex T < 8 := by
      have := relIndex_inf_centralizer_le_card_autI hel (K := H) hTH hTN
      omega
    by_cases hsolv : Group.IsSolvable H
    · rcases E2.e217Concl_of_isSolvable hyp28 hchar hq32 hres hV16' hsolv with h1 | ⟨-, h8⟩
      · exact hY G T Mc M hq hM hCE H hH hV h1
      · omega
    · exact hY G T Mc M hq hM hCE H hH hV
        (hE217 G H T (H ⊓ M) (V154 T Mc M) hyp28 hchar hTI hq32 hres hV16' hsolv hlt)

theorem stageLemma15111One_of_rigid_narrow (h15 : StageLemma1515CE) (h158 : StageLemma1518)
    (h159 : StageLemma1519) (h215 : E215) (hE217 : E2.E217NonsolvableNarrow)
    (hR : He13.Input15111YRigid) : StageLemma15111One :=
  stageLemma15111One_of_inputs_narrow h158 h159 h215 hE217 (He13.input15111Y_of_rigid h15 h159 hR)

end E217Wire

end CFSG.Quasithin
