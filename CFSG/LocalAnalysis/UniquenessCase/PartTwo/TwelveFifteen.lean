module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFifteenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

namespace TwelveFifteen

theorem eq_or_eq_of_inCalV0 {M V₀ V V₁ V₂ : Subgroup G} (h0 : InCalV0 M V₀ V)
    (hV₁ : M ≤ normalizer (V₁ : Set G)) (hV₂ : M ≤ normalizer (V₂ : Set G))
    (hV : V = V₁ ⊔ V₂) : V = V₁ ∨ V = V₂ := by
  obtain ⟨-, -, hle, hTI₀, hnTI, hgen, -⟩ := h0
  have key : ∀ V' : Subgroup G, M ≤ normalizer (V' : Set G) → V' ≤ V → ¬ V' ≤ V₀ →
      V = V' := by
    intro V' hM' hV'V hnot
    obtain ⟨v, hv, hv0⟩ := SetLike.not_le_iff_exists.1 hnot
    have h1 := hgen v (hV'V hv) hv0
    refine le_antisymm ?_ hV'V
    rw [← h1, closure_le]
    rintro _ ⟨m, hm, rfl⟩
    exact (mem_normalizer_iff.1 (hM' hm) v).1 hv
  have h1V : V₁ ≤ V := by rw [hV]; exact le_sup_left
  have h2V : V₂ ≤ V := by rw [hV]; exact le_sup_right
  by_cases h1 : V₁ ≤ V₀
  · by_cases h2 : V₂ ≤ V₀
    · exfalso
      have hVV₀ : V = V₀ := le_antisymm (by rw [hV]; exact sup_le h1 h2) hle
      exact hnTI (by rw [hVV₀]; exact hTI₀)
    · exact Or.inr (key V₂ hV₂ h2V h2)
  · exact Or.inl (key V₁ hV₁ h1V h1)

theorem inCalW_of_le (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) {U V : Subgroup G}
    (hW : InCalW D.M D.T V) (hTI : ¬ IsTI V) (hUV : U ≤ V)
    (hMU : D.M ≤ normalizer (U : Set G))
    (hC : D.M ⊓ centralizer (U : Set G) ≤ centralizer (V : Set G)) : InCalW D.M D.T U := by
  obtain ⟨⟨hV, hV1⟩, h8, hred⟩ := hW
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have hpP : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpP⟩
  obtain ⟨P, hPM, hPel, hPV, hP2⟩ := uc22p22n_exists_good D hx h61 hV hTI hp
  have hPU : P ⊓ centralizer (U : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyP, hyU⟩
    have hy : y ∈ P ⊓ centralizer (V : Set G) := ⟨hyP, hC ⟨hPM hyP, hyU⟩⟩
    rwa [hPV] at hy
  have hp3 : 3 ≤ p := by
    have := hpP.two_le
    have := (D.sig_prime p hp).2
    omega
  have hP9 : 9 ≤ Nat.card P := le_trans (by nlinarith) hP2
  have hUel : IsElemAbelian 2 U := uc22p22n_isElemAbelian_of_le hUV hV.2.2.2
  have hU8 : 8 ≤ Nat.card U := by
    have h4 : ¬ Nat.card U ≤ 4 := fun h4 =>
      uc22p22nb_false_of_card_le_four (hPM.trans hMU) hPU h4 hP9
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hUel)
    rw [hk] at h4 ⊢
    by_contra h8'
    have hk3 : k < 3 := by
      by_contra hk3
      exact h8' (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hk3)))
    interval_cases k <;> simp_all
  have hUne : U ≠ ⊥ := by
    intro hU
    rw [hU] at hU8
    simp at hU8
  have hT : D.T ⊓ centralizer (U : Set G) = D.T ⊓ centralizer (V : Set G) := by
    apply le_antisymm
    · rintro t ⟨htT, htU⟩
      exact ⟨htT, hC ⟨D.sylowM.le htT, htU⟩⟩
    · exact inf_le_inf_left _ (centralizer_le hUV)
  refine ⟨⟨⟨hUne, hUV.trans hV.2.1, hMU, hUel⟩, ?_⟩, hU8, ?_⟩
  · rw [hT]
    exact hV1
  · intro K hKM hMK hCK hK2
    have hKV : (centralizer (U : Set G)).subgroupOf K = (centralizer (V : Set G)).subgroupOf K := by
      ext k
      simp only [mem_subgroupOf]
      exact ⟨fun h => hC ⟨hKM k.2, h⟩, fun h => centralizer_le hUV h⟩
    have hK : K ≤ centralizer (V : Set G) :=
      hred K hKM hMK (le_trans (inf_le_inf_left _ (centralizer_le hUV)) hCK) (hKV ▸ hK2)
    exact hK.trans (centralizer_le hUV)

theorem exists_isTI_sup_eq (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V V₁ V₂ : Subgroup G} (hWs : InCalWStar D.M D.T V) (hTI : ¬ IsTI V)
    (hV₁ : D.M ≤ normalizer (V₁ : Set G)) (hV₂ : D.M ≤ normalizer (V₂ : Set G))
    (hV : V = V₁ ⊔ V₂) (h1 : V ≠ V₁) (h2 : V ≠ V₂) :
    ∃ U₁ U₂ : Subgroup G, U₁ ≤ V₁ ∧ U₂ ≤ V₂ ∧ InCalV D.M U₁ ∧ InCalV D.M U₂ ∧ IsTI U₁ ∧
      IsTI U₂ ∧ V = U₁ ⊔ U₂ := by
  classical
  have hVW := hWs.1
  have hVc : InCalV D.M V := hVW.1.1
  have h1V : V₁ ≤ V := by rw [hV]; exact le_sup_left
  have h2V : V₂ ≤ V := by rw [hV]; exact le_sup_right
  let Adm : Subgroup G × Subgroup G → Prop := fun Q => Q.1 ≤ V₁ ∧ Q.2 ≤ V₂ ∧
    D.M ≤ normalizer (Q.1 : Set G) ∧ D.M ≤ normalizer (Q.2 : Set G) ∧
    D.M ⊓ centralizer ((Q.1 ⊔ Q.2 : Subgroup G) : Set G) ≤ centralizer (V : Set G)
  have hA0 : Adm (V₁, V₂) := ⟨le_rfl, le_rfl, hV₁, hV₂, by rw [← hV]; exact inf_le_right⟩
  have hex : ∃ n, ∃ Q, Adm Q ∧ Nat.card Q.1 + Nat.card Q.2 = n := ⟨_, _, hA0, rfl⟩
  obtain ⟨Q, hQ, hQn⟩ := Nat.find_spec hex
  have hmin : ∀ Q', Adm Q' → Nat.card Q.1 + Nat.card Q.2 ≤ Nat.card Q'.1 + Nat.card Q'.2 := by
    intro Q' hQ'
    rw [hQn]
    exact Nat.find_min' hex ⟨Q', hQ', rfl⟩
  obtain ⟨U₁, U₂⟩ := Q
  obtain ⟨hU₁, hU₂, hMU₁, hMU₂, hC⟩ := hQ
  simp only at hU₁ hU₂ hMU₁ hMU₂ hC hmin
  have hU₁V : U₁ ≤ V := hU₁.trans h1V
  have hU₂V : U₂ ≤ V := hU₂.trans h2V
  have hU₀W : InCalW D.M D.T (U₁ ⊔ U₂) :=
    TwelveFifteen.inCalW_of_le D hx h61 hVW hTI (sup_le hU₁V hU₂V)
      (TwelveFifteen.le_normalizer_sup hMU₁ hMU₂) hC
  have hVU : V = U₁ ⊔ U₂ := (hWs.2 _ hU₀W (sup_le hU₁V hU₂V)).symm
  have hel₁ : IsElemAbelian 2 U₁ := uc22p22n_isElemAbelian_of_le hU₁V hVc.2.2.2
  have hel₂ : IsElemAbelian 2 U₂ := uc22p22n_isElemAbelian_of_le hU₂V hVc.2.2.2
  have hred : TwoReduced D.M (U₁ ⊔ U₂) := hVU ▸ hVW.2.2
  have hred' : TwoReduced D.M (U₂ ⊔ U₁) := by rw [sup_comm]; exact hred
  have htr₁ : TwoReduced D.M U₁ := by
    refine TwelveFifteen.twoReduced_of_forall_eq (uc22p22e_isPGroup_of_elem hel₁) hMU₁ hMU₂
      hred fun U' hU' hMU' hCU' => ?_
    have hle := hmin (U', U₂) ⟨hU'.trans hU₁, hU₂, hMU', hMU₂, by rw [hVU]; exact hCU'⟩
    simp only at hle
    exact Subgroup.eq_of_le_of_card_ge hU' (by omega)
  have htr₂ : TwoReduced D.M U₂ := by
    refine TwelveFifteen.twoReduced_of_forall_eq (uc22p22e_isPGroup_of_elem hel₂) hMU₂ hMU₁
      hred' fun U' hU' hMU' hCU' => ?_
    have hle := hmin (U₁, U') ⟨hU₁, hU'.trans hU₂, hMU₁, hMU', by
      rw [hVU, sup_comm U₁ U₂, sup_comm U₁ U']; exact hCU'⟩
    simp only at hle
    exact Subgroup.eq_of_le_of_card_ge hU' (by omega)
  have hne₁ : U₁ ≠ ⊥ := by
    intro hb
    rw [hb, bot_sup_eq] at hVU
    exact h2 (le_antisymm (hVU ▸ hU₂) h2V)
  have hne₂ : U₂ ≠ ⊥ := by
    intro hb
    rw [hb, sup_bot_eq] at hVU
    exact h1 (le_antisymm (hVU ▸ hU₁) h1V)
  have hc₁ : InCalV D.M U₁ := ⟨hne₁, hU₁V.trans hVc.2.1, hMU₁, hel₁⟩
  have hc₂ : InCalV D.M U₂ := ⟨hne₂, hU₂V.trans hVc.2.1, hMU₂, hel₂⟩
  have hTI₁ : IsTI U₁ := by
    by_contra hn
    have hW₁ : InCalW D.M D.T U₁ := ⟨uc22p22n_inCalV1_of_not_isTI D hx h61 hc₁ hn,
      uc22p22n_eight_le_card D hx h61 hc₁ hn, htr₁⟩
    have he := hWs.2 U₁ hW₁ hU₁V
    exact h1 (le_antisymm (he ▸ hU₁) h1V)
  have hTI₂ : IsTI U₂ := by
    by_contra hn
    have hW₂ : InCalW D.M D.T U₂ := ⟨uc22p22n_inCalV1_of_not_isTI D hx h61 hc₂ hn,
      uc22p22n_eight_le_card D hx h61 hc₂ hn, htr₂⟩
    have he := hWs.2 U₂ hW₂ hU₂V
    exact h2 (le_antisymm (he ▸ hU₂) h2V)
  exact ⟨U₁, U₂, hU₁, hU₂, hc₁, hc₂, hTI₁, hTI₂, hVU⟩

end TwelveFifteen

theorem twelve_fifteen (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V V₁ V₂ : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₁ : InCalV D.M V₁) (hV₂ : InCalV D.M V₂) (hV : V = V₁ ⊔ V₂) : V = V₁ ∨ V = V₂ := by
  rcases h.1 with ⟨hWs, -⟩ | ⟨h0, -, -⟩
  · by_contra hne
    rw [not_or] at hne
    obtain ⟨hn1, hn2⟩ := hne
    have hTI : ¬ IsTI V := (twelve_nine D h127 h).1
    obtain ⟨U₁, U₂, hU₁, hU₂, hc₁, hc₂, hTI₁, hTI₂, hVU⟩ :=
      TwelveFifteen.exists_isTI_sup_eq D hx h61 hWs hTI hV₁.2.2.1 hV₂.2.2.1 hV hn1 hn2
    have h1V : V₁ ≤ V := by rw [hV]; exact le_sup_left
    have h2V : V₂ ≤ V := by rw [hV]; exact le_sup_right
    have hne1 : V ≠ U₁ := fun he => hn1 (le_antisymm (he ▸ hU₁) h1V)
    have hne2 : V ≠ U₂ := fun he => hn2 (le_antisymm (he ▸ hU₂) h2V)
    obtain ⟨H₀, hH, hH4⟩ := h.2
    obtain ⟨p, hp⟩ := hx.sig_nonempty
    have hVc : InCalV D.M V := h.inCalV
    have hrk : 1 < F12.pRankMod p D.M (centralizer (V : Set G)) := by
      rw [TwelveEight.pRankMod_centralizer_eq hVc.2.2.1]
      exact uc22p22n_one_lt_pRank_mbar D hx h61 hVc hTI p hp
    rcases h1214 ⟨H₀, TwelveEight.f12Hyp124_of_mem_hSet D hH hH4⟩ V U₁ U₂ U₁ hVc hc₁ hc₂ hc₁
      hVU hne1 hne2 hne1 p hp hrk with hn | hn
    · exact hn hTI₁
    · exact hn hTI₂
  · exact TwelveFifteen.eq_or_eq_of_inCalV0 h0 hV₁.2.2.1 hV₂.2.2.1 hV

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
