module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
import CFSG.LocalAnalysis.WeakClosure81.EightSeven
import CFSG.Goldschmidt.Steps.Sec82Tools
import CFSG.LocalAnalysis.UniquenessCase.UC22P22p

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

namespace TwelveFourteen

theorem wClos_le_centralizer (D : Data G) {U₀ U₁ U₂ : Subgroup G} (hU₀ : InCalV D.M U₀)
    (hU₁ : InCalV D.M U₁) (hU₂ : InCalV D.M U₂) (hU : U₀ = U₁ ⊔ U₂) (hTI₁ : IsTI U₁)
    (hcard : Nat.card U₂ ≤ Nat.card U₁)
    (h2 : ∀ g : G, g ∉ D.M → conjSubgroup U₁ g ⊓ U₂ = ⊥) :
    E3.wClos U₁ 0 D.T ≤ centralizer (U₀ : Set G) := by
  rw [wClos_zero_eq_iSup hU₁.2.2.2]
  refine iSup₂_le fun g hgT => ?_
  have hAM : conjSubgroup U₁ g ≤ D.M := hgT.trans D.sylowM.le
  by_cases hg : g ∈ D.M
  · have hc : conjSubgroup U₁ g = U₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hU₁.2.2.1 (D.M.inv_mem hg))
    rw [hc]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxU₀ : x ∈ U₀ := hU ▸ (le_sup_left : U₁ ≤ U₁ ⊔ U₂) hx
    exact congrArg Subtype.val (hU₀.2.2.2.1.is_comm.comm ⟨y, hy⟩ ⟨x, hxU₀⟩)
  · have hA : IsElemAbelian 2 (conjSubgroup U₁ g) := E3.isElemAbelian_conjSubgroup hU₁.2.2.2 g
    have hATI : IsTI (conjSubgroup U₁ g) := isTI_conjSubgroup_quasithin hTI₁ g
    have hcardA : Nat.card (conjSubgroup U₁ g) = Nat.card U₁ := E3.card_conjSubgroup U₁ g
    have h1 : conjSubgroup U₁ g ≤ centralizer (U₁ : Set G) :=
      TwelveFourteen.le_centralizer_of_isTI hA hU₁.2.2.2 hATI (hAM.trans hU₁.2.2.1)
        (TwelveFourteen.conjSubgroup_inf_self_eq_bot D hU₁ hTI₁ hg) hcardA.ge
    have h2' : conjSubgroup U₁ g ≤ centralizer (U₂ : Set G) :=
      TwelveFourteen.le_centralizer_of_isTI hA hU₂.2.2.2 hATI (hAM.trans hU₂.2.2.1)
        (h2 g hg) (hcard.trans hcardA.ge)
    rw [hU, Subgroup.le_centralizer_iff, sup_le_iff]
    exact ⟨Subgroup.le_centralizer_iff.1 h1, Subgroup.le_centralizer_iff.1 h2'⟩

theorem normalizer_wClos_le (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {U₀ U₁ : Subgroup G} (hU₀ : InCalV D.M U₀) (hU₁ : InCalV D.M U₁)
    (hW : E3.wClos U₁ 0 D.T ≤ centralizer (U₀ : Set G))
    (hmp : 1 < F12.pRankMod p D.M (centralizer (U₀ : Set G))) :
    normalizer (E3.wClos U₁ 0 D.T : Set G) ≤ D.M ∧
      ∃ X : Subgroup G, X ≤ D.M ∧ IsPGroup p X ∧ ¬ IsCyclic X ∧
        X ≤ normalizer (E3.wClos U₁ 0 D.T : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpP : p.Prime := (D.sig_prime p hp).1
  have hKM : D.M ⊓ centralizer (U₀ : Set G) ≤ D.M := inf_le_left
  have hMK := uc22p22nc_le_normalizer_inf_centralizer hU₀.2.2.1
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ centralizer (U₀ : Set G))
      (D.M ⊓ centralizer (U₀ : Set G)) := by
    have h := D.sylowM.inf_of_le_normalizer hKM hMK
    rwa [← inf_assoc, inf_eq_left.2 D.sylowM.le] at h
  obtain ⟨X, hXM, hXp, hXc, hXS⟩ :=
    TwelveFourteen.exists_noncyclic_le_normalizer hpP hU₀.2.2.1 hS hmp
  have hWS : E3.wClos U₁ 0 D.T ≤ D.T ⊓ centralizer (U₀ : Set G) :=
    le_inf (wClos_zero_le U₁ D.T) hW
  have hNS : normalizer ((D.T ⊓ centralizer (U₀ : Set G) : Subgroup G) : Set G) ≤
      normalizer (E3.wClos U₁ 0 D.T : Set G) :=
    E3.e3_15_normalizer (TwelveShort.isSylowIn_of_le D D.sylowM.le)
      (inf_le_left.trans D.sylowM.le) (D.sylowM.isPGroup.to_le inf_le_left) hWS
  have hXW : X ≤ normalizer (E3.wClos U₁ 0 D.T : Set G) := hXS.trans hNS
  exact ⟨PartTwo.normalizer_le_of_noncyclic D h61 hp hXM hXp hXc
    (TwelveShort.wClos_zero_ne_bot D hU₁) (D.sylowM.isPGroup.to_le (wClos_zero_le U₁ D.T)) hXW,
    X, hXM, hXp, hXc, hXW⟩

theorem normalizersInM (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {U W X₀ : Subgroup G} (hU : InCalV D.M U) (hW : W ≠ ⊥) (hW2 : IsPGroup 2 W)
    (hNW : normalizer (W : Set G) ≤ D.M) (hX₀M : X₀ ≤ D.M) (hX₀p : IsPGroup p X₀)
    (hX₀c : ¬ IsCyclic X₀) (hX₀W : X₀ ≤ normalizer (W : Set G)) (H : Subgroup G) :
    NormalizersInM U H W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro X hX hXle hle
  have hNU : normalizer (U : Set G) = D.M := normalizer_eq_of_inCalV D hU
  have hNinf : normalizer (U : Set G) ⊓ normalizer (W : Set G) = normalizer (W : Set G) := by
    rw [hNU]
    exact inf_eq_right.2 hNW
  rw [hNinf] at hXle hle
  have hO : pCoreOf 2 X ≠ ⊥ :=
    TwelveFourteen.pCoreOf_ne_bot_of_normal D.standing.charTwo hW hW2 hX hXle hle
  have hNXO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  have hNO : normalizer (pCoreOf 2 X : Set G) ≤ D.M :=
    PartTwo.normalizer_le_of_noncyclic D h61 hp hX₀M hX₀p hX₀c hO
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) ((hX₀W.trans hle).trans hNXO)
  rw [hNU]
  exact inf_le_right.trans (hNXO.trans hNO)

theorem rk_le_k (D : Data G) (h126 : R126 D) (h861 : W3Lem86_1 G) {H₀ U : Subgroup G}
    (hH₀ : Hyp124Min D H₀) (hU : InCalV D.M U) (hU7 : Hyp7 U) (hW : E3.wClos U 0 D.T ≠ U)
    (hNW : normalizer (E3.wClos U 0 D.T : Set G) ≤ D.M)
    (hNorm : NormalizersInM U H₀ (E3.wClos U 0 D.T)) : rk ↥U ≤ D.k := by
  have hNU : normalizer (U : Set G) = D.M := normalizer_eq_of_inCalV D hU
  have hH := hH₀.1
  have hHE : E1.InE D.k H₀ := h126 H₀ hH₀
  have hTH : D.T ≤ H₀ ⊓ normalizer (U : Set G) := le_inf hH.1 (hNU ▸ D.sylowM.le)
  have hT : IsSylowIn 2 D.T (H₀ ⊓ normalizer (U : Set G)) := TwelveShort.isSylowIn_of_le D hTH
  have hUT : U ≤ D.T := uc22p22p_le_T_of_inCalV D hU
  have hcalH : IsCalH U H₀ := by
    refine ⟨hUT.trans hH.1, hH.2.2, ?_⟩
    have hS := TwelveShort.isSylowIn_of_le D hH.1
    have hmul := Subgroup.relIndex_mul_relIndex D.T (H₀ ⊓ normalizer (U : Set G)) H₀ hTH
      inf_le_left
    have hodd : ¬ 2 ∣ D.T.relIndex H₀ := hS.2.2
    rw [← hmul] at hodd
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h => hodd (Dvd.dvd.mul_left h _))
  have hnot : ¬ H₀ ≤ D.M := hH.2.1
  have hjoin : (H₀ ⊓ normalizer (U : Set G)) ⊔
      (H₀ ⊓ normalizer (E3.wClos U 0 D.T : Set G)) ≤ D.M :=
    sup_le (inf_le_right.trans hNU.le) (inf_le_right.trans hNW)
  by_cases h0 : IsCalH0 U H₀
  · by_contra hlt
    rw [not_le] at hlt
    have heq := eight_seven_of_isCalH0 (i := 0) hU7 h0 hT (by rw [Nat.add_zero]; exact hlt) hHE
    exact hnot (heq ▸ hjoin)
  · exfalso
    obtain ⟨heq, -⟩ := h861 U H₀ D.T hU7 hcalH h0 hT hW (Or.inr hNorm)
    exact hnot (heq ▸ hjoin)

theorem false_of_isTI (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h611 : UC6.R6_11Used D)
    (hsp : 3 ∈ D.sig1 → CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hsig2 : 3 ∉ D.sig2) (hne : ∃ V : Subgroup G, InCalV D.M V ∧ ¬ IsTI V)
    (h126 : R126 D) (h127 : R127 D) (h861 : W3Lem86_1 G)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h124 : ∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀)
    {U₀ U₁ U₂ : Subgroup G} (hU₀ : InCalV D.M U₀) (hU₁ : InCalV D.M U₁)
    (hU₂ : InCalV D.M U₂) (hU : U₀ = U₁ ⊔ U₂) {p : ℕ} (hp : p ∈ D.sig)
    (hmp : 1 < F12.pRankMod p D.M (centralizer (U₀ : Set G)))
    (hcard : Nat.card U₂ ≤ Nat.card U₁) (hTI₁ : IsTI U₁) (hTI₂ : IsTI U₂) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpP : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  obtain ⟨E, hEM, hEp, hEc, hEU₂⟩ :=
    TwelveFourteen.exists_noncyclic_le_centralizer D hx h61 h127 h124 hp hU₂ hTI₂
  have h2 : ∀ g : G, g ∉ D.M → conjSubgroup U₁ g ⊓ U₂ = ⊥ := fun g hg =>
    TwelveFourteen.conjSubgroup_inf_eq_bot D h61 hp hU₁ hTI₁ hEM hEp hEc hEU₂ hg
  have hWC := TwelveFourteen.wClos_le_centralizer D hU₀ hU₁ hU₂ hU hTI₁ hcard h2
  obtain ⟨hNW, X₀, hX₀M, hX₀p, hX₀c, hX₀W⟩ :=
    TwelveFourteen.normalizer_wClos_le D h61 hp hU₀ hU₁ hWC hmp
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hU₁.2.2.2)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hU₂.2.2.2)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hU₀.2.2.2)
  have hrka : rk ↥U₁ = a := by
    rw [rk, ha, padicValNat.prime_pow]
  have hk2 : D.k ≤ 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split_ifs <;> norm_num
  have hk1 := TwelveShort.one_le_k D
  have hrk : a ≤ D.k := by
    by_cases h4 : 2 < Nat.card U₁
    · obtain ⟨H₀, hH₀⟩ := exists_hyp124Min D h124
      have hW0 : E3.wClos U₁ 0 D.T ≠ ⊥ := TwelveShort.wClos_zero_ne_bot D hU₁
      have hW2 : IsPGroup 2 (E3.wClos U₁ 0 D.T) :=
        D.sylowM.isPGroup.to_le (wClos_zero_le U₁ D.T)
      have h4' : 4 ≤ Nat.card U₁ := by
        rw [ha] at h4 ⊢
        by_contra h5
        have h6 : a ≤ 1 := by
          by_contra h7
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 2 ≤ a by omega)
          omega
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h6
        omega
      rw [← hrka]
      exact TwelveFourteen.rk_le_k D h126 h861 hH₀ hU₁ ⟨hU₁.2.2.2, h4, hTI₁⟩
        (TwelveFourteen.wClos_zero_ne_self hTim hcat D hU₁ hTI₁ h4') hNW
        (TwelveFourteen.normalizersInM D h61 hp hU₁ hW0 hW2 hNW hX₀M hX₀p hX₀c hX₀W H₀)
    · rw [ha] at h4
      have h6 : a ≤ 1 := by
        by_contra h7
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 2 ≤ a by omega)
        omega
      omega
  have hU₀card : Nat.card U₀ ≤ Nat.card U₁ * Nat.card U₂ := by
    rw [hU]
    exact CFSG.Goldschmidt.Sec82.card_sup_le_mul_of_le_normalizer (hU₁.2.1.trans hU₂.2.2.1)
  have hba : b ≤ a := by
    rw [ha, hb] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  have hnab : n ≤ a + b := by
    rw [hn, ha, hb, ← pow_add] at hU₀card
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hU₀card
  have hdvd := TwelveFourteen.sq_dvd_card_mulAut hpP hU₀.2.2.1 hmp
  have hcomm : ∀ x y : ↥U₀, x * y = y * x := fun x y => hU₀.2.2.2.1.is_comm.comm x y
  have hpow : ∀ x : ↥U₀, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hU₀.2.2.2.2 x x.2)
  obtain ⟨h4n, h4⟩ := TwelveFourteen.four_le_and_eq_three hcomm hpow hn hpP hp2 hdvd
  obtain ⟨-, hp3⟩ := h4 (by omega)
  subst hp3
  have hkeq : D.k = 2 := by omega
  have hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    intro hs
    have : D.k = 1 := by
      unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
      rw [if_pos hs]
    omega
  have hp' := hp
  rw [D.sig_sub] at hp'
  rcases hp' with (h1 | h2') | h3
  · exact hns (hsp h1)
  · exact hsig2 h2'
  · obtain ⟨V, hV, hVTI⟩ := hne
    exact hVTI (TwelveFourteen.isTI_of_three_mem_sig3 D h61 h611 h3 hV)

end TwelveFourteen

theorem twelve_fourteen (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h611 : UC6.R6_11Used D)
    (hsp : 3 ∈ D.sig1 → CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hsig2 : 3 ∉ D.sig2) (hne : ∃ V : Subgroup G, InCalV D.M V ∧ ¬ IsTI V)
    (h126 : R126 D) (h127 : R127 D) (h861 : W3Lem86_1 G)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h124 : ∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀)
    {U₀ U₁ U₂ : Subgroup G} (hU₀ : InCalV D.M U₀) (hU₁ : InCalV D.M U₁)
    (hU₂ : InCalV D.M U₂) (hU : U₀ = U₁ ⊔ U₂) {p : ℕ} (hp : p ∈ D.sig)
    (hmp : 1 < F12.pRankMod p D.M (centralizer (U₀ : Set G))) :
    ¬ IsTI U₁ ∨ ¬ IsTI U₂ := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hTI₁, hTI₂⟩ := hcon
  rcases le_total (Nat.card U₂) (Nat.card U₁) with hc | hc
  · exact TwelveFourteen.false_of_isTI D hx h61 h611 hsp hsig2 hne h126 h127 h861 hTim hcat h124
      hU₀ hU₁ hU₂ hU hp hmp hc hTI₁ hTI₂
  · exact TwelveFourteen.false_of_isTI D hx h61 h611 hsp hsig2 hne h126 h127 h861 hTim hcat h124
      hU₀ hU₂ hU₁ (hU.trans (sup_comm _ _)) hp hmp hc hTI₂ hTI₁

theorem r1214_of_twelve_fourteen (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h611 : UC6.R6_11Used D)
    (hsp : 3 ∈ D.sig1 → CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hsig2 : 3 ∉ D.sig2) (hne : ∃ V : Subgroup G, InCalV D.M V ∧ ¬ IsTI V)
    (h126 : R126 D) (h127 : R127 D) (h861 : W3Lem86_1 G)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G) :
    F12.R1214 D := by
  rintro ⟨H₀, h⟩ U₀ U₁ U₂ _ hU₀ hU₁ hU₂ _ hU _ _ _ p hp hmp
  exact twelve_fourteen D hx h61 h611 hsp hsig2 hne h126 h127 h861 hTim hcat
    ⟨H₀, TwelveFourteen.mem_hSet_of_f12Hyp124 D h, TwelveFourteen.hyp124_of_f12Hyp124 D h⟩
    hU₀ hU₁ hU₂ hU hp hmp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
