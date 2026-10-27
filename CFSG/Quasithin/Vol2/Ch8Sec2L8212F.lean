module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8210F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8212F

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem setup_82 (h3228 : Stmt3_2_2_eight) (h3109 : Stmt3_2_10_nine) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h711n : Stmt7_1_1_normal) (h822 : Stmt8_2_2)
    (h825 : Stmt8_2_5) (h828 : Stmt8_2_8) (h829 : Stmt8_2_9_12) (hsimp : HSimple82)
    (hcent : HCent82) (htype : HType82) (hpar : HParab82) (hcovL : KG82CoverL34)
    (hcovM : KG82CoverM22) (hm24 : SchurMult2M24) (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) :
    IsElemAbelian 2 (fsuV T I) ∧ T ≤ Subgroup.normalizer (L : Set G) ∧
      L ≤ Subgroup.normalizer (fsuV T I : Set G) ∧ T ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      fsuV T I ≤ T ∧ fsuV T I ≤ L ∧
      L ⊓ Subgroup.centralizer (fsuV T I : Set G) = fsuV T I ∧
      T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ fsuL0 T L = L ∧
      IsModel82 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ∧
      (∀ n : ℕ, Row711L3Nine T L I n → n = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [← hL0]
    exact le_sup_left.trans hN
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hVL : fsuV T I ≤ L := fsuV_le_of_82 hyp hTL hVT
  have hTCL := inf_centralizer_eq_bot_of_82 h3109 h37 h38 h39 hyp hV hN hTL
  obtain ⟨H, h, k, hH, hh, h22⟩ := exists_concl822_of_82 h822 hyp h731 h821 hrow
  obtain ⟨-, -, hn1, hTabL, hTabM, hTab24, hTab24c, -, -, -, -, -, -⟩ :=
    h825 G T L I hyp h731 h821 hc hrow H h k hH hh h22
  obtain ⟨-, -, hTVA⟩ := h829 G T L I hyp h731 h821 hc hrow H h k hH hh h22
  obtain ⟨-, -, -, -, -, hSyl, -, -, -, -, -, -, hA7, hAC, -, -, -, -, -⟩ := h22
  have hQV : pCoreOf 2 L = fsuV T I :=
    pCoreOf_eq_fsuV_of_82 hsimp hcent htype hpar hcovL hcovM hm24 h711n h822 h825 h828 h829 hyp
      h731 h821 hrow hV hN
  set V := fsuV T I with hVdef
  set A := ch82A V h with hAdef
  have hmod : IsModel82 (V := ↥V) (autOn L V) := isModel82_of_case82 hL0 hrow hn1
  have hAT : A ≤ T := fun x hx =>
    (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl hx.2).1
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := by
    rw [hA7]
    exact inf_le_right
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hAT.trans hTL
  have hAC' : A ⊓ Subgroup.centralizer (V : Set G) ≤ V := by
    rw [hAC]
    exact inf_le_left
  have hmA : mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) ≠ 0 := by
    rcases hrow with ⟨n, hn⟩ | h' | h' | h'
    · rw [(hTabL ⟨n, hn⟩).2.2.1]
      norm_num
    · rw [(hTabM h').2.2.1]
      norm_num
    · rw [(hTab24 h').2.2.1]
      norm_num
    · rw [(hTab24c h').2.2.1]
      norm_num
  have hAnC : ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hmA
    rw [inf_eq_left.mpr hle]
    unfold mQuot
    rw [Subgroup.relIndex_self, padicValNat_one_right]
  have hQC : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_82 hsimp hmod hLN
  have hQT : pCoreOf 2 L ≤ T := pCoreOf_le_T_of_82 hyp hTL
  have hTQ : T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hVC : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1
  have hQA : ⁅pCoreOf 2 L, A⁆ ≤ V :=
    commutator_pCoreOf_le_of_82 hQT hQC hTQ hAT hTVA hAN hVC hAC'
  have hLA : ⁅L, A⁆ = L := commutator_L_eq_of_82 hsimp hcent hyp hmod hLN hAN hAL hAnC hQC
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hQL : ⁅pCoreOf 2 L, L⁆ ≤ V :=
    commutator_Q_L_le_of_82 hLQ hLN (hAT.trans hTQ) hAN hQA hLA
  have hCQ : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L :=
    le_antisymm (inf_centralizer_le_pCoreOf_of_82 hyp.fsu.faithful.2.2.1 hV hLN hQL)
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hQC)
  exact ⟨hV, hTL, hLN, hTV, hVT, hVL, hCQ.trans hQV, hTCL, hL0, hmod, hn1⟩

theorem mem_of_le_of_normalizer_82 {V U : Subgroup G} {z : G} (hT : IsPGroup 2 ↥T)
    (hUV : U ≤ V) (hUT : U ≤ T) (hTU : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥)
    (hz : orderOf z = 2)
    (hzV : V ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) : z ∈ U := by
  have h1 := inf_center_ne_bot_of_82 hT hUT hTU hU
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
  obtain ⟨u, hu⟩ := w
  obtain ⟨huU, huTC⟩ := hu
  have huC : u ∈ Subgroup.centralizer (T : Set G) := huTC.2
  have hu1 : u ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hu : (u : G) ∈ Subgroup.zpowers z := by
    rw [← hzV]
    exact ⟨hUV huU, huC⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hk' : z ^ k = z ^ (k % 2) := by
    have := zpow_mod_orderOf z k
    rw [hz] at this
    exact_mod_cast this.symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · exfalso
    apply hu1
    rw [← hk, hk', h, zpow_zero]
  · have : (u : G) = z := by rw [← hk, hk', h, zpow_one]
    rw [← this]
    exact huU

end L8212F

end CFSG.Quasithin.H13
