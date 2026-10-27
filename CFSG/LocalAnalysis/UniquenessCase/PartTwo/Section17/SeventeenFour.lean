module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEleven
public import CFSG.LocalAnalysis.WeakClosure81.InFSqSymThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeFixedIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
public import CFSG.GroupTheory.TwoResidualOddOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def W3_6_18 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ {V M H S H₁ H₂ : Subgroup G} (hV : IsElemAbelian 2 V), V ≠ ⊥ →
    rankThreeIsMaxTwoLocal M → normalizer (V : Set G) = M →
    IsSylowIn 2 S H →
    Fstar H = pCoreOf 2 H →
    ∀ {k : ℕ}, 1 ≤ k → E1.InE k H →
    IsSylowIn 2 S H₁ → H₁ ≤ M → Fstar H₁ = pCoreOf 2 H₁ →
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ →
    IsSylowIn 2 S H₂ → H₂ ≤ M → Fstar H₂ = pCoreOf 2 H₂ →
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ →
    UniqueMax M (H₁ ⊔ H₂) → k + 2 < E3.sParam hV → E3.wClos V 0 S ≠ ⊥ → H ≤ M

private theorem uniqueMax_le {M X : Subgroup G} (h : UniqueMax M X) : X ≤ M := by
  have hM : M ∈ calMOf X := by rw [h]; simp
  exact hM.2

private theorem uniqueMax_sup_of_sup_eq_T {M L T L₁ L₂ : Subgroup G} (hU : UniqueMax M (L ⊔ T))
    (hsup : L ⊔ T = L₁ ⊔ L₂) : UniqueMax M (L₁ ⊔ L₂) :=
  hsup ▸ hU

private theorem le_of_sup_eq_of_uniqueMax {M L T L₁ L₂ : Subgroup G} (hU : UniqueMax M (L ⊔ T))
    (hsup : L ⊔ T = L₁ ⊔ L₂) : L₁ ≤ M ∧ L₂ ≤ M := by
  have hLM : L ⊔ T ≤ M := uniqueMax_le hU
  have h : L₁ ⊔ L₂ ≤ M := hsup ▸ hLM
  exact ⟨le_sup_left.trans h, le_sup_right.trans h⟩

private theorem isStronglyPEmbedded_of_k_eq_one (D : Data G) (hk : D.k = 1) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  by_contra hns
  have h2 : D.k = 2 := D.k_eq_two_iff.2 hns
  omega

theorem seventeen_four_v0eq1 (D : Data G) (h111 : W3Thm111 G) (h126 : R126 D)
    (h618 : W3_6_18 G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    {L L₁ L₂ : Subgroup G} (hTL : D.T ≤ Subgroup.normalizer (L : Set G))
    (hsup : L ⊔ (D.T ⊓ Subgroup.normalizer (L : Set G)) = L₁ ⊔ L₂)
    (hS1 : (D.T ⊓ Subgroup.normalizer (L : Set G)) ≤ L₁)
    (hS2 : (D.T ⊓ Subgroup.normalizer (L : Set G)) ≤ L₂)
    (hU : UniqueMax D.M (L ⊔ D.T))
    (hbar1 : Nonempty (Bar2 L₁ ≃* Equiv.Perm (Fin 3)))
    (hbar2 : Nonempty (Bar2 L₂ ≃* Equiv.Perm (Fin 3)))
    (hV0 : V₀ = ⊥) (hk : D.k = 1) : False := by
  have hST : (D.T ⊓ Subgroup.normalizer (L : Set G)) = D.T := inf_eq_left.mpr hTL
  have hsup' : L ⊔ D.T = L₁ ⊔ L₂ := by simpa [hST] using hsup
  have hT1 : D.T ≤ L₁ := by simpa [hST] using hS1
  have hT2 : D.T ≤ L₂ := by simpa [hST] using hS2
  have hcard : Nat.card V₀ ≤ 4 := by rw [hV0]; simp
  have hm3 : MBarGT D.M V₀ V 3 := h1669 hcard
  subst hV0
  have hV1 : InCalV1 D.M D.T V := by
    rcases hV.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
    · exact hW.1.1
    · exact absurd rfl h0.1.1
  have hm3' : MBarGT D.M ⊥ V 3 := hm3
  have hm2 : MBarGT D.M ⊥ V 2 := TwelveShort.mBarGT_mono hm3' (by norm_num)
  have hgt3 : 3 < E3.sParam hV.isElemAbelian :=
    TwelveShort.lt_sParam_of_mBarGT D h111 hV1 hm2 hm3'
  have hgt : D.k + 2 < E3.sParam hV.isElemAbelian := by rw [hk]; simpa using hgt3
  obtain ⟨H₀, hmin⟩ := hV.exists_hyp124Min
  have hE : E1.InE D.k H₀ := h126 H₀ hmin
  have hSyl : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hmin.1.1
  have hF0 : Fstar H₀ = pCoreOf 2 H₀ := TwelveEight.fstar_eq_pCoreOf_of_mem_hSet hmin.1
  have hU12 : UniqueMax D.M (L₁ ⊔ L₂) := uniqueMax_sup_of_sup_eq_T hU hsup'
  obtain ⟨hL1M, hL2M⟩ := le_of_sup_eq_of_uniqueMax hU hsup'
  have hF1 : Fstar L₁ = pCoreOf 2 L₁ := by
    rw [← sup_eq_left.mpr hT1]
    exact TwelveEleven.fstar_sup_eq_pCoreOf D hL1M
  have hF2 : Fstar L₂ = pCoreOf 2 L₂ := by
    rw [← sup_eq_left.mpr hT2]
    exact TwelveEleven.fstar_sup_eq_pCoreOf D hL2M
  exact hmin.1.2.1 (h618 hV.isElemAbelian hV1.1.1 D.maxLocal
    (normalizer_eq_of_inCalV D hV1.1) hSyl hF0 (TwelveShort.one_le_k D) hE
    (TwelveShort.isSylowIn_of_le D hT1) hL1M hF1
    (CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_bar2_perm_three L₁ hbar1)
    (TwelveShort.isSylowIn_of_le D hT2) hL2M hF2
    (CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_bar2_perm_three L₂ hbar2)
    hU12 hgt (TwelveShort.wClos_zero_ne_bot D hV1.1))

namespace SeventeenFour

private theorem card_bar2_eq_six {L : Subgroup G}
    (h : Nonempty (Bar2 L ≃* Equiv.Perm (Fin 3))) : Nat.card (Bar2 L) = 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num

private theorem card_sylow_two_eq_pcore {L T : Subgroup G} (hTL : T ≤ L) (hSyl : IsSylowIn 2 T L)
    (hcard : Nat.card L = Nat.card (pCoreOf 2 L) * 6) :
    Nat.card T = 2 * Nat.card (pCoreOf 2 L) := by
  have hOM : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hO2T : pCoreOf 2 L ≤ T :=
    IsSylowIn.le_of_normal hSyl hOM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOM).2
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hO2p : IsPGroup 2 (pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  obtain ⟨m, hm⟩ : ∃ m, Nat.card T = Nat.card (pCoreOf 2 L) * m :=
    Subgroup.card_dvd_of_le hO2T
  have hrel : T.relIndex L * Nat.card T = Nat.card L := by
    have h := CFSG.DisconnectedInvolutionGraph.Helpers.relIndex_mul_card_inf
      (subgroup := T) (ambient := L)
    rwa [inf_eq_left.mpr hTL] at h
  have hmul : m * T.relIndex L = 6 := by
    have h1 : Nat.card (pCoreOf 2 L) * (m * T.relIndex L) = Nat.card (pCoreOf 2 L) * 6 := by
      calc Nat.card (pCoreOf 2 L) * (m * T.relIndex L)
          = (Nat.card (pCoreOf 2 L) * m) * T.relIndex L := by ring
        _ = Nat.card T * T.relIndex L := by rw [hm]
        _ = Nat.card L := by rw [mul_comm]; exact hrel
        _ = Nat.card (pCoreOf 2 L) * 6 := hcard
    exact Nat.mul_left_cancel (Nat.card_pos) h1
  have hrelOdd : Odd (T.relIndex L) :=
    Nat.not_even_iff_odd.mp fun he => hSyl.not_dvd_relIndex (even_iff_two_dvd.mp he)
  have hm_dvd : m ∣ 6 := ⟨T.relIndex L, hmul.symm⟩
  obtain ⟨n, hn⟩ := hSyl.isPGroup.exists_card_eq
  obtain ⟨j, hj⟩ := hO2p.exists_card_eq
  have hpow : m = 2 ^ (n - j) := by
    have h1 : 2 ^ j * m = 2 ^ n := by rw [← hj, ← hn, hm]
    have hjn : j ≤ n := by
      by_contra h
      have hlt : n < j := by omega
      have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
      have hlt' : 2 ^ n < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) hlt
      have hdvd : 2 ^ j ∣ 2 ^ n := h1 ▸ ⟨m, rfl⟩
      have hle := Nat.le_of_dvd hpos hdvd
      omega
    calc m = 2 ^ j * m / 2 ^ j := (Nat.mul_div_cancel_left _ (pow_pos (by norm_num) j)).symm
      _ = 2 ^ n / 2 ^ j := by rw [h1]
      _ = 2 ^ (n - j) := by rw [Nat.pow_div hjn (by norm_num)]
  have hm_ne_one : m ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hmul
    have heven : Even (T.relIndex L) := ⟨3, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hrelOdd) heven
  have hcop3 : Nat.Coprime m 3 := by
    rw [hpow]
    exact (by norm_num : Nat.Coprime 2 3).pow_left (n - j)
  have hm2 : m ∣ 2 := by
    have h6 : m ∣ 2 * 3 := by simpa using hm_dvd
    exact hcop3.dvd_of_dvd_mul_right h6
  have hm_eq : m = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hm2 with h1 | h1
    · exact absurd h1 hm_ne_one
    · exact h1
  rw [hm, hm_eq]
  ring

private theorem exists_order_three_subgroup {K T : Subgroup G} (hTK : T ≤ K)
    (hSyl : IsSylowIn 2 T K) (hcardK : Nat.card K = Nat.card (pCoreOf 2 K) * 6) :
    ∃ X : Subgroup G, X ≤ K ∧ Nat.card X = 3 ∧ IsPGroup 3 X ∧
      (X : Set G) * (T : Set G) = (K : Set G) ∧
      (T : Set G) * (X : Set G) = (K : Set G) ∧ X ⊔ T = K := by
  have hcardT : Nat.card T = 2 * Nat.card (pCoreOf 2 K) :=
    card_sylow_two_eq_pcore hTK hSyl hcardK
  have hTL : Nat.card K = 3 * Nat.card T := by rw [hcardT, hcardK]; ring
  have hdvd3 : 3 ∣ Nat.card K := ⟨Nat.card T, hTL⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 hdvd3
  let X : Subgroup G := Subgroup.zpowers (x : G)
  have hxK : (x : G) ∈ K := x.2
  have hxord : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hXle : X ≤ K := by
    rw [Subgroup.zpowers_le]
    exact hxK
  have hXcard : Nat.card X = 3 := by rw [Nat.card_zpowers, hxord]
  have hXp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [hXcard]; norm_num)
  have hXinfT : X ⊓ T = ⊥ := by
    obtain ⟨n, hn⟩ := hSyl.isPGroup.exists_card_eq
    have hcop : Nat.Coprime (Nat.card X) (Nat.card T) := by
      rw [hXcard, hn]
      exact (by norm_num : Nat.Coprime 3 2).pow_right n
    have h := Subgroup.disjoint_of_coprime_natCard hcop
    rwa [disjoint_iff_inf_le, le_bot_iff] at h
  have hcardXT : Nat.card ↥((X : Set G) * (T : Set G)) = Nat.card K := by
    have h1 := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf X T
    have h2 : Nat.card ↥(X ⊓ T) = 1 := by rw [hXinfT, Subgroup.card_bot]
    rw [h2, mul_one] at h1
    rw [h1, hXcard]
    omega
  have hsub1 : (X : Set G) * (T : Set G) ⊆ (K : Set G) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact K.mul_mem (hXle ha) (hTK hb)
  haveI : Fintype ↥((X : Set G) * (T : Set G)) := Fintype.ofFinite _
  haveI : Fintype ↥(K : Set G) := Fintype.ofFinite _
  have hXT : (X : Set G) * (T : Set G) = (K : Set G) :=
    Set.eq_of_subset_of_card_le hsub1
      (le_of_eq (by simpa [Nat.card_eq_fintype_card] using hcardXT.symm))
  have hsub2 : (T : Set G) * (X : Set G) ⊆ (K : Set G) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact K.mul_mem (hTK ha) (hXle hb)
  have hcardTX : Nat.card ↥((T : Set G) * (X : Set G)) = Nat.card K := by
    have h1 := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf T X
    have h2 : Nat.card ↥(T ⊓ X) = 1 := by rw [inf_comm, hXinfT, Subgroup.card_bot]
    rw [h2, mul_one] at h1
    rw [h1, hXcard]
    omega
  haveI : Fintype ↥((T : Set G) * (X : Set G)) := Fintype.ofFinite _
  have hTX : (T : Set G) * (X : Set G) = (K : Set G) :=
    Set.eq_of_subset_of_card_le hsub2
      (le_of_eq (by simpa [Nat.card_eq_fintype_card] using hcardTX.symm))
  refine ⟨X, hXle, hXcard, hXp, hXT, hTX, ?_⟩
  refine le_antisymm (sup_le hXle hTK) ?_
  intro k hk
  have hk' : k ∈ (X : Set G) * (T : Set G) := by rwa [hXT]
  obtain ⟨a, ha, b, hb, rfl⟩ := hk'
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

private theorem not_twoResidual_le_conj_of_three (D : Data G)
    (hSPE : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) {H X : Subgroup G}
    (hXres : X ≤ twoResidual H) (hXM : X ≤ D.M) (hXp : IsPGroup 3 X) (hXne : X ≠ ⊥)
    {g : G} (hg : g ∉ D.M) : ¬ twoResidual H ≤ conjSubgroup D.M g := by
  intro hle
  have hleX : X ≤ conjSubgroup D.M g := hXres.trans hle
  have hbot : X ⊓ conjSubgroup D.M g = ⊥ := by
    simpa [CFSG.Quasithin.conjSubgroup] using
      hSPE.inf_map_conj_eq_bot (by norm_num : Nat.Prime 3) hXM hXp g⁻¹
        (fun h => hg (by simpa using D.M.inv_mem h))
  have hle_inf : X ≤ X ⊓ conjSubgroup D.M g := le_inf le_rfl hleX
  rw [hbot] at hle_inf
  exact hXne (le_bot_iff.mp hle_inf)

private theorem fixV_conjClosure_eq_bot_of_ne_bot (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) {L : Subgroup G} (hLM : L ≤ D.M)
    (hH : barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥) :
    fixV (barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ := by
  have hYM : barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L) ≤
      Mbar D.M V₀ V h.isElemAbelian :=
    barSub_mono V₀ V h.isElemAbelian (TwelveTwentyThree.conjClosure_le hLM)
  refine s15_Kbar_fixV_eq_bot_of_ne_bot h hV₀ hYM ?_ hH
  rw [Subgroup.normal_subgroupOf_iff hYM]
  intro y m hy hm
  exact TwelveEighteen.conj_mem_barSub h.isElemAbelian
    (TwelveTwentyThree.le_normalizer_conjClosure D.M L) m hm y hy

end SeventeenFour

theorem seventeen_four_gt2 (D : Data G) (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (h8 : 8 ≤ Nat.card V₀)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) (h86 : W3Lem86_1 G) (h126 : R126 D)
    {L L₁ L₂ : Subgroup G} (hTL : D.T ≤ Subgroup.normalizer (L : Set G))
    (hsup : L ⊔ (D.T ⊓ Subgroup.normalizer (L : Set G)) = L₁ ⊔ L₂)
    (hS1 : (D.T ⊓ Subgroup.normalizer (L : Set G)) ≤ L₁)
    (hS2 : (D.T ⊓ Subgroup.normalizer (L : Set G)) ≤ L₂)
    (hbar1 : Nonempty (Bar2 L₁ ≃* Equiv.Perm (Fin 3)))
    (hbar2 : Nonempty (Bar2 L₂ ≃* Equiv.Perm (Fin 3)))
    (hU : UniqueMax D.M (L ⊔ D.T)) (hk : D.k = 1) : False := by
  have hST : (D.T ⊓ Subgroup.normalizer (L : Set G)) = D.T := inf_eq_left.mpr hTL
  have hsup' : L ⊔ D.T = L₁ ⊔ L₂ := by simpa [hST] using hsup
  have hT1 : D.T ≤ L₁ := by simpa [hST] using hS1
  have hT2 : D.T ≤ L₂ := by simpa [hST] using hS2
  obtain ⟨hL1M, hL2M⟩ := le_of_sup_eq_of_uniqueMax hU hsup'
  have hSPE : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    isStronglyPEmbedded_of_k_eq_one D hk
  have hV0ne : V₀ ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at h8
    omega
  obtain ⟨hInv, hTI⟩ : InCalV D.M V₀ ∧ CFSG.CGT.Timmesfeld75.IsTI V₀ := by
    rcases hV.1 with ⟨-, h0⟩ | ⟨h0, -, -⟩
    · exact absurd h0 hV0ne
    · exact ⟨h0.1, h0.2.2.2.1⟩
  have hcardBar1 : Nat.card (Bar2 L₁) = 6 := SeventeenFour.card_bar2_eq_six hbar1
  have hcardBar2 : Nat.card (Bar2 L₂) = 6 := SeventeenFour.card_bar2_eq_six hbar2
  have hcardL1 : Nat.card L₁ = Nat.card (pCoreOf 2 L₁) * 6 := by
    rw [card_eq_card_pCoreOf_mul_card_bar2, hcardBar1]
  have hcardL2 : Nat.card L₂ = Nat.card (pCoreOf 2 L₂) * 6 := by
    rw [card_eq_card_pCoreOf_mul_card_bar2, hcardBar2]
  have hSyl1 : IsSylowIn 2 D.T L₁ := TwelveShort.isSylowIn_of_le D hT1
  have hSyl2 : IsSylowIn 2 D.T L₂ := TwelveShort.isSylowIn_of_le D hT2
  obtain ⟨X₁, hX1le, hX1card, hX1p, hX1T, hTX1, hsup1⟩ :=
    SeventeenFour.exists_order_three_subgroup hT1 hSyl1 hcardL1
  obtain ⟨X₂, hX2le, hX2card, hX2p, hX2T, hTX2, hsup2⟩ :=
    SeventeenFour.exists_order_three_subgroup hT2 hSyl2 hcardL2
  have hX1M : X₁ ≤ D.M := hX1le.trans hL1M
  have hX2M : X₂ ≤ D.M := hX2le.trans hL2M
  have hInt : ∀ (X : Subgroup G), X ≤ D.M → IsPGroup 3 X → Nat.card X = 3 →
      ∀ g : G, g ∉ D.M → V₀ ≤ conjSubgroup D.M g → X ⊓ conjSubgroup D.M g = ⊥ :=
    fun X hXM hXp _ g hg _ => by
      simpa [CFSG.Quasithin.conjSubgroup] using
        hSPE.inf_map_conj_eq_bot (by norm_num : Nat.Prime 3) hXM hXp g⁻¹
          (fun h => hg (by simpa using D.M.inv_mem h))
  have hΓ : ∀ (X : Subgroup G), X ≤ D.M → IsPGroup 3 X →
      CFSG.Open.rankThreeGamma 1 3 X ≤ D.M :=
    fun X hXM hXp =>
      hSPE.rankThreeGamma_one_le_of_le (by norm_num : Nat.Prime 3) hXp hXM
  have hw1 : X₁ ⊔ D.T ≤ Subgroup.normalizer (E3.wClos V₀ 0 D.T : Set G) :=
    (twelve_sixteen hTim hcat D h66 h88 hV h8 h93 (p := 3) (by norm_num) (by norm_num)
      hX1p (hInt X₁ hX1M hX1p hX1card) (hΓ X₁ hX1M hX1p) (by rw [hX1T, hTX1])).2
  have hw2 : X₂ ⊔ D.T ≤ Subgroup.normalizer (E3.wClos V₀ 0 D.T : Set G) :=
    (twelve_sixteen hTim hcat D h66 h88 hV h8 h93 (p := 3) (by norm_num) (by norm_num)
      hX2p (hInt X₂ hX2M hX2p hX2card) (hΓ X₂ hX2M hX2p) (by rw [hX2T, hTX2])).2
  have hN1 : L₁ ≤ Subgroup.normalizer (E3.wClos V₀ 0 D.T : Set G) := by
    rw [← hsup1]; exact hw1
  have hN2 : L₂ ≤ Subgroup.normalizer (E3.wClos V₀ 0 D.T : Set G) := by
    rw [← hsup2]; exact hw2
  have hN : L ⊔ D.T ≤ Subgroup.normalizer (E3.wClos V₀ 0 D.T : Set G) := by
    rw [hsup']
    exact sup_le hN1 hN2
  have hUniq : UniqueMax D.M
      (D.M ⊓ Subgroup.normalizer (E3.wClos V₀ 0 D.T : Set G)) :=
    UC22.uc22p22u_uniqueMax_mono D (le_inf (uniqueMax_le hU) hN) inf_le_left hU
  exact twelve_seven_one hTim hcat D h86 h126 hV.2 hInv hTI h8 hUniq

section Certified

theorem seventeen_four_of_bBound (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (hm3 : MBarGT D.M V₀ V 3) {L L₁ L₂ : Subgroup G} (hL : L ∈ calC D.M)
    (hTL : D.T ≤ Subgroup.normalizer (L : Set G))
    (hLbar : barSub V₀ V hV.isElemAbelian L ∈ compBar D.M V₀ V hV.isElemAbelian)
    (hsup : L ⊔ (D.T ⊓ Subgroup.normalizer (L : Set G)) = L₁ ⊔ L₂)
    (hS1 : (D.T ⊓ Subgroup.normalizer (L : Set G)) ≤ L₁)
    (hS2 : (D.T ⊓ Subgroup.normalizer (L : Set G)) ≤ L₂)
    (hbar1 : Nonempty (Bar2 L₁ ≃* Equiv.Perm (Fin 3)))
    (hbar2 : Nonempty (Bar2 L₂ ≃* Equiv.Perm (Fin 3)))
    (hU : UniqueMax D.M (L ⊔ D.T)) (hV0 : V₀ ≠ ⊥) (hk : D.k = 1)
    (hb : fixV (barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ →
      bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2) : False := by
  classical
  have hST : (D.T ⊓ Subgroup.normalizer (L : Set G)) = D.T := inf_eq_left.mpr hTL
  have hsup' : L ⊔ D.T = L₁ ⊔ L₂ := by simpa [hST] using hsup
  have hT1 : D.T ≤ L₁ := by simpa [hST] using hS1
  have hT2 : D.T ≤ L₂ := by simpa [hST] using hS2
  obtain ⟨hL1M, hL2M⟩ := le_of_sup_eq_of_uniqueMax hU hsup'
  have hU12 : UniqueMax D.M (L₁ ⊔ L₂) := uniqueMax_sup_of_sup_eq_T hU hsup'
  have hSPE : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    isStronglyPEmbedded_of_k_eq_one D hk
  have hm : 3 < mBar D.M V₀ V hV.isElemAbelian :=
    (hV.mBarGT_iff_lt_mBar 3).1 hm3
  have hLbar_ne : barSub V₀ V hV.isElemAbelian L ≠ ⊥ :=
    CFSG.Quasithin.B15P4.ne_bot_of_isComponentOf hLbar
  have hcardBar1 : Nat.card (Bar2 L₁) = 6 := SeventeenFour.card_bar2_eq_six hbar1
  have hcardBar2 : Nat.card (Bar2 L₂) = 6 := SeventeenFour.card_bar2_eq_six hbar2
  have hcardL1 : Nat.card L₁ = Nat.card (pCoreOf 2 L₁) * 6 := by
    rw [card_eq_card_pCoreOf_mul_card_bar2, hcardBar1]
  have hcardL2 : Nat.card L₂ = Nat.card (pCoreOf 2 L₂) * 6 := by
    rw [card_eq_card_pCoreOf_mul_card_bar2, hcardBar2]
  have hSyl1 : IsSylowIn 2 D.T L₁ := TwelveShort.isSylowIn_of_le D hT1
  have hSyl2 : IsSylowIn 2 D.T L₂ := TwelveShort.isSylowIn_of_le D hT2
  obtain ⟨X₁, hX1le, hX1card, hX1p, hX1T, hTX1, hsup1⟩ :=
    SeventeenFour.exists_order_three_subgroup hT1 hSyl1 hcardL1
  obtain ⟨X₂, hX2le, hX2card, hX2p, hX2T, hTX2, hsup2⟩ :=
    SeventeenFour.exists_order_three_subgroup hT2 hSyl2 hcardL2
  have hX1M : X₁ ≤ D.M := hX1le.trans hL1M
  have hX2M : X₂ ≤ D.M := hX2le.trans hL2M
  have hX1res : X₁ ≤ twoResidual L₁ :=
    CFSG.GroupTheory.le_twoResidual_of_odd_card hX1le (by rw [hX1card]; decide)
  have hX2res : X₂ ≤ twoResidual L₂ :=
    CFSG.GroupTheory.le_twoResidual_of_odd_card hX2le (by rw [hX2card]; decide)
  have hX1ne : X₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hX1card
    omega
  have hX2ne : X₂ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hX2card
    omega
  have hO2 : ∀ H ∈ ({L₁, L₂} : Finset (Subgroup G)), ∀ g : G, g ∉ D.M →
      ¬ twoResidual H ≤ conjSubgroup D.M g := by
    intro H hH g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact SeventeenFour.not_twoResidual_le_conj_of_three D hSPE hX1res hX1M hX1p hX1ne hg
    · exact SeventeenFour.not_twoResidual_le_conj_of_three D hSPE hX2res hX2M hX2p hX2ne hg
  have hΔ : ∀ H ∈ ({L₁, L₂} : Finset (Subgroup G)), D.T ≤ H ∧ H ≤ D.M := by
    intro H hH
    have hcases : H = L₁ ∨ H = L₂ := by simpa using hH
    rcases hcases with h | h
    · simpa [h] using (show D.T ≤ L₁ ∧ L₁ ≤ D.M from ⟨hT1, hL1M⟩)
    · simpa [h] using (show D.T ≤ L₂ ∧ L₂ ≤ D.M from ⟨hT2, hL2M⟩)
  have hΔU : UniqueMax D.M (⨆ H ∈ ({L₁, L₂} : Finset (Subgroup G)), H) := by
    rw [← Finset.sup_eq_iSup]
    have hEq : ({L₁, L₂} : Finset (Subgroup G)).sup (fun H => H) = L₁ ⊔ L₂ := by simp
    rw [hEq]
    exact hU12
  have hι : ∀ H ∈ ({L₁, L₂} : Finset (Subgroup G)),
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H := by
    intro H hH
    have hcases : H = L₁ ∨ H = L₂ := by simpa using hH
    rcases hcases with h | h
    · simpa [h] using CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_bar2_perm_three L₁ hbar1
    · simpa [h] using CFSG.LocalAnalysis.WeakClosure81.inFSq_one_of_bar2_perm_three L₂ hbar2
  have hmax : ({L₁, L₂} : Finset (Subgroup G)).sup (fun _ => 1) = 1 := by simp
  have hmk : D.k + 1 < mBar D.M V₀ V hV.isElemAbelian := by rw [hk]; omega
  have hH : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥ := by
    intro hbot
    apply hLbar_ne
    have hle : barSub V₀ V hV.isElemAbelian L ≤
        barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) :=
      barSub_mono V₀ V hV.isElemAbelian (TwelveTwentyThree.le_conjClosure D.M L)
    exact le_bot_iff.mp (hle.trans (le_of_eq hbot))
  have hfix : fixV (barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ :=
    SeventeenFour.fixV_conjClosure_eq_bot_of_ne_bot D hV hV0 hL.1.le hH
  have hb2 : bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2 := hb hfix
  have hbound := twelve_twentyThree_three_two D hx h61 h66 h127 h1114 h162 hTor h1482 h183
    hV hV0 hL.1 hL.2.2 hLbar_ne hΔ hΔU (fun _ => 1) hι hO2 hmax hmk
  omega

private theorem card_le_four_of_not_eight {V₀ : Subgroup G} (hV₀ : IsElemAbelian 2 V₀)
    (h : ¬ 8 ≤ Nat.card V₀) : Nat.card V₀ ≤ 4 := by
  have hlt : Nat.card V₀ < 8 := by omega
  have hV₀p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup hV₀
  have hcard : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hV₀p
  have hm2 : mSub V₀ ≤ 2 := by
    by_contra h2
    have h3 : 3 ≤ mSub V₀ := by omega
    have hle : 2 ^ 3 ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) h3
    rw [← hcard] at hle
    omega
  calc Nat.card V₀ = 2 ^ mSub V₀ := hcard
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
    _ = 4 := by norm_num

theorem seventeen_four_at (D : Data G) (h111 : W3Thm111 G) (h126 : R126 D)
    (h127 : R127 D) (h618 : W3_6_18 G)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h88 : W3Thm88 G) (h86 : W3Lem86_1 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G) {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    {L L₁ L₂ : Subgroup G} (hL : L ∈ calC D.M)
    (hTL : D.T ≤ Subgroup.normalizer (L : Set G))
    (hLbar : barSub V₀ V hV.isElemAbelian L ∈ compBar D.M V₀ V hV.isElemAbelian)
    (hS1 : (D.T ⊓ Subgroup.normalizer (L : Set G)) ≤ L₁)
    (hS2 : (D.T ⊓ Subgroup.normalizer (L : Set G)) ≤ L₂)
    (hsup : L ⊔ (D.T ⊓ Subgroup.normalizer (L : Set G)) = L₁ ⊔ L₂)
    (hbar1 : Nonempty (Bar2 L₁ ≃* Equiv.Perm (Fin 3)))
    (hbar2 : Nonempty (Bar2 L₂ ≃* Equiv.Perm (Fin 3)))
    (hU : UniqueMax D.M (L ⊔ D.T))
    (hb : D.k = 1 → Nat.card V₀ ≤ 4 →
      fixV (barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ →
      bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2) :
    D.k = 2 := by
  by_cases hk : D.k = 1
  · exfalso
    by_cases h8 : 8 ≤ Nat.card V₀
    · exact seventeen_four_gt2 D hTim hcat h66 h88 hV h8 h93 h86 h126 hTL hsup hS1 hS2
        hbar1 hbar2 hU hk
    · have hcard4 : Nat.card V₀ ≤ 4 :=
        card_le_four_of_not_eight (Hyp125.pairFacts hV).elemAbelian₀ h8
      have hm3 : MBarGT D.M V₀ V 3 := h1669 hcard4
      by_cases hV0 : V₀ = ⊥
      · exact seventeen_four_v0eq1 D h111 h126 h618 hV h1669 hTL hsup hS1 hS2 hU
          hbar1 hbar2 hV0 hk
      · exact seventeen_four_of_bBound D hx h61 h66 h127 h1114 h162 hTor h1482 h183
          hV hm3 hL hTL hLbar hsup hS1 hS2 hbar1 hbar2 hU hV0 hk (hb hk hcard4)
  · have h12 : D.k = 1 ∨ D.k = 2 := by
      have h1 := TwelveShort.one_le_k D
      have h2 := TwelveSeven.k_le_two D
      omega
    rcases h12 with h1 | h2
    · exact absurd h1 hk
    · exact h2

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
