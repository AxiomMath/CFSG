module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NThm1Core
public import CFSG.RankThree.PartTwo.Sec8.Hering88NS8
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofAssembly
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
import CFSG.HardMathSupport.Lang.E27Lie.TrialityTwo
public import CFSG.RankThree.PartTwo.Sec8.Hering88FSmall
public import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofRest

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LieType.Ree

theorem false_of_isSolvable_barCentralizer {G : Type} [Group G] [Finite G] {Y W : Subgroup G}
    {x : G} (hxN : x ∈ Subgroup.normalizer (Y : Set G)) (hx3 : x ^ 3 = 1) (hWY : W ≤ Y)
    (hWx : W ≤ Subgroup.centralizer ({x} : Set G)) (hWp : Group.IsPerfect W) (hW : W ≠ ⊥)
    (hS : Group.IsSolvable (barCentralizer (Subgroup.zpowers x) Y)) : False := by
  have hπ : imageModTheta Y W ≤ barCentralizer (Subgroup.zpowers x) Y := by
    rw [← KFacts.imageModTheta_centralizer_eq hxN ⟨1, by simpa using hx3⟩]
    exact Hering88F.imageModTheta_mono' (le_inf hWY hWx)
  haveI := hS
  haveI : Group.IsSolvable (imageModTheta Y W) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hπ)
  haveI := Item87Proof.isSolvable_ker_modThetaOnto hWY
  have hWs : Group.IsSolvable W :=
    solvable_of_ker_le_range (Item87Proof.modThetaOnto hWY).ker.subtype
      (Item87Proof.modThetaOnto hWY) (by rw [Subgroup.range_subtype])
  haveI : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW
  exact Group.IsPerfect.not_isSolvable W hWs

theorem false_of_pgu_bounds {m N : ℕ} (hodd : Odd m) (hm2 : 2 ≤ m)
    (h3 : (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1) ≤ 3 * N)
    (hle : N ≤ (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1))
    (hL : N = 6048 ∨ N ≤ 720 ∨ (17971200 ≤ N ∧ N ≤ 35942400)) : False := by
  obtain ⟨j, rfl⟩ := hodd
  rcases Nat.lt_or_ge j 2 with hj | hj
  · obtain rfl : j = 1 := by omega
    norm_num at h3 hle
    omega
  · have hq : 32 ≤ 2 ^ (2 * j + 1) := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (2 * j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    set q := 2 ^ (2 * j + 1) with hqdef
    have h1 : 32768 ≤ q ^ 3 := by
      calc 32768 = 32 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 1024 ≤ q ^ 2 := by
      calc 1024 = 32 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have hbig : 32768 * 1023 * 32769 ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) (by omega)
    omega


theorem lside_abs {G : Type} [Group G] [Finite G] {A M : Subgroup G} {a v : G}
    (hv : IsGammaIndex A M v 1) (hUn : ¬ IsUnitaryTwo (M ⧸ aschbacherSolvableCore 3 M) 3)
    (ha3 : a ^ 3 = 1)
    (hk : KFacts.InducesStdKind M a .field ∨ KFacts.InducesStdKind M a .graphField) :
    ((IsoTrialityD4 (M ⧸ aschbacherSolvableCore 3 M) 1 ∨
        IsoGTwoEven (M ⧸ aschbacherSolvableCore 3 M) (3 * 1)) ∧
      Nonempty (imageModTheta M (inSubgroup perfectResidual
        (M ⊓ Subgroup.centralizer ({v} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * 1)))) ∨
    Nat.card (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)) ⧸
        aschbacherSolvableCore 3 (inSubgroup perfectResidual
          (M ⊓ Subgroup.centralizer ({a} : Set G)))) ≤ 720 ∨
    (17971200 ≤ Nat.card (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)) ⧸
        aschbacherSolvableCore 3 (inSubgroup perfectResidual
          (M ⊓ Subgroup.centralizer ({a} : Set G)))) ∧
      Nat.card (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)) ⧸
        aschbacherSolvableCore 3 (inSubgroup perfectResidual
          (M ⊓ Subgroup.centralizer ({a} : Set G)))) ≤ 35942400) := by
  classical
  obtain ⟨-, -, -, hcases⟩ := Item87Proof.isGammaIndex_cases hv
  have haN : a ∈ Subgroup.normalizer (M : Set G) :=
    hk.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have haout : Sec4.InducesOuterTheta a M := by
    rcases hk with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta M h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta M h' (by decide)
  have hWM : inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)) ≤ M :=
    (Item87Proof.residual_le _).trans inf_le_left
  have hW_img : imageModTheta M (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G))) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M) :=
    KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by simpa using ha3⟩
  rcases hcases with ⟨hRee, -⟩ | ⟨htype, hKL2⟩
  ·
    right; right
    obtain ⟨k₀, hk₀, hkp, ⟨e₀⟩⟩ := hRee
    have hRT : CFSG.Blueprint.ReeTitsModel (M ⧸ aschbacherSolvableCore 3 M) .twistedF4 2
        (2 * k₀ + 1) :=
      CFSG.SectionRank.reeTitsModel_of_mulEquiv e₀ (Sec4.Census.bridgeExceptional46.reeF4 k₀ hk₀)
    obtain ⟨-, a', ha'1, hka, Kf, _, _, _, hKf, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hRT
    obtain ⟨b', k', _, _, _, hk', hb', ⟨φ⟩⟩ :=
      Item812Res2.exists_barCentralizer_mulEquiv_reeGamma_index ha'1 hKf e ha3 haout
    obtain rfl : b' = 0 := by omega
    have hk2 : Nat.card k' = 2 := by simpa using hk'
    have hS := isSimpleGroup_inSubgroup_perfectResidual_of_reeGamma_zero hk2 φ
    rw [card_quot_theta_eq_of_isSimpleGroup hWM hW_img hS]
    exact card_inSubgroup_perfectResidual_of_reeGamma_zero hk2 φ
  · rcases htype with hD | ⟨q, hq2, hqe, hGq⟩ | hU | hSU | hSp
    · exact Or.inl ⟨Or.inl hD, hKL2⟩
    · exact Or.inl ⟨Or.inr (Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hGq), hKL2⟩
    · exact (hUn (Or.inl (by simpa using hU))).elim
    · exact (hUn (Or.inr (by simpa using hSU))).elim
    ·
      right; left
      obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp one_ne_zero ha3 haout hSp
      have h720 : Nat.card (barCentralizer (Subgroup.zpowers a) M) = 720 := by
        rw [Nat.card_congr ι.toEquiv]
        exact Item812Res2.card_projSp_two_one
      have hdvd := card_quot_theta_dvd_card_imageModTheta hWM
      rw [hW_img] at hdvd
      have hle := Subgroup.card_le_of_le
        (Item87Proof.residual_le (barCentralizer (Subgroup.zpowers a) M))
      exact (Nat.le_of_dvd Nat.card_pos hdvd).trans (hle.trans h720.le)

theorem lside_of_not_unitary {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a b : G} {X : Subgroup G} (h : Sec8Pair G A c L a b X 1)
    (hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3) :
    ((IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) 1 ∨
        IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * 1)) ∧
      Nonempty (imageModTheta L (inSubgroup perfectResidual
        (L ⊓ Subgroup.centralizer ({b} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * 1)))) ∨
    Nat.card (sec8I L a ⧸ aschbacherSolvableCore 3 (sec8I L a)) ≤ 720 ∨
    (17971200 ≤ Nat.card (sec8I L a ⧸ aschbacherSolvableCore 3 (sec8I L a)) ∧
      Nat.card (sec8I L a ⧸ aschbacherSolvableCore 3 (sec8I L a)) ≤ 35942400) := by
  classical
  have ha3 : a ^ 3 = 1 := (Hering88C.pair_commute_pow_three h).2 a h.a_mem
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hUn, ↓reduceIte]
  rw [hIdef]
  exact lside_abs h.isGammaIndex hUn ha3 h.inducesStdKind

theorem classBOne_of_not_unitary (h45 : Sec4.Item4_5) (h47 : Sec4.Inputs47ClassesD4)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} (h : Sec8Pair G A c L a b X 1)
    (hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hxY : KFacts.InducesStdKind Y c .field ∨ KFacts.InducesStdKind Y c .graphField)
    {A₀ : Subgroup G} {d' : G} {m : ℕ} (hodd : Odd m) (hc1 : Case83One Y c A₀ d' m)
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdc : d ∉ Subgroup.zpowers c)
    (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1) :
    Nonempty (imageModTheta Y (inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * m))) := by
  classical
  obtain ⟨-, hA3⟩ := Hering88C.pair_commute_pow_three h
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  have hc3 : c ^ 3 = 1 := hA3 c h.mem_A
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  have haN : a ∈ Subgroup.normalizer (L : Set G) := h.toHyp81.a_mem_normalizer
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) :=
    hxY.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have hcout : Sec4.InducesOuterTheta c Y := by
    rcases hxY with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hUn, ↓reduceIte]
  have hIL : sec8I L a ≤ L := by
    rw [hIdef]
    exact (Item87Proof.residual_le _).trans inf_le_left
  have hIY : sec8I L a ≤ Y := le_sup_left.trans hIJ
  have hIc : sec8I L a ≤ Subgroup.centralizer ({c} : Set G) := hIL.trans hLc
  have hIp : Group.IsPerfect (sec8I L a) := by
    rw [hIdef]
    exact Item87Proof.isPerfect_residual _
  have hIL_img : imageModTheta L (sec8I L a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L) := by
    rw [hIdef]
    exact KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by simpa using ha3⟩
  have hI : sec8I L a ≠ ⊥ := by
    intro hbot
    apply kF87INontriv_holds G L a 1 le_rfl
      (Item87Proof.isGammaType_of_isGammaIndex h.isGammaIndex) hUn ha3 h.inducesStdKind h.gTwo
    rw [← hIL_img, hbot, imageModTheta, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hLside := lside_of_not_unitary h hUn
  have hN6048 : (IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) 1 ∨
      IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * 1)) →
      Nat.card (sec8I L a ⧸ aschbacherSolvableCore 3 (sec8I L a)) = 6048 := fun hL1 => by
    have hG2L := h.gTwo hL1
    rw [card_quot_theta_eq_of_isSimpleGroup hIL hIL_img
      (isSimpleGroup_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2L),
      card_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2L]
  rcases hc1.2.2 with hG2 | ⟨-, hP, -⟩
  ·
    rcases Nat.lt_or_ge m 2 with hm | hm2
    · obtain rfl : m = 1 := by have := hodd.pos; omega
      have hS := isSimpleGroup_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2
      have hM1 := Hering88E.imageModTheta_sec8I_eq_perfectResidual kF87Cent_holds h hUn hI hY hIY
        hcN hS
      have hNY : Nat.card (sec8I L a ⧸ aschbacherSolvableCore 3 (sec8I L a)) = 6048 := by
        rw [card_quot_theta_eq_of_isSimpleGroup hIY hM1 hS,
          card_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2]
      rcases hLside with ⟨hL1, hKL2⟩ | hle | ⟨hge, -⟩
      · exact classBOne_core h45 h47 h hUn hL1 hKL2 hY hIJ hcN hcout hc1.1 hG2 hdcl hdc hdA hd3
          hdN hin hne
      · omega
      · omega
    · exfalso
      have hS := Hering88E.isSimpleGroup_perfectResidual_of_isoGTwoEven hm2 hG2
      have hM1 := Hering88E.imageModTheta_sec8I_eq_perfectResidual kF87Cent_holds h hUn hI hY hIY
        hcN hS
      have hNY : 251596800 ≤ Nat.card (sec8I L a ⧸ aschbacherSolvableCore 3 (sec8I L a)) := by
        rw [card_quot_theta_eq_of_isSimpleGroup hIY hM1 hS]
        exact card_inSubgroup_perfectResidual_ge_of_isoGTwoEven hm2 hG2
      rcases hLside with ⟨hL1, -⟩ | hle | ⟨-, hle⟩
      · have := hN6048 hL1
        omega
      · omega
      · omega
  ·
    exfalso
    rcases Nat.lt_or_ge m 2 with hm | hm2
    · obtain rfl : m = 1 := by have := hodd.pos; omega
      exact false_of_isSolvable_barCentralizer hcN hc3 hIY hIc hIp hI
        (Hering88F.isSolvable_of_isoPGUThree_two hP)
    · have hS := isSimpleGroup_inSubgroup_perfectResidual_of_isoPGUThree hm2 hP
      have hM1 := Hering88E.imageModTheta_sec8I_eq_perfectResidual kF87Cent_holds h hUn hI hY hIY
        hcN hS
      have hNY := card_quot_theta_eq_of_isSimpleGroup hIY hM1 hS
      have h3 := card_le_three_mul_card_inSubgroup_perfectResidual_of_isoPGUThree hm2 hP
      have hle := Subgroup.card_le_of_le
        (Item87Proof.residual_le (barCentralizer (Subgroup.zpowers c) Y))
      have hcard := CFSG.HardMathSupport.Lang.E27Lie.card_isoPGUThree (by omega) hP
      rw [← hNY, hcard] at h3
      rw [← hNY, hcard] at hle
      refine false_of_pgu_bounds hodd hm2 h3 hle ?_
      rcases hLside with ⟨hL1, -⟩ | hle' | hge
      · exact Or.inl (hN6048 hL1)
      · exact Or.inr (Or.inl hle')
      · exact Or.inr (Or.inr hge)

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
