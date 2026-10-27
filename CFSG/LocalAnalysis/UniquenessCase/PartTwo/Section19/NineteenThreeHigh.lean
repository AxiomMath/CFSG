module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThreeNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteenFour
public import CFSG.GroupTheory.PRankCommutingPerfect
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588A1
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructFive
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank
public import CFSG.Quasithin.Vol2.Ch10SecKIK4g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_3At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  3 < mSub V₀ →
    ∀ J : Subgroup G, (J = K ∨ (J = L ∧ IsL2 (Bar2 L) 2 ∧ ⁅K, V₀⁆ = ⊥)) → ⁅J, V₀⁆ ≠ ⊥ →
      ∃ Y : Subgroup G, Y ≤ D.M ∧ Nat.card Y = 5 ∧ (Y : Set G) * D.T = D.T * Y ∧
        ⁅Y, J⁆ ≤ pCoreOf 2 D.M

theorem le_normalizer_wClos_zero_of_isPGroup_five (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (h66 : UC6.R6_6 D) (h88 : W3Thm88 G) (h93 : Thm93 V₀ D.T)
    (hsp : IsStronglyPEmbedded 5 D.M) (h8 : 8 ≤ Nat.card V₀) {Y : Subgroup G}
    (hYp : IsPGroup 5 Y) (hYM : Y ≤ D.M) (hYT : (Y : Set G) * D.T = D.T * Y) :
    Y ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) := by
  have hXM : ∀ g : G, g ∉ D.M → V₀ ≤ conjSubgroup D.M g → Y ⊓ conjSubgroup D.M g = ⊥ := by
    intro g hg _
    have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
    have h' := hsp.inf_map_conj_eq_bot (by norm_num) hYM hYp g⁻¹ hg'
    simpa [conjSubgroup] using h'
  have hΓ : rankThreeGamma 1 5 Y ≤ D.M :=
    hsp.rankThreeGamma_one_le_of_le (by norm_num) hYp hYM
  exact (twelve_sixteen hTim hcat D h66 h88 h h8 h93 (p := 5) (by norm_num) (by norm_num) hYp
    hXM hΓ hYT).2

theorem uniqueMax_of_commutator_le_pCoreOf (D : Data G) (h61 : UC6.R6_1 D) (h5 : 5 ∈ D.sig)
    {H Y J : Subgroup G} (hHM : H ≤ D.M) (hYH : Y ≤ H) (hJH : J ≤ H)
    (hcomm : ⁅Y, J⁆ ≤ pCoreOf 2 D.M) (hJperf : ⁅J, J⁆ = J) (h5J : 5 ∣ Nat.card J)
    (h5Y : 5 ∣ Nat.card Y) : UniqueMax D.M H := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcommH : ⁅Y, J⁆ ≤ H :=
    Subgroup.commutator_le.2 fun a ha b hb =>
      H.mul_mem (H.mul_mem (H.mul_mem (hYH ha) (hJH hb)) (H.inv_mem (hYH ha))) (H.inv_mem (hJH hb))
  have hcore : pCoreOf 2 D.M ⊓ H ≤ pCoreOf 2 H := by
    refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf inf_le_right ?_
      ((CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 D.M).to_le inf_le_left)
    intro x hx y hy
    exact ⟨CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf (hHM hx) hy.1,
      H.mul_mem (H.mul_mem hx hy.2) (H.inv_mem hx)⟩
  have hc : ⁅Y, J⁆ ≤ pCoreOf 2 H := (le_inf hcomm hcommH).trans hcore
  have hrank : CFSG.Open.pRank 5 Y + 1 ≤ CFSG.Open.pRank 5 H :=
    CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf (q := 5) (by norm_num) hYH hJH
      hc hJperf h5J
  have h2 : 2 ≤ CFSG.Open.pRank 5 H := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 5 h5Y
    have hxo : orderOf (x : G) = 5 := (Subgroup.orderOf_coe x).trans hx
    have := CFSG.LocalAnalysis.UniquenessCase.UCK.N588A.one_le_pRank Nat.prime_five
      (Subgroup.zpowers_le.2 x.2) (by rw [Nat.card_zpowers, hxo])
    omega
  obtain ⟨E, hEH, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := H) Nat.prime_five (k := 2) h2
  have hEp : IsPGroup 5 E := by
    intro g
    exact ⟨1, Subtype.ext (by simpa using hEel.2 (g : G) g.2)⟩
  have hEnc : ¬ IsCyclic E :=
    CFSG.LocalAnalysis.RankThreeUC.S15.not_isCyclic_of_isElemAbelian Nat.prime_five
      (by norm_num) hEel hEcard
  exact c23_uniqueMax_of_noncyclic D h61 h5 hEp hEnc hEH hHM

theorem false_of_le_normalizer_wClos_zero (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h61 : UC6.R6_1 D) (h86 : W3Lem86_1 G)
    (h126 : R126 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hne : V₀ ≠ ⊥)
    (h8 : 8 ≤ Nat.card V₀) (h5 : 5 ∈ D.sig) {Y J : Subgroup G} (hYM : Y ≤ D.M)
    (hY5 : Nat.card Y = 5) (hJM : J ≤ D.M) (hJperf : ⁅J, J⁆ = J) (h5J : 5 ∣ Nat.card J)
    (hYJ : ⁅Y, J⁆ ≤ pCoreOf 2 D.M)
    (hYN : Y ≤ normalizer (E3.wClos V₀ 0 D.T : Set G))
    (hJN : J ≤ normalizer (E3.wClos V₀ 0 D.T : Set G)) : False :=
  twelve_seven_one hTim hcat D h86 h126 h.2 (S17.hyp125_inCalV h hne) (S17.hyp125_isTI h hne) h8
    (uniqueMax_of_commutator_le_pCoreOf D h61 h5 inf_le_left (le_inf hYM hYN) (le_inf hJM hJN)
      hYJ hJperf h5J (by rw [hY5]))

theorem le_centralizer_V0_of_isU3 (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hU3 : IsU3 (Bar2 L) 2) : L ≤ centralizer (V₀ : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hbr5 : CFSG.pRank 5 ↥(⊤ : Subgroup (Bar2 L)) =
      CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 5 ↥(⊤ : Subgroup (Bar2 L))).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 5) (⊤ : Subgroup (Bar2 L))).symm
  have hr2 : CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) = 2 :=
    hbr5.symm.trans (Inputs1719.kU34Data_fiveRank (Bar2 L) hU3)
  have hrankL : 2 ≤ CFSG.Open.pRank 5 L :=
    S17.two_le_pRank_of_bar2 Nat.prime_five (by norm_num) (by rw [hr2])
  obtain ⟨E, hEL, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := L) Nat.prime_five (k := 2) hrankL
  have hEp : IsPGroup 5 E := by
    intro g
    exact ⟨1, Subtype.ext (by simpa using hEel.2 (g : G) g.2)⟩
  have hEnc : ¬ IsCyclic E :=
    CFSG.LocalAnalysis.RankThreeUC.S15.not_isCyclic_of_isElemAbelian Nat.prime_five
      (by norm_num) hEel hEcard
  have : IsMulCommutative ↥E := hEel.1
  have : ((E ⊓ centralizer (V₀ : Set G)).subgroupOf E).Normal := Subgroup.normal_of_comm _
  have hcyc := ElevenFourteen.eleven_four_one_of_sig D h61 (Hyp125.hyp11 h127 h.hyp.hyp125)
    (h.p_eq ▸ h.hyp.hp) (hEL.trans hLM) hEp
  have hEC : E ⊓ centralizer (V₀ : Set G) ≠ ⊥ := by
    intro hbot
    apply hEnc
    have hsub : (E ⊓ centralizer (V₀ : Set G)).subgroupOf E = ⊥ := by
      rw [hbot, Subgroup.bot_subgroupOf]
    let e : ↥E ⧸ (E ⊓ centralizer (V₀ : Set G)).subgroupOf E ≃* ↥E :=
      (QuotientGroup.quotientMulEquivOfEq hsub).trans QuotientGroup.quotientBot
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  obtain ⟨⟨c, hcEC⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEC
  have hc1' : c ≠ 1 := fun h1 => hc1 (Subtype.ext h1)
  have hco : orderOf c = 5 := orderOf_eq_prime (hEel.2 c hcEC.1) hc1'
  have hLN : L ≤ normalizer (L ⊓ centralizer (V₀ : Set G) : Set G) := by
    have h1 : L ≤ normalizer (centralizer (V₀ : Set G) : Set G) :=
      CFSG.Quasithin.B6.le_normalizer_centralizer
        (hLM.trans h.hyp.hyp125.pairFacts.le_normalizer₀)
    intro l hl
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl, h1 hl⟩
  have hNn : ((L ⊓ centralizer (V₀ : Set G)).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hLN
  have hnot : ¬ (L ⊓ centralizer (V₀ : Set G)).subgroupOf L ≤ CFSG.pCore 2 ↥L := by
    intro hle
    have hcL : c ∈ L := hEL hcEC.1
    have hmem : (⟨c, hcL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      hle (Subgroup.mem_subgroupOf.2 ⟨hcL, hcEC.2⟩)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hmem⟩
    have hk' : c ^ (2 ^ k) = 1 := by
      have := congrArg (fun x : ↥(CFSG.pCore 2 ↥L) => ((x : ↥L) : G)) hk
      simpa using this
    have hdvd : 5 ∣ 2 ^ k := hco ▸ orderOf_dvd_of_pow_eq_one hk'
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow hdvd)) (by norm_num)
  have htop := CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.eq_top_of_not_le_pCore h.hyp.hL.1.2.1
    (isSimpleGroup_bar2_of_shape h.shape) hnot
  intro l hl
  have hmem : (⟨l, hl⟩ : ↥L) ∈ (L ⊓ centralizer (V₀ : Set G)).subgroupOf L := by
    rw [htop]; exact Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf.1 hmem).2

theorem nineteen_three_of_three_lt (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D)
    (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D) (h127 : R127 D)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h93 : Thm93 V₀ D.T) (hgap : Gap19_3At D V₀ V p L K h)
    (hm : 3 < mSub V₀) : R19_3At D V₀ V p L K h := by
  have hne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have h8 : 8 ≤ Nat.card V₀ := by
    have hcardV0 : Nat.card V₀ = 2 ^ mSub V₀ :=
      card_eq_two_pow_mSub h.hyp.hyp125.pairFacts.elemAbelian₀.isPGroup
    rw [hcardV0]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5
  have key : ∀ J : Subgroup G, (J = K ∨ (J = L ∧ IsL2 (Bar2 L) 2 ∧ ⁅K, V₀⁆ = ⊥)) →
      ⁅J, V₀⁆ = ⊥ := by
    intro J hJ
    by_contra hJV
    obtain ⟨Y, hYM, hY5, hYT, hYJ⟩ := hgap hm J hJ hJV
    have hYp : IsPGroup 5 Y := IsPGroup.of_card (hY5.trans (pow_one 5).symm)
    have hYN := le_normalizer_wClos_zero_of_isPGroup_five hTim hcat h.hyp.hyp125 h66 h88 h93 hsp
      h8 hYp hYM hYT
    have hJdata : J ∈ calC D.M ∧ 5 ∣ Nat.card J := by
      rcases hJ with rfl | ⟨rfl, -, -⟩
      · exact ⟨h.hK, UC22.InS3.UC49.five_dvd_card_of_isAlt h.hKshape⟩
      · exact ⟨h.hyp.hL.1, (h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet J).2⟩
    have hJN := le_normalizer_wClos_zero_of_commutator_ne D h.hyp.hyp125 hne hJdata.1 hJV
    exact false_of_le_normalizer_wClos_zero hTim hcat D h61 h86 h126 h.hyp.hyp125 hne h8 h5 hYM
      hY5 (CFSG.Quasithin.A3.subnormal_le hJdata.1.1) hJdata.1.2.1 hJdata.2 hYJ
      (le_sup_left.trans hYN) hJN
  have hKc : ⁅K, V₀⁆ = ⊥ := key K (Or.inl rfl)
  have hLc : L ≤ centralizer (V₀ : Set G) := by
    rcases h.shape with hL2 | hU3
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (key L (Or.inr ⟨rfl, hL2, hKc⟩))
    · exact le_centralizer_V0_of_isU3 D h61 h127 h hU3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2
    (sup_le hLc (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKc))

theorem nineteen_three_At (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D)
    (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D) (h127 : R127 D)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h93 : Thm93 V₀ D.T) (hgap : Gap19_3At D V₀ V p L K h) :
    R19_3At D V₀ V p L K h := by
  by_cases hm : mSub V₀ ≤ 3
  · exact nineteen_three_of_rank_le_three D h hm
  · exact nineteen_three_of_three_lt hTim hcat D h61 h66 h86 h88 h126 h127 hSg h h93 hgap
      (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
