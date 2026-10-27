module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof
public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofSL3Bridge
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.RankThree.PartTwo.Sec5.Bender.Core
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageSylowNormalizers
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofList
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProof224
public import CFSG.RankThree.PartTwo.Sec21.Item22Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof
open scoped commutatorElement

@[expose] def Item224TorusElliptic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
    ∀ T : Subgroup (MulAut (lBar L)), IsPGroup 2 T → T ≠ ⊥ →
      T ≤ Subgroup.centralizer (Sec4.autThetaQuot A L : Set (MulAut (lBar L))) →
      AutElliptic (lBar L) T

theorem item224Elliptic_of_torusElliptic (h222 : Item222) (h213 : Item213) (h45 : Sec4.Item4_5)
    (hTor : Item224TorusElliptic) : Item224Elliptic := by
  intro G _ _ A U c L hpair hA27 S hS1 M hM hSM hUM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcB, hc1, hLc', hUN, hVN, hLU, hLV⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hLc'
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcB.1
      hc1 L hLc
  have hLq : IsQuasisimple L := h213 G A A U c L hpair
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  set φ := (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hφ
  set S' : Subgroup G := (S : Subgroup (Subgroup.centralizer (A : Set G))).map
    (Subgroup.centralizer (A : Set G)).subtype with hS'
  have hS'A : S' ≤ Subgroup.centralizer (A : Set G) := Subgroup.map_subtype_le _
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map _
  have hS'L : S' ≤ Subgroup.normalizer (L : Set G) :=
    hS'A.trans (centralizer_le_normalizer_of_sec21Pair h222 h213 hpair)
  set E := Sec4.autThetaQuot A L with hE
  set T := Sec4.autThetaQuot S' L with hT
  have hTE : T ≤ Subgroup.centralizer (E : Set (MulAut (lBar L))) := by
    intro τ hτ
    obtain ⟨s, hsN, hsS, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    rw [Subgroup.mem_centralizer_iff]
    intro η hη
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hη
    change φ ⟨a, haN⟩ * φ ⟨s, hsN⟩ = φ ⟨s, hsN⟩ * φ ⟨a, haN⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (show a * s = s * a from Subgroup.mem_centralizer_iff.mp (hS'A hsS) a haA)
  have hell : AutElliptic (lBar L) T := by
    by_cases hT1 : T = ⊥
    · rw [hT1]
      exact autElliptic_bot (Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc)
    · exact hTor G A A U c L hpair hA27 T (isPGroup_autThetaQuot L hS'2) hT1 hTE
  set R := inSubgroup (CFSG.pCore 2) M with hR
  have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup.map _
  have hMR : M ≤ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer.trans
    (CFSG.SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic M (CFSG.pCore 2 M))
  have hRN : (oddFixed (lBar L) T).map MulAut.conj ≤
      Subgroup.normalizer (Sec4.autThetaQuot R L : Set (MulAut (lBar L))) := by
    rw [Subgroup.map_le_iff_le_comap, oddFixed, Subgroup.closure_le]
    rintro x ⟨hxT, hxodd⟩
    obtain ⟨l, hlS, rfl⟩ := exists_centralizer_lift_of_odd hLq hS'2 hS'L hxodd hxT
    have hlM : (l : G) ∈ M := hSM (Subgroup.centralizer_le_normalizer _ hlS)
    rw [SetLike.mem_coe, Subgroup.mem_comap, ← thetaQuotMulAut_normalizerMonoidHom_of_mem l.2]
    exact mem_normalizer_autThetaQuot (L.le_normalizer l.2) (hMR hlM)
  obtain ⟨hRfix, -⟩ := hell (Sec4.autThetaQuot R L) (isPGroup_autThetaQuot L hR2) hRN
  have hU2 : IsPGroup 2 U := Sec5.isPGroup_of_isElemAbelian hpair.mem_U.2.1
  have hUfix : ∀ τ ∈ Sec4.autThetaQuot U L, ∀ x ∈ oddFixed (lBar L) T, τ x = x :=
    fun τ hτ x hx => hRfix τ (autThetaQuot_mono hUM hτ) x hx
  set P := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ((U : Set G) ∪ {c})) with hP
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup.map _
  have hCP : Subgroup.centralizer ((U : Set G) ∪ {c}) ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic _ (CFSG.pCore 2 _))
  have hYN : (oddFixed (lBar L) T).map MulAut.conj ≤
      Subgroup.normalizer (Sec4.autThetaQuot P L : Set (MulAut (lBar L))) := by
    rw [Subgroup.map_le_iff_le_comap, oddFixed, Subgroup.closure_le]
    rintro x ⟨hxT, hxodd⟩
    have hxU : ∀ τ ∈ Sec4.autThetaQuot U L, τ x = x := fun τ hτ =>
      hUfix τ hτ x (Subgroup.subset_closure ⟨hxT, hxodd⟩)
    obtain ⟨l, hlU, rfl⟩ := exists_centralizer_lift_of_odd hLq hU2 hUN hxodd hxU
    have hlC : (l : G) ∈ Subgroup.centralizer ((U : Set G) ∪ {c}) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro y (hy | hy)
      · exact Subgroup.mem_centralizer_iff.mp hlU y hy
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hLC l.2)).symm
    rw [SetLike.mem_coe, Subgroup.mem_comap, ← thetaQuotMulAut_normalizerMonoidHom_of_mem l.2]
    exact mem_normalizer_autThetaQuot (L.le_normalizer l.2) (hCP hlC)
  obtain ⟨-, hYcyc⟩ := hell (Sec4.autThetaQuot P L) (isPGroup_autThetaQuot L hP2) hYN
  set B : Subgroup G := A ⊓ Subgroup.centralizer (U : Set G) with hBdef
  set V : Subgroup G := lThreeV A U c with hVdef
  have hVPB : V = ⁅P, B⁆ := rfl
  have hBC : B ≤ Subgroup.centralizer ((U : Set G) ∪ {c}) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    rintro x (hx | hx)
    · exact Subgroup.mem_centralizer_iff.mp hb.2 x hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact congrArg Subtype.val (hAe.1.is_comm.comm ⟨_, hcB.1⟩ ⟨b, hb.1⟩)
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := hBC.trans hCP
  have hB3 : IsPGroup 3 B := (Sec5.isPGroup_of_isElemAbelian hAe).to_le inf_le_left
  have hcop : Nat.Coprime (Nat.card B) (Nat.card P) := by
    obtain ⟨i, hi⟩ := hB3.exists_card_eq
    obtain ⟨j, hj⟩ := hP2.exists_card_eq
    rw [hi, hj]
    exact Nat.Coprime.pow i j (by norm_num)
  have hVVB : V ≤ ⁅V, B⁆ := hVPB ▸ Sec5.Bender.commutator_le_commutator_commutator P B hBP hcop
  have hVP : V ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hBP
  have hBV : B ≤ Subgroup.normalizer (V : Set G) := Subgroup.normalizer_commutator_ge_right P B
  have : IsCyclic (Sec4.autThetaQuot V L) := Subgroup.isCyclic_of_le (autThetaQuot_mono hVP)
  have hBbVb : Sec4.autThetaQuot B L ≤
      Subgroup.normalizer (Sec4.autThetaQuot V L : Set (MulAut (lBar L))) := by
    intro τ hτ
    obtain ⟨b, hbN, hb, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    exact mem_normalizer_autThetaQuot hbN (hBV hb)
  have hcomm := Item22Res3Proof.commutator_eq_bot_of_isCyclic
    (isPGroup_autThetaQuot L (hP2.to_le hVP)) (isPGroup_autThetaQuot L hB3) hBbVb
  have hVBtriv : ⁅V, B⁆ ≤ Sec4.thetaQuotCentralizer L := by
    rw [Subgroup.commutator_le]
    intro v hv b hb
    have hvN : v ∈ Subgroup.normalizer (L : Set G) := hVN hv
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := hAL hb.1
    refine ⟨⁅(⟨v, hvN⟩ : Subgroup.normalizer (L : Set G)), ⟨b, hbN⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have hx : φ ⟨v, hvN⟩ ∈ Sec4.autThetaQuot V L :=
      Sec4.mem_autThetaQuot_iff.mpr ⟨v, hvN, hv, rfl⟩
    have hy : φ ⟨b, hbN⟩ ∈ Sec4.autThetaQuot B L :=
      Sec4.mem_autThetaQuot_iff.mpr ⟨b, hbN, hb, rfl⟩
    have h1 := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement] at h1
    exact h1
  have hVtriv : V ≤ Sec4.thetaQuotCentralizer L := hVVB.trans hVBtriv
  have hLVθ : ⁅L, V⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    rw [Subgroup.commutator_le]
    intro l hl v hv
    obtain ⟨g, hg, rfl⟩ := hVtriv hv
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hg
    have hgl := congrArg (fun σ : MulAut (lBar L) => σ ((⟨l⁻¹, L.inv_mem hl⟩ : L) : lBar L)) hg
    change (((L.normalizerMonoidHom g) ⟨l⁻¹, L.inv_mem hl⟩ : L) : lBar L) =
      ((⟨l⁻¹, L.inv_mem hl⟩ : L) : lBar L) at hgl
    have hmem : ((⟨l, hl⟩ : L) * (L.normalizerMonoidHom g) ⟨l⁻¹, L.inv_mem hl⟩ : L) ∈
        aschbacherSolvableCore 3 L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hgl, ← QuotientGroup.mk_mul,
        show ((⟨l, hl⟩ : L) * ⟨l⁻¹, L.inv_mem hl⟩ : L) = 1 from Subtype.ext (mul_inv_cancel l),
        QuotientGroup.mk_one]
    refine ⟨_, hmem, ?_⟩
    change l * ((g : G) * l⁻¹ * (g : G)⁻¹) = ⁅l, (g : G)⁆
    rw [commutatorElement_def]
    group
  have hLθ : L ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    calc L = ⁅L, V⁆ := hLV.symm
      _ ≤ _ := hLVθ
  have hLbq : IsQuasisimple (lBar L) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have : Nontrivial (lBar L) := CFSG.LocalCores.isQuasisimple_nontrivial hLbq
  have htriv : ∀ y : L, ((y : L) : lBar L) = 1 := by
    intro y
    obtain ⟨z, hz, hzy⟩ := hLθ y.2
    have : z = y := Subtype.ext hzy
    rw [← this]
    exact (QuotientGroup.eq_one_iff z).mpr hz
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (lBar L)
  apply hxy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [htriv x, htriv y]

section Certs

namespace Item224Res6Proof

variable {G : Type} [Group G] [Finite G]

theorem autElliptic_of_SL3 (hNF3 : Item211NoFieldThree) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) {n : ℕ} (hn : 0 < n)
    (he : Even n) (eL : lBar L ≃* SL3 n) (hE9 : Nat.card (Sec4.autThetaQuot A L) = 9)
    (hfix : ∃ x : lBar L, orderOf x = 3 ∧ x ∉ Subgroup.center (lBar L) ∧
      ∀ e ∈ Sec4.autThetaQuot A L, e x = x)
    {T : Subgroup (MulAut (lBar L))} (hT : IsPGroup 2 T)
    (hTE : T ≤ Subgroup.centralizer (Sec4.autThetaQuot A L : Set (MulAut (lBar L)))) :
    AutElliptic (lBar L) T := by
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hEe : IsElemAbelian 3 (Sec4.autThetaQuot A L) := isElemAbelian_autThetaQuot L hAe
  obtain ⟨ω, hω⟩ := Item224KFactsProof.exists_cube_root_galoisField hn he
  obtain ⟨x, hx3, hxZ, hxE⟩ := hfix
  have hx3' : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx3] at h
  exact Item224KFactsProof.autElliptic_of_inndiag_mulEquiv hω eL (fun α hα => hEe.2 α hα) hE9
    (Item224KFactsProof.inndiag_of_not_field eL (fun a ha => hAe.2 a ha) fun a ha h =>
      (hNF3 G A E U c L hpair hA27 a ha).1 (KFacts.InducesStdKind.sl 3 _ le_rfl h))
    hx3' hxZ hxE hT hTE

end Item224Res6Proof

open Item224Res6Proof

theorem item224TorusElliptic_of_res6 (h221 : Item221) (h222 : Item222) (h213 : Item213)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (hSp4 : KS224Sp4) (hU4 : KS224U4)
    (hU5 : KS224U5) (hNF3 : Item211NoFieldThree) : Item224TorusElliptic := by
  intro G _ _ A E U c L hpair hA27 T hT hT1 hTE
  obtain ⟨hcB, hc1, hLc', -, -, -, -⟩ := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hLc'
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe
      (hpair.mem_E.2 hcB.1) hc1 L hLc
  have hLq : IsQuasisimple L := h213 G A E U c L hpair
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hEe := isElemAbelian_autThetaQuot L hAe
  have hE9 := card_autThetaQuot_eq_nine h66 hpair hA27 hAL
  have hinner := innerThreeFixed_autThetaQuot hpair hLq hAL
  have hfix := exists_noncentral_fixed h222 hpair
  rcases h221 G A E U c L hpair with ⟨h81, -⟩ | ⟨-, hcase⟩
  · rw [hA27] at h81
    norm_num at h81
  rcases hcase with ⟨n, hn, he, heL | heL | heL⟩ | heL | ⟨heB, -⟩
  · obtain ⟨eL⟩ := heL
    have hn2 : 2 ≤ n := by
      obtain ⟨k, hk⟩ := he
      omega
    have := isSimpleGroup_projSp_two hn2
    exact hSp4 (lBar L) n hn he
      ⟨(mulEquiv_lBar_of_theta_eq_bot (inSubgroup_theta_eq_bot_of_mulEquiv hLp eL)).symm.trans eL⟩
      _ hEe hE9 hinner hfix T hT hT1 hTE
  · obtain ⟨eL⟩ := heL
    have := isSimpleGroup_projSU (m := 4) (n := n) le_rfl hn
    exact hU4 (lBar L) n hn he
      ⟨(mulEquiv_lBar_of_theta_eq_bot (inSubgroup_theta_eq_bot_of_mulEquiv hLp eL)).symm.trans eL⟩
      _ hEe hE9 hinner hfix T hT hT1 hTE
  · obtain ⟨eL⟩ := heL
    obtain ⟨eB⟩ := Item222Proof.nonempty_lBar_mulEquiv_SL3 hn he eL
    exact autElliptic_of_SL3 hNF3 hpair hA27 hn he eB hE9 hfix hT hTE
  · obtain ⟨eL⟩ := heL
    have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
    exact hU5 (lBar L)
      ⟨(mulEquiv_lBar_of_theta_eq_bot (inSubgroup_theta_eq_bot_of_mulEquiv hLp eL)).symm.trans eL⟩
      _ hEe hE9 hinner hfix T hT hT1 hTE
  · obtain ⟨eB⟩ := heB
    exact autElliptic_of_SL3 hNF3 hpair hA27 (by norm_num) even_two eB hE9 hfix hT hTE

theorem item224Elliptic_of_res6 (h221 : Item221) (h222 : Item222) (h213 : Item213)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (hSp4 : KS224Sp4) (hU4 : KS224U4)
    (hU5 : KS224U5) (hNF3 : Item211NoFieldThree) : Item224Elliptic :=
  item224Elliptic_of_torusElliptic h222 h213 h45
    (item224TorusElliptic_of_res6 h221 h222 h213 h45 h66 hSp4 hU4 hU5 hNF3)

theorem item224_of_res6 (h310 : CFSG.RankThree.GF2n.Item3_10_small) (h612 : Item612Sec21)
    (h221 : Item221) (h222 : Item222) (h213 : Item213) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hSp4 : KS224Sp4) (hU4 : KS224U4) (hU5 : KS224U5)
    (hNF3 : Item211NoFieldThree) : Item224 :=
  item224_of h310 h612 (item224Elliptic_of_res6 h221 h222 h213 h45 h66 hSp4 hU4 hU5 hNF3)

end Certs

end CFSG.RankThree.PartTwo.Sec21
