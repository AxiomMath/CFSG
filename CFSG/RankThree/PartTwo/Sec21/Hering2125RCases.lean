module

public import CFSG.RankThree.PartTwo.Sec21.Hering2125Reduce
public import CFSG.RankThree.PartTwo.Sec21.Hering2125RM
public import CFSG.RankThree.PartTwo.Sec21.Hering2125RComp
public import CFSG.RankThree.PartTwo.Sec21.Hering2125RG2
public import CFSG.RankThree.PartTwo.Sec21.Hering2125RD4
public import CFSG.RankThree.PartTwo.Sec21.Hering2125RL3
public import CFSG.RankThree.PartTwo.Sec21.Item21Res6ProofNoField
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofND
public import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofList
public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofL3

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec11
open CFSG.RankThree.PartTwo.Sec21.Item2119End4Proof CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof
open CFSG.RankThree.PartTwo.Sec21.Item2119EndProof

theorem trialityD4_even {G : Type} [Group G] [Finite G] {e : G} {Y : Subgroup G}
    (h46 : Sec4.Item4_6) (hD4 : KFact1118Triality46)
    (hC4 : SectionFourHyp (Subgroup.centralizer ({e} : Set G))) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hY : Y ∈ thetaComponentsAt 3 e) {q : TauCeti.PrimePower}
    {hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid}
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group) :
    q.p = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({e} : Set G) with hC
  obtain ⟨hYC, hY'⟩ := mem_thetaComponentsIn_iff.mp hY
  have heC : e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have he3' : orderOf (⟨e, heC⟩ : C) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime he3 he1
  have h3 : 3 ∣ Nat.card (Subgroup.center C) := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center C) (mk_mem_center_centralizer e)
    rwa [he3'] at this
  have hL := h46 C hC4 h3 (Y.subgroupOf C) hY'
  set eY := Subgroup.subgroupOfEquivOfLe hYC
  have η := QuotientGroup.congr _ _ eY
    (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eY)
  exact hD4 _ hL q hq ⟨η.trans φ⟩

theorem item2125Cases_of (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6)
    (hD4 : KFact1118Triality46) (h424 : Sec4.Item4_24M) (hN : Sec11.Item1134E27N)
    (hST : Item1134E27ST) : Item2125Cases := by
  intro G _ _ A E U c L d U₀ a X e Y hgen
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE := hgen.cfg
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A := hpair.mem_S.1.2.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have he := hgen.mem_e
  have he3 : e ^ 3 = 1 := h3 e he
  have hecd := hgen.not_mem_cd
  have hed : e ∉ Subgroup.zpowers d := fun h => hecd (Subgroup.mem_sup_right h)
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  have hec : e ∉ Subgroup.zpowers c := fun h => hecd (Subgroup.mem_sup_left h)
  have hce : c ∉ Subgroup.zpowers e := not_mem_zpowers_symm he3 hc1 hec
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  obtain ⟨n, hn0, hne, ⟨eL⟩, ⟨eI⟩⟩ := hgen.iso
  have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := hne; omega
  obtain ⟨-, hIq, -⟩ :=
    kf2123TypeTwo G L n hn0 hne ⟨eL⟩ e he3 hgen.type_L d hdL hd3 hE.type_d (hcomm e he d hdA)
  have hG4 := hpair.standing.toTheoremFourHyp
  have hC4 := hG4.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG4 he1)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe he he1 Y hgen.mem_Y
  have hAC : A ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy e he)
  have hEF : partTwoE G = partTwoF G := hpair.side (mem_partTwoE_of_card hpair hcfg.card)
  have hdI : d ∈ Sec11.sec11K L e := by
    have h1 : d ∈ A ⊓ Sec11.sec11K L e := by rw [hgen.inf_I]; exact Subgroup.mem_zpowers d
    exact h1.2
  have hKT : Sec11.IsType424 (lBar (Sec11.sec11K L e)) := Or.inl ⟨n, by omega, ⟨eI⟩⟩
  have hNK : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ Sec11.sec11K L e : Subgroup G) : Set G) := by
    rw [hgen.inf_I]
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact Subgroup.zpow_mem _ (hE.normal_d g hg) k
  have h4 := item424M_at h424 hAe hAmax h27 hEF he he1 hC4 hgen.mem_Y hAY hgen.cent hcA hce hLc
    hgen.le_I hKT hIq hNK
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := hAY hcA
  have hc3 : c ^ 3 = 1 := h3 c hcA
  have hI' : Sec11.sec11K L e ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) :=
    mem_thetaComponentsIn_sec11K_inf' hLc hgen.mem_Y hgen.le_I hIq
  have h5I : 5 ∣ Nat.card (lBar (Sec11.sec11K L e)) := by
    rw [Nat.card_congr eI.toEquiv]
    exact Item21Res6Proof.five_dvd_card_projSL_two hn2 hne
  have h5Y : 5 ∣ Nat.card (lBar Y) := h5I.trans (card_lBar_dvd_card_lBar hgen.le_I)
  have hbar : ∀ (X : Type) [Group X], (Sec11.sec11YA e Y A ≃* Multiplicative (ZMod 3) × X) →
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) := fun X _ ε =>
    Item1116Proof.nonempty_thetaQuot_equiv_commutator hgen.mem_Y hAC hAY hcomm ε
  have hperf : ∀ (X : Type) [Group X], Group.IsPerfect X →
      (Sec11.sec11YA e Y A ≃* Multiplicative (ZMod 3) × X) →
        Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* X) := by
    intro X _ hX ε
    obtain ⟨φ⟩ := hbar X ε
    exact ⟨φ.trans ((MulEquiv.subgroupCongr (Group.isPerfect_def.mp hX)).trans
      Subgroup.topEquiv)⟩
  rcases h4 with ⟨hfield, -⟩ | ⟨hG2D4, -⟩ | ⟨hL3, -⟩ | ⟨-, ⟨eK⟩, -⟩
  ·
    exfalso
    have hYs : Y ∈ lStarAt A e := ⟨hgen.mem_lStar, hgen.mem_Y⟩
    have hsc : Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
        (Subgroup.zpowers e : Set G) := by
      rw [Sec13.sectionCentralizer_eq_inf hAY, hgen.cent]
    have hL8 : ¬ Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSL 2 (GaloisField 2 3)) :=
      fun h => Item21Res6Proof.not_five_dvd_card (X := lBar Y) (Or.inl h) h5Y
    have hU8 : ¬ Sec4.IsSLThreePiAt (Y ⧸ aschbacherSolvableCore 3 Y) 8 :=
      fun h => Item21Res6Proof.not_five_dvd_card (X := lBar Y) (Or.inr h) h5Y
    by_cases hAT : A ∈ partTwoT G
    · exact (hST G A e Y hpair.standing hpair.mem_S hAT h27 he he1 hYs hsc
        (Or.inr (Or.inr ⟨hL8, hU8⟩)) hEF c hcA).1 hfield
    · exact (hN G A e Y hpair.standing hpair.mem_S.1 hAT h27 he he1 hYs hsc hL8 hU8
        (fun _ => hEF) c hcA).1 hfield
  ·
    rcases hG2D4 with ⟨q, hq, ⟨ε⟩⟩ | ⟨q, hq, ⟨ε⟩⟩
    · obtain ⟨φ⟩ := hperf _ (SetUp1118Proof.isPerfect_lie_G2 q hq) ε
      rcases g2_cases hcN hc3 hI' hn0 hne ⟨eI⟩ ⟨q, hq, ⟨φ⟩⟩ with
        ⟨hin, K, _, _, hK, ⟨eAd⟩⟩ | hSL
      · refine Or.inr (Or.inl ⟨hin, n, hn0, hne, ⟨Nat.prime_two, by omega, rfl, ?_⟩,
          K, inferInstance, inferInstance, hK, ⟨eAd⟩⟩)
        calc 3 ≤ 4 := by norm_num
          _ = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      · exact Or.inr (Or.inr (Or.inr hSL))
    · obtain ⟨φ⟩ := hperf _ (SetUp1118Proof.isPerfect_lie_trialityD4 q hq) ε
      have hq2 : q.p = 2 := trialityD4_even h46 hD4 hC4 he1 he3 hgen.mem_Y φ
      obtain ⟨hin, m, hm0, hmev, hmod⟩ := d4_cases hcN hc3 hI' hn0 hne ⟨eI⟩ ⟨q, hq, hq2, ⟨φ⟩⟩
      exact Or.inr (Or.inr (Or.inl ⟨hin, m, hm0, hmev, hmod⟩))
  ·
    have hY3 := KS11LieProof.isLThreePi_of_sec11YA hgen.mem_Y hAC hAY hcomm hL3
    rcases l3_cases hcN hc3 hI' hn0 hne ⟨eI⟩ hY3 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  ·
    exfalso
    have h168 : Nat.card (projSL 3 (GaloisField 2 1)) = 168 := by
      rw [Sec8.Item8ModelProof.card_projSL_three_galois le_rfl]
      decide
    rw [Nat.card_congr eK.toEquiv, h168] at h5I
    norm_num at h5I

end CFSG.RankThree.PartTwo.Sec21.Hering2125
