module

public import CFSG.RankThree.PartTwo.Sec8.HeringU3nReduce
public import CFSG.RankThree.PartTwo.Sec8.HeringU3nChoice
public import CFSG.RankThree.PartTwo.Sec8.HeringU3nPartner
public import CFSG.RankThree.PartTwo.Sec8.HeringPair84UL
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofRee
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof CFSG.RankThree.PartTwo.Sec8.Item8KFacts3
open CFSG.RankThree.PartTwo.Sec8.HeringU3n

@[expose] def U3nChoice {G : Type} [Group G] (c : G) (L : Subgroup G) (a d : G) (n : ℕ)
    (S : Subgroup G) (s : G) : Prop :=
  S ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
    CFSG.Assembly.IsElemAbelian 2 S ∧ Nat.card S = 2 ^ (3 * n) ∧
    Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
    s ∈ S ∧ s ≠ 1 ∧ Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.centralizer ({s} : Set G)

section Statements

@[expose] def Pair86LocalSetting (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G) (a d : G) (n : ℕ) (S : Subgroup G) (s e : G) (Le : Subgroup G) : Prop :=
  Sec8Std G A c L a d n ∧ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * n) ∧
    U3nChoice c L a d n S s ∧ e ∈ deltaPrime (Subgroup.closure ({c, d} : Set G)) c s ∧
    ((e = c ∧ Le = L) ∨ (PairRel A c L e Le ∧
      ∃ m : ℕ, IsUnitaryTwo (Le ⧸ aschbacherSolvableCore 3 Le) m))

@[expose] def Pair86LocalCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ)
    (S : Subgroup G) (s e : G) (Le : Subgroup G),
    Pair86LocalSetting G A c L a d n S s e Le → rOf e s ≤ Subgroup.centralizer (S : Set G)

@[expose] def Pair86LocalOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ)
    (S : Subgroup G) (s e : G) (Le : Subgroup G),
    Pair86LocalSetting G A c L a d n S s e Le → ∀ x ∈ rOf e s, x ^ 2 = 1 → x ∈ S

end Statements

theorem pair86NonUnitary_of (h310 : Sec6.Item3_10) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hC : Pair86LocalCentral) (hO : Pair86LocalOmega) : Pair86NonUnitary := by
  classical
  intro G _ _ A c L a d n h hLU3
  by_contra hne
  have hall : ∀ b ∈ Subgroup.closure ({c, d} : Set G), b ∉ Subgroup.zpowers c →
      ∀ X : Subgroup G, PairRel A c L b X →
        ∃ m : ℕ, IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m := by
    intro b hb hbc X hrel
    by_contra hno
    push Not at hno
    exact hne ⟨b, hb, hbc, X, hrel, hno⟩
  have hK := kBar_of_unitary h hLU3
  have hR : KF84FieldReeStd := kF84FieldReeStd_holds
  have hO' : KF84OuterL2 :=
    kF84OuterL2_of (inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds)
  have hKB : KF83KBarTwo := kF83KBarTwo_of_even (kF83KBarEven_of hO' hR)
  have hInd : KF83Indep := kF83Indep_of kF83IndepGTwo_holds
  obtain ⟨S, s, hSK, hSe, hScard, hES, hsS, hs1, hEs, htrans⟩ :=
    exists_choice_of_sec8Std h45 hKB h hK
  have hchoice : U3nChoice c L a d n S s := ⟨hSK, hSe, hScard, hES, hsS, hs1, hEs⟩
  have hd := h.data83
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  set B := Subgroup.closure ({c, d} : Set G) with hBdef
  have hBA : B ≤ A := by
    rw [hBdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact h.mem_A
    · exact hd.d_mem
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := Sec5.isElemAbelian_of_le hAe hBA
  have hdΓ := isGammaIndex_of_data83 hd
  have hdc : d ∉ Subgroup.zpowers c := not_mem_zpowers_of_isGammaIndex h.mem_thetaComponentsAt hdΓ
  have hB9 : 9 ≤ Nat.card B :=
    (CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine (h3 c h.mem_A) (h3 d hd.d_mem)
      (hcomm c h.mem_A d hd.d_mem) h.ne_one hdc).ge
  have hBE : B ≤ Subgroup.closure ({c, a, d} : Set G) := by
    rw [hBdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hset : ∀ e ∈ deltaPrime B c s, ∃ Le : Subgroup G,
      Pair86LocalSetting G A c L a d n S s e Le := by
    intro e he
    by_cases hec : e = c
    · exact ⟨L, h, hLU3, hchoice, he, Or.inl ⟨hec, rfl⟩⟩
    · obtain ⟨heB, he1, hV⟩ := he.resolve_left hec
      have hzK : Subgroup.zpowers s ≤ inSubgroup perfectResidual
          (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
        rw [Subgroup.zpowers_le]
        exact hSK hsS
      have hz1 : Subgroup.zpowers s ≠ ⊥ := by
        rwa [Ne, Subgroup.zpowers_eq_bot]
      have hz2 : IsPGroup 2 (Subgroup.zpowers s) := by
        have hs2 : s ^ 2 = 1 := hSe.2 s hsS
        have : orderOf s = 2 := orderOf_eq_prime hs2 hs1
        exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, this, pow_one])
      have hzET : Subgroup.closure ({c, a, d} : Set G) ≤
          Subgroup.normalizer (Subgroup.zpowers s : Set G) := by
        refine hEs.trans ?_
        rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
        exact Subgroup.centralizer_le_normalizer _
      have hQ : qOf s = inSubgroup (CFSG.pCore 2)
          (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup G) : Set G)) := by
        unfold qOf
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have hV' : ⁅inSubgroup (CFSG.pCore 2)
          (Subgroup.centralizer ((Subgroup.zpowers s : Subgroup G) : Set G)) ⊓
          Subgroup.centralizer ({e} : Set G), Subgroup.zpowers c⁆ ≠ ⊥ := by
        rw [← hQ]
        exact hV
      obtain ⟨X, hrel⟩ := exists_partner_of_commutator h45 h48 hKB hInd hO' hR h hzK hz1 hz2
        hzET heB he1 hV'
      obtain ⟨m, hm⟩ := hrel.2.1
      have hecn : e ∉ Subgroup.zpowers c :=
        not_mem_zpowers_of_isGammaIndex h.mem_thetaComponentsAt hm
      obtain ⟨m', hm'⟩ := hall e heB hecn X hrel
      exact ⟨X, h, hLU3, hchoice, he, Or.inr ⟨hrel, m', hm'⟩⟩
  have h863 : ∀ e ∈ deltaPrime B c s, rOf e s ≤ Subgroup.centralizer (S : Set G) := by
    intro e he
    obtain ⟨Le, hLe⟩ := hset e he
    exact hC G A c L a d n S s e Le hLe
  have h864 : ∀ e ∈ deltaPrime B c s, ∀ x ∈ rOf e s, x ^ 2 = 1 → x ∈ S := by
    intro e he
    obtain ⟨Le, hLe⟩ := hset e he
    exact hO G A c L a d n S s e Le hLe
  exact h.not_inCatalog (inCatalog_of_twoLocalData h310 h.toTheoremFourHyp hBe hB9 hSe hsS hs1
    (hBE.trans hES) (hBE.trans hEs) htrans h863 h864)

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
