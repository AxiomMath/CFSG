module

public import CFSG.Quasithin.H13.A6S13825m
public import CFSG.Quasithin.EmptyFaithful.SBd8FlagNine
public import CFSG.Quasithin.EmptyFaithful.SBd8NS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.ClassicalGroups
public import CFSG.Fischer.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL4L5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSL
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F1Weak
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.SBd8Trio
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13.A6.L13825

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.SBd8.Flag
  CFSG.QuasithinUnique.Vol2Native.L239.L52

theorem dvd_card_of_isPGroup_ker {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (ψ : X →* Y) (hker : IsPGroup 2 ψ.ker) {q : ℕ} (hq : Nat.Coprime q 2)
    (hdvd : q ∣ Nat.card X) : q ∣ Nat.card Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card X = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Subgroup.card_mul_index ψ.ker, Subgroup.index_ker]
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  rw [h1, hk] at hdvd
  have hc : Nat.Coprime q (2 ^ k) := Nat.Coprime.pow_right _ hq
  exact (hc.dvd_of_dvd_mul_left hdvd).trans (Subgroup.card_subgroup_dvd_card ψ.range)

variable {n : ℕ}

theorem isPGroup_unitriangular (hn : 1 ≤ n) : IsPGroup 2 ↥(unitriangular n (ZMod 2)) :=
  (CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (K := ZMod 2) hn).2.1

@[expose] def IsMaxBlock (n : ℕ) (C : Set ℕ) (a m : ℕ) : Prop :=
  a + m ≤ n ∧ (a = 0 ∨ a ∈ C) ∧ (a + m = n ∨ a + m ∈ C) ∧ ∀ c ∈ C, ¬ (a < c ∧ c < a + m)

theorem mem_unitriangular_of_big_blocks {C : Set ℕ} {g : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ flagStabilizer n (ZMod 2) C)
    (hbig : ∀ a m (h : a + m ≤ n), IsMaxBlock n C a m → 2 ≤ m →
      blkAt a m h (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1) :
    g ∈ unitriangular n (ZMod 2) := by
  refine mem_unitriangular_of_blocks hg fun a m h ha hb hno => ?_
  rcases (by omega : m = 0 ∨ m = 1 ∨ 2 ≤ m) with rfl | rfl | hm
  · ext i
    exact Fin.elim0 i
  · exact blkAt_one_eq_one (Nat.card_zmod 2) _ a h (blockLeft_of_cut 1 ha)
      (blockRight_of_cut hb) ⟨g, hg⟩
  · exact hbig a m h ⟨h, ha, hb, hno⟩ hm

@[expose] noncomputable def blkQ (C : Set ℕ) {a m : ℕ} (hB : IsMaxBlock n C a m) :
    ↥(flagStabilizer n (ZMod 2) C) →* SpecialLinearGroup (Fin m) (ZMod 2) :=
  blkSLTwo (Nat.card_zmod 2) _ a m hB.1 (blockLeft_of_cut m hB.2.1) (blockRight_of_cut hB.2.2.1)

theorem blkQ_coe (C : Set ℕ) {a m : ℕ} (hB : IsMaxBlock n C a m)
    (g : ↥(flagStabilizer n (ZMod 2) C)) :
    ((blkQ C hB g : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      blkAt a m hB.1 ((g : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) := rfl

theorem blkAt_eq_one_of_blkQ {C : Set ℕ} {a m : ℕ} (hB : IsMaxBlock n C a m)
    {g : ↥(flagStabilizer n (ZMod 2) C)} (hg : blkQ C hB g = 1) :
    blkAt a m hB.1 ((g : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  rw [← blkQ_coe C hB g, hg]
  rfl

theorem coprime_dvd_of_one_block (hn : 1 ≤ n) {C : Set ℕ} {a m : ℕ} (hB : IsMaxBlock n C a m)
    (huniq : ∀ a' m', IsMaxBlock n C a' m' → 2 ≤ m' → a' = a ∧ m' = m) {q : ℕ}
    (hq : Nat.Coprime q 2) (hdvd : q ∣ Nat.card ↥(flagStabilizer n (ZMod 2) C)) :
    q ∣ Nat.card (SpecialLinearGroup (Fin m) (ZMod 2)) := by
  refine dvd_card_of_isPGroup_ker (blkQ C hB) ?_ hq hdvd
  intro x
  have hxU : ((x : ↥(flagStabilizer n (ZMod 2) C)) : SpecialLinearGroup (Fin n) (ZMod 2)) ∈
      unitriangular n (ZMod 2) := by
    refine mem_unitriangular_of_big_blocks (x : ↥(flagStabilizer n (ZMod 2) C)).2
      fun a' m' h hB' hm' => ?_
    obtain ⟨rfl, rfl⟩ := huniq a' m' hB' hm'
    exact blkAt_eq_one_of_blkQ hB x.2
  obtain ⟨k, hk⟩ := isPGroup_unitriangular hn ⟨_, hxU⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem coprime_dvd_of_two_blocks (hn : 1 ≤ n) {C : Set ℕ} {a₁ m₁ a₂ m₂ : ℕ}
    (hB₁ : IsMaxBlock n C a₁ m₁) (hB₂ : IsMaxBlock n C a₂ m₂)
    (huniq : ∀ a' m', IsMaxBlock n C a' m' → 2 ≤ m' → (a' = a₁ ∧ m' = m₁) ∨ (a' = a₂ ∧ m' = m₂))
    {q : ℕ} (hq : Nat.Coprime q 2) (hdvd : q ∣ Nat.card ↥(flagStabilizer n (ZMod 2) C)) :
    q ∣ Nat.card (SpecialLinearGroup (Fin m₁) (ZMod 2)) *
      Nat.card (SpecialLinearGroup (Fin m₂) (ZMod 2)) := by
  rw [← Nat.card_prod]
  refine dvd_card_of_isPGroup_ker ((blkQ C hB₁).prod (blkQ C hB₂)) ?_ hq hdvd
  intro x
  have hx := x.2
  rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one] at hx
  have hxU : ((x : ↥(flagStabilizer n (ZMod 2) C)) : SpecialLinearGroup (Fin n) (ZMod 2)) ∈
      unitriangular n (ZMod 2) := by
    refine mem_unitriangular_of_big_blocks (x : ↥(flagStabilizer n (ZMod 2) C)).2
      fun a' m' h hB' hm' => ?_
    rcases huniq a' m' hB' hm' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact blkAt_eq_one_of_blkQ hB₁ hx.1
    · exact blkAt_eq_one_of_blkQ hB₂ hx.2
  obtain ⟨k, hk⟩ := isPGroup_unitriangular hn ⟨_, hxU⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem card_SL_two : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [card_SL_eq (by norm_num), Nat.card_zmod]
  decide

theorem card_SL_three : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [card_SL_eq (by norm_num), Nat.card_zmod]
  decide

@[expose] def minPar (n j : ℕ) : Set ℕ := {i | 1 ≤ i ∧ i < n ∧ i ≠ j}

@[expose] def fullCuts (n : ℕ) : Set ℕ := {i | 1 ≤ i ∧ i < n}

theorem isCuts_minPar (n j : ℕ) : IsCuts n (minPar n j) := fun _ hi => ⟨hi.1, hi.2.1⟩

theorem revCuts_minPar {j : ℕ} (hjn : j < n) : revCuts n (minPar n j) = minPar n (n - j) := by
  ext c
  simp only [mem_revCuts, minPar, Set.mem_ofPred_eq]
  omega

theorem eq_of_minPar_eq {j j' : ℕ} (hj' : 1 ≤ j') (hj'n : j' < n)
    (h : minPar n j = minPar n j') : j = j' := by
  by_contra hne
  have hmem : j' ∈ minPar n j := ⟨hj', hj'n, Ne.symm hne⟩
  rw [h] at hmem
  exact hmem.2.2 rfl

theorem cuts_ext {C J : Set ℕ} (hC : IsCuts n C) (hJ : IsCuts n J)
    (h : ∀ c, 1 ≤ c → c < n → (c ∈ C ↔ c ∈ J)) : C = J := by
  ext c
  constructor
  · intro hc
    exact (h c (hC c hc).1 (hC c hc).2).1 hc
  · intro hc
    exact (h c (hJ c hc).1 (hJ c hc).2).2 hc

theorem not_nine_dvd_minPar {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    ¬ 9 ∣ Nat.card ↥(flagStabilizer n (ZMod 2) (minPar n j)) := by
  intro h9
  have hB : IsMaxBlock n (minPar n j) (j - 1) 2 := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rcases (by omega : j = 1 ∨ 2 ≤ j) with h | h
      · left
        omega
      · exact Or.inr ⟨by omega, by omega, by omega⟩
    · rcases (by omega : j + 1 = n ∨ j + 1 < n) with h | h
      · left
        omega
      · exact Or.inr ⟨by omega, by omega, by omega⟩
    · rintro c ⟨-, -, hcj⟩ ⟨h1, h2⟩
      omega
  have huniq : ∀ a' m', IsMaxBlock n (minPar n j) a' m' → 2 ≤ m' → a' = j - 1 ∧ m' = 2 := by
    rintro a' m' ⟨hle, -, -, hno⟩ hm
    have h1 : a' + 1 = j := by
      by_contra hne
      exact hno (a' + 1) ⟨by omega, by omega, hne⟩ ⟨by omega, by omega⟩
    refine ⟨by omega, ?_⟩
    by_contra hm2
    exact hno (a' + 2) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩
  have h := coprime_dvd_of_one_block (by omega) hB huniq (by norm_num) h9
  rw [card_SL_two] at h
  norm_num at h

theorem flagStabilizer_fullCuts :
    flagStabilizer n (ZMod 2) (fullCuts n) = unitriangular n (ZMod 2) := by
  rw [fullCuts, ← CFSG.Quasithin.SBd8.Flag.upperTriangular_eq_flagStabilizer_full,
    upperTriangular_eq_unitriangular (Nat.card_zmod 2)]

theorem not_three_dvd_full (hn : 1 ≤ n) :
    ¬ 3 ∣ Nat.card ↥(flagStabilizer n (ZMod 2) (fullCuts n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [flagStabilizer_fullCuts]
  intro h3
  obtain ⟨k, hk⟩ := (isPGroup_unitriangular hn).exists_card_eq
  rw [hk] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at this

theorem cuts_three {C : Set ℕ} (hC : IsCuts 3 C)
    (hs : Group.IsSolvable ↥(flagStabilizer 3 (ZMod 2) C))
    (h3 : 3 ∣ Nat.card ↥(flagStabilizer 3 (ZMod 2) C)) : C = {1} ∨ C = {2} := by
  have hmem : ∀ c ∈ C, c = 1 ∨ c = 2 := fun c hc => by
    have := hC c hc
    omega
  have hc1 : IsCuts 3 ({1} : Set ℕ) := fun i hi => by
    rw [Set.mem_singleton_iff.1 hi]
    norm_num
  have hc2 : IsCuts 3 ({2} : Set ℕ) := fun i hi => by
    rw [Set.mem_singleton_iff.1 hi]
    norm_num
  by_cases h1 : 1 ∈ C <;> by_cases h2 : 2 ∈ C
  · exfalso
    have hfull : C = fullCuts 3 := cuts_ext hC (fun i hi => hi) fun c hc hcn => by
      rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl <;> simp [fullCuts, *]
    rw [hfull] at h3
    exact not_three_dvd_full (by norm_num) h3
  · exact Or.inl (cuts_ext hC hc1 fun c hc hcn => by
      rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl <;> simp [*])
  · exact Or.inr (cuts_ext hC hc2 fun c hc hcn => by
      rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl <;> simp [*])
  · exfalso
    refine not_isSolvable_flagStabilizer_of_big (a := 0) (m := 3) le_rfl le_rfl (Or.inl rfl)
      (Or.inl rfl) (fun c hc => ?_) hs
    rcases hmem c hc with rfl | rfl <;> simp_all

local macro "cuts_tac" : tactic =>
  `(tactic| (intro i hi; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega))

theorem shape_four {C : Set ℕ} (hC : IsCuts 4 C) :
    C = fullCuts 4 ∨ (∃ j, 1 ≤ j ∧ j < 4 ∧ C = minPar 4 j) ∨ C = {2} ∨
      ¬ Group.IsSolvable ↥(flagStabilizer 4 (ZMod 2) C) := by
  have hmem : ∀ c ∈ C, c = 1 ∨ c = 2 ∨ c = 3 := fun c hc => by
    have := hC c hc
    omega
  by_cases h1 : 1 ∈ C <;> by_cases h2 : 2 ∈ C <;> by_cases h3 : 3 ∈ C
  · exact Or.inl (cuts_ext hC (fun i hi => hi) fun c hc hcn => by
      interval_cases c <;> simp [fullCuts, h1, h2, h3])
  · exact Or.inr (Or.inl ⟨3, by norm_num, by norm_num, cuts_ext hC (isCuts_minPar 4 3)
      fun c hc hcn => by interval_cases c <;> simp [minPar, h1, h2, h3]⟩)
  · exact Or.inr (Or.inl ⟨2, by norm_num, by norm_num, cuts_ext hC (isCuts_minPar 4 2)
      fun c hc hcn => by interval_cases c <;> simp [minPar, h1, h2, h3]⟩)
  · refine Or.inr (Or.inr (Or.inr (not_isSolvable_flagStabilizer_of_big (a := 1) (m := 3)
      (by norm_num) le_rfl (Or.inr h1) (Or.inl rfl) fun c hc hcb => by
        obtain ⟨hlt, hgt⟩ := hcb
        interval_cases c <;> contradiction)))
  · exact Or.inr (Or.inl ⟨1, by norm_num, by norm_num, cuts_ext hC (isCuts_minPar 4 1)
      fun c hc hcn => by interval_cases c <;> simp [minPar, h1, h2, h3]⟩)
  · exact Or.inr (Or.inr (Or.inl (cuts_ext hC (by cuts_tac) fun c hc hcn => by
      interval_cases c <;> simp [h1, h2, h3])))
  · refine Or.inr (Or.inr (Or.inr (not_isSolvable_flagStabilizer_of_big (a := 0) (m := 3)
      (by norm_num) le_rfl (Or.inl rfl) (Or.inr h3) fun c hc hcb => by
        obtain ⟨hlt, hgt⟩ := hcb
        interval_cases c <;> contradiction)))
  · refine Or.inr (Or.inr (Or.inr (not_isSolvable_flagStabilizer_of_big (a := 0) (m := 4)
      le_rfl (by norm_num) (Or.inl rfl) (Or.inl rfl) fun c hc hcb => by
        obtain ⟨hlt, hgt⟩ := hcb
        interval_cases c <;> contradiction)))

theorem shape_five {C : Set ℕ} (hC : IsCuts 5 C) :
    C = fullCuts 5 ∨ (∃ j, 1 ≤ j ∧ j < 5 ∧ C = minPar 5 j) ∨ C = {1, 3} ∨ C = {2, 3} ∨
      C = {2, 4} ∨ ¬ Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) C) := by
  have hmem : ∀ c ∈ C, c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := fun c hc => by
    have := hC c hc
    omega
  have hmp : ∀ j, 1 ≤ j → j < 5 → (∀ c, 1 ≤ c → c < 5 → (c ∈ C ↔ c ∈ minPar 5 j)) →
      C = fullCuts 5 ∨ (∃ j, 1 ≤ j ∧ j < 5 ∧ C = minPar 5 j) ∨ C = {1, 3} ∨ C = {2, 3} ∨
        C = {2, 4} ∨ ¬ Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) C) := fun j hj hjn h =>
    Or.inr (Or.inl ⟨j, hj, hjn, cuts_ext hC (isCuts_minPar 5 j) h⟩)
  have hbig : ∀ a m, a + m ≤ 5 → 3 ≤ m → (a = 0 ∨ a ∈ C) → (a + m = 5 ∨ a + m ∈ C) →
      (∀ c ∈ C, ¬ (a < c ∧ c < a + m)) →
      C = fullCuts 5 ∨ (∃ j, 1 ≤ j ∧ j < 5 ∧ C = minPar 5 j) ∨ C = {1, 3} ∨ C = {2, 3} ∨
        C = {2, 4} ∨ ¬ Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) C) :=
    fun a m h hm ha hb hno => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (not_isSolvable_flagStabilizer_of_big h hm ha hb hno)))))
  by_cases h1 : 1 ∈ C <;> by_cases h2 : 2 ∈ C <;> by_cases h3 : 3 ∈ C <;> by_cases h4 : 4 ∈ C
  · exact Or.inl (cuts_ext hC (fun i hi => hi) fun c hc hcn => by
      interval_cases c <;> simp [fullCuts, h1, h2, h3, h4])
  · exact hmp 4 (by norm_num) (by norm_num) fun c hc hcn => by
      interval_cases c <;> simp [minPar, h1, h2, h3, h4]
  · exact hmp 3 (by norm_num) (by norm_num) fun c hc hcn => by
      interval_cases c <;> simp [minPar, h1, h2, h3, h4]
  · refine hbig 2 3 le_rfl le_rfl (Or.inr h2) (Or.inl rfl) fun c hc hcb => by
      obtain ⟨hlt, hgt⟩ := hcb
      interval_cases c <;> contradiction
  · exact hmp 2 (by norm_num) (by norm_num) fun c hc hcn => by
      interval_cases c <;> simp [minPar, h1, h2, h3, h4]
  · exact Or.inr (Or.inr (Or.inl (cuts_ext hC (by cuts_tac) fun c hc hcn => by
      interval_cases c <;> simp [h1, h2, h3, h4])))
  · refine hbig 1 3 (by norm_num) le_rfl (Or.inr h1) (Or.inr h4) fun c hc hcb => by
      obtain ⟨hlt, hgt⟩ := hcb
      interval_cases c <;> contradiction
  · refine hbig 1 4 le_rfl (by norm_num) (Or.inr h1) (Or.inl rfl) fun c hc hcb => by
      obtain ⟨hlt, hgt⟩ := hcb
      interval_cases c <;> contradiction
  · exact hmp 1 (by norm_num) (by norm_num) fun c hc hcn => by
      interval_cases c <;> simp [minPar, h1, h2, h3, h4]
  · exact Or.inr (Or.inr (Or.inr (Or.inl (cuts_ext hC (by cuts_tac) fun c hc hcn => by
      interval_cases c <;> simp [h1, h2, h3, h4]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (cuts_ext hC (by cuts_tac) fun c hc hcn => by
      interval_cases c <;> simp [h1, h2, h3, h4])))))
  · refine hbig 2 3 le_rfl le_rfl (Or.inr h2) (Or.inl rfl) fun c hc hcb => by
      obtain ⟨hlt, hgt⟩ := hcb
      interval_cases c <;> contradiction
  · refine hbig 0 3 (by norm_num) le_rfl (Or.inl rfl) (Or.inr h3) fun c hc hcb => by
      obtain ⟨hlt, hgt⟩ := hcb
      interval_cases c <;> contradiction
  · refine hbig 0 3 (by norm_num) le_rfl (Or.inl rfl) (Or.inr h3) fun c hc hcb => by
      obtain ⟨hlt, hgt⟩ := hcb
      interval_cases c <;> contradiction
  · refine hbig 0 4 (by norm_num) (by norm_num) (Or.inl rfl) (Or.inr h4) fun c hc hcb => by
      obtain ⟨hlt, hgt⟩ := hcb
      interval_cases c <;> contradiction
  · refine hbig 0 5 le_rfl (by norm_num) (Or.inl rfl) (Or.inl rfl) fun c hc hcb => by
      obtain ⟨hlt, hgt⟩ := hcb
      interval_cases c <;> contradiction

theorem cuts_minPar (hn4 : 4 ≤ n) (hn5 : n ≤ 5) {C : Set ℕ} (hC : IsCuts n C)
    (hs : Group.IsSolvable ↥(flagStabilizer n (ZMod 2) C))
    (h3 : 3 ∣ Nat.card ↥(flagStabilizer n (ZMod 2) C))
    (h9 : ¬ 9 ∣ Nat.card ↥(flagStabilizer n (ZMod 2) C)) :
    ∃ j, 1 ≤ j ∧ j < n ∧ C = minPar n j := by
  rcases (by omega : n = 4 ∨ n = 5) with rfl | rfl
  · rcases shape_four hC with h | h | h | h
    · rw [h] at h3
      exact absurd h3 (not_three_dvd_full (by norm_num))
    · exact h
    · rw [h] at h9
      exact absurd (nine_dvd_card_flagStabilizer (a := 0) (b := 2) le_rfl le_rfl (by norm_num)
        (by simp) (by simp)) h9
    · exact absurd hs h
  · rcases shape_five hC with h | h | h | h | h | h
    · rw [h] at h3
      exact absurd h3 (not_three_dvd_full (by norm_num))
    · exact h
    · rw [h] at h9
      exact absurd (nine_dvd_card_flagStabilizer (a := 1) (b := 3) le_rfl le_rfl le_rfl
        (by simp) (by simp)) h9
    · rw [h] at h9
      exact absurd (nine_dvd_card_flagStabilizer (a := 0) (b := 3) (by norm_num) le_rfl le_rfl
        (by simp) (by simp)) h9
    · rw [h] at h9
      exact absurd (nine_dvd_card_flagStabilizer (a := 0) (b := 2) le_rfl (by norm_num) le_rfl
        (by simp) (by simp)) h9
    · exact absurd hs h

theorem cuts_five_nine {C : Set ℕ} (hC : IsCuts 5 C)
    (hs : Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) C))
    (h9 : 9 ∣ Nat.card ↥(flagStabilizer 5 (ZMod 2) C)) :
    C = {1, 3} ∨ C = {2, 3} ∨ C = {2, 4} := by
  rcases shape_five hC with h | ⟨j, hj, hjn, h⟩ | h | h | h | h
  · rw [h] at h9
    exact absurd ((show 3 ∣ 9 by norm_num).trans h9) (not_three_dvd_full (by norm_num))
  · rw [h] at h9
    exact absurd h9 (not_nine_dvd_minPar hj hjn)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd hs h

theorem false_of_le_one_three {C : Set ℕ} (hC : IsCuts 4 C) (hsub : C ⊆ {1, 3})
    (hs : Group.IsSolvable ↥(flagStabilizer 4 (ZMod 2) C))
    (h9 : 9 ∣ Nat.card ↥(flagStabilizer 4 (ZMod 2) C)) : False := by
  have h2 : (2 : ℕ) ∉ C := fun h => by
    have := hsub h
    simp at this
  rcases shape_four hC with h | ⟨j, hj, hjn, h⟩ | h | h
  · exact h2 (h ▸ (⟨by norm_num, by norm_num⟩ : (2 : ℕ) ∈ fullCuts 4))
  · have hj2 : j = 2 := by
      by_contra hne
      exact h2 (h ▸ (⟨by norm_num, by norm_num, Ne.symm hne⟩ : (2 : ℕ) ∈ minPar 4 j))
    subst hj2
    rw [h] at h9
    exact not_nine_dvd_minPar (by norm_num) (by norm_num) h9
  · exact h2 (h ▸ Set.mem_singleton 2)
  · exact h hs

theorem not_le_normalizer_of_block (hn : 1 ≤ n) {C' : Set ℕ} {a m : ℕ}
    (hB : IsMaxBlock n C' a m) (hm3 : 3 ≤ m) {R : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hRC : R ≤ flagStabilizer n (ZMod 2) C') (hR : Group.IsSolvable ↥R)
    {x : SpecialLinearGroup (Fin n) (ZMod 2)} (hx : x ∈ R ⊔ unitriangular n (ZMod 2))
    (hx3 : x ^ 3 = 1) (hxb : blkAt a m hB.1 (x : Matrix (Fin n) (Fin n) (ZMod 2)) ≠ 1) :
    ¬ flagStabilizer n (ZMod 2) C' ≤
      Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin n) (ZMod 2))) := by
  intro hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := flagStabilizer n (ZMod 2) C' with hQ
  set ψ := blkQ C' hB with hψ
  have hUQ : unitriangular n (ZMod 2) ≤ Q := by
    rw [← upperTriangular_eq_unitriangular (Nat.card_zmod 2)]
    exact upperTriangular_le_flagStabilizer C'
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨z, hz⟩ := bigBlockHom_surjective (K := ZMod 2) (Nat.card_zmod 2) hB.1 hm3 hB.2.1
      hB.2.2.1 hB.2.2.2 y
    refine ⟨⟨(z : SpecialLinearGroup (Fin n) (ZMod 2)), perfectCore_le _ z.2⟩, ?_⟩
    rw [← hz]
    exact Subtype.ext rfl
  have hRn : (R.subgroupOf Q).Normal := ⟨fun r hr g => by
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hN g.2) r).mp hr⟩
  have hRs : Group.IsSolvable ↥(R.subgroupOf Q) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hRC).toMonoidHom) (MulEquiv.injective _)
  have hRs' : Group.IsSolvable ↥((R.subgroupOf Q).map ψ) :=
    Group.isSolvable_of_surjective (f := ψ.subgroupMap (R.subgroupOf Q))
      (MonoidHom.subgroupMap_surjective ψ _)
  have hbot : (R.subgroupOf Q).map ψ = ⊥ :=
    CFSG.Quasithin.SBd8.normal_solvable_eq_bot_of_simple
      (sl_isSimple_of_card_two (Nat.card_zmod 2) hm3) (not_isSolvable_specialLinearGroup hm3) _
      (hRn.map ψ hsurj) hRs'
  have hxQ : x ∈ Q := sup_le hRC hUQ hx
  have hmem : ψ ⟨x, hxQ⟩ ∈ ((unitriangular n (ZMod 2)).subgroupOf Q).map ψ := by
    have h1 : (⟨x, hxQ⟩ : ↥Q) ∈ (R ⊔ unitriangular n (ZMod 2)).subgroupOf Q := hx
    rw [Subgroup.subgroupOf_sup hRC hUQ] at h1
    have h2 := Subgroup.mem_map_of_mem ψ h1
    rwa [Subgroup.map_sup, hbot, bot_sup_eq] at h2
  have hp : IsPGroup 2 ↥(((unitriangular n (ZMod 2)).subgroupOf Q).map ψ) :=
    ((isPGroup_unitriangular hn).of_equiv (Subgroup.subgroupOfEquivOfLe hUQ).symm).map ψ
  obtain ⟨k, hk⟩ := hp ⟨_, hmem⟩
  have h1 : ψ ⟨x, hxQ⟩ ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : ψ ⟨x, hxQ⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxQ⟩ : ↥Q) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have h3 : ψ ⟨x, hxQ⟩ = 1 := by
    have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one h1)
      (orderOf_dvd_of_pow_eq_one h2))
  exact hxb (blkAt_eq_one_of_blkQ hB h3)

@[expose] def PBShape (n : ℕ) (C : Set ℕ) : Prop :=
  ∃ C' : Set ℕ, flagStabilizer n (ZMod 2) C ≤ flagStabilizer n (ZMod 2) C' ∧
    ¬ Group.IsSolvable ↥(flagStabilizer n (ZMod 2) C') ∧
    ¬ 5 ∣ Nat.card ↥(flagStabilizer n (ZMod 2) C') ∧
    ¬ 27 ∣ Nat.card ↥(flagStabilizer n (ZMod 2) C') ∧
    ∀ R : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)), Group.IsSolvable ↥R →
      R ⊔ unitriangular n (ZMod 2) = flagStabilizer n (ZMod 2) C →
      ¬ flagStabilizer n (ZMod 2) C' ≤
        Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin n) (ZMod 2)))

theorem pbShape_of_one_block (hn : 1 ≤ n) {C C' : Set ℕ} {a a' : ℕ} (hC : IsCuts n C)
    (hC' : IsCuts n C') (hsub : C' ⊆ C) (hB : IsMaxBlock n C' a 3)
    (huniq : ∀ b m', IsMaxBlock n C' b m' → 2 ≤ m' → b = a ∧ m' = 3)
    (hx : triElt n a' ∈ flagStabilizer n (ZMod 2) C) (hx3 : triElt n a' ^ 3 = 1)
    (hxb : blkAt a 3 hB.1 (triElt n a' : Matrix (Fin n) (Fin n) (ZMod 2)) ≠ 1) :
    PBShape n C := by
  have hle : flagStabilizer n (ZMod 2) C ≤ flagStabilizer n (ZMod 2) C' :=
    (flagStabilizer_le_iff hC hC').2 hsub
  refine ⟨C', hle, not_isSolvable_flagStabilizer_of_big hB.1 le_rfl hB.2.1 hB.2.2.1 hB.2.2.2,
    fun h5 => ?_, fun h27 => ?_, fun R hR hRU => ?_⟩
  · have := coprime_dvd_of_one_block hn hB huniq (by norm_num) h5
    rw [card_SL_three] at this
    norm_num at this
  · have := coprime_dvd_of_one_block hn hB huniq (by norm_num) h27
    rw [card_SL_three] at this
    norm_num at this
  · have hRC : R ≤ flagStabilizer n (ZMod 2) C' := (le_sup_left.trans hRU.le).trans hle
    exact not_le_normalizer_of_block hn hB le_rfl hRC hR (by rw [hRU]; exact hx) hx3 hxb

theorem pbShape_of_two_blocks (hn : 1 ≤ n) {C C' : Set ℕ} {a a₂ a' : ℕ} (hC : IsCuts n C)
    (hC' : IsCuts n C') (hsub : C' ⊆ C) (hB : IsMaxBlock n C' a 3) (hB₂ : IsMaxBlock n C' a₂ 2)
    (huniq : ∀ b m', IsMaxBlock n C' b m' → 2 ≤ m' → (b = a ∧ m' = 3) ∨ (b = a₂ ∧ m' = 2))
    (hx : triElt n a' ∈ flagStabilizer n (ZMod 2) C) (hx3 : triElt n a' ^ 3 = 1)
    (hxb : blkAt a 3 hB.1 (triElt n a' : Matrix (Fin n) (Fin n) (ZMod 2)) ≠ 1) :
    PBShape n C := by
  have hle : flagStabilizer n (ZMod 2) C ≤ flagStabilizer n (ZMod 2) C' :=
    (flagStabilizer_le_iff hC hC').2 hsub
  refine ⟨C', hle, not_isSolvable_flagStabilizer_of_big hB.1 le_rfl hB.2.1 hB.2.2.1 hB.2.2.2,
    fun h5 => ?_, fun h27 => ?_, fun R hR hRU => ?_⟩
  · have := coprime_dvd_of_two_blocks hn hB hB₂ huniq (by norm_num) h5
    rw [card_SL_three, card_SL_two] at this
    norm_num at this
  · have := coprime_dvd_of_two_blocks hn hB hB₂ huniq (by norm_num) h27
    rw [card_SL_three, card_SL_two] at this
    norm_num at this
  · have hRC : R ≤ flagStabilizer n (ZMod 2) C' := (le_sup_left.trans hRU.le).trans hle
    exact not_le_normalizer_of_block hn hB le_rfl hRC hR (by rw [hRU]; exact hx) hx3 hxb

local macro "uniq_tac" : tactic =>
  `(tactic| (rintro b m' ⟨hle, hb, he, hno⟩ hm
             simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
               forall_eq] at hb he hno
             omega))

local macro "block_tac" : tactic =>
  `(tactic| (refine ⟨by norm_num, by simp, by simp, ?_⟩
             intro c hc
             simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
             omega))

theorem pbShape_minPar (hn4 : 4 ≤ n) (hn5 : n ≤ 5) {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    PBShape n (minPar n j) := by
  have hC := isCuts_minPar n j
  rcases (by omega : n = 4 ∨ n = 5) with rfl | rfl
  · interval_cases j
    · refine pbShape_of_one_block (C' := {3}) (a := 0) (a' := 0) (by norm_num) hC (by cuts_tac)
        (by intro c hc; simp only [Set.mem_singleton_iff] at hc; subst hc; simp [minPar])
        (by block_tac) (by uniq_tac) (triElt_mem (by norm_num) (by simp [minPar])) (by decide)
        (by decide)
    · refine pbShape_of_one_block (C' := {3}) (a := 0) (a' := 1) (by norm_num) hC (by cuts_tac)
        (by intro c hc; simp only [Set.mem_singleton_iff] at hc; subst hc; simp [minPar])
        (by block_tac) (by uniq_tac) (triElt_mem (by norm_num) (by simp [minPar])) (by decide)
        (by decide)
    · refine pbShape_of_one_block (C' := {1}) (a := 1) (a' := 2) (by norm_num) hC (by cuts_tac)
        (by intro c hc; simp only [Set.mem_singleton_iff] at hc; subst hc; simp [minPar])
        (by block_tac) (by uniq_tac) (triElt_mem (by norm_num) (by simp [minPar])) (by decide)
        (by decide)
  · interval_cases j
    · refine pbShape_of_one_block (C' := {3, 4}) (a := 0) (a' := 0) (by norm_num) hC
        (by cuts_tac)
        (by intro c hc; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with rfl | rfl <;> simp [minPar])
        (by block_tac) (by uniq_tac) (triElt_mem (by norm_num) (by simp [minPar])) (by decide)
        (by decide)
    · refine pbShape_of_one_block (C' := {3, 4}) (a := 0) (a' := 1) (by norm_num) hC
        (by cuts_tac)
        (by intro c hc; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with rfl | rfl <;> simp [minPar])
        (by block_tac) (by uniq_tac) (triElt_mem (by norm_num) (by simp [minPar])) (by decide)
        (by decide)
    · refine pbShape_of_one_block (C' := {1, 4}) (a := 1) (a' := 2) (by norm_num) hC
        (by cuts_tac)
        (by intro c hc; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with rfl | rfl <;> simp [minPar])
        (by block_tac) (by uniq_tac) (triElt_mem (by norm_num) (by simp [minPar])) (by decide)
        (by decide)
    · refine pbShape_of_one_block (C' := {1, 2}) (a := 2) (a' := 3) (by norm_num) hC
        (by cuts_tac)
        (by intro c hc; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
            rcases hc with rfl | rfl <;> simp [minPar])
        (by block_tac) (by uniq_tac) (triElt_mem (by norm_num) (by simp [minPar])) (by decide)
        (by decide)

theorem pbShape_five_nine {C : Set ℕ} (hC : IsCuts 5 C)
    (h : C = {1, 3} ∨ C = {2, 3} ∨ C = {2, 4}) : PBShape 5 C := by
  rcases h with rfl | rfl | rfl
  · refine pbShape_of_two_blocks (C' := {3}) (a := 0) (a₂ := 3) (a' := 1) (by norm_num) hC
      (by cuts_tac) (by simp) (by block_tac) (by block_tac) (by uniq_tac)
      (triElt_mem (by norm_num) (by simp)) (by decide) (by decide)
  · refine pbShape_of_two_blocks (C' := {3}) (a := 0) (a₂ := 3) (a' := 0) (by norm_num) hC
      (by cuts_tac) (by simp) (by block_tac) (by block_tac) (by uniq_tac)
      (triElt_mem (by norm_num) (by simp)) (by decide) (by decide)
  · refine pbShape_of_two_blocks (C' := {2}) (a := 2) (a₂ := 0) (a' := 2) (by norm_num) hC
      (by cuts_tac) (by simp) (by block_tac) (by block_tac) (by uniq_tac)
      (triElt_mem (by norm_num) (by simp)) (by decide) (by decide)

end CFSG.Quasithin.H13.A6.L13825
