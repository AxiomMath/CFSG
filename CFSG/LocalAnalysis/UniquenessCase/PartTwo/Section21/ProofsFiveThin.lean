module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteenRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveOrbit
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
import CFSG.LocalAnalysis.UniquenessCase.UC6M591Da
import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoOrbit
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.GroupTheory.SquarefreeOrder
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.GroupTheory
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem center_bar2_eq_bot_of_isCyclic_sylow {M L : Subgroup G} (hL : L ∈ calC M)
    (hcyc : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ P : Sylow p (Bar2 L), IsCyclic ↥(P : Subgroup (Bar2 L))) :
    Subgroup.center (Bar2 L) = ⊥ := by
  classical
  have hZodd : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    intro p hp hp2
    haveI : Fact p.Prime := ⟨hp⟩
    exact CFSG.LocalAnalysis.UniquenessCase.UCK.M591D.not_dvd_card_center
      hL.2.2.1 (hcyc p hp hp2)
  by_contra hZ
  have hcardne : Nat.card (Subgroup.center (Bar2 L)) ≠ 1 := fun h1 =>
    hZ (Subgroup.eq_bot_of_card_eq _ h1)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcardne
  have hp2 : p = 2 := by
    by_contra hne
    exact hZodd p hp hne hpdvd
  have h2dvd : 2 ∣ Nat.card (Subgroup.center (Bar2 L)) := hp2 ▸ hpdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.center (Bar2 L)) 2 h2dvd
  let w : Bar2 L := (z : Subgroup.center (Bar2 L))
  have hwZ : w ∈ Subgroup.center (Bar2 L) := z.2
  have hword : orderOf w = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hz
  have hwne : w ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hword
    omega
  have hwP : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hword, pow_one])
  have hnorm : (Subgroup.zpowers w).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hwZ)
  have hle : Subgroup.zpowers w ≤ CFSG.pCore 2 (Bar2 L) :=
    CFSG.LieType.BorelTits.le_pCore 2 hnorm hwP
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pCore_bar_eq_bot L] at hle
  exact hwne (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers w)))

theorem bar2_isSimpleGroup_of_isCyclic_sylow {M L : Subgroup G} (hL : L ∈ calC M)
    (hcyc : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ P : Sylow p (Bar2 L), IsCyclic ↥(P : Subgroup (Bar2 L))) :
    IsSimpleGroup (Bar2 L) :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident.isSimpleGroup_of_isQuasisimple
    hL.2.2 (center_bar2_eq_bot_of_isCyclic_sylow hL hcyc)

theorem bar2_shape_of_isCyclic_sylow (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hKThin : KThinSimple)
    (hcyc : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ P : Sylow p (Bar2 L), IsCyclic ↥(P : Subgroup (Bar2 L))) :
    (∃ n : ℕ, IsL2 (Bar2 L) n) ∨ (∃ n : ℕ, IsSz (Bar2 L) n) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd (Bar2 L) q) ∨ IsJ1 (Bar2 L) := by
  haveI hsimple : IsSimpleGroup (Bar2 L) :=
    bar2_isSimpleGroup_of_isCyclic_sylow hL hcyc
  have hK : CFSG.IsKGroup (Bar2 L) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_isKGroup_bar D
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_le_of_mem_calC hL)
  have hperf : Group.IsPerfect (Bar2 L) := ⟨hL.2.2.1⟩
  have hnc : ¬ IsMulCommutative (Bar2 L) :=
    Group.IsPerfect.not_isMulCommutative (Bar2 L)
  have hnab : ∃ x y : Bar2 L, x * y ≠ y * x := by
    simpa only [isMulCommutative_iff, not_forall] using hnc
  exact hKThin (Bar2 L) hK hsimple hnab hcyc

private theorem mem_calC_of_le_of_normalizer {M L X : Subgroup G} (hL : L ∈ calC M)
    (hLX : L ≤ X) (hXN : X ≤ Subgroup.normalizer (L : Set G)) : L ∈ calC X :=
  ⟨CFSG.Quasithin.A3.subnormal_of_normal hLX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 hXN),
    hL.2.1, hL.2.2⟩

private theorem exists_elemAbelian_subgroupOf_of_dvd {X L : Subgroup G} {p : ℕ}
    (hLX : L ≤ X) (hp : p.Prime) (hdvd : p ∣ Nat.card (Bar2 L)) :
    ∃ E : Subgroup ↥X, E ≤ L.subgroupOf X ∧ IsElemAbelian p E ∧ Nat.card E = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvdL : p ∣ Nat.card ↥L :=
    hdvd.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) p hdvdL
  let y : ↥X := ⟨(x : G), hLX x.2⟩
  refine ⟨Subgroup.zpowers y, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_subgroupOf.mpr x.2
  · exact isElemAbelian_of_card_prime hp (by
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe y]
      change orderOf (x : G) = p
      rw [Subgroup.orderOf_coe, hx])
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe y]
    change orderOf (x : G) = p
    rw [Subgroup.orderOf_coe, hx]

private theorem family_data_of_three {M L₁ L₂ L₃ : Subgroup G}
    (h₁ : L₁ ∈ calC M) (h₂ : L₂ ∈ calC M) (h₃ : L₃ ∈ calC M)
    (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) :
    ∃ Lf : Fin 3 → Subgroup G,
      (∀ i, Lf i ∈ calC (L₁ ⊔ L₂ ⊔ L₃)) ∧
      Function.Injective (fun i => (Lf i).subgroupOf (L₁ ⊔ L₂ ⊔ L₃)) ∧
      (∀ i, Lf i ∈ ({L₁, L₂, L₃} : Set (Subgroup G))) := by
  classical
  set X : Subgroup G := L₁ ⊔ L₂ ⊔ L₃ with hX
  let Lf : Fin 3 → Subgroup G :=
    fun i => if (i : ℕ) = 0 then L₁ else if (i : ℕ) = 1 then L₂ else L₃
  have hLfM : ∀ i, Lf i ∈ calC M := by
    intro i
    fin_cases i
    · simpa [Lf] using h₁
    · simpa [Lf] using h₂
    · simpa [Lf] using h₃
  have hLf_le : ∀ i, Lf i ≤ X := by
    intro i
    fin_cases i
    · rw [hX]; exact le_sup_left.trans le_sup_left
    · rw [hX]; exact le_sup_right.trans le_sup_left
    · rw [hX]; exact le_sup_right
  have hLf_norm : ∀ i, X ≤ Subgroup.normalizer (Lf i : Set G) := by
    intro i
    fin_cases i
    · rw [hX]
      exact sup_le (sup_le Subgroup.le_normalizer (calC_le_normalizer_of_ne h₁ h₂ h12))
        (calC_le_normalizer_of_ne h₁ h₃ h13)
    · rw [hX]
      exact sup_le (sup_le (calC_le_normalizer_of_ne h₂ h₁ h12.symm) Subgroup.le_normalizer)
        (calC_le_normalizer_of_ne h₂ h₃ h23)
    · rw [hX]
      exact sup_le (sup_le (calC_le_normalizer_of_ne h₃ h₁ h13.symm)
        (calC_le_normalizer_of_ne h₃ h₂ h23.symm)) Subgroup.le_normalizer
  have hcal : ∀ i, Lf i ∈ calC X :=
    fun i => mem_calC_of_le_of_normalizer (hLfM i) (hLf_le i) (hLf_norm i)
  have hLf_inj : Function.Injective Lf := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Lf]
  have hinj : Function.Injective (fun i => (Lf i).subgroupOf X) := by
    intro i j hij
    apply hLf_inj
    have h := (Subgroup.subgroupOf_inj (K := X)).1 hij
    rwa [inf_eq_left.mpr (hLf_le i), inf_eq_left.mpr (hLf_le j)] at h
  have hLf_set : ∀ i, Lf i ∈ ({L₁, L₂, L₃} : Set (Subgroup G)) := by
    intro i
    fin_cases i <;> simp [Lf]
  exact ⟨Lf, hcal, hinj, hLf_set⟩

private theorem exists_elemAbelian_card_pow_three_of_family {X : Subgroup G}
    {Lf : Fin 3 → Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcal : ∀ i, Lf i ∈ calC X)
    (hinj : Function.Injective (fun i => (Lf i).subgroupOf X))
    (hdvd : ∀ i, p ∣ Nat.card (Bar2 (Lf i)) ∧
      ¬ p ∣ Nat.card (Subgroup.center (Bar2 (Lf i)))) :
    ∃ W : Subgroup ↥X, IsElemAbelian p W ∧ Nat.card W = p ^ 3 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let A : Fin 3 → Subgroup ↥X := fun i => (Lf i).subgroupOf X
  have hex : ∀ i, ∃ E : Subgroup ↥X, E ≤ A i ∧ IsElemAbelian p E ∧ Nat.card E = p :=
    fun i => exists_elemAbelian_subgroupOf_of_dvd
      (CFSG.Quasithin.A3.subnormal_le (hcal i).1) hp (hdvd i).1
  choose E hE using hex
  have hEA : ∀ i, E i ≤ A i := fun i => (hE i).1
  have hEel : ∀ i, IsElemAbelian p (E i) := fun i => (hE i).2.1
  have hEc : ∀ i, Nat.card (E i) = p ^ ((fun _ : Fin 3 => 1) i) :=
    fun i => by simpa using (hE i).2.2
  have hZ : ∀ i, ¬ p ∣ Nat.card
      (Subgroup.center (↥(A i) ⧸ CFSG.pCore 2 ↥(A i))) := by
    intro i
    rw [(CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_subgroupOf (hcal i)).2.2.2]
    exact (hdvd i).2
  obtain ⟨W, hWel, hWcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S898.rank_sum_of_family
      (Y := ↥X) (ι := Fin 3) (A := A) (E := E) (q := p) (a := fun _ => 1) hp hp2
      (fun i => (CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_subgroupOf (hcal i)).1)
      (fun i => (CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_subgroupOf (hcal i)).2.1)
      (fun i => (CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_subgroupOf (hcal i)).2.2.1)
      hinj hZ hEA hEel hEc Finset.univ
  refine ⟨W, hWel, ?_⟩
  simpa using hWcard

theorem two_lt_pRank_sup_sup_of_dvd {M L₁ L₂ L₃ : Subgroup G}
    (h₁ : L₁ ∈ calC M) (h₂ : L₂ ∈ calC M) (h₃ : L₃ ∈ calC M)
    (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : ∀ K ∈ ({L₁, L₂, L₃} : Set (Subgroup G)),
      p ∣ Nat.card (Bar2 K) ∧ ¬ p ∣ Nat.card (Subgroup.center (Bar2 K))) :
    2 < CFSG.Open.pRank p (L₁ ⊔ L₂ ⊔ L₃ : Subgroup G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let X : Subgroup G := L₁ ⊔ L₂ ⊔ L₃
  obtain ⟨Lf, hcal, hinj, hLf_set⟩ := family_data_of_three h₁ h₂ h₃ h12 h13 h23
  have hdvdLf : ∀ i, p ∣ Nat.card (Bar2 (Lf i)) ∧
      ¬ p ∣ Nat.card (Subgroup.center (Bar2 (Lf i))) :=
    fun i => hdvd (Lf i) (hLf_set i)
  obtain ⟨W, hWel, hWcard⟩ :=
    exists_elemAbelian_card_pow_three_of_family (X := X) hp hp2 hcal hinj hdvdLf
  have hcardW' : Nat.card (W.map X.subtype) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, hWcard]
  have hle := CFSG.LocalAnalysis.UniquenessCase.UC6S846.le_pRank' hp
    (H := X) (E := W.map X.subtype) (Subgroup.map_subtype_le W)
    (CFSG.Open.IsElemAbelian.map hWel X.subtype) hcardW'
  have hle' : 3 ≤ CFSG.Open.pRank p (L₁ ⊔ L₂ ⊔ L₃) := hle
  omega

theorem exists_eq_two_pow_of_shape {X : Type} [Group X]
    (h : ∀ n : ℕ, IsL2 X n ∨ IsSz X n → ∀ s : ℕ, Odd s → 1 < s → s ∣ n → False)
    (hshape : (∃ n : ℕ, IsL2 X n) ∨ (∃ n : ℕ, IsSz X n) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd X q) ∨ IsJ1 X) :
    (∃ k : ℕ, 1 ≤ k ∧ IsL2 X (2 ^ k)) ∨
      (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd X q) ∨ IsJ1 X := by
  rcases hshape with ⟨n, hL2⟩ | ⟨n, hSz⟩ | hrest
  · rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd n with ⟨k, hk⟩ |
      ⟨p, hp, hpdvd, hpodd⟩
    · left
      have hn2 : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_two_le_of_isL2 hL2
      have hk1 : 1 ≤ k := by
        by_contra hk0
        have hk0' : k = 0 := by omega
        subst hk0'
        rw [hk, pow_zero] at hn2
        omega
      exact ⟨k, hk1, hk ▸ hL2⟩
    · exact (h n (Or.inl hL2) p hpodd hp.one_lt hpdvd).elim
  · have hodd : Odd n :=
      CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSz
    have hn3 : 3 ≤ n :=
      CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hSz
    exact (h n (Or.inr hSz) n hodd (by omega) (dvd_refl n)).elim
  · rcases hrest with ⟨q, hq, h5, hLq⟩ | hJ
    · exact Or.inr (Or.inl ⟨q, hq, h5, hLq⟩)
    · exact Or.inr (Or.inr hJ)

theorem three_dvd_card_of_shape {X : Type} [Group X]
    (h : (∃ n : ℕ, IsL2 X n) ∨ (∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ IsL2Odd X q) ∨ IsJ1 X) :
    3 ∣ Nat.card X := by
  rcases h with ⟨n, hL2⟩ | ⟨q, hq, h5, hLq⟩ | hJ
  · exact three_dvd_card_of_isL2 hL2
  · exact three_dvd_card_of_isL2Odd (by omega) hLq
  · exact three_dvd_card_of_isJ1 hJ

theorem ncard_conjSetOf_le_two_of_shape {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    (h1930 : H1930 D) (hσ : UC6S846.SigmaStd D) (h211 : S21_1 D Ch)
    (h899 : F08.R899 D) (htor : S21_15Torus D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    {n : ℕ} (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    (hne : conjClosure D.M L ≠ L) {s : ℕ} (hsOdd : Odd s) (hs1 : 1 < s) (hsdvd : s ∣ n) :
    (conjSetOf D.M L).ncard ≤ 2 := by
  classical
  have hs0 : 0 < s := by
    obtain ⟨k, hk⟩ := hsOdd
    omega
  have hs2 : 2 ≤ s := by
    obtain ⟨k, hk⟩ := hsOdd
    omega
  have hpow : 4 ≤ 2 ^ s := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs2
  have hne1 : 2 ^ s - 1 ≠ 1 := by omega
  obtain ⟨r, hrPrime, hrdvd⟩ := Nat.exists_prime_and_dvd hne1
  have hrOdd : Odd r :=
    (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hs0).of_dvd_nat hrdvd
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hrOdd
    omega
  have hnotStrong : ¬ IsStronglyPEmbedded r D.M :=
    s21_15_not_strong_of_torus h211 h1930 c hL hshape hne hsOdd hsdvd hrPrime hrdvd htor
  have hMr : CFSG.Open.pRank r D.M ≤ 3 :=
    s21_15_pRank_le_three hσ hrPrime hr2 hL hnotStrong
  have hk3 : (conjSetOf D.M L).ncard ≤ CFSG.Open.pRank r D.M :=
    s21_15Rank_of D Ch h1930 c L hL n hshape r hrPrime hr2
      (hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsdvd))
  have h3 : (conjSetOf D.M L).ncard ≤ 3 := hk3.trans hMr
  have hne3 : (conjSetOf D.M L).ncard ≠ 3 := by
    intro h3eq
    exact s21_15_ncard_ne_three h899 hL hshape hnotStrong hsOdd hsdvd
      hrPrime hrdvd h3eq
  omega

variable {D : Data G} {Ch : Choice2011 G}

theorem Ctx215.false_of_odd_dvd (e : Ctx215 D Ch) (h1930 : H1930 D)
    (hσ : UC6S846.SigmaStd D) (h211 : S21_1 D Ch) (h899 : F08.R899 D)
    (htor : S21_15Torus D Ch) (h3 : 3 ≤ (conjSetOf D.M e.L).ncard) {n : ℕ}
    (hshape : IsL2 (Bar2 e.L) n ∨ IsSz (Bar2 e.L) n)
    {s : ℕ} (hsOdd : Odd s) (hs1 : 1 < s) (hsdvd : s ∣ n) : False := by
  have hne : conjClosure D.M e.L ≠ e.L := by
    intro hcl
    have h1 : (conjSetOf D.M e.L).ncard = 1 :=
      uc22p2214_ncard_eq_one_of_eq hcl.symm
    omega
  have hle : (conjSetOf D.M e.L).ncard ≤ 2 :=
    ncard_conjSetOf_le_two_of_shape e.toCtx21 h1930 hσ h211 h899 htor e.hL
      hshape hne hsOdd hs1 hsdvd
  omega

private theorem pRank_three_eq_one_of_bar2_mulEquiv {K L : Subgroup G}
    (hL3 : 3 ∣ Nat.card (Bar2 L))
    (hcyc : ∀ P : Sylow 3 (Bar2 L), IsCyclic ↥(P : Subgroup (Bar2 L)))
    (e : Bar2 K ≃* Bar2 L) : CFSG.Open.pRank 3 K = 1 := by
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ≤ 1 :=
    CFSG.AGLEmbedding.pRank_le_one_of_isCyclic_sylow Nat.prime_three
      (default : Sylow 3 (Bar2 L)) (hcyc default)
  have heq : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
  have hK3 : 3 ∣ Nat.card (Bar2 K) := by
    rw [Nat.card_congr e.toEquiv]
    exact hL3
  have hone : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K)) :=
    s13_one_le_pRank_of_dvd (⊤ : Subgroup (Bar2 K)) Nat.prime_three (by simpa using hK3)
  have hbar : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K)) = 1 :=
    le_antisymm (heq.trans_le hle) hone
  have hmod := CFSG.Quasithin.pRank_modO2_eq K Nat.prime_three (by norm_num)
  rw [← hmod]
  exact hbar

private noncomputable def conjugatePower_bar2_mulEquiv (e : Ctx215 D Ch) (i : ℕ) :
    Bar2 (conjugatePower e.a e.L i) ≃* Bar2 e.L :=
  (uc22p20d_bar2_conj (e.a ^ i) e.L).some.symm

private theorem three_dvd_card_conjugatePower (e : Ctx215 D Ch)
    (h3 : 3 ∣ Nat.card (Bar2 e.L)) (i : ℕ) :
    3 ∣ Nat.card (Bar2 (conjugatePower e.a e.L i)) := by
  rw [Nat.card_congr (conjugatePower_bar2_mulEquiv e i).toEquiv]
  exact h3

private theorem not_three_dvd_center_conjugatePower (e : Ctx215 D Ch)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 e.L))) (i : ℕ) :
    ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 (conjugatePower e.a e.L i))) := by
  have hbar : conjugatePower e.a e.L i =
      e.L.map (MulAut.conj (e.a ^ i)).toMonoidHom := rfl
  rw [hbar, CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_center_bar2_map]
  exact hZ

private theorem pRank_three_conjugatePower (e : Ctx215 D Ch)
    (h3 : 3 ∣ Nat.card (Bar2 e.L))
    (hcyc3 : ∀ P : Sylow 3 (Bar2 e.L), IsCyclic ↥(P : Subgroup (Bar2 e.L)))
    (i : ℕ) : CFSG.Open.pRank 3 (conjugatePower e.a e.L i) = 1 :=
  pRank_three_eq_one_of_bar2_mulEquiv h3 hcyc3
    (conjugatePower_bar2_mulEquiv e i)

private theorem conjugatePower_three_injective (e : Ctx215 D Ch)
    (hord3 : orderOf e.a = 3) :
    Function.Injective (fun i : Fin 3 => conjugatePower e.a e.L (i : ℕ)) := by
  intro i j hij
  apply Fin.ext
  have hi : (i : ℕ) ∈ Set.Iio (orderOf e.a) := by
    rw [hord3]; exact i.isLt
  have hj : (j : ℕ) ∈ Set.Iio (orderOf e.a) := by
    rw [hord3]; exact j.isLt
  exact conjugatePower_injOn e.ha_prime e.ha_not_mem hi hj hij

private theorem not_three_dvd_center_of_cyclic_sylow (e : Ctx215 D Ch)
    (hcyc3 : ∀ P : Sylow 3 (Bar2 e.L), IsCyclic ↥(P : Subgroup (Bar2 e.L))) :
    ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 e.L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.LocalAnalysis.UniquenessCase.UCK.M591D.not_dvd_card_center
    e.hL.2.2.1 hcyc3

private theorem exists_hyp81_of_orderOf_three (e : Ctx215 D Ch)
    (hord3 : orderOf e.a = 3) (h3 : 3 ∣ Nat.card (Bar2 e.L))
    (hcyc3 : ∀ P : Sylow 3 (Bar2 e.L), IsCyclic ↥(P : Subgroup (Bar2 e.L))) :
    ∃ L : Subgroup G, F08.Hyp81 D.M L := by
  classical
  have haM : e.a ∈ D.M := e.hBM (e.hle e.haB)
  let Lf : Fin 3 → Subgroup G := fun i => conjugatePower e.a e.L (i : ℕ)
  have hLf_calC : ∀ i, Lf i ∈ calC D.M :=
    fun i => conjugatePower_mem_calC e.hL haM (i : ℕ)
  have hinj : Function.Injective Lf := conjugatePower_three_injective e hord3
  have h01 : Lf 0 ≠ Lf 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
  have h02 : Lf 0 ≠ Lf 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)
  have h12 : Lf 1 ≠ Lf 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)
  have hZ3 := not_three_dvd_center_of_cyclic_sylow e hcyc3
  have hdvd3 : ∀ K ∈ ({Lf 0, Lf 1, Lf 2} : Set (Subgroup G)),
      3 ∣ Nat.card (Bar2 K) ∧ ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 K)) := by
    intro K hK
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
    rcases hK with rfl | rfl | rfl
    · exact ⟨three_dvd_card_conjugatePower e h3 0,
        not_three_dvd_center_conjugatePower e hZ3 0⟩
    · exact ⟨three_dvd_card_conjugatePower e h3 1,
        not_three_dvd_center_conjugatePower e hZ3 1⟩
    · exact ⟨three_dvd_card_conjugatePower e h3 2,
        not_three_dvd_center_conjugatePower e hZ3 2⟩
  have hrank : 2 < CFSG.Open.pRank 3 (Lf 0 ⊔ Lf 1 ⊔ Lf 2) :=
    two_lt_pRank_sup_sup_of_dvd (hLf_calC 0) (hLf_calC 1) (hLf_calC 2) h01 h02 h12
      Nat.prime_three (by norm_num) hdvd3
  have hpRank : ∀ i : Fin 3, CFSG.Open.pRank 3 (Lf i) = 1 :=
    fun i => pRank_three_conjugatePower e h3 hcyc3 (i : ℕ)
  refine ⟨Lf 0 ⊔ Lf 1 ⊔ Lf 2, ?_⟩
  unfold F08.Hyp81
  exact ⟨isSubnormal_sup_sup (hLf_calC 0) (hLf_calC 1) (hLf_calC 2),
    commutator_sup_sup (hLf_calC 0) (hLf_calC 1) (hLf_calC 2), hrank, Or.inr
      ⟨Lf 0, Lf 1, Lf 2, hLf_calC 0, hLf_calC 1, hLf_calC 2,
        hpRank 0, hpRank 1, hpRank 2, le_sup_left.trans le_sup_left,
        le_sup_right.trans le_sup_left, le_sup_right,
        coe_sup_sup_eq_mul (hLf_calC 0) (hLf_calC 1) (hLf_calC 2) h01 h02 h12⟩⟩

theorem Ctx215.orderOf_ne_three (e : Ctx215 D Ch)
    (hNM : ¬ Subgroup.normalizer (Subgroup.zpowers e.a : Set G) ≤ D.M)
    (h82 : F08.R82 D)
    (hcyc3 : ∀ P : Sylow 3 (Bar2 e.L), IsCyclic ↥(P : Subgroup (Bar2 e.L)))
    (h3 : 3 ∣ Nat.card (Bar2 e.L)) : orderOf e.a ≠ 3 := by
  classical
  intro hord3
  obtain ⟨L, hHyp⟩ := exists_hyp81_of_orderOf_three e hord3 h3 hcyc3
  have hstrong : IsStronglyPEmbedded 3 D.M := h82 L hHyp
  have haM : e.a ∈ D.M := e.hBM (e.hle e.haB)
  have hXle : Subgroup.zpowers e.a ≤ D.M := Subgroup.zpowers_le.mpr haM
  have hXne : Subgroup.zpowers e.a ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (Subgroup.zpowers e.a) = 3 := by
      rw [Nat.card_zpowers, hord3]
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hXp : IsPGroup 3 ↥(Subgroup.zpowers e.a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord3, pow_one])
  have hXmem : Subgroup.zpowers e.a ∈ uniqueSet D.M :=
    mem_uniqueSet_of_isStronglyPEmbedded Nat.prime_three hstrong hXle hXne hXp
  exact hNM (normalizer_le_of_mem_uniqueSet D.maxLocal hXmem)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
