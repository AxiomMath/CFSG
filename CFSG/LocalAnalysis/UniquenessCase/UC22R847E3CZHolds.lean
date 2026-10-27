module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3CZ
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3CZL34
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3B1
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3L34
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z9
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z7
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z8
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Good
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Inv
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.RankThree.PartTwo.Sec3.ThreeGroupCentralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4 StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedSolvableQ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

theorem R847E3.normalizer_le_of_thin_three_of_ne_bot
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G)
    (hp : 3 ∈ (dataOfSetup hS S).sig) {Y : Subgroup G} (hY : Y ∈ calC S.M)
    (hYN : (Y.subgroupOf S.M).Normal) (hthin : F08.Thin8 Y) {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q)
    (hCZ : pCoreOf 2 S.M ⊓ centralizer (X : Set G) ≠ ⊥) :
    normalizer (X : Set G) ≤ S.M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal 3 Nat.prime_three
    (by norm_num) hsp (PartTwo.Three.normalizer_le_of_mem_sigmaOf S hp)
  have hp3 : k.p = 3 := rfl
  have hK : CFSG.Open.IsKGroup ↥S.M := hS.kProper.isKGroup S.M hsp.1
  have hYM : Y ≤ S.M := hY.1.le
  have hMN : S.M ≤ normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).1 hYN
  have hOp := UC6.opRes_eq_of_stronglyEmbedded_uc6 hS.simple hS.nonab Nat.prime_three hsp
  have h3 := hSg.three_le 3 hp
  have h75 : Sec7Core4.Step75 k := k.step75_of_stronglyEmbeddedThree hp3 hK3
  have h76C : Sec7Core4.Step76C k := k.step76C_of_stronglyEmbeddedThree hp3 hK3
  suffices h : ∀ q : ℕ, ∀ X : Subgroup G, X ≤ Y → q.Prime → 5 ≤ q → Nat.card X = q →
      pCoreOf 2 S.M ⊓ centralizer (X : Set G) ≠ ⊥ → normalizer (X : Set G) ≤ S.M from
    h q X hXY hq hq5 hXc hCZ
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro X hXY hq hq5 hXc hCZ
  have hq2 : q ≠ 2 := by omega
  have hqp : q ≠ 3 := by omega
  have hXq : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  obtain ⟨B₁, hB₁M, hB₁, hB₁c, hB₁X, hB₁Y⟩ := R847E3.exists_B₁_of_thin hThin hCyc hK hY hMN
    hthin Nat.prime_three (by norm_num) hOp h3 hXY hq hq2 hXq
  rcases uc22ine229_normalizer_le_or_card_le_two k hp3 hK3 hX1 (hXY.trans hYM) hB₁M hB₁ hB₁c
    hB₁X with h | hQ
  · exact h
  by_contra hnot
  have hB₁N : B₁ ≤ normalizer (X : Set G) :=
    hB₁X.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hH := k.config_normalizer hX1 (hXY.trans hYM)
    (CFSG.SectionRank.le_pRank k.prime.one_lt (le_inf hB₁M hB₁N) hB₁ hB₁c) hnot
  have hW := uc22ine229_le_centralizer3 hB₁M hQ hB₁ hB₁X hB₁Y
  obtain ⟨s, hsZ, hs1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hCZ
  have hsN : s ∈ normalizer (X : Set G) := Subgroup.centralizer_le_normalizer _ hsZ.2
  have hsQ : s ∈ pCoreOf 2 S.M ⊓ normalizer (X : Set G) := ⟨hsZ.1, hsN⟩
  have hs2 : s ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    by_contra h
    have h' : s ^ 2 = s := congrArg Subtype.val (uc22ine229_eq_of_ne_one hQ
      (c := ⟨s ^ 2, Subgroup.pow_mem _ hsQ 2⟩) (d := ⟨s, hsQ⟩)
      (fun h1 => h (congrArg Subtype.val h1)) fun h1 => hs1 (congrArg Subtype.val h1))
    rw [pow_two, mul_eq_left] at h'
    exact hs1 h'
  have hsc : ∀ m ∈ S.M, m ∈ normalizer (X : Set G) → Commute m s := fun m hmM hmN =>
    (CFSG.RankThree.PartTwo.Sec3.commute_of_card_le_two hQ
      (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 S.M hmM, Subgroup.le_normalizer hmN⟩)
      hsQ).symm
  obtain ⟨w, ⟨hwY, hwN⟩, hwC⟩ :=
    uc22ine229_exists_not_mem_centralizer_of_thin hY hthin hq hq2 hXY hXc
  obtain ⟨ℓ, hℓ, hℓq, u, hu, ⟨e, he⟩, huC⟩ := uc22ine229_exists_prime_part hq hXc hwN hwC
  have huYN : u ∈ Y ⊓ normalizer (X : Set G) :=
    Subgroup.zpowers_le.2 (show w ∈ Y ⊓ normalizer (X : Set G) from ⟨hwY, hwN⟩) hu
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact huC (Subgroup.one_mem _)
  rcases eq_or_ne ℓ 2 with rfl | hℓ2
  ·
    rcases R847E3.normalizer_le_or_l34 hG3 hRee hK3 k hp3 hY hq hXY hXc hB₁M hB₁ hB₁c hB₁X
      hB₁Y (pow_mem huYN _) (uc22ine229_orderOf_pow_eq_prime Nat.prime_two hu1 he) with
      h | ⟨hH', hF⟩
    · exact hnot h
    rcases R847E3.eq_one_or_eq_of_l34 hG3 hRee k hp3 hH' hF hB₁N hB₁ hB₁c huYN.2 hsN ⟨e, he⟩
      ⟨1, hs2⟩ hs1 (hsc u (hYM huYN.1) huYN.2)
      (fun b hb => (Subgroup.mem_centralizer_iff.mp (hW huYN)) b hb)
      (fun b hb => hsc b (hB₁M hb) (hB₁N hb)) with h | h
    · exact hu1 h
    · exact huC (by rw [h]; exact hsZ.2)
  rcases eq_or_ne ℓ 3 with rfl | hℓ3
  ·
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one he)
    exact huC (k.mem_centralizer_of_commute h75 hH (k.goodZ3_of_config hG3 hRee hp3 hH).1
      (uc22ine229_le_pPrimeCore_normalizer k.prime hq hqp hXc) (le_inf hB₁N hB₁M) hB₁ hB₁c hB₁X
      ⟨huYN.2, hYM huYN.1⟩ (IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj, hp3]))
      fun a ha => (Subgroup.mem_centralizer_iff.mp (hW huYN)) a ha)
  have hy := uc22ine229_orderOf_pow_eq_prime hℓ hu1 he
  set y := u ^ (orderOf u / ℓ)
  have hyYN : y ∈ Y ⊓ normalizer (X : Set G) := pow_mem huYN _
  have hℓlt : ℓ < q := by
    have := Nat.le_of_dvd (by have := hq.two_le; omega) hℓq
    have := hq.two_le
    omega
  obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B₁, x ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one B₁ with h | h
    · rw [h, Subgroup.card_bot] at hB₁c
      exact absurd hB₁c (Nat.one_lt_pow (by norm_num) k.prime.one_lt).ne
    · exact h
  obtain ⟨j, hjM, hjy⟩ := k.exists_not_mem_commute_of_prime h75 k.step72L h76C hH
    ⟨hB₁N hxB, hB₁M hxB⟩ ⟨hyYN.2, hYM hyYN.1⟩ (hB₁.isPGroup.to_le (Subgroup.zpowers_le.2 hxB))
    hx1 (by rw [hy]; exact hℓ) (by rw [hy]; exact hℓ2) (by rw [hy]; exact hℓ3)
    ((Subgroup.mem_centralizer_iff.mp (hW hyYN)) x hxB)
  have hcen : ∀ g : G, g * y = y * g →
      g ∈ centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    exact hg
  have hyCZ : pCoreOf 2 S.M ⊓ centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) ≠ ⊥ := by
    intro h
    have hsy : s ∈ pCoreOf 2 S.M ⊓ centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) :=
      ⟨hsZ.1, hcen s (hsc y (hYM hyYN.1) hyYN.2).eq.symm⟩
    rw [h] at hsy
    exact hs1 (Subgroup.mem_bot.1 hsy)
  have hyN := ih ℓ hℓlt (Subgroup.zpowers y) (Subgroup.zpowers_le.2 hyYN.1) hℓ
    (hℓ.five_le_of_ne_two_of_ne_three hℓ2 hℓ3) (by rw [Nat.card_zpowers, hy]) hyCZ
  exact hjM (hyN (Subgroup.centralizer_le_normalizer _ (hcen j hjy)))

theorem r847E3CZRes_dataOfSetup (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G) :
    R847E3CZRes (dataOfSetup hS S) := by
  intro hsig _ Y hY hYN hthin _ X hXY q hq hq5 hXc hCZ
  exact R847E3.normalizer_le_of_thin_three_of_ne_bot hThin hCyc hG3 hRee hK3 hS S
    (by rw [hsig]; exact Set.mem_singleton 3) hY hYN hthin hq hq5 hXY hXc hCZ

theorem r847ThinCZ_dataOfSetup_holds
    (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ) (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hSQ : StronglyEmbeddedSolvableQ) (hK3 : StronglyEmbeddedThree)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hS : Standing G) (S : Setup G) :
    ∀ Y ∈ calC (dataOfSetup hS S).M, F08.Thin8 Y → ∀ X : Subgroup G, X ≤ Y →
      (Nat.card X).Prime → Nat.card X ≠ 2 →
      CFSG.Open.pCoreOf 2 (dataOfSetup hS S).M ⊓ centralizer (X : Set G) ≠ ⊥ →
      normalizer (X : Set G) ≤ (dataOfSetup hS S).M :=
  r847ThinCZ_dataOfSetup hSE hSEZ hThin hCyc hSQ hK3 hG3 hRee hS S
    (r847E3CZRes_dataOfSetup hThin hCyc hG3 hRee hK3 hS S)

end CFSG.LocalAnalysis.UniquenessCase.UC22
