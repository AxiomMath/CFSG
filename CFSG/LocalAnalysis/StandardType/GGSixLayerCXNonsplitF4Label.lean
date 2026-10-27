module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Dvd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLMark
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcToral
public import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf

namespace F4Nonsplit

theorem sq_mul_dvd_pow_mul {q N C b d : ℕ} (hC : (q ^ 2 - 1) * b ∣ C) (hd : d ∣ b) :
    (q ^ 2 - 1) * d ∣ q ^ N * C :=
  (mul_dvd_mul_left _ hd).trans (hC.trans (dvd_mul_left _ _))

theorem sq_sub_one_mul_lieOrderDivisor_dvd {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (ht : t ≠ .twistedB2) :
    ((2 ^ f) ^ 2 - 1) * lieOrderDivisor t n (2 ^ f) ∣ lieOrderNumerator t n (2 ^ f) := by
  rw [CatLeafProof.lieOrderNumerator_eq hadm]
  have hf : f ≠ 0 := by have := hadm.2.1; omega
  have hsub : ∀ i, 2 ^ f - 1 ∣ (2 ^ f) ^ i - 1 := fun i => by
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 i
  have hadd : ∀ i, Odd i → 2 ^ f + 1 ∣ (2 ^ f) ^ i + 1 := fun i hi => by
    simpa using hi.nat_add_dvd_pow_add_pow (2 ^ f) 1
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · rw [Finset.Icc_self, Finset.prod_singleton, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one,
        mul_comm (2 ^ f)]
      exact mul_dvd_mul_left _ ((Nat.gcd_dvd_left 2 _).trans (dvd_pow_self 2 hf))
    · have hs : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_Icc]
        omega
      have hC : ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) ∣
          ∏ i ∈ Finset.Icc 2 n, ((2 ^ f) ^ i - 1) := by
        have := Finset.prod_dvd_prod_of_subset _ _ (fun i => (2 ^ f) ^ i - 1) hs
        rwa [Finset.prod_pair (by norm_num)] at this
      exact sq_mul_dvd_pow_mul hC ((Nat.gcd_dvd_right _ _).trans (hsub 3))
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    have hs : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]
      omega
    have hC : ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) ∣
        ∏ i ∈ Finset.Icc 2 n, (if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1) := by
      have := Finset.prod_dvd_prod_of_subset _ _
        (fun i => if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1) hs
      rw [Finset.prod_pair (by norm_num)] at this
      simpa only [even_two, ite_true, show ¬ Even 3 by decide, ite_false] using this
    exact sq_mul_dvd_pow_mul hC ((Nat.gcd_dvd_right _ _).trans (hadd 3 (by decide)))
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc]
      omega
    have hP : (2 ^ f) ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 1 n, ((2 ^ f) ^ (2 * i) - 1) :=
      Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1) h1
    have hodd : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hf⟩) odd_one
    rw [Nat.coprime_two_left.2 hodd]
    exact sq_mul_dvd_pow_mul (b := 1) (by rwa [mul_one]) (one_dvd _)
  case POmegaOdd =>
    obtain ⟨-, -, -, hp2⟩ := hadm
    exact absurd rfl hp2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 (n - 1) := by
      simp only [Finset.mem_Icc]
      omega
    have hP : (2 ^ f) ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1) :=
      Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1) h1
    exact sq_mul_dvd_pow_mul ((dvd_of_eq (mul_comm _ _)).trans (mul_dvd_mul_left _ hP))
      (Nat.gcd_dvd_right _ _)
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 (n - 1) := by
      simp only [Finset.mem_Icc]
      omega
    have hP : (2 ^ f) ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1) :=
      Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1) h1
    exact sq_mul_dvd_pow_mul ((dvd_of_eq (mul_comm _ _)).trans (mul_dvd_mul_left _ hP))
      (Nat.gcd_dvd_right _ _)
  case G2 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact sq_mul_dvd_pow_mul (b := 1) ⟨(2 ^ f) ^ 6 - 1, by ring⟩ (one_dvd _)
  case F4 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact sq_mul_dvd_pow_mul (b := 1)
      ⟨((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1), by ring⟩ (one_dvd _)
  case E6 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact sq_mul_dvd_pow_mul (b := (2 ^ f) ^ 9 - 1)
      ⟨((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 5 - 1), by ring⟩
      ((Nat.gcd_dvd_right _ _).trans (hsub 9))
  case E7 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact sq_mul_dvd_pow_mul (b := (2 ^ f) ^ 18 - 1)
      ⟨((2 ^ f) ^ 14 - 1) * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 10 - 1) * ((2 ^ f) ^ 8 - 1) *
        ((2 ^ f) ^ 6 - 1), by ring⟩
      ((Nat.gcd_dvd_right _ _).trans (hsub 18))
  case E8 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact sq_mul_dvd_pow_mul (b := 1)
      ⟨((2 ^ f) ^ 30 - 1) * ((2 ^ f) ^ 24 - 1) * ((2 ^ f) ^ 20 - 1) * ((2 ^ f) ^ 18 - 1) *
        ((2 ^ f) ^ 14 - 1) * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 8 - 1), by ring⟩ (one_dvd _)
  case twistedE6 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact sq_mul_dvd_pow_mul (b := (2 ^ f) ^ 9 + 1)
      ⟨((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 5 + 1), by ring⟩
      ((Nat.gcd_dvd_right _ _).trans (hadd 9 (by decide)))
  case trialityD4 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    exact sq_mul_dvd_pow_mul (b := 1)
      ⟨((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1), by ring⟩ (one_dvd _)
  case twistedB2 => exact absurd rfl ht
  case twistedG2 =>
    obtain ⟨-, -, -, hp3, -⟩ := hadm
    exact absurd hp3 (by norm_num)
  case twistedF4 =>
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor]
    have h4 := CFSG.LocalAnalysis.EvenBN.GMSK.TypeDet.sq_sub_one_dvd_pow_four_sub_one (2 ^ f)
    refine sq_mul_dvd_pow_mul (b := 1) ?_ (one_dvd _)
    rw [mul_one]
    exact ((h4.mul_left _).mul_right _).mul_right _
  case Tits =>
    obtain ⟨-, -, -, -, hf1⟩ := hadm
    subst hf1
    simp only [lieOrderDivisor, lieSylowExponent, CatLeafProof.lieOrderCofactor, mul_one]
    exact Dvd.dvd.mul_left (by norm_num) _

theorem markDeg_eq_or {lab : LargeEvenLabel} (hc : markChar lab = 2) :
    markDeg lab = lab.n ∨ markDeg lab = 2 * lab.n := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals first
    | exact Or.inl rfl
    | (show (if l = 2 then 2 * n else n) = n ∨ (if l = 2 then 2 * n else n) = 2 * n
       split_ifs <;> simp)
    | (simp only [markChar] at hc; contradiction)

theorem markTag_ne_twistedB2 {lab : LargeEvenLabel} (h : lab.tag ≠ .twB2) :
    markTag lab ≠ .twistedB2 := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals first
    | exact absurd rfl h
    | (show (if l = 3 then StatedLieTag.PSL else .POmegaPlus) ≠ .twistedB2
       split_ifs <;> (intro h'; cases h'))
    | (show (if l = 2 then StatedLieTag.PSL else if l = 3 then .PSU else .POmegaMinus) ≠
        .twistedB2
       split_ifs <;> (intro h'; cases h'))
    | (intro h'; cases h')

section Card


theorem sq_sub_one_dvd_card_of_lieModel {M : Type} [Group M] {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (h : LieModel M t n 2 f) (ht : t ≠ .twistedB2) :
    (2 ^ f) ^ 2 - 1 ∣ Nat.card M := by
  obtain ⟨-, hmul, -⟩ := CatLeafProof.lieOrderFormulasInput M t n 2 f hadm h
  have h3 := sq_sub_one_mul_lieOrderDivisor_dvd hadm ht
  rw [← hmul] at h3
  exact Nat.dvd_of_mul_dvd_mul_right
    (Nat.pos_of_ne_zero (CatLeafProof.lieOrderDivisor_ne_zero hadm)) h3

theorem seven_dvd_card_of_lieModel_PSL {M : Type} [Group M] {m : ℕ} (hm : 3 ≤ m)
    (hadm : StatedLieAdmissible .PSL m 2 1) (h : LieModel M .PSL m 2 1) : 7 ∣ Nat.card M := by
  obtain ⟨-, hmul, -⟩ := CatLeafProof.lieOrderFormulasInput M .PSL m 2 1 hadm h
  have hd : lieOrderDivisor .PSL m (2 ^ 1) = 1 := by
    simp [lieOrderDivisor]
  rw [hd, mul_one] at hmul
  rw [hmul]
  have h3 : (3 : ℕ) ∈ Finset.Icc 2 m := by
    simp only [Finset.mem_Icc]
    omega
  have h7 : (2 ^ 1) ^ 3 - 1 ∣ ∏ i ∈ Finset.Icc 2 m, ((2 ^ 1) ^ i - 1) :=
    Finset.dvd_prod_of_mem (fun i => (2 ^ 1) ^ i - 1) h3
  exact Dvd.dvd.mul_left h7 _

theorem seven_dvd_card_of_lieModel_E6 {M : Type} [Group M] {m : ℕ}
    (hadm : StatedLieAdmissible .E6 m 2 1) (h : LieModel M .E6 m 2 1) : 7 ∣ Nat.card M := by
  obtain ⟨-, hmul, -⟩ := CatLeafProof.lieOrderFormulasInput M .E6 m 2 1 hadm h
  have hd : lieOrderDivisor .E6 m (2 ^ 1) = 1 := by
    simp [lieOrderDivisor]
  rw [hd, mul_one] at hmul
  rw [hmul]
  norm_num [lieOrderNumerator]

theorem dvd_card_of_markedModel_halfSplit {M : Type} [Group M] {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hc : markChar lab = 2) (hM : MarkedModel lab M)
    (hB2 : lab.tag ≠ .twB2) {p : ℕ} (hp3 : p ≠ 3) {c : Prop}
    (hHS : LargeEvenHalfSplit p lab c) : p ∣ Nat.card M := by
  have hM' : LieModel M (markTag lab) (markRank lab) 2 (markDeg lab) := by
    have h := hM
    unfold MarkedModel at h
    rwa [hc] at h
  obtain ⟨hadm, -⟩ := CFSG.RankThree.PartOne.S12K.card_of_lieModel_two hM'
  have hsq := sq_sub_one_dvd_card_of_lieModel hadm hM' (markTag_ne_twistedB2 hB2)
  have hdeg : (2 ^ lab.n) ^ 2 - 1 ∣ (2 ^ markDeg lab) ^ 2 - 1 := by
    rcases markDeg_eq_or hc with h | h
    · rw [h]
    · have e : (2 : ℕ) ^ (2 * lab.n) = (2 ^ lab.n) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [h, e]
      have := Nat.sub_dvd_pow_sub_pow ((2 ^ lab.n) ^ 2) 1 2
      rwa [one_pow] at this
  rcases LinNonsplit.halfSplit_cases hHS with h1 | h1 | h1 | ⟨-, hn, rfl⟩ | ⟨hAE, hn, rfl⟩
  · exact (h1.trans (Nat.sub_one_dvd_pow_sub_one _ 2)).trans (hdeg.trans hsq)
  · refine (h1.trans ?_).trans (hdeg.trans hsq)
    exact ⟨2 ^ lab.n - 1, by
      have h2 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
      zify [h2, Nat.one_le_pow 2 (2 ^ lab.n) h2]
      ring⟩
  · exact absurd h1 hp3
  · have h5 : (5 : ℕ) ∣ (2 ^ lab.n) ^ 2 - 1 := by
      rw [hn]
      norm_num
    exact h5.trans (hdeg.trans hsq)
  · obtain ⟨t, l, n⟩ := lab
    simp only at hAE hn
    subst hn
    rcases hAE with rfl | rfl
    · have hl2 : 1 ≤ l ∧ (l = 1 → 2 ≤ 1) := hlab.2
      have hl : 2 ≤ l := by
        by_contra hcon
        have := hl2.2 (by omega)
        omega
      exact seven_dvd_card_of_lieModel_PSL (m := l + 1) (by omega) hadm hM'
    · exact seven_dvd_card_of_lieModel_E6 hadm hM'

end Card

end F4Nonsplit

section Top


theorem F4Nonsplit.not_halfSplit_of_isComponentOf_top {τ : Tag} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hQτ : CFSG.IsQuasisimple ↥(adjointGroup τ K)) {p : ℕ} (hp3 : p ≠ 3)
    (hC : ¬ p ∣ Nat.card ↥(adjointGroup τ K)) {X : Subgroup ↥(adjointGroup τ K)}
    (hX : IsComponentOf X ⊤) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hc : markChar lab = 2) (hM : MarkedModel lab (↥X ⧸ Subgroup.center ↥X)) {c : Prop} :
    ¬ LargeEvenHalfSplit p lab c := by
  intro hHS
  have hQ : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥(adjointGroup τ K)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQτ
  have hc' : ⁅(⊤ : Subgroup ↥(adjointGroup τ K)), ⊤⁆ = ⊤ :=
    CFSG.RankThree.Chevalley.commutator_eq_self_of_isPerfect hQ.1
  have hQ' : CFSG.IsQuasisimple ↥(⁅(⊤ : Subgroup ↥(adjointGroup τ K)), ⊤⁆ :
      Subgroup ↥(adjointGroup τ K)) := by
    rw [hc']
    exact hQ
  have hXtop : X = ⊤ := by rw [F4Nonsplit.eq_commutator_of_isComponentOf hQ' hX, hc']
  subst hXtop
  have hZG : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hZ : Subgroup.center ↥(⊤ : Subgroup ↥(adjointGroup τ K)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : (z : ↥(adjointGroup τ K)) ∈ Subgroup.center ↥(adjointGroup τ K) :=
      Subgroup.mem_center_iff.2 fun g =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, trivial⟩)
    rw [hZG, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (Subtype.ext hz')
  have hcard : Nat.card (↥(⊤ : Subgroup ↥(adjointGroup τ K)) ⧸
      Subgroup.center ↥(⊤ : Subgroup ↥(adjointGroup τ K))) =
        Nat.card ↥(adjointGroup τ K) := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, Subgroup.card_top]
  by_cases hB2 : lab.tag = .twB2
  ·
    have hM' : LieModel (↥(⊤ : Subgroup ↥(adjointGroup τ K)) ⧸
        Subgroup.center ↥(⊤ : Subgroup ↥(adjointGroup τ K)))
        (markTag lab) (markRank lab) 2 (markDeg lab) := by
      have h := hM
      unfold MarkedModel at h
      rwa [hc] at h
    have hT : markTag lab = .twistedB2 := by
      obtain ⟨t, l, n⟩ := lab
      simp only at hB2
      subst hB2
      rfl
    rw [hT] at hM'
    have h3K : 3 ∣ Nat.card K ^ 2 - 1 := by
      obtain ⟨f, -, hK⟩ := F4Nonsplit.exists_card_eq_two_pow K
      rw [hK, ← pow_mul, mul_comm, pow_mul]
      have h43 := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 f
      rw [one_pow, show (2 : ℕ) ^ 2 - 1 = 3 by norm_num] at h43
      exact h43
    have h3 : 3 ∣ Nat.card ↥(adjointGroup τ K) := LayerPDivExc.dvd_card_adjointGroup h3K
    rw [← hcard] at h3
    exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_twistedB2_of_lieModel hM' h3
  · have h := F4Nonsplit.dvd_card_of_markedModel_halfSplit hlab hc hM hB2 hp3 hHS
    rw [hcard] at h
    exact hC h

end Top

section Holds


theorem ggF4NonsplitCoprimeLabelInput_holds : GGF4NonsplitCoprimeLabelInput := by
  intro K _ _ _ p hp hp2 hq1 hq2 hC X hX lab hlab hc hM
  exact F4Nonsplit.not_halfSplit_of_isComponentOf_top
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K)
    (ExcNonsplit.ne_three_of_not_dvd_card hq1 hq2) hC hX hlab hc hM

end Holds

end CFSG.StandardType
