module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimLinear
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearNbr
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimUnitary
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimReduced
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySides
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixOriginal
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.StandardType

open CFSG.Assembly
open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.Line63.H5

theorem GGConfig.card_bstar_le_of_card_gamma_J
    {G : Type} [Group G] [Finite G] {p k : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hcap : Nat.card (ggGamma J hBJ).range ≤ p ^ k) : Nat.card Bs ≤ p ^ (k + 3) := by
  have hm : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G :=
    hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hB : Nat.card B = Nat.card (ggGamma J hBJ).range * p ^ 2 := by
    rw [hBcard, hcfg.card_range_gamma_B_J hBJ, ← pow_add]
    congr 1
    omega
  calc Nat.card Bs ≤ p * Nat.card B := hcfg.2.1.2.2.1
    _ = p * (Nat.card (ggGamma J hBJ).range * p ^ 2) := by rw [hB]
    _ ≤ p * (p ^ k * p ^ 2) := Nat.mul_le_mul_left p (Nat.mul_le_mul_right _ hcap)
    _ = p ^ (k + 3) := by
      rw [← pow_add, ← pow_succ']

theorem card_bstar_le_of_two_node_linear_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {r f : ℕ} (hr : 4 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩)
    (hJLab : GGHasLabel ⟨.A, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    Nat.card Bs ≤ p ^ (r + 1) := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hS, hJ⟩ :=
    exists_corank_two_block_of_large_linear_K hRig hLB hH hr hpq hLab hΛ hJLab
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) :=
    hH.1.2.1.1.trans hH.Bs_le_normalizer_J
  have hcap := TypeANbrDvd.card_range_ggGamma_le (Fact.out : p.Prime) φ
    (show J = TypeANbrDvd.blockImage S K φ from hJ) hN hBJ hH.1.2.1.1 hker
    (by omega : 2 ≤ S.card) hdiag (fun b =>
      Subtype.ext (hH.1.tableB_facts.2.1.2 b (hH.1.2.1.1 b.2)))
  have hc := hH.1.card_bstar_le_of_card_gamma_J hBJ hcap
  have he : S.card - 1 + 3 = r + 1 := by omega
  rwa [he] at hc

theorem card_bstar_le_of_two_node_unitary_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5)
    (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hJLab : GGHasLabel ⟨.twA, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    Nat.card Bs ≤ p ^ (r + 1) := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hM, hJ, hS, hdiag⟩ :=
    exists_corank_two_block_of_large_unitary_K hRig hLB hH hr hr5 hpq hpd hLab hΛ hJLab
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) :=
    hH.1.2.1.1.trans hH.Bs_le_normalizer_J
  have hcap := card_range_ggGamma_le hM hN hdiag hH.1.2.1.1 S
    (by omega : 3 ≤ S.card) hJ hBJ (Fact.out : p.Prime)
    (fun b hb => hH.1.tableB_facts.2.1.2 b (hH.1.2.1.1 hb))
  have hc := hH.1.card_bstar_le_of_card_gamma_J hBJ hcap
  have he : S.card - 1 + 3 = r + 1 := by omega
  rwa [he] at hc

theorem card_bstar_le_of_two_node_unitary_six_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {f : ℕ} (hf : f ≠ 1)
    (hpq : 3 ∣ 2 ^ f + 1)
    (hLab : GGHasLabel ⟨.twA, 5, f⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hJLab : GGHasLabel ⟨.twA, 3, f⟩ (J ⧸ Subgroup.center J)) :
    Nat.card Bs ≤ 3 ^ 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hM, hS, hJ, hdiag⟩ :=
    exists_corank_two_block_of_unitary_six_side hRig hLB hH (Or.inr rfl)
      hf hpq hLab hΛ hJLab
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) :=
    hH.1.2.1.1.trans hH.Bs_le_normalizer_J
  have hcap := card_range_ggGamma_le hM hN hdiag hH.1.2.1.1 S
    (by omega : 3 ≤ S.card) hJ hBJ Nat.prime_three
    (fun b hb => hH.1.tableB_facts.2.1.2 b (hH.1.2.1.1 hb))
  have hc := hH.1.card_bstar_le_of_card_gamma_J hBJ hcap
  simpa only [hS] using hc

theorem card_bstar_le_of_two_node_unitary_six_two_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLab : GGHasLabel ⟨.twA, 5, 1⟩ (K ⧸ Subgroup.center K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, 5, 1⟩)
    (hJLab : GGHasLabel ⟨.twA, 3, 1⟩ (J ⧸ Subgroup.center J)) :
    Nat.card Bs ≤ 3 ^ 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hField, hFinite, hChar, hN, hNbar, φ, S, hF, hM, hS,
    hJbar, hdiag, hJK, hBsJ⟩ :=
      exists_block_cover_of_unitary_six_two_side hRig hLB hH (Or.inr rfl) hLab hΛ hJLab
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := hH.1.2.1.1.trans hBsJ
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hH.1.2.1.1.trans hN
  obtain ⟨hbar, hcard⟩ := card_range_ggGamma_eq_redMk hBN hJK hBJ
    hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  have hBBs : (redMkB hBN).range ≤ (redMkB hN).range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hH.1.2.1.1 b.2⟩, rfl⟩
  have hBp : ∀ b ∈ (redMkB hBN).range, b ^ 3 = 1 := by
    rintro _ ⟨b, rfl⟩
    have hb : b ^ 3 = 1 := Subtype.ext
      (hH.1.tableB_facts.2.1.2 b (hH.1.2.1.1 b.2))
    rw [← map_pow, hb, map_one]
  have hcap := card_range_ggGamma_le hM hNbar hdiag hBBs S
    (by omega : 3 ≤ S.card) hJbar hbar Nat.prime_three hBp
  rw [← hcard] at hcap
  have hc := hH.1.card_bstar_le_of_card_gamma_J hBJ hcap
  simpa only [hS] using hc

theorem ggTwoNodeRowDimKnown_of_labelRigid_balance
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) : GGTwoNodeRowDimKnown := by
  intro G _ _ p _ B Bs x L D J y K N hH hrow hp2 hN hpd
  obtain ⟨labJ, labK, hΛJ, hΛK, hJ, hK, hrow, hNK⟩ := hrow
  rcases hrow with hA | hU | hE | hE
  · obtain ⟨htag, hpq, -, heq⟩ := hA
    obtain ⟨t, a, f⟩ := labJ
    dsimp only at htag hpq heq
    subst t
    rw [heq] at hΛK hK hNK
    have hr : 4 ≤ a + 2 := by change a + 2 + 1 = N at hNK; omega
    rw [← hNK]
    apply card_bstar_le_of_two_node_linear_K hRig hLB hH hr hpq hK hΛK
    simpa only [Nat.add_sub_cancel] using hJ
  · obtain ⟨htag, hpq, hpdiv, heq⟩ := hU
    obtain ⟨t, a, f⟩ := labJ
    dsimp only at htag hpq hpdiv heq
    subst t
    rw [heq] at hΛK hK hNK
    have hr : 4 ≤ a + 2 := by change a + 2 + 1 = N at hNK; omega
    by_cases h5 : a + 2 = 5
    · have ha : a = 3 := by omega
      have hp : p.Prime := Fact.out
      have hp6 : p ∣ 2 * 3 := by simpa only [ha] using hpdiv
      have hp3 : p = 3 := by
        rcases hp.dvd_mul.mp hp6 with h2 | h3
        · exact (hp2 (((Nat.dvd_prime Nat.prime_two).mp h2).resolve_left hp.ne_one)).elim
        · exact ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left hp.ne_one
      subst p
      subst a
      have hN6 : N = 6 := by simpa using hNK.symm
      rw [hN6]
      by_cases hf : f = 1
      · subst f
        exact card_bstar_le_of_two_node_unitary_six_two_K hRig hLB hH hK hΛK hJ
      · exact card_bstar_le_of_two_node_unitary_six_K hRig hLB hH hf hpq hK hΛK hJ
    · rw [← hNK]
      apply card_bstar_le_of_two_node_unitary_K hRig hLB hH hr h5 hpq
        (by simpa only [Nat.add_assoc] using hpdiv) hK hΛK
      simpa only [Nat.add_sub_cancel] using hJ
  · rw [hE.2.2.2] at hNK
    change 0 + 1 = N at hNK
    omega
  · rw [hE.2.2.2] at hNK
    change 0 + 1 = N at hNK
    omega

theorem ggTwoNodeRowDimKnown_holds
    : GGTwoNodeRowDimKnown :=
  ggTwoNodeRowDimKnown_of_labelRigid_balance ggLabelRigidInput_holds
    (ggLBalanceInput_of_catalogueSchreier
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds)

end CFSG.StandardType

end
