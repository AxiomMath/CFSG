module

public import CFSG.LocalAnalysis.StandardType.GGResTwDInverterJ
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusE8Rank
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusE7Rank
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusE6Rank
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusF4Rank
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusTwE6Rank
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterOrders

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResHyp.orthTorus_L_of_tbTor
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hNs : ¬ GGInnerDiagOnLabel GGTBTorNonsingularCov p Bs K)
    (hSplit : ¬ GGInnerDiagOnLabel GGTBTorSplitLinearCov p Bs K)
    (hL : ¬ GGInnerDiagOnLabel GGTableBUnitaryLiftLabel p Bs L)
    (hSector : ¬ GGInnerDiagOnLab
        (fun p lab => (GGTypeASplitLabel p lab ∨
          ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1)) ∨
          GGStdSubSmallUnitaryLabel p lab) p Bs L)
    (hcard : ¬ Nat.card Bs ≤ p * Nat.card
      ↥((ggBstarComm K Bs).map Bs.subtype ⊔ Subgroup.zpowers y))
    (hyU : y ∉ (ggBstarComm K Bs).map Bs.subtype) :
    GGInnerDiagOnLabel GGOrthTorusLabel p Bs L := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨⟨tK, r, f⟩, hΛK, hhasK, -, -, -, -, -, ⟨htK, hr, hr5, hpd, hpq⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel (ggInnerDiagOnLabel_twA_of_tbTor hp hp2 hp3 hK hNs hSplit)
  change tK = .twA at htK
  subst htK
  dsimp only at hr hr5 hpd hpq
  obtain ⟨hBseq, -⟩ :=
    hH.exists_unitary_J_block_of_K hRig hLB hPJ hr hr5 hpq hpd hhasK hΛK hcard hyU
  have hp7 : p ≠ 7 := by
    rintro rfl
    exact UnitaryCenter.not_seven_dvd_two_pow_add_one f hpq
  have hSstar : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hBst : GGBstar p B Bs := hH.1.2.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hSstar.1.2.1
  have hm1 : r + 1 ≤ LargeEvenTwoLocalRank p G := by
    have h1 : Nat.card Bs ≤ p * Nat.card B := hBst.2.2.1
    rw [hBseq, hBcard, ← pow_succ'] at h1
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
    omega
  have hm2 : LargeEvenTwoLocalRank p G ≤ r + 2 := by
    have h1 : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBst.1
    rw [hBseq, hBcard] at h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hst.1
  have hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
    obtain ⟨-, -, θ, -⟩ := hh
    exact ⟨θ⟩
  have hsplit : LargeEvenSplit p lab := by
    obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
    exact hP.1
  obtain ⟨hperf', lab₀, hΛ₀, hraw₀⟩ := ggInnerDiagOn_relabel hRig hH.2.2.1.1 hΛ hhas
  obtain ⟨-, -, -, -, -, -, -, hl₀, -, -⟩ := largeEvenRawDatum_exists hraw₀
  have hsplit₀ : LargeEvenSplit p lab₀ := hl₀ ▸ hsplit
  have hmkLabel : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab₀ → GGInnerDiagOnLabel S p Bs L :=
    fun S hS => ⟨hperf', lab₀, hΛ₀, largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hnab, θ, _, hN, hb⟩ => ⟨hs, hnab, θ, hS, hN, hb⟩) hraw₀⟩
  have hmkLab : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab₀ → GGInnerDiagOnLab S p Bs L :=
    fun S hS => ⟨hperf', lab₀, hΛ₀, largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hnab, θ, _, hN, hb⟩ => ⟨hs, hnab, θ, hS, hsplit₀, hN, hb⟩) hraw₀⟩
  have hAdata : ∀ (R : Type) [Group R] (I : Set (MulAut R))
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* R), Bs ≤ Subgroup.normalizer (L : Set G) →
      (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      ∃ A : Subgroup (MulAut R), IsElemAbelian p A ∧ (∀ a ∈ A, a ∈ I) ∧
        (∀ s : ℕ, GGTorusLift p s R → p ^ s ≤ Nat.card A) ∧
        p ^ r ≤ Nat.card A ∧ Nat.card A ≤ p ^ (r + 1) := by
    intro R _ I θ hN hb
    have hBNL : B ≤ Subgroup.normalizer (L : Set G) := hBst.1.trans hN
    have hAp := card_range_ggBeta_mul L θ hp hSstar hperf' hBNL
    rw [hBcard] at hAp
    have hAeq : Nat.card (ggBeta L θ hBNL).range = p ^ (LargeEvenTwoLocalRank p G - 1) := by
      have hdecomp : p ^ LargeEvenTwoLocalRank p G =
          p ^ (LargeEvenTwoLocalRank p G - 1) * p := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hdecomp] at hAp
      exact Nat.mul_right_cancel hp.pos hAp
    refine ⟨(ggBeta L θ hBNL).range, isElemAbelian_range_ggBeta θ hSstar.1.1 hBNL, ?_,
      fun s hs => pow_le_card_range_ggBeta hp hSstar hperf' θ hBNL hs, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ha
      exact ggBeta_mem L θ hBNL (fun b hb' => hb b (hBst.1 hb')) b
    · rw [hAeq]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    · rw [hAeq]
      exact Nat.pow_le_pow_right hp.pos (by omega)
  have hsmall : LargeEvenLabelAll lab₀ (fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3) → False := by
    intro hAll
    obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, hb⟩, hR⟩ := largeEvenRawDatum_exists (hAll _ hraw₀)
    obtain ⟨A, hAb, hAI, -, hlo, -⟩ := hAdata R I θ hN hb
    have h1 := hR A (fun a ha => hAI a ha) hAb
    have h2 : p ^ 3 ≤ p ^ r := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  have hcensus : ∀ C : Prop, ¬ C → LargeEvenLabelAll lab₀ (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
      (∀ s : ℕ, GGTorusLift p s R → p ^ s ≤ Nat.card A) →
      p ^ (r + 1 - 1) ≤ Nat.card A → Nat.card A ≤ p ^ (r + 1) → C) → False := by
    intro C hC hAll
    obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, hb⟩, hR⟩ := largeEvenRawDatum_exists (hAll _ hraw₀)
    obtain ⟨A, hAb, hAI, hbig, hlo, hup⟩ := hAdata R I θ hN hb
    exact hC (hR A hAb hAI hbig (by simpa using hlo) hup)
  obtain ⟨t, l, n⟩ := lab₀
  have hsq : ∀ m : ℕ, p ∣ 2 ^ m + 1 ∨ p ∣ 2 ^ m - 1 → p ∣ (2 ^ m) ^ 2 - 1 := by
    intro m hm
    have h1 : (2 ^ m) ^ 2 - 1 = (2 ^ m - 1) * (2 ^ m + 1) := by
      have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      zify [h2, Nat.one_le_pow 2 _ (Nat.one_le_two_pow (n := m))]
      ring
    rw [h1]
    rcases hm with h | h
    · exact Dvd.dvd.mul_left h _
    · exact Dvd.dvd.mul_right h _
  cases t with
  | A =>
    have hpq' : p ∣ 2 ^ n - 1 := by
      simpa [LargeEvenSplit, LargeEvenUntwisted, hp3] using hsplit₀
    refine absurd (hmkLab _ (Or.inl (Or.inl ?_))) hSector
    by_cases hpl : p ∣ l + 1
    · exact Or.inr ⟨rfl, hpq', hpl⟩
    · exact Or.inl (Or.inl ⟨rfl, hpq', hpl⟩)
  | twA =>
    have hpq' : p ∣ 2 ^ n + 1 := by
      simpa [LargeEvenSplit, LargeEvenUntwisted, hp3] using hsplit₀
    exact absurd (hmkLabel _ ⟨Or.inl rfl, hpq'⟩) hL
  | B =>
    have hpq' : p ∣ 2 ^ n - 1 := by
      simpa [LargeEvenSplit, LargeEvenUntwisted, hp3] using hsplit₀
    exact absurd (hmkLab _ (Or.inl (Or.inr ⟨Or.inl rfl, hpq'⟩))) hSector
  | C =>
    have hpq' : p ∣ 2 ^ n - 1 := by
      simpa [LargeEvenSplit, LargeEvenUntwisted, hp3] using hsplit₀
    exact absurd (hmkLab _ (Or.inl (Or.inr ⟨Or.inr rfl, hpq'⟩))) hSector
  | D =>
    have hpq' : p ∣ 2 ^ n - 1 := by
      simpa [LargeEvenSplit, LargeEvenUntwisted, hp3] using hsplit₀
    have hl3 : 3 ≤ l := hΛ₀.2
    by_cases hl : l = 3
    · subst hl
      exact absurd (hmkLab _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨rfl, rfl, hpq'⟩))))))
        hSector
    · exact hmkLabel _ ⟨Or.inl rfl, show 4 ≤ l by omega, Or.inr hpq'⟩
  | twD =>
    have hpq' : p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1 := by
      have h := hsplit₀
      simp only [LargeEvenSplit, LargeEvenUntwisted] at h
      rcases h with h | h | h | h
      · exact h.1.elim
      · exact Or.inl h.2.2
      · exact Or.inr h.2
      · exact absurd h.2 hp3
    have hl2 : 2 ≤ l := hΛ₀.2
    by_cases hl2' : l = 2
    · subst hl2'
      exact absurd (hmkLab _ (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨rfl, rfl, hsq n hpq'⟩))))))
        hSector
    · by_cases hl3' : l = 3
      · subst hl3'
        rcases hpq' with h | h
        · exact absurd (hmkLabel _ ⟨Or.inr ⟨rfl, rfl⟩, h⟩) hL
        ·
          exfalso
          refine hsmall ((largeEvenLabelAll_card_le_twDThree hp hΛ₀ ⟨rfl, rfl, h⟩).mono ?_)
          intro R _ I _ hX X hXI hXab
          exact (hX X hXI hXab).trans_lt (Nat.pow_lt_pow_right hp.one_lt (by norm_num))
      · exact hmkLabel _ ⟨Or.inr rfl, show 4 ≤ l by omega, hpq'⟩
  | E6 =>
    exact (hcensus _ (by omega) (q2c_E6_rank rfl hp hp2 hsplit₀ hpd)).elim
  | E7 =>
    exact (hcensus _ (by omega) (q2c_E7_rank rfl hp hp2 hsplit₀ hpd)).elim
  | E8 =>
    exact (hcensus _ (by omega) (q2c_E8_rank rfl hp hp2 hsplit₀ hpd)).elim
  | F4 =>
    exact (hcensus _ (by omega) (q2c_F4_rank rfl hp hp2 hsplit₀ hpd)).elim
  | twE6 =>
    exact (hcensus _ (by omega) (q2c_twE6_rank rfl hp hp2 hsplit₀ hpd)).elim
  | triD4 =>
    have hpq' : p ∣ 2 ^ n - 1 := by
      have h := hsplit₀
      simp only [LargeEvenSplit, LargeEvenUntwisted] at h
      rcases h with h | h | h | h
      · exact h.1.elim
      · exact absurd rfl h.2.1
      · exact h.2
      · exact absurd h.2 hp3
    exact (hsmall (NbrInnerNine.largeEvenLabelAll_card_lt_triD4_of hp hΛ₀ rfl
      (Or.inr (hsq n (Or.inr hpq'))))).elim
  | G2 =>
    exact (hsmall (NbrInnerNine.largeEvenLabelAll_card_lt_G2_all hp hp2 rfl)).elim
  | twB2 =>
    exact (hsmall (NbrInnerNine.largeEvenLabelAll_card_lt_twB2_all hp hp2 hΛ₀ rfl)).elim
  | twF4 =>
    exact (hsmall (TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of_ne_three hp3 hp hΛ₀ rfl
      hsplit₀)).elim
  | B2der =>
    have hn1 : n = 1 := hΛ₀.2.2
    subst hn1
    exfalso
    have h := hsplit₀
    simp only [LargeEvenSplit, LargeEvenUntwisted] at h
    rcases h with h | h | h | h
    · exact hp.one_lt.ne' (Nat.dvd_one.mp h.2)
    · exact h.1 trivial
    · rcases h.1 with h1 | h1 <;> exact absurd h1 (by decide)
    · exact hp3 h.2
  | G2der =>
    have hn1 : n = 1 := hΛ₀.2.2
    subst hn1
    exfalso
    have h := hsplit₀
    simp only [LargeEvenSplit, LargeEvenUntwisted] at h
    rcases h with h | h | h | h
    · exact hp.one_lt.ne' (Nat.dvd_one.mp h.2)
    · exact h.1 trivial
    · rcases h.1 with h1 | h1 <;> exact absurd h1 (by decide)
    · exact hp3 h.2
  | twF4der =>
    have hn1 : n = 1 := hΛ₀.2.2
    subst hn1
    exfalso
    have h := hsplit₀
    simp only [LargeEvenSplit, LargeEvenUntwisted] at h
    rcases h with h | h | h | h
    · exact h.1
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h.2.2)
    · rcases h.1 with h1 | h1 <;> exact absurd h1 (by decide)
    · exact hp3 h.2

theorem GGResHyp.exists_inverter_of_tbTor_rest
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hNs : ¬ GGInnerDiagOnLabel GGTBTorNonsingularCov p Bs K)
    (hSplit : ¬ GGInnerDiagOnLabel GGTBTorSplitLinearCov p Bs K)
    (hL : ¬ GGInnerDiagOnLabel GGTableBUnitaryLiftLabel p Bs L)
    (hSector : ¬ GGInnerDiagOnLab
        (fun p lab => (GGTypeASplitLabel p lab ∨
          ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1)) ∨
          GGStdSubSmallUnitaryLabel p lab) p Bs L)
    (hcard : ¬ Nat.card Bs ≤ p * Nat.card
      ↥((ggBstarComm K Bs).map Bs.subtype ⊔ Subgroup.zpowers y))
    (hyU : y ∉ (ggBstarComm K Bs).map Bs.subtype) :
    (ggBstarComm K Bs).map Bs.subtype = Bs ⊓ J ∧ ggBstarComm K Bs = (Bs ⊓ J).subgroupOf Bs ∧
      ∃ n : G, n ∈ L ∧ n ∈ Subgroup.normalizer (Bs : Set G) ∧ n * x * n⁻¹ = x ∧
        ∀ u ∈ Bs ⊓ J, n * u * n⁻¹ = u⁻¹ :=
  hH.exists_twD_inverter_of_tbTor hRig hLB hPJ hp3 hK hNs hSplit
    (hH.orthTorus_L_of_tbTor hRig hLB hPJ hp3 hp5 hK hNs hSplit hL hSector hcard hyU) hcard hyU

end CFSG.StandardType
