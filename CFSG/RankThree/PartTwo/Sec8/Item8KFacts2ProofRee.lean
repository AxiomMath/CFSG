module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeField
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofDistinct
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
public import CFSG.LieType.Chevalley.ExactG2FiniteOrder

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LieType.Ree
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace Item8KFacts2Proof

theorem padicValNat_two_pow_mul_odd' {a r : ℕ} (hr : Odd r) : padicValNat 2 (2 ^ a * r) = a := by
  rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) hr.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hr)
      (even_iff_two_dvd.mpr h2)), add_zero]


theorem padicValNat_card_reeGamma {k : ℕ} {Kf : Type} [Field Kf] [Finite Kf]
    [CharP Kf ReeTag.F4.prime] (hKf : Nat.card Kf = 2 ^ (2 * k + 1)) :
    padicValNat 2 (Nat.card (ReeTag.F4.reeGamma Kf k)) = (2 * k + 1) * 12 := by
  rw [(LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion k Kf hKf).1]
  obtain ⟨r, hr, hr'⟩ := KFacts.exists_two_part_ree (q := 2 ^ (2 * k + 1)) (f := 2 * k + 1) rfl
    (by omega)
  rw [hr']
  exact padicValNat_two_pow_mul_odd' hr

theorem not_isList_of_ree
    {X : Type} [Group X] {k n : ℕ}
    (hn : 1 ≤ n) (hkn : 2 * k + 1 = 3 * n) {Kf : Type} [Field Kf]
    [Finite Kf] [CharP Kf ReeTag.F4.prime] (hKf : Nat.card Kf = 2 ^ (2 * k + 1))
    (e : X ≃* ReeTag.F4.reeGamma Kf k) :
    ¬ IsoTrialityD4 X n ∧ ¬ IsoGTwoEven X (3 * n) ∧ ¬ IsoSUThree X (2 ^ (3 * n)) ∧
      IsEmpty (X ≃* projSU 3 2 (3 * n)) ∧ IsEmpty (X ≃* projSp 2 (GaloisField 2 (3 * n))) := by
  have hv : padicValNat 2 (Nat.card X) = (2 * k + 1) * 12 := by
    rw [Nat.card_congr e.toEquiv]
    exact padicValNat_card_reeGamma hKf
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, ⟨fun f => ?_⟩, ⟨fun f => ?_⟩⟩
  · have := (Item83Proof.card_of_isoTrialityD4 hn h).2
    omega
  · obtain ⟨K, _, _, hK, ⟨f⟩⟩ := h
    have hcard := (CFSG.LieType.Chevalley.exact_G2_finite_order K hK).2.1
    rw [← Nat.card_congr f.toEquiv] at hcard
    have hodd : Odd (((2 ^ (3 * n)) ^ 6 - 1) * ((2 ^ (3 * n)) ^ 2 - 1)) :=
      (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
        (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
    obtain ⟨r, hr⟩ : ∃ r, r = ((2 ^ (3 * n)) ^ 6 - 1) * ((2 ^ (3 * n)) ^ 2 - 1) := ⟨_, rfl⟩
    have hcard' : Nat.card X = 2 ^ (3 * n * 6) * r := by rw [hcard, hr, mul_assoc, ← pow_mul]
    have h2 : padicValNat 2 (Nat.card X) = 3 * n * 6 := by
      rw [hcard']
      exact padicValNat_two_pow_mul_odd' (hr ▸ hodd)
    omega
  · obtain ⟨K, _, _, hK, ⟨f⟩⟩ := h
    have h2 := Item82Proof.padicValNat_card_statedSU_three (m := 3 * n) (by omega) hK
    rw [← Nat.card_congr f.toEquiv] at h2
    omega
  · have := (KFacts.padicValNat_card_and_card_cube_lt (by omega) f).1
    omega
  · have hcard := Sec19.Step1911Proof.card_projSp_two (n := 3 * n) (by omega)
    rw [← Nat.card_congr f.toEquiv] at hcard
    have hodd : Odd (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 4 - 1)) :=
      (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
        (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
    have h2 : padicValNat 2 (Nat.card X) = 3 * n * 4 := by
      rw [hcard]
      exact padicValNat_two_pow_mul_odd' hodd
    omega

end Item8KFacts2Proof

open Item8KFacts2Proof


theorem kF84FieldReeStd_holds :
    Item86ResProof.KF84FieldReeStd := by
  intro G _ _ A c L a A₀ d n h hA hd hRee
  have hn1 : 1 ≤ n := hd.odd.pos
  obtain ⟨k, Kf, _, _, _, hkn, hKf, ⟨e⟩⟩ := hRee
  have hk : 1 ≤ k := by omega
  have hKf' : Nat.card Kf = 2 ^ (2 * k + 1) := by rw [hKf, hkn]
  obtain ⟨hD4, hG2, hSU, hU, hSp⟩ := not_isList_of_ree hn1 hkn hKf' e
  have hKbar : IsoSUThree (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer {d}))) (2 ^ (2 * k + 1)) := by
    rw [hkn]
    rcases hd.cases with ⟨hL1, -, -⟩ | ⟨-, -, hK⟩ | ⟨hL3, -, -⟩ | ⟨hL4, -, -⟩ | ⟨hL5, -, -⟩
    · rcases hL1 with h1 | h1
      · exact (hD4 h1).elim
      · exact (hG2 h1).elim
    · exact hK
    · exact (hSU hL3).elim
    · exact (hU.false (Classical.choice hL4)).elim
    · exact (hSp.false (Classical.choice hL5)).elim
  have ha3 : a ^ 3 = 1 := Item86ResProof.pow_three_of_data83 hd
  have hout : Sec4.InducesOuterTheta a L := by
    rcases h.inducesStdKind with hk' | hk'
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk' (by decide)
  exact inducesStdKind_field_of_ree ((Item87Proof.residual_le _).trans inf_le_left)
    h.a_mem_normalizer (Item86ResProof.mem_normalizer_residual_of_data83 h hd) ha3 hout hk hKf'
    e hKbar

theorem kF84FieldRee_holds :
    KF84FieldRee := by
  intro G _ _ A c L a b X n h hRee
  obtain ⟨hbA, -, hn1, hcases⟩ := h.isGammaIndex
  obtain ⟨k, hk', hkn, ⟨e₀⟩⟩ := hRee
  have hR := (Sec4.Census.bridgeExceptional46).reeF4 k hk'
  obtain ⟨-, k₁, hk₁, hkk₁, Kf, _, _, _, hKf, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
  have hkk : k₁ = k := by omega
  subst hkk
  set e := e₀.trans e₁ with he
  obtain ⟨hD4, hG2, hSU, hU, hSp⟩ := not_isList_of_ree hn1 hkn hKf e
  have hKbar : IsoSUThree (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer {b}))) (2 ^ (2 * k₁ + 1)) := by
    rw [hkn]
    rcases hcases with ⟨-, -, -, -, hK⟩ | ⟨hL, -⟩
    · exact hK
    · rcases hL with hL1 | ⟨q, hq2, hqe, hGq⟩ | hL3 | hL4 | hL5
      · exact (hD4 hL1).elim
      · exact (hG2 (Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hGq)).elim
      · exact (hU.false (Classical.choice hL3)).elim
      · exact (hSU hL4).elim
      · exact (hSp.false (Classical.choice hL5)).elim
  have hAel := h.mem_partTwoF.1
  have ha3 : a ^ 3 = 1 := hAel.2 a h.a_mem
  have hout : Sec4.InducesOuterTheta a L := by
    rcases h.inducesStdKind with hk' | hk'
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk' (by decide)
  have hba : b * a = a * b :=
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨b, hbA⟩ ⟨a, h.a_mem⟩)
  have haK : a ∈ Subgroup.normalizer
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) : Set G) := by
    have ha := h.a_mem_normalizer
    have haC : a ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hba.symm)
    have haLb : a ∈ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp ha y),
        (Subgroup.mem_normalizer_iff.mp haC y)]
    exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ haLb
  exact inducesStdKind_field_of_ree ((Item87Proof.residual_le _).trans inf_le_left)
    h.a_mem_normalizer haK ha3 hout hk₁ hKf e hKbar

end CFSG.RankThree.PartTwo.Sec8
