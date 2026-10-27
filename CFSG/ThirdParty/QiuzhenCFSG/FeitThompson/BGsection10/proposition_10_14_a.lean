module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_13_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
private theorem CFSG.section10_generatorRank_le_natCard
    (H : Type*) [Group H] [Finite H] :
    generatorRank H ≤ Nat.card H := by
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨S, hS_card, _hS_top⟩ := Group.rank_spec H
  calc
    generatorRank H = Group.rank H := generatorRank_eq_group_rank H
    _ = S.card := by rw [← hS_card]
    _ ≤ Fintype.card H := by simpa using Finset.card_le_univ S
    _ = Nat.card H := by simp [Nat.card_eq_fintype_card]

private theorem CFSG.section10_primeRank_le_natCard
    {q : ℕ} (H : Type*) [Group H] [Finite H] :
    primeRank q H ≤ Nat.card H := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := H), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section10_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)

private theorem CFSG.section10_not_isCyclic_of_two_le_generatorRank
    {H : Type*} [Group H] [Finite H] (hHrank : 2 ≤ generatorRank H) :
    ¬ IsCyclic H := by
  intro hcyc
  have hle : generatorRank H ≤ 1 := generatorRank_le_one_of_isCyclic (G := H) hcyc
  omega

private theorem CFSG.section10_exists_pSubgroup_two_le_generatorRank_of_two_le_groupRank
    {R : Type*} [Group R] [Finite R] (hrank : 2 ≤ groupRank R) :
    ∃ q : Nat.Primes, ∃ A : Subgroup R,
      IsPGroup q.val A ∧ IsMulCommutative A ∧ 2 ≤ generatorRank A := by
  let S : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hrank' : 1 < sSup S := by
    exact lt_of_lt_of_le (by decide : 1 < 2) (by simpa [groupRank, S] using hrank)
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hqprime, hnq⟩
    exact hnq.trans (section10_primeRank_le_natCard (q := q) R)
  have hSnonempty : S.Nonempty := by
    by_contra hS
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have : ¬ 1 < sSup S := by simp [hSempty]
    exact this hrank'
  have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hSnonempty hSbdd
  rcases hsSup_mem with ⟨q, hqprime, hsSup_le⟩
  have hqrank : 1 < primeRank q R := lt_of_lt_of_le hrank' hsSup_le
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hqrank' : 1 < sSup T := by
    simpa [primeRank, T] using hqrank
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section10_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 1 < sSup T := by simp [hTempty]
    exact this hqrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨A, hAq, hAcomm, htSup_le⟩
  exact ⟨⟨q, hqprime⟩, A, hAq, hAcomm,
    Nat.succ_le_of_lt (lt_of_lt_of_le hqrank' htSup_le)⟩

private theorem CFSG.section10_elementaryAbelian_card_ge_pow_generatorRank
    {p : ℕ} [Fact p.Prime]
    (H : Type*) [Group H] [Finite H] [IsElementaryAbelian p H] :
    p ^ generatorRank H ≤ Nat.card H := by
  let : CommGroup H := IsMulCommutative.instCommGroup
  let : AddCommGroup (Additive H) := Additive.addCommGroup
  have hcard : Nat.card H = p ^ Module.finrank (ZMod p) (Additive H) := by
    calc
      Nat.card H = Nat.card (Additive H) := (Nat.card_congr Additive.toMul).symm
      _ = p ^ Module.finrank (ZMod p) (Additive H) :=
        by simpa [ZMod.card] using
          Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive H)
  have hgr_le_finrank : generatorRank H ≤ Module.finrank (ZMod p) (Additive H) :=
    generatorRank_le_finrank_of_elementaryAbelian (p := p) H
  rw [hcard]
  exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hgr_le_finrank

private theorem CFSG.section10_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 2) :
    2 ≤ generatorRank A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  rw [hA] at hcard_dvd
  have hle_rank : 2 ≤ Group.rank A := by
    exact (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_dvd
  simpa [generatorRank_eq_group_rank] using hle_rank

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_characteristic_of_subgroup_of_isCyclic
    {H : Type*} [Group H] {K : Subgroup H} [IsCyclic H] :
    K.Characteristic := by
  classical
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have hK_le_z : K ≤ Subgroup.zpowers g := by
    intro x _hx
    exact hg x
  obtain ⟨n, hK_eq⟩ := (Subgroup.le_zpowers_iff g K).mp hK_le_z
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
  rw [hK_eq] at hx ⊢
  rcases Subgroup.mem_zpowers_iff.mp hx with ⟨k, rfl⟩
  rw [map_zpow]
  apply Subgroup.zpow_mem
  rw [map_pow]
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic φ.toMonoidHom
  rw [hm g]
  have hpow : (g ^ m) ^ n = (g ^ n) ^ m := by
    rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul, zpow_natCast]
  rw [hpow]
  exact (Subgroup.zpowers (g ^ n)).zpow_mem (Subgroup.mem_zpowers (g ^ n)) m

private theorem CFSG.section10_omega1_isElementaryAbelian_of_commutative
    {p : ℕ} [Fact p.Prime]
    (H : Type*) [Group H] [IsMulCommutative H] :
    IsElementaryAbelian p (omega₁ (G := H) (p := p)) := by
  let : CommGroup H := IsMulCommutative.instCommGroup
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  exact
    Subgroup.closure_induction (k := {y : H | y ^ (p ^ 1) = 1})
      (p := fun z _hz => z ^ p = 1) (x := x) (by
        intro y hy
        simpa [pow_one] using hy) (by simp) (by
        intro y z _ _ hy hz
        calc
          (y * z) ^ p = y ^ p * z ^ p := by
            simpa using mul_pow y z p
          _ = 1 := by simp [hy, hz]) (by
        intro y _ hy
        simp [hy]) x.property

private theorem CFSG.section10_omega1_card_eq_card_quotient_frattini_of_commutative
    {p : ℕ} [Fact p.Prime]
    (H : Type*) [Group H] [Finite H] [IsMulCommutative H] [Fact (IsPGroup p H)] :
    Nat.card (omega₁ (G := H) (p := p)) = Nat.card (H ⧸ frattini H) := by
  classical
  let : CommGroup H := IsMulCommutative.instCommGroup
  let φ : H →* H := powMonoidHom p
  have hφker : φ.ker = omega₁ (G := H) (p := p) := by
    ext x
    constructor
    · intro hx
      change x ∈ Subgroup.closure {y : H | y ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [φ, pow_one] using hx
    · intro hx
      refine
        Subgroup.closure_induction (k := {y : H | y ^ (p ^ 1) = 1})
          (p := fun z _hz => z ∈ φ.ker) (x := x) (by
            intro y hy
            simpa [φ, pow_one] using hy) (by simp [φ]) (by
            intro y z _ _ hy hz
            have hy' : y ^ p = 1 := by simpa [φ] using hy
            have hz' : z ^ p = 1 := by simpa [φ] using hz
            simp [φ, mul_pow, hy', hz']) (by
            intro y _ hy
            exact φ.ker.inv_mem hy) hx
  have hφrange : φ.range = frattini H := by
    have hcomm_top :
        (⊤ : Subgroup H) ≤ Subgroup.centralizer (((⊤ : Subgroup H) : Set H)) := by
      intro x _hx
      rw [Subgroup.mem_centralizer_iff]
      intro y _hy
      exact mul_comm y x
    have hcomm_bot : _root_.commutator H = ⊥ := by
      have htop_comm_bot : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hcomm_top
      simpa [_root_.commutator_def] using htop_comm_bot
    have hderived_bot : derivedSubgroup H = ⊥ := by
      change derivedSeries H 1 = ⊥
      rw [derivedSeries_one]
      exact hcomm_bot
    have hrange :
        Set.range (fun x : H => x ^ p) = ((φ.range : Subgroup H) : Set H) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by simp [φ]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by simpa [φ] using hx⟩
    have hfrattini : frattini H = φ.range := by
      calc
        frattini H =
            Subgroup.closure ((derivedSubgroup H : Set H) ∪ Set.range (fun x : H => x ^ p)) := by
              simpa using (lemma_1_7_d (R := H) (p := p))
        _ = Subgroup.closure (Set.range (fun x : H => x ^ p)) := by
              rw [hderived_bot]
              simp
        _ = Subgroup.closure ((φ.range : Subgroup H) : Set H) := by rw [hrange]
        _ = φ.range := by simpa using (Subgroup.closure_eq (K := φ.range))
    exact hfrattini.symm
  have hcard_range :
      Nat.card (H ⧸ φ.ker) = Nat.card φ.range := by
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hmul_ker :
      Nat.card H = Nat.card (frattini H) * Nat.card (omega₁ (G := H) (p := p)) := by
    calc
      Nat.card H = Nat.card (H ⧸ φ.ker) * Nat.card φ.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := φ.ker)
      _ = Nat.card φ.range * Nat.card φ.ker := by rw [hcard_range]
      _ = Nat.card (frattini H) * Nat.card (omega₁ (G := H) (p := p)) := by
        rw [hφrange, hφker]
  have hmul_frattini :
      Nat.card H = Nat.card (frattini H) * Nat.card (H ⧸ frattini H) := by
    calc
      Nat.card H = Nat.card (H ⧸ frattini H) * Nat.card (frattini H) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := frattini H)
      _ = Nat.card (frattini H) * Nat.card (H ⧸ frattini H) := by
        rw [Nat.mul_comm]
  have hΦpos : 0 < Nat.card (frattini H) := Nat.card_pos (α := frattini H)
  have hmul_eq :
      Nat.card (frattini H) * Nat.card (omega₁ (G := H) (p := p)) =
        Nat.card (frattini H) * Nat.card (H ⧸ frattini H) :=
    hmul_ker.symm.trans hmul_frattini
  exact Nat.eq_of_mul_eq_mul_left hΦpos hmul_eq


private theorem CFSG.section10_primeRank_le_of_equiv
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (q : ℕ) (e : R ≃* S) :
    primeRank q S ≤ primeRank q R := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card S, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans <| (section10_generatorRank_le_natCard A).trans
      (Subgroup.card_le_card_group A)
  by_cases hT : T.Nonempty
  · have hsSup_mem : sSup T ∈ T := Nat.sSup_mem hT hTbdd
    rcases hsSup_mem with ⟨A, hAq, hAcomm, hsSup_le⟩
    let A' : Subgroup R := A.map e.symm.toMonoidHom
    have hA'q : IsPGroup q A' :=
      IsPGroup.map (p := q) (H := A) hAq e.symm.toMonoidHom
    have hA'comm : IsMulCommutative A' := by
      let : IsMulCommutative A := hAcomm
      infer_instance
    have hgen_le : generatorRank A ≤ generatorRank A' := by
      let eA : A ≃* A' :=
        Subgroup.equivMapOfInjective A e.symm.toMonoidHom e.symm.injective
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact le_of_eq (Group.rank_congr eA)
    have hmem : generatorRank A ∈
        {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧
          n ≤ generatorRank B} :=
      ⟨A', hA'q, hA'comm, hgen_le⟩
    have hprimeRank : generatorRank A ≤ primeRank q R := by
      rw [primeRank]
      refine le_csSup ?_ hmem
      refine ⟨Nat.card R, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
      exact hnB.trans <| (section10_generatorRank_le_natCard B).trans
        (Subgroup.card_le_card_group B)
    rw [primeRank]
    exact hsSup_le.trans hprimeRank
  · have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hSet :
        {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧
          n ≤ generatorRank A} = ∅ := by
      simpa [T] using hTempty
    rw [primeRank, hSet]
    simp

public theorem CFSG.section10_groupRank_le_of_equiv
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (e : R ≃* S) :
    groupRank S ≤ groupRank R := by
  let U : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S}
  have hUbdd : BddAbove U := by
    refine ⟨Nat.card S, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact hnq.trans (section10_primeRank_le_natCard (q := q) S)
  by_cases hU : U.Nonempty
  · have hsSup_mem : sSup U ∈ U := Nat.sSup_mem hU hUbdd
    rcases hsSup_mem with ⟨q, hq, hsSup_le⟩
    have hqle : primeRank q S ≤ groupRank R := by
      rw [groupRank]
      refine (section10_primeRank_le_of_equiv (R := R) (S := S) q e).trans ?_
      refine le_csSup ?_ ⟨q, hq, le_rfl⟩
      refine ⟨Nat.card R, ?_⟩
      intro n hn
      rcases hn with ⟨r, _hr, hnr⟩
      exact hnr.trans (section10_primeRank_le_natCard (q := r) R)
    rw [groupRank]
    exact hsSup_le.trans hqle
  · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
    have hSet :
        {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S} = ∅ := by
      simpa [U] using hUempty
    rw [groupRank, hSet]
    simp

public theorem CFSG.section10_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank
    {p : ℕ} {R : Type*} [Group R] [Finite R] (hrank : 3 ≤ primeRank p R) :
    ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧ 3 ≤ generatorRank A := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hrank' : 2 < sSup T := by
    exact lt_of_lt_of_le (by decide : 2 < 3) (by simpa [primeRank, T] using hrank)
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section10_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 2 < sSup T := by simp [hTempty]
    exact this hrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨A, hAp, hAcomm, htSup_le⟩
  exact ⟨A, hAp, hAcomm, Nat.succ_le_of_lt (lt_of_lt_of_le hrank' htSup_le)⟩

omit [IsMinCE G] in
public theorem CFSG.section10_prime_dvd_card_of_pSubgroup_two_le_generatorRank
    {p : ℕ} [Fact p.Prime] {B : Subgroup G}
    (hBp : IsPGroup p B) (hBgen : 2 ≤ generatorRank B) :
    p ∣ Nat.card G := by
  have hBnoncyc : ¬ IsCyclic B := section10_not_isCyclic_of_two_le_generatorRank hBgen
  have hBnontrivial : Nontrivial B := by
    by_contra hnt
    let : Subsingleton B := not_nontrivial_iff_subsingleton.mp hnt
    exact hBnoncyc (isCyclic_of_subsingleton (α := B))
  obtain ⟨n, hn_pos, hBcard⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := B) (hG := hBp)).mp hBnontrivial
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos)
  have hp_dvd_B : p ∣ Nat.card B := by
    rw [hBcard, pow_succ']
    exact dvd_mul_right p (p ^ m)
  exact hp_dvd_B.trans (Subgroup.card_subgroup_dvd_card B)

omit [IsMinCE G] in
private theorem CFSG.section10_generatorRank_le_groupRank_of_subgroup
    {q : ℕ} (hq : Nat.Prime q) {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A) :
    generatorRank A ≤ groupRank K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' := by
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    let : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  have hqrankK : generatorRank A ≤ primeRank q K := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card K, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <| (section10_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
    · exact ⟨A', hA'p, hA'comm, by simp [hgen_eq]⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (section10_primeRank_le_natCard (q := r) K)
  · exact ⟨q, hq, hqrankK⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_groupRank_at_least_two_of_noncyclic_pgroup
    {p : ℕ} [Fact p.Prime] (R : Type*) [Group R] [Finite R] [Fact (IsPGroup p R)]
    (hpodd : p ≠ 2) (hncyc : ¬ IsCyclic R) :
    2 ≤ groupRank R := by
  classical
  obtain ⟨E, _hEnorm, hEcard, hEelem⟩ := lemma_4_5_a (R := R) (p := p) hpodd hncyc
  let : IsElementaryAbelian p E := hEelem
  have hEgen : 2 ≤ generatorRank E :=
    section10_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq (p := p) hEcard
  have hprank : 2 ≤ primeRank p R := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card R, ?_⟩
      intro n hn
      rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
      exact hnA.trans <|
        (section10_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
    · exact ⟨E, IsElementaryAbelian.isPGroup p E, inferInstance, hEgen⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact hnq.trans (section10_primeRank_le_natCard (q := q) R)
  · exact ⟨p, Fact.out, hprank⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_normalizer_le_normalizer_map_subtype_of_characteristic
    (H : Subgroup G) (K : Subgroup H) [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (((K : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem ((K : Subgroup H).map H.subtype)
    (Subgroup.normalizer (H : Set G)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, by simp⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := hxComap
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

omit [IsMinCE G] in
public theorem CFSG.section10_primeRank_le_groupRank_sylow
    {p : Nat.Primes} (S : Sylow p.val G) :
    primeRank p.val G ≤ groupRank (S : Subgroup G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := p.val) (G := G), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, hAp, hAcomm, hnA⟩
    obtain ⟨Q, hAQ⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
    let Aconj : Subgroup G := A.map (MulAut.conj g).toMonoidHom
    have hAconj_le_S : Aconj ≤ (S : Subgroup G) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨a, haA, rfl⟩
      have haQ : a ∈ (Q : Subgroup G) := hAQ haA
      have hmem : (MulAut.conj g) a ∈ ((g • Q : Sylow p.val G) : Subgroup G) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) (Q : Subgroup G) haQ
      simpa [hg] using hmem
    have hAconj_p : IsPGroup p.val Aconj := by
      exact hAp.of_equiv
        (Subgroup.equivMapOfInjective (f := (MulAut.conj g).toMonoidHom) A
          (EquivLike.injective (MulAut.conj g)))
    have hAconj_comm : IsMulCommutative Aconj := by
      let : IsMulCommutative A := hAcomm
      simpa [Aconj] using
        (Subgroup.map_isMulCommutative (f := (MulAut.conj g).toMonoidHom) (H := A))
    have hgen_eq : generatorRank A = generatorRank Aconj := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact Group.rank_congr
        (Subgroup.equivMapOfInjective (f := (MulAut.conj g).toMonoidHom) A
          (EquivLike.injective (MulAut.conj g)))
    exact hnA.trans <| by
      rw [hgen_eq]
      exact section10_generatorRank_le_groupRank_of_subgroup
        (G := G) (q := p.val) p.property hAconj_le_S hAconj_p hAconj_comm


private theorem CFSG.section10_prime_not_dvd_index_of_sup_hall
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes}
    {K U : Subgroup H} [K.Normal] {p : Nat.Primes}
    (hKHall : IsHallSubgroup π K) (hpπ : p ∉ π)
    (hKU : K ⊔ U = ⊤) :
    ¬ p.val ∣ U.index := by
  intro hpU
  have hrel_eq :
      U.relIndex (U ⊔ K) = (U ⊓ K).relIndex K := by
    have hK_rel :
        K.relIndex (U ⊔ K) = (U ⊓ K).relIndex U := by
      calc
        K.relIndex (U ⊔ K) = K.relIndex U := by
          simp
        _ = (U ⊓ K).relIndex U := by
          symm
          simpa [inf_comm] using (Subgroup.inf_relIndex_left (H := U) (K := K))
    have hmul :
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
          (U ⊓ K).relIndex K * (U ⊓ K).relIndex U := by
      calc
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
            (U ⊓ K).relIndex (U ⊔ K) := by
          exact
            Subgroup.relIndex_mul_relIndex (H := U ⊓ K) (K := U) (L := U ⊔ K)
              inf_le_left le_sup_left
        _ = (U ⊓ K).relIndex K * K.relIndex (U ⊔ K) := by
          symm
          exact
            Subgroup.relIndex_mul_relIndex (H := U ⊓ K) (K := K) (L := U ⊔ K)
              inf_le_right le_sup_right
        _ = (U ⊓ K).relIndex K * (U ⊓ K).relIndex U := by
          rw [hK_rel]
    have hrel_pos : 0 < (U ⊓ K).relIndex U := by
      have hrel_ne_zero : (U ⊓ K).relIndex U ≠ 0 := by
        dsimp [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite (H := (U ⊓ K).subgroupOf U)
      exact Nat.pos_of_ne_zero hrel_ne_zero
    have hmul' :
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
          (U ⊓ K).relIndex U * (U ⊓ K).relIndex K := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    exact Nat.eq_of_mul_eq_mul_left hrel_pos hmul'
  have hidx_eq : U.relIndex (U ⊔ K) = U.index := by
    rw [show U ⊔ K = ⊤ by simpa [sup_comm] using hKU]
    exact Subgroup.relIndex_top_right (H := U)
  have hrel_dvd_cardK : U.relIndex (U ⊔ K) ∣ Nat.card K := by
    rw [hrel_eq]
    exact Subgroup.relIndex_dvd_card (H := U ⊓ K) (K := K)
  have hidx_dvd_cardK : U.index ∣ Nat.card K := by
    simpa [hidx_eq] using hrel_dvd_cardK
  exact hpπ (hKHall.p_in_pi_of_p_dvd_card p (hpU.trans hidx_dvd_cardK))

/-- If `p ∉ β(M)` has rank two, then the normalizer in `M` of any
Sylow subgroup of `M'` has `p`-rank at least two. This is the
Frattini-normalizer rank bridge used in Lemma 13.1. -/
public theorem CFSG.section10_primeRank_normalizer_of_derived_sylow_ge_of_not_beta_primeRank
    {M : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpβ : p ∉ section10BetaPrimes M)
    (X : Sylow q.val (ambientDerivedSubgroup M))
    (hprank : primeRank p.val M = 2) :
    2 ≤ primeRank p.val
      (subgroupNormalizerIn M
        (section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X : Set G)) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let Dg : Subgroup G := ambientDerivedSubgroup M
  let XG : Subgroup G := section10AmbientSylowSubgroup Dg X
  let U : Subgroup G := subgroupNormalizerIn M (XG : Set G)
  let Usub : Subgroup M := U.subgroupOf M
  have hU_le_M : U ≤ M := by
    simpa [U, XG] using section10_subgroupNormalizerIn_le M (XG : Set G)
  have hKU :
      section10MbetaSubgroup M ⊔ Usub = ⊤ := by
    simpa [Usub, U, XG, Dg] using
      section10_mbeta_sup_ambient_normalizer_of_derived_sylow
        (G := G) hM X
  have hUsub_not_index : ¬ p.val ∣ Usub.index :=
    section10_prime_not_dvd_index_of_sup_hall
      (H := M) (π := section10BetaPrimes M)
      ((lemma_10_8_a (G := G) hM).2) hpβ hKU
  let S : Sylow p.val Usub := Classical.choice (Sylow.nonempty (p := p.val) (G := Usub))
  let SMsub : Subgroup M := (S : Subgroup Usub).map Usub.subtype
  have hSMsub_p : IsPGroup p.val SMsub := by
    simpa [SMsub] using
      IsPGroup.map (p := p.val) (H := (S : Subgroup Usub)) S.isPGroup' Usub.subtype
  have hSMsub_not_index : ¬ p.val ∣ SMsub.index := by
    have hidx :
        SMsub.index = (S : Subgroup Usub).index * Usub.index := by
      simpa [SMsub] using
        (Subgroup.index_map_subtype (H := Usub) (K := (S : Subgroup Usub)))
    rw [hidx]
    exact Nat.Prime.not_dvd_mul p.property S.not_dvd_index hUsub_not_index
  let SM : Sylow p.val M := hSMsub_p.toSylow hSMsub_not_index
  have hSM_eq : (SM : Subgroup M) = SMsub := by
    simp [SM, SMsub, IsPGroup.toSylow_coe]
  have hM_rank : 2 ≤ groupRank (SM : Subgroup M) := by
    have htwo : 2 ≤ primeRank p.val M := by omega
    exact htwo.trans (section10_primeRank_le_groupRank_sylow (G := M) SM)
  have hSMsub_rank : 2 ≤ groupRank SMsub := by
    rw [← hSM_eq]
    exact hM_rank
  have hS_rank : 2 ≤ groupRank (S : Subgroup Usub) := by
    let eS : (S : Subgroup Usub) ≃* SMsub :=
      Subgroup.equivMapOfInjective
        (f := Usub.subtype) (S : Subgroup Usub) Usub.subtype_injective
    exact hSMsub_rank.trans
      (section10_groupRank_le_of_equiv (R := (S : Subgroup Usub)) (S := SMsub) eS)
  have hUsub_rank : 2 ≤ primeRank p.val Usub :=
    hS_rank.trans <|
      (section10_groupRank_le_primeRank_of_isPGroup_local
        (R := (S : Subgroup Usub)) (p := p.val) S.isPGroup').trans
        (section8_primeRank_le_of_subgroup (G := Usub) (S : Subgroup Usub) p.val)
  let eU : Usub ≃* U :=
    Subgroup.subgroupOfEquivOfLe (H := U) (K := M) hU_le_M
  exact hUsub_rank.trans
    (section10_primeRank_le_of_equiv (R := U) (S := Usub) p.val eU.symm)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_isElementaryAbelian_of_le
    {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    [IsElementaryAbelian p K] (hHK : H ≤ K) :
    IsElementaryAbelian p H := by
  refine
    { toIsMulCommutative := by
        exact
          { is_comm := ⟨fun x y =>
              Subtype.ext <|
                setLike_mul_comm (s := K)
                  (hHK x.2) (hHK y.2)⟩ }
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  let xK : K := ⟨(x : G), hHK x.2⟩
  have hxpow : xK ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p K) xK
  simpa [xK] using congrArg Subtype.val hxpow

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_isElementaryAbelian_map_of_injective
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} [IsElementaryAbelian p A]
    {G' : Type*} [Group G'] (f : G →* G') :
    IsElementaryAbelian p (A.map f) := by
  refine
    { toIsMulCommutative := by
        simpa using (Subgroup.map_isMulCommutative (f := f) (H := A))
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hyA, hyx⟩
  let yA : A := ⟨y, hyA⟩
  have hypow : yA ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) yA
  have hx_eq : (x : G') = f y := by simpa using hyx.symm
  calc
    (x : G') ^ p = (f y) ^ p := by simp [hx_eq]
    _ = f (y ^ p) := by simp
    _ = 1 := by simpa using congrArg f (congrArg Subtype.val hypow)

omit [IsMinCE G] in
public theorem CFSG.section10_exists_elementaryAbelian_rank_two_subgroup_of_pgroup_rank_two
    {p : ℕ} [Fact p.Prime] {R : Subgroup G}
    (hRp : IsPGroup p R) (hRrank : 2 ≤ groupRank R) :
    ∃ A : Subgroup G, A ≤ R ∧ A ∈ elementaryAbelianSubgroupsOfRank p 2 G := by
  classical
  obtain ⟨_q, A₀, _hA₀q, hA₀comm, hA₀gen⟩ :=
    section10_exists_pSubgroup_two_le_generatorRank_of_two_le_groupRank (R := R) hRrank
  have hA₀p : IsPGroup p A₀ := hRp.to_subgroup A₀
  let Ωsub : Subgroup A₀ := omega₁ (G := A₀) (p := p)
  have : Fact (IsPGroup p A₀) := ⟨hA₀p⟩
  have hΩelem : IsElementaryAbelian p Ωsub := by
    let : IsMulCommutative A₀ := hA₀comm
    simpa [Ωsub] using section10_omega1_isElementaryAbelian_of_commutative (p := p) A₀
  have hΩcard :
      Nat.card Ωsub = Nat.card (A₀ ⧸ frattini A₀) := by
    let : IsMulCommutative A₀ := hA₀comm
    simpa [Ωsub] using
      section10_omega1_card_eq_card_quotient_frattini_of_commutative (p := p) A₀
  have hquot_rank : 2 ≤ generatorRank (A₀ ⧸ frattini A₀) :=
    hA₀gen.trans (generatorRank_le_generatorRank_quotient_frattini (p := p) A₀)
  have hpow_le_quot : p ^ 2 ≤ Nat.card (A₀ ⧸ frattini A₀) := by
    let : IsElementaryAbelian p (A₀ ⧸ frattini A₀) :=
      isElementaryAbelian_quotient_frattini (R := A₀) (p := p)
    calc
      p ^ 2 ≤ p ^ generatorRank (A₀ ⧸ frattini A₀) := by
        exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hquot_rank
      _ ≤ Nat.card (A₀ ⧸ frattini A₀) := by
        exact section10_elementaryAbelian_card_ge_pow_generatorRank
          (p := p) (A₀ ⧸ frattini A₀)
  have hpow_le_Ω : p ^ 2 ≤ Nat.card Ωsub := by
    rw [hΩcard]
    exact hpow_le_quot
  have hΩp : IsPGroup p Ωsub := IsElementaryAbelian.isPGroup p Ωsub
  rcases hΩp.exists_card_eq with ⟨k, hk⟩
  have hk2 : 2 ≤ k := by
    rw [hk] at hpow_le_Ω
    exact
      (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hpow_le_Ω
  have : Ωsub.Normal := by
    let : Ωsub.Characteristic := by
      simpa [Ωsub] using (omega₁_characteristic (G := A₀) (p := p))
    infer_instance
  obtain ⟨C, _hCnorm, hCΩ, hCcard⟩ :=
    lemma_1_22 (G := A₀) p Ωsub inferInstance k hk 2 hk2
  have hCelem : IsElementaryAbelian p C := by
    let : IsElementaryAbelian p Ωsub := hΩelem
    exact section10_isElementaryAbelian_of_le (p := p) hCΩ
  let f : A₀ →* G := R.subtype.comp A₀.subtype
  let B : Subgroup G := C.map f
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext <| Subtype.ext <| by
      simpa [f] using hxy
  have hB_le_R : B ≤ R := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨c, _hc, rfl⟩
    exact ((c : A₀) : R).2
  have hBcard : Nat.card B = p ^ 2 := by
    simpa [B, f, hCcard] using
      Subgroup.card_map_of_injective (K := C) (f := f) hf_inj
  have hBelem : IsElementaryAbelian p B := by
    let : IsElementaryAbelian p C := hCelem
    simpa [B, f] using
      section10_isElementaryAbelian_map_of_injective (G := A₀) (p := p) (A := C) f
  exact ⟨B, hB_le_R, ⟨hBcard, hBelem⟩⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_rankTwoMaximal_subgroupOf_of_le
    {p : Nat.Primes} {A S : Subgroup G} (hAS : A ≤ S)
    (hArankTwo : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G)
    (hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G) :
    A.subgroupOf S ∈ section10RankTwoMaximalElementaryAbelianSubgroups p S := by
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases hArankTwo with ⟨hAcard, hAelem⟩
  rcases hAmax with ⟨_hAelem', hAmax'⟩
  have : IsElementaryAbelian p.val A := hAelem
  have hAsub_card : Nat.card (A.subgroupOf S) = p.val ^ 2 := by
    simpa [hAcard] using
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := S) hAS).toEquiv
  have hAsub_elem : IsElementaryAbelian p.val (A.subgroupOf S) :=
    IsElementaryAbelian.subgroupOf (G := G) (p := p.val) hAS
  have hAsub_max : A.subgroupOf S ∈ maximalElementaryAbelianSubgroups p.val S := by
    refine ⟨hAsub_elem, ?_⟩
    intro B hAB hBelem
    let Bmap : Subgroup G := B.map S.subtype
    have hA_le_Bmap : A ≤ Bmap := by
      intro a ha
      let aS : A.subgroupOf S := ⟨⟨a, hAS ha⟩, ha⟩
      exact Subgroup.mem_map.mpr ⟨aS, hAB aS.2, rfl⟩
    have hBmap_elem : IsElementaryAbelian p.val Bmap := by
      let : IsElementaryAbelian p.val B := hBelem
      simpa [Bmap] using
        section10_isElementaryAbelian_map_of_injective (p := p.val) (A := B) S.subtype
    have hEq : A = Bmap := hAmax' Bmap hA_le_Bmap hBmap_elem
    apply Subgroup.ext
    intro x
    constructor
    · intro hx
      have hxA : ((x : S) : G) ∈ A := hx
      rw [hEq] at hxA
      rcases Subgroup.mem_map.mp hxA with ⟨y, hyB, hyx⟩
      have : y = x := Subtype.ext hyx
      simpa [this] using hyB
    · intro hx
      have hxMap : ((x : S) : G) ∈ Bmap := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [← hEq] at hxMap
      exact hxMap
  exact ⟨⟨hAsub_card, hAsub_elem⟩, hAsub_max⟩

public theorem CFSG.section10_proposition_10_14_a_sylow
    {p : Nat.Primes} (hpβG : section10IdealPrime p G) (P : Sylow p.val G) :
    section10RankTwoMaximalElementaryAbelianSubgroups p P = ∅ := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  rcases hpβG with ⟨hprankG, hnotNarrow⟩
  have hprimeRank_le : 3 ≤ primeRank p.val G := Nat.succ_le_of_lt hprankG
  obtain ⟨A, hAp, hAcomm, hAgen⟩ :=
    section10_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank
      (R := G) hprimeRank_le
  have hpG : p.val ∣ Nat.card G :=
    section10_prime_dvd_card_of_pSubgroup_two_le_generatorRank
      (p := p.val) hAp (le_trans (by decide : 2 ≤ 3) hAgen)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
  have hPrank : 3 ≤ groupRank (P : Subgroup G) := by
    exact hprimeRank_le.trans (section10_primeRank_le_groupRank_sylow (G := G) P)
  ext X
  constructor
  · intro hX
    have hNarrowP : IsNarrowPGroup p.val P := by
      exact
        (theorem_5_3 (p := p.val) hpodd (R := P) P.isPGroup' hPrank).2
          ⟨X, hX.1, hX.2⟩
    exact (hnotNarrow P) hNarrowP
  · intro hX
    exact False.elim hX

public theorem CFSG.section10_proposition_10_14_a_ambient
    {p : Nat.Primes} (hpβG : section10IdealPrime p G) :
    section10RankTwoMaximalElementaryAbelianSubgroups p G = ∅ := by
  classical
  ext A
  constructor
  · intro hA
    rcases hA with ⟨hArankTwo, hAmax⟩
    have hArankTwo' : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G := hArankTwo
    rcases hArankTwo with ⟨_hAcard, hAelem⟩
    have : IsElementaryAbelian p.val A := hAelem
    have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
    obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
    have hASylow :
        A.subgroupOf (S : Subgroup G) ∈ section10RankTwoMaximalElementaryAbelianSubgroups p S :=
      section10_rankTwoMaximal_subgroupOf_of_le (G := G) hAS hArankTwo' hAmax
    have hEmpty : section10RankTwoMaximalElementaryAbelianSubgroups p S = ∅ :=
      section10_proposition_10_14_a_sylow (G := G) hpβG S
    simp [hEmpty] at hASylow
  · intro hA
    exact False.elim hA

public theorem CFSG.section10_pSubgroup_proper_of_min_ce
    {p : ℕ} [Fact p.Prime] {R : Subgroup G} (hRp : IsPGroup p R) :
    R ≠ ⊤ := by
  intro hRtop
  have htop_p : IsPGroup p (⊤ : Subgroup G) :=
    hRp.of_equiv (MulEquiv.subgroupCongr hRtop)
  have hGp : IsPGroup p G :=
    htop_p.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
  have : Group.IsNilpotent G :=
    IsPGroup.isNilpotent (p := p) (G := G) (h := hGp)
  exact IsMinCE.not_solvable (G := G) (inferInstance : Group.IsSolvable G)


end Section10

/-!
# Proposition 10.14(a) from BG Section 10

This file contains Proposition 10.14(a) from BG Section 10.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Proposition 10.14(a). -/
public theorem CFSG.proposition_10_14_a
    {p : Nat.Primes} (hpβG : section10IdealPrime p G) (P : Sylow p.val G) :
    section10RankTwoMaximalElementaryAbelianSubgroups p P = ∅ ∧
      section10RankTwoMaximalElementaryAbelianSubgroups p G = ∅ := by
  exact ⟨section10_proposition_10_14_a_sylow (G := G) hpβG P,
    section10_proposition_10_14_a_ambient (G := G) hpβG⟩

end Section10
