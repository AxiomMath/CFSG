module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGK1ADvd
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSU
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
public import CFSG.RankThree.PartOne.CTP.SeitzUSplit
public import CFSG.RankThree.PartTwo.KFacts.KS14SzClassical

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag

private theorem twsur_exists_maxElemAb_le {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ f + 1) {A : Subgroup ↥(unitarySU 2 f K n)} (hA : IsElemAbelian p A) :
    ∃ M : Subgroup ↥(unitarySU 2 f K n), SUTB.MaxElemAb p M ∧ A ≤ M := by
  classical
  have : Finite K := h.finite
  set Q : Subgroup ↥(unitarySU 2 f K n) → Prop := fun E =>
    A ≤ E ∧ (∀ a ∈ E, a ^ p = 1) ∧ ∀ a ∈ E, ∀ b ∈ E, a * b = b * a with hQ
  set P : ℕ → Prop := fun k => ∃ E, Q E ∧ Nat.card E = k with hP
  have hQ0 : Q A :=
    ⟨le_rfl, hA.2, fun a ha b hb =>
      congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)⟩
  have hbound : ∀ k, P k → k ≤ Nat.card ↥(unitarySU 2 f K n) := by
    rintro k ⟨E, -, rfl⟩
    exact Subgroup.card_le_card_group E
  have hP0 : P (Nat.card A) := ⟨_, hQ0, rfl⟩
  set N := Nat.findGreatest P (Nat.card ↥(unitarySU 2 f K n)) with hN
  obtain ⟨E, hE, hEN⟩ : P N := Nat.findGreatest_spec (hbound _ hP0) hP0
  refine ⟨E, ⟨hp, hp2, hpq, hE.2.1, hE.2.2, fun g hg hgE => ?_⟩, hE.1⟩
  set E' := Subgroup.closure ((E : Set ↥(unitarySU 2 f K n)) ∪ {g}) with hE'
  have h1 := OrdPNsU.closure_comm_pow (S := (E : Set ↥(unitarySU 2 f K n)) ∪ {g}) (p := p)
    (by
      rintro x (hx | hx) y (hy | hy)
      · exact hE.2.2 x hx y hy
      · rw [Set.mem_singleton_iff.mp hy]; exact (hgE x hx).symm
      · rw [Set.mem_singleton_iff.mp hx]; exact hgE y hy
      · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
    (by
      rintro x (hx | hx)
      · exact hE.2.1 x hx
      · rw [Set.mem_singleton_iff.mp hx]; exact hg)
  have hEE' : E ≤ E' := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hQ' : Q E' := ⟨hE.1.trans hEE', h1.2, h1.1⟩
  have hcard : Nat.card E' ≤ Nat.card E := by
    rw [hEN]
    exact Nat.le_findGreatest (hbound _ ⟨E', hQ', rfl⟩) ⟨E', hQ', rfl⟩
  have heq : E = E' := Subgroup.eq_of_le_of_card_ge hEE' hcard
  rw [heq]
  exact Subgroup.subset_closure (Or.inr rfl)

private theorem twsur_ker_no_torsion {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 1 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) :
    ∀ z ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker, z ^ p = 1 → z = 1 := by
  intro z hz hzp
  by_contra hz1
  have hord : orderOf z = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_iff_pow_eq_one.mpr hzp) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hpdvd : p ∣ Nat.card ↥((LargeEvenProjMk (unitarySU 2 n K d)).ker) := by
    have h := orderOf_dvd_natCard (⟨z, hz⟩ : ↥((LargeEvenProjMk (unitarySU 2 n K d)).ker))
    rwa [Subgroup.orderOf_mk z hz, hord] at h
  have hdvd : Nat.card ↥((LargeEvenProjMk (unitarySU 2 n K d)).ker) ∣ 2 ^ n + 1 := by
    rw [LargeEvenProjMk, QuotientGroup.ker_mk']
    exact card_scalars_statedSU_dvd hK hd
  exact not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
    (hpdvd.trans hdvd)

private theorem twsur_su_order_three_exists {K : Type} [Field K] {n d : ℕ} (hd : 6 ≤ d) :
    ∃ y : LargeEvenProj (unitarySU 2 n K d), orderOf y = 3 :=
  CFSG.RankThree.PartTwo.KFacts.KS14.exists_orderOf_eq_three_statedProj_statedSU
    (K := K) (n := d) (q := 2 ^ n) (by omega) (by positivity)

theorem ggTwSU_rankLE_rec_of_dvd_sub_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {n d r p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd1 : 1 ≤ d)
    (hd : 2 * r ≤ d ∧ d ≤ 2 * r + 1) (hpq : p ∣ 2 ^ n - 1) :
    GGElemAbelianRankLE (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) p r := by
  change GGElemAbelianRankLE (LargeEvenProj (unitarySU 2 n K d)) p r
  intro E hE
  have hF : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hpq' : ¬ p ∣ 2 ^ n + 1 :=
    not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have hker := twsur_ker_no_torsion (K := K) (n := n) (d := d) hK hd1 hp hp2 hpq
  obtain ⟨A, hAmap, -, hA, hAcard⟩ := TableBUE.exists_lift_of_noTorsion
    (π := LargeEvenProjMk (unitarySU 2 n K d))
    (QuotientGroup.mk'_surjective _) hp hker hE
  obtain ⟨M, hM, hAM⟩ := twsur_exists_maxElemAb_le hF hp hp2 hpq' hA
  have hord : CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n p = 2 :=
    CFSG.RankThree.PartOne.CTP.ordNegQ_eq_two_of_dvd_sub_one
      Nat.prime_two hp hp2 hpq
  have hdiv : d / CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n p = r := by
    rw [hord]
    omega
  calc Nat.card E = Nat.card A := hAcard.symm
    _ ≤ Nat.card M := Nat.card_le_card_of_injective
        (Subgroup.inclusion hAM) (Subgroup.inclusion_injective hAM)
    _ ≤ p ^ (d / CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n p) :=
        OrdPNsU.card_le_pow_ordNegQ hF hM
    _ = p ^ r := by rw [hdiv]

theorem ggTwSU_rankLE_rec {K : Type} [Field K] [Finite K] [CharP K 2] {n d r : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hr : 3 ≤ r)
    (hd : 2 * r ≤ d ∧ d ≤ 2 * r + 1) (h3 : 3 ∣ 2 ^ n - 1) :
    GGElemAbelianRankLE (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) 3 r :=
  ggTwSU_rankLE_rec_of_dvd_sub_one Nat.prime_three (by norm_num) hK hn (by omega) hd h3

theorem pow_le_card_of_selfCent_unitary_split {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    {E : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hE : IsElemAbelian p E)
    (hsc : ∀ g : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) (hEne : E ≠ ⊥) :
    p ^ (d / 2) ≤ Nat.card E := by
  change Subgroup (LargeEvenProj (unitarySU 2 n K d)) at E
  change IsElemAbelian p E at hE
  change (∀ g : LargeEvenProj (unitarySU 2 n K d),
    (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) at hsc
  have hF : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hpnot : ¬ p ∣ 2 ^ n + 1 :=
    not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have hker := twsur_ker_no_torsion (K := K) (n := n) (d := d) hK hd hp hp2 hpq
  obtain ⟨A, hAmap, -, hA, hAcard⟩ := TableBUE.exists_lift_of_noTorsion
    (π := LargeEvenProjMk (unitarySU 2 n K d))
    (QuotientGroup.mk'_surjective _) hp hker hE
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAmax : SUTB.MaxElemAb p A :=
    ⟨hp, hp2, hpnot, hA.2, hAcomm, fun g hg hgc => by
      have hgE : LargeEvenProjMk (unitarySU 2 n K d) g ∈ E := by
        apply hsc
        · intro e he
          obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp (hAmap.symm ▸ he)
          rw [← map_mul, ← map_mul, hgc a ha]
        · rw [← map_pow, hg, map_one]
      obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp (hAmap.symm ▸ hgE)
      have hmem : g⁻¹ * a ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, haeq, inv_mul_cancel]
      have hcomm : Commute g a := hgc a ha
      have hpow : (g⁻¹ * a) ^ p = 1 := by
        rw [hcomm.inv_left.mul_pow, inv_pow, hg, inv_one, hA.2 a ha, one_mul]
      have hga : g = a := inv_mul_eq_one.mp (hker (g⁻¹ * a) hmem hpow)
      rw [hga]
      exact ha⟩
  have hord : CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n p = 2 :=
    CFSG.RankThree.PartOne.CTP.ordNegQ_eq_two_of_dvd_sub_one
      Nat.prime_two hp hp2 hpq
  have hne : ∃ c ∈ A, c ≠ 1 := by
    have hex : ∃ c ∈ E, c ≠ 1 := by
      by_contra h
      push Not at h
      exact hEne ((Subgroup.eq_bot_iff_forall E).mpr (fun x hx => h x hx))
    obtain ⟨c, hc, hc1⟩ := hex
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp (hAmap.symm ▸ hc)
    refine ⟨a, ha, ?_⟩
    intro ha1
    apply hc1
    rw [← haeq, ha1, map_one]
  calc p ^ (d / 2) = p ^ (d / CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n p) := by
        rw [hord]
    _ ≤ Nat.card A := OrdPNsU.pow_ordNegQ_le_card hF hAmax hne
    _ = Nat.card E := hAcard

theorem ggTwSU_scRank_rec {K : Type} [Field K] [Finite K] [CharP K 2] {n d r : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hr : 3 ≤ r)
    (hd : 2 * r ≤ d ∧ d ≤ 2 * r + 1) (h3 : 3 ∣ 2 ^ n - 1) :
    GGSelfCentRankGE 3 r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  change GGSelfCentRankGE 3 r (LargeEvenProj (unitarySU 2 n K d))
  intro E hE hsc
  have hEne : E ≠ ⊥ := by
    intro hbot
    obtain ⟨y, hy3⟩ := twsur_su_order_three_exists (K := K) (n := n) (d := d) (by omega)
    have hyE : y ∈ E := hsc y (fun e he => by
      rw [hbot, Subgroup.mem_bot] at he
      rw [he, mul_one, one_mul]) (by rw [← hy3, pow_orderOf_eq_one])
    rw [hbot, Subgroup.mem_bot] at hyE
    rw [hyE, orderOf_one] at hy3
    omega
  have hdiv : d / 2 = r := by omega
  rw [← hdiv]
  exact pow_le_card_of_selfCent_unitary_split hK hn (by omega) Nat.prime_three
    (by norm_num) h3 hE hsc hEne

end CFSG.StandardType

end
