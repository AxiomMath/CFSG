module

public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Chevalley.G2TorusRank

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.Timmesfeld.ExceptionalOrders

theorem factorization_ordG2_of_dvd_sub_one {q r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hq : 0 < q) (hrd : r ∣ q - 1) :
    (ordG2 q).factorization r = 2 * (q - 1).factorization r := by
  rcases eq_or_lt_of_le (Nat.succ_le_iff.mpr hq) with hq1 | hq2
  · subst hq1
    simp [ordG2]
  have hq1 : 1 ≤ q := by omega
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨w, hw⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
    rw [hw]
    have h : (w + 1) ^ 2 = w * (w + 2) + 1 := by ring
    rw [h, Nat.add_sub_cancel]
    have hw1 : w + 1 - 1 = w := by omega
    rw [hw1]
  have hsix : q ^ 6 - 1 = (q - 1) * ((q + 1) * (q ^ 4 + q ^ 2 + 1)) := by
    have hq6 : q ^ 6 = (q ^ 2) ^ 3 := by ring
    have h3 : (q ^ 2) ^ 3 - 1 = (q ^ 2 - 1) * ((q ^ 2) ^ 2 + q ^ 2 + 1) := by
      have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
      obtain ⟨y, hy⟩ : ∃ y, q ^ 2 = y + 1 :=
        ⟨q ^ 2 - 1, (Nat.sub_add_cancel hq2pos).symm⟩
      rw [hy]
      have h : (y + 1) ^ 3 = y * (y ^ 2 + 3 * y + 3) + 1 := by ring
      rw [h, Nat.add_sub_cancel]
      have hy1 : y + 1 - 1 = y := by omega
      rw [hy1]
      ring
    rw [hq6, h3, hsq]
    ring
  have hord : ordG2 q = (q - 1) ^ 2 * (q ^ 6 * (q + 1) ^ 2 * (q ^ 4 + q ^ 2 + 1)) := by
    unfold ordG2
    rw [hsix, hsq]
    ring
  have hA : (q - 1) ^ 2 ≠ 0 := by
    have : 0 < q - 1 := by omega
    positivity
  have hB : q ^ 6 * (q + 1) ^ 2 * (q ^ 4 + q ^ 2 + 1) ≠ 0 := by positivity
  have hrq : ¬ r ∣ q := by
    intro h
    have h1 : r ∣ q - (q - 1) := Nat.dvd_sub h hrd
    have h2 : q - (q - 1) = 1 := by omega
    rw [h2] at h1
    exact hr.not_dvd_one h1
  have hrq1 : ¬ r ∣ q + 1 := by
    intro h
    have h1 : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub h hrd
    have h2 : (q + 1) - (q - 1) = 2 := by omega
    rw [h2] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hrq4 : ¬ r ∣ q ^ 4 + q ^ 2 + 1 := by
    intro h
    have hA' : r ∣ (q - 1) * ((q + 1) * (q ^ 2 + 2)) := dvd_mul_of_dvd_left hrd _
    have hsum : q ^ 4 + q ^ 2 + 1 = (q - 1) * ((q + 1) * (q ^ 2 + 2)) + 3 := by
      obtain ⟨w, hw⟩ : ∃ w, q = w + 1 :=
        ⟨q - 1, (Nat.sub_add_cancel hq1).symm⟩
      rw [hw]
      have hw1 : w + 1 - 1 = w := by omega
      rw [hw1]
      ring
    have h3 : r ∣ 3 := (Nat.dvd_add_right hA').1 (by rwa [← hsum])
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hBfactor : (q ^ 6 * (q + 1) ^ 2 * (q ^ 4 + q ^ 2 + 1)).factorization r = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact hrq (hr.dvd_of_dvd_pow h)
      · exact hrq1 (hr.dvd_of_dvd_pow h)
    · exact hrq4 h
  calc
    (ordG2 q).factorization r = ((q - 1) ^ 2).factorization r +
        (q ^ 6 * (q + 1) ^ 2 * (q ^ 4 + q ^ 2 + 1)).factorization r := by
      rw [hord, Nat.factorization_mul hA hB, Finsupp.add_apply]
    _ = 2 * (q - 1).factorization r := by
      rw [Nat.factorization_pow, hBfactor, Finsupp.smul_apply, smul_eq_mul, add_zero]

section Certificates


theorem exists_sylow_abelian_adjointGroup_G2
    {K : Type} [Field K] [Finite K] {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrd : r ∣ Nat.card K - 1) :
    ∃ T : Subgroup (adjointGroup .G2 K),
      T ≤ (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) ∧
      Nat.card T = (Nat.card K - 1) ^ 2 ∧
      IsMulCommutative ↥T ∧
      (∀ S : Sylow r (adjointGroup .G2 K),
        Nat.card S = r ^ (2 * (Nat.card K - 1).factorization r) ∧
        IsMulCommutative ↥S) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  let G := adjointGroup .G2 K
  let q := Nat.card K
  have hqpos : 0 < q := Nat.card_pos
  have hTA : torusGroup .G2 K ≤ adjointGroup .G2 K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact torusElt_mem_adjointGroup i t
  let T : Subgroup G := (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)
  have hTcard : Nat.card T = (q - 1) ^ 2 := by
    change Nat.card ((torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)) = (q - 1) ^ 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv]
    exact card_torusGroup_G2
  have hHcomm : IsMulCommutative (torusGroup .G2 K) := by
    obtain ⟨eT, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
    refine IsMulCommutative.of_comm fun a b => eT.symm.injective ?_
    rw [map_mul, map_mul, mul_comm]
  have hTcomm : IsMulCommutative ↥T := by
    change IsMulCommutative ↥((torusGroup .G2 K).subgroupOf (adjointGroup .G2 K))
    infer_instance
  have hGcard : Nat.card G = ordG2 q :=
    card_adjointGroup_G2
  have hfactG : (Nat.card G).factorization r = 2 * (q - 1).factorization r := by
    rw [hGcard]
    exact factorization_ordG2_of_dvd_sub_one hr hr3 hqpos hrd
  obtain ⟨P⟩ := Sylow.nonempty (p := r) (G := T)
  have hTfac : (Nat.card T).factorization r = (Nat.card G).factorization r := by
    rw [hTcard, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hfactG]
  have hPcard : Nat.card (P.map T.subtype) = r ^ (Nat.card G).factorization r := by
    rw [Subgroup.card_map_of_injective T.subtype_injective, P.card_eq_multiplicity, hTfac]
  let S : Sylow r G := Sylow.ofCard (P.map T.subtype) hPcard
  have hScomm : IsMulCommutative ↥S := by
    change IsMulCommutative ↥(S : Subgroup G)
    rw [Sylow.coe_ofCard]
    infer_instance
  refine ⟨T, ?_, hTcard, hTcomm, fun Q => ?_⟩
  · change T ≤ (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)
    exact le_rfl
  constructor
  · rw [Sylow.card_eq_multiplicity Q, hfactG]
  · have e : Q ≃* S := Sylow.equiv Q S
    refine IsMulCommutative.of_comm fun a b => e.injective ?_
    rw [map_mul, map_mul]
    exact mul_comm' (e a) (e b)

theorem two_le_pRank_and_sylow_abelian_adjointGroup_G2
    {K : Type} [Field K] [Finite K] {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrd : r ∣ Nat.card K - 1) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (adjointGroup .G2 K)) ∧
      (∀ S : Sylow r (adjointGroup .G2 K), IsMulCommutative ↥S) := by
  refine ⟨two_le_pRank_G2_of_dvd (F := K) hr hrd, ?_⟩
  intro S
  obtain ⟨T, -, -, -, hS⟩ :=
    exists_sylow_abelian_adjointGroup_G2 (K := K) hr hr3 hrd
  exact (hS S).2

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
