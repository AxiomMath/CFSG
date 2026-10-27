module

public import CFSG.Quasithin.EmptyFaithful.T1515eC
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
import CFSG.Adapters.StatedClassicalOrders

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {Y : Type} [Group Y]

theorem card_of_isPSL {n p e : ℕ} (h : IsPSL n p e Y) :
    Nat.card Y = (p ^ e) ^ (n * (n - 1) / 2) * (∏ j ∈ Finset.Icc 2 n, ((p ^ e) ^ j - 1)) /
      Nat.gcd n (p ^ e - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by obtain ⟨⟨-, -, hn, -⟩, -⟩ := h; omega) h

theorem card_of_isPSU3 {p : ℕ} (h : IsPSU 3 p 1 Y) :
    Nat.card Y * Nat.gcd 3 (p + 1) = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨φ⟩⟩ := h
  rw [Nat.card_congr φ.toEquiv]
  have h1 := CFSG.Quasithin.card_statedProj_statedSU_three_mul_gcd (K := K) hp
    le_rfl hK
  simpa using h1

theorem card_of_isSU3 {p : ℕ} [Fact p.Prime] (h : IsSU3 p Y) :
    Nat.card Y = p ^ 3 * ((p + 1) * (p - 1)) * ((p + 1) * (p ^ 2 - p + 1)) := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  rw [Nat.card_congr φ.toEquiv,
    CFSG.SectionRank.OddCover.card_statedSU_three_eq_mul (K := K) hK]

theorem card_of_isSL3 {q : ℕ} (h : IsSL3 q Y) :
    Nat.card Y = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  rw [Nat.card_congr φ.toEquiv, CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hK]
  simp [Finset.prod_Icc_succ_top]

theorem card_of_isSL2 {p : ℕ} [Fact p.Prime] (h : IsSL2 p Y) :
    Nat.card Y = p * (p ^ 2 - 1) := by
  obtain ⟨φ⟩ := h
  rw [Nat.card_congr φ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    Nat.card_zmod]

theorem card_of_isAlt {n : ℕ} (hn : 2 ≤ n) (h : IsAlt n Y) : Nat.card Y = n.factorial / 2 := by
  obtain ⟨φ⟩ := h
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_fin] at h2
  rw [Nat.card_congr φ.toEquiv, ← h2]
  omega

theorem card_of_isHat {S : Type} [Group S] (h : IsHat Y S) : Nat.card Y = 3 * Nat.card S := by
  obtain ⟨-, h3, ⟨φ⟩⟩ := h
  rw [(Subgroup.center Y).card_eq_card_quotient_mul_card_subgroup, h3,
    Nat.card_congr φ.toEquiv, mul_comm]

theorem card_quotient_dvd_of_isExt {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt Y PV PY) :
    ∃ (V : Subgroup Y) (_ : V.Normal), PY (Y ⧸ V) ∧ Nat.card (Y ⧸ V) ∣ Nat.card Y := by
  obtain ⟨V, hV, -, hY⟩ := h
  exact ⟨V, hV, hY, Subgroup.card_quotient_dvd_card V⟩

end CFSG.Quasithin.Vol2.Ch10.A312C
