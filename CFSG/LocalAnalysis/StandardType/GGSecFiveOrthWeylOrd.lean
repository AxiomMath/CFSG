module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.Monster.B.Geometry.F4Weyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

public section

namespace CFSG.StandardType.OrthF3


private lemma ct_od_coxeterMatrix_F4 :
    CFSG.LieType.RootSystem.coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) = CoxeterMatrix.F₄ :=
  coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)
    ⟨by decide, fun i => by fin_cases i <;> decide⟩

private lemma ct_od_card_G2 : Nat.card (CoxeterMatrix.G₂).Group = 12 := by
  let cs := (CoxeterMatrix.G₂).toCoxeterSystem
  have hs : cs.simple 0 * cs.simple 0 = 1 := cs.simple_mul_simple_self 0
  have ht : cs.simple 1 * cs.simple 1 = 1 := cs.simple_mul_simple_self 1
  have hs1 : cs.simple 0 ≠ 1 := cs.simple_ne_one 0
  have ht1 : cs.simple 1 ≠ 1 := cs.simple_ne_one 1
  have hn : orderOf (cs.simple 0 * cs.simple 1) = 6 := by
    rw [cs.orderOf_simple_mul_simple]
    decide
  have hgen : Subgroup.closure ({cs.simple 0, cs.simple 1} : Set (CoxeterMatrix.G₂).Group) = ⊤ := by
    rw [← cs.subgroup_closure_range_simple]
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨0, hx.symm⟩
      · exact ⟨1, hx.symm⟩
    · intro hx
      obtain ⟨i, hi⟩ := hx
      rw [← hi]
      have hi' : i = 0 ∨ i = 1 := by
        have h : i.val = 0 ∨ i.val = 1 := by omega
        rcases h with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hi' with rfl | rfl <;> simp
  have e : DihedralGroup 6 ≃* (CoxeterMatrix.G₂).Group :=
    TauCeti.dihedralGroupMulEquiv (s := cs.simple 0) (t := cs.simple 1) (n := 6)
      hs ht hs1 ht1 hn hgen
  calc Nat.card (CoxeterMatrix.G₂).Group = Nat.card (DihedralGroup 6) :=
        (Nat.card_congr e.toEquiv).symm
    _ = 12 := by rw [DihedralGroup.nat_card]

private lemma ct_od_family (n : ℕ) (hn : 2 ≤ n) :
    (24 ∣ 2 ^ n * n.factorial → 2 ^ n * n.factorial ∣ 1440 → 2 ^ n * n.factorial = 48) ∧
      (720 ∣ 2 ^ n * n.factorial → ¬ 2 ^ n * n.factorial ∣ 103680) ∧
      (120 ∣ 2 ^ n * n.factorial → 2 ^ n * n.factorial ∣ 103680 →
        2 ^ n * n.factorial = 3840) ∧
      (192 ∣ 2 ^ n * n.factorial → 2 ^ n * n.factorial ∣ 103680 →
        2 ^ n * n.factorial = 384 ∨ 2 ^ n * n.factorial = 1152 ∨
          2 ^ n * n.factorial = 3840) := by
  by_cases hn6 : n ≤ 6
  · interval_cases n <;> decide
  · push Not at hn6
    have hpow : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfac : Nat.factorial 7 ≤ n.factorial := Nat.factorial_le (by omega)
    have hbig : 2 ^ 7 * Nat.factorial 7 ≤ 2 ^ n * n.factorial := Nat.mul_le_mul hpow hfac
    norm_num at hbig
    have hgt : 103680 < 2 ^ n * n.factorial := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h1 h2
      have hle : 2 ^ n * n.factorial ≤ 1440 := Nat.le_of_dvd (by norm_num) h2
      omega
    · intro h1 h2
      have hle : 2 ^ n * n.factorial ≤ 103680 := Nat.le_of_dvd (by norm_num) h2
      omega
    · intro h1 h2
      have hle : 2 ^ n * n.factorial ≤ 103680 := Nat.le_of_dvd (by norm_num) h2
      omega
    · intro h1 h2
      have hle : 2 ^ n * n.factorial ≤ 103680 := Nat.le_of_dvd (by norm_num) h2
      omega

theorem card_of_nonSimplyLaced {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {W : Subgroup (MulAut ↥Bs)}
    (h : (∃ n : ℕ, 2 ≤ n ∧ GGWeylOfType p (CoxeterMatrix.B n) W) ∨ GGWeylOfType p CoxeterMatrix.F₄ W ∨
      GGWeylOfType p CoxeterMatrix.G₂ W) :
    Nat.card ↥W = 12 ∨ Nat.card ↥W = 1152 ∨ ∃ n : ℕ, 2 ≤ n ∧ Nat.card ↥W = 2 ^ n * n.factorial := by
  rcases h with ⟨n, hn, e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · right; right
    refine ⟨n, hn, ?_⟩
    rw [← Nat.card_congr e.toEquiv]
    exact Nat.le_antisymm (card_coxeterB_le n) (CFSG.StandardType.SpFrame.card_coxeterB_ge n hn)
  · right; left
    rw [← Nat.card_congr e.toEquiv, ← ct_od_coxeterMatrix_F4]
    exact CFSG.Monster.B.Geometry.card_f4WeylGroup
  · left
    rw [← Nat.card_congr e.toEquiv]
    exact ct_od_card_G2

theorem orth_order_arith (N : ℕ) (hN : N = 12 ∨ N = 1152 ∨ ∃ n : ℕ, 2 ≤ n ∧ N = 2 ^ n * n.factorial) :
    (24 ∣ N → N ∣ 1440 → N = 48) ∧ (720 ∣ N → ¬ N ∣ 103680) ∧ (120 ∣ N → N ∣ 103680 → N = 3840) ∧
      (192 ∣ N → N ∣ 103680 → N = 384 ∨ N = 1152 ∨ N = 3840) := by
  rcases hN with rfl | rfl | ⟨n, hn, rfl⟩
  · decide
  · decide
  · exact ct_od_family n hn

end CFSG.StandardType.OrthF3

end
