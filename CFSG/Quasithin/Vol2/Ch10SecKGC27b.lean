module

public import CFSG.Quasithin.Vol2.Ch10SecKGC27a
public import CFSG.Quasithin.Vol2.F134J1
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Sporadic.J1
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace C10KG

variable {G : Type} [Group G] [Finite G]

theorem two_mul_card_psl2 {Q : Type} [Group Q] {p e : ℕ} (h : IsPSL 2 p e Q) (hp2 : p ≠ 2) :
    2 * Nat.card Q = p ^ e * ((p ^ e) ^ 2 - 1) := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨φ⟩⟩ := h
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hev : 2 ∣ p ^ e - 1 := even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one)
  rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
    (n := 2) (by norm_num), hK, Nat.gcd_eq_left hev,
    show Finset.Icc 2 2 = ({2} : Finset ℕ) by decide, Finset.prod_singleton,
    show (2 * (2 - 1) / 2 : ℕ) = 1 from rfl, pow_one]
  refine Nat.mul_div_cancel' (Dvd.dvd.mul_left ?_ _)
  have h1 : 1 ≤ p ^ e := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  rw [sq_sub_one']
  exact Dvd.dvd.mul_right hev _

theorem q_facts {Q : Type} [Group Q]
    (hQ : (∃ p : ℕ, p.Prime ∧ IsPSL 2 p 1 Q ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5)) ∨
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsPSL 2 p 2 Q) ∨ IsSporadic .J1 Q) :
    IsSimpleGroup Q ∧ ¬ C27Order (Nat.card Q) := by
  rcases hQ with ⟨p, hp, hpsl, h5, h8⟩ | ⟨p, hp, hp3, hpsl⟩ | ⟨⟨e⟩⟩
  · refine ⟨(CFSG.LieType.Simplicity.fam_PSL_simplicity Q 2 p 1 hpsl).2,
      not_c27Order_psl_p hp h5 h8 ?_⟩
    have := two_mul_card_psl2 hpsl (by omega)
    simpa using this
  · refine ⟨(CFSG.LieType.Simplicity.fam_PSL_simplicity Q 2 p 2 hpsl).2,
      not_c27Order_psl_p2 hp hp3 ?_⟩
    rw [two_mul_card_psl2 hpsl (by omega), ← pow_mul]
  · have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J1) :=
      CFSG.Sporadic.J1.isSimpleGroup_J1
    refine ⟨e.isSimpleGroup, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.F134.card_carrier_J1]
    exact not_c27Order_j1

end C10KG

end CFSG.Quasithin.Vol2.Ch10.SecB
