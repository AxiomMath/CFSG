module

public import CFSG.Quasithin.Vol2.Ch7Lem734Rows
public import CFSG.Quasithin.H13.A5M12Row
public import CFSG.Quasithin.H13.A5M22HatRow
public import CFSG.Quasithin.Vol2.Ch7Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

theorem rk_of_card {V : Type*} [Group V] {k : ℕ} (h : Nat.card V = 2 ^ k) : rk V = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rk, h, padicValNat.prime_pow]

theorem stmt7_2_1_m_Mathieu :
    Stmt7_2_1_m_Mathieu := by
  intro G _ _ T L I _ hV _ hNM _ hrow
  have hLM : Mathieu.IsOver (autI hV (fsuL0 T L)) (autI hV ⊤) :=
    ⟨autI_fsuL0_le hV, autI_top_le_normalizer hV hNM⟩
  have h144 := Mathieu.stmtH14_4 (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV ⊤) hLM
  rcases hrow with h | h | h | h | h | h | h | h
  ·
    have hM : M12Ten (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := h.1
    obtain ⟨e, -⟩ := A5.M12.m12_std hM
    have hcard : Nat.card (IntMod (fsuV T I) hV) = 2 ^ 10 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 10 → ZMod 2) = _
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    refine Mathieu.le_mParam_of (by rw [rk_of_card hcard]; norm_num) fun s hs hs2 => ?_
    exact A5.factM12Row1321_holds _ _ _ hLM.1 hLM.2 hM s hs hs2
  ·
    have hM : Mhat22Twelve (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := h
    have hcard : Nat.card (IntMod (fsuV T I) hV) = 2 ^ 12 := by
      obtain ⟨K, _, _, Γ₀, hK, -, -, π, hπ⟩ := hM
      obtain ⟨e, -⟩ := exists_mulEquiv_of_realizesVia Γ₀ hπ
      rw [Nat.card_congr e.toEquiv]
      exact A5.M22Hat.card_stdMod_six hK
    refine Mathieu.le_mParam_of (by rw [rk_of_card hcard]; norm_num) fun s hs hs2 => ?_
    exact A5.factM22HatRow1321_holds _ _ _ hLM.1 hLM.2 hM s hs hs2
  · exact h144.2 (Or.inr h)
  · exact h144.2 (Or.inl h)
  · exact (h144.1 (Or.inr (Or.inr (Or.inr h)))).ge.trans' (by norm_num)
  · exact (h144.1 (Or.inr (Or.inr (Or.inl h)))).ge.trans' (by norm_num)
  · exact (h144.1 (Or.inr (Or.inl h))).ge.trans' (by norm_num)
  · exact (h144.1 (Or.inl h)).ge.trans' (by norm_num)

end CFSG.Quasithin.H13
