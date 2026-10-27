module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2NoOffData
public import CFSG.Quasithin.Background.S1549DL3N
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Gens

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat

theorem card_D :
    Nat.card (g2Derived (ZMod 2)) = 6048 := by
  have h := S1549D.card_commutator_quasithinG2_two (K := ZMod 2) (Nat.card_zmod 2)
  rw [← h]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self _)).toEquiv

theorem not_S_le_D :
    ¬ sSubG ≤ g2Derived (ZMod 2) := by
  intro h
  have := Subgroup.card_dvd_of_le h
  rw [card_sSubG, card_D] at this
  norm_num at this

@[expose] def cexp (w : List ℕ) : List ℕ :=
  w.flatMap fun j => if j = 0 then [0, 1, 0, 1] else [3, 2, 3, 2]

theorem wd_cexp_mem (w : List ℕ) : wd (cexp w) ∈ g2Derived (ZMod 2) := by
  induction w with
  | nil => exact one_mem _
  | cons j w ih =>
    have : cexp (j :: w) = (if j = 0 then [0, 1, 0, 1] else [3, 2, 3, 2]) ++ cexp w := by
      simp [cexp]
    rw [this, wd_append]
    refine mul_mem ?_ ih
    split_ifs
    · exact wd_mem_derived 0 1
    · exact wd_mem_derived 3 2

theorem cexp_lt (w : List ℕ) : ∀ j ∈ cexp w, j < 4 := by
  intro j hj
  simp only [cexp, List.mem_flatMap] at hj
  obtain ⟨x, -, hx⟩ := hj
  split_ifs at hx <;> simp at hx <;> omega

theorem cw_checks : wcode (cexp cwT01) = matT01 ∧ wcode (cexp cwT10) = matT10 ∧
    ∀ k < 6, mmul (wcode (cexp (cwOuter.getD k []))) matX = sM (outerIdx2.getD k 0) := by
  decide +kernel

theorem sE8_outer2 : ∀ e < 8, ∃ k < 6, outerIdx2.getD k 0 ∈ sE8.getD e [] := by
  decide

theorem outerIdx2_lt : ∀ k < 6, outerIdx2.getD k 0 < 64 := by
  decide

theorem zT01_mem_D : wd [0] ∈ g2Derived (ZMod 2) := by
  have : wd [0] = wd (cexp cwT01) := eq_of_code (by
    rw [matCode_wd (by decide), matCode_wd (cexp_lt _), cw_checks.1]
    decide +kernel)
  rw [this]
  exact wd_cexp_mem _

theorem zT10_mem_D : wd [1] ∈ g2Derived (ZMod 2) := by
  have : wd [1] = wd (cexp cwT10) := eq_of_code (by
    rw [matCode_wd (by decide), matCode_wd (cexp_lt _), cw_checks.2.1]
    decide +kernel)
  rw [this]
  exact wd_cexp_mem _

theorem wdW_eq' : wd [1, 0, 2, 0, 1] = wd [1] * wd [0] * wd [2] * wd [0] * wd [1] := by
  simp only [wd_cons, wd_nil, mul_one, mul_assoc]

theorem outer_not_mem_D
    {k : ℕ} (hk : k < 6) :
    sEltG (outerIdx2.getD k 0) ∉ g2Derived (ZMod 2) := by
  intro h
  have hu : sEltG (outerIdx2.getD k 0) = wd (cexp (cwOuter.getD k [])) * wd [2] := by
    refine eq_of_code ?_
    rw [matCode_mulG, matCode_sEltG (outerIdx2_lt k hk), matCode_wd (cexp_lt _),
      matCode_wd (by decide)]
    exact (cw_checks.2.2 k hk).symm
  have hX : wd [2] ∈ g2Derived (ZMod 2) := by
    have h2 := mul_mem (inv_mem (wd_cexp_mem (cwOuter.getD k []))) h
    rwa [hu, inv_mul_cancel_left] at h2
  refine not_S_le_D (S_le_of_three _ ?_)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact zT01_mem_D
  · exact hX
  · rw [wdW_eq']
    exact mul_mem (mul_mem (mul_mem (mul_mem zT10_mem_D zT01_mem_D) hX) zT01_mem_D) zT10_mem_D

theorem noOff_S_of_cls
    {B : Subgroup Gam}
    (hBD : B ≤ g2Derived (ZMod 2)) {e : ℕ} (he : e < 8)
    (hiff : ∀ l, l ∈ idx B ↔ l ∈ sE8.getD e []) : False := by
  obtain ⟨k, hk, hkm⟩ := sE8_outer2 e he
  exact outer_not_mem_D hk (hBD (mem_idx.1 ((hiff _).2 hkm)).2)

end CFSG.Quasithin.H13.U3.GC137.S2
