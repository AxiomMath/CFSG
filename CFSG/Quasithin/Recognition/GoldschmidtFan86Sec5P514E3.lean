module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514E2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514E
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Fix
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Gc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_E (F : FanTree Γ G) (h40 : Fan40 F) (h54 : Fan54 F) (T : Track Γ G)
    (hT : T.fixer = ⊥) {z : G} {a r : ℤ} (hzc : z ∈ T.line.Zc)
    (hcore : T.line.IsCoreC z a (a + 2))
    (hfix : ∀ i, i ∈ T.line.fixIdx z ↔ a - r ≤ i ∧ i ≤ a + 2 + r) (hr : Odd r)
    (C : LblCtx Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2))) :
    ∃ w₁ w₂ : G, w₁ * w₁ = 1 ∧ w₂ * w₂ = 1 ∧ w₁ * w₂ = lab T z 1 ∧ w₁ ≠ 1 ∧ w₂ ≠ 1 ∧
      (∃ p q, Γ.Adj (T.line.vert (a + 2)) p ∧ Γ.Adj (T.line.vert (a + 2)) q ∧ p ≠ q ∧
        w₁ = Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q) ∧
      (∃ p q, Γ.Adj (T.line.vert (a + 2)) p ∧ Γ.Adj (T.line.vert (a + 2)) q ∧ p ≠ q ∧
        w₂ = Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q) ∧
      w₁ ∈ Cen (T.line.edgeCirc (G := G) (a + 2)) ∧ w₂ ∈ Cen (T.line.edgeCirc (G := G) (a + 2)) ∧
      ∀ i, a + 2 - r ≤ i → i ≤ a + 2 + r →
        w₁ • T.line.vert i = T.line.vert i ∧ w₂ • T.line.vert i = T.line.vert i := by
  classical
  have hcz : z ∈ Cinv G (T.line.vert (a + 1)) := C.cinv
  have hadjo : Γ.Adj (T.line.vert (a + 2)) (T.line.vert (a + 2 + 1)) := T.line.adj (a + 2)
  have hne : T.line.vert (a + 1) ≠ T.line.vert (a + 2 + 1) := by
    have := T.line.vert_pred_ne_succ (a + 2)
    rwa [show a + 2 - 1 = a + 1 by ring] at this
  obtain ⟨h, hhG, hhn, hadj_u, hu1, hu2⟩ := exists_h F C hadjo hne
  have hz1 : lab T z 1 = Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) :=
    lab_one_eq T hcz
  have hLα : Lb z (T.line.vert (a + 1)) (T.line.vert (a + 1)) = z := Lb_self hcz
  have hea : Lb z (T.line.vert (a + 1)) (h • T.line.vert (a + 1)) = h * z * h⁻¹ :=
    Lb_eq hcz rfl
  have hz2 : z * z = 1 := hcz.2.1
  have hz1sq := C.sq F hadjo
  have heasq := C.sq F hadj_u
  have c1 : z * Lb z (T.line.vert (a + 1)) (h • T.line.vert (a + 1)) =
      Lb z (T.line.vert (a + 1)) (h • T.line.vert (a + 1)) * z := by
    have := C.commute F C.adj.symm hadj_u
    rwa [hLα] at this
  have c2 : Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) * z =
      z * Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) := by
    have := C.commute F hadjo C.adj.symm
    rwa [hLα] at this
  have c3 := C.commute F hadjo hadj_u
  have hKz : z ∈ nbrStab Γ G (T.line.vert (a + 2)) := by
    have := Lb_mem_nbrStab F hcz C.ball C.adj C.adj.symm
    rwa [hLα] at this
  have hKe := Lb_mem_nbrStab F hcz C.ball C.adj hadj_u
  have hKz1 := Lb_mem_nbrStab F hcz C.ball C.adj hadjo
  have hKcomm : ∀ k ∈ nbrStab Γ G (T.line.vert (a + 2)),
      k * z = z * k ∧ k * Lb z (T.line.vert (a + 1)) (h • T.line.vert (a + 1)) =
        Lb z (T.line.vert (a + 1)) (h • T.line.vert (a + 1)) * k ∧
      k * Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) =
        Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) * k := fun k hk => by
    refine ⟨?_, comm_nbrStab_Lb F hcz C.adj hadj_u hk, comm_nbrStab_Lb F hcz C.adj hadjo hk⟩
    have := comm_nbrStab_Lb F hcz C.adj C.adj.symm hk
    rwa [hLα] at this
  have hhh : (h * h) * z = z * (h * h) := (hKcomm _ hhG.2).1
  have hz1h : h * Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) =
      Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) * h :=
    (Lb_cinv hcz (exists_conj_of_adj F C.adj hadjo)).2.2.2 h
      (MulAction.mem_stabilizer_iff.2 (MulAction.mem_stabilizer_iff.1 hhG.1.2))
  obtain ⟨hch1, hch2, hw1, hw2, hw12⟩ := alg_E hz2 heasq hz1sq hea c1 c2 c3 hhh hz1h
  obtain ⟨b, c, hb, hc, hnd⟩ := exists_five_nbrs C.v5 (a₁ := T.line.vert (a + 2 + 1))
    (a₂ := T.line.vert (a + 1)) (a₃ := h • T.line.vert (a + 1)) hne.symm hu2.symm hu1.symm
  have hprod := C.prod5 [T.line.vert (a + 2 + 1), T.line.vert (a + 1), h • T.line.vert (a + 1),
    b, c] hnd rfl (by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hu | hu | hu | hu | hu <;> rw [hu]
      · exact hadjo
      · exact C.adj.symm
      · exact hadj_u
      · exact hb
      · exact hc)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hLα] at hprod
  have hbc' : b ≠ c := by
    have := List.nodup_cons.1 hnd
    simp [List.nodup_cons] at this
    tauto
  have hbc : Lb z (T.line.vert (a + 1)) b ≠ Lb z (T.line.vert (a + 1)) c := C.ne b c hb hc hbc'
  have hw2eq : Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) *
      (z * Lb z (T.line.vert (a + 1)) (h • T.line.vert (a + 1))) =
      Lb z (T.line.vert (a + 1)) b * Lb z (T.line.vert (a + 1)) c := by
    have h1 : Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) *
        (z * Lb z (T.line.vert (a + 1)) (h • T.line.vert (a + 1))) *
        (Lb z (T.line.vert (a + 1)) b * Lb z (T.line.vert (a + 1)) c) = 1 := by
      rw [← hprod]
      simp only [mul_assoc]
    have h2 := eq_inv_of_mul_eq_one_left h1
    rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_right (C.sq F hb),
      inv_eq_of_mul_eq_one_right (C.sq F hc)]
    exact C.commute F hc hb
  have hv5 : valence Γ (T.line.vert (a + 2)) = 5 := C.v5
  have hfixea : ∀ i, a + 2 - r ≤ i → i ≤ a + 2 + r →
      Lb z (T.line.vert (a + 1)) (h • T.line.vert (a + 1)) • T.line.vert i = T.line.vert i := by
    refine fix_off F h40 h54 T hzc hcore hr
      (fun hmem => C.ne_one F hadj_u (by rw [hT] at hmem; exact Subgroup.mem_bot.1 hmem))
      (MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hKe)) fun j hj1 hj2 => ?_
    have hKj : lab T z j ∈ nbrStab Γ G (T.line.vert (a + 2)) := T.line.mem_nbrStab_of_fix F
      (u := a + 2) ((mem_fixIdx_lab T z j (a + 2 - 1)).2 ((hfix _).2 ⟨by omega, by omega⟩))
      ((mem_fixIdx_lab T z j (a + 2)).2 ((hfix _).2 ⟨by omega, by omega⟩))
      ((mem_fixIdx_lab T z j (a + 2 + 1)).2 ((hfix _).2 ⟨by omega, by omega⟩))
    exact (comm_nbrStab_Lb F hcz C.adj hadj_u hKj).symm
  refine ⟨z * Lb z (T.line.vert (a + 1)) (h • T.line.vert (a + 1)),
    Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) *
      (z * Lb z (T.line.vert (a + 1)) (h • T.line.vert (a + 1))), hw1, hw2, ?_, ?_, ?_,
    ⟨_, _, C.adj.symm, hadj_u, hu1.symm, by rw [hLα]⟩, ⟨b, c, hb, hc, hbc', hw2eq⟩, ?_, ?_, ?_⟩
  · rw [hz1]
    exact hw12
  · intro h1
    have := eq_inv_of_mul_eq_one_right h1
    rw [inv_eq_of_mul_eq_one_right hz2] at this
    exact C.ne _ _ C.adj.symm hadj_u hu1.symm (by rw [hLα]; exact this.symm)
  · intro h1
    rw [hw2eq] at h1
    have := eq_inv_of_mul_eq_one_right h1
    rw [inv_eq_of_mul_eq_one_right (C.sq F hb)] at this
    exact hbc this.symm
  · rw [T.line.edgeCirc_of_five hv5]
    exact cen_gcirc_of F hadjo hhG hhn ((nbrStab Γ G _).mul_mem hKz hKe)
      (fun k hk => Commute.mul_right (hKcomm k hk).1 (hKcomm k hk).2.1) hch1
  · rw [T.line.edgeCirc_of_five hv5]
    exact cen_gcirc_of F hadjo hhG hhn ((nbrStab Γ G _).mul_mem hKz1
      ((nbrStab Γ G _).mul_mem hKz hKe))
      (fun k hk => Commute.mul_right (hKcomm k hk).2.2
        (Commute.mul_right (hKcomm k hk).1 (hKcomm k hk).2.1)) hch2
  · intro i h1 h2
    have hzi : z • T.line.vert i = T.line.vert i := (hfix i).2 ⟨by omega, by omega⟩
    have hz1i : Lb z (T.line.vert (a + 1)) (T.line.vert (a + 2 + 1)) • T.line.vert i =
        T.line.vert i := by
      rw [← hz1]
      exact (mem_fixIdx_lab T z 1 i).2 ((hfix _).2 ⟨by omega, by omega⟩)
    have hw1i : (z * Lb z (T.line.vert (a + 1)) (h • T.line.vert (a + 1))) • T.line.vert i =
        T.line.vert i := by
      rw [mul_smul, hfixea i h1 h2, hzi]
    exact ⟨hw1i, by rw [mul_smul, hw1i, hz1i]⟩

end P514

end CFSG.Quasithin.Fan86
