module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94Ac
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94O
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94B8
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94M3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem count_chain_exact {H : Type*} [Group H] {K G2 G3 H1 H2 H3 : Subgroup H}
    (h32 : G3 ≤ G2) (h2K : G2 ≤ K) {n1 n2 n3 : ℕ} (hK0 : 0 < Nat.card K)
    (hn : Nat.card K = n1 * n2 * n3)
    (hH1 : H1 ≤ K) (hH2 : H2 ≤ G2) (hH3 : H3 ≤ G3)
    (b1 : n1 ≤ G2.relIndex (H1 ⊔ G2)) (b2 : n2 ≤ G3.relIndex (H2 ⊔ G3))
    (b3 : n3 ≤ Nat.card H3) :
    G2.relIndex K = n1 ∧ G3.relIndex G2 = n2 ∧ Nat.card G3 = n3 := by
  obtain ⟨e1, e2, e3⟩ := count_chain h32 h2K hK0 hn hH1 hH2 hH3 b1 b2 b3
  rw [e1] at b1
  rw [e2] at b2
  rw [e3] at b3
  have c1 : G2.relIndex K * Nat.card G2 = Nat.card K := by
    simpa [inf_of_le_left h2K] using Subgroup.relIndex_mul_card (H := G2) (K := K)
  have c2 : G3.relIndex G2 * Nat.card G3 = Nat.card G2 := by
    simpa [inf_of_le_left h32] using Subgroup.relIndex_mul_card (H := G3) (K := G2)
  set a := G2.relIndex K
  set b := G3.relIndex G2
  set c := Nat.card G3
  have habc : a * b * c = n1 * n2 * n3 := by
    rw [← hn, ← c1, ← c2]
    ring
  have hpos : 0 < n1 * n2 * n3 := hn ▸ hK0
  have hn1 : 0 < n1 := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have hn2 : 0 < n2 := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have hn3 : 0 < n3 := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have s1 : n1 * n2 * n3 ≤ a * n2 * n3 := Nat.mul_le_mul (Nat.mul_le_mul b1 le_rfl) le_rfl
  have s2 : a * n2 * n3 ≤ a * b * n3 := Nat.mul_le_mul (Nat.mul_le_mul le_rfl b2) le_rfl
  have s3 : a * b * n3 ≤ a * b * c := Nat.mul_le_mul le_rfl b3
  have t1 : a * n2 * n3 = n1 * n2 * n3 := by omega
  have t2 : a * b * n3 = a * n2 * n3 := by omega
  have t3 : a * b * c = a * b * n3 := by omega
  have ha : a = n1 := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hn2 hn3) ?_
    calc a * (n2 * n3) = a * n2 * n3 := by ring
      _ = n1 * n2 * n3 := t1
      _ = n1 * (n2 * n3) := by ring
  have ha0 : 0 < a := ha ▸ hn1
  have hb : b = n2 := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos ha0 hn3) ?_
    calc b * (a * n3) = a * b * n3 := by ring
      _ = a * n2 * n3 := t2
      _ = n2 * (a * n3) := by ring
  have hb0 : 0 < b := hb ▸ hn2
  have hc' : c = n3 := by
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos ha0 hb0) t3
  exact ⟨ha, hb, hc'⟩

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem ballStab_two_le_nbrStab : ballStab Γ G 2 S.beta ≤ nbrStab Γ G S.beta := fun _ hg =>
  mem_nbrStab.2 fun w hw => mem_ballStab.1 hg w (by rw [dist_eq_one_iff_adj.2 hw]; norm_num)

theorem finite_nbrStab_beta (F : FanTree Γ G) : Finite ↥(nbrStab Γ G S.beta) := by
  have : Finite ↥(MulAction.stabilizer G S.beta) := F.loc_finite S.beta
  exact Finite.of_injective (Subgroup.inclusion (F.nbrStab_le_stabilizer S.beta))
    (Subgroup.inclusion_injective _)

theorem card_nbrStab_beta_pos (F : FanTree Γ G) : 0 < Nat.card ↥(nbrStab Γ G S.beta) := by
  have := S.finite_nbrStab_beta F
  exact Nat.card_pos

theorem fan94b_of (F : FanTree Γ G) (h7 : Fan7 F L) (h65 : Fan65 F) (h81 : Fan81 F L)
    (h82 : Fan82 F L) (h83b : Fan83b F L) (h512 : Fan512 F L)
    (hw : S.w ∈ nbrStab Γ G S.beta) (hwA : S.wA 1 ∈ nbrStab Γ G S.beta)
    (hc : S.c ∈ nbrStab Γ G S.beta)
    (htop : 8 * Nat.card S.D.calpha ≤ (ballStab Γ G 2 S.beta).relIndex
      (Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta)) :
    nbrStab Γ G S.beta = Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta ∧
    ballStab Γ G 2 S.beta =
      Subgroup.closure (insert S.ubs (Set.range S.yMu)) ⊔ ballStab Γ G 3 S.beta ∧
    ballStab Γ G 3 S.beta = Subgroup.closure (insert S.ub (Set.range S.zNb)) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hH1 : Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ≤ nbrStab Γ G S.beta := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hw
    · exact hwA
    · exact hc
  have hH3 : Subgroup.closure (insert S.ub (Set.range S.zNb)) ≤ ballStab Γ G 3 S.beta := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | ⟨i, rfl⟩)
    · exact S.ub_mem_ballStab_three F h71c h82.2.2
    · exact S.zNb_mem_ballStab_three h71c i
  have hcnt : Nat.card ↥(nbrStab Γ G S.beta) =
      (8 * Nat.card S.D.calpha) * 8 * 8 := by
    rw [S.card_nbrStab_beta h65 h71c]
    ring
  obtain ⟨e1, e2, e3⟩ := count_chain (K := nbrStab Γ G S.beta) (G2 := ballStab Γ G 2 S.beta)
    (G3 := ballStab Γ G 3 S.beta)
    (H1 := Subgroup.closure ({S.w, S.wA 1, S.c} : Set G))
    (H2 := Subgroup.closure (insert S.ubs (Set.range S.yMu)))
    (H3 := Subgroup.closure (insert S.ub (Set.range S.zNb)))
    S.ballStab_three_le_two S.ballStab_two_le_nbrStab (S.card_nbrStab_beta_pos F) hcnt hH1
    (S.closure_mid_le F h71c h81) hH3 htop (S.mid_lower F h71c h81 h83b h512)
    (S.eight_le_card_closure_ub F h71c h82.1 h512)
  exact ⟨e1.symm, e2.symm, e3.symm⟩

theorem fan94_exact_of (F : FanTree Γ G) (h7 : Fan7 F L) (h65 : Fan65 F) (h81 : Fan81 F L)
    (h82 : Fan82 F L) (h83b : Fan83b F L) (h512 : Fan512 F L)
    (hw : S.w ∈ nbrStab Γ G S.beta) (hwA : S.wA 1 ∈ nbrStab Γ G S.beta)
    (hc : S.c ∈ nbrStab Γ G S.beta)
    (htop : 8 * Nat.card S.D.calpha ≤ (ballStab Γ G 2 S.beta).relIndex
      (Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta)) :
    (ballStab Γ G 2 S.beta).relIndex (nbrStab Γ G S.beta) = 8 * Nat.card S.D.calpha ∧
    (ballStab Γ G 3 S.beta).relIndex (ballStab Γ G 2 S.beta) = 8 ∧
    Nat.card ↥(ballStab Γ G 3 S.beta) = 8 := by
  have h71c : Fan71c F L := h7.2.2.1
  have hH1 : Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ≤ nbrStab Γ G S.beta := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hw
    · exact hwA
    · exact hc
  have hH3 : Subgroup.closure (insert S.ub (Set.range S.zNb)) ≤ ballStab Γ G 3 S.beta := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | ⟨i, rfl⟩)
    · exact S.ub_mem_ballStab_three F h71c h82.2.2
    · exact S.zNb_mem_ballStab_three h71c i
  have hcnt : Nat.card ↥(nbrStab Γ G S.beta) =
      (8 * Nat.card S.D.calpha) * 8 * 8 := by
    rw [S.card_nbrStab_beta h65 h71c]
    ring
  exact count_chain_exact (K := nbrStab Γ G S.beta) (G2 := ballStab Γ G 2 S.beta)
    (G3 := ballStab Γ G 3 S.beta)
    (H1 := Subgroup.closure ({S.w, S.wA 1, S.c} : Set G))
    (H2 := Subgroup.closure (insert S.ubs (Set.range S.yMu)))
    (H3 := Subgroup.closure (insert S.ub (Set.range S.zNb)))
    S.ballStab_three_le_two S.ballStab_two_le_nbrStab (S.card_nbrStab_beta_pos F) hcnt hH1
    (S.closure_mid_le F h71c h81) hH3 htop (S.mid_lower F h71c h81 h83b h512)
    (S.eight_le_card_closure_ub F h71c h82.1 h512)

end Sec9Cfg

end CFSG.Quasithin.Fan86
