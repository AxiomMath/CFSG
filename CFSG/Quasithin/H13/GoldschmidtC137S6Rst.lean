module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin3
public import CFSG.Quasithin.H13.GoldschmidtC137S6Std

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

theorem pCoreOf_eq_of_char {H T R : Subgroup (Gp 6)} (hT : IsSylowTwoOf T H)
    (hR : ∀ r, r ∈ R ↔ r ∈ H ∧ ∀ x ∈ H, x⁻¹ * r * x ∈ T) : pCoreOf 2 H = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRT : R ≤ T := fun r hr => by simpa using ((hR r).1 hr).2 1 H.one_mem
  have hRH : R ≤ H := fun r hr => ((hR r).1 hr).1
  have hRn : ∀ r ∈ R, ∀ y ∈ H, y⁻¹ * r * y ∈ R := by
    intro r hr y hy
    refine (hR _).2 ⟨H.mul_mem (H.mul_mem (H.inv_mem hy) ((hR r).1 hr).1) hy, fun x hx => ?_⟩
    have := ((hR r).1 hr).2 (y * x) (H.mul_mem hy hx)
    simpa [mul_assoc] using this
  apply le_antisymm
  · intro r hr
    refine (hR r).2 ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 H hr, fun x hx => ?_⟩
    have hn := Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hx)) r
    have h1 : x⁻¹ * r * x ∈ pCoreOf 2 H := by
      have := hn.1 hr
      simpa using this
    exact pCoreOf_two_le_of_sylowIn hT.1 hT.2.1 hT.2.2 h1
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRH (fun y hy => ?_)
      (hT.2.1.to_le hRT)
    refine B6.mem_normalizer_of_forall_mem (fun r hr => ?_) (fun r hr => hRn r hr y hy)
    have := hRn r hr y⁻¹ (H.inv_mem hy)
    simpa using this

theorem sylow_T6_H1 : IsSylowTwoOf T6 H1 := by
  refine ⟨T6_le_H1, isSylowTwoOf_T6.2.1, ?_⟩
  have h1 := Subgroup.relIndex_mul_card T6 H1
  rw [inf_eq_left.2 T6_le_H1, card_T6, card_H1] at h1
  show ¬ 2 ∣ T6.relIndex H1
  have : T6.relIndex H1 = 3 := by omega
  rw [this]
  norm_num

theorem sylow_T6_H2 : IsSylowTwoOf T6 H2 := by
  refine ⟨T6_le_H2, isSylowTwoOf_T6.2.1, ?_⟩
  have h1 := Subgroup.relIndex_mul_card T6 H2
  rw [inf_eq_left.2 T6_le_H2, card_T6, card_H2] at h1
  show ¬ 2 ∣ T6.relIndex H2
  have : T6.relIndex H2 = 3 := by omega
  rw [this]
  norm_num

set_option maxRecDepth 100000 in
theorem R1_char_list : ∀ r : Gp 6, (tab r ∈ R1l ↔ tab r ∈ H1l ∧
    ∀ x ∈ H1l, cjT (invT x) (tab r) ∈ T6l) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem R2_char_list : ∀ r : Gp 6, (tab r ∈ R2l ↔ tab r ∈ H2l ∧
    ∀ x ∈ H2l, cjT (invT x) (tab r) ∈ T6l) := by
  decide +kernel

theorem char_of_list {H T R : Subgroup (Gp 6)} {Hl Tl Rl : List Tab} (hH : subOK 6 Hl = true)
    (hHm : ∀ x, x ∈ H ↔ tab x ∈ Hl) (hTm : ∀ x, x ∈ T ↔ tab x ∈ Tl)
    (hRm : ∀ x, x ∈ R ↔ tab x ∈ Rl)
    (hl : ∀ r : Gp 6, (tab r ∈ Rl ↔ tab r ∈ Hl ∧ ∀ x ∈ Hl, cjT (invT x) (tab r) ∈ Tl)) :
    ∀ r, r ∈ R ↔ r ∈ H ∧ ∀ x ∈ H, x⁻¹ * r * x ∈ T := by
  intro r
  rw [hRm, hl, hHm]
  refine and_congr Iff.rfl ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · rw [hTm, show x⁻¹ * r * x = x⁻¹ * r * x⁻¹⁻¹ by rw [inv_inv], tab_cj, tab_inv]
    exact h _ ((hHm x).1 hx)
  · obtain ⟨y, rfl⟩ := exists_tab_eq ((subOK_spec hH).1 x hx)
    have := (hTm _).1 (h y ((hHm y).2 hx))
    rw [show y⁻¹ * r * y = y⁻¹ * r * y⁻¹⁻¹ by rw [inv_inv], tab_cj, tab_inv] at this
    exact this

theorem pCoreOf_H1 : pCoreOf 2 H1 = R1 :=
  pCoreOf_eq_of_char sylow_T6_H1 (char_of_list subOK_lists.2.1 (fun _ => mem_H1)
    (fun _ => mem_T6) (fun _ => mem_R1) R1_char_list)

theorem pCoreOf_H2 : pCoreOf 2 H2 = R2 :=
  pCoreOf_eq_of_char sylow_T6_H2 (char_of_list subOK_lists.2.2.1 (fun _ => mem_H2)
    (fun _ => mem_T6) (fun _ => mem_R2) R2_char_list)

end CFSG.Quasithin.H13.U3.GC137
