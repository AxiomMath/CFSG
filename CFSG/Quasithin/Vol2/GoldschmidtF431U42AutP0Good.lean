module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP0Base
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP0Cls

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431 CFSG.Quasithin.H13.F431.U42
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 f45)

@[expose] def clsW : List (List ℕ) :=
  [[], [1], [1, 1], [3, 1], [0, 1, 1], [1, 1, 1], [3, 1, 1], [1, 3, 1], [1, 0, 1, 1],
    [3, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1], [3, 1, 1, 1], [1, 3, 1, 1], [0, 1, 3, 1],
    [3, 1, 3, 1], [1, 1, 0, 1, 1], [3, 1, 0, 1, 1], [1, 3, 0, 1, 1], [3, 0, 1, 1, 1],
    [3, 1, 1, 1, 1], [1, 3, 1, 1, 1], [1, 1, 3, 1, 1], [3, 1, 3, 1, 1], [1, 0, 1, 3, 1],
    [3, 0, 1, 3, 1], [3, 1, 1, 0, 1, 1], [1, 1, 3, 0, 1, 1], [3, 1, 3, 0, 1, 1],
    [1, 3, 0, 1, 1, 1], [1, 3, 1, 1, 1, 1], [0, 1, 3, 1, 1, 1], [1, 1, 3, 1, 1, 1],
    [0, 1, 1, 3, 1, 1], [3, 1, 1, 3, 1, 1], [1, 1, 1, 3, 0, 1, 1]]

@[expose] def clsL : List PL :=
  clsW.map fun w => comp (comp (evalAL w) fhatL) (evalAL (invAL w))

theorem cls_check : clsL.Nodup ∧ fhatL ∈ clsL ∧
    ∀ c ∈ clsL, ∀ s ∈ [(xL, xL), (yL, yiL), (f45L, f45L)], comp (comp s.1 c) s.2 ∈ clsL := by
  decide +kernel

@[expose] def clsP : List P45 := clsW.map fun w => wordAP w * fhat * (wordAP w)⁻¹

theorem repL_cls (w : List ℕ) :
    RepL (comp (comp (evalAL w) fhatL) (evalAL (invAL w))) (wordAP w * fhat * (wordAP w)⁻¹) :=
  repL_mul (repL_mul (repL_wordAP w) repL_fhat) (by
    rw [← wordAP_invAL]
    exact repL_wordAP _)

theorem clsP_map : clsP.map permL = clsL := by
  rw [clsP, List.map_map]
  exact List.map_congr_left fun w _ => permL_eq_of_repL (repL_cls w)

theorem mem_of_permL_mem {l : List P45} {σ : P45} (h : permL σ ∈ l.map permL) : σ ∈ l := by
  obtain ⟨c, hc, hce⟩ := List.mem_map.1 h
  have : c = σ := eq_of_repL (repL_permL c) (by rw [hce]; exact repL_permL σ)
  exact this ▸ hc

theorem clsP_nodup : clsP.Nodup := List.Nodup.of_map permL (clsP_map ▸ cls_check.1)

theorem fhat_mem_clsP : fhat ∈ clsP :=
  mem_of_permL_mem (by rw [clsP_map, permL_eq_of_repL repL_fhat]; exact cls_check.2.1)

theorem clsP_conj : ∀ c ∈ clsP, ∃ a ∈ QA45.originalSubgroup, c = a * fhat * a⁻¹ := by
  intro c hc
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hc
  exact ⟨wordAP w, wordAP_mem w, rfl⟩

theorem clsP_closed : ∀ c ∈ clsP, ∀ s ∈ ({x45, y45, f45} : Set P45), s * c * s⁻¹ ∈ clsP := by
  intro c hc s hs
  have hcL : permL c ∈ clsL := clsP_map ▸ List.mem_map_of_mem hc
  have key : ∀ (sL sinvL : PL), RepL sL s → RepL sinvL s⁻¹ →
      (sL, sinvL) ∈ [(xL, xL), (yL, yiL), (f45L, f45L)] → s * c * s⁻¹ ∈ clsP := by
    intro sL sinvL h1 h2 hmem
    have h3 := cls_check.2.2 _ hcL _ hmem
    refine mem_of_permL_mem ?_
    rw [clsP_map, permL_eq_of_repL (repL_mul (repL_mul h1 (repL_permL c)) h2)]
    exact h3
  rcases hs with rfl | rfl | rfl
  · exact key xL xL repL_x (by rw [x45_inv]; exact repL_x) (by simp)
  · exact key yL yiL repL_y repL_yi (by simp)
  · exact key f45L f45L repL_f45 (by rw [f45_inv]; exact repL_f45) (by simp)

theorem card_centralizer_fhat :
    Nat.card (Subgroup.centralizer
      ({(⟨fhat, fhat_mem⟩ : ↥QA45.originalSubgroup)} : Set ↥QA45.originalSubgroup)) = 1440 := by
  have h := card_centralizer_mul_of_closed_class (Γ := ({x45, y45, f45} : Set P45))
    QA45_closure_eq.symm fhat_mem clsP_nodup clsP_conj fhat_mem_clsP clsP_closed
  have hl : clsP.length = 36 := by simp [clsP, clsW]
  rw [hl, card_A] at h
  have h' : Nat.card (Subgroup.centralizer
      ({(⟨fhat, fhat_mem⟩ : ↥QA45.originalSubgroup)} : Set ↥QA45.originalSubgroup)) * 36 =
        51840 := h
  omega

end CFSG.Quasithin.H13.F431.U42Aut
