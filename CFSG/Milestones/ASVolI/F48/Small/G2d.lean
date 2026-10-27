module

public import CFSG.Milestones.ASVolI.F48.Small.G2dRel
public import CFSG.Milestones.ASVolI.F48.Small.Core
public import Certificates.Certificate7532
public import Certificates.Certificate7533
public import CFSG.Milestones.ASVolI.F4N.BId
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F48.Small.Base

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.CosetTable CFSG.Sporadic.Bridge

theorem burnsideF48s_ev_invW {G : Type*} [Group G] {m : ℕ} (h : Fin m → G)
    (w : List (Fin m × Bool)) : burnsideF48s_ev h (burnsideF48s_invW w) = (burnsideF48s_ev h w)⁻¹ := by
  induction w with
  | nil => simp [burnsideF48s_invW]
  | cons l w ih =>
    have e : burnsideF48s_invW (l :: w) = burnsideF48s_invW w ++ [(l.1, !l.2)] := by
      simp [burnsideF48s_invW]
    rw [e, burnsideF48s_ev_append, ih, burnsideF48s_ev_cons, burnsideF48s_ev_cons,
      burnsideF48s_ev_nil, mul_one, mul_inv_rev]
    obtain ⟨i, b⟩ := l
    cases b <;> simp

theorem burnsideF48s_exists_word {G : Type*} [Group G] {m : ℕ} (L : Fin m → G) (I : Fin m → Prop)
    {S : Set G} (hS : ∀ g ∈ S, ∃ i, I i ∧ L i = g) {z : G} (hz : z ∈ Subgroup.closure S) :
    ∃ w : List (Fin m × Bool), (∀ l ∈ w, I l.1) ∧ burnsideF48s_ev L w = z := by
  induction hz using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hS g hg
    exact ⟨[(i, true)], by simpa using hi, by simp [burnsideF48s_ev]⟩
  | one => exact ⟨[], by simp, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨wx, hx1, hx2⟩ := hx
    obtain ⟨wy, hy1, hy2⟩ := hy
    refine ⟨wx ++ wy, fun l hl => ?_, by rw [burnsideF48s_ev_append, hx2, hy2]⟩
    rcases List.mem_append.1 hl with h | h
    · exact hx1 l h
    · exact hy1 l h
  | inv x _ hx =>
    obtain ⟨w, h1, h2⟩ := hx
    refine ⟨burnsideF48s_invW w, fun l hl => ?_, by rw [burnsideF48s_ev_invW, h2]⟩
    simp only [burnsideF48s_invW, List.mem_reverse, List.mem_map] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    exact h1 l' hl'

theorem burnsideF48s_wordProd_u33W {G : Type*} [Group G] (gen : ℕ → G) (s : String) :
    wordProd gen (u33W s) = burnsideF48s_ev (fun k : Fin 5 => gen k.val) (u33Word s) := by
  unfold wordProd u33W burnsideF48s_ev
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨i, b⟩ -
  cases b <;> rfl

theorem burnsideF48s_range_comp_mulEquiv_g2d {A B C : Type*} [Group A] [Group B] [Group C]
    (g : B →* C) (e : A ≃* B) : (g.comp e.toMonoidHom).range = g.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map]

theorem burnsideF48s_getD_map_range {α : Type*} (f : ℕ → α) {n i : ℕ} (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

section Model

theorem burnsideF48s_g2d_repL (hg : burnsideF48s_g2dCheckGens () = true)
    (w : List (Fin 5 × Bool)) : RepL (burnsideF48s_g2dEvL w) (burnsideF48s_ev u33Img w) := by
  simp only [burnsideF48s_g2dCheckGens, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
    decide_eq_true_eq, true_implies] at hg
  have hlet : ∀ l : Fin 5 × Bool,
      RepL (burnsideF48s_g2dLetL l) (cond l.2 (u33Img l.1) (u33Img l.1)⁻¹) := by
    rintro ⟨i, b⟩
    cases b
    · exact (hg i).2
    · exact (hg i).1
  have key : ∀ (w : List (Fin 5 × Bool)) (acc : List ℕ) (σ : Equiv.Perm (Fin 28)), RepL acc σ →
      RepL (w.foldl (fun acc l => compL acc (burnsideF48s_g2dLetL l)) acc)
        (σ * burnsideF48s_ev u33Img w) := by
    intro w
    induction w with
    | nil =>
      intro acc σ h
      simpa using h
    | cons l w ih =>
      intro acc σ h
      rw [List.foldl_cons, burnsideF48s_ev_cons, ← mul_assoc]
      exact ih _ _ (repL_mul h (hlet l))
  have := key w (List.range 28) 1 (repL_one 28)
  rwa [one_mul] at this

theorem burnsideF48s_g2d_ev_tdt {G : Type*} [Group G] (h : Fin 5 → G) (i j : ℕ) (s : String) :
    burnsideF48s_ev h (burnsideF48s_g2dTelF i ++ u33Word s ++ burnsideF48s_g2dTelF j) =
      burnsideF48s_ev h (burnsideF48s_g2dTelF i) * burnsideF48s_ev h (u33Word s) *
        burnsideF48s_ev h (burnsideF48s_g2dTelF j) := by
  rw [burnsideF48s_ev_append, burnsideF48s_ev_append]

theorem burnsideF48s_g2d_specA (hg : burnsideF48s_g2dCheckGens () = true)
    (hA : burnsideF48s_g2dCheckA () = true) {i₁ i₂ : ℕ} (h₁ : i₁ < 32) (h₂ : i₂ < 32)
    (hinv : burnsideF48s_ev u33Img (burnsideF48s_g2dTelF i₁ ++ u33Word "X" ++ burnsideF48s_g2dTelF i₂) *
      burnsideF48s_ev u33Img (burnsideF48s_g2dTelF i₁ ++ u33Word "X" ++ burnsideF48s_g2dTelF i₂) = 1) :
    ∃ k < 8, burnsideF48s_ev u33Img
      (burnsideF48s_g2dTelF i₁ ++ u33Word "X" ++ burnsideF48s_g2dTelF i₂) =
        burnsideF48s_ev u33Img (burnsideF48s_g2dAF k) := by
  have hR := burnsideF48s_g2d_repL hg
  simp only [burnsideF48s_g2dCheckA, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true, decide_eq_true_eq] at hA
  have hA' := hA i₁ h₁ i₂ h₂
  rw [burnsideF48s_g2dTL, burnsideF48s_getD_map_range _ h₁, burnsideF48s_getD_map_range _ h₂] at hA'
  have hg' : RepL (compL (compL (burnsideF48s_g2dEvL (burnsideF48s_g2dTelF i₁))
      (burnsideF48s_g2dEvL (u33Word "X"))) (burnsideF48s_g2dEvL (burnsideF48s_g2dTelF i₂)))
      (burnsideF48s_ev u33Img (burnsideF48s_g2dTelF i₁ ++ u33Word "X" ++ burnsideF48s_g2dTelF i₂)) := by
    rw [burnsideF48s_g2d_ev_tdt]
    exact repL_mul (repL_mul (hR _) (hR _)) (hR _)
  rcases hA' with hne | ⟨k, hk, hkeq⟩
  · exfalso
    apply hne
    have h2 := repL_mul hg' hg'
    rw [hinv] at h2
    exact repL_unique h2 (repL_one 28)
  · refine ⟨k, hk, eq_of_repL hg' ?_⟩
    rw [hkeq, burnsideF48s_g2dAL, burnsideF48s_getD_map_range _ (show k < 64 by omega)]
    exact hR _

theorem burnsideF48s_g2d_specB (hg : burnsideF48s_g2dCheckGens () = true)
    (hB : burnsideF48s_g2dCheckB () = true) {i₁ i₂ : ℕ} (h₁ : i₁ < 32) (h₂ : i₂ < 32) :
    ∃ k < 64, burnsideF48s_ev u33Img
      (burnsideF48s_g2dTelF i₁ ++ u33Word "Y" ++ burnsideF48s_g2dTelF i₂) =
        burnsideF48s_ev u33Img (burnsideF48s_g2dBF k) := by
  have hR := burnsideF48s_g2d_repL hg
  simp only [burnsideF48s_g2dCheckB, List.all_eq_true, List.mem_range, List.any_eq_true,
    decide_eq_true_eq] at hB
  obtain ⟨k, hk, hkeq⟩ := hB i₁ h₁ i₂ h₂
  rw [burnsideF48s_g2dTL, burnsideF48s_getD_map_range _ h₁, burnsideF48s_getD_map_range _ h₂,
    burnsideF48s_g2dBL, burnsideF48s_getD_map_range _ hk] at hkeq
  refine ⟨k, hk, eq_of_repL ?_ (hR _)⟩
  rw [burnsideF48s_g2d_ev_tdt, ← hkeq]
  exact repL_mul (repL_mul (hR _) (hR _)) (hR _)

theorem burnsideF48s_g2d_specCand (hg : burnsideF48s_g2dCheckGens () = true)
    (hC : burnsideF48s_g2dCheckCand () = true) {a b c : ℕ} (ha : a < 8) (hb : b < 64)
    (hc : c < 8) :
    ∃ j < 4, ∃ t < 32, ∃ r < 32,
      burnsideF48s_ev u33Img (burnsideF48s_g2dTelF t) * burnsideF48s_ev u33Img (burnsideF48s_g2dAF a) *
          (burnsideF48s_ev u33Img (burnsideF48s_g2dTelF t))⁻¹ = burnsideF48s_ev u33Img (u33Word "Xs") ∧
      burnsideF48s_ev u33Img (burnsideF48s_g2dTelF t) * burnsideF48s_ev u33Img (burnsideF48s_g2dBF b) *
          (burnsideF48s_ev u33Img (burnsideF48s_g2dTelF t))⁻¹ *
          burnsideF48s_ev u33Img (burnsideF48s_g2dTelF r) = burnsideF48s_ev u33Img (u33Word "Y") ∧
      (burnsideF48s_ev u33Img (burnsideF48s_g2dTelF r))⁻¹ *
          (burnsideF48s_ev u33Img (burnsideF48s_g2dTelF t) *
            burnsideF48s_ev u33Img (burnsideF48s_g2dAF c) *
            (burnsideF48s_ev u33Img (burnsideF48s_g2dTelF t))⁻¹) *
          burnsideF48s_ev u33Img (burnsideF48s_g2dTelF r) =
        burnsideF48s_ev u33Img (u33Word (burnsideF48s_g2dCandV.getD j "")) := by
  have hR := burnsideF48s_g2d_repL hg
  have hRi : ∀ w, RepL (burnsideF48s_g2dEvL (burnsideF48s_invW w))
      (burnsideF48s_ev u33Img w)⁻¹ := fun w => by
    rw [← burnsideF48s_ev_invW]
    exact hR _
  simp only [burnsideF48s_g2dCheckCand, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hC
  obtain ⟨⟨⟨⟨⟨hj, ht⟩, hr⟩, e1⟩, e2⟩, e3⟩ := hC a ha b hb c hc
  simp only [burnsideF48s_g2dTL, burnsideF48s_g2dTiL, burnsideF48s_g2dAL, burnsideF48s_g2dBL,
    burnsideF48s_g2dVL] at e1 e2 e3
  rw [burnsideF48s_getD_map_range _ ht, burnsideF48s_getD_map_range _ ht,
    burnsideF48s_getD_map_range _ (by omega : a < 64)] at e1
  rw [burnsideF48s_getD_map_range _ ht, burnsideF48s_getD_map_range _ ht,
    burnsideF48s_getD_map_range _ hr, burnsideF48s_getD_map_range _ hb] at e2
  rw [burnsideF48s_getD_map_range _ ht, burnsideF48s_getD_map_range _ ht,
    burnsideF48s_getD_map_range _ hr, burnsideF48s_getD_map_range _ hr,
    burnsideF48s_getD_map_range _ (by omega : c < 64), burnsideF48s_getD_map_range _ hj] at e3
  refine ⟨_, hj, _, ht, _, hr, ?_, ?_, ?_⟩
  · refine eq_of_repL ?_ (hR _)
    rw [← e1]
    exact repL_mul (repL_mul (hR _) (hR _)) (hRi _)
  · refine eq_of_repL ?_ (hR _)
    rw [← e2]
    exact repL_mul (repL_mul (repL_mul (hR _) (hR _)) (hRi _)) (hR _)
  · refine eq_of_repL ?_ (hR _)
    rw [← e3]
    exact repL_mul (repL_mul (hRi _) (repL_mul (repL_mul (hR _) (hR _)) (hRi _))) (hR _)

theorem burnsideF48s_g2d_specRel (hg : burnsideF48s_g2dCheckGens () = true) {j : ℕ}
    (hj : burnsideF48s_g2dEvL (burnsideF48s_g2dCand j) = List.range 28) :
    burnsideF48s_ev u33Img (burnsideF48s_g2dCand j) = 1 :=
  eq_of_repL (hj ▸ burnsideF48s_g2d_repL hg _) (repL_one 28)

end Model

section U33

noncomputable def burnsideF48s_g2dLG : Fin 5 → U33G := fun i => PresentedGroup.of i

theorem burnsideF48s_g2d_hom_ev (w : List (Fin 5 × Bool)) :
    u33PresHom (burnsideF48s_ev burnsideF48s_g2dLG w) = burnsideF48s_ev u33Img w :=
  (burnsideF48s_ev_map u33PresHom burnsideF48s_g2dLG w).symm.trans
    (burnsideF48s_ev_congr w fun l _ => u33PresHom_of l.1)

theorem burnsideF48s_g2d_genPG : (fun k : Fin 5 => u33GenPG k.val) = burnsideF48s_g2dLG :=
  funext u33GenPG_of

theorem burnsideF48s_g2d_tel (i : Fin 32) :
    u33Data.Tel i = burnsideF48s_ev burnsideF48s_g2dLG (burnsideF48s_g2dTelF i) := by
  show wordProd u33GenPG (u33W (u33TelWords.getD i "")) = _
  rw [burnsideF48s_wordProd_u33W, burnsideF48s_g2d_genPG]
  rfl

theorem burnsideF48s_g2d_D1 :
    u33Data.D 1 = burnsideF48s_ev burnsideF48s_g2dLG (u33Word "X") := by
  show wordProd u33GenPG (u33W (u33DWords.getD 1 "")) = _
  rw [burnsideF48s_wordProd_u33W, burnsideF48s_g2d_genPG]
  rfl

theorem burnsideF48s_g2d_D2 :
    u33Data.D 2 = burnsideF48s_ev burnsideF48s_g2dLG (u33Word "Y") := by
  show wordProd u33GenPG (u33W (u33DWords.getD 2 "")) = _
  rw [burnsideF48s_wordProd_u33W, burnsideF48s_g2d_genPG]
  rfl

theorem burnsideF48s_g2d_tel_mem {i : ℕ} (hi : i < 32) :
    burnsideF48s_ev burnsideF48s_g2dLG (burnsideF48s_g2dTelF i) ∈ u33Data.T := by
  have := u33Data.Tel_mem_T ⟨i, hi⟩
  rwa [burnsideF48s_g2d_tel] at this

theorem burnsideF48s_g2d_decA {u : U33G} (hu : u ∈ u33Data.A) (huT : u ∉ u33Data.T) :
    ∃ i₁ i₂ : ℕ, i₁ < 32 ∧ i₂ < 32 ∧ u = burnsideF48s_ev burnsideF48s_g2dLG
      (burnsideF48s_g2dTelF i₁ ++ u33Word "X" ++ burnsideF48s_g2dTelF i₂) := by
  obtain ⟨j, hj, i₁, i₂, rfl⟩ := (u33Data.mem_A_iff u).1 hu
  rcases hj with rfl | rfl
  · exfalso
    apply huT
    rw [u33Data.D_zero, mul_one]
    exact u33Data.T.mul_mem (u33Data.Tel_mem_T i₁) (u33Data.Tel_mem_T i₂)
  · refine ⟨i₁, i₂, i₁.2, i₂.2, ?_⟩
    rw [burnsideF48s_ev_append, burnsideF48s_ev_append, ← burnsideF48s_g2d_tel,
      ← burnsideF48s_g2d_tel, ← burnsideF48s_g2d_D1]
    rfl

theorem burnsideF48s_g2d_decB {w : U33G} (hw : w ∈ u33Data.B) (hwT : w ∉ u33Data.T) :
    ∃ i₁ i₂ : ℕ, i₁ < 32 ∧ i₂ < 32 ∧ w = burnsideF48s_ev burnsideF48s_g2dLG
      (burnsideF48s_g2dTelF i₁ ++ u33Word "Y" ++ burnsideF48s_g2dTelF i₂) := by
  obtain ⟨j, hj, i₁, i₂, rfl⟩ := (u33Data.mem_B_iff w).1 hw
  rcases hj with rfl | rfl
  · exfalso
    apply hwT
    rw [u33Data.D_zero, mul_one]
    exact u33Data.T.mul_mem (u33Data.Tel_mem_T i₁) (u33Data.Tel_mem_T i₂)
  · refine ⟨i₁, i₂, i₁.2, i₂.2, ?_⟩
    rw [burnsideF48s_ev_append, burnsideF48s_ev_append, ← burnsideF48s_g2d_tel,
      ← burnsideF48s_g2d_tel, ← burnsideF48s_g2d_D2]
    rfl

theorem burnsideF48s_g2d_LG_memB {i : Fin 5} (hi : i ≠ 3) : burnsideF48s_g2dLG i ∈ u33Data.B := by
  have e : ∀ k : Fin 5, burnsideF48s_g2dLG k = u33GenPG k.val := fun k => (u33GenPG_of k).symm
  fin_cases i
  · rw [e]; exact u33Data.T_le_B u33Data.a_mem_T
  · rw [e]; exact u33Data.T_le_B u33Data.b_mem_T
  · rw [e]; exact u33Data.T_le_B u33Data.s_mem_T
  · exact absurd rfl hi
  · rw [e]; exact u33Data.y_mem_B

theorem burnsideF48s_g2d_LG_memA {i : Fin 5} (hi : i ≠ 4) : burnsideF48s_g2dLG i ∈ u33Data.A := by
  have e : ∀ k : Fin 5, burnsideF48s_g2dLG k = u33GenPG k.val := fun k => (u33GenPG_of k).symm
  fin_cases i
  · rw [e]; exact u33Data.T_le_A u33Data.a_mem_T
  · rw [e]; exact u33Data.T_le_A u33Data.b_mem_T
  · rw [e]; exact u33Data.T_le_A u33Data.s_mem_T
  · rw [e]; exact u33Data.x_mem_A
  · exact absurd rfl hi

theorem burnsideF48s_g2d_sup : u33Data.B ⊔ u33Data.A = ⊤ := by
  rw [eq_top_iff, ← u33Data.gen, Subgroup.closure_le]
  rintro g (rfl | rfl | rfl | rfl | rfl)
  · exact Subgroup.mem_sup_left (u33Data.T_le_B u33Data.a_mem_T)
  · exact Subgroup.mem_sup_left (u33Data.T_le_B u33Data.b_mem_T)
  · exact Subgroup.mem_sup_left (u33Data.T_le_B u33Data.s_mem_T)
  · exact Subgroup.mem_sup_right u33Data.x_mem_A
  · exact Subgroup.mem_sup_left u33Data.y_mem_B

theorem burnsideF48s_g2d_covB : ∀ z ∈ u33Data.B, ∃ w : List (Fin 5 × Bool),
    (∀ l ∈ w, burnsideF48s_g2dLG l.1 ∈ u33Data.B) ∧ burnsideF48s_ev burnsideF48s_g2dLG w = z := by
  intro z hz
  have e : ∀ k : Fin 5, burnsideF48s_g2dLG k = u33GenPG k.val := fun k => (u33GenPG_of k).symm
  refine burnsideF48s_exists_word burnsideF48s_g2dLG (fun i => burnsideF48s_g2dLG i ∈ u33Data.B)
    (S := {u33Data.a, u33Data.b, u33Data.s, u33Data.y}) ?_ hz
  rintro g (rfl | rfl | rfl | rfl)
  · exact ⟨0, burnsideF48s_g2d_LG_memB (by decide), e 0⟩
  · exact ⟨1, burnsideF48s_g2d_LG_memB (by decide), e 1⟩
  · exact ⟨2, burnsideF48s_g2d_LG_memB (by decide), e 2⟩
  · exact ⟨4, burnsideF48s_g2d_LG_memB (by decide), e 4⟩

theorem burnsideF48s_g2d_covA : ∀ z ∈ u33Data.A, ∃ w : List (Fin 5 × Bool),
    (∀ l ∈ w, burnsideF48s_g2dLG l.1 ∈ u33Data.A) ∧ burnsideF48s_ev burnsideF48s_g2dLG w = z := by
  intro z hz
  have e : ∀ k : Fin 5, burnsideF48s_g2dLG k = u33GenPG k.val := fun k => (u33GenPG_of k).symm
  refine burnsideF48s_exists_word burnsideF48s_g2dLG (fun i => burnsideF48s_g2dLG i ∈ u33Data.A)
    (S := {u33Data.a, u33Data.b, u33Data.s, u33Data.x}) ?_ hz
  rintro g (rfl | rfl | rfl | rfl)
  · exact ⟨0, burnsideF48s_g2d_LG_memA (by decide), e 0⟩
  · exact ⟨1, burnsideF48s_g2d_LG_memA (by decide), e 1⟩
  · exact ⟨2, burnsideF48s_g2d_LG_memA (by decide), e 2⟩
  · exact ⟨3, burnsideF48s_g2d_LG_memA (by decide), e 3⟩

theorem burnsideF48s_g2dAmal_facts : ∀ r ∈ burnsideF48s_g2dAmal, r ∈ u33PresRels ∧
    ((∀ l ∈ r, l.1 ≠ 3) ∨ (∀ l ∈ r, l.1 ≠ 4)) := by
  decide +kernel

theorem burnsideF48s_g2d_amal_U33 : ∀ r ∈ burnsideF48s_g2dAmal,
    burnsideF48s_ev burnsideF48s_g2dLG r = 1 := by
  intro r hr
  apply u33PresHom_injective
  rw [burnsideF48s_g2d_hom_ev, map_one]
  exact u33Img_relators r (burnsideF48s_g2dAmal_facts r hr).1

end U33

section Core

theorem burnsideF48s_g2d_card_PG (j : ℕ) (hj : j < 4) :
    Finite (PG 5 (burnsideF48s_g2dWs j)) ∧
      Nat.card (PG 5 (burnsideF48s_g2dWs j)) ≤ if j % 2 = 1 then 6048 else 96 :=
  Certificates.certificate7532 j hj

theorem burnsideF48s_g2d_core {Y : Type} [Group Y] (f₁ : ↥u33Data.B →* Y) (f₂ : ↥u33Data.A →* Y)
    (h12 : ∀ (t : U33G) (h : t ∈ u33Data.B ⊓ u33Data.A), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hgen : f₁.range ⊔ f₂.range = ⊤) (hcard : 6048 ≤ Nat.card Y)
    {u v w : U33G} (hu : u ∈ u33Data.A) (huT : u ∉ u33Data.T) (hu2 : u * u = 1)
    (hv : v ∈ u33Data.A) (hvT : v ∉ u33Data.T) (hv2 : v * v = 1)
    (hw : w ∈ u33Data.B) (hwT : w ∉ u33Data.T)
    (hrel : (f₂ ⟨u, hu⟩ * f₁ ⟨w, hw⟩ * f₂ ⟨v, hv⟩ * (f₁ ⟨w, hw⟩)⁻¹) ^ 3 = 1) :
    ∃ φ : Y ≃* U33G, (∀ z : ↥u33Data.B, φ (f₁ z) = z) ∧ (∀ z : ↥u33Data.A, φ (f₂ z) = z) := by
  obtain ⟨cg, cA, cB, cC, cR1, cR3⟩ := Certificates.certificate7533
  set L := burnsideF48s_g2dLG with hL
  obtain ⟨i₁, i₂, h₁, h₂, hueq⟩ := burnsideF48s_g2d_decA hu huT
  obtain ⟨i₅, i₆, h₅, h₆, hveq⟩ := burnsideF48s_g2d_decA hv hvT
  obtain ⟨i₃, i₄, h₃, h₄, hweq⟩ := burnsideF48s_g2d_decB hw hwT
  have hperm : ∀ {z : U33G} {w' : List (Fin 5 × Bool)}, z = burnsideF48s_ev L w' →
      u33PresHom z = burnsideF48s_ev u33Img w' := by
    intro z w' h
    rw [h]
    exact burnsideF48s_g2d_hom_ev w'
  have hsq : ∀ {z : U33G} {w' : List (Fin 5 × Bool)}, z = burnsideF48s_ev L w' → z * z = 1 →
      burnsideF48s_ev u33Img w' * burnsideF48s_ev u33Img w' = 1 := by
    intro z w' h hz
    rw [← hperm h, ← map_mul, hz, map_one]
  obtain ⟨ka, hka, hkaeq⟩ := burnsideF48s_g2d_specA cg cA h₁ h₂ (hsq hueq hu2)
  obtain ⟨kc, hkc, hkceq⟩ := burnsideF48s_g2d_specA cg cA h₅ h₆ (hsq hveq hv2)
  obtain ⟨kb, hkb, hkbeq⟩ := burnsideF48s_g2d_specB cg cB h₃ h₄
  obtain ⟨j, hj, t, ht, r, hr, e1, e2, e3⟩ := burnsideF48s_g2d_specCand cg cC hka hkb hkc
  set τ := burnsideF48s_ev L (burnsideF48s_g2dTelF t) with hτ
  set ρ := burnsideF48s_ev L (burnsideF48s_g2dTelF r) with hρ
  have hτT : τ ∈ u33Data.T := burnsideF48s_g2d_tel_mem ht
  have hρT : ρ ∈ u33Data.T := burnsideF48s_g2d_tel_mem hr
  have hτp : u33PresHom τ = burnsideF48s_ev u33Img (burnsideF48s_g2dTelF t) := hperm rfl
  have hρp : u33PresHom ρ = burnsideF48s_ev u33Img (burnsideF48s_g2dTelF r) := hperm rfl
  have hup : u33PresHom u = burnsideF48s_ev u33Img (burnsideF48s_g2dAF ka) :=
    (hperm hueq).trans hkaeq
  have hvp : u33PresHom v = burnsideF48s_ev u33Img (burnsideF48s_g2dAF kc) :=
    (hperm hveq).trans hkceq
  have hwp : u33PresHom w = burnsideF48s_ev u33Img (burnsideF48s_g2dBF kb) :=
    (hperm hweq).trans hkbeq
  have E1 : τ * u * τ⁻¹ = burnsideF48s_ev L (u33Word "Xs") := by
    apply u33PresHom_injective
    rw [map_mul, map_mul, map_inv, hτp, hup, e1, burnsideF48s_g2d_hom_ev]
  have E2 : τ * w * τ⁻¹ * ρ = burnsideF48s_ev L (u33Word "Y") := by
    apply u33PresHom_injective
    rw [map_mul, map_mul, map_mul, map_inv, hτp, hwp, hρp, e2, burnsideF48s_g2d_hom_ev]
  have E3 : ρ⁻¹ * (τ * v * τ⁻¹) * ρ =
      burnsideF48s_ev L (u33Word (burnsideF48s_g2dCandV.getD j "")) := by
    apply u33PresHom_injective
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hτp, hvp, hρp, e3,
      burnsideF48s_g2d_hom_ev]
  set yL := burnsideF48s_yL L f₁ f₂ with hyL
  have h12' : ∀ (t : U33G) (h : t ∈ u33Data.B ⊓ u33Data.A), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩ := h12
  have hX : ∀ l ∈ u33Word "Xs", L l.1 ∈ u33Data.A := by
    intro l hl
    exact burnsideF48s_g2d_LG_memA (by revert l; decide)
  have hYw : ∀ l ∈ u33Word "Y", L l.1 ∈ u33Data.B := by
    intro l hl
    exact burnsideF48s_g2d_LG_memB (by revert l; decide)
  have hV : ∀ l ∈ u33Word (burnsideF48s_g2dCandV.getD j ""), L l.1 ∈ u33Data.A := by
    intro l hl
    refine burnsideF48s_g2d_LG_memA ?_
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      revert l <;> decide
  obtain ⟨mU, eU⟩ := burnsideF48s_ev_yL_B (f₁ := f₁) (f₂ := f₂) h12' _ hX
  obtain ⟨mW, eW⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) _ hYw
  obtain ⟨mV, eV⟩ := burnsideF48s_ev_yL_B (f₁ := f₁) (f₂ := f₂) h12' _ hV
  have hτA : τ ∈ u33Data.A := u33Data.T_le_A hτT
  have hτB : τ ∈ u33Data.B := u33Data.T_le_B hτT
  have hρA : ρ ∈ u33Data.A := u33Data.T_le_A hρT
  have hρB : ρ ∈ u33Data.B := u33Data.T_le_B hρT
  have hτ12 : f₁ ⟨τ, hτB⟩ = f₂ ⟨τ, hτA⟩ := h12 τ ⟨hτB, hτA⟩
  have hρ12 : f₁ ⟨ρ, hρB⟩ = f₂ ⟨ρ, hρA⟩ := h12 ρ ⟨hρB, hρA⟩
  have fU : f₂ ⟨_, mU⟩ = f₂ ⟨τ, hτA⟩ * f₂ ⟨u, hu⟩ * (f₂ ⟨τ, hτA⟩)⁻¹ := by
    have e : (⟨_, mU⟩ : ↥u33Data.A) = ⟨τ, hτA⟩ * ⟨u, hu⟩ * (⟨τ, hτA⟩ : ↥u33Data.A)⁻¹ :=
      Subtype.ext E1.symm
    rw [e, map_mul, map_mul, map_inv]
  have fW : f₁ ⟨_, mW⟩ = f₂ ⟨τ, hτA⟩ * f₁ ⟨w, hw⟩ * (f₂ ⟨τ, hτA⟩)⁻¹ * f₂ ⟨ρ, hρA⟩ := by
    have e : (⟨_, mW⟩ : ↥u33Data.B) =
        ⟨τ, hτB⟩ * ⟨w, hw⟩ * (⟨τ, hτB⟩ : ↥u33Data.B)⁻¹ * ⟨ρ, hρB⟩ :=
      Subtype.ext E2.symm
    rw [e, map_mul, map_mul, map_mul, map_inv, hτ12, hρ12]
  have fV : f₂ ⟨_, mV⟩ = (f₂ ⟨ρ, hρA⟩)⁻¹ * (f₂ ⟨τ, hτA⟩ * f₂ ⟨v, hv⟩ * (f₂ ⟨τ, hτA⟩)⁻¹) *
      f₂ ⟨ρ, hρA⟩ := by
    have e : (⟨_, mV⟩ : ↥u33Data.A) = (⟨ρ, hρA⟩ : ↥u33Data.A)⁻¹ *
        (⟨τ, hτA⟩ * ⟨v, hv⟩ * (⟨τ, hτA⟩ : ↥u33Data.A)⁻¹) * ⟨ρ, hρA⟩ :=
      Subtype.ext E3.symm
    rw [e, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hcandY : burnsideF48s_ev yL (burnsideF48s_g2dCand j) = 1 := by
    unfold burnsideF48s_g2dCand burnsideF48s_g2dRelW
    rw [burnsideF48s_ev_replicate, burnsideF48s_ev_append, burnsideF48s_ev_append,
      burnsideF48s_ev_append, burnsideF48s_ev_invW, eU, eW, eV, fU, fW, fV]
    set T₀ := f₂ ⟨τ, hτA⟩
    set R₀ := f₂ ⟨ρ, hρA⟩
    have e : T₀ * f₂ ⟨u, hu⟩ * T₀⁻¹ * (T₀ * f₁ ⟨w, hw⟩ * T₀⁻¹ * R₀) *
        (R₀⁻¹ * (T₀ * f₂ ⟨v, hv⟩ * T₀⁻¹) * R₀) * (T₀ * f₁ ⟨w, hw⟩ * T₀⁻¹ * R₀)⁻¹ =
        T₀ * (f₂ ⟨u, hu⟩ * f₁ ⟨w, hw⟩ * f₂ ⟨v, hv⟩ * (f₁ ⟨w, hw⟩)⁻¹) * T₀⁻¹ := by
      group
    rw [e, ← MulAut.conj_apply, ← map_pow, hrel, map_one]
  have hamalY : ∀ r ∈ burnsideF48s_g2dAmal, burnsideF48s_ev yL r = 1 := by
    intro r hr
    rcases (burnsideF48s_g2dAmal_facts r hr).2 with h3 | h4
    · obtain ⟨m, e⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) r
        (fun l hl => burnsideF48s_g2d_LG_memB (h3 l hl))
      rw [e]
      have : (⟨burnsideF48s_ev L r, m⟩ : ↥u33Data.B) = 1 :=
        Subtype.ext (burnsideF48s_g2d_amal_U33 r hr)
      rw [this, map_one]
    · obtain ⟨m, e⟩ := burnsideF48s_ev_yL_B (f₁ := f₁) (f₂ := f₂) h12' r
        (fun l hl => burnsideF48s_g2d_LG_memA (h4 l hl))
      rw [e]
      have : (⟨burnsideF48s_ev L r, m⟩ : ↥u33Data.A) = 1 :=
        Subtype.ext (burnsideF48s_g2d_amal_U33 r hr)
      rw [this, map_one]
  have hY : ∀ r ∈ burnsideF48s_g2dWs j, burnsideF48s_ev yL r = 1 := by
    intro r hr
    rcases List.mem_append.1 hr with h | h
    · exact hamalY r h
    · rw [List.mem_singleton] at h
      rw [h]
      exact hcandY
  obtain ⟨hfin, hcardP⟩ := burnsideF48s_g2d_card_PG j hj
  haveI := hfin
  have hYle := burnsideF48s_core_card_le (L := L) (f₁ := f₁) (f₂ := f₂) h12' hgen
    burnsideF48s_g2d_covB burnsideF48s_g2d_covA hY
  have hj13 : j % 2 = 1 := by
    by_contra hne
    rw [if_neg hne] at hcardP
    omega
  rw [if_pos hj13] at hcardP
  have hcandU : burnsideF48s_ev L (burnsideF48s_g2dCand j) = 1 := by
    apply u33PresHom_injective
    rw [burnsideF48s_g2d_hom_ev, map_one]
    rcases (show j = 1 ∨ j = 3 by omega) with rfl | rfl
    · exact burnsideF48s_g2d_specRel cg cR1
    · exact burnsideF48s_g2d_specRel cg cR3
  have hD : ∀ r ∈ burnsideF48s_g2dWs j, burnsideF48s_ev L r = 1 := by
    intro r hr
    rcases List.mem_append.1 hr with h | h
    · exact burnsideF48s_g2d_amal_U33 r h
    · rw [List.mem_singleton] at h
      rw [h]
      exact hcandU
  haveI : Finite U33G := Nat.finite_of_card_ne_zero (by rw [card_u33Pres]; norm_num)
  exact burnsideF48s_core_gen h12' hgen burnsideF48s_g2d_sup burnsideF48s_g2d_covB
    burnsideF48s_g2d_covA hD hY (by rw [card_u33Pres]; exact hcardP)
    (by rw [card_u33Pres]; exact hcard)

end Core

section Main

theorem burnsideF48s_small_G2d (h45 : F_4_5) (h46 : F_4_6) {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .G2d p f Gp M₁ M₂) : F48Concl .G2d p f Gp M₁ M₂ := by
  haveI : Finite E := hyp.finite
  have hext := burnsideF48s_isLieExtGroup_E ChF.nativeChartCompatibility hyp
  have hGp : Gp = ⊤ := hyp.canonical (Or.inl rfl)
  subst hGp
  obtain ⟨hp2, hf1, -⟩ := hyp.model
  subst hp2
  subst hf1
  obtain ⟨Φ, hT, hB, hA⟩ := burnsideF4nB_ident hyp
  have hcardE : Nat.card E = 6048 := by
    rw [← Nat.card_congr Φ.toEquiv, card_u33Pres]
  refine burnsideF48s_concl_of_qe hext (incl M₁ M₂) (incl_faithful M₁ M₂)
    (burnsideF4b_IotaSmall_of (burnsideF4k_facts46All h46) h45 .G2d 2 1 E ⊤ M₁ M₂ hyp)
    ((MulEquiv.subgroupCongr hyp.gen).trans Subgroup.topEquiv) ?_
  intro Y _ β hβ hs
  have h13 := (burnside_as_F_4_13_of h45 h46 .G2d 2 1 E ⊤ M₁ M₂ hyp Y β hβ hs).2
  rw [card_G0, hcardE] at h13
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [h13]; norm_num)
  obtain ⟨u, v, w, huM, hvM, hwM, hu2, hv2, hrel⟩ := burnsideF48s_g2d_rel h45 h46 hyp β hβ hs
  have hmemΦ : ∀ {P : Subgroup U33G} {M : Subgroup E}, P.map Φ.toMonoidHom = M →
      ∀ z : U33G, Φ z ∈ M ↔ z ∈ P := by
    intro P M hPM z
    rw [← hPM]
    exact Subgroup.mem_map_iff_mem Φ.injective
  let r₁ : ↥u33Data.B ≃* ↥M₁ := (Φ.subgroupMap u33Data.B).trans (MulEquiv.subgroupCongr hB)
  let r₂ : ↥u33Data.A ≃* ↥M₂ := (Φ.subgroupMap u33Data.A).trans (MulEquiv.subgroupCongr hA)
  have hr₁ : ∀ z : ↥u33Data.B, ((r₁ z : ↥M₁) : E) = Φ z := fun _ => rfl
  have hr₂ : ∀ z : ↥u33Data.A, ((r₂ z : ↥M₂) : E) = Φ z := fun _ => rfl
  let f₁ : ↥u33Data.B →* Y := β.φ1.comp r₁.toMonoidHom
  let f₂ : ↥u33Data.A →* Y := β.φ2.comp r₂.toMonoidHom
  have h12β : ∀ (t : E) (h1 : t ∈ M₁) (h2 : t ∈ M₂), β.φ1 ⟨t, h1⟩ = β.φ2 ⟨t, h2⟩ :=
    fun t h1 h2 => (β.comm1 ⟨t, ⟨h1, h2⟩⟩).trans (β.comm2 ⟨t, ⟨h1, h2⟩⟩).symm
  have hf12 : ∀ (t : U33G) (h : t ∈ u33Data.B ⊓ u33Data.A), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩ :=
    fun t h => h12β (Φ t) _ _
  have hfgen : f₁.range ⊔ f₂.range = ⊤ := by
    rw [show f₁.range = β.φ1.range from burnsideF48s_range_comp_mulEquiv_g2d _ _,
      show f₂.range = β.φ2.range from burnsideF48s_range_comp_mulEquiv_g2d _ _]
    exact β.gen
  have hpre : ∀ {P : Subgroup U33G} {M : Subgroup E}, P.map Φ.toMonoidHom = M →
      ∀ m : ↥M, ∃ z : U33G, z ∈ P ∧ Φ z = m := by
    intro P M hPM m
    obtain ⟨z, hz, hzm⟩ : (m : E) ∈ P.map Φ.toMonoidHom := by rw [hPM]; exact m.2
    exact ⟨z, hz, hzm⟩
  obtain ⟨u', hu', hu'e⟩ := hpre hA u
  obtain ⟨v', hv', hv'e⟩ := hpre hA v
  obtain ⟨w', hw', hw'e⟩ := hpre hB w
  have hnotT : ∀ {z : U33G} {M : Subgroup E}, (Φ z : E) ∉ M → (M₁ ⊓ M₂ ≤ M) → z ∉ u33Data.T := by
    intro z M hz hle hzT
    exact hz (hle ((hmemΦ hT z).2 hzT))
  have hu'T : u' ∉ u33Data.T := hnotT (by rw [hu'e]; exact huM) inf_le_left
  have hv'T : v' ∉ u33Data.T := hnotT (by rw [hv'e]; exact hvM) inf_le_left
  have hw'T : w' ∉ u33Data.T := hnotT (by rw [hw'e]; exact hwM) inf_le_right
  have hsq : ∀ {M : Subgroup E} {z : U33G} {m : ↥M}, Φ z = m → m * m = 1 → z * z = 1 := by
    intro M z m hzm hm
    apply Φ.injective
    rw [map_mul, hzm, map_one]
    exact congrArg Subtype.val hm
  have hu'2 : u' * u' = 1 := hsq hu'e hu2
  have hv'2 : v' * v' = 1 := hsq hv'e hv2
  have eu : r₂ ⟨u', hu'⟩ = u := Subtype.ext hu'e
  have evv : r₂ ⟨v', hv'⟩ = v := Subtype.ext hv'e
  have ew : r₁ ⟨w', hw'⟩ = w := Subtype.ext hw'e
  have hrel' : (f₂ ⟨u', hu'⟩ * f₁ ⟨w', hw'⟩ * f₂ ⟨v', hv'⟩ * (f₁ ⟨w', hw'⟩)⁻¹) ^ 3 = 1 := by
    show (β.φ2 (r₂ ⟨u', hu'⟩) * β.φ1 (r₁ ⟨w', hw'⟩) * β.φ2 (r₂ ⟨v', hv'⟩) *
      (β.φ1 (r₁ ⟨w', hw'⟩))⁻¹) ^ 3 = 1
    rw [eu, evv, ew]
    exact hrel
  have hcardY : 6048 ≤ Nat.card Y := by
    rw [h13]
  obtain ⟨φ, hφ1, hφ2⟩ := burnsideF48s_g2d_core f₁ f₂ hf12 hfgen hcardY hu' hu'T hu'2 hv' hv'T hv'2
    hw' hw'T hrel'
  let eE : E ≃* ↥(M₁ ⊔ M₂) := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hyp.gen.symm)
  refine burnsideF48s_qe_of_equiv β hβ (φ.trans (Φ.trans eE)) (fun x => ?_) (fun x => ?_)
  · obtain ⟨z, hz, hzx⟩ := hpre hB x
    have hx : x = r₁ ⟨z, hz⟩ := Subtype.ext hzx.symm
    show ((eE (Φ (φ (β.φ1 x))) : ↥(M₁ ⊔ M₂)) : E) ∈ M₁
    rw [hx]
    have : φ (β.φ1 (r₁ ⟨z, hz⟩)) = z := hφ1 ⟨z, hz⟩
    rw [this]
    exact (hmemΦ hB z).2 hz
  · obtain ⟨z, hz, hzx⟩ := hpre hA x
    have hx : x = r₂ ⟨z, hz⟩ := Subtype.ext hzx.symm
    show ((eE (Φ (φ (β.φ2 x))) : ↥(M₁ ⊔ M₂)) : E) ∈ M₂
    rw [hx]
    have : φ (β.φ2 (r₂ ⟨z, hz⟩)) = z := hφ2 ⟨z, hz⟩
    rw [this]
    exact (hmemΦ hA z).2 hz

end Main

end CFSG.ASVolI
