module

public import CFSG.Milestones.ASVolI.F48.Small.Eng
public import CFSG.Milestones.ASVolI.F48.Small.AutBase
public import Certificates.Certificate7552
public import Certificates.Certificate7553
public import Certificates.Certificate7554
public import Certificates.Certificate7555
public import Certificates.Certificate7556

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42 CFSG.Quasithin.H13.F431.U42Aut CFSG.CosetTable
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 f45)

@[expose] noncomputable def burnsideF48s_u42eK (j : ℕ) : Subgroup Ah :=
  Subgroup.closure {z | ∃ w ∈ burnsideF48s_u42eKW j, z = burnsideF48s_ev burnsideF48s_u42eG w}

@[expose] def burnsideF48s_u42eC0 : Subgroup Ah :=
  Subgroup.zpowers (burnsideF48s_u42eG 0 ^ 2)

section Facts

theorem burnsideF48s_u42e_checks : burnsideF48s_u42eCheckGens () = true ∧
    burnsideF48s_u42eCheckRels () = true ∧ burnsideF48s_u42eCheckLetters () = true ∧
    burnsideF48s_u42eCheckClosed () = true ∧ burnsideF48s_u42eCheckCand () = true ∧
    burnsideF48s_u42eCheckClass () = true :=
  ⟨Certificates.certificate7553.1, Certificates.certificate7553.2.1,
    Certificates.certificate7553.2.2, Certificates.certificate7554,
    Certificates.certificate7555, Certificates.certificate7556⟩

theorem burnsideF48s_u42e_rep :
    burnsideF48s_eRec burnsideF48s_u42eG burnsideF48s_u42eLS burnsideF48s_u42eLSi := by
  have hg := burnsideF48s_u42e_checks.1
  simp only [burnsideF48s_u42eCheckGens, Bool.and_eq_true, decide_eq_true_eq] at hg
  intro i
  have hi : (i : ℕ) < burnsideF48s_u42eXY.length := by
    have := i.2
    simp only [burnsideF48s_u42eXY, List.length_cons, List.length_nil]
    omega
  constructor
  · rw [hg.1, burnsideF48s_e_getD_map _ _ hi [] []]
    exact repL_wordAP _
  · rw [hg.2, burnsideF48s_e_getD_map _ _ hi [] []]
    show RepL _ (wordAP _)⁻¹
    rw [← wordAP_invAL]
    exact repL_wordAP _

theorem burnsideF48s_u42e_G_mem1 {i : Fin 5} (h : i ≠ 3) :
    burnsideF48s_u42eG i ∈ burnsideF48s_u42eP1 := by
  fin_cases i
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · exact absurd rfl h
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))

theorem burnsideF48s_u42e_G_mem2 {i : Fin 5} (h : i ≠ 2) :
    burnsideF48s_u42eG i ∈ burnsideF48s_u42eP2 := by
  fin_cases i
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact absurd rfl h
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))

theorem burnsideF48s_u42e_G_mem_sup (i : Fin 5) :
    burnsideF48s_u42eG i ∈ burnsideF48s_u42eP1 ⊔ burnsideF48s_u42eP2 := by
  by_cases h : i = 3
  · subst h
    exact Subgroup.mem_sup_right (burnsideF48s_u42e_G_mem2 (by decide))
  · exact Subgroup.mem_sup_left (burnsideF48s_u42e_G_mem1 h)

theorem burnsideF48s_u42e_letters :
    (∀ w ∈ burnsideF48s_u42eP1W ++ burnsideF48s_u42eR1, ∀ l ∈ w, l.1 ≠ 3) ∧
    (∀ w ∈ burnsideF48s_u42eP2W ++ burnsideF48s_u42eR2, ∀ l ∈ w, l.1 ≠ 2) ∧
    (∀ w ∈ burnsideF48s_u42eC0W ++ burnsideF48s_u42eN0W, ∀ l ∈ w, l.1 ≠ 2 ∧ l.1 ≠ 3) ∧
    ∀ j ∈ List.range 7, (∀ w ∈ burnsideF48s_u42eU j, ∀ l ∈ w, l.1 ≠ 3) ∧
      (∀ w ∈ burnsideF48s_u42eV j, ∀ l ∈ w, l.1 ≠ 2) ∧
      ∀ w ∈ burnsideF48s_u42eKW j ++ burnsideF48s_u42eTW j ++ burnsideF48s_u42eW j, ∀ l ∈ w,
        l.1 ≠ 2 ∧ l.1 ≠ 3 := by
  have hl := burnsideF48s_u42e_checks.2.2.1
  simp only [burnsideF48s_u42eCheckLetters, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hl
  exact ⟨hl.1.1.1, hl.1.1.2, hl.1.2, fun j hj => ⟨(hl.2 j hj).1.1, (hl.2 j hj).1.2, (hl.2 j hj).2⟩⟩

theorem burnsideF48s_u42e_closed :
    burnsideF48s_u42eP1W.length = 1152 ∧ burnsideF48s_u42eP2W.length = 1920 ∧
    burnsideF48s_u42eP1W.getD 0 [(0, true)] = [] ∧ burnsideF48s_u42eP2W.getD 0 [(0, true)] = [] ∧
    burnsideF48s_u42eC0W = [[], burnsideF48s_u42eWord "AA", burnsideF48s_u42eWord "aa"] ∧
    (burnsideF48s_u42eU 3).length = 98 ∧
    burnsideF48s_eClosed (burnsideF48s_u42eP1W.map burnsideF48s_u42eEvL) burnsideF48s_u42eLS
      [0, 1, 2, 4] = true ∧
    burnsideF48s_eClosed (burnsideF48s_u42eP2W.map burnsideF48s_u42eEvL) burnsideF48s_u42eLS
      [0, 1, 3, 4] = true ∧
    ∀ j ∈ List.range 7, (burnsideF48s_u42eKW j).getD 0 [(0, true)] = [] ∧
      0 < (burnsideF48s_u42eKW j).length ∧
      (∀ c ∈ burnsideF48s_u42eC0W.map burnsideF48s_u42eEvL,
        ((burnsideF48s_u42eKW j).map burnsideF48s_u42eEvL).contains c = true) ∧
      burnsideF48s_eClosedW ((burnsideF48s_u42eKW j).map burnsideF48s_u42eEvL)
        ((burnsideF48s_u42eKW j).map burnsideF48s_u42eEvL) = true ∧
      (burnsideF48s_u42eU j).length ≤ (burnsideF48s_u42eV j).length ∧
      (burnsideF48s_u42eU j).length ≤ (burnsideF48s_u42eW j).length := by
  have hc := burnsideF48s_u42e_checks.2.2.2.1
  simp only [burnsideF48s_u42eCheckClosed, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun j hj => ?_⟩
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h9 j hj
  exact ⟨a1, a2, a3, a4, a5, a6⟩

theorem burnsideF48s_u42e_rels :
    (∀ w ∈ burnsideF48s_u42eR1 ++ burnsideF48s_u42eR2,
      burnsideF48s_ev burnsideF48s_u42eG w = 1) ∧
    (∀ k ∈ [0, 5, 8, 11, 17, 22, 27, 67, 73, 77, 83], burnsideF48s_ev burnsideF48s_u42eG
      (burnsideF48s_eCandRel 4 ((burnsideF48s_u42eU 3).getD k []) ((burnsideF48s_u42eV 3).getD k [])
        ((burnsideF48s_u42eW 3).getD k [])) = 1) ∧
    burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eWord "aa") ≠ 1 ∧
    ((burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eWord "apapap") : Ah) : P45) = x45 ∧
    ((burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eWord "bqpaqp") : Ah) : P45) = y45 ∧
    ((burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eWord "bpbpfb") : Ah) : P45) = f45 ∧
    ∀ j ∈ List.range 7, ((burnsideF48s_u42eKW j).map burnsideF48s_u42eEvL).Nodup := by
  have hr := burnsideF48s_u42e_checks.2.1
  simp only [burnsideF48s_u42eCheckRels, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at hr
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hr
  have hrep := burnsideF48s_u42e_rep
  have h4' : burnsideF48s_eEvL 45 burnsideF48s_u42eLS burnsideF48s_u42eLSi
      (burnsideF48s_u42eWord "apapap") = U42F431.xL := h4
  have h5' : burnsideF48s_eEvL 45 burnsideF48s_u42eLS burnsideF48s_u42eLSi
      (burnsideF48s_u42eWord "bqpaqp") = U42F431.yL := h5
  have h6' : burnsideF48s_eEvL 45 burnsideF48s_u42eLS burnsideF48s_u42eLSi
      (burnsideF48s_u42eWord "bpbpfb") = f45L := h6
  refine ⟨fun w hw => burnsideF48s_e_one hrep (h1 w hw), fun k hk => burnsideF48s_e_one hrep (h2 k hk),
    fun h => h3 ?_, ?_, ?_, ?_, h7⟩
  · exact repL_unique (burnsideF48s_e_repL hrep _) (h ▸ repL_one 45)
  · exact eq_of_repL (burnsideF48s_e_repL hrep _) (by rw [h4']; exact repL_x)
  · exact eq_of_repL (burnsideF48s_e_repL hrep _) (by rw [h5']; exact repL_y)
  · exact eq_of_repL (burnsideF48s_e_repL hrep _) (by rw [h6']; exact repL_f45)

theorem burnsideF48s_u42e_ev_aa :
    burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eWord "aa") = burnsideF48s_u42eG 0 ^ 2 := by
  simp [burnsideF48s_u42eWord, burnsideF48s_u42eLetter, burnsideF48s_ev, pow_succ, mul_assoc]

theorem burnsideF48s_u42e_ev_AA :
    burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eWord "AA") =
      (burnsideF48s_u42eG 0 ^ 2)⁻¹ := by
  simp [burnsideF48s_u42eWord, burnsideF48s_u42eLetter, burnsideF48s_ev, pow_succ, mul_assoc]

theorem burnsideF48s_u42e_a6 : burnsideF48s_u42eG 0 ^ 6 = 1 := by
  have h := burnsideF48s_u42e_rels.1 (burnsideF48s_u42eWord "aaaaaa") (by
    apply List.mem_append_left
    show burnsideF48s_u42eWord "aaaaaa" ∈ burnsideF48s_u42eWords burnsideF48s_u42eR1S
    exact List.mem_map_of_mem (by decide))
  rw [← h]
  simp [burnsideF48s_u42eWord, burnsideF48s_u42eLetter, burnsideF48s_ev, pow_succ, mul_assoc]

end Facts

section Classes

theorem burnsideF48s_u42e_C0_cases {z : Ah} (hz : z ∈ burnsideF48s_u42eC0) :
    ∃ l < burnsideF48s_u42eC0W.length, z = burnsideF48s_ev burnsideF48s_u42eG
      (burnsideF48s_u42eC0W.getD l []) := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have h3 : (burnsideF48s_u42eG 0 ^ 2) ^ (3 : ℕ) = 1 := by
    rw [← pow_mul]; exact burnsideF48s_u42e_a6
  rw [zpow_eq_zpow_emod' j h3, burnsideF48s_u42e_closed.2.2.2.2.1]
  have hj : j % ((3 : ℕ) : ℤ) = 0 ∨ j % ((3 : ℕ) : ℤ) = 1 ∨ j % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hj with h | h | h
  · exact ⟨0, by simp, by rw [h, zpow_zero]; rfl⟩
  · exact ⟨2, by simp, by rw [h, zpow_one]; exact burnsideF48s_u42e_ev_aa.symm⟩
  · refine ⟨1, by simp, ?_⟩
    rw [List.getD_cons_succ, List.getD_cons_zero, burnsideF48s_u42e_ev_AA, h]
    have e : (burnsideF48s_u42eG 0 ^ 2) ^ ((2 : ℕ) : ℤ) * (burnsideF48s_u42eG 0 ^ 2) = 1 := by
      rw [zpow_natCast, ← pow_succ, ← pow_mul]
      exact burnsideF48s_u42e_a6
    exact eq_inv_of_mul_eq_one_left e

theorem burnsideF48s_u42e_C0_mem {l : ℕ} (hl : l < burnsideF48s_u42eC0W.length) :
    burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eC0W.getD l []) ∈ burnsideF48s_u42eC0 := by
  rw [burnsideF48s_u42e_closed.2.2.2.2.1] at hl ⊢
  rcases (show l = 0 ∨ l = 1 ∨ l = 2 by simp at hl; omega) with rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · rw [List.getD_cons_succ, List.getD_cons_zero, burnsideF48s_u42e_ev_AA]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, burnsideF48s_u42e_ev_aa]
    exact Subgroup.mem_zpowers _

theorem burnsideF48s_u42e_card_C0 : Nat.card ↥burnsideF48s_u42eC0 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [burnsideF48s_u42eC0, Nat.card_zpowers]
  refine orderOf_eq_prime (by rw [← pow_mul]; exact burnsideF48s_u42e_a6) ?_
  rw [← burnsideF48s_u42e_ev_aa]
  exact burnsideF48s_u42e_rels.2.2.1

theorem burnsideF48s_u42e_C0_le : burnsideF48s_u42eC0 ≤ burnsideF48s_u42eP1 ⊓ burnsideF48s_u42eP2 := by
  rw [burnsideF48s_u42eC0, Subgroup.zpowers_le]
  exact ⟨pow_mem (burnsideF48s_u42e_G_mem1 (by decide)) 2,
    pow_mem (burnsideF48s_u42e_G_mem2 (by decide)) 2⟩

theorem burnsideF48s_u42e_mem_B {w : List (Fin 5 × Bool)} (h : ∀ l ∈ w, l.1 ≠ 2 ∧ l.1 ≠ 3) :
    burnsideF48s_ev burnsideF48s_u42eG w ∈ burnsideF48s_u42eP1 ⊓ burnsideF48s_u42eP2 :=
  burnsideF48s_ev_mem _ _ fun l hl =>
    ⟨burnsideF48s_u42e_G_mem1 (h l hl).2, burnsideF48s_u42e_G_mem2 (h l hl).1⟩

theorem burnsideF48s_u42e_K_le {j : ℕ} (hj : j < 7) :
    burnsideF48s_u42eK j ≤ burnsideF48s_u42eP1 ⊓ burnsideF48s_u42eP2 := by
  rw [burnsideF48s_u42eK, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact burnsideF48s_u42e_mem_B ((burnsideF48s_u42e_letters.2.2.2 j (List.mem_range.2 hj)).2.2 w
    (List.mem_append_left _ (List.mem_append_left _ hw)))

theorem burnsideF48s_u42e_K_cov {j : ℕ} (hj : j < 7) :
    ∀ z ∈ burnsideF48s_u42eK j, ∃ l < (burnsideF48s_u42eKW j).length,
      z = burnsideF48s_ev burnsideF48s_u42eG ((burnsideF48s_u42eKW j).getD l []) := by
  obtain ⟨a1, a2, -, a4, -, -⟩ := burnsideF48s_u42e_closed.2.2.2.2.2.2.2.2 j (List.mem_range.2 hj)
  refine burnsideF48s_e_cover_words burnsideF48s_u42e_rep a2 ?_ a4 ?_
  · rw [List.getD_eq_getElem _ _ a2] at a1 ⊢
    exact a1
  · rintro s ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩

theorem burnsideF48s_u42e_K_mem {j l : ℕ} (hl : l < (burnsideF48s_u42eKW j).length) :
    burnsideF48s_ev burnsideF48s_u42eG ((burnsideF48s_u42eKW j).getD l []) ∈ burnsideF48s_u42eK j :=
  Subgroup.subset_closure ⟨_, burnsideF48s_e_getD_mem _ hl [], rfl⟩

theorem burnsideF48s_u42e_card_K {j : ℕ} (hj : j < 7) : Nat.card ↥(burnsideF48s_u42eK j) = 6 := by
  rw [burnsideF48s_e_card_of_cover burnsideF48s_u42e_rep (burnsideF48s_u42e_K_cov hj)
    (fun l hl => burnsideF48s_u42e_K_mem hl)
    (burnsideF48s_u42e_rels.2.2.2.2.2.2 j (List.mem_range.2 hj))]
  interval_cases j <;> rfl

theorem burnsideF48s_u42e_C0_le_K {j : ℕ} (hj : j < 7) :
    burnsideF48s_u42eC0 ≤ burnsideF48s_u42eK j := by
  obtain ⟨-, -, a3, -, -, -⟩ := burnsideF48s_u42e_closed.2.2.2.2.2.2.2.2 j (List.mem_range.2 hj)
  intro z hz
  obtain ⟨l, hl, rfl⟩ := burnsideF48s_u42e_C0_cases hz
  have h := a3 _ (List.mem_map_of_mem (burnsideF48s_e_getD_mem _ hl []))
  rw [List.contains_iff_mem] at h
  obtain ⟨i, hi, e⟩ := burnsideF48s_e_mem_map [] h
  rw [burnsideF48s_e_eq burnsideF48s_u42e_rep e]
  exact burnsideF48s_u42e_K_mem hi

end Classes

section Model

theorem burnsideF48s_u42e_getD0 {Ws : List (List (Fin 5 × Bool))} (hn : 0 < Ws.length)
    (h : Ws.getD 0 [(0, true)] = []) : Ws.getD 0 [] = [] := by
  rw [List.getD_eq_getElem _ _ hn] at h ⊢
  exact h

theorem burnsideF48s_u42e_model {j : ℕ} (hj : j < 7) : burnsideF48s_EModel burnsideF48s_u42eG
    burnsideF48s_u42eLS burnsideF48s_u42eLSi burnsideF48s_u42eP1 burnsideF48s_u42eP2
    (burnsideF48s_u42eK j) burnsideF48s_u42eP1W burnsideF48s_u42eP2W (burnsideF48s_u42eKW j)
    burnsideF48s_u42eR1 burnsideF48s_u42eR2 := by
  have hrep := burnsideF48s_u42e_rep
  obtain ⟨hl1, hl2, -, -⟩ := burnsideF48s_u42e_letters
  obtain ⟨c1, c2, c3, c4, -, -, c7, c8, -⟩ := burnsideF48s_u42e_closed
  obtain ⟨r1, -, -, rx, ry, rf, -⟩ := burnsideF48s_u42e_rels
  refine ⟨hrep, ?_, burnsideF48s_u42e_K_le hj, ?_, ?_, burnsideF48s_u42e_K_cov hj, ?_, ?_,
    fun l hl => burnsideF48s_u42e_K_mem hl, ?_, ?_⟩
  · rw [eq_top_iff, ← burnsideF48s_e_closure_top QA45_closure_eq
      (S := {burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eWord "apapap"),
        burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eWord "bqpaqp"),
        burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eWord "bpbpfb")}) (by
        rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
        simp only [Subgroup.coe_subtype]
        rw [rx, ry, rf]), Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;>
      exact burnsideF48s_ev_mem _ _ fun l _ => burnsideF48s_u42e_G_mem_sup l.1
  · refine burnsideF48s_e_cover hrep (by rw [c1]; norm_num) (burnsideF48s_u42e_getD0
      (by rw [c1]; norm_num) c3) (gs := [0, 1, 2, 4]) c7 (S := {burnsideF48s_u42eG 0,
      burnsideF48s_u42eG 1, burnsideF48s_u42eG 2, burnsideF48s_u42eG 4}) ?_
    rintro s (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, rfl⟩
    · exact ⟨2, by simp, rfl⟩
    · exact ⟨4, by simp, rfl⟩
  · refine burnsideF48s_e_cover hrep (by rw [c2]; norm_num) (burnsideF48s_u42e_getD0
      (by rw [c2]; norm_num) c4) (gs := [0, 1, 3, 4]) c8 (S := {burnsideF48s_u42eG 0,
      burnsideF48s_u42eG 1, burnsideF48s_u42eG 3, burnsideF48s_u42eG 4}) ?_
    rintro s (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, rfl⟩
    · exact ⟨3, by simp, rfl⟩
    · exact ⟨4, by simp, rfl⟩
  · intro i hi l hl
    exact burnsideF48s_u42e_G_mem1 (hl1 _ (List.mem_append_left _
      (burnsideF48s_e_getD_mem _ hi [])) l hl)
  · intro i hi l hl
    exact burnsideF48s_u42e_G_mem2 (hl2 _ (List.mem_append_left _
      (burnsideF48s_e_getD_mem _ hi [])) l hl)
  · intro r hr
    exact ⟨fun l hl => burnsideF48s_u42e_G_mem1 (hl1 r (List.mem_append_right _ hr) l hl),
      r1 r (List.mem_append_left _ hr)⟩
  · intro r hr
    exact ⟨fun l hl => burnsideF48s_u42e_G_mem2 (hl2 r (List.mem_append_right _ hr) l hl),
      r1 r (List.mem_append_right _ hr)⟩

theorem burnsideF48s_u42e_tc {k : ℕ} (hk : k < 98) :
    Finite (PG 5 (burnsideF48s_u42eWs k)) ∧
      Nat.card (PG 5 (burnsideF48s_u42eWs k)) ≤
        (if k ∈ [0, 5, 8, 11, 17, 22, 27, 67, 73, 77, 83] then 45 else 1) * 1152 :=
  Certificates.certificate7552 k hk

theorem burnsideF48s_u42e_cands {j : ℕ} (hj : j < 7) : burnsideF48s_ECands burnsideF48s_u42eG
    burnsideF48s_u42eLS burnsideF48s_u42eLSi burnsideF48s_u42eP1 burnsideF48s_u42eP2
    burnsideF48s_u42eP1W burnsideF48s_u42eP2W (burnsideF48s_u42eKW j) burnsideF48s_u42eR1
    burnsideF48s_u42eR2 (burnsideF48s_u42eTW j) (burnsideF48s_u42eU j) (burnsideF48s_u42eV j)
    (burnsideF48s_u42eW j) 4 := by
  obtain ⟨-, -, -, hlj⟩ := burnsideF48s_u42e_letters
  obtain ⟨hU, hV, hKTW⟩ := hlj j (List.mem_range.2 hj)
  obtain ⟨-, -, -, -, -, c6, -, -, hcl⟩ := burnsideF48s_u42e_closed
  obtain ⟨-, -, -, -, a5, a6⟩ := hcl j (List.mem_range.2 hj)
  obtain ⟨-, r2, -, -, -, -, -⟩ := burnsideF48s_u42e_rels
  have hcand := burnsideF48s_u42e_checks.2.2.2.2.1
  simp only [burnsideF48s_u42eCheckCand, List.all_eq_true] at hcand
  have hX : Nat.card ↥QA45.originalSubgroup = 51840 := card_A
  refine ⟨a5, a6, fun t ht => fun l hl => ⟨burnsideF48s_u42e_G_mem1 (hKTW _ (List.mem_append_left _
    (List.mem_append_right _ (burnsideF48s_e_getD_mem _ ht []))) l hl).2,
      burnsideF48s_u42e_G_mem2 (hKTW _ (List.mem_append_left _
    (List.mem_append_right _ (burnsideF48s_e_getD_mem _ ht []))) l hl).1⟩,
    fun k hk l hl => burnsideF48s_u42e_G_mem1 (hU _ (burnsideF48s_e_getD_mem _ hk []) l hl),
    fun k hk l hl => burnsideF48s_u42e_G_mem2 (hV _ (burnsideF48s_e_getD_mem _ (hk.trans_le a5) [])
      l hl),
    fun k hk l hl => ⟨burnsideF48s_u42e_G_mem1 (hKTW _ (List.mem_append_right _
      (burnsideF48s_e_getD_mem _ (hk.trans_le a6) [])) l hl).2,
      burnsideF48s_u42e_G_mem2 (hKTW _ (List.mem_append_right _
      (burnsideF48s_e_getD_mem _ (hk.trans_le a6) [])) l hl).1⟩,
    hcand j (List.mem_range.2 hj), fun k hk => ?_⟩
  by_cases hj3 : j = 3
  · subst hj3
    rw [c6] at hk
    obtain ⟨hfin, hcard⟩ := burnsideF48s_u42e_tc hk
    refine ⟨hfin, ?_⟩
    rw [hX]
    by_cases hh : k ∈ [0, 5, 8, 11, 17, 22, 27, 67, 73, 77, 83]
    · rw [if_pos hh] at hcard
      exact Or.inr ⟨hcard.trans (by norm_num), r2 k hh⟩
    · rw [if_neg hh] at hcard
      exact Or.inl (lt_of_le_of_lt hcard (by norm_num))
  · exfalso
    have h0 : (burnsideF48s_u42eU j).length = 0 := by
      interval_cases j
      all_goals first
        | (exact absurd rfl hj3)
        | rfl
    omega

end Model

section QE

open CFSG.Open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF48s_u42e_contains2 {w : List (Fin 5 × Bool)}
    (h : burnsideF48s_ev burnsideF48s_u42eG w ∈ burnsideF48s_u42eP2) :
    (burnsideF48s_u42eP2W.map burnsideF48s_u42eEvL).contains (burnsideF48s_u42eEvL w) = true := by
  obtain ⟨j, hj, e⟩ := (burnsideF48s_u42e_model (j := 0) (by norm_num)).cov2 _ h
  rw [List.contains_iff_mem]
  have e2 : burnsideF48s_u42eEvL w = burnsideF48s_u42eEvL (burnsideF48s_u42eP2W.getD j []) :=
    repL_unique (burnsideF48s_e_repL burnsideF48s_u42e_rep w)
      (e ▸ burnsideF48s_e_repL burnsideF48s_u42e_rep _)
  rw [e2]
  exact List.mem_map_of_mem (burnsideF48s_e_getD_mem _ hj [])

theorem burnsideF48s_u42e_containsC0 {w : List (Fin 5 × Bool)}
    (h : burnsideF48s_ev burnsideF48s_u42eG w ∈ burnsideF48s_u42eC0) :
    (burnsideF48s_u42eC0W.map burnsideF48s_u42eEvL).contains (burnsideF48s_u42eEvL w) = true := by
  obtain ⟨l, hl, e⟩ := burnsideF48s_u42e_C0_cases h
  rw [List.contains_iff_mem]
  have e2 : burnsideF48s_u42eEvL w = burnsideF48s_u42eEvL (burnsideF48s_u42eC0W.getD l []) :=
    repL_unique (burnsideF48s_e_repL burnsideF48s_u42e_rep w)
      (e ▸ burnsideF48s_e_repL burnsideF48s_u42e_rep _)
  rw [e2]
  exact List.mem_map_of_mem (burnsideF48s_e_getD_mem _ hl [])

theorem burnsideF48s_u42e_memC0_of {w : List (Fin 5 × Bool)}
    (h : (burnsideF48s_u42eC0W.map burnsideF48s_u42eEvL).contains (burnsideF48s_u42eEvL w) = true) :
    burnsideF48s_ev burnsideF48s_u42eG w ∈ burnsideF48s_u42eC0 := by
  rw [List.contains_iff_mem] at h
  obtain ⟨l, hl, e⟩ := burnsideF48s_e_mem_map [] h
  rw [burnsideF48s_e_eq burnsideF48s_u42e_rep e]
  exact burnsideF48s_u42e_C0_mem hl

theorem burnsideF48s_u42e_normC0 {w : List (Fin 5 × Bool)}
    (hK : ∀ k ∈ burnsideF48s_u42eC0, burnsideF48s_ev burnsideF48s_u42eG w * k *
      (burnsideF48s_ev burnsideF48s_u42eG w)⁻¹ ∈ burnsideF48s_u42eC0) :
    burnsideF48s_eNorm (burnsideF48s_u42eC0W.map burnsideF48s_u42eEvL) (burnsideF48s_u42eEvL w) =
      true := by
  simp only [burnsideF48s_eNorm, List.all_eq_true, List.any_eq_true, beq_iff_eq]
  intro kl hkl
  obtain ⟨l, hl, rfl⟩ := burnsideF48s_e_mem_map [] hkl
  obtain ⟨l', hl', e'⟩ := burnsideF48s_u42e_C0_cases (hK _ (burnsideF48s_u42e_C0_mem hl))
  refine ⟨_, List.mem_map_of_mem (burnsideF48s_e_getD_mem _ hl' []), ?_⟩
  have e2 : burnsideF48s_ev burnsideF48s_u42eG w * burnsideF48s_ev burnsideF48s_u42eG
      (burnsideF48s_u42eC0W.getD l []) = burnsideF48s_ev burnsideF48s_u42eG
      (burnsideF48s_u42eC0W.getD l' []) * burnsideF48s_ev burnsideF48s_u42eG w := by
    rw [← e']
    group
  exact repL_unique (burnsideF48s_e_repL_mul burnsideF48s_u42e_rep _ _)
    (by rw [e2]; exact burnsideF48s_e_repL_mul burnsideF48s_u42e_rep _ _)

theorem burnsideF48s_u42e_norm_of_test {w : List (Fin 5 × Bool)}
    (h : burnsideF48s_eNorm (burnsideF48s_u42eC0W.map burnsideF48s_u42eEvL)
      (burnsideF48s_u42eEvL w) = true) :
    ∀ k ∈ burnsideF48s_u42eC0, burnsideF48s_ev burnsideF48s_u42eG w * k *
      (burnsideF48s_ev burnsideF48s_u42eG w)⁻¹ ∈ burnsideF48s_u42eC0 := by
  simp only [burnsideF48s_eNorm, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  intro k hk
  obtain ⟨l, hl, rfl⟩ := burnsideF48s_u42e_C0_cases hk
  obtain ⟨kl', hkl', e⟩ := h _ (List.mem_map_of_mem (burnsideF48s_e_getD_mem _ hl []))
  obtain ⟨l', hl', rfl⟩ := burnsideF48s_e_mem_map [] hkl'
  have e2 := burnsideF48s_e_mul_eq burnsideF48s_u42e_rep e
  have e3 : burnsideF48s_ev burnsideF48s_u42eG w * burnsideF48s_ev burnsideF48s_u42eG
      (burnsideF48s_u42eC0W.getD l []) * (burnsideF48s_ev burnsideF48s_u42eG w)⁻¹ =
      burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eC0W.getD l' []) := by
    rw [e2]
    group
  rw [e3]
  exact burnsideF48s_u42e_C0_mem hl'

theorem burnsideF48s_u42e_classify
    (hB : Nat.card ↥(burnsideF48s_u42eP1 ⊓ burnsideF48s_u42eP2) = 384) :
    ∀ K'' : Subgroup Ah, K'' ≤ burnsideF48s_u42eP1 ⊓ burnsideF48s_u42eP2 → Nat.card ↥K'' = 6 →
      ∃ j : Fin 7, ∃ t ∈ burnsideF48s_u42eP1 ⊓ burnsideF48s_u42eP2, ∀ z, z ∈ K'' ↔
        t * z * t⁻¹ ∈ burnsideF48s_u42eK j := by
  intro K'' hle hcard
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set Bh := burnsideF48s_u42eP1 ⊓ burnsideF48s_u42eP2 with hBh
  set C₀ := burnsideF48s_u42eC0 with hC₀
  have hC0le : C₀ ≤ Bh := burnsideF48s_u42e_C0_le
  have hcC0 : Nat.card ↥C₀ = 3 := burnsideF48s_u42e_card_C0
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥K'') 3 (by rw [hcard]; norm_num)
  set C'' : Subgroup Ah := Subgroup.zpowers (g : Ah) with hC''
  have hC''le : C'' ≤ K'' := Subgroup.zpowers_le.2 g.2
  have hcC'' : Nat.card ↥C'' = 3 := by
    rw [hC'', Nat.card_zpowers, Subgroup.orderOf_coe, hg]
  have hidx : ¬ 3 ∣ C₀.relIndex Bh := by
    have h := Subgroup.relIndex_mul_card (H := C₀) (K := Bh)
    rw [inf_eq_left.2 hC0le, hcC0, hB] at h
    have : C₀.relIndex Bh = 128 := by omega
    rw [this]
    decide
  obtain ⟨t₁, ht₁, hiff₁⟩ := burnsideF48s_e_sylow_conj (q := 3) hC0le
    (IsPGroup.of_card (n := 1) (by rw [hcC0]; norm_num)) hidx C'' (hC''le.trans hle)
    (hcC''.trans hcC0.symm)
  set K₁ : Subgroup Ah := K''.map (MulAut.conj t₁).toMonoidHom with hK₁
  have hmemK₁ : ∀ z, z ∈ K₁ ↔ t₁⁻¹ * z * t₁ ∈ K'' := by
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  have hcK₁ : Nat.card ↥K₁ = 6 := by
    rw [hK₁, Subgroup.card_map_of_injective (MulAut.conj t₁).injective, hcard]
  have hK₁le : K₁ ≤ Bh := by
    intro z hz
    have h1 := hle ((hmemK₁ z).1 hz)
    have := Bh.mul_mem (Bh.mul_mem ht₁ h1) (Bh.inv_mem ht₁)
    simpa [mul_assoc] using this
  have hC0K₁ : C₀ ≤ K₁ := by
    intro c hc
    refine (hmemK₁ c).2 (hC''le ((hiff₁ _).2 ?_))
    simpa [mul_assoc] using hc
  have hidx2 : (C₀.subgroupOf K₁).index = 2 := by
    have h := Subgroup.relIndex_mul_card (H := C₀) (K := K₁)
    rw [inf_eq_left.2 hC0K₁, hcC0, hcK₁] at h
    show C₀.relIndex K₁ = 2
    omega
  obtain ⟨s, hsK, hsC⟩ : ∃ s ∈ K₁, s ∉ C₀ := by
    by_contra hne
    simp only [not_exists, not_and, not_not] at hne
    have := Subgroup.card_le_of_le hne
    omega
  have hN : (C₀.subgroupOf K₁).Normal := Subgroup.normal_of_index_eq_two hidx2
  have hsnorm : ∀ c ∈ C₀, s * c * s⁻¹ ∈ C₀ := by
    intro c hc
    have := hN.conj_mem ⟨c, hC0K₁ hc⟩ hc ⟨s, hsK⟩
    exact this
  have hss : s * s ∈ C₀ := Subgroup.mul_self_mem_of_index_two hidx2 ⟨s, hsK⟩
  have hM0 := burnsideF48s_u42e_model (j := 0) (by norm_num)
  obtain ⟨i, hi, rfl⟩ := hM0.cov1 s (hK₁le hsK).1
  have hcl := burnsideF48s_u42e_checks.2.2.2.2.2
  simp only [burnsideF48s_u42eCheckClass, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_true, List.mem_range, beq_iff_eq] at hcl
  obtain ⟨hN0, hcl⟩ := hcl
  have hs := hcl _ (List.mem_map_of_mem (burnsideF48s_e_getD_mem _ hi []))
  rcases hs with (((h1 | h1) | h1) | h1) | ⟨nl, hnl, j, hj, kl, hkl, e⟩
  · rw [burnsideF48s_u42e_normC0 hsnorm] at h1
    exact absurd h1 (by simp)
  · exact absurd (burnsideF48s_u42e_memC0_of h1) hsC
  · have h2 := burnsideF48s_u42e_containsC0 (w := burnsideF48s_u42eP1W.getD i [] ++
      burnsideF48s_u42eP1W.getD i []) (by rw [burnsideF48s_ev_append]; exact hss)
    rw [show burnsideF48s_u42eEvL
        (burnsideF48s_u42eP1W.getD i [] ++ burnsideF48s_u42eP1W.getD i []) =
        compL (burnsideF48s_u42eEvL (burnsideF48s_u42eP1W.getD i []))
          (burnsideF48s_u42eEvL (burnsideF48s_u42eP1W.getD i [])) from
      repL_unique (burnsideF48s_e_repL burnsideF48s_u42e_rep _)
        (by rw [burnsideF48s_ev_append]; exact burnsideF48s_e_repL_mul burnsideF48s_u42e_rep _ _)]
      at h2
    rw [h2] at h1
    exact absurd h1 (by simp)
  · rw [burnsideF48s_u42e_contains2 (hK₁le hsK).2] at h1
    exact absurd h1 (by simp)
  obtain ⟨l', hl', rfl⟩ := burnsideF48s_e_mem_map [] hnl
  obtain ⟨l'', hl'', rfl⟩ := burnsideF48s_e_mem_map [] hkl
  set n := burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eN0W.getD l' []) with hn
  set s := burnsideF48s_ev burnsideF48s_u42eG (burnsideF48s_u42eP1W.getD i []) with hsdef
  have hns := burnsideF48s_e_mul_eq burnsideF48s_u42e_rep e
  have hnN := hN0 _ (List.mem_map_of_mem (burnsideF48s_e_getD_mem _ hl' []))
  obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hnN
  have hnB : n ∈ Bh := ⟨(burnsideF48s_u42e_model (j := 0) (by norm_num)).mem_of_contains1 hn1,
    (burnsideF48s_u42e_model (j := 0) (by norm_num)).mem_of_contains2 hn2⟩
  have hnC := burnsideF48s_u42e_norm_of_test hn3
  have hkK : burnsideF48s_ev burnsideF48s_u42eG ((burnsideF48s_u42eKW j).getD l'' []) ∈
      burnsideF48s_u42eK j := burnsideF48s_u42e_K_mem hl''
  have hsub : ∀ z ∈ K₁, n * z * n⁻¹ ∈ burnsideF48s_u42eK j := by
    intro z hz
    by_cases hzC : z ∈ C₀
    · exact burnsideF48s_u42e_C0_le_K hj (hnC z hzC)
    · have hzs : z * s⁻¹ ∈ C₀ := by
        have h := (Subgroup.mul_mem_iff_of_index_two hidx2 (a := (⟨z, hz⟩ : ↥K₁))
          (b := (⟨s, hsK⟩ : ↥K₁)⁻¹)).2 ⟨fun h => absurd h hzC, fun h => absurd (by
            have h' : s⁻¹ ∈ C₀ := h
            have := C₀.inv_mem h'
            simpa using this) hsC⟩
        exact h
      have e1 : n * z * n⁻¹ = (n * (z * s⁻¹) * n⁻¹) * (n * s * n⁻¹) := by group
      have e2 : n * s * n⁻¹ = burnsideF48s_ev burnsideF48s_u42eG ((burnsideF48s_u42eKW j).getD l'' []) := by
        rw [hns, mul_assoc, ← hn, mul_inv_cancel, mul_one]
      rw [e1, e2]
      exact Subgroup.mul_mem _ (burnsideF48s_u42e_C0_le_K hj (hnC _ hzs)) hkK
  have hKeq : K₁.map (MulAut.conj n).toMonoidHom = burnsideF48s_u42eK j := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨z, hz, rfl⟩
      exact hsub z hz
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hcK₁,
        burnsideF48s_u42e_card_K hj]
  refine ⟨⟨j, hj⟩, n * t₁, Bh.mul_mem hnB ht₁, fun z => ?_⟩
  rw [← hKeq]
  constructor
  · intro hz
    refine ⟨t₁ * z * t₁⁻¹, (hmemK₁ _).2 (by simpa [mul_assoc] using hz), ?_⟩
    simp [mul_assoc]
  · rintro ⟨y, hy, hyz⟩
    have hy' := (hmemK₁ y).1 hy
    have hyz' : n * y * n⁻¹ = n * t₁ * z * (n * t₁)⁻¹ := hyz
    have e : y = t₁ * z * t₁⁻¹ := by
      calc y = n⁻¹ * (n * y * n⁻¹) * n := by group
        _ = n⁻¹ * (n * t₁ * z * (n * t₁)⁻¹) * n := by rw [hyz']
        _ = t₁ * z * t₁⁻¹ := by group
    rw [e] at hy'
    simpa [mul_assoc] using hy'

theorem burnsideF48s_u42e_ecore
    (hB : Nat.card ↥(burnsideF48s_u42eP1 ⊓ burnsideF48s_u42eP2) = 384) :
    burnsideF48s_ECore burnsideF48s_u42eP1 burnsideF48s_u42eP2 4 (fun K'' => Nat.card ↥K'' = 6) :=
  burnsideF48s_e_ecore_multi (Ks := fun j : Fin 7 => burnsideF48s_u42eK j)
    (KWs := fun j => burnsideF48s_u42eKW j) (TWs := fun j => burnsideF48s_u42eTW j)
    (Us := fun j => burnsideF48s_u42eU j) (Vs := fun j => burnsideF48s_u42eV j)
    (Ws := fun j => burnsideF48s_u42eW j) (fun j => burnsideF48s_u42e_model j.2)
    (fun j => burnsideF48s_u42e_cands j.2) (burnsideF48s_u42e_classify hB)

theorem burnsideF48s_u42e_qe
    (hB : Nat.card ↥(burnsideF48s_u42eP1 ⊓ burnsideF48s_u42eP2) = 384)
    {E : Type} [Group E] [Finite E] {M₁ M₂ : Subgroup E} (θ : Ah ≃* E)
    {A₁ A₂ : Subgroup Ah}
    (hA : (A₁ = burnsideF48s_u42eP1 ∧ A₂ = burnsideF48s_u42eP2) ∨
      (A₁ = burnsideF48s_u42eP2 ∧ A₂ = burnsideF48s_u42eP1))
    (hM1 : M₁ = A₁.map θ.toMonoidHom) (hM2 : M₂ = A₂.map θ.toMonoidHom) (hgen : M₁ ⊔ M₂ = ⊤)
    {Z : Type} [Group Z] (β : ChF.Cpl M₁ M₂ Z) (hβ : β.IsFaithful) (hcard : 51840 ≤ Nat.card Z)
    {a : ↥M₁} {b : ↥M₂} {K' : Subgroup E} (haM : (a : E) ∉ M₂) (hbM : (b : E) ∉ M₁)
    (hK'le : K' ≤ M₁ ⊓ M₂) (hK'card : Nat.card ↥K' = 6)
    (haK : ∀ k ∈ K', (a : E) * k * (a : E)⁻¹ ∈ K') (hbK : ∀ k ∈ K', (b : E) * k * (b : E)⁻¹ ∈ K')
    (ha2 : (a : E) * a ∈ K') (hb2 : (b : E) * b ∈ K')
    {c : ↥(M₁ ⊓ M₂)} (hcK : (c : E) ∈ K') (hrel : (β.φ1 a * β.φ2 b) ^ 4 = β.φ12 c) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion :=
  burnsideF48s_e_qe_of_core (burnsideF48s_u42e_ecore hB) θ hA hM1 hM2 hgen β hβ
    (by rw [card_A]; exact hcard) haM hbM hK'le
    (by rw [← hK'card]; exact Nat.card_congr (Equiv.subtypeEquiv θ.toEquiv fun z => Iff.rfl))
    haK hbK ha2 hb2 hcK hrel

end QE

end CFSG.ASVolI
