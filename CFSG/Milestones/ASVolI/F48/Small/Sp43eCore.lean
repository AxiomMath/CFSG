module

public import CFSG.Milestones.ASVolI.F48.Small.Eng
public import CFSG.Milestones.ASVolI.F48.Small.AutBase
public import Certificates.Certificate7550
public import Certificates.Certificate7551

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42 CFSG.Quasithin.H13.F431.U42Aut CFSG.CosetTable
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 f45)

section Facts


theorem burnsideF48s_sp43e_checks : burnsideF48s_sp43eCheckGens () = true ∧
    burnsideF48s_sp43eCheckRels () = true ∧ burnsideF48s_sp43eCheckLetters () = true ∧
    burnsideF48s_sp43eCheckClosed () = true ∧ burnsideF48s_sp43eCheckCand () = true :=
  Certificates.certificate7551

theorem burnsideF48s_sp43e_rep :
    burnsideF48s_eRec burnsideF48s_sp43eG burnsideF48s_sp43eLS burnsideF48s_sp43eLSi := by
  have hg := burnsideF48s_sp43e_checks.1
  simp only [burnsideF48s_sp43eCheckGens, Bool.and_eq_true, decide_eq_true_eq] at hg
  intro i
  have hi : (i : ℕ) < burnsideF48s_sp43eXY.length := by
    have := i.2
    simp only [burnsideF48s_sp43eXY, List.length_cons, List.length_nil]
    omega
  constructor
  · rw [hg.1, burnsideF48s_e_getD_map _ _ hi [] []]
    exact repL_wordAP _
  · rw [hg.2, burnsideF48s_e_getD_map _ _ hi [] []]
    show RepL _ (wordAP _)⁻¹
    rw [← wordAP_invAL]
    exact repL_wordAP _

theorem burnsideF48s_sp43e_G_mem1 {i : Fin 5} (h : i ≠ 3) :
    burnsideF48s_sp43eG i ∈ burnsideF48s_sp43eP1 := by
  fin_cases i
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · exact absurd rfl h
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))

theorem burnsideF48s_sp43e_G_mem2 {i : Fin 5} (h : i ≠ 2) :
    burnsideF48s_sp43eG i ∈ burnsideF48s_sp43eP2 := by
  fin_cases i
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact absurd rfl h
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))

theorem burnsideF48s_sp43e_G_mem_sup (i : Fin 5) :
    burnsideF48s_sp43eG i ∈ burnsideF48s_sp43eP1 ⊔ burnsideF48s_sp43eP2 := by
  by_cases h : i = 3
  · subst h
    exact Subgroup.mem_sup_right (burnsideF48s_sp43e_G_mem2 (by decide))
  · exact Subgroup.mem_sup_left (burnsideF48s_sp43e_G_mem1 h)

theorem burnsideF48s_sp43e_letters :
    (∀ w ∈ burnsideF48s_sp43eP1W ++ burnsideF48s_sp43eR1 ++ burnsideF48s_sp43eU, ∀ l ∈ w,
      l.1 ≠ 3) ∧
    (∀ w ∈ burnsideF48s_sp43eP2W ++ burnsideF48s_sp43eR2 ++ burnsideF48s_sp43eV, ∀ l ∈ w,
      l.1 ≠ 2) ∧
    (∀ w ∈ burnsideF48s_sp43eKW ++ burnsideF48s_sp43eTW ++ burnsideF48s_sp43eW, ∀ l ∈ w,
      l.1 ≠ 2 ∧ l.1 ≠ 3) := by
  have hl := burnsideF48s_sp43e_checks.2.2.1
  simp only [burnsideF48s_sp43eCheckLetters, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hl
  exact ⟨hl.1.1, hl.1.2, hl.2⟩

theorem burnsideF48s_sp43e_closed :
    burnsideF48s_sp43eP1W.length = 1296 ∧ burnsideF48s_sp43eP2W.length = 1296 ∧
    burnsideF48s_sp43eP1W.getD 0 [(0, true)] = [] ∧ burnsideF48s_sp43eP2W.getD 0 [(0, true)] = [] ∧
    burnsideF48s_sp43eKW = [[], burnsideF48s_sp43eWord "f", burnsideF48s_sp43eWord "aaa",
      burnsideF48s_sp43eWord "aaaf"] ∧ burnsideF48s_sp43eU.length = 32 ∧
    burnsideF48s_sp43eV.length = 32 ∧ burnsideF48s_sp43eW.length = 32 ∧
    burnsideF48s_eClosed (burnsideF48s_sp43eP1W.map burnsideF48s_sp43eEvL) burnsideF48s_sp43eLS
      [0, 1, 2, 4] = true ∧
    burnsideF48s_eClosed (burnsideF48s_sp43eP2W.map burnsideF48s_sp43eEvL) burnsideF48s_sp43eLS
      [0, 1, 3, 4] = true ∧
    burnsideF48s_eClosedW (burnsideF48s_sp43eKW.map burnsideF48s_sp43eEvL)
      ([burnsideF48s_sp43eWord "f", burnsideF48s_sp43eWord "aaa"].map burnsideF48s_sp43eEvL) =
        true := by
  have hc := burnsideF48s_sp43e_checks.2.2.2.1
  simp only [burnsideF48s_sp43eCheckClosed, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem burnsideF48s_sp43e_ev_f :
    burnsideF48s_ev burnsideF48s_sp43eG (burnsideF48s_sp43eWord "f") = burnsideF48s_sp43eG 4 := by
  simp [burnsideF48s_sp43eWord, burnsideF48s_sp43eLetter, burnsideF48s_ev]

theorem burnsideF48s_sp43e_ev_aaa :
    burnsideF48s_ev burnsideF48s_sp43eG (burnsideF48s_sp43eWord "aaa") =
      burnsideF48s_sp43eG 0 ^ 3 := by
  simp [burnsideF48s_sp43eWord, burnsideF48s_sp43eLetter, burnsideF48s_ev, pow_succ, mul_assoc]

theorem burnsideF48s_sp43e_ev_aaaf :
    burnsideF48s_ev burnsideF48s_sp43eG (burnsideF48s_sp43eWord "aaaf") =
      burnsideF48s_sp43eG 0 ^ 3 * burnsideF48s_sp43eG 4 := by
  simp [burnsideF48s_sp43eWord, burnsideF48s_sp43eLetter, burnsideF48s_ev, pow_succ, mul_assoc]

theorem burnsideF48s_sp43e_rels :
    (∀ w ∈ burnsideF48s_sp43eR1 ++ burnsideF48s_sp43eR2,
      burnsideF48s_ev burnsideF48s_sp43eG w = 1) ∧
    (∀ k ∈ [0, 4, 8, 12, 16, 20, 24, 28], burnsideF48s_ev burnsideF48s_sp43eG
      (burnsideF48s_eCandRel 4 (burnsideF48s_sp43eU.getD k []) (burnsideF48s_sp43eV.getD k [])
        (burnsideF48s_sp43eW.getD k [])) = 1) ∧
    ((burnsideF48s_ev burnsideF48s_sp43eG (burnsideF48s_sp43eWord "pbpBp") : Ah) : P45) = x45 ∧
    ((burnsideF48s_ev burnsideF48s_sp43eG (burnsideF48s_sp43eWord "aQABpBp") : Ah) : P45) = y45 ∧
    ((burnsideF48s_ev burnsideF48s_sp43eG (burnsideF48s_sp43eWord "abapBQpfb") : Ah) : P45) =
      f45 ∧
    (burnsideF48s_sp43eKW.map burnsideF48s_sp43eEvL).Nodup := by
  have hr := burnsideF48s_sp43e_checks.2.1
  simp only [burnsideF48s_sp43eCheckRels, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hr
  have hrep := burnsideF48s_sp43e_rep
  have h3' : burnsideF48s_eEvL 45 burnsideF48s_sp43eLS burnsideF48s_sp43eLSi
      (burnsideF48s_sp43eWord "pbpBp") = U42F431.xL := h3
  have h4' : burnsideF48s_eEvL 45 burnsideF48s_sp43eLS burnsideF48s_sp43eLSi
      (burnsideF48s_sp43eWord "aQABpBp") = U42F431.yL := h4
  have h5' : burnsideF48s_eEvL 45 burnsideF48s_sp43eLS burnsideF48s_sp43eLSi
      (burnsideF48s_sp43eWord "abapBQpfb") = f45L := h5
  refine ⟨fun w hw => burnsideF48s_e_one hrep (h1 w hw), fun k hk => burnsideF48s_e_one hrep (h2 k hk),
    ?_, ?_, ?_, h6⟩
  · exact eq_of_repL (burnsideF48s_e_repL hrep _) (by rw [h3']; exact repL_x)
  · exact eq_of_repL (burnsideF48s_e_repL hrep _) (by rw [h4']; exact repL_y)
  · exact eq_of_repL (burnsideF48s_e_repL hrep _) (by rw [h5']; exact repL_f45)

end Facts

section Model


theorem burnsideF48s_sp43e_let1 {w : List (Fin 5 × Bool)} (h : ∀ l ∈ w, l.1 ≠ 3) :
    ∀ l ∈ w, burnsideF48s_sp43eG l.1 ∈ burnsideF48s_sp43eP1 :=
  fun l hl => burnsideF48s_sp43e_G_mem1 (h l hl)

theorem burnsideF48s_sp43e_let2 {w : List (Fin 5 × Bool)} (h : ∀ l ∈ w, l.1 ≠ 2) :
    ∀ l ∈ w, burnsideF48s_sp43eG l.1 ∈ burnsideF48s_sp43eP2 :=
  fun l hl => burnsideF48s_sp43e_G_mem2 (h l hl)

theorem burnsideF48s_sp43e_getD0 {Ws : List (List (Fin 5 × Bool))} (hn : 0 < Ws.length)
    (h : Ws.getD 0 [(0, true)] = []) : Ws.getD 0 [] = [] := by
  rw [List.getD_eq_getElem _ _ hn] at h ⊢
  exact h

theorem burnsideF48s_sp43e_model : burnsideF48s_EModel burnsideF48s_sp43eG burnsideF48s_sp43eLS
    burnsideF48s_sp43eLSi burnsideF48s_sp43eP1 burnsideF48s_sp43eP2 burnsideF48s_sp43eK
    burnsideF48s_sp43eP1W burnsideF48s_sp43eP2W burnsideF48s_sp43eKW burnsideF48s_sp43eR1
    burnsideF48s_sp43eR2 := by
  have hrep := burnsideF48s_sp43e_rep
  obtain ⟨hl1, hl2, hl3⟩ := burnsideF48s_sp43e_letters
  obtain ⟨c1, c2, c3, c4, c5, -, -, -, c9, c10, c11⟩ := burnsideF48s_sp43e_closed
  obtain ⟨r1, -, rx, ry, rf, -⟩ := burnsideF48s_sp43e_rels
  have hfK : burnsideF48s_sp43eG 4 ∈ burnsideF48s_sp43eK :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have haK : burnsideF48s_sp43eG 0 ^ 3 ∈ burnsideF48s_sp43eK :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine ⟨hrep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← burnsideF48s_e_closure_top QA45_closure_eq
      (S := {burnsideF48s_ev burnsideF48s_sp43eG (burnsideF48s_sp43eWord "pbpBp"),
        burnsideF48s_ev burnsideF48s_sp43eG (burnsideF48s_sp43eWord "aQABpBp"),
        burnsideF48s_ev burnsideF48s_sp43eG (burnsideF48s_sp43eWord "abapBQpfb")}) (by
        rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
        simp only [Subgroup.coe_subtype]
        rw [rx, ry, rf]), Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;>
      exact burnsideF48s_ev_mem _ _ fun l _ => burnsideF48s_sp43e_G_mem_sup l.1
  · rw [burnsideF48s_sp43eK, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨burnsideF48s_sp43e_G_mem1 (by decide), burnsideF48s_sp43e_G_mem2 (by decide)⟩
    · exact ⟨pow_mem (burnsideF48s_sp43e_G_mem1 (by decide)) 3,
        pow_mem (burnsideF48s_sp43e_G_mem2 (by decide)) 3⟩
  · refine burnsideF48s_e_cover hrep (by rw [c1]; norm_num) (burnsideF48s_sp43e_getD0
      (by rw [c1]; norm_num) c3) (gs := [0, 1, 2, 4]) c9 (S := {burnsideF48s_sp43eG 0,
      burnsideF48s_sp43eG 1, burnsideF48s_sp43eG 2, burnsideF48s_sp43eG 4}) ?_
    rintro s (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, rfl⟩
    · exact ⟨2, by simp, rfl⟩
    · exact ⟨4, by simp, rfl⟩
  · refine burnsideF48s_e_cover hrep (by rw [c2]; norm_num) (burnsideF48s_sp43e_getD0
      (by rw [c2]; norm_num) c4) (gs := [0, 1, 3, 4]) c10 (S := {burnsideF48s_sp43eG 0,
      burnsideF48s_sp43eG 1, burnsideF48s_sp43eG 3, burnsideF48s_sp43eG 4}) ?_
    rintro s (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, rfl⟩
    · exact ⟨3, by simp, rfl⟩
    · exact ⟨4, by simp, rfl⟩
  · refine burnsideF48s_e_cover_words hrep (by rw [c5]; norm_num) (by rw [c5]; rfl) c11 ?_
    rintro s (rfl | rfl)
    · exact ⟨_, List.mem_cons_self, burnsideF48s_sp43e_ev_f.symm⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, burnsideF48s_sp43e_ev_aaa.symm⟩
  · intro i hi
    exact burnsideF48s_sp43e_let1 (hl1 _ (List.mem_append_left _ (List.mem_append_left _
      (burnsideF48s_e_getD_mem _ hi []))))
  · intro j hj
    exact burnsideF48s_sp43e_let2 (hl2 _ (List.mem_append_left _ (List.mem_append_left _
      (burnsideF48s_e_getD_mem _ hj []))))
  · intro l hl
    rw [c5] at hl ⊢
    rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 by simp at hl; omega) with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · rw [List.getD_cons_succ, List.getD_cons_zero, burnsideF48s_sp43e_ev_f]
      exact hfK
    · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero, burnsideF48s_sp43e_ev_aaa]
      exact haK
    · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
        burnsideF48s_sp43e_ev_aaaf]
      exact Subgroup.mul_mem _ haK hfK
  · intro r hr
    exact ⟨burnsideF48s_sp43e_let1 (hl1 r (List.mem_append_left _ (List.mem_append_right _ hr))),
      r1 r (List.mem_append_left _ hr)⟩
  · intro r hr
    exact ⟨burnsideF48s_sp43e_let2 (hl2 r (List.mem_append_left _ (List.mem_append_right _ hr))),
      r1 r (List.mem_append_right _ hr)⟩

theorem burnsideF48s_sp43e_card_K : Nat.card ↥burnsideF48s_sp43eK = 4 := by
  have hM := burnsideF48s_sp43e_model
  obtain ⟨-, -, -, -, c5, -⟩ := burnsideF48s_sp43e_closed
  have h := burnsideF48s_e_card_of_cover hM.rep hM.covK hM.memK burnsideF48s_sp43e_rels.2.2.2.2.2
  rw [h, c5]
  rfl

end Model

section TC


theorem burnsideF48s_sp43e_tc {k : ℕ} (hk : k < 32) :
    Finite (PG 5 (burnsideF48s_sp43eWs k)) ∧
      Nat.card (PG 5 (burnsideF48s_sp43eWs k)) ≤ (if k % 4 = 0 then 40 else 1) * 1296 :=
  Certificates.certificate7550 k hk

theorem burnsideF48s_sp43e_mem_holds {k : ℕ} (hk : k < 32) (hev : k % 4 = 0) :
    k ∈ [0, 4, 8, 12, 16, 20, 24, 28] := by
  interval_cases k <;> simp_all


theorem burnsideF48s_sp43e_cands : burnsideF48s_ECands burnsideF48s_sp43eG burnsideF48s_sp43eLS
    burnsideF48s_sp43eLSi burnsideF48s_sp43eP1 burnsideF48s_sp43eP2 burnsideF48s_sp43eP1W
    burnsideF48s_sp43eP2W burnsideF48s_sp43eKW burnsideF48s_sp43eR1 burnsideF48s_sp43eR2
    burnsideF48s_sp43eTW burnsideF48s_sp43eU burnsideF48s_sp43eV burnsideF48s_sp43eW 4 := by
  obtain ⟨hl1, hl2, hl3⟩ := burnsideF48s_sp43e_letters
  obtain ⟨-, -, -, -, -, c6, c7, c8, -, -, -⟩ := burnsideF48s_sp43e_closed
  obtain ⟨-, r2, -, -, -, -⟩ := burnsideF48s_sp43e_rels
  have hB : ∀ {w : List (Fin 5 × Bool)}, (∀ l ∈ w, l.1 ≠ 2 ∧ l.1 ≠ 3) →
      ∀ l ∈ w, burnsideF48s_sp43eG l.1 ∈ burnsideF48s_sp43eP1 ⊓ burnsideF48s_sp43eP2 :=
    fun h l hl => ⟨burnsideF48s_sp43e_G_mem1 (h l hl).2, burnsideF48s_sp43e_G_mem2 (h l hl).1⟩
  have hX : Nat.card ↥QA45.originalSubgroup = 51840 := card_A
  refine ⟨by rw [c6, c7], by rw [c6, c8], fun t ht => hB (hl3 _ (List.mem_append_left _
    (List.mem_append_right _ (burnsideF48s_e_getD_mem _ ht [])))), fun k hk =>
    burnsideF48s_sp43e_let1 (hl1 _ (List.mem_append_right _ (burnsideF48s_e_getD_mem _ hk []))),
    fun k hk => burnsideF48s_sp43e_let2 (hl2 _ (List.mem_append_right _
      (burnsideF48s_e_getD_mem _ (by rw [c7]; rw [c6] at hk; exact hk) []))),
    fun k hk => hB (hl3 _ (List.mem_append_right _
      (burnsideF48s_e_getD_mem _ (by rw [c8]; rw [c6] at hk; exact hk) []))),
    burnsideF48s_sp43e_checks.2.2.2.2, fun k hk => ?_⟩
  rw [c6] at hk
  obtain ⟨hfin, hcard⟩ := burnsideF48s_sp43e_tc hk
  refine ⟨hfin, ?_⟩
  rw [hX]
  by_cases hev : k % 4 = 0
  · rw [if_pos hev] at hcard
    exact Or.inr ⟨hcard.trans (by norm_num), r2 k (burnsideF48s_sp43e_mem_holds hk hev)⟩
  · rw [if_neg hev] at hcard
    exact Or.inl (lt_of_le_of_lt hcard (by norm_num))

end TC

section QE

open CFSG.Open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


theorem burnsideF48s_sp43e_conj
    (hB : Nat.card ↥(burnsideF48s_sp43eP1 ⊓ burnsideF48s_sp43eP2) = 324) :
    ∀ K'' : Subgroup Ah, K'' ≤ burnsideF48s_sp43eP1 ⊓ burnsideF48s_sp43eP2 →
      Nat.card ↥K'' = Nat.card ↥burnsideF48s_sp43eK →
      ∃ t ∈ burnsideF48s_sp43eP1 ⊓ burnsideF48s_sp43eP2, ∀ z, z ∈ K'' ↔
        t * z * t⁻¹ ∈ burnsideF48s_sp43eK := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKB := burnsideF48s_sp43e_model.K_le
  have hcK := burnsideF48s_sp43e_card_K
  refine burnsideF48s_e_sylow_conj (q := 2) hKB (IsPGroup.of_card (n := 2) (by rw [hcK]; norm_num))
    ?_
  have h := Subgroup.relIndex_mul_card (H := burnsideF48s_sp43eK)
    (K := burnsideF48s_sp43eP1 ⊓ burnsideF48s_sp43eP2)
  rw [inf_eq_left.2 hKB, hcK, hB] at h
  have h81 : burnsideF48s_sp43eK.relIndex (burnsideF48s_sp43eP1 ⊓ burnsideF48s_sp43eP2) = 81 := by
    omega
  rw [h81]
  decide


theorem burnsideF48s_sp43e_qe
    (hB : Nat.card ↥(burnsideF48s_sp43eP1 ⊓ burnsideF48s_sp43eP2) = 324)
    {E : Type} [Group E] [Finite E] {M₁ M₂ : Subgroup E} (θ : Ah ≃* E)
    {A₁ A₂ : Subgroup Ah}
    (hA : (A₁ = burnsideF48s_sp43eP1 ∧ A₂ = burnsideF48s_sp43eP2) ∨
      (A₁ = burnsideF48s_sp43eP2 ∧ A₂ = burnsideF48s_sp43eP1))
    (hM1 : M₁ = A₁.map θ.toMonoidHom) (hM2 : M₂ = A₂.map θ.toMonoidHom) (hgen : M₁ ⊔ M₂ = ⊤)
    {Z : Type} [Group Z] (β : ChF.Cpl M₁ M₂ Z) (hβ : β.IsFaithful) (hcard : 51840 ≤ Nat.card Z)
    {a : ↥M₁} {b : ↥M₂} {K' : Subgroup E} (haM : (a : E) ∉ M₂) (hbM : (b : E) ∉ M₁)
    (hK'le : K' ≤ M₁ ⊓ M₂) (hK'card : Nat.card ↥K' = 4)
    (haK : ∀ k ∈ K', (a : E) * k * (a : E)⁻¹ ∈ K') (hbK : ∀ k ∈ K', (b : E) * k * (b : E)⁻¹ ∈ K')
    (ha2 : (a : E) * a ∈ K') (hb2 : (b : E) * b ∈ K')
    {c : ↥(M₁ ⊓ M₂)} (hcK : (c : E) ∈ K') (hrel : (β.φ1 a * β.φ2 b) ^ 4 = β.φ12 c) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion :=
  burnsideF48s_e_qe burnsideF48s_sp43e_model burnsideF48s_sp43e_cands (burnsideF48s_sp43e_conj hB)
    θ hA hM1 hM2 hgen β hβ (by rw [card_A]; exact hcard) haM hbM hK'le
    (by rw [hK'card, burnsideF48s_sp43e_card_K]) haK hbK ha2 hb2 hcK hrel

end QE

end CFSG.ASVolI
