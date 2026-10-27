module

public import CFSG.Milestones.ASVolI.F48.Small.G2d
public import Certificates.Certificate7534
public import Certificates.Certificate7535

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.CosetTable

section Model

theorem burnsideF48s_getD_map_lt {α β : Type*} (f : α → β) (l : List α) {i : ℕ} (hi : i < l.length)
    (d : β) (d' : α) : (l.map f).getD i d = f (l.getD i d') := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

theorem burnsideF48s_g22_repL (hg : burnsideF48s_g22CheckGens () = true)
    (w : List (Fin 6 × Bool)) : RepL (burnsideF48s_g22EvL w) (burnsideF48s_ev burnsideF48s_g22Gen w) := by
  simp only [burnsideF48s_g22CheckGens, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
    decide_eq_true_eq, true_implies] at hg
  have hlet : ∀ l : Fin 6 × Bool,
      RepL (burnsideF48s_g22LetL l) (cond l.2 (burnsideF48s_g22Gen l.1) (burnsideF48s_g22Gen l.1)⁻¹) := by
    rintro ⟨i, b⟩
    cases b
    · exact (hg i).2
    · exact (hg i).1
  have key : ∀ (w : List (Fin 6 × Bool)) (acc : List ℕ) (σ : Equiv.Perm (Fin 28)), RepL acc σ →
      RepL (w.foldl (fun acc l => compL acc (burnsideF48s_g22LetL l)) acc)
        (σ * burnsideF48s_ev burnsideF48s_g22Gen w) := by
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

theorem burnsideF48s_g22_repL_gen (hg : burnsideF48s_g22CheckGens () = true) (g : Fin 6) :
    RepL (burnsideF48s_g22GL.getD g []) (burnsideF48s_g22Gen g) := by
  simp only [burnsideF48s_g22CheckGens, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
    decide_eq_true_eq, true_implies] at hg
  exact (hg g).1

theorem burnsideF48s_g22_coe_ev (w : List (Fin 6 × Bool)) :
    ((burnsideF48s_ev burnsideF48s_g22L w : ↥burnsideF48s_g22X) : Equiv.Perm (Fin 28)) =
      burnsideF48s_ev burnsideF48s_g22Gen w :=
  (burnsideF48s_ev_map burnsideF48s_g22X.subtype burnsideF48s_g22L w).symm.trans
    (burnsideF48s_ev_congr w fun _ _ => rfl)

theorem burnsideF48s_g22_ev_eq (hg : burnsideF48s_g22CheckGens () = true)
    {w w' : List (Fin 6 × Bool)} (h : burnsideF48s_g22EvL w = burnsideF48s_g22EvL w') :
    burnsideF48s_ev burnsideF48s_g22L w = burnsideF48s_ev burnsideF48s_g22L w' := by
  apply Subtype.ext
  rw [burnsideF48s_g22_coe_ev, burnsideF48s_g22_coe_ev]
  exact eq_of_repL (burnsideF48s_g22_repL hg w) (h ▸ burnsideF48s_g22_repL hg w')

theorem burnsideF48s_g22_ev_one (hg : burnsideF48s_g22CheckGens () = true)
    {w : List (Fin 6 × Bool)} (h : burnsideF48s_g22EvL w = List.range 28) :
    burnsideF48s_ev burnsideF48s_g22L w = 1 := by
  apply Subtype.ext
  rw [burnsideF48s_g22_coe_ev]
  exact eq_of_repL (h ▸ burnsideF48s_g22_repL hg w) (repL_one 28)

theorem burnsideF48s_g22_repL_mul (hg : burnsideF48s_g22CheckGens () = true)
    (w w' : List (Fin 6 × Bool)) :
    RepL (compL (burnsideF48s_g22EvL w) (burnsideF48s_g22EvL w'))
      ((burnsideF48s_ev burnsideF48s_g22L w * burnsideF48s_ev burnsideF48s_g22L w' :
        ↥burnsideF48s_g22X) : Equiv.Perm (Fin 28)) := by
  rw [Subgroup.coe_mul, burnsideF48s_g22_coe_ev, burnsideF48s_g22_coe_ev]
  exact repL_mul (burnsideF48s_g22_repL hg w) (burnsideF48s_g22_repL hg w')

theorem burnsideF48s_g22_cover (hg : burnsideF48s_g22CheckGens () = true) {Ws : List String}
    {n : ℕ} (hn : 0 < n) (h0 : Ws.getD 0 "x" = "") {gs : List (Fin 6)}
    (hcl : ∀ i < n, ∀ g ∈ gs, ∃ j < n,
      compL (burnsideF48s_g22EvL (burnsideF48s_g22Word (Ws.getD i "")))
        (burnsideF48s_g22GL.getD g []) =
      burnsideF48s_g22EvL (burnsideF48s_g22Word (Ws.getD j "")))
    (hord : ∀ g ∈ gs, ∃ k : ℕ, 0 < k ∧ burnsideF48s_g22L g ^ k = 1)
    {S : Set ↥burnsideF48s_g22X} (hS : ∀ s ∈ S, ∃ g ∈ gs, s = burnsideF48s_g22L g) :
    ∀ z ∈ Subgroup.closure S, ∃ i < n,
      z = burnsideF48s_ev burnsideF48s_g22L (burnsideF48s_g22Word (Ws.getD i "")) := by
  intro z hz
  have hsub := closure_subset_of_right_closed (S := S)
    (P := {z | ∃ i < n, z = burnsideF48s_ev burnsideF48s_g22L (burnsideF48s_g22Word (Ws.getD i ""))})
    (fun s hs => by
      obtain ⟨g, hg', rfl⟩ := hS s hs
      exact hord g hg')
    ⟨0, hn, by
      have : Ws.getD 0 "" = "" := by
        cases Ws with
        | nil => rfl
        | cons w Ws => simpa using h0
      rw [this]
      rfl⟩
    (fun p ⟨i, hi, hp⟩ s hs => by
      obtain ⟨g, hg', rfl⟩ := hS s hs
      obtain ⟨j, hj, hjeq⟩ := hcl i hi g hg'
      refine ⟨j, hj, ?_⟩
      rw [hp]
      apply Subtype.ext
      have h1 : RepL (compL (burnsideF48s_g22EvL (burnsideF48s_g22Word (Ws.getD i "")))
          (burnsideF48s_g22GL.getD g []))
          ((burnsideF48s_ev burnsideF48s_g22L (burnsideF48s_g22Word (Ws.getD i "")) *
            burnsideF48s_g22L g : ↥burnsideF48s_g22X) : Equiv.Perm (Fin 28)) := by
        rw [Subgroup.coe_mul, burnsideF48s_g22_coe_ev]
        rw [burnsideF48s_g22L_coe]
        exact repL_mul (burnsideF48s_g22_repL hg _) (burnsideF48s_g22_repL_gen hg g)
      rw [hjeq] at h1
      rw [burnsideF48s_g22_coe_ev]
      exact eq_of_repL h1 (burnsideF48s_g22_repL hg _))
  exact hsub hz

theorem burnsideF48s_g22_ev_mem {K : Subgroup ↥burnsideF48s_g22X} {w : List (Fin 6 × Bool)}
    (hw : ∀ l ∈ w, burnsideF48s_g22L l.1 ∈ K) : burnsideF48s_ev burnsideF48s_g22L w ∈ K :=
  burnsideF48s_ev_mem _ w hw

end Model

section Facts

theorem burnsideF48s_g22_ev_replicate_letter (g : Fin 6) (k : ℕ) :
    burnsideF48s_ev burnsideF48s_g22L (List.replicate k (g, true)) = burnsideF48s_g22L g ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, burnsideF48s_ev_cons, ih, pow_succ']
    rfl

theorem burnsideF48s_g22_rels_X : (∀ s ∈ burnsideF48s_g22RelP1 ++ burnsideF48s_g22RelP2,
    burnsideF48s_ev burnsideF48s_g22L (burnsideF48s_g22Word s) = 1) ∧
    burnsideF48s_ev burnsideF48s_g22L (burnsideF48s_g22Cand 1) = 1 := by
  obtain ⟨hg, hr, -, -, -⟩ := Certificates.certificate7535
  simp only [burnsideF48s_g22CheckRels, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hr
  exact ⟨fun s hs => burnsideF48s_g22_ev_one hg (hr.1 s hs), burnsideF48s_g22_ev_one hg hr.2⟩

theorem burnsideF48s_g22_ord (g : Fin 6) : ∃ k : ℕ, 0 < k ∧ burnsideF48s_g22L g ^ k = 1 := by
  have h := burnsideF48s_g22_rels_X.1
  have e : ∀ (s : String) (k : ℕ), s ∈ burnsideF48s_g22RelP1 ++ burnsideF48s_g22RelP2 →
      burnsideF48s_g22Word s = List.replicate k (g, true) → 0 < k →
      ∃ k : ℕ, 0 < k ∧ burnsideF48s_g22L g ^ k = 1 := by
    intro s k hs hw hk
    refine ⟨k, hk, ?_⟩
    rw [← burnsideF48s_g22_ev_replicate_letter, ← hw]
    exact h s hs
  fin_cases g
  · exact e "aaaa" 4 (by decide) (by decide) (by norm_num)
  · exact e "bbbb" 4 (by decide) (by decide) (by norm_num)
  · exact e "ss" 2 (by decide) (by decide) (by norm_num)
  · exact e "xxx" 3 (by decide) (by decide) (by norm_num)
  · exact e "yyy" 3 (by decide) (by decide) (by norm_num)
  · exact e "tt" 2 (by decide) (by decide) (by norm_num)

theorem burnsideF48s_g22_letters :
    (∀ s ∈ burnsideF48s_g22TW, ∀ l ∈ burnsideF48s_g22Word s, l.1 ≠ 3 ∧ l.1 ≠ 4) ∧
    (∀ s ∈ burnsideF48s_g22P1W ++ burnsideF48s_g22RelP1 ++ ["bTY"],
      ∀ l ∈ burnsideF48s_g22Word s, l.1 ≠ 3) ∧
    (∀ s ∈ burnsideF48s_g22P2W ++ burnsideF48s_g22RelP2 ++ burnsideF48s_g22CandV,
      ∀ l ∈ burnsideF48s_g22Word s, l.1 ≠ 4) := by
  obtain ⟨-, -, hl, -, -⟩ := Certificates.certificate7535
  simp only [burnsideF48s_g22CheckLetters, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hl
  exact ⟨hl.1.1, hl.1.2, hl.2⟩

theorem burnsideF48s_g22_L_memT {g : Fin 6} (h3 : g ≠ 3) (h4 : g ≠ 4) :
    burnsideF48s_g22L g ∈ burnsideF48s_g22T := by
  fin_cases g
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · exact absurd rfl h3
  · exact absurd rfl h4
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))

theorem burnsideF48s_g22_L_memP1 {g : Fin 6} (h3 : g ≠ 3) :
    burnsideF48s_g22L g ∈ burnsideF48s_g22P1 := by
  fin_cases g
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · exact absurd rfl h3
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))

theorem burnsideF48s_g22_L_memP2 {g : Fin 6} (h4 : g ≠ 4) :
    burnsideF48s_g22L g ∈ burnsideF48s_g22P2 := by
  fin_cases g
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  · exact absurd rfl h4
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))

theorem burnsideF48s_g22_closed :
    burnsideF48s_g22TW.length = 64 ∧ burnsideF48s_g22P1W.length = 192 ∧
    burnsideF48s_g22P2W.length = 192 ∧ burnsideF48s_g22TW.getD 0 "x" = "" ∧
    burnsideF48s_g22P1W.getD 0 "x" = "" ∧ burnsideF48s_g22P2W.getD 0 "x" = "" ∧
    (∀ i < 64, ∀ g : ℕ, g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 5 → ∃ j < 64,
      compL ((burnsideF48s_g22TL ()).getD i []) (burnsideF48s_g22GL.getD g []) =
        (burnsideF48s_g22TL ()).getD j []) ∧
    (∀ i < 192, ∀ g : ℕ, g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 4 ∨ g = 5 → ∃ j < 192,
      compL ((burnsideF48s_g22P1L ()).getD i []) (burnsideF48s_g22GL.getD g []) =
        (burnsideF48s_g22P1L ()).getD j []) ∧
    (∀ i < 192, ∀ g : ℕ, g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 5 → ∃ j < 192,
      compL ((burnsideF48s_g22P2L ()).getD i []) (burnsideF48s_g22GL.getD g []) =
        (burnsideF48s_g22P2L ()).getD j []) ∧
    (∀ i < 64, ∀ j < 64, (burnsideF48s_g22TL ()).getD i [] = (burnsideF48s_g22TL ()).getD j [] →
      i = j) := by
  obtain ⟨-, -, -, hc, -⟩ := Certificates.certificate7535
  simp only [burnsideF48s_g22CheckClosed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, List.mem_range, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, h6, fun i hi g hg => h7 i hi g hg, fun i hi g hg => h8 i hi g hg,
    fun i hi g hg => h9 i hi g hg, fun i hi j hj hij => ?_⟩
  rcases h10 i hi j hj with h | h
  · exact absurd hij h
  · exact h

end Facts

section Cover

theorem burnsideF48s_g22_getD_L {Ws : List String} {i : ℕ} (hi : i < Ws.length) :
    (Ws.map fun s => burnsideF48s_g22EvL (burnsideF48s_g22Word s)).getD i [] =
      burnsideF48s_g22EvL (burnsideF48s_g22Word (Ws.getD i "")) :=
  burnsideF48s_getD_map_lt _ Ws hi [] ""

theorem burnsideF48s_g22_coverT : ∀ z ∈ burnsideF48s_g22T, ∃ i < 64,
    z = burnsideF48s_ev burnsideF48s_g22L (burnsideF48s_g22Word (burnsideF48s_g22TW.getD i "")) := by
  obtain ⟨hg, -, -, -, -⟩ := Certificates.certificate7535
  obtain ⟨hl, -, -, h0, -, -, hcl, -, -, -⟩ := burnsideF48s_g22_closed
  refine burnsideF48s_g22_cover hg (by norm_num) h0 (gs := [0, 1, 2, 5]) (fun i hi g hg' => ?_)
    (fun g _ => burnsideF48s_g22_ord g) (fun s hs => ?_)
  · have hg'' : (g : ℕ) = 0 ∨ (g : ℕ) = 1 ∨ (g : ℕ) = 2 ∨ (g : ℕ) = 5 := by
      revert g; decide
    obtain ⟨j, hj, e⟩ := hcl i hi g hg''
    refine ⟨j, hj, ?_⟩
    rwa [burnsideF48s_g22TL, burnsideF48s_g22_getD_L (by omega),
      burnsideF48s_g22_getD_L (by omega)] at e
  · rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨5, by decide, rfl⟩

theorem burnsideF48s_g22_coverP1 : ∀ z ∈ burnsideF48s_g22P1, ∃ i < 192,
    z = burnsideF48s_ev burnsideF48s_g22L (burnsideF48s_g22Word (burnsideF48s_g22P1W.getD i "")) := by
  obtain ⟨hg, -, -, -, -⟩ := Certificates.certificate7535
  obtain ⟨-, hl, -, -, h0, -, -, hcl, -, -⟩ := burnsideF48s_g22_closed
  refine burnsideF48s_g22_cover hg (by norm_num) h0 (gs := [0, 1, 2, 4, 5]) (fun i hi g hg' => ?_)
    (fun g _ => burnsideF48s_g22_ord g) (fun s hs => ?_)
  · have hg'' : (g : ℕ) = 0 ∨ (g : ℕ) = 1 ∨ (g : ℕ) = 2 ∨ (g : ℕ) = 4 ∨ (g : ℕ) = 5 := by
      revert g; decide
    obtain ⟨j, hj, e⟩ := hcl i hi g hg''
    refine ⟨j, hj, ?_⟩
    rwa [burnsideF48s_g22P1L, burnsideF48s_g22_getD_L (by omega),
      burnsideF48s_g22_getD_L (by omega)] at e
  · rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨4, by decide, rfl⟩
    · exact ⟨5, by decide, rfl⟩

theorem burnsideF48s_g22_coverP2 : ∀ z ∈ burnsideF48s_g22P2, ∃ i < 192,
    z = burnsideF48s_ev burnsideF48s_g22L (burnsideF48s_g22Word (burnsideF48s_g22P2W.getD i "")) := by
  obtain ⟨hg, -, -, -, -⟩ := Certificates.certificate7535
  obtain ⟨-, -, hl, -, -, h0, -, -, hcl, -⟩ := burnsideF48s_g22_closed
  refine burnsideF48s_g22_cover hg (by norm_num) h0 (gs := [0, 1, 2, 3, 5]) (fun i hi g hg' => ?_)
    (fun g _ => burnsideF48s_g22_ord g) (fun s hs => ?_)
  · have hg'' : (g : ℕ) = 0 ∨ (g : ℕ) = 1 ∨ (g : ℕ) = 2 ∨ (g : ℕ) = 3 ∨ (g : ℕ) = 5 := by
      revert g; decide
    obtain ⟨j, hj, e⟩ := hcl i hi g hg''
    refine ⟨j, hj, ?_⟩
    rwa [burnsideF48s_g22P2L, burnsideF48s_g22_getD_L (by omega),
      burnsideF48s_g22_getD_L (by omega)] at e
  · rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨3, by decide, rfl⟩
    · exact ⟨5, by decide, rfl⟩

theorem burnsideF48s_g22_TW_mem {i : ℕ} (hi : i < 64) :
    burnsideF48s_ev burnsideF48s_g22L (burnsideF48s_g22Word (burnsideF48s_g22TW.getD i "")) ∈
      burnsideF48s_g22T := by
  obtain ⟨hl, -, -, -, -, -, -, -, -, -⟩ := burnsideF48s_g22_closed
  refine burnsideF48s_g22_ev_mem fun l hl' => burnsideF48s_g22_L_memT ?_ ?_
  · have hm : burnsideF48s_g22TW.getD i "" ∈ burnsideF48s_g22TW := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    exact (burnsideF48s_g22_letters.1 _ hm l hl').1
  · have hm : burnsideF48s_g22TW.getD i "" ∈ burnsideF48s_g22TW := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    exact (burnsideF48s_g22_letters.1 _ hm l hl').2

theorem burnsideF48s_g22_card_T : Nat.card ↥burnsideF48s_g22T = 64 := by
  obtain ⟨hg, -, -, -, -⟩ := Certificates.certificate7535
  obtain ⟨hl, -, -, -, -, -, -, -, -, hdist⟩ := burnsideF48s_g22_closed
  let F : Fin 64 → ↥burnsideF48s_g22T := fun i => ⟨_, burnsideF48s_g22_TW_mem i.2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun i j hij => ?_, fun z => ?_⟩
    · have e := congrArg (fun z : ↥burnsideF48s_g22T => ((z : ↥burnsideF48s_g22X) :
        Equiv.Perm (Fin 28))) hij
      simp only [F, burnsideF48s_g22_coe_ev] at e
      have e' : burnsideF48s_g22EvL (burnsideF48s_g22Word (burnsideF48s_g22TW.getD i "")) =
          burnsideF48s_g22EvL (burnsideF48s_g22Word (burnsideF48s_g22TW.getD j "")) :=
        repL_unique (burnsideF48s_g22_repL hg _) (e ▸ burnsideF48s_g22_repL hg _)
      have := hdist i i.2 j j.2 (by
        rw [burnsideF48s_g22TL, burnsideF48s_g22_getD_L (by omega),
          burnsideF48s_g22_getD_L (by omega)]
        exact e')
      exact Fin.ext this
    · obtain ⟨i, hi, hz⟩ := burnsideF48s_g22_coverT z z.2
      exact ⟨⟨i, hi⟩, Subtype.ext hz.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem burnsideF48s_g22_cand {x y : ↥burnsideF48s_g22X} (hx : x ∈ burnsideF48s_g22P1)
    (hxT : x ∉ burnsideF48s_g22T) (hx2 : x * x = 1) (hy : y ∈ burnsideF48s_g22P2)
    (hyT : y ∉ burnsideF48s_g22T) (hy2 : y * y = 1) :
    ∃ t ∈ burnsideF48s_g22T, ∃ k < 4,
      t * x * t⁻¹ = burnsideF48s_ev burnsideF48s_g22L (burnsideF48s_g22Word "bTY") ∧
      t * y * t⁻¹ = burnsideF48s_ev burnsideF48s_g22L
        (burnsideF48s_g22Word (burnsideF48s_g22CandV.getD k "")) := by
  obtain ⟨hg, -, -, -, hC⟩ := Certificates.certificate7535
  obtain ⟨hlT, hl1, hl2, -, -, -, -, -, -, -⟩ := burnsideF48s_g22_closed
  obtain ⟨i, hi, rfl⟩ := burnsideF48s_g22_coverP1 x hx
  obtain ⟨j, hj, rfl⟩ := burnsideF48s_g22_coverP2 y hy
  simp only [burnsideF48s_g22CheckCand, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_false, not_not] at hC
  have hRi : ∀ w, RepL (burnsideF48s_g22EvL (burnsideF48s_g22InvW w))
      (burnsideF48s_ev burnsideF48s_g22Gen w)⁻¹ := fun w => by
    rw [← burnsideF48s_ev_invW]
    exact burnsideF48s_g22_repL hg _
  set wx := burnsideF48s_g22Word (burnsideF48s_g22P1W.getD i "")
  set wy := burnsideF48s_g22Word (burnsideF48s_g22P2W.getD j "")
  have hsq : ∀ w : List (Fin 6 × Bool), burnsideF48s_ev burnsideF48s_g22L w *
      burnsideF48s_ev burnsideF48s_g22L w = 1 →
      compL (burnsideF48s_g22EvL w) (burnsideF48s_g22EvL w) = List.range 28 := by
    intro w hw
    have h1 := burnsideF48s_g22_repL_mul hg w w
    rw [hw] at h1
    exact repL_unique h1 (repL_one 28)
  have hnT : ∀ w : List (Fin 6 × Bool), burnsideF48s_ev burnsideF48s_g22L w ∉ burnsideF48s_g22T →
      ∀ t < 64, burnsideF48s_g22EvL w ≠
        burnsideF48s_g22EvL (burnsideF48s_g22Word (burnsideF48s_g22TW.getD t "")) := by
    intro w hw t ht he
    exact hw (burnsideF48s_g22_ev_eq hg he ▸ burnsideF48s_g22_TW_mem ht)
  have hC' := hC i hi
  rw [burnsideF48s_g22P1L, burnsideF48s_g22_getD_L (by omega)] at hC'
  rcases hC' with (hC' | ⟨t, ht, hteq⟩) | hC'
  · exact absurd (hsq wx hx2) hC'
  · rw [burnsideF48s_g22TL, burnsideF48s_g22_getD_L (by omega)] at hteq
    exact absurd hteq (hnT wx hxT t ht)
  have hC'' := hC' j hj
  rw [burnsideF48s_g22P2L, burnsideF48s_g22_getD_L (by omega)] at hC''
  rcases hC'' with (hC'' | ⟨t, ht, hteq⟩) | ⟨t, ht, k, hk, e1, e2⟩
  · exact absurd (hsq wy hy2) hC''
  · rw [burnsideF48s_g22TL, burnsideF48s_g22_getD_L (by omega)] at hteq
    exact absurd hteq (hnT wy hyT t ht)
  rw [burnsideF48s_g22TL, burnsideF48s_g22TiL, burnsideF48s_g22_getD_L (by omega)] at e1 e2
  rw [burnsideF48s_getD_map_lt _ _ (by omega) [] ""] at e1 e2
  rw [burnsideF48s_getD_map_lt _ _ (by simpa [burnsideF48s_g22CandV] using hk) [] ""] at e2
  refine ⟨_, burnsideF48s_g22_TW_mem ht, k, hk, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, burnsideF48s_g22_coe_ev,
      burnsideF48s_g22_coe_ev, burnsideF48s_g22_coe_ev]
    refine eq_of_repL ?_ (burnsideF48s_g22_repL hg _)
    rw [← e1]
    exact repL_mul (repL_mul (burnsideF48s_g22_repL hg _) (burnsideF48s_g22_repL hg _)) (hRi _)
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, burnsideF48s_g22_coe_ev,
      burnsideF48s_g22_coe_ev, burnsideF48s_g22_coe_ev]
    refine eq_of_repL ?_ (burnsideF48s_g22_repL hg _)
    rw [← e2]
    exact repL_mul (repL_mul (burnsideF48s_g22_repL hg _) (burnsideF48s_g22_repL hg _)) (hRi _)

end Cover

section Main

theorem burnsideF48s_g22_closure_L :
    Subgroup.closure (Set.range burnsideF48s_g22L) = ⊤ := by
  apply Subgroup.map_injective burnsideF48s_g22X.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hrange : ⇑burnsideF48s_g22X.subtype '' Set.range burnsideF48s_g22L =
      Set.range burnsideF48s_g22Gen := by
    rw [← Set.range_comp]
    rfl
  rw [hrange]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact burnsideF48s_g22Gen_mem i
  · refine sup_le ?_ ?_
    · rw [show u33J = u33PresHom.range from range_u33PresHom.symm, MonoidHom.range_eq_map,
        ← PresentedGroup.closure_range_of, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨⟨k.val, by omega⟩, ?_⟩
      rw [u33PresHom_of]
      simp [burnsideF48s_g22Gen, k.2]
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure ⟨5, rfl⟩

theorem burnsideF48s_g22_sup : burnsideF48s_g22P1 ⊔ burnsideF48s_g22P2 = ⊤ := by
  rw [eq_top_iff, ← burnsideF48s_g22_closure_L, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  by_cases h3 : i = 3
  · subst h3
    exact Subgroup.mem_sup_right (burnsideF48s_g22_L_memP2 (by decide))
  · exact Subgroup.mem_sup_left (burnsideF48s_g22_L_memP1 h3)

theorem burnsideF48s_g22_card_PG (j : ℕ) (hj : j < 4) :
    Finite (PG 6 (burnsideF48s_g22Ws j)) ∧
      Nat.card (PG 6 (burnsideF48s_g22Ws j)) ≤ if j = 1 then 12096 else 192 :=
  Certificates.certificate7534 j hj

theorem burnsideF48s_g22_core (hX : Nat.card ↥burnsideF48s_g22X = 12096) {Y : Type} [Group Y]
    (f₁ : ↥burnsideF48s_g22P1 →* Y) (f₂ : ↥burnsideF48s_g22P2 →* Y)
    (h12 : ∀ (t : ↥burnsideF48s_g22X) (h : t ∈ burnsideF48s_g22P1 ⊓ burnsideF48s_g22P2),
      f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hgen : f₁.range ⊔ f₂.range = ⊤) (hcard : 12096 ≤ Nat.card Y)
    {x y : ↥burnsideF48s_g22X} (hx : x ∈ burnsideF48s_g22P1) (hxT : x ∉ burnsideF48s_g22T)
    (hx2 : x * x = 1) (hy : y ∈ burnsideF48s_g22P2) (hyT : y ∉ burnsideF48s_g22T) (hy2 : y * y = 1)
    (hrel : (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ 6 = 1) :
    ∃ φ : Y ≃* ↥burnsideF48s_g22X, (∀ z : ↥burnsideF48s_g22P1, φ (f₁ z) = z) ∧
      (∀ z : ↥burnsideF48s_g22P2, φ (f₂ z) = z) := by
  set L := burnsideF48s_g22L with hL
  obtain ⟨hlT, hl1, hl2⟩ := burnsideF48s_g22_letters
  obtain ⟨t, htT, k, hk, ex, ey⟩ := burnsideF48s_g22_cand hx hxT hx2 hy hyT hy2
  have htP1 : t ∈ burnsideF48s_g22P1 := (Subgroup.closure_mono (by
    rintro _ (rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))) : burnsideF48s_g22T ≤ burnsideF48s_g22P1) htT
  have htP2 : t ∈ burnsideF48s_g22P2 := (Subgroup.closure_mono (by
    rintro _ (rfl | rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))) : burnsideF48s_g22T ≤ burnsideF48s_g22P2) htT
  have ht12 : f₁ ⟨t, htP1⟩ = f₂ ⟨t, htP2⟩ := h12 t ⟨htP1, htP2⟩
  set yL := burnsideF48s_yL L f₁ f₂ with hyL
  have hU : ∀ l ∈ burnsideF48s_g22Word "bTY", L l.1 ∈ burnsideF48s_g22P1 := fun l hl =>
    burnsideF48s_g22_L_memP1 (hl1 _ (List.mem_append_right _ (List.mem_singleton_self _)) l hl)
  have hV : ∀ l ∈ burnsideF48s_g22Word (burnsideF48s_g22CandV.getD k ""),
      L l.1 ∈ burnsideF48s_g22P2 := by
    intro l hl
    refine burnsideF48s_g22_L_memP2 (hl2 _ (List.mem_append_right _ ?_) l hl)
    rw [List.getD_eq_getElem _ _ (by simpa [burnsideF48s_g22CandV] using hk)]
    exact List.getElem_mem _
  obtain ⟨mU, eU⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) _ hU
  obtain ⟨mV, eV⟩ := burnsideF48s_ev_yL_B (f₁ := f₁) (f₂ := f₂) h12 _ hV
  have fU : f₁ ⟨_, mU⟩ = f₁ ⟨t, htP1⟩ * f₁ ⟨x, hx⟩ * (f₁ ⟨t, htP1⟩)⁻¹ := by
    have e : (⟨_, mU⟩ : ↥burnsideF48s_g22P1) =
        ⟨t, htP1⟩ * ⟨x, hx⟩ * (⟨t, htP1⟩ : ↥burnsideF48s_g22P1)⁻¹ := Subtype.ext ex.symm
    rw [e, map_mul, map_mul, map_inv]
  have fV : f₂ ⟨_, mV⟩ = f₂ ⟨t, htP2⟩ * f₂ ⟨y, hy⟩ * (f₂ ⟨t, htP2⟩)⁻¹ := by
    have e : (⟨_, mV⟩ : ↥burnsideF48s_g22P2) =
        ⟨t, htP2⟩ * ⟨y, hy⟩ * (⟨t, htP2⟩ : ↥burnsideF48s_g22P2)⁻¹ := Subtype.ext ey.symm
    rw [e, map_mul, map_mul, map_inv]
  have hcandY : burnsideF48s_ev yL (burnsideF48s_g22Cand k) = 1 := by
    unfold burnsideF48s_g22Cand
    rw [burnsideF48s_ev_replicate, burnsideF48s_ev_append, eU, eV, fU, fV, ← ht12]
    have e : f₁ ⟨t, htP1⟩ * f₁ ⟨x, hx⟩ * (f₁ ⟨t, htP1⟩)⁻¹ *
        (f₁ ⟨t, htP1⟩ * f₂ ⟨y, hy⟩ * (f₁ ⟨t, htP1⟩)⁻¹) =
        f₁ ⟨t, htP1⟩ * (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) * (f₁ ⟨t, htP1⟩)⁻¹ := by
      group
    rw [e, ← MulAut.conj_apply, ← map_pow, hrel, map_one]
  have hrelY : ∀ s ∈ burnsideF48s_g22RelP1 ++ burnsideF48s_g22RelP2,
      burnsideF48s_ev yL (burnsideF48s_g22Word s) = 1 := by
    intro s hs
    have h1X := burnsideF48s_g22_rels_X.1 s hs
    rcases List.mem_append.1 hs with hs1 | hs2
    · obtain ⟨m, e⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) (burnsideF48s_g22Word s)
        (fun l hl => burnsideF48s_g22_L_memP1
          (hl1 s (List.mem_append_left _ (List.mem_append_right _ hs1)) l hl))
      rw [e]
      have : (⟨_, m⟩ : ↥burnsideF48s_g22P1) = 1 := Subtype.ext h1X
      rw [this, map_one]
    · obtain ⟨m, e⟩ := burnsideF48s_ev_yL_B (f₁ := f₁) (f₂ := f₂) h12 (burnsideF48s_g22Word s)
        (fun l hl => burnsideF48s_g22_L_memP2
          (hl2 s (List.mem_append_left _ (List.mem_append_right _ hs2)) l hl))
      rw [e]
      have : (⟨_, m⟩ : ↥burnsideF48s_g22P2) = 1 := Subtype.ext h1X
      rw [this, map_one]
  have hY : ∀ r ∈ burnsideF48s_g22Ws k, burnsideF48s_ev yL r = 1 := by
    intro r hr
    rcases List.mem_append.1 hr with h | h
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
      exact hrelY s hs
    · rw [List.mem_singleton] at h
      rw [h]
      exact hcandY
  have hcov1 : ∀ z ∈ burnsideF48s_g22P1, ∃ w : List (Fin 6 × Bool),
      (∀ l ∈ w, L l.1 ∈ burnsideF48s_g22P1) ∧ burnsideF48s_ev L w = z := by
    intro z hz
    refine burnsideF48s_exists_word L (fun i => L i ∈ burnsideF48s_g22P1)
      (S := {L 0, L 1, L 2, L 4, L 5}) ?_ hz
    rintro g (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, burnsideF48s_g22_L_memP1 (by decide), rfl⟩
    · exact ⟨1, burnsideF48s_g22_L_memP1 (by decide), rfl⟩
    · exact ⟨2, burnsideF48s_g22_L_memP1 (by decide), rfl⟩
    · exact ⟨4, burnsideF48s_g22_L_memP1 (by decide), rfl⟩
    · exact ⟨5, burnsideF48s_g22_L_memP1 (by decide), rfl⟩
  have hcov2 : ∀ z ∈ burnsideF48s_g22P2, ∃ w : List (Fin 6 × Bool),
      (∀ l ∈ w, L l.1 ∈ burnsideF48s_g22P2) ∧ burnsideF48s_ev L w = z := by
    intro z hz
    refine burnsideF48s_exists_word L (fun i => L i ∈ burnsideF48s_g22P2)
      (S := {L 0, L 1, L 2, L 3, L 5}) ?_ hz
    rintro g (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, burnsideF48s_g22_L_memP2 (by decide), rfl⟩
    · exact ⟨1, burnsideF48s_g22_L_memP2 (by decide), rfl⟩
    · exact ⟨2, burnsideF48s_g22_L_memP2 (by decide), rfl⟩
    · exact ⟨3, burnsideF48s_g22_L_memP2 (by decide), rfl⟩
    · exact ⟨5, burnsideF48s_g22_L_memP2 (by decide), rfl⟩
  obtain ⟨hfin, hcardP⟩ := burnsideF48s_g22_card_PG k hk
  haveI := hfin
  have hYle := burnsideF48s_core_card_le (L := L) (f₁ := f₁) (f₂ := f₂) h12 hgen hcov1 hcov2 hY
  have hk1 : k = 1 := by
    by_contra hne
    rw [if_neg hne] at hcardP
    omega
  subst hk1
  rw [if_pos rfl] at hcardP
  have hD : ∀ r ∈ burnsideF48s_g22Ws 1, burnsideF48s_ev L r = 1 := by
    intro r hr
    rcases List.mem_append.1 hr with h | h
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
      exact burnsideF48s_g22_rels_X.1 s hs
    · rw [List.mem_singleton] at h
      rw [h]
      exact burnsideF48s_g22_rels_X.2
  haveI : Finite ↥burnsideF48s_g22X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  exact burnsideF48s_core_gen h12 hgen burnsideF48s_g22_sup hcov1 hcov2 hD hY
    (by rw [hX]; exact hcardP) (by rw [hX]; exact hcard)

end Main

section QE

theorem burnsideF48s_g22_T_le_P1 : burnsideF48s_g22T ≤ burnsideF48s_g22P1 := by
  rw [burnsideF48s_g22T, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl)
  · exact burnsideF48s_g22_L_memP1 (by decide)
  · exact burnsideF48s_g22_L_memP1 (by decide)
  · exact burnsideF48s_g22_L_memP1 (by decide)
  · exact burnsideF48s_g22_L_memP1 (by decide)

theorem burnsideF48s_g22_T_le_P2 : burnsideF48s_g22T ≤ burnsideF48s_g22P2 := by
  rw [burnsideF48s_g22T, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl)
  · exact burnsideF48s_g22_L_memP2 (by decide)
  · exact burnsideF48s_g22_L_memP2 (by decide)
  · exact burnsideF48s_g22_L_memP2 (by decide)
  · exact burnsideF48s_g22_L_memP2 (by decide)

theorem burnsideF48s_g22_qe (hX : Nat.card ↥burnsideF48s_g22X = 12096) {E : Type} [Group E]
    [Finite E] {M₁ M₂ : Subgroup E} (θ : ↥burnsideF48s_g22X ≃* E)
    {A₁ A₂ : Subgroup ↥burnsideF48s_g22X}
    (hA : (A₁ = burnsideF48s_g22P1 ∧ A₂ = burnsideF48s_g22P2) ∨
      (A₁ = burnsideF48s_g22P2 ∧ A₂ = burnsideF48s_g22P1))
    (hM1 : M₁ = A₁.map θ.toMonoidHom) (hM2 : M₂ = A₂.map θ.toMonoidHom) (hgen : M₁ ⊔ M₂ = ⊤)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hcard : 12096 ≤ Nat.card Y)
    {a : ↥M₁} {b : ↥M₂} (haM : (a : E) ∉ M₂) (hbM : (b : E) ∉ M₁) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hrel : (β.φ1 a * β.φ2 b) ^ 6 = 1) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion := by
  let eG : ↥(M₁ ⊔ M₂) ≃* E := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have h12β : ∀ (t : E) (h1 : t ∈ M₁) (h2 : t ∈ M₂), β.φ1 ⟨t, h1⟩ = β.φ2 ⟨t, h2⟩ :=
    fun t h1 h2 => (β.comm1 ⟨t, ⟨h1, h2⟩⟩).trans (β.comm2 ⟨t, ⟨h1, h2⟩⟩).symm
  have hmemθ : ∀ {A : Subgroup ↥burnsideF48s_g22X} {M : Subgroup E}, M = A.map θ.toMonoidHom →
      ∀ z, θ z ∈ M ↔ z ∈ A := by
    intro A M hM z
    rw [hM]
    exact Subgroup.mem_map_iff_mem θ.injective
  have hpre : ∀ {A : Subgroup ↥burnsideF48s_g22X} {M : Subgroup E}, M = A.map θ.toMonoidHom →
      ∀ u : ↥M, ∃ z, z ∈ A ∧ θ z = u := by
    intro A M hM u
    obtain ⟨z, hz, hzu⟩ : (u : E) ∈ A.map θ.toMonoidHom := by rw [← hM]; exact u.2
    exact ⟨z, hz, hzu⟩
  have hrange : ∀ {P : Subgroup E} {Q : Subgroup ↥burnsideF48s_g22X} (g : ↥P →* Y) (e : ↥Q ≃* ↥P),
      (g.comp e.toMonoidHom).range = g.range :=
    fun g e => burnsideF48s_range_comp_mulEquiv_g2d g e
  have hsq : ∀ {M : Subgroup E} {z : ↥burnsideF48s_g22X} {m : ↥M}, θ z = m → m * m = 1 →
      z * z = 1 := by
    intro M z m hzm hm
    apply θ.injective
    rw [map_mul, hzm, map_one]
    exact congrArg Subtype.val hm
  rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · let r₁ : ↥burnsideF48s_g22P1 ≃* ↥M₁ :=
      (θ.subgroupMap burnsideF48s_g22P1).trans (MulEquiv.subgroupCongr hM1.symm)
    let r₂ : ↥burnsideF48s_g22P2 ≃* ↥M₂ :=
      (θ.subgroupMap burnsideF48s_g22P2).trans (MulEquiv.subgroupCongr hM2.symm)
    let f₁ : ↥burnsideF48s_g22P1 →* Y := β.φ1.comp r₁.toMonoidHom
    let f₂ : ↥burnsideF48s_g22P2 →* Y := β.φ2.comp r₂.toMonoidHom
    have hf12 : ∀ (t : ↥burnsideF48s_g22X) (h : t ∈ burnsideF48s_g22P1 ⊓ burnsideF48s_g22P2),
        f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩ := fun t h => h12β (θ t) _ _
    have hfgen : f₁.range ⊔ f₂.range = ⊤ := by
      rw [show f₁.range = β.φ1.range from hrange _ _, show f₂.range = β.φ2.range from hrange _ _]
      exact β.gen
    obtain ⟨x, hx, hxa⟩ := hpre hM1 a
    obtain ⟨y, hy, hyb⟩ := hpre hM2 b
    have hxT : x ∉ burnsideF48s_g22T := fun h =>
      haM (hxa ▸ (hmemθ hM2 x).2 (burnsideF48s_g22_T_le_P2 h))
    have hyT : y ∉ burnsideF48s_g22T := fun h =>
      hbM (hyb ▸ (hmemθ hM1 y).2 (burnsideF48s_g22_T_le_P1 h))
    have hra : r₁ ⟨x, hx⟩ = a := Subtype.ext hxa
    have hrb : r₂ ⟨y, hy⟩ = b := Subtype.ext hyb
    have hrel' : (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ 6 = 1 := by
      show (β.φ1 (r₁ ⟨x, hx⟩) * β.φ2 (r₂ ⟨y, hy⟩)) ^ 6 = 1
      rw [hra, hrb]
      exact hrel
    obtain ⟨φ, hφ1, hφ2⟩ := burnsideF48s_g22_core hX f₁ f₂ hf12 hfgen hcard hx hxT (hsq hxa ha2)
      hy hyT (hsq hyb hb2) hrel'
    refine burnsideF48s_qe_of_equiv β hβ (φ.trans (θ.trans eG.symm)) (fun u => ?_) (fun u => ?_)
    · obtain ⟨z, hz, hzu⟩ := hpre hM1 u
      have hu : u = r₁ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₁ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ1]
      exact (hmemθ hM1 z).2 hz
    · obtain ⟨z, hz, hzu⟩ := hpre hM2 u
      have hu : u = r₂ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₂ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ2]
      exact (hmemθ hM2 z).2 hz
  · let r₁ : ↥burnsideF48s_g22P1 ≃* ↥M₂ :=
      (θ.subgroupMap burnsideF48s_g22P1).trans (MulEquiv.subgroupCongr hM2.symm)
    let r₂ : ↥burnsideF48s_g22P2 ≃* ↥M₁ :=
      (θ.subgroupMap burnsideF48s_g22P2).trans (MulEquiv.subgroupCongr hM1.symm)
    let f₁ : ↥burnsideF48s_g22P1 →* Y := β.φ2.comp r₁.toMonoidHom
    let f₂ : ↥burnsideF48s_g22P2 →* Y := β.φ1.comp r₂.toMonoidHom
    have hf12 : ∀ (t : ↥burnsideF48s_g22X) (h : t ∈ burnsideF48s_g22P1 ⊓ burnsideF48s_g22P2),
        f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩ := fun t h => (h12β (θ t) _ _).symm
    have hfgen : f₁.range ⊔ f₂.range = ⊤ := by
      rw [show f₁.range = β.φ2.range from hrange _ _, show f₂.range = β.φ1.range from hrange _ _,
        sup_comm]
      exact β.gen
    obtain ⟨x, hx, hxb⟩ := hpre hM2 b
    obtain ⟨y, hy, hya⟩ := hpre hM1 a
    have hxT : x ∉ burnsideF48s_g22T := fun h =>
      hbM (hxb ▸ (hmemθ hM1 x).2 (burnsideF48s_g22_T_le_P2 h))
    have hyT : y ∉ burnsideF48s_g22T := fun h =>
      haM (hya ▸ (hmemθ hM2 y).2 (burnsideF48s_g22_T_le_P1 h))
    have hrb : r₁ ⟨x, hx⟩ = b := Subtype.ext hxb
    have hra : r₂ ⟨y, hy⟩ = a := Subtype.ext hya
    have hrel' : (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ 6 = 1 := by
      show (β.φ2 (r₁ ⟨x, hx⟩) * β.φ1 (r₂ ⟨y, hy⟩)) ^ 6 = 1
      rw [hra, hrb]
      have e : (β.φ2 b * β.φ1 a) ^ 6 = (β.φ1 a)⁻¹ * (β.φ1 a * β.φ2 b) ^ 6 * β.φ1 a := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      rw [e, hrel, mul_one, inv_mul_cancel]
    obtain ⟨φ, hφ1, hφ2⟩ := burnsideF48s_g22_core hX f₁ f₂ hf12 hfgen hcard hx hxT (hsq hxb hb2)
      hy hyT (hsq hya ha2) hrel'
    refine burnsideF48s_qe_of_equiv β hβ (φ.trans (θ.trans eG.symm)) (fun u => ?_) (fun u => ?_)
    · obtain ⟨z, hz, hzu⟩ := hpre hM1 u
      have hu : u = r₂ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₂ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ2]
      exact (hmemθ hM1 z).2 hz
    · obtain ⟨z, hz, hzu⟩ := hpre hM2 u
      have hu : u = r₁ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₁ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ1]
      exact (hmemθ hM2 z).2 hz

end QE

end CFSG.ASVolI
