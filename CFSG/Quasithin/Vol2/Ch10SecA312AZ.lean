module

public import CFSG.Quasithin.Vol2.Ch10SecA312AW
public import CFSG.Quasithin.Vol2.Ch10SecA312AR
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23
public import CFSG.Sporadic.Recognition.M23MultiplierCert
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Tab

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

section M23Data

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.A312M24 CFSG.Sporadic.Schreier
  CFSG.Blueprint

@[expose] def m23aT : List ℕ :=
  [1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22]

@[expose] def m23bT : List ℕ :=
  [15, 8, 0, 4, 7, 21, 6, 22, 20, 9, 2, 1, 19, 17, 16, 10, 14, 5, 18, 12, 11, 13, 3]

@[expose] def m23bIT : List ℕ :=
  [2, 11, 10, 22, 3, 17, 6, 4, 1, 9, 15, 20, 19, 21, 16, 0, 14, 13, 18, 12, 8, 5, 7]

@[expose] def m23kT : List (List ℕ) :=
  [[0, 1, 9, 8, 4, 5, 6, 7, 3, 2, 11, 10, 13, 12, 20, 21, 17, 16, 19, 18, 14, 15, 22],
    [1, 0, 2, 3, 4, 5, 7, 6, 8, 9, 16, 17, 19, 18, 20, 21, 10, 11, 13, 12, 14, 15, 22],
    [8, 9, 13, 12, 11, 10, 21, 20, 0, 1, 16, 17, 14, 15, 7, 6, 5, 4, 3, 2, 18, 19, 22],
    [0, 1, 3, 2, 16, 11, 21, 20, 18, 19, 10, 17, 14, 15, 13, 12, 4, 22, 7, 6, 8, 9, 5]]

@[expose] def m23uW : List (List ℕ) :=
  [[2, 2, 2], [1, 2, 1, 2], [0, 2, 2, 2, 0], [0, 2, 0, 2, 0, 2]]

@[expose] def m23uT : List (List ℕ) :=
  [[8, 9, 6, 7, 4, 5, 2, 3, 0, 1, 10, 11, 20, 21, 18, 19, 16, 17, 14, 15, 12, 13, 22],
    [1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22],
    [3, 2, 1, 0, 4, 5, 9, 8, 7, 6, 10, 11, 15, 14, 13, 12, 16, 17, 21, 20, 19, 18, 22],
    [21, 20, 19, 18, 4, 5, 15, 14, 13, 12, 10, 11, 9, 8, 7, 6, 16, 17, 3, 2, 1, 0, 22]]

@[expose] def m23gW : List ℕ := [1, 0, 1, 1, 0, 1, 1, 1]

@[expose] def m23gT : List ℕ :=
  [6, 9, 8, 7, 16, 11, 0, 3, 2, 1, 10, 5, 12, 15, 14, 13, 4, 17, 18, 21, 20, 19, 22]

@[expose] def m23mT : List (List ℕ) :=
  [[0, 4, 2, 6, 1, 5, 3, 7, 15, 11, 13, 9, 14, 10, 12, 8],
    [0, 3, 2, 1, 6, 5, 4, 7, 13, 14, 15, 12, 11, 8, 9, 10],
    [0, 1, 2, 3, 10, 11, 8, 9, 15, 14, 13, 12, 5, 4, 7, 6],
    [0, 12, 2, 14, 6, 10, 4, 8, 3, 15, 1, 13, 5, 9, 7, 11]]

@[expose] def m23gM : List ℕ := [0, 1, 4, 5, 2, 3, 6, 7, 9, 8, 13, 12, 11, 10, 15, 14]

@[expose] def m23bits (e : ℕ) : List ℕ := (List.range 4).filter fun i => e.testBit i

@[expose] def m23uPowL : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22],
    [8, 9, 6, 7, 4, 5, 2, 3, 0, 1, 10, 11, 20, 21, 18, 19, 16, 17, 14, 15, 12, 13, 22],
    [1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22],
    [9, 8, 7, 6, 4, 5, 3, 2, 1, 0, 10, 11, 21, 20, 19, 18, 16, 17, 15, 14, 13, 12, 22],
    [3, 2, 1, 0, 4, 5, 9, 8, 7, 6, 10, 11, 15, 14, 13, 12, 16, 17, 21, 20, 19, 18, 22],
    [7, 6, 9, 8, 4, 5, 1, 0, 3, 2, 10, 11, 19, 18, 21, 20, 16, 17, 13, 12, 15, 14, 22],
    [2, 3, 0, 1, 4, 5, 8, 9, 6, 7, 10, 11, 14, 15, 12, 13, 16, 17, 20, 21, 18, 19, 22],
    [6, 7, 8, 9, 4, 5, 0, 1, 2, 3, 10, 11, 18, 19, 20, 21, 16, 17, 12, 13, 14, 15, 22],
    [21, 20, 19, 18, 4, 5, 15, 14, 13, 12, 10, 11, 9, 8, 7, 6, 16, 17, 3, 2, 1, 0, 22],
    [13, 12, 15, 14, 4, 5, 19, 18, 21, 20, 10, 11, 1, 0, 3, 2, 16, 17, 7, 6, 9, 8, 22],
    [20, 21, 18, 19, 4, 5, 14, 15, 12, 13, 10, 11, 8, 9, 6, 7, 16, 17, 2, 3, 0, 1, 22],
    [12, 13, 14, 15, 4, 5, 18, 19, 20, 21, 10, 11, 0, 1, 2, 3, 16, 17, 6, 7, 8, 9, 22],
    [18, 19, 20, 21, 4, 5, 12, 13, 14, 15, 10, 11, 6, 7, 8, 9, 16, 17, 0, 1, 2, 3, 22],
    [14, 15, 12, 13, 4, 5, 20, 21, 18, 19, 10, 11, 2, 3, 0, 1, 16, 17, 8, 9, 6, 7, 22],
    [19, 18, 21, 20, 4, 5, 13, 12, 15, 14, 10, 11, 7, 6, 9, 8, 16, 17, 1, 0, 3, 2, 22],
    [15, 14, 13, 12, 4, 5, 21, 20, 19, 18, 10, 11, 3, 2, 1, 0, 16, 17, 9, 8, 7, 6, 22]]

@[expose] def m23uPowT (e : ℕ) : List ℕ := m23uPowL.getD e []

@[expose] def m23addVec (V : List ℕ) (y : ℕ) : List ℕ := if y ∈ V then V else V ++ V.map (· ^^^ y)

@[expose] def m23round (V : List ℕ) : List ℕ :=
  V.foldl (fun W x =>
    (List.range 4).foldl (fun W' j => m23addVec W' ((m23mT.getD j []).getD x 0)) W) V

@[expose] def m23CodesTab : List ℤ → List ℕ
  | [] => List.range 23
  | z :: w => compTab (if z = 2 then m23bT else if z = -2 then m23bIT else m23aT) (m23CodesTab w)

theorem m23Check_letters :
    ∀ j ∈ List.range 4, ∀ z ∈ m23CentWords1.getD j [], z = 1 ∨ z = 2 ∨ z = -1 ∨ z = -2 := by
  decide +kernel

theorem m23Check_tabs :
    (∀ j ∈ List.range 4, m23CodesTab (m23CentWords1.getD j []) = m23kT.getD j []) ∧
    (∀ i ∈ List.range 4, wordTab 23 m23kT (m23uW.getD i []) = m23uT.getD i []) ∧
    wordTab 23 [m23aT, m23bT] m23gW = m23gT ∧
    ∀ e ∈ List.range 16, wordTab 23 m23uT (m23bits e) = m23uPowT e := by
  decide +kernel

theorem m23Check_mul : ∀ e ∈ List.range 16, ∀ f ∈ List.range 16,
    compTab (m23uPowT e) (m23uPowT f) = m23uPowT (e ^^^ f) := by
  decide +kernel

theorem m23Check_conj :
    (∀ j ∈ List.range 4, ∀ e ∈ List.range 16, (m23mT.getD j []).getD e 0 < 16 ∧
      compTab (m23kT.getD j []) (m23uPowT e) =
        compTab (m23uPowT ((m23mT.getD j []).getD e 0)) (m23kT.getD j [])) ∧
    ∀ e ∈ List.range 16, m23gM.getD e 0 < 16 ∧
      compTab m23gT (m23uPowT e) = compTab (m23uPowT (m23gM.getD e 0)) m23gT := by
  decide +kernel

theorem m23Check_misc :
    (∀ e ∈ List.range 16, e = 0 ∨ m23uPowT e ≠ List.range 23) ∧ m23uPowT 2 = m23aT ∧
    m23gM.getD 2 0 = 4 ∧ (m23mT.getD 0 []).getD 4 0 = 1 ∧ (m23mT.getD 0 []).getD 2 0 = 2 := by
  decide +kernel

theorem m23Check_clos :
    ∀ e ∈ List.range 16, e = 0 ∨ e = 2 ∨ ∀ f ∈ List.range 16, f ∈ m23round (m23round [0, e]) := by
  decide +kernel

@[expose] def m23k (j : ℕ) : Equiv.Perm (Fin 23) :=
  evalCodes [m23PermA, m23PermB] (m23CentWords1.getD j [])

@[expose] def m23u (i : ℕ) : Equiv.Perm (Fin 23) :=
  evalEltL [m23k 0, m23k 1, m23k 2, m23k 3] (m23uW.getD i [])

@[expose] def m23uPow (e : ℕ) : Equiv.Perm (Fin 23) :=
  evalEltL [m23u 0, m23u 1, m23u 2, m23u 3] (m23bits e)

@[expose] def m23g : Equiv.Perm (Fin 23) := evalEltL [m23PermA, m23PermB] m23gW

theorem tab_m23letter (z : ℤ) (hz : z = 1 ∨ z = 2 ∨ z = -1 ∨ z = -2) :
    tab 23 (if 0 < z then [m23PermA, m23PermB].getD (z.toNat - 1) 1
      else ([m23PermA, m23PermB].getD ((-z).toNat - 1) 1)⁻¹) =
      if z = 2 then m23bT else if z = -2 then m23bIT else m23aT := by
  rcases hz with rfl | rfl | rfl | rfl <;> decide

theorem tab_evalCodes (w : List ℤ) (hw : ∀ z ∈ w, z = 1 ∨ z = 2 ∨ z = -1 ∨ z = -2) :
    tab 23 (evalCodes [m23PermA, m23PermB] w) = m23CodesTab w := by
  induction w with
  | nil => simp [evalCodes, m23CodesTab, tab_one_L]
  | cons z w ih =>
    rw [evalCodes, tab_mul, ih fun z' hz' => hw z' (List.mem_cons_of_mem _ hz'), m23CodesTab,
      tab_m23letter z (hw z List.mem_cons_self)]

theorem tab_m23k {j : ℕ} (hj : j < 4) : tab 23 (m23k j) = m23kT.getD j [] := by
  rw [m23k, tab_evalCodes _ (m23Check_letters j (List.mem_range.2 hj))]
  exact m23Check_tabs.1 j (List.mem_range.2 hj)

theorem tab_m23u {i : ℕ} (hi : i < 4) : tab 23 (m23u i) = m23uT.getD i [] := by
  have hw : ∀ l ∈ m23uW.getD i [], l < 4 := by
    interval_cases i <;> decide
  rw [m23u, tab_evalEltL _ _ (by simpa using hw)]
  have hk : [m23k 0, m23k 1, m23k 2, m23k 3].map (tab 23) = m23kT := by
    simp only [List.map_cons, List.map_nil, tab_m23k (by norm_num : 0 < 4),
      tab_m23k (by norm_num : 1 < 4), tab_m23k (by norm_num : 2 < 4),
      tab_m23k (by norm_num : 3 < 4)]
    rfl
  rw [hk]
  exact m23Check_tabs.2.1 i (List.mem_range.2 hi)

theorem tab_m23uPow {e : ℕ} (he : e < 16) : tab 23 (m23uPow e) = m23uPowT e := by
  have hw : ∀ l ∈ m23bits e, l < [m23u 0, m23u 1, m23u 2, m23u 3].length := by
    intro l hl
    simp only [m23bits, List.mem_filter, List.mem_range] at hl
    simpa using hl.1
  rw [m23uPow, tab_evalEltL _ _ hw]
  have hu : [m23u 0, m23u 1, m23u 2, m23u 3].map (tab 23) = m23uT := by
    simp only [List.map_cons, List.map_nil, tab_m23u (by norm_num : 0 < 4),
      tab_m23u (by norm_num : 1 < 4), tab_m23u (by norm_num : 2 < 4),
      tab_m23u (by norm_num : 3 < 4)]
    rfl
  rw [hu]
  exact m23Check_tabs.2.2.2 e (List.mem_range.2 he)

theorem tab_m23g : tab 23 m23g = m23gT := by
  rw [m23g, tab_evalEltL _ _ (by decide)]
  have hA : tab 23 m23PermA = m23aT := by decide
  have hB : tab 23 m23PermB = m23bT := by decide
  simp only [List.map_cons, List.map_nil, hA, hB]
  exact m23Check_tabs.2.2.1

@[expose] def m23M (j e : ℕ) : ℕ := (m23mT.getD j []).getD e 0

@[expose] def m23G (e : ℕ) : ℕ := m23gM.getD e 0

theorem m23uPow_mul {e f : ℕ} (he : e < 16) (hf : f < 16) :
    m23uPow e * m23uPow f = m23uPow (e ^^^ f) := by
  have hef : e ^^^ f < 16 := Nat.xor_lt_two_pow (n := 4) he hf
  apply eq_of_tab_eq (n := 23)
  rw [tab_mul, tab_m23uPow he, tab_m23uPow hf, tab_m23uPow hef]
  exact m23Check_mul e (List.mem_range.2 he) f (List.mem_range.2 hf)

theorem m23k_uPow {j e : ℕ} (hj : j < 4) (he : e < 16) :
    m23M j e < 16 ∧ m23k j * m23uPow e = m23uPow (m23M j e) * m23k j := by
  obtain ⟨hlt, h⟩ := m23Check_conj.1 j (List.mem_range.2 hj) e (List.mem_range.2 he)
  refine ⟨hlt, eq_of_tab_eq (n := 23) ?_⟩
  rw [tab_mul, tab_mul, tab_m23k hj, tab_m23uPow he, tab_m23uPow (show m23M j e < 16 from hlt)]
  exact h

theorem m23g_uPow {e : ℕ} (he : e < 16) :
    m23G e < 16 ∧ m23g * m23uPow e = m23uPow (m23G e) * m23g := by
  obtain ⟨hlt, h⟩ := m23Check_conj.2 e (List.mem_range.2 he)
  refine ⟨hlt, eq_of_tab_eq (n := 23) ?_⟩
  rw [tab_mul, tab_mul, tab_m23g, tab_m23uPow he, tab_m23uPow (show m23G e < 16 from hlt)]
  exact h

theorem m23uPow_ne_one {e : ℕ} (he : e < 16) (he0 : e ≠ 0) : m23uPow e ≠ 1 := by
  intro h
  have h' := congrArg (tab 23) h
  rw [tab_m23uPow he, tab_one_L] at h'
  rcases m23Check_misc.1 e (List.mem_range.2 he) with h0 | h0
  · exact he0 h0
  · exact h0 h'

theorem m23uPow_two : m23uPow 2 = m23PermA := by
  apply eq_of_tab_eq (n := 23)
  rw [tab_m23uPow (by norm_num), m23Check_misc.2.1]
  decide

theorem m23getD_mem (i : ℕ) : [m23PermA, m23PermB].getD i 1 ∈ NativeSporadic.M23 := by
  rw [m23_eq_closure]
  rcases i with _ | _ | i
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact one_mem _

theorem evalCodes_mem_m23 (w : List ℤ) :
    evalCodes [m23PermA, m23PermB] w ∈ NativeSporadic.M23 := by
  induction w with
  | nil => exact one_mem _
  | cons z w ih =>
    rw [evalCodes]
    refine mul_mem ?_ ih
    split_ifs
    · exact m23getD_mem _
    · exact inv_mem (m23getD_mem _)

theorem m23k_mem (j : ℕ) : m23k j ∈ NativeSporadic.M23 := evalCodes_mem_m23 _

theorem m23u_mem (i : ℕ) : m23u i ∈ NativeSporadic.M23 :=
  evalEltL_mem _ (by simp [m23k_mem]) _

theorem m23uPow_mem (e : ℕ) : m23uPow e ∈ NativeSporadic.M23 :=
  evalEltL_mem _ (by simp [m23u_mem]) _

theorem m23g_mem : m23g ∈ NativeSporadic.M23 := by
  refine evalEltL_mem _ (fun x hx => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact m23getD_mem 0
  · exact m23getD_mem 1

theorem m23_centralizerIn_eq :
    centralizerIn NativeSporadic.M23 m23PermA = Subgroup.closure {x | ∃ j < 4, m23k j = x} ∧
      Nat.card (Subgroup.closure {x | ∃ j < 4, m23k j = x}) = 2688 := by
  obtain ⟨-, hcent⟩ := CFSG.ClassicalInvolution.m23_cover_and_centralizers
  obtain ⟨-, -, -, hKc1, -⟩ := m23_rep_data1
  have hc := hcent _ (List.mem_singleton_self _)
  have hrep : m23Rep1 = m23PermA := by decide
  have hlen : m23CentWords1.length = 4 := rfl
  have hset : {g | g ∈ m23CentWords1.map (evalCodes [m23PermA, m23PermB])} =
      {x | ∃ j < 4, m23k j = x} := by
    ext x
    show x ∈ m23CentWords1.map _ ↔ ∃ j < 4, m23k j = x
    rw [List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
      exact ⟨j, hlen ▸ hj, by rw [m23k, List.getD_eq_getElem _ _ hj]⟩
    · rintro ⟨j, hj, rfl⟩
      have hj' : j < m23CentWords1.length := hlen ▸ hj
      exact ⟨_, List.getElem_mem hj', by rw [m23k, List.getD_eq_getElem _ _ hj']⟩
  have hQ : m23CentQ1.originalSubgroup = Subgroup.closure {x | ∃ j < 4, m23k j = x} := by
    rw [m23CentQ1, certificate_originalSubgroup, hset]
  dsimp only at hc
  rw [m23Certificate_originalSubgroup, hrep] at hc
  exact ⟨hc.trans hQ, hQ ▸ hKc1⟩

theorem m23M_lt {j e : ℕ} (hj : j < 4) (he : e < 16) : m23M j e < 16 :=
  (m23Check_conj.1 j (List.mem_range.2 hj) e (List.mem_range.2 he)).1

theorem m23G_lt {e : ℕ} (he : e < 16) : m23G e < 16 :=
  (m23Check_conj.2 e (List.mem_range.2 he)).1

theorem foldl_invariant {α β : Type} (f : β → α → β) (Q : β → Prop) (L : List α) (b : β)
    (hb : Q b) (hf : ∀ b, Q b → ∀ a ∈ L, Q (f b a)) : Q (L.foldl f b) := by
  induction L generalizing b with
  | nil => exact hb
  | cons a L ih =>
    exact ih _ (hf b hb a List.mem_cons_self) fun b' hb' a' ha' =>
      hf b' hb' a' (List.mem_cons_of_mem _ ha')

theorem m23round_sub {P : ℕ → Prop} (hxor : ∀ x y, P x → P y → P (x ^^^ y))
    (hM : ∀ x, P x → ∀ j < 4, P (m23M j x)) {V : List ℕ} (hV : ∀ x ∈ V, P x) :
    ∀ x ∈ m23round V, P x := by
  have hadd : ∀ W : List ℕ, (∀ x ∈ W, P x) → ∀ y, P y → ∀ x ∈ m23addVec W y, P x := by
    intro W hW y hy x hx
    unfold m23addVec at hx
    split_ifs at hx
    · exact hW x hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact hW x hx
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
        exact hxor w y (hW w hw) hy
  refine foldl_invariant _ (fun W => ∀ x ∈ W, P x) V V hV fun W hW x hx => ?_
  refine foldl_invariant _ (fun W => ∀ x ∈ W, P x) (List.range 4) W hW fun W' hW' j hj => ?_
  exact hadd W' hW' _ (hM x (hV x hx) j (List.mem_range.1 hj))

end M23Data

structure M23Frame (X : Type) [Group X] (t : X) where
  k : ℕ → X
  u : ℕ → X
  g : X
  u_mul : ∀ {e f : ℕ}, e < 16 → f < 16 → u e * u f = u (e ^^^ f)
  k_u : ∀ {j e : ℕ}, j < 4 → e < 16 → k j * u e = u (m23M j e) * k j
  g_u : ∀ {e : ℕ}, e < 16 → g * u e = u (m23G e) * g
  u_ne : ∀ {e : ℕ}, e < 16 → e ≠ 0 → u e ≠ 1
  u_two : u 2 = t
  cent : Subgroup.centralizer ({t} : Set X) = Subgroup.closure {x | ∃ j < 4, k j = x}
  card : Nat.card (Subgroup.centralizer ({t} : Set X)) = 2688

section FrameExists

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.A312M24 CFSG.Sporadic.Schreier
  CFSG.Blueprint

theorem mem_closure_map_iff {G H : Type} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) (S : Set G) (x : G) :
    f x ∈ Subgroup.closure (f '' S) ↔ x ∈ Subgroup.closure S := by
  rw [← MonoidHom.map_closure, Subgroup.mem_map_iff_mem hf]

theorem nonempty_m23Frame
    {X : Type} [Group X] (e : X ≃* ↥NativeSporadic.M23) {t : X}
    (ht : orderOf t = 2) : Nonempty (M23Frame X t) := by
  have hso : orderOf (e t : Equiv.Perm (Fin 23)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  obtain ⟨hcov, -⟩ := CFSG.ClassicalInvolution.m23_cover_and_centralizers
  obtain ⟨d, hd, c, hc, hsc⟩ := hcov (e t)
    (by rw [inv_one, one_mul, m23Certificate_originalSubgroup]; exact (e t).2) hso
  rw [List.mem_singleton] at hd
  subst hd
  rw [m23Certificate_originalSubgroup] at hc
  have hrep : m23Rep1 = m23PermA := by decide
  dsimp only at hsc
  rw [hrep] at hsc
  let θ : X ≃* ↥NativeSporadic.M23 := e.trans (MulAut.conj (⟨c, hc⟩ : ↥NativeSporadic.M23)⁻¹)
  have hθ : ∀ x, (θ x : Equiv.Perm (Fin 23)) = c⁻¹ * e x * c := fun x => by
    simp [θ]
  have hθt : θ t = ⟨m23PermA, m23getD_mem 0⟩ := Subtype.ext (by rw [hθ, hsc]; group)
  let P := NativeSporadic.M23
  let kP : ℕ → ↥P := fun j => ⟨m23k j, m23k_mem j⟩
  let uP : ℕ → ↥P := fun e => ⟨m23uPow e, m23uPow_mem e⟩
  have hSP : ∀ y : ↥P, (y : Equiv.Perm (Fin 23)) ∈ Subgroup.closure {x | ∃ j < 4, m23k j = x} ↔
      y ∈ Subgroup.closure {x | ∃ j < 4, kP j = x} := fun y => by
    have : {x | ∃ j < 4, m23k j = x} = P.subtype '' {x | ∃ j < 4, kP j = x} := by
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨kP j, ⟨j, hj, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨j, hj, rfl⟩
    rw [this]
    exact mem_closure_map_iff P.subtype_injective _ y
  have hSX : ∀ x : X, θ x ∈ Subgroup.closure {x | ∃ j < 4, kP j = x} ↔
      x ∈ Subgroup.closure {x | ∃ j < 4, θ.symm (kP j) = x} := fun x => by
    have : {x | ∃ j < 4, kP j = x} = θ.toMonoidHom '' {x | ∃ j < 4, θ.symm (kP j) = x} := by
      ext y
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨θ.symm (kP j), ⟨j, hj, rfl⟩, by simp⟩
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨j, hj, by simp⟩
    rw [this]
    exact mem_closure_map_iff θ.injective _ x
  obtain ⟨hCa, hcard⟩ := m23_centralizerIn_eq
  have hcent : Subgroup.centralizer ({t} : Set X) =
      Subgroup.closure {x | ∃ j < 4, θ.symm (kP j) = x} := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, ← hSX, ← hSP, ← hCa, centralizerIn,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    have h1 : x * t = t * x ↔ θ x * θ t = θ t * θ x := by
      rw [← map_mul, ← map_mul, θ.injective.eq_iff]
    rw [h1, hθt, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
    exact ⟨fun h => ⟨(θ x).2, h⟩, fun h => h.2⟩
  refine ⟨⟨fun j => θ.symm (kP j), fun e => θ.symm (uP e), θ.symm ⟨m23g, m23g_mem⟩,
    fun he hf => ?_, fun hj he => ?_, fun he => ?_, fun he he0 => ?_, ?_, hcent, ?_⟩⟩
  · rw [← map_mul]
    exact congrArg θ.symm (Subtype.ext (m23uPow_mul he hf))
  · rw [← map_mul, ← map_mul]
    exact congrArg θ.symm (Subtype.ext (m23k_uPow hj he).2)
  · rw [← map_mul, ← map_mul]
    exact congrArg θ.symm (Subtype.ext (m23g_uPow he).2)
  · intro h
    apply m23uPow_ne_one he he0
    have h' := congrArg θ h
    rw [MulEquiv.apply_symm_apply, map_one] at h'
    exact congrArg Subtype.val h'
  · rw [← θ.symm_apply_apply t, hθt]
    exact congrArg θ.symm (Subtype.ext m23uPow_two)
  · rw [hcent, ← hcard]
    have h1 : (Subgroup.closure {x | ∃ j < 4, θ.symm (kP j) = x}).map θ.toMonoidHom =
        Subgroup.closure {x | ∃ j < 4, kP j = x} := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨j, hj, by simp⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨θ.symm (kP j), ⟨j, hj, rfl⟩, by simp⟩
    have h2 : (Subgroup.closure {x | ∃ j < 4, kP j = x}).map P.subtype =
        Subgroup.closure {x | ∃ j < 4, m23k j = x} := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨j, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨kP j, ⟨j, hj, rfl⟩, rfl⟩
    rw [← h2, Subgroup.card_map_of_injective P.subtype_injective, ← h1,
      Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]

end FrameExists

namespace M23Frame

variable {X : Type} [Group X] {t : X} (F : M23Frame X t)

theorem u_zero : F.u 0 = 1 := by
  have h := F.u_mul (e := 0) (f := 0) (by norm_num) (by norm_num)
  rw [show (0 : ℕ) ^^^ 0 = 0 from rfl] at h
  exact mul_eq_left.mp h

theorem u_mul_self {e : ℕ} (he : e < 16) : F.u e * F.u e = 1 := by
  rw [F.u_mul he he, Nat.xor_self, F.u_zero]

theorem u_inj {e f : ℕ} (he : e < 16) (hf : f < 16) (h : F.u e = F.u f) : e = f := by
  by_contra hne
  have hx : e ^^^ f ≠ 0 := fun h0 => hne (by
    have h1 := congrArg (· ^^^ f) h0
    simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using h1)
  apply F.u_ne (Nat.xor_lt_two_pow (n := 4) he hf) hx
  rw [← F.u_mul he hf, h, F.u_mul_self hf]

@[expose] def U : Subgroup X where
  carrier := {x | ∃ e < 16, F.u e = x}
  one_mem' := ⟨0, by norm_num, F.u_zero⟩
  mul_mem' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩
    exact ⟨e ^^^ f, Nat.xor_lt_two_pow (n := 4) he hf, (F.u_mul he hf).symm⟩
  inv_mem' := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, he, (inv_eq_of_mul_eq_one_right (F.u_mul_self he)).symm⟩

theorem u_mem {e : ℕ} (he : e < 16) : F.u e ∈ F.U := ⟨e, he, rfl⟩

theorem isPGroup_U : IsPGroup 2 F.U := by
  rintro ⟨_, e, he, rfl⟩
  exact ⟨1, Subtype.ext (by simpa [pow_one, pow_two] using F.u_mul_self he)⟩

theorem card_U [Finite X] : 16 ≤ Nat.card F.U := by
  have hinj : Function.Injective (fun i : Fin 16 => (⟨F.u i, F.u_mem i.2⟩ : F.U)) :=
    fun i j h => Fin.ext (F.u_inj i.2 j.2 (congrArg Subtype.val h))
  simpa using Nat.card_le_card_of_injective _ hinj

theorem k_conj {j e : ℕ} (hj : j < 4) (he : e < 16) :
    F.k j * F.u e * (F.k j)⁻¹ = F.u (m23M j e) := by
  rw [F.k_u hj he, mul_inv_cancel_right]

theorem k_mem {j : ℕ} (hj : j < 4) : F.k j ∈ Subgroup.centralizer ({t} : Set X) := by
  rw [F.cent]
  exact Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem U_le_cent : F.U ≤ Subgroup.centralizer ({t} : Set X) := by
  rintro _ ⟨e, he, rfl⟩
  have h : F.u e * F.u 2 = F.u 2 * F.u e := by
    rw [F.u_mul he (by norm_num), F.u_mul (by norm_num) he, Nat.xor_comm]
  rw [F.u_two] at h
  exact Subgroup.mem_centralizer_singleton_iff.mpr h

theorem cent_le_normalizer [Finite X] :
    Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (F.U : Set X) := by
  rw [F.cent, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨e, he, rfl⟩ := hn
  rw [F.k_conj hj he]
  exact F.u_mem (m23M_lt hj he)

theorem g_mem_normalizer [Finite X] : F.g ∈ Subgroup.normalizer (F.U : Set X) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨e, he, rfl⟩ := hn
  rw [F.g_u he, mul_inv_cancel_right]
  exact F.u_mem (m23G_lt he)

theorem g_not_mem_normalizer :
    F.g ∉ Subgroup.normalizer (Subgroup.centralizer ({t} : Set X) : Set X) := by
  intro hg
  have hg' : F.g⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer ({t} : Set X) : Set X) :=
    inv_mem hg
  have hk := (Subgroup.mem_normalizer_iff.mp hg' (F.k 0)).mp (F.k_mem (by norm_num))
  rw [inv_inv] at hk
  have hgt : F.g * t * F.g⁻¹ = F.u 4 := by
    have h : F.g * F.u 2 * F.g⁻¹ = F.u 4 := by
      rw [F.g_u (by norm_num), mul_inv_cancel_right]
      rfl
    rwa [F.u_two] at h
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hk
  have h4 : F.k 0 * F.u 4 = F.u 4 * F.k 0 := by
    rw [← hgt]
    calc F.k 0 * (F.g * t * F.g⁻¹) = F.g * ((F.g⁻¹ * F.k 0 * F.g) * t) * F.g⁻¹ := by group
      _ = F.g * (t * (F.g⁻¹ * F.k 0 * F.g)) * F.g⁻¹ := by rw [hc]
      _ = F.g * t * F.g⁻¹ * F.k 0 := by group
  rw [F.k_u (by norm_num) (by norm_num)] at h4
  have h14 := F.u_inj (m23M_lt (by norm_num) (by norm_num)) (by norm_num) (mul_right_cancel h4)
  exact absurd h14 (by decide)

theorem U_le {W : Subgroup X} (hWk : ∀ j < 4, ∀ x ∈ W, F.k j * x * (F.k j)⁻¹ ∈ W) {e : ℕ}
    (he : e < 16) (he0 : e ≠ 0) (he2 : e ≠ 2) (heW : F.u e ∈ W) : F.U ≤ W := by
  have key : ∀ V : List ℕ, (∀ x ∈ V, x < 16 ∧ F.u x ∈ W) →
      ∀ x ∈ m23round V, x < 16 ∧ F.u x ∈ W := fun V hV =>
    m23round_sub (P := fun x => x < 16 ∧ F.u x ∈ W)
      (fun x y hx hy => ⟨Nat.xor_lt_two_pow (n := 4) hx.1 hy.1, by
        rw [← F.u_mul hx.1 hy.1]; exact W.mul_mem hx.2 hy.2⟩)
      (fun x hx j hj => ⟨m23M_lt hj hx.1, by rw [← F.k_conj hj hx.1]; exact hWk j hj _ hx.2⟩) hV
  have h0 : ∀ x ∈ [0, e], x < 16 ∧ F.u x ∈ W := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨by norm_num, by rw [F.u_zero]; exact W.one_mem⟩
    · exact ⟨he, heW⟩
  have hall := key _ (key _ h0)
  rintro _ ⟨f, hf, rfl⟩
  rcases m23Check_clos e (List.mem_range.2 he) with h | h | h
  · exact absurd h he0
  · exact absurd h he2
  · exact (hall f (h f (List.mem_range.2 hf))).2

end M23Frame

theorem m23_lift_injective
    {X : Type} [Group X] (e : X ≃* ↥CFSG.Blueprint.NativeSporadic.M23) {I : Type} [Group I]
    {π : I →* X} (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center I)
    (hperf : ⁅(⊤ : Subgroup I), (⊤ : Subgroup I)⁆ = ⊤) : Function.Injective π := by
  have hZX : Subgroup.center X = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, CFSG.Sporadic.Schreier.m23_center_eq_bot',
      Subgroup.map_bot]
  have hZI : Subgroup.center I ≤ π.ker := fun x hx => by
    have h : π x ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun y => by
      obtain ⟨y', rfl⟩ := hπ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y']
    rw [hZX, Subgroup.mem_bot] at h
    exact h
  have hkerZ : π.ker = Subgroup.center I := le_antisymm hker hZI
  have hQ : Group.IsPerfect I := Group.isPerfect_def.mpr hperf
  let e₁ : I ⧸ Subgroup.center I ≃* ↥CFSG.Blueprint.NativeSporadic.M23 :=
    (QuotientGroup.quotientMulEquivOfEq hkerZ.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective π hπ).trans e)
  have h1 := CFSG.Sporadic.Recognition.M23Multiplier.card_center_eq_one_of_certificate hQ e₁
  rw [← MonoidHom.ker_eq_bot_iff, hkerZ]
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem normalizer_le_of_lift {X I : Type} [Group X] [Group I] {π : I →* X}
    (hπ : Function.Surjective π) (hinj : Function.Injective π) {B V : Subgroup X}
    {V₁ : Subgroup I} (hV₁ : V₁.map π = V)
    (hN : Subgroup.normalizer (V₁ : Set I) ≤
      Subgroup.normalizer ((B.comap π : Subgroup I) : Set I)) :
    Subgroup.normalizer (V : Set X) ≤ Subgroup.normalizer (B : Set X) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hπ x
  have hmem : ∀ w : I, w ∈ V₁ ↔ π w ∈ V := fun w => by
    rw [← hV₁, Subgroup.mem_map_iff_mem hinj]
  have hy : y ∈ Subgroup.normalizer (V₁ : Set I) := by
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro w
    have h := hx (π w)
    rw [← map_inv, ← map_mul, ← map_mul] at h
    exact (hmem w).trans (h.trans (hmem _).symm)
  have hy' := hN hy
  rw [Subgroup.mem_normalizer_iff] at hy' ⊢
  intro b
  obtain ⟨w, rfl⟩ := hπ b
  rw [← map_inv, ← map_mul, ← map_mul]
  exact hy' w

theorem card_pCoreOf_of_isExt_psl32 {X : Type} [Group X] [Finite X] {T B : Subgroup X}
    (hB : B ∈ lFamily T) {n : ℕ} (h : IsExt ↥B (fun V _ => IsE2 n V) (fun Y _ => IsPSL 3 2 1 Y)) :
    Nat.card (pCoreOf 2 B) = 2 ^ n ∧ Nat.card ↥B = 2 ^ n * 168 := by
  obtain ⟨W, hWn, hW, hY⟩ := h
  have hW2 : IsPGroup 2 W := fun w => ⟨1, by rw [pow_one]; exact pow_eq_one_of_elemAbelian hW w⟩
  have heq := pCore_eq_of_isSimpleGroup W hW2 (isSimpleGroup_of_stated hY)
    (not_isPGroup_quotient hB W hW2)
  obtain ⟨eW⟩ := hW
  have hcardW : Nat.card W = 2 ^ n := by
    rw [Nat.card_congr (eW.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod]
    simp
  have hQ : Nat.card (↥B ⧸ W) = 168 := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hY).1 rfl]
    decide
  refine ⟨?_, ?_⟩
  · rw [pCoreOf_eq_map, heq, Subgroup.card_map_of_injective B.subtype_injective, hcardW]
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup W, hQ, hcardW, mul_comm]

theorem a312ZCentRestM23_holds :
    A312ZCentRestM23 := by
  intro X _ _ T B hcase hM23 hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hT, hB, -, -, -, ⟨z, hzT, hz1, -, hzB⟩, V, hVB, hV, hBV, hcomm, hV1, -,
    hLift⟩ := hc
  obtain ⟨e₀⟩ := hM23
  let e : X ≃* ↥CFSG.Blueprint.NativeSporadic.M23 :=
    (Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X)).trans e₀
  obtain ⟨k, hk1, hk2⟩ := exists_pow_involution hT.isPGroup (γ := ⟨z, hzT⟩)
    (fun h => hz1 (congrArg Subtype.val h))
  have ht1 : z ^ k ≠ 1 := fun h => hk1 (Subtype.ext (by simpa using h))
  have ht2 : z ^ k * z ^ k = 1 := by simpa using congrArg Subtype.val hk2
  have hto : orderOf (z ^ k) = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  obtain ⟨F⟩ := nonempty_m23Frame e hto
  have hBC : B ≤ Subgroup.centralizer ({z ^ k} : Set X) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Commute.pow_left (hzB b hb) k).eq.symm
  rcases hcase with h16 | h8
  · obtain ⟨hO, hcardB⟩ := card_pCoreOf_of_isExt_psl32 hB h16
    have hBeq : B = Subgroup.centralizer ({z ^ k} : Set X) :=
      Subgroup.eq_of_le_of_card_ge hBC (by rw [F.card, hcardB]; norm_num)
    have hUB : F.U ≤ B := by rw [hBeq]; exact F.U_le_cent
    have hBN : B ≤ Subgroup.normalizer (F.U : Set X) := by rw [hBeq]; exact F.cent_le_normalizer
    have hUeq : F.U = pCoreOf 2 B := Subgroup.eq_of_le_of_card_ge
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUB hBN F.isPGroup_U)
      (by rw [hO]; exact F.card_U)
    have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
    have hVU : V ≤ F.U := by
      rw [hUeq]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVB hBV hVp
    have hVk : ∀ j < 4, ∀ x ∈ V, F.k j * x * (F.k j)⁻¹ ∈ V := fun j hj x hx => by
      have hkB : F.k j ∈ B := by rw [hBeq]; exact F.k_mem hj
      exact (Subgroup.mem_normalizer_iff.mp (hBV hkB) x).mp hx
    by_cases hVt : ∃ x ∈ V, x ≠ 1 ∧ x ≠ z ^ k
    · obtain ⟨x, hxV, hx1, hxt⟩ := hVt
      obtain ⟨e', he', rfl⟩ := hVU hxV
      have he0 : e' ≠ 0 := fun h => hx1 (by rw [h, F.u_zero])
      have he2 : e' ≠ 2 := fun h => hxt (by rw [h, F.u_two])
      have hVeq : V = F.U := le_antisymm hVU (F.U_le hVk he' he0 he2 hxV)
      obtain ⟨I, _, _, π, hπ, hker, -, hperf, V₁, hV₁, hN⟩ := hLift
      have hNVB := normalizer_le_of_lift hπ (m23_lift_injective e hπ hker hperf) hV₁ hN
      have hg : F.g ∈ Subgroup.normalizer (B : Set X) :=
        hNVB (by rw [hVeq]; exact F.g_mem_normalizer)
      apply F.g_not_mem_normalizer
      rw [← hBeq]
      exact hg
    · push Not at hVt
      apply hV1
      have hle : V ≤ Subgroup.centralizer (B : Set X) := fun x hx => by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        rcases eq_or_ne x 1 with rfl | hx1
        · rw [mul_one, one_mul]
        · rw [hVt x hx hx1]
          exact Subgroup.mem_centralizer_singleton_iff.mp (hBC hb)
      rw [← hcomm, (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hle]
  · obtain ⟨hO, hcardB⟩ := card_pCoreOf_of_isExt_psl32 hB h8
    have hidx : (B.subgroupOf (Subgroup.centralizer ({z ^ k} : Set X))).index = 2 := by
      have h := Subgroup.card_mul_index (B.subgroupOf (Subgroup.centralizer ({z ^ k} : Set X)))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, hcardB, F.card] at h
      omega
    have hnorm := Subgroup.normal_of_index_eq_two hidx
    have hWk : ∀ j < 4, ∀ x ∈ F.U ⊓ B, F.k j * x * (F.k j)⁻¹ ∈ F.U ⊓ B := by
      intro j hj x hx
      refine ⟨(Subgroup.mem_normalizer_iff.mp (F.cent_le_normalizer (F.k_mem hj)) x).mp hx.1, ?_⟩
      exact hnorm.conj_mem ⟨x, F.U_le_cent hx.1⟩ hx.2 ⟨F.k j, F.k_mem hj⟩
    have hex : ∃ e' < 16, e' ≠ 0 ∧ e' ≠ 2 ∧ F.u e' ∈ F.U ⊓ B := by
      by_cases h1 : F.u 1 ∈ B
      · exact ⟨1, by norm_num, by norm_num, by norm_num, F.u_mem (by norm_num), h1⟩
      by_cases h4 : F.u 4 ∈ B
      · exact ⟨4, by norm_num, by norm_num, by norm_num, F.u_mem (by norm_num), h4⟩
      refine ⟨5, by norm_num, by norm_num, by norm_num, F.u_mem (by norm_num), ?_⟩
      have hmul := (Subgroup.mul_mem_iff_of_index_two hidx
        (a := ⟨F.u 1, F.U_le_cent (F.u_mem (by norm_num))⟩)
        (b := ⟨F.u 4, F.U_le_cent (F.u_mem (by norm_num))⟩)).mpr
        ⟨fun h => absurd h h1, fun h => absurd h h4⟩
      have h14 : F.u 1 * F.u 4 ∈ B := hmul
      rwa [F.u_mul (by norm_num) (by norm_num)] at h14
    obtain ⟨e', he', he0, he2, heW⟩ := hex
    have hUB : F.U ≤ B := fun x hx => (F.U_le hWk he' he0 he2 heW hx).2
    have hUO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUB
      (hBC.trans F.cent_le_normalizer) F.isPGroup_U
    have h16 := F.card_U
    have h8' : Nat.card F.U ≤ 2 ^ 3 := hO ▸ Subgroup.card_le_of_le hUO
    omega

end CFSG.Quasithin.Vol2.Ch10.A312A
