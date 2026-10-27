module

public import Certificates.Certificate19953

public section

namespace CFSG.Quasithin

open CFSG.CosetTable CFSG.Sporadic.Bridge

theorem u33_genTab_rep :
    ∀ k < 5, RepL (u33GenTab.getD k []) (u33GenP k) :=
  Certificates.certificate19953.1.1

theorem u33_genInvTab_rep :
    ∀ k < 5, RepL (u33GenInvTab.getD k []) (u33GenP k)⁻¹ :=
  Certificates.certificate19953.1.2.1

theorem wordProd_invW {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool)) :
    wordProd x (u33InvW w) = (wordProd x w)⁻¹ := by
  induction w with
  | nil => simp [u33InvW, wordProd]
  | cons l w ih =>
    have e : u33InvW (l :: w) = u33InvW w ++ [(l.1, !l.2)] := by simp [u33InvW]
    rw [e]
    simp only [wordProd, List.map_append, List.prod_append, List.map_cons, List.prod_cons,
      List.map_nil, List.prod_nil, mul_one, mul_inv_rev] at ih ⊢
    rw [ih]
    rcases l with ⟨i, b⟩
    cases b <;> simp

theorem u33_wordL_rep
    (w : List (ℕ × Bool)) (hw : ∀ l ∈ w, l.1 < 5) :
    RepL (u33WordL w) (wordProd u33GenP w) := by
  induction w with
  | nil => exact repL_one 28
  | cons l w ih =>
    simp only [u33WordL, List.foldr_cons, wordProd, List.map_cons, List.prod_cons] at ih ⊢
    have hl : l.1 < 5 := hw l List.mem_cons_self
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    rcases l with ⟨i, b⟩
    cases b
    · exact repL_mul (u33_genInvTab_rep i hl) ih'
    · exact repL_mul (u33_genTab_rep i hl) ih'

theorem u33T_telTab :
    ∀ i < 32, u33TelTab.getD i [] = u33WordL (u33TelW i) :=
  Certificates.certificate19953.1.2.2.1

theorem u33T_dTab :
    ∀ j < 14, u33DTab.getD j [] = u33WordL (u33DW j) :=
  Certificates.certificate19953.1.2.2.2.1

theorem u33T_dInvTab :
    ∀ j < 14, u33DInvTab.getD j [] = u33WordL (u33InvW (u33DW j)) :=
  Certificates.certificate19953.1.2.2.2.2.1

theorem u33P_letters :
    (∀ i < 32, ∀ l ∈ u33TelW i, l.1 < 3) ∧ (∀ j < 14, ∀ l ∈ u33DW j, l.1 < 5) ∧
    (∀ l ∈ u33DW 1, l.1 < 4) ∧ (∀ l ∈ u33DW 2, l.1 = 4) :=
  Certificates.certificate19953.1.2.2.2.2.2.1

theorem u33_telTab_rep :
    ∀ i < 32, RepL (u33TelTab.getD i []) (u33Tel u33GenP i) := by
  intro i hi
  rw [u33T_telTab i hi]
  exact u33_wordL_rep _ fun l hl => by have := u33P_letters.1 i hi l hl; omega

theorem u33_dTab_rep :
    ∀ j < 14, RepL (u33DTab.getD j []) (u33D u33GenP j) := by
  intro j hj
  rw [u33T_dTab j hj]
  exact u33_wordL_rep _ (u33P_letters.2.1 j hj)

theorem u33_dInvTab_rep :
    ∀ j < 14, RepL (u33DInvTab.getD j []) (u33D u33GenP j)⁻¹ := by
  intro j hj
  rw [u33T_dInvTab j hj]
  have h := u33_wordL_rep (u33InvW (u33DW j)) (fun l hl => by
    simp only [u33InvW, List.mem_map, List.mem_reverse] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    exact u33P_letters.2.1 j hj l' hl')
  rwa [wordProd_invW] at h

theorem repL_pow {σ : Equiv.Perm (Fin 28)} {g : List ℕ} (h : RepL g σ) (n : ℕ) :
    RepL ((List.replicate n g).foldr compL (List.range 28)) (σ ^ n) := by
  induction n with
  | zero => simpa using repL_one 28
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, pow_succ']
    exact repL_mul h ih

theorem u33T_orders :
    (List.replicate 4 (u33GenTab.getD 0 [])).foldr compL (List.range 28) = List.range 28 ∧
    (List.replicate 4 (u33GenTab.getD 1 [])).foldr compL (List.range 28) = List.range 28 ∧
    (List.replicate 2 (u33GenTab.getD 2 [])).foldr compL (List.range 28) = List.range 28 ∧
    (List.replicate 3 (u33GenTab.getD 3 [])).foldr compL (List.range 28) = List.range 28 ∧
    (List.replicate 3 (u33GenTab.getD 4 [])).foldr compL (List.range 28) = List.range 28 :=
  Certificates.certificate19953.1.2.2.2.2.2.2.1

theorem u33P_orders :
    u33GenP 0 ^ 4 = 1 ∧ u33GenP 1 ^ 4 = 1 ∧ u33GenP 2 ^ 2 = 1 ∧
    u33GenP 3 ^ 3 = 1 ∧ u33GenP 4 ^ 3 = 1 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := u33T_orders
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := repL_pow (u33_genTab_rep 0 (by norm_num)) 4
    rw [h0] at this
    exact eq_of_repL this (repL_one 28)
  · have := repL_pow (u33_genTab_rep 1 (by norm_num)) 4
    rw [h1] at this
    exact eq_of_repL this (repL_one 28)
  · have := repL_pow (u33_genTab_rep 2 (by norm_num)) 2
    rw [h2] at this
    exact eq_of_repL this (repL_one 28)
  · have := repL_pow (u33_genTab_rep 3 (by norm_num)) 3
    rw [h3] at this
    exact eq_of_repL this (repL_one 28)
  · have := repL_pow (u33_genTab_rep 4 (by norm_num)) 3
    rw [h4] at this
    exact eq_of_repL this (repL_one 28)

theorem u33T_next : ∀ i < 32, ∀ g < 3,
    compL (u33TelTab.getD i []) (u33GenTab.getD g []) = u33TelTab.getD (u33Nxt i g % 32) [] :=
  Certificates.certificate19953.1.2.2.2.2.2.2.2.1

theorem u33P_next : ∀ i : Fin 32, ∀ g : Fin 3,
    u33Tel u33GenP i * u33GenP g = u33Tel u33GenP (u33Nxt i g % 32) := by
  intro i g
  have h1 := repL_mul (u33_telTab_rep i i.2) (u33_genTab_rep g (by omega))
  rw [u33T_next i i.2 g g.2] at h1
  exact eq_of_repL h1 (u33_telTab_rep _ (Nat.mod_lt _ (by norm_num)))

theorem u33T_decX_0 : ∀ i < 32,
    compL (compL (u33DTab.getD 0 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 0 i % 32) [])
        (u33DTab.getD (u33DecXk 0 i % 14) [])) (u33TelTab.getD (u33DecXb 0 i % 32) []) :=
  Certificates.certificate19953.1.2.2.2.2.2.2.2.2.1

theorem u33T_decX_1 : ∀ i < 32,
    compL (compL (u33DTab.getD 1 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 1 i % 32) [])
        (u33DTab.getD (u33DecXk 1 i % 14) [])) (u33TelTab.getD (u33DecXb 1 i % 32) []) :=
  Certificates.certificate19953.1.2.2.2.2.2.2.2.2.2

theorem u33T_decX_2 : ∀ i < 32,
    compL (compL (u33DTab.getD 2 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 2 i % 32) [])
        (u33DTab.getD (u33DecXk 2 i % 14) [])) (u33TelTab.getD (u33DecXb 2 i % 32) []) :=
  Certificates.certificate19953.2.1.1

theorem u33T_decX_3 : ∀ i < 32,
    compL (compL (u33DTab.getD 3 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 3 i % 32) [])
        (u33DTab.getD (u33DecXk 3 i % 14) [])) (u33TelTab.getD (u33DecXb 3 i % 32) []) :=
  Certificates.certificate19953.2.1.2.1

theorem u33T_decX_4 : ∀ i < 32,
    compL (compL (u33DTab.getD 4 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 4 i % 32) [])
        (u33DTab.getD (u33DecXk 4 i % 14) [])) (u33TelTab.getD (u33DecXb 4 i % 32) []) :=
  Certificates.certificate19953.2.1.2.2.1

theorem u33T_decX_5 : ∀ i < 32,
    compL (compL (u33DTab.getD 5 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 5 i % 32) [])
        (u33DTab.getD (u33DecXk 5 i % 14) [])) (u33TelTab.getD (u33DecXb 5 i % 32) []) :=
  Certificates.certificate19953.2.1.2.2.2.1

theorem u33T_decX_6 : ∀ i < 32,
    compL (compL (u33DTab.getD 6 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 6 i % 32) [])
        (u33DTab.getD (u33DecXk 6 i % 14) [])) (u33TelTab.getD (u33DecXb 6 i % 32) []) :=
  Certificates.certificate19953.2.1.2.2.2.2.1

theorem u33T_decX_7 : ∀ i < 32,
    compL (compL (u33DTab.getD 7 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 7 i % 32) [])
        (u33DTab.getD (u33DecXk 7 i % 14) [])) (u33TelTab.getD (u33DecXb 7 i % 32) []) :=
  Certificates.certificate19953.2.1.2.2.2.2.2.1

theorem u33T_decX_8 : ∀ i < 32,
    compL (compL (u33DTab.getD 8 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 8 i % 32) [])
        (u33DTab.getD (u33DecXk 8 i % 14) [])) (u33TelTab.getD (u33DecXb 8 i % 32) []) :=
  Certificates.certificate19953.2.1.2.2.2.2.2.2.1

theorem u33T_decX_9 : ∀ i < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 9 i % 32) [])
        (u33DTab.getD (u33DecXk 9 i % 14) [])) (u33TelTab.getD (u33DecXb 9 i % 32) []) :=
  Certificates.certificate19953.2.1.2.2.2.2.2.2.2.1

theorem u33T_decX_10 : ∀ i < 32,
    compL (compL (u33DTab.getD 10 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 10 i % 32) [])
        (u33DTab.getD (u33DecXk 10 i % 14) [])) (u33TelTab.getD (u33DecXb 10 i % 32) []) :=
  Certificates.certificate19953.2.1.2.2.2.2.2.2.2.2.1

theorem u33T_decX_11 : ∀ i < 32,
    compL (compL (u33DTab.getD 11 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 11 i % 32) [])
        (u33DTab.getD (u33DecXk 11 i % 14) [])) (u33TelTab.getD (u33DecXb 11 i % 32) []) :=
  Certificates.certificate19953.2.1.2.2.2.2.2.2.2.2.2

theorem u33T_decX_12 : ∀ i < 32,
    compL (compL (u33DTab.getD 12 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 12 i % 32) [])
        (u33DTab.getD (u33DecXk 12 i % 14) [])) (u33TelTab.getD (u33DecXb 12 i % 32) []) :=
  Certificates.certificate19953.2.2.1.1

theorem u33T_decX_13 : ∀ i < 32,
    compL (compL (u33DTab.getD 13 []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa 13 i % 32) [])
        (u33DTab.getD (u33DecXk 13 i % 14) [])) (u33TelTab.getD (u33DecXb 13 i % 32) []) :=
  Certificates.certificate19953.2.2.1.2.1

theorem u33T_decX : ∀ j < 14, ∀ i < 32,
    compL (compL (u33DTab.getD j []) (u33TelTab.getD i [])) (u33GenTab.getD 3 []) =
      compL (compL (u33TelTab.getD (u33DecXa j i % 32) [])
        (u33DTab.getD (u33DecXk j i % 14) [])) (u33TelTab.getD (u33DecXb j i % 32) []) := by
  intro j hj
  interval_cases j
  · exact u33T_decX_0
  · exact u33T_decX_1
  · exact u33T_decX_2
  · exact u33T_decX_3
  · exact u33T_decX_4
  · exact u33T_decX_5
  · exact u33T_decX_6
  · exact u33T_decX_7
  · exact u33T_decX_8
  · exact u33T_decX_9
  · exact u33T_decX_10
  · exact u33T_decX_11
  · exact u33T_decX_12
  · exact u33T_decX_13

theorem u33P_decX : ∀ j : Fin 14, ∀ i : Fin 32,
    u33D u33GenP j * u33Tel u33GenP i * u33GenP 3 =
      u33Tel u33GenP (u33DecXa j i % 32) * u33D u33GenP (u33DecXk j i % 14) *
        u33Tel u33GenP (u33DecXb j i % 32) := by
  intro j i
  have h1 := repL_mul (repL_mul (u33_dTab_rep j j.2) (u33_telTab_rep i i.2))
    (u33_genTab_rep 3 (by norm_num))
  rw [u33T_decX j j.2 i i.2] at h1
  exact eq_of_repL h1 (repL_mul (repL_mul (u33_telTab_rep _ (Nat.mod_lt _ (by norm_num)))
    (u33_dTab_rep _ (Nat.mod_lt _ (by norm_num)))) (u33_telTab_rep _ (Nat.mod_lt _ (by norm_num))))

theorem u33T_decY_0 : ∀ i < 32,
    compL (compL (u33DTab.getD 0 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 0 i % 32) [])
        (u33DTab.getD (u33DecYk 0 i % 14) [])) (u33TelTab.getD (u33DecYb 0 i % 32) []) :=
  Certificates.certificate19953.2.2.1.2.2.1

theorem u33T_decY_1 : ∀ i < 32,
    compL (compL (u33DTab.getD 1 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 1 i % 32) [])
        (u33DTab.getD (u33DecYk 1 i % 14) [])) (u33TelTab.getD (u33DecYb 1 i % 32) []) :=
  Certificates.certificate19953.2.2.1.2.2.2.1

theorem u33T_decY_2 : ∀ i < 32,
    compL (compL (u33DTab.getD 2 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 2 i % 32) [])
        (u33DTab.getD (u33DecYk 2 i % 14) [])) (u33TelTab.getD (u33DecYb 2 i % 32) []) :=
  Certificates.certificate19953.2.2.1.2.2.2.2.1

theorem u33T_decY_3 : ∀ i < 32,
    compL (compL (u33DTab.getD 3 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 3 i % 32) [])
        (u33DTab.getD (u33DecYk 3 i % 14) [])) (u33TelTab.getD (u33DecYb 3 i % 32) []) :=
  Certificates.certificate19953.2.2.1.2.2.2.2.2.1

theorem u33T_decY_4 : ∀ i < 32,
    compL (compL (u33DTab.getD 4 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 4 i % 32) [])
        (u33DTab.getD (u33DecYk 4 i % 14) [])) (u33TelTab.getD (u33DecYb 4 i % 32) []) :=
  Certificates.certificate19953.2.2.1.2.2.2.2.2.2.1

theorem u33T_decY_5 : ∀ i < 32,
    compL (compL (u33DTab.getD 5 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 5 i % 32) [])
        (u33DTab.getD (u33DecYk 5 i % 14) [])) (u33TelTab.getD (u33DecYb 5 i % 32) []) :=
  Certificates.certificate19953.2.2.1.2.2.2.2.2.2.2.1

theorem u33T_decY_6 : ∀ i < 32,
    compL (compL (u33DTab.getD 6 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 6 i % 32) [])
        (u33DTab.getD (u33DecYk 6 i % 14) [])) (u33TelTab.getD (u33DecYb 6 i % 32) []) :=
  Certificates.certificate19953.2.2.1.2.2.2.2.2.2.2.2.1

theorem u33T_decY_7 : ∀ i < 32,
    compL (compL (u33DTab.getD 7 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 7 i % 32) [])
        (u33DTab.getD (u33DecYk 7 i % 14) [])) (u33TelTab.getD (u33DecYb 7 i % 32) []) :=
  Certificates.certificate19953.2.2.1.2.2.2.2.2.2.2.2.2

theorem u33T_decY_8 : ∀ i < 32,
    compL (compL (u33DTab.getD 8 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 8 i % 32) [])
        (u33DTab.getD (u33DecYk 8 i % 14) [])) (u33TelTab.getD (u33DecYb 8 i % 32) []) :=
  Certificates.certificate19953.2.2.2.1.1

theorem u33T_decY_9 : ∀ i < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 9 i % 32) [])
        (u33DTab.getD (u33DecYk 9 i % 14) [])) (u33TelTab.getD (u33DecYb 9 i % 32) []) :=
  Certificates.certificate19953.2.2.2.1.2.1

theorem u33T_decY_10 : ∀ i < 32,
    compL (compL (u33DTab.getD 10 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 10 i % 32) [])
        (u33DTab.getD (u33DecYk 10 i % 14) [])) (u33TelTab.getD (u33DecYb 10 i % 32) []) :=
  Certificates.certificate19953.2.2.2.1.2.2.1

theorem u33T_decY_11 : ∀ i < 32,
    compL (compL (u33DTab.getD 11 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 11 i % 32) [])
        (u33DTab.getD (u33DecYk 11 i % 14) [])) (u33TelTab.getD (u33DecYb 11 i % 32) []) :=
  Certificates.certificate19953.2.2.2.1.2.2.2.1

theorem u33T_decY_12 : ∀ i < 32,
    compL (compL (u33DTab.getD 12 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 12 i % 32) [])
        (u33DTab.getD (u33DecYk 12 i % 14) [])) (u33TelTab.getD (u33DecYb 12 i % 32) []) :=
  Certificates.certificate19953.2.2.2.1.2.2.2.2.1

theorem u33T_decY_13 : ∀ i < 32,
    compL (compL (u33DTab.getD 13 []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa 13 i % 32) [])
        (u33DTab.getD (u33DecYk 13 i % 14) [])) (u33TelTab.getD (u33DecYb 13 i % 32) []) :=
  Certificates.certificate19953.2.2.2.1.2.2.2.2.2.1

theorem u33T_decY : ∀ j < 14, ∀ i < 32,
    compL (compL (u33DTab.getD j []) (u33TelTab.getD i [])) (u33GenTab.getD 4 []) =
      compL (compL (u33TelTab.getD (u33DecYa j i % 32) [])
        (u33DTab.getD (u33DecYk j i % 14) [])) (u33TelTab.getD (u33DecYb j i % 32) []) := by
  intro j hj
  interval_cases j
  · exact u33T_decY_0
  · exact u33T_decY_1
  · exact u33T_decY_2
  · exact u33T_decY_3
  · exact u33T_decY_4
  · exact u33T_decY_5
  · exact u33T_decY_6
  · exact u33T_decY_7
  · exact u33T_decY_8
  · exact u33T_decY_9
  · exact u33T_decY_10
  · exact u33T_decY_11
  · exact u33T_decY_12
  · exact u33T_decY_13

theorem u33P_decY : ∀ j : Fin 14, ∀ i : Fin 32,
    u33D u33GenP j * u33Tel u33GenP i * u33GenP 4 =
      u33Tel u33GenP (u33DecYa j i % 32) * u33D u33GenP (u33DecYk j i % 14) *
        u33Tel u33GenP (u33DecYb j i % 32) := by
  intro j i
  have h1 := repL_mul (repL_mul (u33_dTab_rep j j.2) (u33_telTab_rep i i.2))
    (u33_genTab_rep 4 (by norm_num))
  rw [u33T_decY j j.2 i i.2] at h1
  exact eq_of_repL h1 (repL_mul (repL_mul (u33_telTab_rep _ (Nat.mod_lt _ (by norm_num)))
    (u33_dTab_rep _ (Nat.mod_lt _ (by norm_num)))) (u33_telTab_rep _ (Nat.mod_lt _ (by norm_num))))

theorem u33P_decXA :
    ∀ j < 2, ∀ i < 32, u33DecXk j i % 14 = 0 ∨ u33DecXk j i % 14 = 1 :=
  Certificates.certificate19953.2.2.2.1.2.2.2.2.2.2.1

theorem u33P_decYB : ∀ j < 3, j ≠ 1 → ∀ i < 32,
    u33DecYk j i % 14 = 0 ∨ u33DecYk j i % 14 = 2 :=
  Certificates.certificate19953.2.2.2.1.2.2.2.2.2.2.2.1

theorem u33_posL4_rep (j : ℕ) (hj : j < 14) (i : ℕ) :
    RepL (u33PosL4 j i) (u33Gen4 u33GenP (u33D u33GenP j) i) := by
  unfold u33PosL4 u33Gen4
  split_ifs
  · exact u33_genTab_rep 0 (by norm_num)
  · exact u33_genTab_rep 1 (by norm_num)
  · exact u33_genTab_rep 2 (by norm_num)
  · exact u33_dTab_rep j hj

theorem u33_negL4_rep (j : ℕ) (hj : j < 14) (i : ℕ) :
    RepL (u33NegL4 j i) (u33Gen4 u33GenP (u33D u33GenP j) i)⁻¹ := by
  unfold u33NegL4 u33Gen4
  split_ifs
  · exact u33_genInvTab_rep 0 (by norm_num)
  · exact u33_genInvTab_rep 1 (by norm_num)
  · exact u33_genInvTab_rep 2 (by norm_num)
  · exact u33_dInvTab_rep j hj

theorem u33_wordL4_rep (j : ℕ) (hj : j < 14) (w : List (ℕ × Bool)) :
    RepL (u33WordL4 j w) (wordProd (u33Gen4 u33GenP (u33D u33GenP j)) w) := by
  induction w with
  | nil => exact repL_one 28
  | cons l w ih =>
    simp only [u33WordL4, List.foldr_cons, wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rcases l with ⟨i, b⟩
    cases b
    · exact repL_mul (u33_negL4_rep j hj i) ih
    · exact repL_mul (u33_posL4_rep j hj i) ih

theorem u33T_mem : ∀ j < 14,
    (u33MemX.getD j "" ≠ "" →
      u33WordL4 j (u33W4 (u33MemX.getD j "")) = u33GenTab.getD 3 []) ∧
    (u33MemY.getD j "" ≠ "" →
      u33WordL4 j (u33W4 (u33MemY.getD j "")) = u33GenTab.getD 4 []) :=
  Certificates.certificate19953.2.2.2.1.2.2.2.2.2.2.2.2.1

theorem u33T_memLetters : ∀ j < 14,
    (∀ l ∈ u33W4 (u33MemX.getD j ""), l.1 < 4) ∧ (∀ l ∈ u33W4 (u33MemY.getD j ""), l.1 < 4) :=
  Certificates.certificate19953.2.2.2.1.2.2.2.2.2.2.2.2.2

theorem u33P_mem : ∀ j : Fin 14,
    (∀ l ∈ u33W4 (u33MemX.getD j ""), l.1 < 4) ∧ (∀ l ∈ u33W4 (u33MemY.getD j ""), l.1 < 4) ∧
    (u33MemX.getD j "" ≠ "" →
      wordProd (u33Gen4 u33GenP (u33D u33GenP j)) (u33W4 (u33MemX.getD j "")) = u33GenP 3) ∧
    (u33MemY.getD j "" ≠ "" →
      wordProd (u33Gen4 u33GenP (u33D u33GenP j)) (u33W4 (u33MemY.getD j "")) = u33GenP 4) := by
  intro j
  obtain ⟨h1, h2⟩ := u33T_memLetters j j.2
  refine ⟨h1, h2, fun hne => ?_, fun hne => ?_⟩
  · refine eq_of_repL (u33_wordL4_rep j j.2 _) ?_
    rw [(u33T_mem j j.2).1 hne]
    exact u33_genTab_rep 3 (by norm_num)
  · refine eq_of_repL (u33_wordL4_rep j j.2 _) ?_
    rw [(u33T_mem j j.2).2 hne]
    exact u33_genTab_rep 4 (by norm_num)

theorem u33P_mem_ne :
    u33MemX.getD 1 "" ≠ "" ∧ u33MemY.getD 2 "" ≠ "" ∧
    ∀ j : Fin 14, 3 ≤ j.val → u33MemX.getD j "" ≠ "" ∧ u33MemY.getD j "" ≠ "" :=
  Certificates.certificate19953.2.2.2.2.1.1

theorem u33T_sep3_0 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 0 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.1.2.1

theorem u33T_sep3_1 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 1 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.1.2.2.1

theorem u33T_sep3_2 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 2 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.1.2.2.2.1

theorem u33T_sep3_3 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 3 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.1.2.2.2.2.1

theorem u33T_sep3_4 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 4 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.1.2.2.2.2.2.1

theorem u33T_sep3_5 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 5 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.1.2.2.2.2.2.2.1

theorem u33T_sep3_6 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 6 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.1.2.2.2.2.2.2.2.1

theorem u33T_sep3_7 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 7 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.1.2.2.2.2.2.2.2.2.1

theorem u33T_sep3_8 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 8 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.1.2.2.2.2.2.2.2.2.2

theorem u33T_sep3_9 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 9 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.1.1

theorem u33T_sep3_10 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 10 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.1.2.1

theorem u33T_sep3_11 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 11 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.1.2.2.1

theorem u33T_sep3_12 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 12 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.1.2.2.2.1

theorem u33T_sep3_13 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 13 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.1.2.2.2.2.1

theorem u33T_sep3_14 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 14 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.1.2.2.2.2.2.1

theorem u33T_sep3_15 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 15 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.1.2.2.2.2.2.2.1

theorem u33T_sep3_16 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 16 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.1.2.2.2.2.2.2.2.1

theorem u33T_sep3_17 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 17 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1

theorem u33T_sep3_18 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 18 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2

theorem u33T_sep3_19 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 19 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.1.1

theorem u33T_sep3_20 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 20 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.1.2.1

theorem u33T_sep3_21 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 21 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.1.2.2.1

theorem u33T_sep3_22 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 22 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.1.2.2.2.1

theorem u33T_sep3_23 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 23 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.1.2.2.2.2.1

theorem u33T_sep3_24 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 24 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.1.2.2.2.2.2.1

theorem u33T_sep3_25 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 25 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.1.2.2.2.2.2.2.1

theorem u33T_sep3_26 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 26 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1

theorem u33T_sep3_27 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 27 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1

theorem u33T_sep3_28 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 28 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2

theorem u33T_sep3_29 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 29 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.2.1.1

theorem u33T_sep3_30 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 30 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.2.1.2.1

theorem u33T_sep3_31 : ∀ i₂ < 32,
    compL (compL (u33TelTab.getD 31 []) (u33DTab.getD 1 [])) (u33TelTab.getD i₂ []) ≠
      u33DTab.getD 2 [] :=
  Certificates.certificate19953.2.2.2.2.2.2.2.1.2.2.1

theorem u33T_sep :
    (∀ i < 32, u33TelTab.getD i [] ≠ u33DTab.getD 1 []) ∧
    (∀ i < 32, u33TelTab.getD i [] ≠ u33DTab.getD 2 []) ∧
    (∀ i₁ < 32, ∀ i₂ < 32, compL (compL (u33TelTab.getD i₁ []) (u33DTab.getD 1 []))
      (u33TelTab.getD i₂ []) ≠ u33DTab.getD 2 []) := by
  refine ⟨Certificates.certificate19953.2.2.2.2.2.2.2.1.2.2.2.1,
    Certificates.certificate19953.2.2.2.2.2.2.2.1.2.2.2.2.1, ?_⟩
  intro i₁ h₁
  interval_cases i₁
  · exact u33T_sep3_0
  · exact u33T_sep3_1
  · exact u33T_sep3_2
  · exact u33T_sep3_3
  · exact u33T_sep3_4
  · exact u33T_sep3_5
  · exact u33T_sep3_6
  · exact u33T_sep3_7
  · exact u33T_sep3_8
  · exact u33T_sep3_9
  · exact u33T_sep3_10
  · exact u33T_sep3_11
  · exact u33T_sep3_12
  · exact u33T_sep3_13
  · exact u33T_sep3_14
  · exact u33T_sep3_15
  · exact u33T_sep3_16
  · exact u33T_sep3_17
  · exact u33T_sep3_18
  · exact u33T_sep3_19
  · exact u33T_sep3_20
  · exact u33T_sep3_21
  · exact u33T_sep3_22
  · exact u33T_sep3_23
  · exact u33T_sep3_24
  · exact u33T_sep3_25
  · exact u33T_sep3_26
  · exact u33T_sep3_27
  · exact u33T_sep3_28
  · exact u33T_sep3_29
  · exact u33T_sep3_30
  · exact u33T_sep3_31

theorem u33P_sep :
    (∀ i : Fin 32, u33Tel u33GenP i ≠ u33D u33GenP 1) ∧
    (∀ i : Fin 32, u33Tel u33GenP i ≠ u33D u33GenP 2) ∧
    (∀ i₁ i₂ : Fin 32, u33Tel u33GenP i₁ * u33D u33GenP 1 * u33Tel u33GenP i₂ ≠
      u33D u33GenP 2) := by
  refine ⟨fun i h => ?_, fun i h => ?_, fun i₁ i₂ h => ?_⟩
  · refine u33T_sep.1 i i.2 (repL_unique (u33_telTab_rep i i.2) ?_)
    rw [h]; exact u33_dTab_rep 1 (by norm_num)
  · refine u33T_sep.2.1 i i.2 (repL_unique (u33_telTab_rep i i.2) ?_)
    rw [h]; exact u33_dTab_rep 2 (by norm_num)
  · refine u33T_sep.2.2 i₁ i₁.2 i₂ i₂.2 (repL_unique
      (repL_mul (repL_mul (u33_telTab_rep i₁ i₁.2) (u33_dTab_rep 1 (by norm_num)))
        (u33_telTab_rep i₂ i₂.2)) ?_)
    rw [h]; exact u33_dTab_rep 2 (by norm_num)

theorem u33T_inj :
    ∀ i < 32, ∀ j < 32, u33TelTab.getD i [] = u33TelTab.getD j [] → i = j :=
  Certificates.certificate19953.2.2.2.2.2.2.2.1.2.2.2.2.2.1

theorem u33P_inj
    : ∀ i j : Fin 32, u33Tel u33GenP i = u33Tel u33GenP j → i = j := by
  intro i j h
  refine Fin.ext (u33T_inj i i.2 j j.2 (repL_unique (u33_telTab_rep i i.2) ?_))
  rw [h]; exact u33_telTab_rep j j.2

theorem u33_gword_eq : u33W u33GWord = u33DW 9 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1

theorem u33T_g_0 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 0 [] → u33TelTab.getD 0 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1

theorem u33T_g_1 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 1 [] → u33TelTab.getD 1 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1

theorem u33T_g_2 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 2 [] → u33TelTab.getD 2 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2

theorem u33T_g_3 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 3 [] → u33TelTab.getD 3 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.1.1

theorem u33T_g_4 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 4 [] → u33TelTab.getD 4 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.1.2.1

theorem u33T_g_5 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 5 [] → u33TelTab.getD 5 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.1.2.2.1

theorem u33T_g_6 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 6 [] → u33TelTab.getD 6 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.1.2.2.2.1

theorem u33T_g_7 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 7 [] → u33TelTab.getD 7 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.1.2.2.2.2.1

theorem u33T_g_8 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 8 [] → u33TelTab.getD 8 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1

theorem u33T_g_9 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 9 [] → u33TelTab.getD 9 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1

theorem u33T_g_10 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 10 [] → u33TelTab.getD 10 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1

theorem u33T_g_11 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 11 [] → u33TelTab.getD 11 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1

theorem u33T_g_12 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 12 [] → u33TelTab.getD 12 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2

theorem u33T_g_13 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 13 [] → u33TelTab.getD 13 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.1.1

theorem u33T_g_14 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 14 [] → u33TelTab.getD 14 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.1.2.1

theorem u33T_g_15 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 15 [] → u33TelTab.getD 15 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.1.2.2.1

theorem u33T_g_16 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 16 [] → u33TelTab.getD 16 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.1.2.2.2.1

theorem u33T_g_17 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 17 [] → u33TelTab.getD 17 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1

theorem u33T_g_18 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 18 [] → u33TelTab.getD 18 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1

theorem u33T_g_19 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 19 [] → u33TelTab.getD 19 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1

theorem u33T_g_20 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 20 [] → u33TelTab.getD 20 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1

theorem u33T_g_21 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 21 [] → u33TelTab.getD 21 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1

theorem u33T_g_22 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 22 [] → u33TelTab.getD 22 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2

theorem u33T_g_23 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 23 [] → u33TelTab.getD 23 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.1.1

theorem u33T_g_24 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 24 [] → u33TelTab.getD 24 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.1.2.1

theorem u33T_g_25 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 25 [] → u33TelTab.getD 25 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.1.2.2.1

theorem u33T_g_26 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 26 [] → u33TelTab.getD 26 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1

theorem u33T_g_27 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 27 [] → u33TelTab.getD 27 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1

theorem u33T_g_28 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 28 [] → u33TelTab.getD 28 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1

theorem u33T_g_29 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 29 [] → u33TelTab.getD 29 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.1

theorem u33T_g_30 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 30 [] → u33TelTab.getD 30 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1

theorem u33T_g_31 : ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD 31 [] → u33TelTab.getD 31 [] = List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1

theorem u33T_g : ∀ i < 32, ∀ i' < 32,
    compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' [])) (u33DInvTab.getD 9 []) =
      u33TelTab.getD i [] → u33TelTab.getD i [] = List.range 28 := by
  intro i hi
  interval_cases i
  · exact u33T_g_0
  · exact u33T_g_1
  · exact u33T_g_2
  · exact u33T_g_3
  · exact u33T_g_4
  · exact u33T_g_5
  · exact u33T_g_6
  · exact u33T_g_7
  · exact u33T_g_8
  · exact u33T_g_9
  · exact u33T_g_10
  · exact u33T_g_11
  · exact u33T_g_12
  · exact u33T_g_13
  · exact u33T_g_14
  · exact u33T_g_15
  · exact u33T_g_16
  · exact u33T_g_17
  · exact u33T_g_18
  · exact u33T_g_19
  · exact u33T_g_20
  · exact u33T_g_21
  · exact u33T_g_22
  · exact u33T_g_23
  · exact u33T_g_24
  · exact u33T_g_25
  · exact u33T_g_26
  · exact u33T_g_27
  · exact u33T_g_28
  · exact u33T_g_29
  · exact u33T_g_30
  · exact u33T_g_31

theorem u33P_g : ∀ i i' : Fin 32,
    wordProd u33GenP (u33W u33GWord) * u33Tel u33GenP i' *
        (wordProd u33GenP (u33W u33GWord))⁻¹ = u33Tel u33GenP i → u33Tel u33GenP i = 1 := by
  intro i i' h
  rw [u33_gword_eq] at h
  have h1 := repL_mul (repL_mul (u33_dTab_rep 9 (by norm_num)) (u33_telTab_rep i' i'.2))
    (u33_dInvTab_rep 9 (by norm_num))
  have h2 : RepL (compL (compL (u33DTab.getD 9 []) (u33TelTab.getD i' []))
      (u33DInvTab.getD 9 [])) (u33Tel u33GenP i) := by
    rw [← h]; exact h1
  have h3 := repL_unique h2 (u33_telTab_rep i i.2)
  have h4 := u33T_g i i.2 i' i'.2 h3
  exact eq_of_repL (by rw [← h4]; exact u33_telTab_rep i i.2) (repL_one 28)

theorem u33T_xy : u33GenTab.getD 0 [] ≠ List.range 28 ∧
    (∀ i' < 32, compL (compL (u33GenTab.getD 3 []) (u33TelTab.getD 5 []))
      (u33GenInvTab.getD 3 []) ≠ u33TelTab.getD i' []) ∧
    (∀ i' < 32, compL (compL (u33GenTab.getD 4 []) (u33TelTab.getD 1 []))
      (u33GenInvTab.getD 4 []) ≠ u33TelTab.getD i' []) :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2

theorem u33P_xy : u33GenP 0 ≠ 1 ∧
    (∀ i' : Fin 32, u33GenP 3 * u33Tel u33GenP 5 * (u33GenP 3)⁻¹ ≠ u33Tel u33GenP i') ∧
    (∀ i' : Fin 32, u33GenP 4 * u33Tel u33GenP 1 * (u33GenP 4)⁻¹ ≠ u33Tel u33GenP i') := by
  refine ⟨ne_of_repL_ne (u33_genTab_rep 0 (by norm_num)) (repL_one 28) u33T_xy.1, fun i' h => ?_,
    fun i' h => ?_⟩
  · refine u33T_xy.2.1 i' i'.2 (repL_unique
      (repL_mul (repL_mul (u33_genTab_rep 3 (by norm_num)) (u33_telTab_rep 5 (by norm_num)))
        (u33_genInvTab_rep 3 (by norm_num))) ?_)
    rw [h]; exact u33_telTab_rep i' i'.2
  · refine u33T_xy.2.2 i' i'.2 (repL_unique
      (repL_mul (repL_mul (u33_genTab_rep 4 (by norm_num)) (u33_telTab_rep 1 (by norm_num)))
        (u33_genInvTab_rep 4 (by norm_num))) ?_)
    rw [h]; exact u33_telTab_rep i' i'.2

theorem u33_a2_rep : RepL u33A2Tab u33A2 :=
  repL_mul (u33_genTab_rep 0 (by norm_num)) (u33_genTab_rep 0 (by norm_num))

theorem u33_b2_rep : RepL u33B2Tab u33B2 :=
  repL_mul (u33_genTab_rep 1 (by norm_num)) (u33_genTab_rep 1 (by norm_num))

theorem u33_z_rep :
    RepL u33ZTab u33Z := repL_mul u33_a2_rep u33_b2_rep

theorem u33_vTab_rep (i : Fin 3) : RepL (u33VTab i) (u33V3 i) := by
  fin_cases i
  · exact u33_a2_rep
  · exact u33_b2_rep
  · exact u33_z_rep

theorem u33T_V : ∀ k < 4, ∀ i < 3,
    (∃ j < 3, compL (compL (u33GenTab.getD k []) (u33VTab i)) (u33GenInvTab.getD k []) =
      u33VTab j) ∧
    (∃ j < 3, compL (compL (u33GenInvTab.getD k []) (u33VTab i)) (u33GenTab.getD k []) =
      u33VTab j) :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.2.1

theorem u33P_V_aux (k : ℕ) (hk : k < 4) : ∀ i : Fin 3,
    (∃ j : Fin 3, u33GenP k * u33V3 i * (u33GenP k)⁻¹ = u33V3 j) ∧
    (∃ j : Fin 3, (u33GenP k)⁻¹ * u33V3 i * u33GenP k = u33V3 j) := by
  intro i
  obtain ⟨⟨j, hj, hj'⟩, ⟨j', hj2, hj2'⟩⟩ := u33T_V k hk i i.2
  refine ⟨⟨⟨j, hj⟩, ?_⟩, ⟨⟨j', hj2⟩, ?_⟩⟩
  · have h1 := repL_mul (repL_mul (u33_genTab_rep k (by omega)) (u33_vTab_rep i))
      (u33_genInvTab_rep k (by omega))
    rw [hj'] at h1
    exact eq_of_repL h1 (u33_vTab_rep ⟨j, hj⟩)
  · have h1 := repL_mul (repL_mul (u33_genInvTab_rep k (by omega)) (u33_vTab_rep i))
      (u33_genTab_rep k (by omega))
    rw [hj2'] at h1
    exact eq_of_repL h1 (u33_vTab_rep ⟨j', hj2⟩)

theorem u33P_V0
    : ∀ i : Fin 3, (∃ j : Fin 3, u33GenP 0 * u33V3 i * (u33GenP 0)⁻¹ = u33V3 j) ∧
    (∃ j : Fin 3, (u33GenP 0)⁻¹ * u33V3 i * u33GenP 0 = u33V3 j) :=
  u33P_V_aux 0 (by norm_num)

theorem u33P_V1
    : ∀ i : Fin 3, (∃ j : Fin 3, u33GenP 1 * u33V3 i * (u33GenP 1)⁻¹ = u33V3 j) ∧
    (∃ j : Fin 3, (u33GenP 1)⁻¹ * u33V3 i * u33GenP 1 = u33V3 j) :=
  u33P_V_aux 1 (by norm_num)

theorem u33P_V2
    : ∀ i : Fin 3, (∃ j : Fin 3, u33GenP 2 * u33V3 i * (u33GenP 2)⁻¹ = u33V3 j) ∧
    (∃ j : Fin 3, (u33GenP 2)⁻¹ * u33V3 i * u33GenP 2 = u33V3 j) :=
  u33P_V_aux 2 (by norm_num)

theorem u33P_V3
    : ∀ i : Fin 3, (∃ j : Fin 3, u33GenP 3 * u33V3 i * (u33GenP 3)⁻¹ = u33V3 j) ∧
    (∃ j : Fin 3, (u33GenP 3)⁻¹ * u33V3 i * u33GenP 3 = u33V3 j) :=
  u33P_V_aux 3 (by norm_num)

theorem u33T_A2 :
    u33A2Tab ≠ List.range 28 ∧ u33ZTab ≠ List.range 28 :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem u33P_A2 :
    u33A2 ≠ 1 := ne_of_repL_ne u33_a2_rep (repL_one 28) u33T_A2.1

theorem u33T_Z : ∀ k < 5, k ≠ 3 →
    compL (compL (u33GenTab.getD k []) u33ZTab) (u33GenInvTab.getD k []) = u33ZTab ∧
    compL (compL (u33GenInvTab.getD k []) u33ZTab) (u33GenTab.getD k []) = u33ZTab :=
  Certificates.certificate19953.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem u33P_Z :
    (∀ k ∈ [0, 1, 2, 4], u33GenP k * u33Z * (u33GenP k)⁻¹ = u33Z ∧
    (u33GenP k)⁻¹ * u33Z * u33GenP k = u33Z) ∧ u33Z ≠ 1 := by
  refine ⟨fun k hk => ?_, ne_of_repL_ne u33_z_rep (repL_one 28) u33T_A2.2⟩
  have hk5 : k < 5 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  have hk3 : k ≠ 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  obtain ⟨e1, e2⟩ := u33T_Z k hk5 hk3
  constructor
  · have h1 := repL_mul (repL_mul (u33_genTab_rep k hk5) u33_z_rep) (u33_genInvTab_rep k hk5)
    rw [e1] at h1
    exact eq_of_repL h1 u33_z_rep
  · have h1 := repL_mul (repL_mul (u33_genInvTab_rep k hk5) u33_z_rep) (u33_genTab_rep k hk5)
    rw [e2] at h1
    exact eq_of_repL h1 u33_z_rep

end CFSG.Quasithin
