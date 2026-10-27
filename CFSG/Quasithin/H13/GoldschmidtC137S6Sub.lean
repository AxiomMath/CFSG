module

public import CFSG.Quasithin.EmptyFaithful.S143LB

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.Quasithin.B3

theorem subOK_of_props {n : ℕ} {S : List Tab} (h1 : ∀ t ∈ S, isTab n t = true) (h2 : idT n ∈ S)
    (h3 : ∀ a ∈ S, ∀ b ∈ S, mulT a b ∈ S) (h4 : ∀ a ∈ S, invT a ∈ S) (h5 : S.Nodup) :
    subOK n S = true := by
  simp only [subOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq]
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

theorem exists_sublist_of_le {L : List Tab} (hLn : L.Nodup) {K : Subgroup (Gp 6)}
    (hKL : ∀ x ∈ K, tab x ∈ L) :
    ∃ X : List Tab, X.Sublist L ∧ subOK 6 X = true ∧ ∀ x : Gp 6, x ∈ K ↔ tab x ∈ X := by
  classical
  let X : List Tab := L.filter fun t => decide (∃ x ∈ K, tab x = t)
  have hmem : ∀ t, t ∈ X ↔ ∃ x ∈ K, tab x = t := by
    intro t
    simp only [X, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hKL x hx, x, hx, rfl⟩
  have hK : ∀ x : Gp 6, x ∈ K ↔ tab x ∈ X := by
    intro x
    rw [hmem]
    constructor
    · exact fun hx => ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← tab_injective hyx]
  refine ⟨X, List.filter_sublist, subOK_of_props (fun t ht => ?_) ?_ (fun a ha b hb => ?_)
    (fun a ha => ?_) (hLn.filter _), hK⟩
  · obtain ⟨x, -, rfl⟩ := (hmem t).1 ht
    exact isTab_tab x
  · rw [← tab_one]
    exact (hmem _).2 ⟨1, K.one_mem, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := (hmem a).1 ha
    obtain ⟨y, hy, rfl⟩ := (hmem b).1 hb
    rw [← tab_mul]
    exact (hmem _).2 ⟨x * y, K.mul_mem hx hy, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := (hmem a).1 ha
    rw [← tab_inv]
    exact (hmem _).2 ⟨x⁻¹, K.inv_mem hx, rfl⟩

theorem forall_le_subOf {L : List Tab} (hL : subOK 6 L = true) (P : Subgroup (Gp 6) → Prop)
    (h : ∀ X : List Tab, X.Sublist L → subOK 6 X = true → P (subOf 6 X)) :
    ∀ K : Subgroup (Gp 6), K ≤ subOf 6 L → P K := by
  intro K hK
  obtain ⟨X, hXL, hX, hKX⟩ := exists_sublist_of_le (subOK_spec hL).2.2.2.2 (K := K)
    (fun x hx => (mem_subOf hL).1 (hK hx))
  rw [subOf_eq hX hKX]
  exact h X hXL hX

theorem card_V6 : Nat.card (Mod.V 6 Mod.ut0) = 16 := by
  rw [← Nat.card_congr (S143.n6ModEquiv).toEquiv, S143.n6_card]

theorem cN6 : cN 6 Mod.ut0 = 2 := by
  have h := cntF_id (n := 6) Mod.ut0
  rw [card_V6] at h
  have h2 : cntF 6 Mod.ut0 [idT 6] = 32 := by decide +kernel
  omega

theorem card_mul_fix_eq {X : List Tab} (hX : subOK 6 X = true) :
    Nat.card ((subOf 6 X).map (Mod.act 6 Mod.ut0)) *
      Nat.card (fixV ((subOf 6 X).map (Mod.act 6 Mod.ut0))) * 2 = Fval 6 Mod.ut0 X := by
  rw [← cN6]
  exact fval_eq (by norm_num) Mod.ut0 hX (fun x => mem_subOf hX)

theorem act_fix_iff {m : ℕ} (hm : inWk 6 Mod.ut0 m = true) (σ : Gp 6) :
    Mod.act 6 Mod.ut0 σ (toV 6 Mod.ut0 m) = toV 6 Mod.ut0 m ↔
      inNk 6 Mod.ut0 (actM 6 (tab σ) m ^^^ m) = true := by
  have h1 := toV_ratio (k := Mod.ut0) σ hm
  have hw : inWk 6 Mod.ut0 (actM 6 (tab σ) m ^^^ m) = true := inWk_xor (inWk_actM σ hm) hm
  rw [← toV_eq_one_iff hw, ← h1, mul_inv_eq_one]

@[expose] def tokG (G : List Tab) (a : ℕ) : Tab :=
  if a < 100 then G.getD a (idT 6) else invT (G.getD (a - 100) (idT 6))

@[expose] def evalG (G : List Tab) : List ℕ → Tab
  | [] => idT 6
  | a :: l => mulT (tokG G a) (evalG G l)

theorem evalG_mem {K : Subgroup (Gp 6)} {G : List Tab} (hG : ∀ g ∈ G, ∃ x ∈ K, tab x = g) :
    ∀ l : List ℕ, ∃ σ ∈ K, tab σ = evalG G l := by
  have htok : ∀ a, ∃ σ ∈ K, tab σ = tokG G a := by
    intro a
    have hget : ∀ b, ∃ σ ∈ K, tab σ = G.getD b (idT 6) := by
      intro b
      by_cases hb : b < G.length
      · rw [List.getD_eq_getElem _ _ hb]
        exact hG _ (List.getElem_mem _)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact ⟨1, K.one_mem, tab_one⟩
    unfold tokG
    split_ifs
    · exact hget a
    · obtain ⟨σ, hσ, e⟩ := hget (a - 100)
      exact ⟨σ⁻¹, K.inv_mem hσ, by rw [tab_inv, e]⟩
  intro l
  induction l with
  | nil => exact ⟨1, K.one_mem, tab_one⟩
  | cons a l ih =>
    obtain ⟨σ, hσ, e1⟩ := htok a
    obtain ⟨τ, hτ, e2⟩ := ih
    exact ⟨σ * τ, K.mul_mem hσ hτ, by rw [tab_mul, e1, e2]; rfl⟩

theorem mem_of_word {K : Subgroup (Gp 6)} {G : List Tab} (hG : ∀ g ∈ G, ∃ x ∈ K, tab x = g)
    {l : List ℕ} {σ : Gp 6} (h : tab σ = evalG G l) : σ ∈ K := by
  obtain ⟨τ, hτ, e⟩ := evalG_mem hG l
  rwa [← tab_injective (e.trans h.symm)]

theorem eq_top_of_adjacent {K : Subgroup (Gp 6)}
    (h : ∀ i : Fin 5, Equiv.swap i.castSucc i.succ ∈ K) : K = ⊤ := by
  rw [eq_top_iff, ← Subgroup.closure_eq_top_of_mclosure_eq_top
    (Equiv.Perm.mclosure_swap_castSucc_succ 5), Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact h i

end CFSG.Quasithin.H13.U3.GC137
