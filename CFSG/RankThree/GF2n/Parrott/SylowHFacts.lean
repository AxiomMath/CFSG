module

public import CFSG.RankThree.GF2n.Parrott.SylowH
import CFSG.GF2Type.Aschbacher1976Full.HSFiniteDefs

public section

namespace CFSG.RankThree.GF2n.Parrott

open scoped commutatorElement
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GF2Type.Aschbacher1976Full.HS.Six (tab tab_getD tab_one)

local notation "P45" => Equiv.Perm (Fin 45)

namespace SylowHFactsAux

private def pk : List ℕ → ℕ
  | [] => 0
  | x :: l => x + 64 * pk l

private def dg (n j : ℕ) : ℕ := n / 64 ^ j % 64

private theorem dg_pk : ∀ (l : List ℕ), (∀ x ∈ l, x < 64) → ∀ j, dg (pk l) j = l.getD j 0
  | [], _, j => by simp [pk, dg]
  | x :: l, h, 0 => by
    have hx : x < 64 := h x (by simp)
    simp only [dg, pk, pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hx
  | x :: l, h, j + 1 => by
    have hx : x < 64 := h x (by simp)
    have ih := dg_pk l (fun y hy => h y (by simp [hy])) j
    simp only [dg, pk] at ih ⊢
    rw [List.getD_cons_succ, ← ih, pow_succ, mul_comm (64 ^ j) 64, ← Nat.div_div_eq_div_mul]
    congr 2
    rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hx, zero_add]

private def mulN (a b : ℕ) : ℕ := pk ((List.range 45).map fun j => dg a (dg b j))

private def oneN : ℕ := pk (List.range 45)

private def tabN (σ : P45) : ℕ := pk (tab σ)

private theorem tab_lt (σ : P45) : ∀ x ∈ tab σ, x < 64 := by
  intro x hx
  simp only [tab, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  have := (σ i).isLt
  omega

private theorem dg_tabN (σ : P45) (j : Fin 45) : dg (tabN σ) j = σ j := by
  rw [tabN, dg_pk _ (tab_lt σ), tab_getD]

private theorem tabN_mul (σ τ : P45) : tabN (σ * τ) = mulN (tabN σ) (tabN τ) := by
  unfold tabN mulN
  congr 1
  apply List.ext_getElem
  · simp [tab]
  · intro k h1 h2
    have hk : k < 45 := by simpa [tab] using h1
    have e1 : (tab (σ * τ))[k]'h1 = ((σ * τ) ⟨k, hk⟩ : ℕ) := by
      rw [← tab_getD (σ * τ) ⟨k, hk⟩, List.getD_eq_getElem _ _ h1]
    have h3 : dg (pk (tab τ)) k = (τ ⟨k, hk⟩ : ℕ) := dg_tabN τ ⟨k, hk⟩
    have h4 : dg (pk (tab σ)) (τ ⟨k, hk⟩ : ℕ) = (σ (τ ⟨k, hk⟩) : ℕ) := dg_tabN σ (τ ⟨k, hk⟩)
    rw [e1, List.getElem_map, List.getElem_range, h3, h4]
    rfl

private theorem tabN_one : tabN 1 = oneN := by
  unfold tabN oneN
  rw [tab_one]
  rfl

private theorem tabN_injective : Function.Injective tabN := by
  intro σ τ h
  ext j
  rw [← dg_tabN σ j, ← dg_tabN τ j, h]

private def spanL : List P45 → List P45
  | [] => [1]
  | g :: gs => spanL gs ++ (spanL gs).map (g * ·)

private def spanN : List ℕ → List ℕ
  | [] => [oneN]
  | g :: gs => spanN gs ++ (spanN gs).map (mulN g)

private theorem map_tabN_spanL (gs : List P45) : (spanL gs).map tabN = spanN (gs.map tabN) := by
  induction gs with
  | nil => simp only [spanL, spanN, List.map_cons, List.map_nil, tabN_one]
  | cons g gs ih =>
    have h2 : ((spanL gs).map (g * ·)).map tabN =
        ((spanL gs).map tabN).map (mulN (tabN g)) := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun x _ => tabN_mul g x
    rw [spanL, List.map_append, h2, ih, List.map_cons, spanN]

private theorem one_mem_spanL (gs : List P45) : (1 : P45) ∈ spanL gs := by
  induction gs with
  | nil => simp [spanL]
  | cons g gs ih => simp [spanL, ih]

private theorem mem_closure_of_mem_spanL : ∀ (gs : List P45) {x : P45}, x ∈ spanL gs →
    x ∈ Subgroup.closure {g | g ∈ gs}
  | [], x, h => by
    simp only [spanL, List.mem_singleton] at h
    subst h
    exact one_mem _
  | g :: gs, x, h => by
    simp only [spanL, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨y, hy, rfl⟩
    · exact Subgroup.closure_mono (fun z hz => by simp only [Set.mem_setOf_eq] at hz ⊢; simp [hz])
        (mem_closure_of_mem_spanL gs h)
    · exact mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.closure_mono (fun z hz => by simp only [Set.mem_setOf_eq] at hz ⊢; simp [hz])
          (mem_closure_of_mem_spanL gs hy))

private theorem mem_spanL_of_mem_closure {gs : List P45}
    (hcl : ∀ τ ∈ spanN (gs.map tabN), ∀ σ ∈ gs.map tabN, mulN τ σ ∈ spanN (gs.map tabN))
    {x : P45} (hx : x ∈ Subgroup.closure {g | g ∈ gs}) : x ∈ spanL gs := by
  have key : ∀ x, x ∈ Submonoid.closure {g | g ∈ gs} → x ∈ spanL gs := by
    intro x hx'
    induction hx' using Submonoid.closure_induction_right with
    | one => exact one_mem_spanL gs
    | mul_right x _ y hy ih =>
      rw [← List.mem_map_of_injective tabN_injective, map_tabN_spanL, tabN_mul]
      refine hcl _ ?_ _ (List.mem_map_of_mem hy)
      rw [← map_tabN_spanL]
      exact List.mem_map_of_mem ih
  have hx' : x ∈ (Subgroup.closure {g | g ∈ gs}).toSubmonoid := hx
  rw [Subgroup.closure_toSubmonoid_of_finite] at hx'
  exact key x hx'

private theorem mem_closure_iff_tabN {gs : List P45} {Tgs : List ℕ} (hT : gs.map tabN = Tgs)
    (hcl : ∀ τ ∈ spanN Tgs, ∀ σ ∈ Tgs, mulN τ σ ∈ spanN Tgs) (x : P45) :
    x ∈ Subgroup.closure {g | g ∈ gs} ↔ tabN x ∈ spanN Tgs := by
  subst hT
  constructor
  · intro hx
    rw [← map_tabN_spanL]
    exact List.mem_map_of_mem (mem_spanL_of_mem_closure hcl hx)
  · intro hx
    rw [← map_tabN_spanL, List.mem_map_of_injective tabN_injective] at hx
    exact mem_closure_of_mem_spanL gs hx

private theorem card_closure_eq_length {gs : List P45} {Tgs : List ℕ} (hT : gs.map tabN = Tgs)
    (hcl : ∀ τ ∈ spanN Tgs, ∀ σ ∈ Tgs, mulN τ σ ∈ spanN Tgs) (hnd : (spanN Tgs).Nodup) :
    Nat.card ↥(Subgroup.closure {g | g ∈ gs}) = (spanN Tgs).length := by
  have hset : ∀ x : P45, x ∈ Subgroup.closure {g | g ∈ gs} ↔ x ∈ (spanL gs).toFinset := by
    intro x
    rw [mem_closure_iff_tabN hT hcl, List.mem_toFinset,
      ← List.mem_map_of_injective tabN_injective, map_tabN_spanL, hT]
  have hnd' : (spanL gs).Nodup := by
    subst hT
    rw [← map_tabN_spanL] at hnd
    exact List.Nodup.of_map _ hnd
  have hlen : (spanL gs).length = (spanN Tgs).length := by
    subst hT
    rw [← map_tabN_spanL, List.length_map]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hset), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd', hlen]

private def nU : ℕ :=
  pk [0, 1, 2, 9, 10, 11, 12, 13, 14, 3, 4, 5, 6, 7, 8, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
    35, 44, 42, 43, 38, 36, 37, 41, 39, 40, 25, 30, 31, 29, 33, 34, 32, 27, 28, 26]

private theorem tabN_u : tabN u = nU := by decide +kernel

private def nV : ℕ :=
  pk [0, 1, 2, 6, 8, 7, 3, 5, 4, 12, 14, 13, 9, 11, 10, 15, 16, 22, 19, 18, 24, 21, 17, 23, 20,
    35, 36, 42, 39, 38, 44, 41, 37, 43, 40, 25, 26, 32, 29, 28, 34, 31, 27, 33, 30]

private theorem tabN_v : tabN v = nV := by decide +kernel

private def nA1 : ℕ :=
  pk [0, 12, 9, 23, 43, 33, 21, 41, 31, 1, 11, 13, 2, 14, 10, 16, 15, 38, 29, 42, 24, 3, 27, 6,
    20, 26, 25, 18, 39, 22, 34, 5, 37, 8, 30, 36, 35, 28, 19, 32, 44, 4, 17, 7, 40]

private theorem tabN_alpha1 : tabN alpha1 = nA1 := by decide +kernel

private def nB1 : ℕ :=
  pk [0, 14, 11, 39, 29, 19, 37, 27, 17, 10, 12, 1, 13, 9, 2, 24, 20, 5, 41, 8, 16, 32, 43, 28,
    15, 34, 30, 4, 21, 7, 26, 42, 23, 38, 25, 44, 40, 3, 31, 6, 36, 22, 33, 18, 35]

private theorem tabN_beta1 : tabN beta1 = nB1 := by decide +kernel

private def nA2 : ℕ :=
  pk [0, 6, 3, 1, 5, 7, 2, 8, 4, 23, 28, 39, 21, 32, 37, 16, 15, 29, 38, 27, 24, 9, 42, 12, 20,
    30, 34, 17, 13, 19, 25, 43, 10, 41, 26, 44, 40, 11, 22, 14, 36, 31, 18, 33, 35]

private theorem tabN_alpha2 : tabN alpha2 = nA2 := by decide +kernel

private def nB2 : ℕ :=
  pk [0, 8, 5, 4, 6, 1, 7, 3, 2, 33, 38, 19, 31, 42, 17, 24, 20, 11, 32, 14, 16, 41, 28, 43, 15,
    26, 25, 39, 18, 37, 34, 9, 22, 12, 30, 40, 44, 27, 13, 29, 35, 23, 10, 21, 36]

private theorem tabN_beta2 : tabN beta2 = nB2 := by decide +kernel

private theorem mem_closure_list_iff (l : List ↥QA45.originalSubgroup)
    (x : ↥QA45.originalSubgroup) :
    x ∈ Subgroup.closure {y | y ∈ l} ↔
      (x : P45) ∈ Subgroup.closure {g | g ∈ l.map Subtype.val} := by
  have h1 : (Subgroup.closure {y | y ∈ l}).map QA45.originalSubgroup.subtype =
      Subgroup.closure {g | g ∈ l.map Subtype.val} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    simp
  rw [← h1]
  exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).symm

private theorem mem_closure_list_iff_tabN {l : List ↥QA45.originalSubgroup} {Tgs : List ℕ}
    (hT : (l.map Subtype.val).map tabN = Tgs)
    (hcl : ∀ τ ∈ spanN Tgs, ∀ σ ∈ Tgs, mulN τ σ ∈ spanN Tgs) (x : ↥QA45.originalSubgroup) :
    x ∈ Subgroup.closure {y | y ∈ l} ↔ tabN (x : P45) ∈ spanN Tgs := by
  rw [mem_closure_list_iff, mem_closure_iff_tabN hT hcl]

private theorem card_closure_list {l : List ↥QA45.originalSubgroup} {Tgs : List ℕ}
    (hT : (l.map Subtype.val).map tabN = Tgs)
    (hcl : ∀ τ ∈ spanN Tgs, ∀ σ ∈ Tgs, mulN τ σ ∈ spanN Tgs) (hnd : (spanN Tgs).Nodup) :
    Nat.card ↥(Subgroup.closure {y | y ∈ l}) = (spanN Tgs).length := by
  have h1 : (Subgroup.closure {y | y ∈ l}).map QA45.originalSubgroup.subtype =
      Subgroup.closure {g | g ∈ l.map Subtype.val} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    simp
  rw [← card_closure_eq_length hT hcl hnd, ← h1]
  exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm

private def tN : ℕ := mulN nA1 nA1

private def TgsO : List ℕ := [tN, nA1, nB1, nA2, nB2]

private def TgsT : List ℕ := [nU, nV, tN, nA1, nB1, nA2, nB2]

private def TgsS : List ℕ := [nU, mulN nA1 nA2, mulN nB1 nB2, tN]

private def TgsE3 : List ℕ := [mulN nU nV, mulN nA1 nA2, mulN (mulN nA1 nB1) nB2, tN]

private def TgsE1 : List ℕ := [nV, nU, tN, mulN nA1 nA2]

private def TgsE2 : List ℕ := [mulN nV nA1, mulN (mulN nU nB1) nB2, tN, mulN nA1 nA2]

private theorem hclO : ∀ τ ∈ spanN TgsO, ∀ σ ∈ TgsO, mulN τ σ ∈ spanN TgsO := by decide +kernel
private theorem ndO : (spanN TgsO).Nodup := by decide +kernel
private theorem lenO : (spanN TgsO).length = 32 := by decide +kernel

private theorem hclT : ∀ τ ∈ spanN TgsT, ∀ σ ∈ TgsT, mulN τ σ ∈ spanN TgsT := by decide +kernel

private theorem hclS : ∀ τ ∈ spanN TgsS, ∀ σ ∈ TgsS, mulN τ σ ∈ spanN TgsS := by decide +kernel
private theorem ndS : (spanN TgsS).Nodup := by decide +kernel
private theorem lenS : (spanN TgsS).length = 16 := by decide +kernel
private theorem sqS : ∀ τ ∈ spanN TgsS, mulN τ τ = oneN := by decide +kernel
private theorem commS : ∀ τ ∈ spanN TgsS, ∀ σ ∈ TgsS, mulN τ σ = mulN σ τ := by decide +kernel

private theorem hclE3 : ∀ τ ∈ spanN TgsE3, ∀ σ ∈ TgsE3, mulN τ σ ∈ spanN TgsE3 := by
  decide +kernel
private theorem ndE3 : (spanN TgsE3).Nodup := by decide +kernel
private theorem lenE3 : (spanN TgsE3).length = 16 := by decide +kernel
private theorem hclE1 : ∀ τ ∈ spanN TgsE1, ∀ σ ∈ TgsE1, mulN τ σ ∈ spanN TgsE1 := by
  decide +kernel
private theorem ndE1 : (spanN TgsE1).Nodup := by decide +kernel
private theorem lenE1 : (spanN TgsE1).length = 16 := by decide +kernel
private theorem hclE2 : ∀ τ ∈ spanN TgsE2, ∀ σ ∈ TgsE2, mulN τ σ ∈ spanN TgsE2 := by
  decide +kernel
private theorem ndE2 : (spanN TgsE2).Nodup := by decide +kernel
private theorem lenE2 : (spanN TgsE2).length = 16 := by decide +kernel
private theorem cTO : ∀ τ ∈ spanN TgsT, (∀ σ ∈ TgsO, mulN τ σ = mulN σ τ) → τ = oneN ∨ τ = tN := by
  decide +kernel

private theorem commO : ∀ τ ∈ spanN TgsO, ∀ σ ∈ spanN TgsO,
    mulN τ σ = mulN σ τ ∨ mulN τ σ = mulN tN (mulN σ τ) := by decide +kernel

private theorem normO : ∀ σ ∈ TgsT, ∀ τ ∈ TgsO, ∃ y ∈ spanN TgsO, mulN σ τ = mulN y σ := by
  decide +kernel
private theorem conjE1E2 : ∀ τ ∈ TgsE1, ∃ y ∈ spanN TgsE2, mulN nB1 τ = mulN y nB1 := by
  decide +kernel

private theorem comm_a1_b1 : alpha1 * beta1 * alpha1⁻¹ * beta1⁻¹ = alpha1 * alpha1 := by
  decide +kernel

private theorem beta_mul_v_aux : beta * v = u * v * (alpha1 * alpha1) * beta := by
  decide +kernel

private theorem conj_ut_aux : beta1 * beta * alpha1 * (u * (alpha1 * alpha1)) =
    alpha1 * alpha2 * (beta1 * beta * alpha1) := by
  decide +kernel

private theorem mem_normalizer_closure {G : Type*} [Group G] [Finite G] {s : Set G} {g : G}
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s) :
    g ∈ Subgroup.normalizer ((Subgroup.closure s : Subgroup G) : Set G) := by
  have hle : (Subgroup.closure s).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure s := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro x hx
    exact h x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

private theorem closure_eq_of_subset {G : Type*} [Group G] {s : Set G} {l : List G}
    (h1 : ∀ y ∈ s, y ∈ Subgroup.closure {x | x ∈ l})
    (h2 : ∀ y ∈ l, y ∈ Subgroup.closure s) :
    Subgroup.closure s = Subgroup.closure {x | x ∈ l} :=
  le_antisymm ((Subgroup.closure_le _).2 h1) ((Subgroup.closure_le _).2 h2)

private theorem comm_of_comm_gens {G : Type*} [Group G] {s : Set G}
    (h : ∀ x ∈ Subgroup.closure s, ∀ g ∈ s, x * g = g * x) :
    ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
  intro x hx y hy
  have hle : Subgroup.closure s ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (h x hx g hg).symm
  exact ((Subgroup.mem_centralizer_singleton_iff).1 (hle hy)).symm

private theorem conj_mem_closure_list {lG lY lX : List ↥QA45.originalSubgroup}
    {TG TY TX : List ℕ} (hG : (lG.map Subtype.val).map tabN = TG)
    (hY : (lY.map Subtype.val).map tabN = TY) (hX : (lX.map Subtype.val).map tabN = TX)
    (h : ∀ σ ∈ TG, ∀ τ ∈ TY, ∃ y ∈ spanN TX, mulN σ τ = mulN y σ) :
    ∀ g ∈ lG, ∀ x ∈ lY, g * x * g⁻¹ ∈ Subgroup.closure {y | y ∈ lX} := by
  intro g hg x hx
  have hσ : tabN (g : P45) ∈ TG := by
    rw [← hG]
    exact List.mem_map_of_mem (List.mem_map_of_mem hg)
  have hτ : tabN (x : P45) ∈ TY := by
    rw [← hY]
    exact List.mem_map_of_mem (List.mem_map_of_mem hx)
  obtain ⟨y, hy, he⟩ := h _ hσ _ hτ
  rw [← hX, ← map_tabN_spanL] at hy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  rw [mem_closure_list_iff]
  have hgx : (g : P45) * x = z * g := by
    apply tabN_injective
    rw [tabN_mul, tabN_mul]
    exact he
  have : ((g * x * g⁻¹ : ↥QA45.originalSubgroup) : P45) = z := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hgx, mul_inv_cancel_right]
  rw [this]
  exact mem_closure_of_mem_spanL _ hz

private theorem closure_le_normalizer {lG lX : List ↥QA45.originalSubgroup} {TG TX : List ℕ}
    (hG : (lG.map Subtype.val).map tabN = TG) (hX : (lX.map Subtype.val).map tabN = TX)
    (h : ∀ σ ∈ TG, ∀ τ ∈ TX, ∃ y ∈ spanN TX, mulN σ τ = mulN y σ) :
    Subgroup.closure {y | y ∈ lG} ≤
      Subgroup.normalizer ((Subgroup.closure {y | y ∈ lX} : Subgroup ↥QA45.originalSubgroup) :
        Set ↥QA45.originalSubgroup) :=
  (Subgroup.closure_le _).2 fun g hg =>
    mem_normalizer_closure (conj_mem_closure_list hG hX hX h g hg)

private theorem map_center_eq_inf_centralizer {G : Type*} [Group G] (X : Subgroup G) :
    (Subgroup.center ↥X).map X.subtype = X ⊓ Subgroup.centralizer (X : Set G) := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, fun h hh => congrArg Subtype.val (hw ⟨h, hh⟩)⟩
  · rintro ⟨hz, hc⟩
    exact ⟨⟨z, hz⟩, fun w => Subtype.ext (hc w.1 w.2), rfl⟩

private theorem card_map_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card ↥(H.map (MulAut.conj g).toMonoidHom) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem isElemAbelian_of {X : Subgroup ↥QA45.originalSubgroup}
    {l : List ↥QA45.originalSubgroup} {Tgs : List ℕ}
    (hX : X = Subgroup.closure {y | y ∈ l})
    (hmem : ∀ x : ↥QA45.originalSubgroup, x ∈ X ↔ tabN (x : P45) ∈ spanN Tgs)
    (hT : (l.map Subtype.val).map tabN = Tgs) (hsq : ∀ τ ∈ spanN Tgs, mulN τ τ = oneN)
    (hcomm : ∀ τ ∈ spanN Tgs, ∀ σ ∈ Tgs, mulN τ σ = mulN σ τ) : CFSG.Open.IsElemAbelian 2 X := by
  refine ⟨isMulCommutative_iff.2 fun a b => ?_, fun x hx => ?_⟩
  · have hcg : ∀ x ∈ Subgroup.closure {y | y ∈ l}, ∀ g ∈ {y | y ∈ l}, x * g = g * x := by
      intro x hx g hg
      have hx' : tabN (x : P45) ∈ spanN Tgs := (hmem x).1 (hX ▸ hx)
      have hg' : tabN (g : P45) ∈ Tgs := by
        rw [← hT]
        exact List.mem_map_of_mem (List.mem_map_of_mem hg)
      refine Subtype.ext (tabN_injective ?_)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, tabN_mul, tabN_mul]
      exact hcomm _ hx' _ hg'
    exact Subtype.ext (comm_of_comm_gens hcg a.1 (hX ▸ a.2) b.1 (hX ▸ b.2))
  · have hx' := (hmem x).1 hx
    have : (x : P45) * x = 1 := tabN_injective (by rw [tabN_mul, tabN_one]; exact hsq _ hx')
    rw [sq]
    exact Subtype.ext this

end SylowHFactsAux

open SylowHFactsAux

section Model

set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "a1A" => (⟨alpha1, alpha1_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "b1A" => (⟨beta1, beta1_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "bA" => (⟨beta, beta_mem_A⟩ : ↥QA45.originalSubgroup)

@[expose] noncomputable def oTwoQA45 : Subgroup ↥QA45.originalSubgroup :=
  Subgroup.closure {a1A, b1A, a2A, b2A}

@[expose] noncomputable def sQA45 : Subgroup ↥QA45.originalSubgroup :=
  Subgroup.closure {uA, a1A * a2A, b1A * b2A, tA}

@[expose] noncomputable def eUVQA45 : Subgroup ↥QA45.originalSubgroup :=
  Subgroup.closure {uA * vA, a1A * a2A, a1A * b1A * b2A, tA}

@[expose] noncomputable def eVQA45 : Subgroup ↥QA45.originalSubgroup :=
  Subgroup.closure {vA, uA, tA, a1A * a2A}

@[expose] noncomputable def eVAQA45 : Subgroup ↥QA45.originalSubgroup :=
  Subgroup.closure {vA * a1A, uA * b1A * b2A, tA, a1A * a2A}

namespace SylowHFactsAux

private theorem tabN_t : tabN t = tN := by
  rw [← alpha1_sq, tabN_mul, tabN_alpha1]
  rfl

private noncomputable def lO : List ↥QA45.originalSubgroup := [tA, a1A, b1A, a2A, b2A]

private noncomputable def lT : List ↥QA45.originalSubgroup := [uA, vA, tA, a1A, b1A, a2A, b2A]

private noncomputable def lS : List ↥QA45.originalSubgroup := [uA, a1A * a2A, b1A * b2A, tA]

private noncomputable def lE3 : List ↥QA45.originalSubgroup :=
  [uA * vA, a1A * a2A, a1A * b1A * b2A, tA]

private noncomputable def lE1 : List ↥QA45.originalSubgroup := [vA, uA, tA, a1A * a2A]

private noncomputable def lE2 : List ↥QA45.originalSubgroup :=
  [vA * a1A, uA * b1A * b2A, tA, a1A * a2A]

private theorem lO_tab : (lO.map Subtype.val).map tabN = TgsO := by
  simp only [lO, TgsO, List.map_cons, List.map_nil, tabN_t, tabN_alpha1, tabN_beta1, tabN_alpha2,
    tabN_beta2]

private theorem lT_tab : (lT.map Subtype.val).map tabN = TgsT := by
  simp only [lT, TgsT, List.map_cons, List.map_nil, tabN_t, tabN_u, tabN_v, tabN_alpha1,
    tabN_beta1, tabN_alpha2, tabN_beta2]

private theorem lS_tab : (lS.map Subtype.val).map tabN = TgsS := by
  simp only [lS, TgsS, List.map_cons, List.map_nil, Subgroup.coe_mul, tabN_mul, tabN_t, tabN_u,
    tabN_alpha1, tabN_beta1, tabN_alpha2, tabN_beta2]

private theorem lE3_tab : (lE3.map Subtype.val).map tabN = TgsE3 := by
  simp only [lE3, TgsE3, List.map_cons, List.map_nil, Subgroup.coe_mul, tabN_mul, tabN_t, tabN_u,
    tabN_v, tabN_alpha1, tabN_beta1, tabN_alpha2, tabN_beta2]

private theorem lE1_tab : (lE1.map Subtype.val).map tabN = TgsE1 := by
  simp only [lE1, TgsE1, List.map_cons, List.map_nil, Subgroup.coe_mul, tabN_mul, tabN_t, tabN_u,
    tabN_v, tabN_alpha1, tabN_alpha2]

private theorem lE2_tab : (lE2.map Subtype.val).map tabN = TgsE2 := by
  simp only [lE2, TgsE2, List.map_cons, List.map_nil, Subgroup.coe_mul, tabN_mul, tabN_t, tabN_u,
    tabN_v, tabN_alpha1, tabN_beta1, tabN_alpha2, tabN_beta2]

private theorem tA_mem_closure {s : Set ↥QA45.originalSubgroup} (h : a1A ∈ s) :
    tA ∈ Subgroup.closure s := by
  have : tA = a1A * a1A := Subtype.ext alpha1_sq.symm
  rw [this]
  exact mul_mem (Subgroup.subset_closure h) (Subgroup.subset_closure h)

private theorem oTwoQA45_eq : oTwoQA45 = Subgroup.closure {y | y ∈ lO} := by
  refine closure_eq_of_subset (fun y hy => Subgroup.subset_closure ?_) (fun y hy => ?_)
  · rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [lO, Set.mem_setOf_eq, List.mem_cons, true_or, or_true]
  · simp only [lO, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact tA_mem_closure (Set.mem_insert _ _)
    all_goals exact Subgroup.subset_closure (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or, or_true])

private theorem sylowTwoQA45_eq : sylowTwoQA45 = Subgroup.closure {y | y ∈ lT} := by
  unfold sylowTwoQA45
  refine closure_eq_of_subset (fun y hy => Subgroup.subset_closure ?_) (fun y hy => ?_)
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [lT, Set.mem_setOf_eq, List.mem_cons, true_or, or_true]
  · simp only [lT, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp only [Set.mem_insert_iff, true_or])
    · exact Subgroup.subset_closure (by simp only [Set.mem_insert_iff, true_or, or_true])
    · exact tA_mem_closure (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
        or_true])
    all_goals exact Subgroup.subset_closure (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or, or_true])

private theorem sQA45_eq : sQA45 = Subgroup.closure {y | y ∈ lS} := by
  unfold sQA45
  refine closure_eq_of_subset (fun y hy => Subgroup.subset_closure ?_)
    (fun y hy => Subgroup.subset_closure ?_)
  · rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [lS, Set.mem_setOf_eq, List.mem_cons, true_or, or_true]
  · simp only [lS, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]

private theorem eUVQA45_eq : eUVQA45 = Subgroup.closure {y | y ∈ lE3} := by
  unfold eUVQA45
  refine closure_eq_of_subset (fun y hy => Subgroup.subset_closure ?_)
    (fun y hy => Subgroup.subset_closure ?_)
  · rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [lE3, Set.mem_setOf_eq, List.mem_cons, true_or, or_true]
  · simp only [lE3, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]

private theorem eVQA45_eq : eVQA45 = Subgroup.closure {y | y ∈ lE1} := by
  unfold eVQA45
  refine closure_eq_of_subset (fun y hy => Subgroup.subset_closure ?_)
    (fun y hy => Subgroup.subset_closure ?_)
  · rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [lE1, Set.mem_setOf_eq, List.mem_cons, true_or, or_true]
  · simp only [lE1, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]

private theorem eVAQA45_eq : eVAQA45 = Subgroup.closure {y | y ∈ lE2} := by
  unfold eVAQA45
  refine closure_eq_of_subset (fun y hy => Subgroup.subset_closure ?_)
    (fun y hy => Subgroup.subset_closure ?_)
  · rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [lE2, Set.mem_setOf_eq, List.mem_cons, true_or, or_true]
  · simp only [lE2, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]

private theorem mem_oTwoQA45 (x : ↥QA45.originalSubgroup) :
    x ∈ oTwoQA45 ↔ tabN (x : P45) ∈ spanN TgsO := by
  rw [oTwoQA45_eq]
  exact mem_closure_list_iff_tabN lO_tab hclO x

private theorem mem_sylowTwoQA45 (x : ↥QA45.originalSubgroup) :
    x ∈ sylowTwoQA45 ↔ tabN (x : P45) ∈ spanN TgsT := by
  rw [sylowTwoQA45_eq]
  exact mem_closure_list_iff_tabN lT_tab hclT x

private theorem mem_sQA45 (x : ↥QA45.originalSubgroup) :
    x ∈ sQA45 ↔ tabN (x : P45) ∈ spanN TgsS := by
  rw [sQA45_eq]
  exact mem_closure_list_iff_tabN lS_tab hclS x

private theorem t_commutes_T {y : ↥QA45.originalSubgroup} (hy : y ∈ sylowTwoQA45) :
    y * tA = tA * y := by
  have hle : sylowTwoQA45 ≤ Subgroup.centralizer {tA} := by
    unfold sylowTwoQA45
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subtype.ext t_commute_u.symm
    · exact Subtype.ext t_commute_v.symm
    · exact Subtype.ext t_commute_alpha1.symm
    · exact Subtype.ext t_commute_beta1.symm
    · exact Subtype.ext t_commute_alpha2.symm
    · exact Subtype.ext t_commute_beta2.symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

private theorem eq_one_or_t {z : ↥QA45.originalSubgroup} (hz : z ∈ sylowTwoQA45)
    (hc : ∀ y ∈ lO, z * y = y * z) : z = 1 ∨ z = tA := by
  have h1 : tabN (z : P45) ∈ spanN TgsT := (mem_sylowTwoQA45 z).1 hz
  have h2 : ∀ σ ∈ TgsO, mulN (tabN (z : P45)) σ = mulN σ (tabN (z : P45)) := by
    intro σ hσ
    rw [← lO_tab] at hσ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hσ
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    rw [← tabN_mul, ← tabN_mul]
    exact congrArg tabN (congrArg Subtype.val (hc y hy))
  rcases cTO _ h1 h2 with h | h
  · left
    refine Subtype.ext (tabN_injective ?_)
    rw [h, ← tabN_one]
    rfl
  · right
    refine Subtype.ext (tabN_injective ?_)
    rw [h, ← tabN_t]

private theorem card_zpowers_tA : Nat.card ↥(Subgroup.zpowers tA) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  refine orderOf_eq_prime ?_ ?_
  · rw [sq]
    exact Subtype.ext t_sq
  · intro h
    exact t_ne_one (by simpa using congrArg Subtype.val h)

private theorem card_oTwoQA45_aux : Nat.card ↥oTwoQA45 = 32 := by
  rw [oTwoQA45_eq, card_closure_list lO_tab hclO ndO, lenO]

private theorem lO_mem_oTwoQA45 {y : ↥QA45.originalSubgroup} (hy : y ∈ lO) : y ∈ oTwoQA45 := by
  rw [oTwoQA45_eq]
  exact Subgroup.subset_closure hy

end SylowHFactsAux

theorem t_mem_oTwoQA45 : (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup) ∈ oTwoQA45 := by
  rw [oTwoQA45_eq]
  exact tA_mem_closure (by simp only [lO, Set.mem_setOf_eq, List.mem_cons, true_or, or_true])

theorem t_mem_sylowTwoQA45 : (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup) ∈ sylowTwoQA45 := by
  unfold sylowTwoQA45
  exact tA_mem_closure (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true])

theorem card_oTwoQA45 : Nat.card ↥oTwoQA45 = 2 ^ 5 := by
  rw [card_oTwoQA45_aux]
  norm_num

theorem oTwoQA45_le_sylowTwoQA45 : oTwoQA45 ≤ sylowTwoQA45 := by
  rw [oTwoQA45_eq, sylowTwoQA45_eq]
  refine (Subgroup.closure_le _).2 fun y hy => Subgroup.subset_closure ?_
  simp only [lO, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    simp only [lT, Set.mem_setOf_eq, List.mem_cons, true_or, or_true]

theorem sylowTwoQA45_le_normalizer_oTwoQA45 :
    sylowTwoQA45 ≤ Subgroup.normalizer (oTwoQA45 : Set ↥QA45.originalSubgroup) := by
  rw [sylowTwoQA45_eq, oTwoQA45_eq]
  exact closure_le_normalizer lT_tab lO_tab normO

theorem oTwoQA45_inf_centralizer :
    oTwoQA45 ⊓ Subgroup.centralizer (oTwoQA45 : Set ↥QA45.originalSubgroup) =
      Subgroup.zpowers tA := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hzO, hzC⟩ := Subgroup.mem_inf.1 hz
    have hc : ∀ y ∈ lO, z * y = y * z := fun y hy =>
      (Subgroup.mem_centralizer_iff.1 hzC y (lO_mem_oTwoQA45 hy)).symm
    rcases eq_one_or_t (oTwoQA45_le_sylowTwoQA45 hzO) hc with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨t_mem_oTwoQA45, Subgroup.mem_centralizer_iff.2 fun y hy =>
      t_commutes_T (oTwoQA45_le_sylowTwoQA45 hy)⟩

theorem commutator_oTwoQA45 : ⁅oTwoQA45, oTwoQA45⁆ = Subgroup.zpowers tA := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rcases commO _ ((mem_oTwoQA45 g₁).1 hg₁) _ ((mem_oTwoQA45 g₂).1 hg₂) with h | h
    · have : g₁ * g₂ = g₂ * g₁ := by
        refine Subtype.ext (tabN_injective ?_)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, tabN_mul, tabN_mul]
        exact h
      rw [commutatorElement_eq_one_iff_mul_comm.2 this]
      exact one_mem _
    · have : g₁ * g₂ = tA * (g₂ * g₁) := by
        refine Subtype.ext (tabN_injective ?_)
        have e : tabN ((tA : ↥QA45.originalSubgroup) : P45) = tN := tabN_t
        simp only [Subgroup.coe_mul, tabN_mul, e]
        exact h
      have h3 : ⁅g₁, g₂⁆ = tA := by
        rw [commutatorElement_def, this]
        group
      rw [h3]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    have h1 : ⁅a1A, b1A⁆ = tA := by
      refine Subtype.ext ?_
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [comm_a1_b1, alpha1_sq]
    rw [← h1]
    exact Subgroup.commutator_mem_commutator
      (lO_mem_oTwoQA45 (by simp only [lO, List.mem_cons, true_or, or_true]))
      (lO_mem_oTwoQA45 (by simp only [lO, List.mem_cons, true_or, or_true]))

theorem sylowTwoQA45_inf_centralizer :
    sylowTwoQA45 ⊓ Subgroup.centralizer (sylowTwoQA45 : Set ↥QA45.originalSubgroup) =
      Subgroup.zpowers tA := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.1 hz
    have hc : ∀ y ∈ lO, z * y = y * z := fun y hy =>
      (Subgroup.mem_centralizer_iff.1 hzC y
        (oTwoQA45_le_sylowTwoQA45 (lO_mem_oTwoQA45 hy))).symm
    rcases eq_one_or_t hzT hc with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨t_mem_sylowTwoQA45, Subgroup.mem_centralizer_iff.2 fun y hy =>
      t_commutes_T hy⟩

theorem isExtraspecial2_oTwoQA45 :
    CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 oTwoQA45 := by
  refine ⟨IsPGroup.of_card card_oTwoQA45, ?_, ?_⟩
  · rw [commutator_oTwoQA45, map_center_eq_inf_centralizer, oTwoQA45_inf_centralizer]
  · rw [commutator_oTwoQA45]
    exact card_zpowers_tA

theorem isElemAbelian_sQA45 : CFSG.Open.IsElemAbelian 2 sQA45 :=
  isElemAbelian_of sQA45_eq mem_sQA45 lS_tab sqS commS

theorem card_sQA45 : Nat.card ↥sQA45 = 2 ^ 4 := by
  rw [sQA45_eq, card_closure_list lS_tab hclS ndS, lenS]
  norm_num

theorem card_eUVQA45 : Nat.card ↥eUVQA45 = 2 ^ 4 := by
  rw [eUVQA45_eq, card_closure_list lE3_tab hclE3 ndE3, lenE3]
  norm_num

theorem card_eVQA45 : Nat.card ↥eVQA45 = 2 ^ 4 := by
  rw [eVQA45_eq, card_closure_list lE1_tab hclE1 ndE1, lenE1]
  norm_num

theorem card_eVAQA45 : Nat.card ↥eVAQA45 = 2 ^ 4 := by
  rw [eVAQA45_eq, card_closure_list lE2_tab hclE2 ndE2, lenE2]
  norm_num

theorem map_conj_eVQA45 : eVQA45.map (MulAut.conj b1A).toMonoidHom = eVAQA45 := by
  have hG : (([b1A] : List ↥QA45.originalSubgroup).map Subtype.val).map tabN = [nB1] := by
    simp only [List.map_cons, List.map_nil, tabN_beta1]
  have hle : eVQA45.map (MulAut.conj b1A).toMonoidHom ≤ eVAQA45 := by
    rw [Subgroup.map_le_iff_le_comap, eVQA45_eq]
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    rw [SetLike.mem_coe, Subgroup.mem_comap, eVAQA45_eq]
    exact conj_mem_closure_list hG lE1_tab lE2_tab
      (fun σ hσ τ hτ => by rw [List.mem_singleton.1 hσ]; exact conjE1E2 τ hτ) b1A
      (List.mem_singleton_self _) y hy
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_conj, card_eVQA45, card_eVAQA45])

theorem conj_v_uvt_QA45 : bA * vA * bA⁻¹ = uA * vA * tA := by
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [mul_inv_eq_iff_eq_mul, ← alpha1_sq]
  exact beta_mul_v_aux

theorem conj_ut_alpha12_QA45 :
    b1A * bA * a1A * (uA * tA) * (b1A * bA * a1A)⁻¹ = a1A * a2A := by
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [mul_inv_eq_iff_eq_mul, ← alpha1_sq]
  exact conj_ut_aux

end Model

end CFSG.RankThree.GF2n.Parrott
