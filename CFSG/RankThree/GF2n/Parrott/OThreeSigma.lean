module

public import CFSG.RankThree.GF2n.Parrott.PSp43Model
import CFSG.GF2Type.Aschbacher1976Full.HSFiniteDefs

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GF2Type.Aschbacher1976Full.HS.Six (tab tab_getD tab_one suppT suppT_tab)

local notation "P45" => Equiv.Perm (Fin 45)

namespace OThreeSigmaAux

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

private theorem closure_eq_of_subset {G : Type*} [Group G] {s : Set G} {l : List G}
    (h1 : ∀ y ∈ s, y ∈ Subgroup.closure {x | x ∈ l})
    (h2 : ∀ y ∈ l, y ∈ Subgroup.closure s) :
    Subgroup.closure s = Subgroup.closure {x | x ∈ l} :=
  le_antisymm ((Subgroup.closure_le _).2 h1) ((Subgroup.closure_le _).2 h2)

private theorem mulN_comm_of_comm {a b : ↥QA45.originalSubgroup} (h : a * b = b * a) :
    mulN (tabN (a : P45)) (tabN (b : P45)) = mulN (tabN (b : P45)) (tabN (a : P45)) := by
  have h' := congrArg (fun w : ↥QA45.originalSubgroup => tabN (w : P45)) h
  simpa only [Subgroup.coe_mul, tabN_mul] using h'

private theorem comm_of_mulN_comm {a b : ↥QA45.originalSubgroup}
    (h : mulN (tabN (a : P45)) (tabN (b : P45)) = mulN (tabN (b : P45)) (tabN (a : P45))) :
    a * b = b * a := by
  refine Subtype.ext (tabN_injective ?_)
  simpa only [Subgroup.coe_mul, tabN_mul] using h

private theorem eq_of_tabN_eq {a b : ↥QA45.originalSubgroup}
    (h : tabN (a : P45) = tabN (b : P45)) : a = b :=
  Subtype.ext (tabN_injective h)

private def conjWordP (TP : List (ℕ × ℕ)) (w : List ℕ) (x : ℕ) : ℕ :=
  w.foldr (fun ℓ y => mulN (mulN (TP.getD ℓ (oneN, oneN)).1 y) (TP.getD ℓ (oneN, oneN)).2) x

private theorem conjWordP_spec {G : Subgroup ↥QA45.originalSubgroup}
    {lG : List ↥QA45.originalSubgroup} {TP : List (ℕ × ℕ)}
    (hP : lG.map (fun g : ↥QA45.originalSubgroup => (tabN (g : P45), tabN (g : P45)⁻¹)) = TP)
    (hG : ∀ g ∈ lG, g ∈ G) :
    ∀ w : List ℕ, ∃ c ∈ G, ∀ x : ↥QA45.originalSubgroup,
      tabN ((c * x * c⁻¹ : ↥QA45.originalSubgroup) : P45) = conjWordP TP w (tabN (x : P45)) := by
  intro w
  induction w with
  | nil =>
    refine ⟨1, one_mem _, fun x => ?_⟩
    simp [conjWordP]
  | cons ℓ w ih =>
    obtain ⟨c, hc, hcx⟩ := ih
    have hgG : lG.getD ℓ 1 ∈ G := by
      by_cases hℓ : ℓ < lG.length
      · rw [List.getD_eq_getElem _ _ hℓ]
        exact hG _ (List.getElem_mem hℓ)
      · rw [List.getD_eq_default _ _ (not_lt.1 hℓ)]
        exact one_mem _
    have hTP : TP.getD ℓ (oneN, oneN) =
        (tabN ((lG.getD ℓ 1 : ↥QA45.originalSubgroup) : P45),
          tabN ((lG.getD ℓ 1 : ↥QA45.originalSubgroup) : P45)⁻¹) := by
      rw [← hP]
      have h1 : (oneN, oneN) = (fun g : ↥QA45.originalSubgroup =>
          (tabN (g : P45), tabN (g : P45)⁻¹)) 1 := by
        simp [tabN_one]
      rw [h1, List.getD_map]
    refine ⟨lG.getD ℓ 1 * c, mul_mem hgG hc, fun x => ?_⟩
    have hconj : (lG.getD ℓ 1 * c) * x * (lG.getD ℓ 1 * c)⁻¹ =
        lG.getD ℓ 1 * (c * x * c⁻¹) * (lG.getD ℓ 1)⁻¹ := by group
    rw [hconj, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, tabN_mul, tabN_mul, hcx]
    simp only [conjWordP, List.foldr_cons, hTP]

private def nS1 : ℕ :=
  pk [0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 9, 10, 14, 12, 13, 35, 44, 42, 43, 38, 36, 37, 41, 39, 40,
    15, 24, 22, 23, 18, 16, 17, 21, 19, 20, 25, 34, 32, 33, 28, 26, 27, 31, 29, 30]

private def nS1i : ℕ :=
  pk [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 9, 13, 14, 12, 25, 30, 31, 29, 33, 34, 32, 27, 28, 26,
    35, 40, 41, 39, 43, 44, 42, 37, 38, 36, 15, 20, 21, 19, 23, 24, 22, 17, 18, 16]

private def nS2 : ℕ :=
  pk [0, 1, 2, 5, 3, 4, 8, 6, 7, 9, 10, 11, 12, 13, 14, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
    35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]

private def nS2i : ℕ :=
  pk [0, 1, 2, 4, 5, 3, 7, 8, 6, 9, 10, 11, 12, 13, 14, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44,
    15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]

private def nA2 : ℕ :=
  pk [0, 6, 3, 1, 5, 7, 2, 8, 4, 23, 28, 39, 21, 32, 37, 16, 15, 29, 38, 27, 24, 9, 42, 12, 20,
    30, 34, 17, 13, 19, 25, 43, 10, 41, 26, 44, 40, 11, 22, 14, 36, 31, 18, 33, 35]

private def nA2i : ℕ :=
  pk [0, 3, 6, 2, 8, 4, 1, 5, 7, 21, 32, 37, 23, 28, 39, 16, 15, 27, 42, 29, 24, 12, 38, 9, 20,
    30, 34, 19, 10, 17, 25, 41, 13, 43, 26, 44, 40, 14, 18, 11, 36, 33, 22, 31, 35]

private def nB2 : ℕ :=
  pk [0, 8, 5, 4, 6, 1, 7, 3, 2, 33, 38, 19, 31, 42, 17, 24, 20, 11, 32, 14, 16, 41, 28, 43, 15,
    26, 25, 39, 18, 37, 34, 9, 22, 12, 30, 40, 44, 27, 13, 29, 35, 23, 10, 21, 36]

private def nB2i : ℕ :=
  pk [0, 5, 8, 7, 3, 2, 4, 6, 1, 31, 42, 17, 33, 38, 19, 24, 20, 14, 28, 11, 16, 43, 32, 41, 15,
    26, 25, 37, 22, 39, 34, 12, 18, 9, 30, 40, 44, 29, 10, 27, 35, 21, 13, 23, 36]

private def nX1 : ℕ :=
  pk [1, 2, 0, 5, 3, 4, 7, 8, 6, 11, 9, 10, 13, 14, 12, 15, 21, 19, 20, 24, 22, 23, 18, 16, 17,
    25, 31, 29, 30, 34, 32, 33, 28, 26, 27, 35, 41, 39, 40, 44, 42, 43, 38, 36, 37]

private def nX1i : ℕ :=
  pk [2, 0, 1, 4, 5, 3, 8, 6, 7, 10, 11, 9, 14, 12, 13, 15, 23, 24, 22, 17, 18, 16, 20, 21, 19,
    25, 33, 34, 32, 27, 28, 26, 30, 31, 29, 35, 43, 44, 42, 37, 38, 36, 40, 41, 39]

private def nX2 : ℕ :=
  pk [6, 7, 8, 0, 2, 1, 3, 5, 4, 12, 13, 14, 15, 25, 35, 9, 16, 19, 22, 26, 29, 32, 36, 39, 42,
    10, 17, 20, 23, 27, 30, 33, 37, 40, 43, 11, 18, 21, 24, 28, 31, 34, 38, 41, 44]

private def nX2i : ℕ :=
  pk [3, 5, 4, 6, 8, 7, 0, 1, 2, 15, 25, 35, 9, 10, 11, 12, 16, 26, 36, 17, 27, 37, 18, 28, 38,
    13, 19, 29, 39, 20, 30, 40, 21, 31, 41, 14, 22, 32, 42, 23, 33, 43, 24, 34, 44]

private def x1P : P45 := beta * sigma1 * sigma2⁻¹ * beta⁻¹

private def x2P : P45 := alpha2 * x1P * alpha2⁻¹

private theorem tabN_sigma1 : tabN sigma1 = nS1 := by decide +kernel
private theorem tabN_sigma1_inv : tabN sigma1⁻¹ = nS1i := by decide +kernel
private theorem tabN_sigma2 : tabN sigma2 = nS2 := by decide +kernel
private theorem tabN_sigma2_inv : tabN sigma2⁻¹ = nS2i := by decide +kernel
private theorem tabN_alpha2 : tabN alpha2 = nA2 := by decide +kernel
private theorem tabN_alpha2_inv : tabN alpha2⁻¹ = nA2i := by decide +kernel
private theorem tabN_beta2 : tabN beta2 = nB2 := by decide +kernel
private theorem tabN_beta2_inv : tabN beta2⁻¹ = nB2i := by decide +kernel
private theorem tabN_x1P : tabN x1P = nX1 := by decide +kernel
private theorem tabN_x1P_inv : tabN x1P⁻¹ = nX1i := by decide +kernel
private theorem tabN_x2P : tabN x2P = nX2 := by decide +kernel
private theorem tabN_x2P_inv : tabN x2P⁻¹ = nX2i := by decide +kernel

private def TgsU : List ℕ := [nS1, nS1, nX1, nX1, nX2, nX2]

private def TPC : List (ℕ × ℕ) :=
  [(nS1, nS1i), (nX1, nX1i), (nX2, nX2i), (nA2, nA2i), (nB2, nB2i), (nS2, nS2i)]

private def Xlist : List ℕ :=
  (spanN TgsU).filter fun τ => !(τ == oneN) && !(τ == nS1) && !(τ == mulN nS1 nS1)

private def cWords : List (List ℕ) :=
  [[], [2], [3], [4], [1, 3], [1, 4], [2, 2], [3, 2], [3, 3], [3, 4], [4, 2], [4, 3], [3, 1, 3],
    [3, 1, 4], [3, 3, 2], [3, 3, 3], [3, 4, 2], [4, 1, 3], [4, 3, 2], [4, 3, 3], [3, 3, 1, 3],
    [3, 3, 3, 2], [4, 3, 1, 3], [4, 3, 3, 2]]

private def Ylist : List ℕ := cWords.map fun w => conjWordP TPC w nX1

private theorem hclU : ∀ τ ∈ spanN TgsU, ∀ σ ∈ TgsU, mulN τ σ ∈ spanN TgsU := by decide +kernel
private theorem cubeU : ∀ τ ∈ spanN TgsU, mulN (mulN τ τ) τ = oneN := by decide +kernel
private theorem zU : ∀ τ ∈ spanN TgsU, mulN τ nX1 = mulN nX1 τ → mulN τ nX2 = mulN nX2 τ →
    τ = oneN ∨ τ = nS1 ∨ τ = mulN nS1 nS1 := by decide +kernel
private theorem s1cU : ∀ τ ∈ spanN TgsU, mulN τ nS1 = mulN nS1 τ := by decide +kernel
private theorem nonabU : mulN nX1 nX2 ≠ mulN nX2 nX1 := by decide +kernel
private theorem s1cLetters : ∀ p ∈ TPC, mulN p.1 nS1 = mulN nS1 p.1 := by decide +kernel
private theorem hXY : ∀ τ ∈ Xlist, τ ∈ Ylist := by decide +kernel
end OThreeSigmaAux

open OThreeSigmaAux

section Model

set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "bA" => (⟨beta, beta_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "x1A" => bA * s1A * s2A⁻¹ * bA⁻¹
set_option quotPrecheck false in
local notation "x2A" => a2A * x1A * a2A⁻¹

@[expose] noncomputable def oThreeSigmaQA45 : Subgroup ↥QA45.originalSubgroup :=
  Subgroup.closure {s1A, x1A, x2A}

@[expose] noncomputable def cSigmaQA45 : Subgroup ↥QA45.originalSubgroup :=
  Subgroup.closure {s1A, x1A, x2A, a2A, b2A, s2A}

namespace OThreeSigmaAux

private noncomputable def lU : List ↥QA45.originalSubgroup := [s1A, s1A, x1A, x1A, x2A, x2A]

private noncomputable def lC : List ↥QA45.originalSubgroup := [s1A, x1A, x2A, a2A, b2A, s2A]

private theorem coe_x1A : ((x1A : ↥QA45.originalSubgroup) : P45) = x1P := rfl

private theorem coe_x2A : ((x2A : ↥QA45.originalSubgroup) : P45) = x2P := rfl

private theorem lU_tab : (lU.map Subtype.val).map tabN = TgsU := by
  simp only [lU, TgsU, List.map_cons, List.map_nil, coe_x1A, coe_x2A, tabN_x1P, tabN_x2P,
    tabN_sigma1]

private theorem lC_pairs :
    lC.map (fun g : ↥QA45.originalSubgroup => (tabN (g : P45), tabN (g : P45)⁻¹)) = TPC := by
  simp only [lC, TPC, List.map_cons, List.map_nil, coe_x1A, coe_x2A, tabN_x1P, tabN_x1P_inv,
    tabN_x2P, tabN_x2P_inv, tabN_sigma1, tabN_sigma1_inv, tabN_sigma2, tabN_sigma2_inv,
    tabN_alpha2, tabN_alpha2_inv, tabN_beta2, tabN_beta2_inv]

private theorem oThreeSigmaQA45_eq : oThreeSigmaQA45 = Subgroup.closure {y | y ∈ lU} := by
  unfold oThreeSigmaQA45
  refine closure_eq_of_subset (fun y hy => Subgroup.subset_closure ?_)
    (fun y hy => Subgroup.subset_closure ?_)
  · rcases hy with rfl | rfl | rfl <;>
      simp only [lU, Set.mem_setOf_eq, List.mem_cons, true_or, or_true]
  · simp only [lU, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]

private theorem cSigmaQA45_eq : cSigmaQA45 = Subgroup.closure {y | y ∈ lC} := by
  unfold cSigmaQA45
  refine closure_eq_of_subset (fun y hy => Subgroup.subset_closure ?_)
    (fun y hy => Subgroup.subset_closure ?_)
  · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [lC, Set.mem_setOf_eq, List.mem_cons, true_or, or_true]
  · simp only [lC, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]

private theorem mem_oThreeSigmaQA45 (x : ↥QA45.originalSubgroup) :
    x ∈ oThreeSigmaQA45 ↔ tabN (x : P45) ∈ spanN TgsU := by
  rw [oThreeSigmaQA45_eq]
  exact mem_closure_list_iff_tabN lU_tab hclU x

private theorem s1A_pow_three : (s1A : ↥QA45.originalSubgroup) ^ 3 = 1 := Subtype.ext sigma1_cube

private theorem mem_zpowers_s1A (y : ↥QA45.originalSubgroup) :
    y ∈ Subgroup.zpowers s1A ↔ y = 1 ∨ y = s1A ∨ y = s1A * s1A := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    have h3 : s1A ^ (3 : ℤ) = 1 := by simpa using s1A_pow_three
    have hk : s1A ^ k = s1A ^ (k % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
      rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
    rw [hk]
    have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h0 | h1 | h2
    · left
      rw [h0, zpow_zero]
    · right
      left
      rw [h1, zpow_one]
    · right
      right
      rw [h2, zpow_two]
  · rintro (rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
    · exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

private theorem tab_not_mem_zpowers {y : ↥QA45.originalSubgroup}
    (hy : y ∉ Subgroup.zpowers s1A) :
    tabN (y : P45) ≠ oneN ∧ tabN (y : P45) ≠ nS1 ∧ tabN (y : P45) ≠ mulN nS1 nS1 := by
  rw [mem_zpowers_s1A] at hy
  simp only [not_or] at hy
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨fun h => h1 (Subtype.ext (tabN_injective ?_)), fun h => h2 (Subtype.ext
    (tabN_injective ?_)), fun h => h3 (Subtype.ext (tabN_injective ?_))⟩
  · rw [h, ← tabN_one]
    rfl
  · rw [h]
    exact tabN_sigma1.symm
  · rw [h, Subgroup.coe_mul, tabN_mul, tabN_sigma1]

private theorem mem_Xlist {z : ↥QA45.originalSubgroup} (hz : z ∈ oThreeSigmaQA45)
    (hz1 : z ∉ Subgroup.zpowers s1A) : tabN (z : P45) ∈ Xlist := by
  unfold Xlist
  rw [List.mem_filter]
  refine ⟨(mem_oThreeSigmaQA45 z).1 hz, ?_⟩
  obtain ⟨h1, h2, h3⟩ := tab_not_mem_zpowers hz1
  simp [h1, h2, h3]

private theorem exists_conj_x1A {z : ↥QA45.originalSubgroup} (hz : z ∈ oThreeSigmaQA45)
    (hz1 : z ∉ Subgroup.zpowers s1A) : ∃ g ∈ cSigmaQA45, g * x1A * g⁻¹ = z := by
  have hx := mem_Xlist hz hz1
  obtain ⟨w, -, hw⟩ := List.mem_map.1 (hXY _ hx)
  obtain ⟨c, hc, hcx⟩ := conjWordP_spec (G := cSigmaQA45) lC_pairs
    (fun g hg => by rw [cSigmaQA45_eq]; exact Subgroup.subset_closure hg) w
  refine ⟨c, hc, Subtype.ext (tabN_injective ?_)⟩
  rw [hcx, coe_x1A, tabN_x1P]
  exact hw

end OThreeSigmaAux

theorem s1A_mem_oThreeSigmaQA45 : s1A ∈ oThreeSigmaQA45 :=
  Subgroup.subset_closure (by simp only [Set.mem_insert_iff, true_or])

theorem x1A_mem_oThreeSigmaQA45 : x1A ∈ oThreeSigmaQA45 :=
  Subgroup.subset_closure (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
    or_true])

theorem x2A_mem_oThreeSigmaQA45 : x2A ∈ oThreeSigmaQA45 :=
  Subgroup.subset_closure (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true])

theorem pow_three_oThreeSigmaQA45 : ∀ x ∈ oThreeSigmaQA45, x ^ 3 = 1 := by
  intro x hx
  have h := cubeU _ ((mem_oThreeSigmaQA45 x).1 hx)
  have h' : (x : P45) * x * x = 1 :=
    tabN_injective (by rw [tabN_mul, tabN_mul, tabN_one]; exact h)
  rw [pow_succ, pow_two]
  exact Subtype.ext h'

theorem not_isMulCommutative_oThreeSigmaQA45 : ¬ IsMulCommutative ↥oThreeSigmaQA45 := by
  intro hc
  have h := congrArg Subtype.val (congrArg Subtype.val (isMulCommutative_iff.1 hc
    ⟨x1A, x1A_mem_oThreeSigmaQA45⟩ ⟨x2A, x2A_mem_oThreeSigmaQA45⟩))
  have h' : x1P * x2P = x2P * x1P := h
  apply nonabU
  rw [← tabN_x1P, ← tabN_x2P, ← tabN_mul, ← tabN_mul, h']

theorem oThreeSigmaQA45_inf_centralizer :
    oThreeSigmaQA45 ⊓ Subgroup.centralizer (oThreeSigmaQA45 : Set ↥QA45.originalSubgroup) =
      Subgroup.zpowers s1A := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hzU, hzC⟩ := Subgroup.mem_inf.1 hz
    have e1 := mulN_comm_of_comm (Subgroup.mem_centralizer_iff.1 hzC _
      x1A_mem_oThreeSigmaQA45).symm
    have e2 := mulN_comm_of_comm (Subgroup.mem_centralizer_iff.1 hzC _
      x2A_mem_oThreeSigmaQA45).symm
    rw [coe_x1A, tabN_x1P] at e1
    rw [coe_x2A, tabN_x2P] at e2
    rw [mem_zpowers_s1A]
    rcases zU _ ((mem_oThreeSigmaQA45 z).1 hzU) e1 e2 with h | h | h
    · left
      exact eq_of_tabN_eq (by rw [h]; exact (tabN_one).symm)
    · right
      left
      exact eq_of_tabN_eq (by rw [h]; exact tabN_sigma1.symm)
    · right
      right
      refine eq_of_tabN_eq ?_
      rw [h, Subgroup.coe_mul, tabN_mul, tabN_sigma1]
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨s1A_mem_oThreeSigmaQA45,
      Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    refine comm_of_mulN_comm ?_
    have h := s1cU _ ((mem_oThreeSigmaQA45 y).1 hy)
    rw [← tabN_sigma1] at h
    exact h

theorem oThreeSigmaQA45_le_centralizer :
    oThreeSigmaQA45 ≤ Subgroup.centralizer {s1A} := fun y hy => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine comm_of_mulN_comm ?_
  have h := s1cU _ ((mem_oThreeSigmaQA45 y).1 hy)
  rw [← tabN_sigma1] at h
  exact h

theorem oThreeSigmaQA45_le_QP45 :
    oThreeSigmaQA45 ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  unfold oThreeSigmaQA45
  rw [Subgroup.closure_le]
  have hb : bA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := beta_mem_Q
  have hs1 : s1A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := sigma1_mem_Q
  have hs2 : s2A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := sigma2_mem_Q
  have ha2 : a2A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := alpha2_mem_Q
  have hx1 : x1A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    mul_mem (mul_mem (mul_mem hb hs1) (inv_mem hs2)) (inv_mem hb)
  have hx2 : x2A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    mul_mem (mul_mem ha2 hx1) (inv_mem ha2)
  intro y hy
  rcases hy with rfl | rfl | rfl
  exacts [hs1, hx1, hx2]

theorem cSigmaQA45_le_QP45 :
    cSigmaQA45 ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  unfold cSigmaQA45
  rw [Subgroup.closure_le]
  have hb : bA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := beta_mem_Q
  have hs1 : s1A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := sigma1_mem_Q
  have hs2 : s2A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := sigma2_mem_Q
  have ha2 : a2A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := alpha2_mem_Q
  have hb2 : b2A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := beta2_mem_Q
  have hx1 : x1A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    mul_mem (mul_mem (mul_mem hb hs1) (inv_mem hs2)) (inv_mem hb)
  have hx2 : x2A ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    mul_mem (mul_mem ha2 hx1) (inv_mem ha2)
  intro y hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hs1, hx1, hx2, ha2, hb2, hs2]

theorem cSigmaQA45_le_centralizer : cSigmaQA45 ≤ Subgroup.centralizer {s1A} := by
  rw [cSigmaQA45_eq]
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have hp : (tabN (g : P45), tabN (g : P45)⁻¹) ∈ TPC := by
    rw [← lC_pairs]
    exact List.mem_map_of_mem hg
  refine comm_of_mulN_comm ?_
  have h := s1cLetters _ hp
  rw [← tabN_sigma1] at h
  exact h

theorem exists_conj_sigma12_QA45 {x : ↥QA45.originalSubgroup} (hx : x ∈ oThreeSigmaQA45)
    (hx1 : x ∉ Subgroup.zpowers s1A) :
    ∃ g ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup,
      g * (s1A * s2A⁻¹) * g⁻¹ = x := by
  obtain ⟨c, hc, rfl⟩ := exists_conj_x1A hx hx1
  exact ⟨c * bA, mul_mem (cSigmaQA45_le_QP45 hc) beta_mem_Q, by group⟩

end Model

end CFSG.RankThree.GF2n.Parrott
