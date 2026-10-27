module

public import CFSG.Quasithin.H13.NQCoreA6EOneCodes
public import CFSG.Quasithin.H13.NQCoreA6EOneStmt
public import Certificates.Certificate7095
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.H13.A6EOne

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.NQCore
open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open CFSG.QuasithinUnique.A6Facts.Core (cmul cid autL pslLit autReps autRepsInv pslGenC)
open CFSG.QuasithinUnique.Setup.X3Aut (invC code_inv)
open scoped commutatorElement

theorem checkAll_spec : checkAll = true :=
  Certificates.certificate7095

theorem setEqC_iff {L M : List (List ℕ)} : setEqC L M = true ↔ ∀ c, c ∈ L ↔ c ∈ M := by
  simp only [setEqC, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq]
  exact ⟨fun h c => ⟨h.1 c, h.2 c⟩, fun h => ⟨fun c => (h c).1, fun c => (h c).2⟩⟩

theorem commutesAll_iff {c : List ℕ} {E : List (List ℕ)} :
    commutesAll c E = true ↔ ∀ e ∈ E, cmul c e = cmul e c := by
  simp [commutesAll]

theorem exists_of_isPow2 {n : ℕ} (h : isPow2 n = true) : ∃ b, n = 2 ^ b := by
  simp only [isPow2, List.any_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨b, -, hb⟩ := h
  exact ⟨b, hb⟩

theorem code_conj (x y : P10) : code (x * y * x⁻¹) = conjC (code x) (code y) := by
  rw [code_mul, code_mul, code_inv]
  rfl

theorem code_commutator (x y : P10) : code ⁅x, y⁆ = commC (code x) (code y) := by
  rw [commutatorElement_def, code_mul, code_mul, code_mul, code_inv, code_inv]
  rfl

noncomputable def el (n : ℕ) : P10 := (exists_dc n).choose

theorem el_mem_autA6 (n : ℕ) : el n ∈ A6Models.autA6 := (exists_dc n).choose_spec.1

theorem code_el (n : ℕ) : code (el n) = dc n := (exists_dc n).choose_spec.2

theorem exists_el_of_mem_codes {L : List ℕ} {c : List ℕ} (hc : c ∈ codes L) :
    ∃ x : P10, code x = c := codes_realized L c hc

theorem foldl_cmul_code (w : List ℕ) (x₀ : P10) :
    w.foldl (fun acc l => cmul acc (dc l)) (code x₀) = code (x₀ * (w.map el).prod) := by
  induction w generalizing x₀ with
  | nil => simp
  | cons l w ih =>
    rw [List.foldl_cons, ← code_el l, ← code_mul, ih, List.map_cons, List.prod_cons, mul_assoc]

theorem mem_normalizer_of_conj_le {W : Subgroup P10} {x : P10}
    (h : ∀ w ∈ W, x * w * x⁻¹ ∈ W) : x ∈ normalizer (W : Set P10) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  let f : W → W := fun w => ⟨x * w * x⁻¹, h w w.2⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (by
    have := congrArg Subtype.val hab
    simpa [f] using this)
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hf) ⟨x * y * x⁻¹, hy⟩
  have hwy : (w : P10) = y := by
    have := congrArg Subtype.val hw
    simp only [f] at this
    exact mul_left_cancel (mul_right_cancel this)
  rw [← hwy]
  exact w.2

section Grp

variable {g : Grp}

theorem Grp.check_spec (h : g.check = true) :
    g.chkX = true ∧ g.chkS = true ∧ g.chkInv = true ∧ g.chkClose = true ∧ g.chkCls = true ∧
      g.chkWit = true ∧ g.chkWords = true := by
  simpa [Grp.check, and_assoc] using h

theorem Grp.chkS_spec (h : g.chkS = true) :
    isSubC g.Sc = true ∧ g.Sc.Nodup ∧ (∀ c ∈ g.Sc, inX g.I c = true) ∧
      g.Sc.length = 8 * g.I.length ∧ ∃ b, g.Sc.length = 2 ^ b := by
  simp only [Grp.chkS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, exists_of_isPow2 h.2⟩

theorem Grp.Ec_eq {j : ℕ} (hj : j < g.inv.length) : g.Ec j = codes g.inv[j] := by
  rw [Grp.Ec, List.getD_eq_getElem _ _ hj]

theorem Grp.chkInv_spec (h : g.chkInv = true) :
    (∀ j < g.inv.length, isSubC (g.Ec j) = true ∧ (g.Ec j).Nodup ∧ ∀ c ∈ g.Ec j, c ∈ g.Sc) ∧
      (∃ j < g.inv.length, ∀ c, c ∈ g.Ec j ↔ c = cid) ∧
      ∀ j < g.inv.length, (g.Ec j).length < 2 ∨ g.cls.getD j 0 < g.m := by
  simp only [Grp.chkInv, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, List.contains_eq_mem, List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨h1, j0, hj0, h2⟩, h3⟩ := h
  refine ⟨fun j hj => ?_, ?_, fun j hj => h3 j hj⟩
  · rw [g.Ec_eq hj]
    exact and_assoc.mp (h1 _ (List.getElem_mem hj))
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hj0
    refine ⟨j, hj, fun c => ?_⟩
    rw [g.Ec_eq hj]
    have := (setEqC_iff.mp h2) c
    simpa using this

theorem Grp.chkClose_spec (h : g.chkClose = true) :
    ∀ j < g.inv.length, ∀ c ∈ g.Sc, c ∉ g.Ec j → cmul c c = cid → commutesAll c (g.Ec j) = true →
      ∃ j' < g.inv.length, ∀ d, d ∈ g.Ec j' ↔ d ∈ g.Ec j ++ (g.Ec j).map (cmul c) := by
  simp only [Grp.chkClose, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    List.contains_eq_mem, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
    List.any_eq_true] at h
  intro j hj c hc hcj hcc hcomm
  rcases h j hj c hc with ((h1 | h1) | h1) | ⟨F, hF, h1⟩
  · exact absurd h1 hcj
  · exact absurd hcc h1
  · rw [hcomm] at h1
    exact absurd h1 (by decide)
  · obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hF
    refine ⟨j', hj', fun d => ?_⟩
    rw [g.Ec_eq hj']
    exact (setEqC_iff.mp h1) d

theorem Grp.chkCls_spec (h : g.chkCls = true) :
    ∀ j < g.inv.length, g.cls.getD j 0 < g.m →
      inX g.I (dc (g.cj.getD j 0)) = true ∧
        ∀ d, d ∈ (g.Ec j).map (conjC (dc (g.cj.getD j 0))) ↔
          d ∈ g.Ec (g.rep.getD (g.cls.getD j 0) 0) := by
  simp only [Grp.chkCls, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_lt, Bool.and_eq_true] at h
  intro j hj hc
  rcases h j hj with h1 | ⟨h1, h2⟩
  · omega
  · exact ⟨h1, setEqC_iff.mp h2⟩

theorem Grp.chkW_spec {w : Wit} (h : g.chkW w = true) :
    w.A < g.inv.length ∧ g.cls.getD w.A 0 < g.m ∧
    isSubC (codes w.K) = true ∧ isSubC (codes w.Q) = true ∧ isSubC (codes w.P) = true ∧
    (codes w.K).Nodup ∧ (codes w.Q).Nodup ∧ (codes w.P).Nodup ∧
    (∀ c ∈ codes w.K, inX g.I c = true) ∧ (∀ c ∈ g.Ec w.A, c ∈ codes w.K) ∧
    (∀ s ∈ g.Sc, commutesAll s (g.Ec w.A) = true → s ∈ codes w.K) ∧
    (0 < (g.Sc.filter (codes w.K).contains).length ∧
      (codes w.K).length % (g.Sc.filter (codes w.K).contains).length = 0 ∧
      (codes w.K).length / (g.Sc.filter (codes w.K).contains).length % 2 = 1) ∧
    (∀ c ∈ codes w.Q, c ∈ g.Sc) ∧ (∀ c ∈ codes w.Q, c ∈ codes w.K) ∧
    (∀ k ∈ codes w.K, ∀ q ∈ codes w.Q, conjC k q ∈ codes w.Q) ∧
    (∀ s ∈ g.Sc, s ∈ codes w.K → s ∉ codes w.Q → ∃ k ∈ codes w.K, conjC (invC k) s ∉ g.Sc) ∧
    (∀ c ∈ codes w.Q, c ∈ codes w.P) ∧ (∀ c ∈ codes w.P, c ∈ codes w.K) ∧
    (∀ k ∈ codes w.K, ∀ x ∈ codes w.P, conjC k x ∈ codes w.P) ∧
    (w.p = 3 ∨ w.p = 5) ∧ (codes w.P).length = (codes w.Q).length * w.p ∧
    (codes w.K).length % (codes w.P).length = 0 ∧
    (∃ b, (codes w.K).length / (codes w.P).length = 2 ^ b) ∧
    (g.Ec w.A).length = 2 * ((g.Ec w.A).filter (codes w.Q).contains).length ∧
    (∀ s ∈ g.Sc, s ∈ codes w.K → ∀ a ∈ g.Ec w.A, commC s a ∈ codes w.Q) ∧
    ∃ x ∈ codes w.P, ∃ a ∈ g.Ec w.A, commC x a ∉ codes w.Q := by
  simp only [Grp.chkW, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun s hs hc => ?_, ⟨h12, h13, h14⟩, h15, h16,
    h17, fun s hs hk hq => ?_, h19, h20, h21, h22, h23, h24, exists_of_isPow2 h25, h26,
    fun s hs hk a ha => ?_, h28⟩
  · rcases h11 s hs with h | h
    · rw [hc] at h
      exact absurd h (by decide)
    · exact h
  · rcases h18 s hs with (h | h) | h
    · exact absurd hk h
    · exact absurd h hq
    · exact h
  · rcases h27 s hs with h | h
    · exact absurd hk h
    · exact h a ha

theorem Grp.inU_iff {u : List Bool} {j : ℕ} :
    g.inU u j = true ↔ g.cls.getD j 0 < g.m ∧ u.getD (g.cls.getD j 0) false = true := by
  simp [Grp.inU]

theorem Grp.letterOK_spec {u : List Bool} {l : ℕ} (h : g.letterOK u l = true) :
    (∃ w ∈ g.wit, g.inU u w.A = true ∧ dc l ∈ codes w.K) ∨
      (inX g.I (dc l) = true ∧ g.normU u (dc l) = true) := by
  simpa [Grp.letterOK] using h

theorem Grp.normU_spec {u : List Bool} {x : List ℕ} (h : g.normU u x = true) :
    ∀ j < g.inv.length, g.inU u j = true → ∃ j' < g.inv.length, g.inU u j' = true ∧
      ∀ d, d ∈ (g.Ec j).map (conjC x) ↔ d ∈ g.Ec j' := by
  simp only [Grp.normU, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, Bool.and_eq_true] at h
  intro j hj hu
  rcases h j hj with h1 | ⟨j', hj', hu', h2⟩
  · rw [hu] at h1
    exact absurd h1 (by decide)
  · exact ⟨j', hj', hu', setEqC_iff.mp h2⟩

theorem exists_of_all_zip' {α β : Type*} (f : α × β → Bool) :
    ∀ (l₁ : List α) (l₂ : List β), (l₁.zip l₂).all f = true → l₁.length = l₂.length →
      ∀ x ∈ l₁, ∃ y ∈ l₂, f (x, y) = true
  | [], _, _, _, x, hx => by simp at hx
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | a :: l₁, b :: l₂, h, hl, x, hx => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, h.1⟩
    · obtain ⟨y, hy, hp⟩ := exists_of_all_zip' f l₁ l₂ h.2 (by simpa using hl) x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hp⟩

theorem mem_allBoolVecs : ∀ {m : ℕ} {v : List Bool}, v ∈ allBoolVecs m ↔ v.length = m
  | 0, v => by cases v <;> simp [allBoolVecs]
  | m + 1, v => by
    rw [allBoolVecs, List.mem_flatMap]
    constructor
    · rintro ⟨w, hw, hv⟩
      rw [mem_allBoolVecs] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl <;> simp [hw]
    · intro hv
      cases v with
      | nil => simp at hv
      | cons b w =>
        refine ⟨w, mem_allBoolVecs.mpr (by simpa using hv), ?_⟩
        cases b <;> simp

theorem Grp.chkWords_spec (h : g.chkWords = true) {u : List Bool} (hu : u.length = g.m) :
    ∀ γ ∈ g.gens, ∃ w : List ℕ, w.foldl (fun acc l => cmul acc (dc l)) cid = γ ∧
      ∀ l ∈ w, g.letterOK u l = true := by
  simp only [Grp.chkWords, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨ws, -, hws⟩ := exists_of_all_zip' _ _ _ hall hlen.symm u (mem_allBoolVecs.mpr hu)
  simp only [Bool.and_eq_true, beq_iff_eq] at hws
  intro γ hγ
  obtain ⟨w, -, hw⟩ := exists_of_all_zip' _ _ _ hws.2 hws.1.symm γ hγ
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hw
  exact ⟨w, hw.1, hw.2⟩

theorem Grp.mem_E {j : ℕ} (hInv : g.chkInv = true) (hj : j < g.inv.length) {x : P10} :
    x ∈ cSub (g.Ec j) ↔ code x ∈ g.Ec j :=
  mem_cSub ((g.chkInv_spec hInv).1 j hj).1

theorem Grp.card_E {j : ℕ} (hInv : g.chkInv = true) (hj : j < g.inv.length) :
    Nat.card (cSub (g.Ec j)) = (g.Ec j).length := by
  obtain ⟨h1, h2, -⟩ := (g.chkInv_spec hInv).1 j hj
  refine card_cSub h1 h2 ?_
  rw [g.Ec_eq hj]
  exact codes_realized _

theorem Grp.exhaustive (hS : isSubC g.Sc = true) (hInv : g.chkInv = true)
    (hClose : g.chkClose = true) {A : Subgroup P10} (hAS : A ≤ cSub g.Sc)
    (hA : IsElemAbelian 2 A) : ∃ j < g.inv.length, ∀ x, x ∈ A ↔ code x ∈ g.Ec j := by
  obtain ⟨-, ⟨j₀, hj₀, h0⟩, -⟩ := g.chkInv_spec hInv
  have hclose := g.chkClose_spec hClose
  have hreal : ∀ j < g.inv.length, ∀ e ∈ g.Ec j, ∃ y : P10, code y = e := fun j hj e he => by
    rw [g.Ec_eq hj] at he
    exact codes_realized _ e he
  suffices H : ∀ n, ∀ j < g.inv.length, (∀ x, code x ∈ g.Ec j → x ∈ A) →
      Nat.card A - (g.Ec j).length ≤ n → ∃ j' < g.inv.length, ∀ x, x ∈ A ↔ code x ∈ g.Ec j' by
    refine H _ j₀ hj₀ (fun x hx => ?_) le_rfl
    have : code x = code 1 := by rw [code_one]; exact (h0 _).mp hx
    rw [code_injective this]
    exact A.one_mem
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hj hEA hn
  by_cases hall : ∀ x ∈ A, code x ∈ g.Ec j
  · exact ⟨j, hj, fun x => ⟨hall x, hEA x⟩⟩
  push Not at hall
  obtain ⟨c, hcA, hcE⟩ := hall
  have hcS : code c ∈ g.Sc := (mem_cSub hS).mp (hAS hcA)
  have hcc : cmul (code c) (code c) = cid := by
    rw [← code_mul, ← code_one, ← pow_two]
    exact congrArg code (hA.2 c hcA)
  have hcomm : commutesAll (code c) (g.Ec j) = true := commutesAll_iff.mpr fun e he => by
    obtain ⟨y, rfl⟩ := hreal j hj e he
    have hy : y ∈ A := hEA y he
    rw [← code_mul, ← code_mul]
    congr 1
    have := hA.1.is_comm.comm ⟨c, hcA⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  obtain ⟨j', hj', hF⟩ := hclose j hj (code c) hcS hcE hcc hcomm
  have hE'A : ∀ x, code x ∈ g.Ec j' → x ∈ A := by
    intro x hx
    rcases List.mem_append.mp ((hF _).mp hx) with h1 | h1
    · exact hEA x h1
    · obtain ⟨e, he, hxe⟩ := List.mem_map.mp h1
      obtain ⟨y, rfl⟩ := hreal j hj e he
      have : x = c * y := code_injective (by rw [code_mul]; exact hxe.symm)
      rw [this]
      exact A.mul_mem hcA (hEA y he)
  have hsub : cSub (g.Ec j) < cSub (g.Ec j') := by
    refine lt_of_le_of_ne (fun x hx => ?_) fun heq => hcE ?_
    · rw [g.mem_E hInv hj] at hx
      rw [g.mem_E hInv hj']
      exact (hF _).mpr (List.mem_append_left _ hx)
    · have hc' : c ∈ cSub (g.Ec j') := by
        rw [g.mem_E hInv hj']
        refine (hF _).mpr (List.mem_append_right _ (List.mem_map.mpr ⟨cid, ?_, ?_⟩))
        · obtain ⟨h1, -, -⟩ := (g.chkInv_spec hInv).1 j hj
          exact (isSubC_spec h1).1
        · rw [← code_one, ← code_mul, mul_one]
      rw [← heq, g.mem_E hInv hj] at hc'
      exact hc'
  have hlt := Subgroup.card_lt_of_lt hsub
  rw [g.card_E hInv hj, g.card_E hInv hj'] at hlt
  have hle : (g.Ec j').length ≤ Nat.card A := by
    rw [← g.card_E hInv hj']
    exact Subgroup.card_le_of_le fun x hx => hE'A x ((g.mem_E hInv hj').mp hx)
  exact ih (Nat.card A - (g.Ec j').length) (by omega) j' hj' hE'A le_rfl

theorem Grp.typeOne {X : Subgroup P10} (hpsl : A6Models.psl29 ≤ X)
    (hI : ∀ i ∈ g.I, A6EOne.rep i ∈ X) (hS : g.chkS = true) (hInv : g.chkInv = true) {w : Wit}
    (hw : g.chkW w = true) :
    E1TypeOne X (cSub g.Sc) (cSub (g.Ec w.A)) (cSub (codes w.K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hA, -, hK, hQ, hP, hKn, hQn, hPn, hKX, hAK, hCK, ⟨hsk0, hskd, hsko⟩, hQS, hQK, hQnorm,
    hcore, hQP, hPK, hPnorm, hp, hPcard, hKPd, ⟨b, hb⟩, hAQ, hcomm, ⟨x₀, hx₀, a₀, ha₀, hc₀⟩⟩ :=
    g.chkW_spec hw
  obtain ⟨hSsub, hSn, -, -, ⟨bS, hbS⟩⟩ := g.chkS_spec hS
  obtain ⟨hAsub, hAn, -⟩ := (g.chkInv_spec hInv).1 w.A hA
  have hrealA : ∀ c ∈ g.Ec w.A, ∃ y : P10, code y = c := by
    rw [g.Ec_eq hA]
    exact codes_realized _
  have hrealS : ∀ c ∈ g.Sc, ∃ y : P10, code y = c := codes_realized _
  set S := cSub g.Sc with hSdef
  set A := cSub (g.Ec w.A) with hAdef
  set K := cSub (codes w.K) with hKdef
  set Q := cSub (codes w.Q) with hQdef
  set P := cSub (codes w.P) with hPdef
  have mS : ∀ x, x ∈ S ↔ code x ∈ g.Sc := fun x => mem_cSub hSsub
  have mA : ∀ x, x ∈ A ↔ code x ∈ g.Ec w.A := fun x => mem_cSub hAsub
  have mK : ∀ x, x ∈ K ↔ code x ∈ codes w.K := fun x => mem_cSub hK
  have mQ : ∀ x, x ∈ Q ↔ code x ∈ codes w.Q := fun x => mem_cSub hQ
  have mP : ∀ x, x ∈ P ↔ code x ∈ codes w.P := fun x => mem_cSub hP
  have cS : Nat.card S = g.Sc.length := card_cSub hSsub hSn hrealS
  have cK : Nat.card K = (codes w.K).length := card_cSub hK hKn (codes_realized _)
  have cQ : Nat.card Q = (codes w.Q).length := card_cSub hQ hQn (codes_realized _)
  have cP : Nat.card P = (codes w.P).length := card_cSub hP hPn (codes_realized _)
  have cA : Nat.card A = (g.Ec w.A).length := card_cSub hAsub hAn hrealA
  have cSK : Nat.card (S ⊓ K : Subgroup P10) = (g.Sc.filter (codes w.K).contains).length := by
    refine card_eq_length (hSn.filter _) (fun x => ?_) fun c hc =>
      hrealS c (List.mem_filter.mp hc).1
    rw [mem_inf, mS, mK, List.mem_filter, List.contains_eq_mem, decide_eq_true_eq]
  have cAQ : Nat.card (A ⊓ Q : Subgroup P10) =
      ((g.Ec w.A).filter (codes w.Q).contains).length := by
    refine card_eq_length (hAn.filter _) (fun x => ?_) fun c hc =>
      hrealA c (List.mem_filter.mp hc).1
    rw [mem_inf, mA, mQ, List.mem_filter, List.contains_eq_mem, decide_eq_true_eq]
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (cS.trans hbS)
  have hQK' : Q ≤ K := fun x hx => (mK x).mpr (hQK _ ((mQ x).mp hx))
  have hQS' : Q ≤ S := fun x hx => (mS x).mpr (hQS _ ((mQ x).mp hx))
  have hQP' : Q ≤ P := fun x hx => (mP x).mpr (hQP _ ((mQ x).mp hx))
  have hPK' : P ≤ K := fun x hx => (mK x).mpr (hPK _ ((mP x).mp hx))
  have hAK' : A ≤ K := fun x hx => (mK x).mpr (hAK _ ((mA x).mp hx))
  have hQnormal : (Q.subgroupOf K).Normal := (normal_subgroupOf_iff hQK').mpr fun q k hq hk => by
    rw [mQ, code_conj]
    exact hQnorm _ ((mK k).mp hk) _ ((mQ q).mp hq)
  have hPnormal : (P.subgroupOf K).Normal := (normal_subgroupOf_iff hPK').mpr fun x k hx hk => by
    rw [mP, code_conj]
    exact hPnorm _ ((mK k).mp hk) _ ((mP x).mp hx)
  have hsyl : IsSylowIn 2 (S ⊓ K) K := by
    refine ⟨inf_le_right, hS2.to_le inf_le_left, ?_⟩
    have h1 := Subgroup.relIndex_mul_card (S ⊓ K) K
    rw [inf_of_le_left inf_le_right, cK, cSK] at h1
    have h2 : (S ⊓ K).relIndex K =
        (codes w.K).length / (g.Sc.filter (codes w.K).contains).length := by
      rw [← h1, Nat.mul_div_cancel _ hsk0]
    rw [h2]
    omega
  have hcoreeq : pCoreOf 2 K = Q := by
    apply le_antisymm
    · intro x hx
      have hxSK : x ∈ S ⊓ K := (pCoreOf_le_of_isSylowIn hsyl) hx
      by_contra hxQ
      obtain ⟨kc, hkc, hkS⟩ := hcore _ ((mS x).mp (mem_inf.mp hxSK).1)
        ((mK x).mp (mem_inf.mp hxSK).2) fun h => hxQ ((mQ x).mpr h)
      obtain ⟨k, rfl⟩ := codes_realized _ kc hkc
      have hkK : k ∈ K := (mK k).mpr hkc
      have h1 : k⁻¹ * x * k⁻¹⁻¹ ∈ pCoreOf 2 K :=
        (mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (K.inv_mem hkK))
          x).mp hx
      have h2 := (mem_inf.mp ((pCoreOf_le_of_isSylowIn hsyl) h1)).1
      rw [mS, code_conj, code_inv] at h2
      exact hkS h2
    · exact CFSG.LieType.BorelTits.le_pCoreOf 2 hQK' hQnormal (hS2.to_le hQS')
  have hpp : w.p.Prime := by rcases hp with h | h <;> rw [h] <;> norm_num
  have hPA : ⁅P, A⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro u hu a ha
    rw [commutatorElement_def]
    have h1 : a * u⁻¹ * a⁻¹ ∈ P := by
      rw [mP, code_conj]
      exact hPnorm _ ((mK a).mp (hAK' ha)) _ ((mP _).mp (P.inv_mem hu))
    have := P.mul_mem hu h1
    simpa [mul_assoc] using this
  have hPeq : P = Q ⊔ ⁅P, A⁆ := by
    obtain ⟨u₀, rfl⟩ := codes_realized _ x₀ hx₀
    obtain ⟨b₀, rfl⟩ := hrealA a₀ ha₀
    have hMP : Q ⊔ ⁅P, A⁆ ≤ P := sup_le hQP' hPA
    have hcM : ⁅u₀, b₀⁆ ∈ Q ⊔ ⁅P, A⁆ :=
      le_sup_right (a := Q) (Subgroup.commutator_mem_commutator ((mP u₀).mpr hx₀) ((mA b₀).mpr ha₀))
    have hcQ : ⁅u₀, b₀⁆ ∉ Q := by
      rw [mQ, code_commutator]
      exact hc₀
    have hlt := Subgroup.card_lt_of_lt (lt_of_le_of_ne (le_sup_left : Q ≤ Q ⊔ ⁅P, A⁆)
      fun h => hcQ (h ▸ hcM))
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : Q ≤ Q ⊔ ⁅P, A⁆)
    obtain ⟨k', hk'⟩ := Subgroup.card_dvd_of_le hMP
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have hPQ : Nat.card P = Nat.card Q * w.p := by rw [cP, cQ, hPcard]
    have hkk : k * k' = w.p := by
      rw [hk, mul_assoc] at hk'
      rw [hPQ] at hk'
      exact (Nat.eq_of_mul_eq_mul_left hQpos hk').symm
    have hk1 : k ≠ 1 := fun h => by rw [h, mul_one] at hk; omega
    rcases (Nat.dvd_prime hpp).mp ⟨k', hkk.symm⟩ with h | h
    · exact absurd h hk1
    · refine (Subgroup.eq_of_le_of_card_ge hMP ?_).symm
      rw [hk, h, hPQ]
  refine ⟨fun x hx => mem_of_inX hpsl hI (hKX _ ((mK x).mp hx)), hAK', fun x hx => ?_, hsyl,
    ⟨P, w.p, hp, hcoreeq ▸ hQP', hPK', hPnormal, by rw [cP, hcoreeq, cQ, hPcard], ⟨b, ?_⟩,
      hcoreeq ▸ hPeq⟩, by rw [cA, hcoreeq, cAQ, hAQ], ?_⟩
  · obtain ⟨hxS, hxC⟩ := mem_inf.mp hx
    rw [mK]
    refine hCK _ ((mS x).mp hxS) (commutesAll_iff.mpr fun e he => ?_)
    obtain ⟨y, rfl⟩ := hrealA e he
    rw [← code_mul, ← code_mul]
    exact congrArg code (mem_centralizer_iff.mp hxC y ((mA y).mpr he)).symm
  · rw [cK, cP, ← hb, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hKPd)]
  · rw [hcoreeq, Subgroup.commutator_le]
    intro s hs a ha
    rw [mQ, code_commutator]
    exact hcomm _ ((mS s).mp (mem_inf.mp hs).1) ((mK s).mp (mem_inf.mp hs).2) _ ((mA a).mp ha)

theorem length_xList (I : List ℕ) : (xList I).length = 360 * I.length := by
  simp only [xList, List.length_flatMap, List.length_map, Core.psl_length, List.map_const',
    List.sum_replicate, smul_eq_mul]
  ring

theorem Grp.eOne (hg : g.check = true) {X : Subgroup P10} (hpsl : A6Models.psl29 ≤ X)
    (haut : X ≤ A6Models.autA6) (hI : ∀ i < 4, A6EOne.rep i ∈ X ↔ i ∈ g.I)
    (hI4 : ∀ i ∈ g.I, i < 4) :
    IsSylowIn 2 (cSub g.Sc) X ∧ ∀ Ω : Set (Subgroup P10), E1.IsInvColl X Ω →
      ∃ F : Set (Subgroup P10 × Subgroup P10),
        (∀ AK ∈ F, AK.1 ∈ Ω ∧ AK.1 ≤ cSub g.Sc ∧ E1TypeOne X (cSub g.Sc) AK.1 AK.2) ∧
          (⨆ AK ∈ F, AK.2) ⊔ (X ⊓ normalizer (E1.weakClosure (cSub g.Sc) Ω : Set P10)) = X := by
  classical
  obtain ⟨hX, hS, hInv, hClose, hCls, hWit, hWords⟩ := g.check_spec hg
  obtain ⟨hSsub, hSn, hSX, hSlen, ⟨bS, hbS⟩⟩ := g.chkS_spec hS
  have hIX : ∀ i ∈ g.I, A6EOne.rep i ∈ X := fun i hi => (hI i (hI4 i hi)).mpr hi
  have memX : ∀ x, inX g.I (code x) = true → x ∈ X := fun x h => mem_of_inX hpsl hIX h
  set S := cSub g.Sc with hSdef
  have mS : ∀ x, x ∈ S ↔ code x ∈ g.Sc := fun x => mem_cSub hSsub
  have hSX' : S ≤ X := fun x hx => memX x (hSX _ ((mS x).mp hx))
  have cS : Nat.card S = g.Sc.length := card_cSub hSsub hSn (codes_realized _)
  have hnd : (xList g.I).Nodup := by simpa [Grp.chkX] using hX
  have cX : Nat.card X = 360 * g.I.length := by
    rw [card_eq_xList hpsl haut hI hI4 hnd, length_xList]
  have hsyl : IsSylowIn 2 S X := by
    refine ⟨hSX', IsPGroup.of_card (cS.trans hbS), ?_⟩
    have h1 := Subgroup.relIndex_mul_card S X
    rw [inf_of_le_left hSX', cX, cS, hSlen] at h1
    have hI0 : 0 < g.I.length := by
      have h0 : (0 : ℕ) ∈ g.I := (hI 0 (by norm_num)).mp (by
        rw [A6EOne.rep, show autRepsP.getD 0 1 = 1 from rfl]
        exact X.one_mem)
      exact List.length_pos_of_mem h0
    have h2 : S.relIndex X = 45 := by
      have h3 : S.relIndex X * (8 * g.I.length) = 45 * (8 * g.I.length) := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_right (by omega) h3
    rw [h2]
    norm_num
  refine ⟨hsyl, fun Ω hΩ => ?_⟩
  obtain ⟨hEsub, -, hElen⟩ := g.chkInv_spec hInv
  have hcls := g.chkCls_spec hCls
  set u : List Bool := (List.range g.m).map fun c => decide (cSub (g.Ec (g.rep.getD c 0)) ∈ Ω)
    with hudef
  have hulen : u.length = g.m := by simp [hudef]
  have huc : ∀ c < g.m, u.getD c false = true ↔ cSub (g.Ec (g.rep.getD c 0)) ∈ Ω := by
    intro c hc
    simp [hudef, List.getD_eq_getElem?_getD, hc]
  have hconj : ∀ j < g.inv.length, g.cls.getD j 0 < g.m → ∃ γ ∈ X,
      A1b.conjSub γ (cSub (g.Ec j)) = cSub (g.Ec (g.rep.getD (g.cls.getD j 0) 0)) := by
    intro j hj hc
    obtain ⟨hinX, hset⟩ := hcls j hj hc
    set r := g.rep.getD (g.cls.getD j 0) 0 with hr
    set γ := el (g.cj.getD j 0) with hγ
    have hγc : code γ = dc (g.cj.getD j 0) := code_el _
    have hrlen : r < g.inv.length := by
      by_contra hrl
      have h1 : conjC (dc (g.cj.getD j 0)) cid ∈ g.Ec r :=
        (hset _).mp (List.mem_map.mpr ⟨cid, (isSubC_spec (hEsub j hj).1).1, rfl⟩)
      rw [Grp.Ec, List.getD_eq_default _ _ (not_lt.mp hrl)] at h1
      simp [codes] at h1
    refine ⟨γ, memX γ (hγc ▸ hinX), ?_⟩
    ext x
    rw [A1b.mem_conjSub_iff, g.mem_E hInv hj, g.mem_E hInv hrlen]
    constructor
    · intro hx
      refine (hset _).mp (List.mem_map.mpr ⟨_, hx, ?_⟩)
      rw [← hγc, ← code_conj]
      congr 1
      group
    · intro hx
      obtain ⟨e, he, hxe⟩ := List.mem_map.mp ((hset _).mpr hx)
      have hreal : ∃ y : P10, code y = e := by
        rw [g.Ec_eq hj] at he
        exact codes_realized _ e he
      obtain ⟨y, rfl⟩ := hreal
      rw [← hγc, ← code_conj] at hxe
      rw [← code_injective hxe]
      have : γ⁻¹ * (γ * y * γ⁻¹) * γ = y := by group
      rw [this]
      exact he
  have hΩ1 : ∀ j < g.inv.length, g.inU u j = true → cSub (g.Ec j) ∈ Ω := by
    intro j hj hu
    obtain ⟨hc, hc'⟩ := g.inU_iff.mp hu
    obtain ⟨γ, hγ, hγE⟩ := hconj j hj hc
    have h1 := hΩ.conj _ ((huc _ hc).mp hc') γ⁻¹ (X.inv_mem hγ)
    rwa [← hγE, ← A1b.conjSub_mul, inv_mul_cancel, show A1b.conjSub (1 : P10) (cSub (g.Ec j)) =
      cSub (g.Ec j) from by ext; simp [A1b.mem_conjSub_iff]] at h1
  have hES : ∀ j < g.inv.length, cSub (g.Ec j) ≤ S := fun j hj x hx =>
    (mS x).mpr ((hEsub j hj).2.2 _ ((g.mem_E hInv hj).mp hx))
  have hΩS : ∀ A ∈ Ω, A ≤ S → A = ⊥ ∨ ∃ j < g.inv.length, g.inU u j = true ∧ A = cSub (g.Ec j) := by
    intro A hA hAS
    by_cases hbot : A = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨j, hj, hjA⟩ := g.exhaustive hSsub hInv hClose hAS (hΩ.isElemAbelian A hA)
    have hAE : A = cSub (g.Ec j) := by
      ext x
      rw [hjA, g.mem_E hInv hj]
    have hcard : 2 ≤ (g.Ec j).length := by
      have h1 : Nat.card A ≠ 1 := fun h => hbot (Subgroup.eq_bot_of_card_eq A h)
      have h3 : 0 < Nat.card A := Nat.card_pos
      rw [hAE, g.card_E hInv hj] at h1 h3
      omega
    have hc : g.cls.getD j 0 < g.m := by
      rcases hElen j hj with h | h
      · omega
      · exact h
    obtain ⟨γ, hγ, hγE⟩ := hconj j hj hc
    have h1 := hΩ.conj A hA γ hγ
    rw [hAE, hγE] at h1
    exact ⟨j, hj, g.inU_iff.mpr ⟨hc, (huc _ hc).mpr h1⟩, hAE⟩
  have hnorm : ∀ x : P10, inX g.I (code x) = true → g.normU u (code x) = true →
      x ∈ X ⊓ normalizer (E1.weakClosure S Ω : Set P10) := by
    intro x hxX hxN
    refine mem_inf.mpr ⟨memX x hxX, mem_normalizer_of_conj_le fun w hw => ?_⟩
    have hle : E1.weakClosure S Ω ≤
        (E1.weakClosure S Ω).comap (MulAut.conj x).toMonoidHom := by
      refine iSup₂_le fun A hA => iSup_le fun hAS => fun a ha => ?_
      show x * a * x⁻¹ ∈ E1.weakClosure S Ω
      rcases hΩS A hA hAS with rfl | ⟨j, hj, hju, rfl⟩
      · rw [mem_bot.mp ha, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · obtain ⟨j', hj', hj'u, hset⟩ := g.normU_spec hxN j hj hju
        have h1 : x * a * x⁻¹ ∈ cSub (g.Ec j') := by
          rw [g.mem_E hInv hj', ← hset, code_conj]
          exact List.mem_map_of_mem ((g.mem_E hInv hj).mp ha)
        have hEW : cSub (g.Ec j') ≤ E1.weakClosure S Ω := by
          unfold E1.weakClosure
          exact le_iSup₂_of_le (cSub (g.Ec j')) (hΩ1 j' hj' hj'u)
            (le_iSup_of_le (hES j' hj') le_rfl)
        exact hEW h1
    exact hle hw
  have hWit' : ∀ w ∈ g.wit, g.chkW w = true := by
    simpa [Grp.chkWit, List.all_eq_true] using hWit
  set F : Set (Subgroup P10 × Subgroup P10) := {AK | ∃ w ∈ g.wit, g.inU u w.A = true ∧
    AK = (cSub (g.Ec w.A), cSub (codes w.K))} with hFdef
  have hKF : ∀ w ∈ g.wit, g.inU u w.A = true → cSub (codes w.K) ≤ ⨆ AK ∈ F, AK.2 :=
    fun w hw hwu => le_iSup₂_of_le (cSub (g.Ec w.A), cSub (codes w.K)) ⟨w, hw, hwu, rfl⟩ le_rfl
  refine ⟨F, ?_, ?_⟩
  · rintro AK ⟨w, hw, hwu, rfl⟩
    have hwc := hWit' w hw
    have hwA := (g.chkW_spec hwc).1
    exact ⟨hΩ1 _ hwA hwu, hES _ hwA, g.typeOne hpsl hIX hS hInv hwc⟩
  apply le_antisymm
  · refine sup_le (iSup₂_le fun AK hAK => ?_) inf_le_left
    obtain ⟨w, hw, -, rfl⟩ := hAK
    exact (g.typeOne hpsl hIX hS hInv (hWit' w hw)).le
  have hletter : ∀ l, g.letterOK u l = true →
      el l ∈ (⨆ AK ∈ F, AK.2) ⊔ (X ⊓ normalizer (E1.weakClosure S Ω : Set P10)) := by
    intro l hl
    rcases g.letterOK_spec hl with ⟨w, hw, hwu, hlK⟩ | ⟨hlX, hlN⟩
    · have h1 : el l ∈ cSub (codes w.K) := by
        rw [mem_cSub (g.chkW_spec (hWit' w hw)).2.2.1, code_el]
        exact hlK
      exact Subgroup.mem_sup_left (hKF w hw hwu h1)
    · refine Subgroup.mem_sup_right (hnorm (el l) ?_ ?_)
      · rw [code_el]
        exact hlX
      · rw [code_el]
        exact hlN
  have hgen : ∀ γ : P10, code γ ∈ g.gens →
      γ ∈ (⨆ AK ∈ F, AK.2) ⊔ (X ⊓ normalizer (E1.weakClosure S Ω : Set P10)) := by
    intro γ hγ
    obtain ⟨w, hw, hwl⟩ := g.chkWords_spec hWords hulen _ hγ
    rw [← code_one, foldl_cmul_code, one_mul] at hw
    rw [← code_injective hw]
    refine Subgroup.list_prod_mem _ ?_
    intro y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
    exact hletter l (hwl l hl)
  intro x hx
  obtain ⟨r, hr, hxr⟩ := (mem_autA6_iff_exists x).mp (haut hx)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hri : autRepsP[i] = A6EOne.rep i := by rw [A6EOne.rep, List.getD_eq_getElem]
  rw [hri] at hxr
  have hi4 : i < 4 := by simpa [autRepsP] using hi
  have hrX : A6EOne.rep i ∈ X := by
    have := X.mul_mem (X.inv_mem (hpsl hxr)) hx
    rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
  have hx' : x = x * (A6EOne.rep i)⁻¹ * A6EOne.rep i := by group
  rw [hx']
  refine Subgroup.mul_mem _ ?_ ?_
  ·
    rw [psl29_eq] at hxr
    refine (Subgroup.closure_le _).mpr (fun y hy => hgen y ?_) hxr
    rw [Grp.gens, List.mem_append]
    left
    rw [← pslGens_code]
    exact List.mem_map_of_mem hy
  · by_cases hi0 : i = 0
    · subst hi0
      exact Subgroup.one_mem _
    · refine hgen _ ?_
      rw [Grp.gens, List.mem_append]
      right
      refine List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨(hI i hi4).mp hrX, by simpa using hi0⟩, ?_⟩
      rw [code_rep]

end Grp

theorem rep_mem_of_mul {X : Subgroup P10} (hpsl : A6Models.psl29 ≤ X) {i j k : ℕ}
    (h : pslLit.contains (cmul (cmul (autReps.getD i cid) (autReps.getD j cid))
      (autRepsInv.getD k cid)) = true) (hi : rep i ∈ X) (hj : rep j ∈ X) : rep k ∈ X := by
  have h1 : rep i * rep j * (rep k)⁻¹ ∈ A6Models.psl29 := by
    rw [mem_psl29_iff, code_mul, code_mul, code_rep, code_rep, code_rep_inv]
    simpa using h
  have h2 := X.mul_mem (X.inv_mem (hpsl h1)) (X.mul_mem hi hj)
  have h3 : (rep i * rep j * (rep k)⁻¹)⁻¹ * (rep i * rep j) = rep k := by group
  rwa [h3] at h2

theorem a6_eOne_concrete {X : Subgroup P10}
    (hpsl : A6Models.psl29 ≤ X) (haut : X ≤ A6Models.autA6) :
    ∃ S : Subgroup P10, IsSylowIn 2 S X ∧ ∀ Ω : Set (Subgroup P10), E1.IsInvColl X Ω →
      ∃ F : Set (Subgroup P10 × Subgroup P10),
        (∀ AK ∈ F, AK.1 ∈ Ω ∧ AK.1 ≤ S ∧ E1TypeOne X S AK.1 AK.2) ∧
          (⨆ AK ∈ F, AK.2) ⊔ (X ⊓ normalizer (E1.weakClosure S Ω : Set P10)) = X := by
  have hc := checkAll_spec
  simp only [checkAll, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hcos, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  simp only [cosetOK, Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] at hcos
  obtain ⟨-, h123, h213, h132, h312, h231, h321⟩ := hcos
  have hr0 : rep 0 ∈ X := by
    rw [rep, show autRepsP.getD 0 1 = 1 from rfl]
    exact X.one_mem
  have key : ∀ g : Grp, g.check = true → (∀ i < 4, rep i ∈ X ↔ i ∈ g.I) →
      (∀ i ∈ g.I, i < 4) → ∃ S : Subgroup P10, IsSylowIn 2 S X ∧ ∀ Ω : Set (Subgroup P10),
        E1.IsInvColl X Ω → ∃ F : Set (Subgroup P10 × Subgroup P10),
          (∀ AK ∈ F, AK.1 ∈ Ω ∧ AK.1 ≤ S ∧ E1TypeOne X S AK.1 AK.2) ∧
            (⨆ AK ∈ F, AK.2) ⊔ (X ⊓ normalizer (E1.weakClosure S Ω : Set P10)) = X :=
    fun g hg hI hI4 => ⟨cSub g.Sc, (g.eOne hg hpsl haut hI hI4).1, (g.eOne hg hpsl haut hI hI4).2⟩
  have hI0 : grp0.I = [0] := rfl
  have hI1 : grp1.I = [0, 1] := rfl
  have hI2 : grp2.I = [0, 2] := rfl
  have hI3 : grp3.I = [0, 3] := rfl
  have hI4 : grp4.I = [0, 1, 2, 3] := rfl
  by_cases b1 : rep 1 ∈ X <;> by_cases b2 : rep 2 ∈ X <;> by_cases b3 : rep 3 ∈ X
  · refine key grp4 h4 (fun i hi => ?_) (by rw [hI4]; decide)
    rw [hI4]
    interval_cases i <;> simp [hr0, b1, b2, b3]
  · exact absurd (rep_mem_of_mul hpsl h123 b1 b2) b3
  · exact absurd (rep_mem_of_mul hpsl h132 b1 b3) b2
  · refine key grp1 h1 (fun i hi => ?_) (by rw [hI1]; decide)
    rw [hI1]
    interval_cases i <;> simp [hr0, b1, b2, b3]
  · exact absurd (rep_mem_of_mul hpsl h231 b2 b3) b1
  · refine key grp2 h2 (fun i hi => ?_) (by rw [hI2]; decide)
    rw [hI2]
    interval_cases i <;> simp [hr0, b1, b2, b3]
  · refine key grp3 h3 (fun i hi => ?_) (by rw [hI3]; decide)
    rw [hI3]
    interval_cases i <;> simp [hr0, b1, b2, b3]
  · refine key grp0 h0 (fun i hi => ?_) (by rw [hI0]; decide)
    rw [hI0]
    interval_cases i <;> simp [hr0, b1, b2, b3]

end CFSG.Quasithin.H13.A6EOne
