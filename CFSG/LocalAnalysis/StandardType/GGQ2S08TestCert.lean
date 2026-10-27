module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestLin
public import Mathlib.Data.List.GetD
public import Mathlib.LinearAlgebra.StdBasis

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {n : ℕ}

@[expose] def letApp (l : Vn n × Vn n) (v : Vn n) : Vn n := v - (l.2 ⬝ᵥ v) • l.1

@[expose] def letAt (alph : List (Vn n × Vn n)) (i : ℕ) : Vn n × Vn n := alph.getD i (0, 0)

@[expose] def wEval (alph : List (Vn n × Vn n)) (w : List ℕ) (v : Vn n) : Vn n :=
  w.foldr (fun i u => letApp (letAt alph i) u) v

@[expose] def wDual (alph : List (Vn n × Vn n)) (m : List ℕ) (a : Vn n) : Vn n :=
  fun j => a ⬝ᵥ wEval alph m.reverse (Pi.single j 1)

@[expose] def wConj (alph : List (Vn n × Vn n)) (m : List ℕ) (l : Vn n × Vn n) : Vn n × Vn n :=
  (wEval alph m l.1, wDual alph m l.2)

@[expose] def sameRefl (l l' : Vn n × Vn n) : Bool :=
  decide (l' = l) || decide (l' = ((2 : ZMod 3) • l.1, (2 : ZMod 3) • l.2))

@[expose] def symB (l l' : Vn n × Vn n) : Bool :=
  decide ((l.2 ⬝ᵥ l'.1 = 0) ↔ (l'.2 ⬝ᵥ l.1 = 0))

@[expose] def pmB (x y : Vn n) : Bool := decide (y = x) || decide (y = -x)

inductive PatV (n : ℕ) where
  | symw (m : List ℕ) (k : ℕ)
  | excl (h : List ℕ) (k si : ℕ) (v : Vn n)
  | tv (T : List ℕ) (c a : Vn n)
  | cls (m : List ℕ) (ri : ℕ)

inductive S2V (n : ℕ) where
  | inn (m : List ℕ)
  | sym (m : List ℕ)
  | orb (m : List ℕ)
  | excl (h : List ℕ) (k si : ℕ) (v : Vn n)
  | stab (segs : List (List ℕ))

@[expose] def exclB (alph gens : List (Vn n × Vn n)) (sets : List (List (Vn n))) (x₀ : Vn n)
    (h : List ℕ) (k si : ℕ) (v : Vn n) : Bool :=
  pmB x₀ (wEval alph h x₀) && decide (k < gens.length) && decide (v ∈ sets.getD si []) &&
    !decide (wEval alph h (letApp (letAt gens k) (wEval alph h.reverse v)) ∈ sets.getD si [])

@[expose] def tvB (alph : List (Vn n × Vn n)) (T : List ℕ) (c a : Vn n) : Bool :=
  decide (c ≠ 0) && decide (a ≠ 0) && decide (a ⬝ᵥ c = 0) &&
    (List.finRange n).all fun j =>
      decide (wEval alph T (Pi.single j 1) = Pi.single j 1 + (a ⬝ᵥ Pi.single j 1) • c)

@[expose] def patB (gens : List (Vn n × Vn n)) (sets : List (List (Vn n))) (x₀ : Vn n)
    (reps : List (Vn n × Vn n)) (p : (Vn n × Vn n) × PatV n) : Bool :=
  decide (p.1.2 ⬝ᵥ p.1.1 = 2) &&
    match p.2 with
    | .symw m k => decide (k < gens.length) && !symB p.1 (wConj gens m (letAt gens k))
    | .excl h k si v => exclB (gens ++ [p.1]) gens sets x₀ h k si v
    | .tv T c a => tvB (gens ++ [p.1]) T c a
    | .cls m ri => decide (ri < reps.length) && sameRefl (wConj gens m p.1) (letAt reps ri)

@[expose] def s2B (gens : List (Vn n × Vn n)) (sets : List (List (Vn n))) (x₀ : Vn n)
    (reps : List (Vn n × Vn n)) (i j : ℕ) : S2V n → Bool
  | .inn m => sameRefl (wConj gens m (letAt reps i)) (letAt reps j)
  | .sym m => !symB (letAt reps j) (wConj gens m (letAt reps i))
  | .orb m => pmB (letApp (letAt reps j) x₀) (wEval (gens ++ [letAt reps i]) m x₀)
  | .excl h k si v => exclB (gens ++ [letAt reps i, letAt reps j]) gens sets x₀ h k si v
  | .stab segs => (segs.all fun s => s.all (fun l => decide (l ≤ gens.length)) ||
        pmB x₀ (wEval (gens ++ [letAt reps i, letAt reps j]) s x₀)) &&
      pmB (letApp (letAt reps j) x₀) (wEval (gens ++ [letAt reps i, letAt reps j]) segs.flatten x₀)

@[expose] def certOK (gens : List (Vn n × Vn n)) (x₀ : Vn n) (sets : List (List (Vn n)))
    (pats : List ((Vn n × Vn n) × PatV n)) (reps : List (Vn n × Vn n)) (s2 : List (S2V n)) :
    Bool :=
  gens.all (fun l => decide (l.2 ⬝ᵥ l.1 = 2)) && reps.all (fun l => decide (l.2 ⬝ᵥ l.1 = 2)) &&
    sets.all (fun S => gens.all fun g => S.all fun v => decide (letApp g v ∈ S)) &&
    pats.all (patB gens sets x₀ reps) &&
    (List.range reps.length).all fun i => (List.range reps.length).all fun j =>
      s2B gens sets x₀ reps i j (s2.getD (i * reps.length + j) (.sym []))

@[expose] def letLin (l : Vn n × Vn n) : Vn n ≃ₗ[ZMod 3] Vn n :=
  if h : l.2 ⬝ᵥ l.1 = 2 then refl l.1 l.2 h else 1

@[expose] def wLin (alph : List (Vn n × Vn n)) (w : List ℕ) : Vn n ≃ₗ[ZMod 3] Vn n :=
  (w.map fun i => letLin (letAt alph i)).prod

@[expose] def AlphOK (alph : List (Vn n × Vn n)) : Prop := ∀ l ∈ alph, l.2 ⬝ᵥ l.1 = 2

theorem letLin_of (l : Vn n × Vn n) (h : l.2 ⬝ᵥ l.1 = 2) : letLin l = refl l.1 l.2 h :=
  dif_pos h

theorem letLin_zero : letLin ((0 : Vn n), (0 : Vn n)) = 1 :=
  dif_neg (by rw [dotProduct_zero]; decide)

theorem letLin_mul_self (l : Vn n × Vn n) : letLin l * letLin l = 1 := by
  unfold letLin
  split_ifs with h
  · exact refl_mul_self l.1 l.2 h
  · exact mul_one 1

theorem letLin_inv (l : Vn n × Vn n) : (letLin l)⁻¹ = letLin l :=
  inv_eq_of_mul_eq_one_right (letLin_mul_self l)

theorem letAt_cases (alph : List (Vn n × Vn n)) (i : ℕ) :
    letAt alph i ∈ alph ∨ letAt alph i = (0, 0) := by
  unfold letAt
  by_cases hi : i < alph.length
  · left
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · right
    exact List.getD_eq_default _ _ (Nat.le_of_not_lt hi)

theorem letLin_letAt_apply {alph : List (Vn n × Vn n)} (hA : AlphOK alph) (i : ℕ) (v : Vn n) :
    letLin (letAt alph i) v = letApp (letAt alph i) v := by
  rcases letAt_cases alph i with h | h
  · rw [letLin_of _ (hA _ h), refl_apply]
    rfl
  · rw [h, letLin_zero]
    simp [letApp]

theorem wLin_apply {alph : List (Vn n × Vn n)} (hA : AlphOK alph) (w : List ℕ) (v : Vn n) :
    wLin alph w v = wEval alph w v := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [wLin, List.map_cons, List.prod_cons, LinearEquiv.mul_apply]
      change letLin (letAt alph i) (wLin alph w v) = letApp (letAt alph i) (wEval alph w v)
      rw [ih, letLin_letAt_apply hA]

theorem wLin_mem {alph : List (Vn n × Vn n)} {H : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)}
    (hA : ∀ l ∈ alph, letLin l ∈ H) (w : List ℕ) : wLin alph w ∈ H := by
  refine list_prod_mem fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  rcases letAt_cases alph i with h | h
  · exact hA _ h
  · rw [h, letLin_zero]
    exact H.one_mem

theorem wLin_flatten (alph : List (Vn n × Vn n)) (segs : List (List ℕ)) :
    wLin alph segs.flatten = (segs.map (wLin alph)).prod := by
  induction segs with
  | nil => rfl
  | cons s segs ih =>
      rw [List.flatten_cons, List.map_cons, List.prod_cons, ← ih]
      unfold wLin
      rw [List.map_append, List.prod_append]

theorem wLin_inv (alph : List (Vn n × Vn n)) (w : List ℕ) :
    (wLin alph w)⁻¹ = wLin alph w.reverse := by
  unfold wLin
  rw [List.prod_inv_reverse, List.map_map, List.map_reverse]
  congr 2
  exact List.map_congr_left fun i _ => letLin_inv _

theorem wLin_inv_apply {alph : List (Vn n × Vn n)} (hA : AlphOK alph) (w : List ℕ) (v : Vn n) :
    (wLin alph w)⁻¹ v = wEval alph w.reverse v := by
  rw [wLin_inv, wLin_apply hA]

theorem refl_congr {c a c' a' : Vn n} (hc : c = c') (ha : a = a') (h : a ⬝ᵥ c = 2)
    (h' : a' ⬝ᵥ c' = 2) : refl c a h = refl c' a' h' := by
  subst hc
  subst ha
  rfl

theorem refl_two_smul (c a : Vn n) (h : a ⬝ᵥ c = 2)
    (h' : ((2 : ZMod 3) • a) ⬝ᵥ ((2 : ZMod 3) • c) = 2) :
    refl ((2 : ZMod 3) • c) ((2 : ZMod 3) • a) h' = refl c a h := by
  apply LinearEquiv.ext
  intro v
  rw [refl_apply, refl_apply, smul_dotProduct, smul_smul]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  have h4 : (4 : ZMod 3) = 1 := by decide
  rw [h4, mul_one]

theorem refl_eq_of_sameRefl {l l' : Vn n × Vn n} (hS : sameRefl l l' = true)
    (h : l.2 ⬝ᵥ l.1 = 2) (h' : l'.2 ⬝ᵥ l'.1 = 2) : refl l.1 l.2 h = refl l'.1 l'.2 h' := by
  unfold sameRefl at hS
  rcases Bool.or_eq_true_iff.mp hS with hS | hS
  · have hl := of_decide_eq_true hS
    exact refl_congr (congrArg Prod.fst hl).symm (congrArg Prod.snd hl).symm h h'
  · have hl := of_decide_eq_true hS
    subst hl
    exact (refl_two_smul l.1 l.2 h h').symm

theorem wLin_conj {alph : List (Vn n × Vn n)} (hA : AlphOK alph) (m : List ℕ)
    (l : Vn n × Vn n) (h : l.2 ⬝ᵥ l.1 = 2) :
    ∃ h' : (wConj alph m l).2 ⬝ᵥ (wConj alph m l).1 = 2,
      wLin alph m * refl l.1 l.2 h * (wLin alph m)⁻¹ =
        refl (wConj alph m l).1 (wConj alph m l).2 h' := by
  have hc : wLin alph m l.1 = (wConj alph m l).1 := wLin_apply hA m l.1
  have ha : dualVec ((wLin alph m).symm : Vn n →ₗ[ZMod 3] Vn n) l.2 = (wConj alph m l).2 := by
    funext j
    change l.2 ⬝ᵥ (wLin alph m).symm (Pi.single j 1) = l.2 ⬝ᵥ wEval alph m.reverse (Pi.single j 1)
    rw [← wLin_inv_apply hA]
    rfl
  have hconj := conj_refl (wLin alph m) l.1 l.2 h
  have h' : (wConj alph m l).2 ⬝ᵥ (wConj alph m l).1 = 2 := by
    rw [← hc, ← ha, dualVec_dotProduct]
    simpa using h
  exact ⟨h', hconj.trans (refl_congr hc ha _ h')⟩

theorem AlphOK.append {alph alph' : List (Vn n × Vn n)} (h : AlphOK alph) (h' : AlphOK alph') :
    AlphOK (alph ++ alph') := by
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · exact h l hl
  · exact h' l hl

theorem AlphOK.of_all {alph : List (Vn n × Vn n)}
    (h : alph.all (fun l => decide (l.2 ⬝ᵥ l.1 = 2)) = true) : AlphOK alph := fun l hl =>
  of_decide_eq_true (List.all_eq_true.mp h l hl)

theorem fixesLine_of_pmB {x y : Vn n} (h : pmB x y = true) : y = x ∨ y = -x := by
  unfold pmB at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Or.inl (of_decide_eq_true h)
  · exact Or.inr (of_decide_eq_true h)

private def transvLin (c a : Vn n) : Vn n →ₗ[ZMod 3] Vn n where
  toFun v := v + (a ⬝ᵥ v) • c
  map_add' u v := by
    rw [dotProduct_add, add_smul]
    abel
  map_smul' r v := by
    rw [dotProduct_smul, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply]

variable {W A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} {x₀ : Vn n}

theorem TestHyp.false_of_exclB (hT : TestHyp W x₀ A M) {alph gens : List (Vn n × Vn n)}
    (hA : AlphOK alph) (halph : ∀ l ∈ alph, letLin l ∈ A) (hgens : AlphOK gens)
    (hgW : ∀ l ∈ gens, letLin l ∈ W) {sets : List (List (Vn n))}
    (hinv : ∀ S ∈ sets, ∀ w ∈ W, ∀ v ∈ S, w v ∈ S) {h : List ℕ} {k si : ℕ} {v : Vn n}
    (hB : exclB alph gens sets x₀ h k si v = true) : False := by
  unfold exclB at hB
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    at hB
  obtain ⟨⟨⟨hfix, hk⟩, hv⟩, hout⟩ := hB
  have hS : sets.getD si [] ∈ sets := by
    by_cases hsi : si < sets.length
    · rw [List.getD_eq_getElem _ _ hsi]
      exact List.getElem_mem hsi
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hsi)] at hv
      exact absurd hv (List.not_mem_nil)
  have hgk : letAt gens k ∈ gens := by
    unfold letAt
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  refine hT.false_of_witness {u | u ∈ sets.getD si []} (fun w hw u hu => hinv _ hS w hw u hu)
    (wLin_mem halph h) ?_ (hgW _ hgk) (s := v) hv ?_
  · rw [FixesLine, wLin_apply hA]
    exact fixesLine_of_pmB hfix
  · simp only [Set.mem_setOf_eq, LinearEquiv.mul_apply]
    rw [wLin_inv_apply hA, letLin_letAt_apply hgens, wLin_apply hA]
    exact hout

theorem TestHyp.false_of_tvB (hT : TestHyp W x₀ A M) {alph : List (Vn n × Vn n)}
    (hA : AlphOK alph) (halph : ∀ l ∈ alph, letLin l ∈ A) {T : List ℕ} {c a : Vn n}
    (hB : tvB alph T c a = true) : False := by
  unfold tvB at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hB
  obtain ⟨⟨⟨hc, ha⟩, hac⟩, hbasis⟩ := hB
  have hlin : (wLin alph T).toLinearMap = transvLin c a := by
    refine (Pi.basisFun (ZMod 3) (Fin n)).ext fun j => ?_
    rw [Pi.basisFun_apply, LinearEquiv.coe_coe, wLin_apply hA]
    exact hbasis j (List.mem_finRange j)
  refine hT.noTransv _ (wLin_mem halph T) ⟨c, a, hc, ha, hac, fun v => ?_⟩
  exact congrArg (fun F : Vn n →ₗ[ZMod 3] Vn n => F v) hlin

theorem TestHyp.false_of_symw (hT : TestHyp W x₀ A M) {gens : List (Vn n × Vn n)}
    (hgens : AlphOK gens) (hgW : ∀ l ∈ gens, letLin l ∈ W) {u : Vn n × Vn n}
    (hu : u.2 ⬝ᵥ u.1 = 2) (huA : refl u.1 u.2 hu ∈ A) {m : List ℕ} {k : ℕ} (hk : k < gens.length)
    (hB : symB u (wConj gens m (letAt gens k)) = false) : False := by
  have hgk : letAt gens k ∈ gens := by
    unfold letAt
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have hgkOK := hgens _ hgk
  obtain ⟨h', hconj⟩ := wLin_conj hgens m (letAt gens k) hgkOK
  have hsW : wLin gens m * refl (letAt gens k).1 (letAt gens k).2 hgkOK * (wLin gens m)⁻¹ ∈ W := by
    refine W.mul_mem (W.mul_mem (wLin_mem hgW m) ?_) (W.inv_mem (wLin_mem hgW m))
    rw [← letLin_of _ hgkOK]
    exact hgW _ hgk
  rw [hconj] at hsW
  have hsym := sym_of_noTransv hT.noTransv hu h' huA (hT.le (hT.W_le hsW))
  unfold symB at hB
  rw [decide_eq_false_iff_not] at hB
  exact hB hsym

theorem sets_inv_of_gens {gens : List (Vn n × Vn n)} (hgens : AlphOK gens)
    (hWgen : W ≤ Subgroup.closure {g | ∃ l ∈ gens, g = letLin l}) {sets : List (List (Vn n))}
    (hB : sets.all (fun S => gens.all fun g => S.all fun v => decide (letApp g v ∈ S)) = true) :
    ∀ S ∈ sets, ∀ w ∈ W, ∀ v ∈ S, w v ∈ S := by
  intro S hS w hw
  have hgen : ∀ l ∈ gens, ∀ v ∈ S, letLin l v ∈ S := by
    intro l hl v hv
    have h1 := List.all_eq_true.mp hB S hS
    have h2 := List.all_eq_true.mp h1 l hl
    have h3 := of_decide_eq_true (List.all_eq_true.mp h2 v hv)
    rw [letLin_of _ (hgens l hl), refl_apply]
    exact h3
  have hw' := hWgen hw
  clear hw
  induction hw' using Subgroup.closure_induction'' with
  | mem g hg =>
      obtain ⟨l, hl, rfl⟩ := hg
      exact hgen l hl
  | inv_mem g hg =>
      obtain ⟨l, hl, rfl⟩ := hg
      rw [letLin_inv]
      exact hgen l hl
  | one => exact fun v hv => hv
  | mul g g' _ _ ih ih' => exact fun v hv => ih _ (ih' v hv)

theorem TestHyp.exists_rep_of_patB (hT : TestHyp W x₀ A M) {gens : List (Vn n × Vn n)}
    (hgens : AlphOK gens) (hgW : ∀ l ∈ gens, letLin l ∈ W) {sets : List (List (Vn n))}
    (hinv : ∀ S ∈ sets, ∀ w ∈ W, ∀ v ∈ S, w v ∈ S) {reps : List (Vn n × Vn n)}
    (hreps : AlphOK reps) {p : (Vn n × Vn n) × PatV n} (hB : patB gens sets x₀ reps p = true)
    (hp : p.1.2 ⬝ᵥ p.1.1 = 2) (hpA : refl p.1.1 p.1.2 hp ∈ A) :
    ∃ w ∈ W, ∃ i < reps.length, ∃ h : (letAt reps i).2 ⬝ᵥ (letAt reps i).1 = 2,
      w * refl p.1.1 p.1.2 hp * w⁻¹ = refl (letAt reps i).1 (letAt reps i).2 h := by
  have hgA : ∀ l ∈ gens, letLin l ∈ A := fun l hl => hT.le (hT.W_le (hgW l hl))
  have halph : AlphOK (gens ++ [p.1]) :=
    hgens.append fun l hl => by rw [List.mem_singleton.mp hl]; exact hp
  have halphA : ∀ l ∈ gens ++ [p.1], letLin l ∈ A := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hgA l hl
    · rw [List.mem_singleton.mp hl, letLin_of _ hp]
      exact hpA
  unfold patB at hB
  rw [Bool.and_eq_true] at hB
  obtain ⟨-, hB⟩ := hB
  rcases hp2 : p.2 with ⟨m, k⟩ | ⟨h, k, si, v⟩ | ⟨T, c, a⟩ | ⟨m, ri⟩ <;> rw [hp2] at hB
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hB
    exact (hT.false_of_symw hgens hgW hp hpA hB.1 hB.2).elim
  · exact (hT.false_of_exclB halph halphA hgens hgW hinv hB).elim
  · exact (hT.false_of_tvB halph halphA hB).elim
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
    obtain ⟨hri, hsame⟩ := hB
    have hrepOK : (letAt reps ri).2 ⬝ᵥ (letAt reps ri).1 = 2 := by
      unfold letAt
      rw [List.getD_eq_getElem _ _ hri]
      exact hreps _ (List.getElem_mem hri)
    obtain ⟨h', hconj⟩ := wLin_conj hgens m p.1 hp
    refine ⟨wLin gens m, wLin_mem hgW m, ri, hri, hrepOK, ?_⟩
    rw [hconj]
    exact refl_eq_of_sameRefl hsame h' hrepOK

theorem TestHyp.mem_of_s2B (hT : TestHyp W x₀ A M) {gens : List (Vn n × Vn n)}
    (hgens : AlphOK gens) (hgW : ∀ l ∈ gens, letLin l ∈ W) {sets : List (List (Vn n))}
    (hinv : ∀ S ∈ sets, ∀ w ∈ W, ∀ v ∈ S, w v ∈ S) {reps : List (Vn n × Vn n)} {i j : ℕ}
    (hi : (letAt reps i).2 ⬝ᵥ (letAt reps i).1 = 2) (hj : (letAt reps j).2 ⬝ᵥ (letAt reps j).1 = 2)
    (hrM : refl (letAt reps i).1 (letAt reps i).2 hi ∈ M)
    (htA : refl (letAt reps j).1 (letAt reps j).2 hj ∈ A) {V : S2V n}
    (hB : s2B gens sets x₀ reps i j V = true) :
    refl (letAt reps j).1 (letAt reps j).2 hj ∈ M := by
  have hgA : ∀ l ∈ gens, letLin l ∈ A := fun l hl => hT.le (hT.W_le (hgW l hl))
  have hgM : ∀ l ∈ gens, letLin l ∈ M := fun l hl => hT.W_le (hgW l hl)
  cases V with
  | inn m =>
      obtain ⟨h', hconj⟩ := wLin_conj hgens m (letAt reps i) hi
      have hmem : wLin gens m * refl (letAt reps i).1 (letAt reps i).2 hi * (wLin gens m)⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem (wLin_mem hgM m) hrM) (M.inv_mem (wLin_mem hgM m))
      rw [hconj, refl_eq_of_sameRefl hB h' hj] at hmem
      exact hmem
  | sym m =>
      exfalso
      obtain ⟨h', hconj⟩ := wLin_conj hgens m (letAt reps i) hi
      have hmem : wLin gens m * refl (letAt reps i).1 (letAt reps i).2 hi * (wLin gens m)⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem (wLin_mem hgA m) (hT.le hrM)) (A.inv_mem (wLin_mem hgA m))
      rw [hconj] at hmem
      have hsym := sym_of_noTransv hT.noTransv hj h' htA hmem
      change (!symB (letAt reps j) (wConj gens m (letAt reps i))) = true at hB
      rw [Bool.not_eq_true', symB, decide_eq_false_iff_not] at hB
      exact hB hsym
  | orb m =>
      have halph : AlphOK (gens ++ [letAt reps i]) :=
        hgens.append fun l hl => by rw [List.mem_singleton.mp hl]; exact hi
      have halphM : ∀ l ∈ gens ++ [letAt reps i], letLin l ∈ M := by
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact hgM l hl
        · rw [List.mem_singleton.mp hl, letLin_of _ hi]
          exact hrM
      refine hT.mem_of_orbit htA (wLin_mem halphM m) ?_
      rw [wLin_apply halph, refl_apply]
      exact fixesLine_of_pmB hB
  | excl h k si v =>
      exfalso
      have halph : AlphOK (gens ++ [letAt reps i, letAt reps j]) := by
        refine hgens.append fun l hl => ?_
        rcases List.mem_pair.mp hl with rfl | rfl
        · exact hi
        · exact hj
      have halphA : ∀ l ∈ gens ++ [letAt reps i, letAt reps j], letLin l ∈ A := by
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact hgA l hl
        · rcases List.mem_pair.mp hl with rfl | rfl
          · rw [letLin_of _ hi]
            exact hT.le hrM
          · rw [letLin_of _ hj]
            exact htA
      exact hT.false_of_exclB halph halphA hgens hgW hinv hB
  | stab segs =>
      have halph : AlphOK (gens ++ [letAt reps i, letAt reps j]) := by
        refine hgens.append fun l hl => ?_
        rcases List.mem_pair.mp hl with rfl | rfl
        · exact hi
        · exact hj
      have halphA : ∀ l ∈ gens ++ [letAt reps i, letAt reps j], letLin l ∈ A := by
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact hgA l hl
        · rcases List.mem_pair.mp hl with rfl | rfl
          · rw [letLin_of _ hi]
            exact hT.le hrM
          · rw [letLin_of _ hj]
            exact htA
      have hletM : ∀ l ≤ gens.length,
          letLin (letAt (gens ++ [letAt reps i, letAt reps j]) l) ∈ M := by
        intro l hl
        unfold letAt
        rcases Nat.lt_or_eq_of_le hl with hl | rfl
        · rw [List.getD_append _ _ _ _ hl]
          rcases letAt_cases gens l with h | h
          · exact hgM _ h
          · change letLin (letAt gens l) ∈ M
            rw [h, letLin_zero]
            exact M.one_mem
        · rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
          change letLin (letAt reps i) ∈ M
          rw [letLin_of _ hi]
          exact hrM
      change ((segs.all fun s => s.all (fun l => decide (l ≤ gens.length)) ||
          pmB x₀ (wEval (gens ++ [letAt reps i, letAt reps j]) s x₀)) &&
        pmB (letApp (letAt reps j) x₀)
          (wEval (gens ++ [letAt reps i, letAt reps j]) segs.flatten x₀)) = true at hB
      rw [Bool.and_eq_true] at hB
      obtain ⟨hsegs, hpm⟩ := hB
      have hsegM : ∀ s ∈ segs, wLin (gens ++ [letAt reps i, letAt reps j]) s ∈ M := by
        intro s hs
        rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hsegs s hs) with hs' | hs'
        · refine list_prod_mem fun g hg => ?_
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
          exact hletM l (of_decide_eq_true (List.all_eq_true.mp hs' l hl))
        · refine hT.stab_mem _ (wLin_mem halphA s) ?_
          rw [FixesLine, wLin_apply halph]
          exact fixesLine_of_pmB hs'
      have hmM : wLin (gens ++ [letAt reps i, letAt reps j]) segs.flatten ∈ M := by
        rw [wLin_flatten]
        refine list_prod_mem fun g hg => ?_
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
        exact hsegM s hs
      refine hT.mem_of_orbit htA hmM ?_
      rw [wLin_apply halph, refl_apply]
      exact fixesLine_of_pmB hpm

theorem TestHyp.mem_of_certOK (hT : TestHyp W x₀ A M) {gens : List (Vn n × Vn n)}
    {sets : List (List (Vn n))} {pats : List ((Vn n × Vn n) × PatV n)}
    {reps : List (Vn n × Vn n)} {s2 : List (S2V n)}
    (hOK : certOK gens x₀ sets pats reps s2 = true) (hgW : ∀ l ∈ gens, letLin l ∈ W)
    (hWgen : W ≤ Subgroup.closure {g | ∃ l ∈ gens, g = letLin l})
    (hred : ∀ u ∈ A, IsRefl u → ¬ FixesLine x₀ u → ∃ w ∈ W, ∃ p ∈ pats,
      ∃ h : p.1.2 ⬝ᵥ p.1.1 = 2, w * u * w⁻¹ = refl p.1.1 p.1.2 h)
    {r t : Vn n ≃ₗ[ZMod 3] Vn n} (hr : r ∈ M) (hrR : IsRefl r) (hrx : ¬ FixesLine x₀ r)
    (ht : t ∈ A) (htR : IsRefl t) (htx : ¬ FixesLine x₀ t) : t ∈ M := by
  unfold certOK at hOK
  simp only [Bool.and_eq_true] at hOK
  obtain ⟨⟨⟨⟨hgOK, hrOK⟩, hsOK⟩, hpOK⟩, hs2OK⟩ := hOK
  have hgens : AlphOK gens := AlphOK.of_all hgOK
  have hreps : AlphOK reps := AlphOK.of_all hrOK
  have hinv := sets_inv_of_gens hgens hWgen hsOK
  have hcls : ∀ u ∈ A, IsRefl u → ¬ FixesLine x₀ u → ∃ w ∈ W, ∃ i < reps.length,
      ∃ h : (letAt reps i).2 ⬝ᵥ (letAt reps i).1 = 2,
        w * u * w⁻¹ = refl (letAt reps i).1 (letAt reps i).2 h := by
    intro u hu huR hux
    obtain ⟨w, hw, p, hp, hpc, hwu⟩ := hred u hu huR hux
    have hpA : refl p.1.1 p.1.2 hpc ∈ A := by
      rw [← hwu]
      exact A.mul_mem (A.mul_mem (hT.le (hT.W_le hw)) hu) (A.inv_mem (hT.le (hT.W_le hw)))
    obtain ⟨w', hw', i, hi, hrep, hw'p⟩ := hT.exists_rep_of_patB hgens hgW hinv hreps
      (List.all_eq_true.mp hpOK p hp) hpc hpA
    refine ⟨w' * w, W.mul_mem hw' hw, i, hi, hrep, ?_⟩
    rw [← hw'p, ← hwu, mul_inv_rev]
    group
  obtain ⟨wr, hwr, i, hi, hri, hwrr⟩ := hcls r (hT.le hr) hrR hrx
  obtain ⟨wt, hwt, j, hj, htj, hwtt⟩ := hcls t ht htR htx
  have hrM : refl (letAt reps i).1 (letAt reps i).2 hri ∈ M := by
    rw [← hwrr]
    exact M.mul_mem (M.mul_mem (hT.W_le hwr) hr) (M.inv_mem (hT.W_le hwr))
  have htA : refl (letAt reps j).1 (letAt reps j).2 htj ∈ A := by
    rw [← hwtt]
    exact A.mul_mem (A.mul_mem (hT.le (hT.W_le hwt)) ht) (A.inv_mem (hT.le (hT.W_le hwt)))
  have hB := List.all_eq_true.mp (List.all_eq_true.mp hs2OK i (List.mem_range.mpr hi)) j
    (List.mem_range.mpr hj)
  have htM := hT.mem_of_s2B hgens hgW hinv hri htj hrM htA hB
  have heq : t = wt⁻¹ * refl (letAt reps j).1 (letAt reps j).2 htj * wt := by
    rw [← hwtt]
    group
  rw [heq]
  exact M.mul_mem (M.mul_mem (M.inv_mem (hT.W_le hwt)) htM) (hT.W_le hwt)

end CFSG.StandardType.TestLin

end
