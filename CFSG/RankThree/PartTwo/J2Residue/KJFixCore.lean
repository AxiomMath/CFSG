module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3
public import Certificates.Certificate111603
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.RankThree.PartTwo.J2Residue.C280

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.ComponentClassification.J2Cover CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

@[expose] noncomputable def genP (k : ℕ) : GJ := if k = 0 then pa else pb

@[expose] noncomputable def wordP (w : List ℕ) : GJ := w.foldr (fun k acc => genP k * acc) 1

theorem wordP_cons (k : ℕ) (w : List ℕ) : wordP (k :: w) = genP k * wordP w := rfl

theorem rep_genA (k : ℕ) : Rep 315 (genA k) (genP k).1 := by
  unfold genA genP
  split_ifs
  · exact rep_permA
  · exact rep_permB

theorem wordA_nil : wordA [] = idA 315 := by
  simp only [wordA, List.foldr_nil]

theorem wordA_cons (k : ℕ) (w : List ℕ) : wordA (k :: w) = compA 315 (genA k) (wordA w) := by
  simp only [wordA, List.foldr_cons]

theorem rep_wordA (w : List ℕ) :
    Rep 315 (wordA w) (wordP w).1 := by
  induction w with
  | nil =>
    rw [wordA_nil, show (wordP []).1 = 1 from rfl]
    exact rep_idA
  | cons k w ih =>
    rw [wordA_cons, wordP_cons, Subgroup.coe_mul]
    exact rep_compA (rep_genA k) ih

theorem forall_of_gens {p : GJ → Prop} (ha : p pa) (hb : p pb) (h1 : p 1)
    (hmul : ∀ g h, p g → p h → p (g * h)) (g : GJ) : p g := by
  have hpow : ∀ x, p x → ∀ n : ℕ, p (x ^ n) := by
    intro x hx n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hx
  have hg : g ∈ Subgroup.closure ({pa, pb} : Set GJ) := by
    rw [closure_pa_pb]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy
  | inv x _ hx =>
    have hxinv : x⁻¹ = x ^ (orderOf x - 1) := inv_eq_of_mul_eq_one_left (by
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one])
    rw [hxinv]
    exact hpow x hx _

theorem ofFn_getElem! {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem checkA_spec :
    validA 315 (genA 0) = true ∧ validA 315 (genA 1) = true ∧ validA 315 zArr = true ∧
      ∀ i < 280, validA 315 (wordA words[i]!) = true ∧ tA[i]! < 280 ∧ tB[i]! < 280 ∧
        tZ[i]! < 280 ∧ sameLine (conjA 315 (genA 0) (conjY i)) (conjY tA[i]!) = true ∧
        sameLine (conjA 315 (genA 1) (conjY i)) (conjY tB[i]!) = true ∧
        sameLine (conjA 315 zArr (conjY i)) (conjY tZ[i]!) = true := by
  have h := Certificates.certificate111603.1
  simp only [checkA, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h4 i hi
  rw [ofFn_getElem! _ hi, ofFn_getElem! _ h6] at h9
  rw [ofFn_getElem! _ hi, ofFn_getElem! _ h7] at h10
  rw [ofFn_getElem! _ hi, ofFn_getElem! _ h8] at h11
  exact ⟨h5, h6, h7, h8, h9, h10, h11⟩

theorem checkB_spec :
    (∀ c < 3, reps[c]! < 280 ∧ tZ[tZ[tZ[reps[c]!]!]!]! = reps[c]!) ∧
      ∀ p < 7, (∀ t ∈ combs[p]!, cls[t.2]! < 3) ∧
        parityOK (combList pats[p]! combs[p]!) = true := by
  have h := Certificates.certificate111603.2.1
  simp only [checkB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at h
  exact h

theorem checkC_spec :
    tZ[0]! = 0 ∧ words[0]! = [] ∧ ∀ j < 280, j ≠ 0 → cls[j]! < 3 ∧ tab (uOf j) 0 = 0 ∧
      permEq ((rel cls[j]!).map (tab (uOf j))) [j, tZ[j]!, tZ[tZ[j]!]!] = true := by
  have h := Certificates.certificate111603.2.2
  simp only [checkC, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun j hj hj0 => ?_⟩
  rcases h3 j hj with h | ⟨⟨h4, h5⟩, h6⟩
  · exact absurd h hj0
  · exact ⟨h4, h5, h6⟩

section Model


@[expose] noncomputable def yP (i : ℕ) : GJ := wordP words[i]! * zJ * (wordP words[i]!)⁻¹

theorem rep_conjY {i : ℕ} (hi : i < 280) : Rep 315 (conjY i) (yP i).1 := by
  have hv := (checkA_spec.2.2.2 i hi).1
  have h := rep_conjA hv rep_z
  rw [(rep_of_validA hv).unique (rep_wordA _)] at h
  exact h

theorem eq_or_eq_sq_of_sameLine {t y : Array ℕ} {g h : Equiv.Perm (Fin 315)} (ht : Rep 315 t g)
    (hy : Rep 315 y h) (hs : sameLine t y = true) : g = h ∨ g = h * h := by
  simp only [sameLine, Bool.or_eq_true] at hs
  rcases hs with h1 | h1
  · exact Or.inl (eq_of_eqA ht hy h1)
  · exact Or.inr (eq_of_eqA ht (rep_compA hy hy) h1)

theorem conj_yP {g : GJ} {t : Array ℕ} (hg : Rep 315 t g.1) (hv : validA 315 t = true)
    {i j : ℕ} (hi : i < 280) (hj : j < 280)
    (hs : sameLine (conjA 315 t (conjY i)) (conjY j) = true) :
    g * yP i * g⁻¹ = yP j ∨ g * yP i * g⁻¹ = yP j * yP j := by
  have h1 := rep_conjA hv (rep_conjY hi)
  rw [(rep_of_validA hv).unique hg] at h1
  rcases eq_or_eq_sq_of_sameLine h1 (rep_conjY hj) hs with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem tabOf_lt (k : ℕ) {i : ℕ} (hi : i < 280) : (tabOf k)[i]! < 280 := by
  unfold tabOf
  split_ifs
  · exact (checkA_spec.2.2.2 i hi).2.1
  · exact (checkA_spec.2.2.2 i hi).2.2.1

theorem tab_cons (k : ℕ) (u : List ℕ) (i : ℕ) : tab (k :: u) i = (tabOf k)[tab u i]! := rfl

theorem tab_lt (u : List ℕ) {i : ℕ} (hi : i < 280) : tab u i < 280 := by
  induction u with
  | nil => exact hi
  | cons k u ih => exact tabOf_lt k ih

theorem conj_yP_genP (k : ℕ) {i : ℕ} (hi : i < 280) :
    genP k * yP i * (genP k)⁻¹ = yP (tabOf k)[i]! ∨
      genP k * yP i * (genP k)⁻¹ = yP (tabOf k)[i]! * yP (tabOf k)[i]! := by
  have hA := checkA_spec.2.2.2 i hi
  by_cases hk : k = 0
  · subst hk
    exact conj_yP (rep_genA 0) checkA_spec.1 hi hA.2.1 hA.2.2.2.2.1
  · have hg : genP k = genP 1 := by simp [genP, hk]
    have ht : tabOf k = tB := by simp [tabOf, hk]
    rw [hg, ht]
    exact conj_yP (rep_genA 1) checkA_spec.2.1 hi hA.2.2.1 hA.2.2.2.2.2.1

theorem conj_yP_z {i : ℕ} (hi : i < 280) :
    zJ * yP i * zJ⁻¹ = yP tZ[i]! ∨ zJ * yP i * zJ⁻¹ = yP tZ[i]! * yP tZ[i]! := by
  have hA := checkA_spec.2.2.2 i hi
  exact conj_yP rep_z checkA_spec.2.2.1 hi hA.2.2.2.1 hA.2.2.2.2.2.2

end Model

theorem prod_eq_of_parityOK {V : Type*} [CommGroup V] (hV : ∀ x : V, x * x = 1) (f : ℕ → V)
    {l : List ℕ} (hl : ∀ x ∈ l, x < 280) (h : parityOK l = true) : (l.map f).prod = f 0 := by
  classical
  simp only [parityOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [Finset.prod_list_map_count]
  have hpow : ∀ m ∈ l.toFinset, f m ^ l.count m = if m = 0 then f m else 1 := by
    intro m hm
    have hc := h m (hl m (List.mem_toFinset.mp hm))
    have h2 : f m ^ 2 = 1 := by rw [sq]; exact hV _
    rw [← Nat.mod_add_div (l.count m) 2, pow_add, pow_mul, h2, one_pow, mul_one, hc]
    split_ifs <;> simp
  rw [Finset.prod_congr rfl hpow, Finset.prod_ite_eq']
  have h0 := h 0 (by norm_num)
  have hmem : 0 ∈ l.toFinset := by
    rw [List.mem_toFinset, ← List.count_pos_iff]
    simp only [if_true] at h0
    omega
  simp [hmem]

theorem prod_eq_of_permEq {V : Type*} [CommGroup V] (f : ℕ → V) {l₁ l₂ : List ℕ}
    (h : permEq l₁ l₂ = true) : (l₁.map f).prod = (l₂.map f).prod := by
  have hp : l₁.Perm l₂ := by
    rw [List.perm_iff_count]
    intro a
    simp only [permEq, List.all_eq_true, beq_iff_eq] at h
    by_cases ha : a ∈ l₁ ++ l₂
    · exact h a ha
    · rw [List.mem_append, not_or] at ha
      rw [List.count_eq_zero_of_not_mem ha.1, List.count_eq_zero_of_not_mem ha.2]
  exact (hp.map f).prod_eq

theorem prod_map_flatMap {V : Type*} [CommGroup V] (f : ℕ → V) {α : Type*} (F : α → List ℕ)
    (ts : List α) : ((ts.flatMap F).map f).prod = (ts.map fun t => ((F t).map f).prod).prod := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [List.flatMap_cons, List.map_append, List.prod_append, ih]; rfl

section Module

variable {V : Type*} [CommGroup V] (ρ : GJ →* MulAut V) (v : V)

@[expose] noncomputable def phi (i : ℕ) : V := ρ (wordP words[i]!) v

theorem phi_zero : phi ρ v 0 = v := by
  rw [phi, checkC_spec.2.1]
  simp [wordP]

theorem rho_fix (hfix : ∀ x : V, ρ zJ x = x ↔ x = 1 ∨ x = v) (hv : v ≠ 1) {n : GJ}
    (hn : n * zJ * n⁻¹ = zJ ∨ n * zJ * n⁻¹ = zJ * zJ) : ρ n v = v := by
  have hzv : ρ zJ v = v := (hfix v).2 (Or.inr rfl)
  have hz3 : zJ * zJ * zJ = 1 := by
    have h := z_cube
    rwa [pow_three, ← mul_assoc] at h
  have key : ρ zJ (ρ n v) = ρ n v := by
    rcases hn with h | h
    · have hc : zJ * n = n * zJ := by
        calc zJ * n = n * zJ * n⁻¹ * n := by rw [h]
          _ = n * zJ := inv_mul_cancel_right _ _
      calc ρ zJ (ρ n v) = ρ (zJ * n) v := by rw [map_mul, MulAut.mul_apply]
        _ = ρ (n * zJ) v := by rw [hc]
        _ = ρ n v := by rw [map_mul, MulAut.mul_apply, hzv]
    · have hc : zJ * zJ * n = n * zJ := by
        calc zJ * zJ * n = n * zJ * n⁻¹ * n := by rw [h]
          _ = n * zJ := inv_mul_cancel_right _ _
      have h2 : ρ (zJ * zJ) (ρ n v) = ρ n v := by
        calc ρ (zJ * zJ) (ρ n v) = ρ (zJ * zJ * n) v := by
              rw [map_mul ρ (zJ * zJ) n, MulAut.mul_apply]
          _ = ρ (n * zJ) v := by rw [hc]
          _ = ρ n v := by rw [map_mul, MulAut.mul_apply, hzv]
      calc ρ zJ (ρ n v) = ρ zJ (ρ (zJ * zJ) (ρ n v)) := by rw [h2]
        _ = ρ (zJ * zJ * zJ) (ρ n v) := by
          rw [mul_assoc, map_mul ρ zJ (zJ * zJ), MulAut.mul_apply]
        _ = ρ n v := by rw [hz3, map_one, MulAut.one_apply]
  rcases (hfix _).1 key with h | h
  · refine absurd ?_ hv
    have h' : ρ n v = ρ n 1 := by rw [h, map_one]
    exact (ρ n).injective h'
  · exact h

theorem rho_phi_of (hfix : ∀ x : V, ρ zJ x = x ↔ x = 1 ∨ x = v) (hv : v ≠ 1) {g : GJ}
    {i j : ℕ} (h : g * yP i * g⁻¹ = yP j ∨ g * yP i * g⁻¹ = yP j * yP j) :
    ρ g (phi ρ v i) = phi ρ v j := by
  set wi := wordP words[i]! with hwi
  set wj := wordP words[j]! with hwj
  have e : (wj⁻¹ * g * wi) * zJ * (wj⁻¹ * g * wi)⁻¹ = wj⁻¹ * (g * yP i * g⁻¹) * wj := by
    simp only [yP, ← hwi]
    group
  have hn : (wj⁻¹ * g * wi) * zJ * (wj⁻¹ * g * wi)⁻¹ = zJ ∨
      (wj⁻¹ * g * wi) * zJ * (wj⁻¹ * g * wi)⁻¹ = zJ * zJ := by
    rw [e]
    rcases h with h | h
    · left
      rw [h]
      simp only [yP, ← hwj]
      group
    · right
      rw [h]
      simp only [yP, ← hwj]
      group
  have hfixn := rho_fix ρ v hfix hv hn
  calc ρ g (phi ρ v i) = ρ (g * wi) v := by rw [phi, map_mul, MulAut.mul_apply]
    _ = ρ (wj * (wj⁻¹ * g * wi)) v := by
      rw [show wj * (wj⁻¹ * g * wi) = g * wi by
        simp only [← mul_assoc, mul_inv_cancel, one_mul]]
    _ = ρ wj (ρ (wj⁻¹ * g * wi) v) := by rw [map_mul, MulAut.mul_apply]
    _ = phi ρ v j := by rw [hfixn]; rfl

theorem rho_genP_phi (hfix : ∀ x : V, ρ zJ x = x ↔ x = 1 ∨ x = v) (hv : v ≠ 1) (k : ℕ)
    {i : ℕ} (hi : i < 280) : ρ (genP k) (phi ρ v i) = phi ρ v (tabOf k)[i]! :=
  rho_phi_of ρ v hfix hv (conj_yP_genP k hi)

theorem rho_z_phi (hfix : ∀ x : V, ρ zJ x = x ↔ x = 1 ∨ x = v) (hv : v ≠ 1) {i : ℕ}
    (hi : i < 280) : ρ zJ (phi ρ v i) = phi ρ v tZ[i]! :=
  rho_phi_of ρ v hfix hv (conj_yP_z hi)

theorem rho_wordP_phi (hfix : ∀ x : V, ρ zJ x = x ↔ x = 1 ∨ x = v) (hv : v ≠ 1)
    (u : List ℕ) {i : ℕ} (hi : i < 280) : ρ (wordP u) (phi ρ v i) = phi ρ v (tab u i) := by
  induction u with
  | nil => simp [wordP, tab]
  | cons k u ih =>
    rw [wordP_cons, map_mul, MulAut.mul_apply, ih, tab_cons,
      rho_genP_phi ρ v hfix hv k (tab_lt u hi)]

theorem rho_wordP_prod (hfix : ∀ x : V, ρ zJ x = x ↔ x = 1 ∨ x = v) (hv : v ≠ 1)
    (u : List ℕ) {l : List ℕ} (hl : ∀ x ∈ l, x < 280) :
    ρ (wordP u) (l.map (phi ρ v)).prod = ((l.map (tab u)).map (phi ρ v)).prod := by
  rw [map_list_prod, List.map_map, List.map_map]
  exact congrArg List.prod
    (List.map_congr_left fun x hx => rho_wordP_phi ρ v hfix hv u (hl x hx))

theorem rel_lt {c : ℕ} (hc : c < 3) : ∀ x ∈ rel c, x < 280 := by
  have hr := (checkB_spec.1 c hc).1
  have h1 := (checkA_spec.2.2.2 _ hr).2.2.2.1
  have h2 := (checkA_spec.2.2.2 _ h1).2.2.2.1
  intro x hx
  simp only [rel, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact hr
  · exact h1
  · exact h2

theorem prod_rel_fixed (hfix : ∀ x : V, ρ zJ x = x ↔ x = 1 ∨ x = v) (hv : v ≠ 1) {c : ℕ}
    (hc : c < 3) : ρ zJ ((rel c).map (phi ρ v)).prod = ((rel c).map (phi ρ v)).prod := by
  obtain ⟨hr, h3⟩ := checkB_spec.1 c hc
  have h1 := (checkA_spec.2.2.2 _ hr).2.2.2.1
  have h2 := (checkA_spec.2.2.2 _ h1).2.2.2.1
  simp only [rel, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_mul]
  rw [rho_z_phi ρ v hfix hv hr, rho_z_phi ρ v hfix hv h1, rho_z_phi ρ v hfix hv h2, h3]
  rw [mul_comm (phi ρ v reps[c]!), mul_assoc]

theorem prod_rel_eq (hV : ∀ x : V, x * x = 1) (hfix : ∀ x : V, ρ zJ x = x ↔ x = 1 ∨ x = v)
    (hv : v ≠ 1) {c : ℕ} (hc : c < 3) : ((rel c).map (phi ρ v)).prod = v := by
  classical
  set Φ : ℕ → V := fun c => ((rel c).map (phi ρ v)).prod with hΦ
  have hΦ1 : ∀ c < 3, Φ c = 1 ∨ Φ c = v := fun c hc => (hfix _).1 (prod_rel_fixed ρ v hfix hv hc)
  by_contra hne
  have hpat : ∀ b₀ b₁ b₂ : Bool, ¬ (b₀ = true ∧ b₁ = true ∧ b₂ = true) →
      ∃ p < 7, pats[p]! = [b₀, b₁, b₂] := by decide
  obtain ⟨p, hp, hpm⟩ := hpat (decide (Φ 0 = v)) (decide (Φ 1 = v)) (decide (Φ 2 = v)) (by
    simp only [decide_eq_true_eq]
    rintro ⟨h0, h1, h2⟩
    interval_cases c
    · exact hne h0
    · exact hne h1
    · exact hne h2)
  obtain ⟨hcls, hpar⟩ := checkB_spec.2 p hp
  rw [hpm] at hpar
  set m : List Bool := [decide (Φ 0 = v), decide (Φ 1 = v), decide (Φ 2 = v)] with hm
  have hrelmu : ∀ c < 3, ((relMu m c).map (phi ρ v)).prod = 1 := by
    intro c hc
    have hget : m.getD c false = decide (Φ c = v) := by
      interval_cases c <;> rfl
    rw [relMu, hget, List.map_append, List.prod_append]
    by_cases h : Φ c = v
    · rw [decide_eq_true h, if_pos rfl]
      change Φ c * _ = 1
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, phi_zero]
      rw [h, hV v]
    · rw [decide_eq_false h, if_neg Bool.false_ne_true]
      change Φ c * _ = 1
      rw [(hΦ1 c hc).resolve_right h]
      simp
  have hrelmu_lt : ∀ c < 3, ∀ x ∈ relMu m c, x < 280 := by
    intro c hc x hx
    rw [relMu, List.mem_append] at hx
    rcases hx with hx | hx
    · exact rel_lt hc x hx
    · split_ifs at hx
      · rw [List.mem_singleton] at hx
        rw [hx]
        norm_num
      · simp at hx
  have hlt : ∀ x ∈ combList m combs[p]!, x < 280 := by
    intro x hx
    simp only [combList, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨t, ht, y, hy, rfl⟩ := hx
    exact tab_lt _ (hrelmu_lt _ (hcls t ht) y hy)
  have h1 := prod_eq_of_parityOK hV (phi ρ v) hlt hpar
  rw [phi_zero] at h1
  have h2 : ((combList m combs[p]!).map (phi ρ v)).prod = 1 := by
    rw [combList, prod_map_flatMap]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    rw [← rho_wordP_prod ρ v hfix hv _ (hrelmu_lt _ (hcls t ht)), hrelmu _ (hcls t ht), map_one]
  exact hv (h1.symm.trans h2)

theorem prod_orbit_eq (hV : ∀ x : V, x * x = 1) (hfix : ∀ x : V, ρ zJ x = x ↔ x = 1 ∨ x = v)
    (hv : v ≠ 1) {j : ℕ} (hj : j < 280) :
    phi ρ v j * (phi ρ v tZ[j]! * phi ρ v tZ[tZ[j]!]!) = v := by
  by_cases h0 : j = 0
  · subst h0
    simp only [checkC_spec.1, phi_zero]
    rw [hV v, mul_one]
  · obtain ⟨hc, hu0, hperm⟩ := checkC_spec.2.2 j hj h0
    have h := prod_eq_of_permEq (phi ρ v) hperm
    rw [← rho_wordP_prod ρ v hfix hv _ (rel_lt hc), prod_rel_eq ρ v hV hfix hv hc] at h
    have hu : ρ (wordP (uOf j)) v = v := by
      conv_lhs => rw [← phi_zero ρ v]
      rw [rho_wordP_phi ρ v hfix hv _ (by norm_num : 0 < 280), hu0, phi_zero]
    rw [hu] at h
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using h.symm

theorem phi_eq (hV : ∀ x : V, x * x = 1)
    (hirr : ∀ W : Subgroup V, (∀ g : GJ, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hfix : ∀ x : V, ρ zJ x = x ↔ x = 1 ∨ x = v) (hv : v ≠ 1) {j : ℕ} (hj : j < 280) :
    phi ρ v j = v := by
  have hzv : ρ zJ v = v := (hfix v).2 (Or.inr rfl)
  set W : Subgroup V := Subgroup.closure (Set.range fun i : Fin 280 => phi ρ v i * v) with hW
  have hmemW : ∀ i < 280, phi ρ v i * v ∈ W := fun i hi =>
    Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
  have hgen : ∀ k : ℕ, ∀ w ∈ W, ρ (genP k) w ∈ W := by
    intro k w hw
    have hle : W ≤ W.comap (ρ (genP k)).toMonoidHom := by
      rw [hW, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, map_mul,
        SetLike.mem_coe]
      have h0 : ρ (genP k) v = phi ρ v (tabOf k)[0]! := by
        rw [← rho_genP_phi ρ v hfix hv k (by norm_num : 0 < 280), phi_zero]
      rw [rho_genP_phi ρ v hfix hv k i.2, h0]
      have e : phi ρ v (tabOf k)[(i : ℕ)]! * phi ρ v (tabOf k)[0]! =
          (phi ρ v (tabOf k)[(i : ℕ)]! * v) * (phi ρ v (tabOf k)[0]! * v) := by
        rw [mul_mul_mul_comm, hV v, mul_one]
      rw [e]
      exact W.mul_mem (hmemW _ (tabOf_lt k i.2)) (hmemW _ (tabOf_lt k (by norm_num)))
    exact hle hw
  have hinv : ∀ g : GJ, ∀ w ∈ W, ρ g w ∈ W := by
    refine forall_of_gens (p := fun g => ∀ w ∈ W, ρ g w ∈ W) (hgen 0) (hgen 1) ?_ ?_
    · intro w hw
      simpa using hw
    · intro g h hg hh w hw
      rw [map_mul, MulAut.mul_apply]
      exact hg _ (hh w hw)
  have hvW : v ∉ W := by
    intro hvW
    have key : ∀ w ∈ W, w * (ρ zJ w * ρ zJ (ρ zJ w)) = 1 := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        have h1 := (checkA_spec.2.2.2 i i.2).2.2.2.1
        simp only [map_mul, hzv]
        rw [rho_z_phi ρ v hfix hv i.2, rho_z_phi ρ v hfix hv h1]
        have h3 := prod_orbit_eq ρ v hV hfix hv i.2
        calc phi ρ v i * v * (phi ρ v tZ[(i : ℕ)]! * v * (phi ρ v tZ[tZ[(i : ℕ)]!]! * v))
            = (phi ρ v i * (phi ρ v tZ[(i : ℕ)]! * phi ρ v tZ[tZ[(i : ℕ)]!]!)) *
                (v * (v * v)) := by
              simp only [mul_assoc, mul_left_comm, mul_comm]
          _ = 1 := by rw [h3, hV v, mul_one, hV v]
      | one => simp
      | mul x y _ _ hx hy =>
        simp only [map_mul]
        calc x * y * (ρ zJ x * ρ zJ y * (ρ zJ (ρ zJ x) * ρ zJ (ρ zJ y)))
            = (x * (ρ zJ x * ρ zJ (ρ zJ x))) * (y * (ρ zJ y * ρ zJ (ρ zJ y))) := by
              simp only [mul_assoc, mul_left_comm, mul_comm]
          _ = 1 := by rw [hx, hy, mul_one]
      | inv x _ hx =>
        simp only [map_inv]
        rw [← mul_inv, ← mul_inv, hx, inv_one]
    have h := key v hvW
    rw [hzv, hzv, hV v, mul_one] at h
    exact hv h
  rcases hirr W hinv with hW0 | hW0
  · have h := hmemW j hj
    rw [hW0, Subgroup.mem_bot] at h
    calc phi ρ v j = phi ρ v j * v * v := by rw [mul_assoc, hV v, mul_one]
      _ = v := by rw [h, one_mul]
  · exact absurd (hW0 ▸ Subgroup.mem_top v) hvW

theorem card_eq_two (hV : ∀ x : V, x * x = 1)
    (hirr : ∀ W : Subgroup V, (∀ g : GJ, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hv : v ≠ 1) (hfix : ∀ x : V, ρ zJ x = x ↔ x = 1 ∨ x = v) : Nat.card V = 2 := by
  have hgv : ∀ k : ℕ, ρ (genP k) v = v := by
    intro k
    have h := rho_genP_phi ρ v hfix hv k (by norm_num : 0 < 280)
    rwa [phi_zero, phi_eq ρ v hV hirr hfix hv (tabOf_lt k (by norm_num))] at h
  have hall : ∀ g : GJ, ρ g v = v := by
    refine forall_of_gens (p := fun g => ρ g v = v) (hgv 0) (hgv 1) ?_ ?_
    · simp
    · intro g h hg hh
      rw [map_mul, MulAut.mul_apply, hh, hg]
  have hinv : ∀ g : GJ, ∀ w ∈ Subgroup.zpowers v, ρ g w ∈ Subgroup.zpowers v := by
    intro g w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [map_zpow, hall g]⟩
  rcases hirr _ hinv with h | h
  · exact absurd (Subgroup.zpowers_eq_bot.mp h) hv
  · rw [← Subgroup.card_top (G := V), ← h, Nat.card_zpowers,
      orderOf_eq_prime (by rw [sq]; exact hV v) hv]

end Module

end CFSG.RankThree.PartTwo.J2Residue.C280
