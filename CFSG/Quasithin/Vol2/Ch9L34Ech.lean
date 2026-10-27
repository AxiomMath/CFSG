module

public import CFSG.Quasithin.Vol2.Ch9L34QBnd
public import Mathlib.Data.LawfulXor.Basic
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.H13.Ch9.L34N

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.L34M

@[expose] def echOK : List ℕ → Bool
  | [] => true
  | a :: l => decide (a ≠ 0) && l.all (fun b => decide (b < 2 ^ Nat.log2 a)) && echOK l

theorem combos_nodup_of_echOK : ∀ {l : List ℕ}, echOK l = true → (combos l).Nodup
  | [], _ => List.nodup_singleton 0
  | a :: l, h => by
    simp only [echOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨ha, hl⟩, hrest⟩ := h
    have hlt : ∀ x ∈ combos l, x < 2 ^ Nat.log2 a := combos_lt hl
    rw [combos, List.nodup_append]
    refine ⟨combos_nodup_of_echOK hrest, ?_, ?_⟩
    · exact (combos_nodup_of_echOK hrest).map fun x y h => by
        simpa using congrArg (· ^^^ a) h
    · intro x hx y hy hxy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      have h1 : (z ^^^ a).testBit (Nat.log2 a) = true := by
        rw [Nat.testBit_xor, Nat.testBit_lt_two_pow (hlt z hz), Nat.testBit_log2 ha]
        rfl
      have h2 : x.testBit (Nat.log2 a) = false := Nat.testBit_lt_two_pow (hlt x hx)
      rw [hxy, h1] at h2
      exact absurd h2 (by decide)

@[expose] def pivOK (n : ℕ) (vs : List ℕ) : Bool :=
  (List.range n).all fun k => vs.any fun v => decide (2 ^ k ≤ v) && decide (v < 2 ^ (k + 1))

theorem xor_lt_of_pivot {k a b : ℕ} (ha : 2 ^ k ≤ a) (ha' : a < 2 ^ (k + 1)) (hb : 2 ^ k ≤ b)
    (hb' : b < 2 ^ (k + 1)) : a ^^^ b < 2 ^ k := by
  have hbit : ∀ x, 2 ^ k ≤ x → x < 2 ^ (k + 1) → x.testBit k = true := fun x h1 h2 => by
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le h1
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by rw [pow_succ] at h2; omega)]
    rfl
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_xor]
  rcases Nat.eq_or_lt_of_le hi with rfl | hlt
  · rw [hbit a ha ha', hbit b hb hb']
    rfl
  · have h1 : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hlt
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha' h1),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb' h1)]
    rfl

theorem closure_eq_top_of_pivOK {V : Type*} [CommGroup V] {n : ℕ} (c : MaskCoords V n)
    {vs : List ℕ} (h : pivOK n vs = true) : Subgroup.closure {v | ∃ w ∈ vs, c.vm w = v} = ⊤ := by
  set H := Subgroup.closure {v | ∃ w ∈ vs, c.vm w = v} with hH
  have hpiv : ∀ k < n, ∃ v ∈ vs, 2 ^ k ≤ v ∧ v < 2 ^ (k + 1) := by
    intro k hk
    have h1 := List.all_eq_true.1 h k (List.mem_range.2 hk)
    obtain ⟨v, hv, hv'⟩ := List.any_eq_true.1 h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv'
    exact ⟨v, hv, hv'⟩
  have key : ∀ k ≤ n, ∀ m < 2 ^ k, c.vm m ∈ H := by
    intro k
    induction k with
    | zero =>
      intro _ m hm
      rw [show m = 0 by simpa using hm, c.vm_zero]
      exact H.one_mem
    | succ k ih =>
      intro hk m hm
      by_cases hmk : m < 2 ^ k
      · exact ih (by omega) m hmk
      · obtain ⟨v, hv, hv1, hv2⟩ := hpiv k (by omega)
        have hx := xor_lt_of_pivot (not_lt.1 hmk) hm hv1 hv2
        have e : m = v ^^^ (m ^^^ v) := by
          rw [Nat.xor_comm m v, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        rw [e, c.vm_xor]
        exact H.mul_mem (Subgroup.subset_closure ⟨v, hv, rfl⟩) (ih (by omega) _ hx)
  rw [eq_top_iff]
  rintro x -
  obtain ⟨m, hm, rfl⟩ := c.vm_surj x
  exact key n le_rfl m hm

theorem xor_div_two_pow (a b n : ℕ) : (a ^^^ b) / 2 ^ n = a / 2 ^ n ^^^ b / 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_div_two_pow, Nat.testBit_xor]

@[expose] def prodCoords {V V' : Type*} [CommGroup V] [CommGroup V'] {n n' : ℕ}
    (c : MaskCoords V n) (c' : MaskCoords V' n') : MaskCoords (V × V') (n + n') where
  vm m := (c.vm m, c'.vm (m / 2 ^ n))
  vm_xor a b := by
    rw [c.vm_xor, xor_div_two_pow, c'.vm_xor]
    rfl
  vm_mod a := by
    refine Prod.ext ?_ ?_
    · show c.vm (a % 2 ^ (n + n')) = c.vm a
      rw [← c.vm_mod (a % 2 ^ (n + n')), ← c.vm_mod a, Nat.mod_mod_of_dvd _
        (pow_dvd_pow 2 (Nat.le_add_right n n'))]
    · show c'.vm (a % 2 ^ (n + n') / 2 ^ n) = c'.vm (a / 2 ^ n)
      rw [← c'.vm_mod (a % 2 ^ (n + n') / 2 ^ n), ← c'.vm_mod (a / 2 ^ n)]
      congr 1
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      by_cases hi : i < n'
      · simp [hi, show i + n < n + n' by omega]
      · simp [hi]
  vm_inj a b ha hb h := by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    rw [← c.vm_mod a, ← c.vm_mod b] at h1
    have e1 := c.vm_inj _ _ (Nat.mod_lt _ (Nat.two_pow_pos n)) (Nat.mod_lt _ (Nat.two_pow_pos n)) h1
    have hlt : ∀ x < 2 ^ (n + n'), x / 2 ^ n < 2 ^ n' := fun x hx => by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n), ← pow_add, add_comm]
      exact hx
    have e2 := c'.vm_inj _ _ (hlt a ha) (hlt b hb) h2
    rw [← Nat.div_add_mod a (2 ^ n), ← Nat.div_add_mod b (2 ^ n), e1, e2]
  vm_surj v := by
    obtain ⟨y, hy, hyv⟩ := c.vm_surj v.1
    obtain ⟨z, hz, hzv⟩ := c'.vm_surj v.2
    refine ⟨y + 2 ^ n * z, ?_, Prod.ext ?_ ?_⟩
    · have h1 : 2 ^ n * z + 2 ^ n ≤ 2 ^ n * 2 ^ n' := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ hz
      rw [pow_add]
      omega
    · show c.vm (y + 2 ^ n * z) = v.1
      rw [← c.vm_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy, hyv]
    · show c'.vm ((y + 2 ^ n * z) / 2 ^ n) = v.2
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt hy, zero_add, hzv]

theorem prodCoords_vm {V V' : Type*} [CommGroup V] [CommGroup V'] {n n' : ℕ}
    (c : MaskCoords V n) (c' : MaskCoords V' n') (m : ℕ) :
    (prodCoords c c').vm m = (c.vm m, c'.vm (m / 2 ^ n)) := rfl

theorem prodCoords_vm_add {V V' : Type*} [CommGroup V] [CommGroup V'] {n n' : ℕ}
    (c : MaskCoords V n) (c' : MaskCoords V' n') {a : ℕ} (ha : a < 2 ^ n) (b : ℕ) :
    (prodCoords c c').vm (a + 2 ^ n * b) = (c.vm a, c'.vm b) := by
  rw [prodCoords_vm]
  refine Prod.ext ?_ ?_
  · show c.vm (a + 2 ^ n * b) = c.vm a
    rw [← c.vm_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · show c'.vm ((a + 2 ^ n * b) / 2 ^ n) = c'.vm b
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt ha, zero_add]

section Four

variable {V : Type*} [CommGroup V] {n : ℕ} (c : MaskCoords V n)

@[expose] def dif (cs : List ℕ) (w : ℕ) : ℕ := actM cs w ^^^ w

@[expose] def stack4 (n : ℕ) (cs₁ cs₂ cs₃ cs₄ : List ℕ) (w : ℕ) : ℕ :=
  (dif cs₁ w + 2 ^ n * dif cs₂ w) + 2 ^ (n + n) * (dif cs₃ w + 2 ^ n * dif cs₄ w)

theorem dif_lt {cs : List ℕ} (hcs : AllLt n cs = true) {w : ℕ} (hw : w < 2 ^ n) :
    dif cs w < 2 ^ n :=
  Nat.xor_lt_two_pow (actM_lt (allLt_spec hcs) w) hw

theorem two_pow_mul_card_le_four {s₁ s₂ s₃ s₄ : MulAut V} {cs₁ cs₂ cs₃ cs₄ : List ℕ}
    (h₁ : ActsBy c s₁ cs₁) (h₂ : ActsBy c s₂ cs₂) (h₃ : ActsBy c s₃ cs₃) (h₄ : ActsBy c s₄ cs₄)
    (hc₁ : AllLt n cs₁ = true) (hc₂ : AllLt n cs₂ = true) (hc₃ : AllLt n cs₃ = true)
    (hc₄ : AllLt n cs₄ = true) {ws : List ℕ} (hws : AllLt n ws = true)
    (hech : echOK (ws.map (stack4 n cs₁ cs₂ cs₃ cs₄)) = true) {F : Subgroup V}
    (hF : ∀ v ∈ F, s₁ v = v ∧ s₂ v = v ∧ s₃ v = v ∧ s₄ v = v) :
    2 ^ ws.length * Nat.card F ≤ 2 ^ n := by
  have := finite_of_coords c
  set c4 := prodCoords (prodCoords c c) (prodCoords c c) with hc4
  let D : V →* (V × V) × (V × V) :=
    ((commHom s₁).prod (commHom s₂)).prod ((commHom s₃).prod (commHom s₄))
  have hD : ∀ v, D v = ((s₁ v * v, s₂ v * v), (s₃ v * v, s₄ v * v)) := fun v => rfl
  have hFk : F ≤ D.ker := fun v hv => by
    obtain ⟨e₁, e₂, e₃, e₄⟩ := hF v hv
    rw [MonoidHom.mem_ker, hD, e₁, e₂, e₃, e₄, mul_self_of_coords c]
    rfl
  have hmask : ∀ w < 2 ^ n, D (c.vm w) = c4.vm (stack4 n cs₁ cs₂ cs₃ cs₄ w) := by
    intro w hw
    have hd : ∀ (s : MulAut V) (cs : List ℕ), ActsBy c s cs → s (c.vm w) * c.vm w =
        c.vm (dif cs w) := fun s cs hs => by rw [hs w hw, ← c.vm_xor]; rfl
    have hl₁₂ : dif cs₁ w + 2 ^ n * dif cs₂ w < 2 ^ (n + n) := by
      have h1 := dif_lt hc₁ hw
      have h2 := dif_lt hc₂ hw
      have h3 : 2 ^ n * dif cs₂ w + 2 ^ n ≤ 2 ^ n * 2 ^ n := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ h2
      rw [pow_add]
      omega
    rw [hD, hd s₁ cs₁ h₁, hd s₂ cs₂ h₂, hd s₃ cs₃ h₃, hd s₄ cs₄ h₄, stack4,
      prodCoords_vm_add _ _ hl₁₂, prodCoords_vm_add _ _ (dif_lt hc₁ hw),
      prodCoords_vm_add _ _ (dif_lt hc₃ hw)]
  have hlt : ∀ a ∈ ws.map (stack4 n cs₁ cs₂ cs₃ cs₄), a < 2 ^ (n + n + (n + n)) := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    have hw' := allLt_spec hws w hw
    have hb : ∀ cs cs' : List ℕ, AllLt n cs = true → AllLt n cs' = true →
        dif cs w + 2 ^ n * dif cs' w < 2 ^ (n + n) := fun cs cs' hcs hcs' => by
      have h1 := dif_lt hcs hw'
      have h2 := dif_lt hcs' hw'
      have h3 : 2 ^ n * dif cs' w + 2 ^ n ≤ 2 ^ n * 2 ^ n := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ h2
      rw [pow_add]
      omega
    have e1 := hb cs₁ cs₂ hc₁ hc₂
    have e2 := hb cs₃ cs₄ hc₃ hc₄
    have h3 : 2 ^ (n + n) * (dif cs₃ w + 2 ^ n * dif cs₄ w) + 2 ^ (n + n) ≤
        2 ^ (n + n) * 2 ^ (n + n) := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ e2
    rw [stack4, pow_add 2 (n + n)]
    omega
  have hmem : ∀ a ∈ ws.map (stack4 n cs₁ cs₂ cs₃ cs₄), c4.vm a ∈ D.range := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    exact ⟨c.vm w, hmask w (allLt_spec hws w hw)⟩
  have h1 := c4.pow_le_card D.range _ (combos_nodup_of_echOK hech) hlt hmem
  rw [List.length_map] at h1
  have h2 : Nat.card D.ker * Nat.card D.range = 2 ^ n := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, card_of_coords c]
  have h3 : Nat.card F ≤ Nat.card D.ker := Subgroup.card_le_of_le hFk
  calc 2 ^ ws.length * Nat.card F ≤ Nat.card D.range * Nat.card D.ker := Nat.mul_le_mul h1 h3
    _ = 2 ^ n := by rw [mul_comm, h2]

end Four

@[expose] def insFst {β : Type*} (r : ℕ × β) : List (ℕ × β) → List (ℕ × β)
  | [] => [r]
  | b :: bs => if b.1 < r.1 then r :: b :: bs else b :: insFst r bs

@[expose] def redBy {β : Type*} (op : β → β → β) (basis : List (ℕ × β)) (x : ℕ × β) : ℕ × β :=
  basis.foldl (fun acc b => if acc.1.testBit (Nat.log2 b.1) then (acc.1 ^^^ b.1, op acc.2 b.2)
    else acc) x

@[expose] def echAux {β : Type*} (op : β → β → β) : List (ℕ × β) → List (ℕ × β) → List (ℕ × β)
  | [], basis => basis
  | x :: xs, basis =>
    let r := redBy op basis x
    echAux op xs (if r.1 = 0 then basis else insFst r basis)

@[expose] def echKer (n : ℕ) (f : ℕ → ℕ) : List ℕ :=
  (echAux (· ^^^ ·) ((List.range n).map fun j => (f (2 ^ j), 2 ^ j)) []).map Prod.snd

@[expose] def echComb (os : List ℕ) : List (ℕ × ℕ) :=
  echAux (· ^^^ ·) ((List.range os.length).map fun i => (os.getD i 0, 2 ^ i)) []

@[expose] def sel (os : List ℕ) (k : ℕ) : List ℕ :=
  ((List.range os.length).filter fun i => k.testBit i).map fun i => os.getD i 0

@[expose] def combOK (os : List ℕ) (ps : List (ℕ × ℕ)) : Bool :=
  ps.all fun p => p.1 == xorAll (sel os p.2)

theorem vm_xorAll {V : Type*} [CommGroup V] {n : ℕ} (c : MaskCoords V n) :
    ∀ s : List ℕ, (s.map c.vm).prod = c.vm (xorAll s)
  | [] => by simp [xorAll, c.vm_zero]
  | a :: s => by rw [List.map_cons, List.prod_cons, vm_xorAll c s, xorAll, c.vm_xor]

theorem eq_top_of_comb {V : Type*} [CommGroup V] {n : ℕ} (c : MaskCoords V n) {os : List ℕ}
    {ps : List (ℕ × ℕ)} (hc : combOK os ps = true) (hp : pivOK n (ps.map Prod.fst) = true)
    {H : Subgroup V} (hH : ∀ o ∈ os, c.vm o ∈ H) : H = ⊤ := by
  have hget : ∀ i, c.vm (os.getD i 0) ∈ H := fun i => by
    by_cases hi : i < os.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hH _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (not_lt.1 hi), c.vm_zero]
      exact H.one_mem
  have hps : ∀ w ∈ ps.map Prod.fst, c.vm w ∈ H := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    have h1 := List.all_eq_true.1 hc p hp
    rw [beq_iff_eq] at h1
    rw [h1, ← vm_xorAll c]
    refine Subgroup.list_prod_mem H fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rw [sel] at hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact hget i
  rw [eq_top_iff, ← closure_eq_top_of_pivOK c hp, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact hps w hw

theorem mem_fixV_closure {V : Type*} [CommGroup V] {S : Set (MulAut V)} {v : V}
    (h : ∀ s ∈ S, s v = v) : v ∈ fixV (Subgroup.closure S) := by
  intro x hx
  have hle : Subgroup.closure S ≤ MulAction.stabilizer (MulAut V) v :=
    (Subgroup.closure_le _).2 fun s hs => MulAction.mem_stabilizer_iff.2 (h s hs)
  exact MulAction.mem_stabilizer_iff.1 (hle hx)

end CFSG.Quasithin.H13.Ch9.L34N
