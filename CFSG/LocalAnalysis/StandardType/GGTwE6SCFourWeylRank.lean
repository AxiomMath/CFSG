module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourWeylGram

public section

namespace CFSG.StandardType.SCFourCover.WeylFix

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg

private theorem card_le_of_det {K : Type*} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}
    {P : Fin 3 → Fin n → K} (c : Fin 3 → Fin n)
    (hdet : (Matrix.of fun r s => P r (c s)).det ≠ 0) {V : Finset (Fin n → K)}
    (hV : ∀ b ∈ V, ∀ r, ∑ k, b k * P r k = 0) : V.card ≤ Fintype.card K ^ (n - 3) := by
  have hc : Function.Injective c := fun s s' h => by
    by_contra hne
    exact hdet (Matrix.det_zero_of_column_eq hne fun r => by simp [h])
  set T : Finset (Fin n) := (Finset.univ.image c)ᶜ
  have hT : T.card = n - 3 := by
    rw [Finset.card_compl, Finset.card_image_of_injective _ hc, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin]
  have hinj : Set.InjOn (fun (b : Fin n → K) (k : T) => b k) V := by
    intro b hb b' hb' h
    have hx : ∀ k ∈ T, b k - b' k = 0 := fun k hk => sub_eq_zero.2 (congrFun h ⟨k, hk⟩)
    have hsum : ∀ r, ∑ s, P r (c s) * (b (c s) - b' (c s)) = 0 := by
      intro r
      rw [← Finset.sum_image (f := fun k => P r k * (b k - b' k)) fun s _ s' _ h => hc h,
        Finset.sum_subset (Finset.subset_univ _) fun k _ hk => by
          rw [hx k (Finset.mem_compl.2 hk), mul_zero]]
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl fun k _ => mul_comm (P r k) (b k), hV b hb r,
        Finset.sum_congr rfl fun k _ => mul_comm (P r k) (b' k), hV b' hb' r, sub_zero]
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet (v := fun s => b (c s) - b' (c s))
      (funext fun r => by simpa [Matrix.mulVec, dotProduct] using hsum r)
    funext k
    by_cases hk : k ∈ T
    · exact sub_eq_zero.1 (hx k hk)
    · obtain ⟨s, rfl⟩ : ∃ s, c s = k := by simpa [T] using hk
      exact sub_eq_zero.1 (congrFun h0 s)
  calc V.card ≤ (Finset.univ : Finset (T → K)).card :=
        Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = Fintype.card K ^ (n - 3) := by simp [hT]

private theorem bif_beq (k j : ℕ) :
    (bif Nat.beq k j then 2 else 0 : ℕ) = if k = j then 2 else 0 := by
  cases h : Nat.beq k j
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

private theorem dv_cast {a : ℕ} (ha : a < 72) (j k : Fin Tag.E6.rank) :
    ((dv j a k : ℕ) : ZMod 3) =
      (((e6Certificate.root a - Pi.single j 1 : Fin Tag.E6.rank → ℤ) k : ℤ) : ZMod 3) := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  rw [dv, ZMod.natCast_mod, Nat.cast_add, r3_cast ha, bif_beq, Pi.sub_apply, Pi.single_apply]
  by_cases h : k = j
  · subst h
    simp only [if_true]
    push_cast
    linear_combination h3
  · simp only [if_neg (show (k : ℕ) ≠ j from fun e => h (Fin.ext e)), if_neg h]
    push_cast
    ring

private theorem det3N_cast (w : Fin 3 → ℕ × ℕ) (c : Fin 3 → Fin Tag.E6.rank) :
    ((det3N (w 0) (w 1) (w 2) (c 0) (c 1) (c 2) : ℕ) : ZMod 3) =
      (Matrix.of fun r s => ((dv (w r).1 (w r).2 (c s) : ℕ) : ZMod 3)).det := by
  rw [Matrix.det_fin_three]
  simp only [det3N, Matrix.of_apply, ZMod.natCast_mod]
  push_cast
  ring_nf
  reduce_mod_char
  ring

def OrthRow (V : Finset (Fin Tag.E6.rank → ZMod 3)) (j a : ℕ) : Prop :=
  ∀ b ∈ V, ∑ k : Fin Tag.E6.rank, b k * ((dv j a k : ℕ) : ZMod 3) = 0

private theorem mem_of_mem_pairsOf {α : Type} {x y : α} :
    ∀ {l : List α}, (x, y) ∈ pairsOf l → x ∈ l ∧ y ∈ l
  | [], h => by simp [pairsOf] at h
  | z :: zs, h => by
    simp only [pairsOf, List.mem_append, List.mem_map, Prod.mk.injEq] at h
    rcases h with ⟨w, hw, rfl, rfl⟩ | h
    · exact ⟨List.mem_cons.2 (Or.inl rfl), List.mem_cons_of_mem _ hw⟩
    · obtain ⟨h1, h2⟩ := mem_of_mem_pairsOf h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

private theorem natCast_ne_zero_of_lt {n : ℕ} (h3 : n < 3) (h0 : n ≠ 0) :
    ((n : ℕ) : ZMod 3) ≠ 0 := by
  interval_cases n <;> first | exact absurd rfl h0 | decide

theorem prune_eq_false_of_card {V : Finset (Fin Tag.E6.rank → ZMod 3)} (hV : 27 < V.card)
    {olds : List (ℕ × ℕ)} {v : ℕ × ℕ} (ho : ∀ p ∈ olds, OrthRow V p.1 p.2)
    (hv : OrthRow V v.1 v.2) : prune olds v = false := by
  unfold prune
  split
  · rfl
  · rename_i p q c1 c2 hb
    obtain ⟨pq, hpq, hf⟩ := List.exists_of_findSome?_eq_some hb
    obtain ⟨cc, hc, hmap⟩ := Option.map_eq_some_iff.1 hf
    simp only [Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmap
    have hcc := List.mem_of_find?_eq_some hc
    have hc6 : cc.1 < 6 ∧ cc.2 < 6 := by
      revert hcc
      simp only [cols2, List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h]
    obtain ⟨hp, hq⟩ := mem_of_mem_pairsOf hpq
    rw [List.any_eq_false]
    intro c3 hc3 hdet
    rw [List.mem_range] at hc3
    have hne : det3N pq.1 pq.2 v cc.1 cc.2 c3 ≠ 0 := by simpa using hdet
    let w : Fin 3 → ℕ × ℕ := ![pq.1, pq.2, v]
    let c : Fin 3 → Fin Tag.E6.rank := ![⟨cc.1, hc6.1⟩, ⟨cc.2, hc6.2⟩, ⟨c3, hc3⟩]
    have hdet0 : (Matrix.of fun r s => ((dv (w r).1 (w r).2 (c s) : ℕ) : ZMod 3)).det ≠ 0 := by
      rw [← det3N_cast w c]
      exact natCast_ne_zero_of_lt (Nat.mod_lt _ (by decide)) hne
    have hcard := card_le_of_det (P := fun r k => ((dv (w r).1 (w r).2 k : ℕ) : ZMod 3)) c hdet0
      (V := V) fun b hb r => by
        fin_cases r
        · exact ho _ hp b hb
        · exact ho _ hq b hb
        · exact hv b hb
    have h27 : Fintype.card (ZMod 3) ^ (Tag.E6.rank - 3) = 27 := by
      rw [ZMod.card]
      rfl
    omega

theorem orthRow_of_fix {V : Finset (Fin Tag.E6.rank → ZMod 3)} {u : WeylGroup Tag.E6}
    (hu : ∀ b ∈ V, ∀ v, triPairing b (u • v) = triPairing b v) {a : ℕ} (ha : a < 72)
    {j : Fin Tag.E6.rank} (hj : e6Certificate.root a = u • Pi.single j 1) : OrthRow V j a := by
  intro b hb
  have e : ∑ k : Fin Tag.E6.rank, b k * ((dv j a k : ℕ) : ZMod 3) =
      triPairing b (e6Certificate.root a - Pi.single j 1) :=
    Finset.sum_congr rfl fun k _ => by rw [dv_cast ha]
  have h1 := triPairing_add b (e6Certificate.root a - Pi.single j 1) (Pi.single j 1)
  rw [sub_add_cancel] at h1
  have h2 : triPairing b (e6Certificate.root a) = triPairing b (Pi.single j 1) := by
    rw [hj, hu b hb]
  rw [e]
  linear_combination h2 - h1

private theorem sum_comb6 {R : Type*} [CommRing R] {n : ℕ} (b : Fin n → R)
    (x₀ x₁ x₂ x₃ x₄ x₅ : R) {d₀ d₁ d₂ d₃ d₄ d₅ : Fin n → R} (h₀ : ∑ k, b k * d₀ k = 0)
    (h₁ : ∑ k, b k * d₁ k = 0) (h₂ : ∑ k, b k * d₂ k = 0) (h₃ : ∑ k, b k * d₃ k = 0)
    (h₄ : ∑ k, b k * d₄ k = 0) (h₅ : ∑ k, b k * d₅ k = 0) :
    ∑ k, b k * (x₀ * d₀ k + x₁ * d₁ k + x₂ * d₂ k + x₃ * d₃ k + x₄ * d₄ k + x₅ * d₅ k) = 0 := by
  have e : ∀ k, b k * (x₀ * d₀ k + x₁ * d₁ k + x₂ * d₂ k + x₃ * d₃ k + x₄ * d₄ k + x₅ * d₅ k) =
      x₀ * (b k * d₀ k) + x₁ * (b k * d₁ k) + x₂ * (b k * d₂ k) + x₃ * (b k * d₃ k) +
        x₄ * (b k * d₄ k) + x₅ * (b k * d₅ k) := fun k => by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h₀, h₁, h₂, h₃, h₄, h₅, mul_zero,
    add_zero]

theorem triPairing_eq_zero_of_coefOK {V : Finset (Fin Tag.E6.rank → ZMod 3)} {t : List ℕ}
    (ho : ∀ j < 6, OrthRow V j (t.getD j 0)) {p : ℕ × ℕ} (hp : p.1 < 72)
    (hc : coefOK t p = true) : ∀ b ∈ V, triPairing b (e6Certificate.root p.1) = 0 := by
  intro b hb
  have h3 : (3 : ZMod 3) = 0 := by decide
  simp only [coefOK, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  have hk : ∀ k : Fin Tag.E6.rank, ((e6Certificate.root p.1 k : ℤ) : ZMod 3) =
      ((p.2 % 3 : ℕ) : ZMod 3) * ((dv 0 (t.getD 0 0) k : ℕ) : ZMod 3) +
      ((p.2 / 3 % 3 : ℕ) : ZMod 3) * ((dv 1 (t.getD 1 0) k : ℕ) : ZMod 3) +
      ((p.2 / 9 % 3 : ℕ) : ZMod 3) * ((dv 2 (t.getD 2 0) k : ℕ) : ZMod 3) +
      ((p.2 / 27 % 3 : ℕ) : ZMod 3) * ((dv 3 (t.getD 3 0) k : ℕ) : ZMod 3) +
      ((p.2 / 81 % 3 : ℕ) : ZMod 3) * ((dv 4 (t.getD 4 0) k : ℕ) : ZMod 3) +
      ((p.2 / 243 % 3 : ℕ) : ZMod 3) * ((dv 5 (t.getD 5 0) k : ℕ) : ZMod 3) := by
    intro k
    have h0 : ((comb t p.2 k + 2 * r3 p.1 k : ℕ) : ZMod 3) = 0 := by
      rw [← ZMod.natCast_mod, hc k k.2, Nat.cast_zero]
    rw [← r3_cast hp k]
    simp only [comb, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h0
    linear_combination -h0 + ((r3 p.1 k : ℕ) : ZMod 3) * h3
  simp only [triPairing, hk]
  exact sum_comb6 b _ _ _ _ _ _ (ho 0 (by decide) b hb) (ho 1 (by decide) b hb)
    (ho 2 (by decide) b hb) (ho 3 (by decide) b hb) (ho 4 (by decide) b hb)
    (ho 5 (by decide) b hb)

end CFSG.StandardType.SCFourCover.WeylFix

end
