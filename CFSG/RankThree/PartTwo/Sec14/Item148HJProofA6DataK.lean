module

public import CFSG.Permutation.FinPackPow

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148HJK

open Equiv Equiv.Perm CFSG.Permutation.FinPack

theorem h16 : 6 ≤ 16 := by norm_num

@[expose] noncomputable def cjK (C Ci u : ℕ) : ℕ := mulK 6 (mulK 6 C u) Ci

@[expose] noncomputable def o3K (E w : ℕ) : Bool := !Nat.beq w E && Nat.beq (powK 6 E w 3) E

@[expose] noncomputable def w3K (C Ci E u : ℕ) : Bool :=
  o3K E (mulK 6 (mulK 6 (mulK 6 u u) (cjK C Ci u)) (cjK C Ci (cjK C Ci u))) ||
    o3K E (mulK 6 (mulK 6 (mulK 6 u u) (cjK C Ci (cjK C Ci u))) (cjK C Ci u)) ||
    o3K E (mulK 6 (mulK 6 (mulK 6 u (cjK C Ci u)) u) (cjK C Ci (cjK C Ci u)))

@[expose] noncomputable def qW3 (C Ci E : ℕ) (L : List ℕ) (u : ℕ) : Bool :=
  !evenK 6 u || Nat.beq u E || memK u L || w3K C Ci E u

@[expose] noncomputable def qThree (E : ℕ) (L : List ℕ) (y : ℕ) : Bool :=
  Nat.beq y E || !Nat.beq (powK 6 E y 3) E ||
    allK (fun u => !Nat.beq (mulK 6 u y) (mulK 6 y u)) L

@[expose] noncomputable def qFive (C Ci E : ℕ) (y : ℕ) : Bool :=
  Nat.beq y E || !Nat.beq (powK 6 E y 5) E ||
    (!Nat.beq (cjK C Ci y) y && !Nat.beq (cjK C Ci y) (powK 6 E y 2) &&
      !Nat.beq (cjK C Ci y) (powK 6 E y 3) && !Nat.beq (cjK C Ci y) (powK 6 E y 4))

variable {c : Perm (Fin 6)} {l : List (Perm (Fin 6))} {C Ci E : ℕ} {L : List ℕ}

theorem cjK_enc (hC : enc c = C) (hCi : enc c⁻¹ = Ci) (u : Perm (Fin 6)) :
    cjK C Ci (enc u) = enc (c * u * c⁻¹) := by
  rw [cjK, ← hC, ← hCi, enc_mul h16, enc_mul h16]

theorem ne_of_beq {σ τ : Perm (Fin 6)} (h : Nat.beq (enc σ) (enc τ) = false) : σ ≠ τ :=
  fun e => by
    rw [e, Nat.beq_refl] at h
    cases h

theorem o3K_sound (hE : enc (1 : Perm (Fin 6)) = E) (w : Perm (Fin 6)) (h : o3K E (enc w) = true) :
    w ≠ 1 ∧ w ^ 3 = 1 := by
  rw [o3K.eq_1, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  rw [← enc_pow h16 hE, ← hE] at h2
  rw [← hE] at h1
  exact ⟨ne_of_beq h1, (beq_enc_iff h16).1 h2⟩

theorem memK_enc (hL : l.map enc = L) (u : Perm (Fin 6)) : memK (enc u) L = true ↔ u ∈ l := by
  rw [memK_iff, ← hL, ← mem_iff_enc h16]

theorem w3_of (hC : enc c = C) (hCi : enc c⁻¹ = Ci) (hE : enc (1 : Perm (Fin 6)) = E)
    (hL : l.map enc = L) (h : walkK 6 (qW3 C Ci E L) 6 0 0 0 = true) :
    ∀ u : Perm (Fin 6), Perm.sign u = 1 → u ≠ 1 → u ∉ l →
      (u * u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) ≠ 1 ∧
          (u * u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹)) ^ 3 = 1) ∨
        (u * u * (c * (c * u * c⁻¹) * c⁻¹) * (c * u * c⁻¹) ≠ 1 ∧
          (u * u * (c * (c * u * c⁻¹) * c⁻¹) * (c * u * c⁻¹)) ^ 3 = 1) ∨
        (u * (c * u * c⁻¹) * u * (c * (c * u * c⁻¹) * c⁻¹) ≠ 1 ∧
          (u * (c * u * c⁻¹) * u * (c * (c * u * c⁻¹) * c⁻¹)) ^ 3 = 1) := by
  intro u h1 h2 h3
  have hw := walkK_sound h u
  have e2 : Nat.beq (enc u) E = false := by
    rw [← hE]
    exact beq_enc_false h16 h2
  have e3 : memK (enc u) L = false := Bool.eq_false_iff.2 fun e => h3 ((memK_enc hL u).1 e)
  rw [qW3.eq_1, (sign_eq_one_iff_evenK h16 u).1 h1, e2, e3] at hw
  simp only [Bool.not_true, Bool.false_or] at hw
  rw [w3K.eq_1, cjK_enc hC hCi u, cjK_enc hC hCi (c * u * c⁻¹)] at hw
  simp only [← enc_mul h16, Bool.or_eq_true] at hw
  rcases hw with (e | e) | e
  · exact Or.inl (o3K_sound hE _ e)
  · exact Or.inr (Or.inl (o3K_sound hE _ e))
  · exact Or.inr (Or.inr (o3K_sound hE _ e))

theorem three_of (hE : enc (1 : Perm (Fin 6)) = E) (hL : l.map enc = L)
    (h : walkK 6 (qThree E L) 6 0 0 0 = true) :
    ∀ y : Perm (Fin 6), y ≠ 1 → y ^ 3 = 1 → ∀ u ∈ l, u * y ≠ y * u := by
  intro y h1 h2 u hu
  have hw := walkK_sound h y
  have e1 : Nat.beq (enc y) E = false := by
    rw [← hE]
    exact beq_enc_false h16 h1
  have e2 : Nat.beq (powK 6 E (enc y) 3) E = true := by
    rw [← enc_pow h16 hE, ← hE, beq_enc_iff h16]
    exact h2
  rw [qThree.eq_1, e1, e2] at hw
  simp only [Bool.not_true, Bool.false_or] at hw
  have hm : enc u ∈ L := by
    rw [← hL]
    exact List.mem_map_of_mem hu
  have hk := allK_iff.1 hw (enc u) hm
  simp only [Bool.not_eq_true'] at hk
  rw [← enc_mul h16, ← enc_mul h16] at hk
  exact ne_of_beq hk

theorem five_of (hC : enc c = C) (hCi : enc c⁻¹ = Ci) (hE : enc (1 : Perm (Fin 6)) = E)
    (h : walkK 6 (qFive C Ci E) 6 0 0 0 = true) :
    ∀ y : Perm (Fin 6), y ≠ 1 → y ^ 5 = 1 →
      c * y * c⁻¹ ≠ y ∧ c * y * c⁻¹ ≠ y ^ 2 ∧ c * y * c⁻¹ ≠ y ^ 3 ∧ c * y * c⁻¹ ≠ y ^ 4 := by
  intro y h1 h2
  have hw := walkK_sound h y
  have e1 : Nat.beq (enc y) E = false := by
    rw [← hE]
    exact beq_enc_false h16 h1
  have e2 : Nat.beq (powK 6 E (enc y) 5) E = true := by
    rw [← enc_pow h16 hE, ← hE, beq_enc_iff h16]
    exact h2
  rw [qFive.eq_1, e1, e2] at hw
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hw
  rw [cjK_enc hC hCi y, ← enc_pow h16 hE, ← enc_pow h16 hE, ← enc_pow h16 hE] at hw
  obtain ⟨⟨⟨f1, f2⟩, f3⟩, f4⟩ := hw
  exact ⟨ne_of_beq f1, ne_of_beq f2, ne_of_beq f3, ne_of_beq f4⟩

@[expose] noncomputable def inSK (C Ci u v : ℕ) : Bool :=
  Nat.beq v u || (Nat.beq v (cjK C Ci u) || Nat.beq v (mulK 6 u (cjK C Ci u)))

theorem inSK_iff (hC : enc c = C) (hCi : enc c⁻¹ = Ci) (u v : Perm (Fin 6)) :
    inSK C Ci (enc u) (enc v) = true ↔ v = u ∨ v = c * u * c⁻¹ ∨ v = u * (c * u * c⁻¹) := by
  rw [inSK.eq_1, cjK_enc hC hCi, ← enc_mul h16]
  simp only [Bool.or_eq_true, beq_enc_iff h16]

@[expose] noncomputable def listK (C Ci E : ℕ) (L : List ℕ) : Bool :=
  allK (fun u => (Nat.beq (mulK 6 u u) E && (!Nat.beq u E && (memK (cjK C Ci u) L &&
      (Nat.beq (mulK 6 u (cjK C Ci u)) (cjK C Ci (cjK C Ci u)) &&
        Nat.beq (mulK 6 u (cjK C Ci u)) (mulK 6 (cjK C Ci u) u))))) &&
    allK (fun v => (inSK C Ci u v || (!Nat.beq (mulK 6 u v) E && !memK (mulK 6 u v) L)) &&
      (!inSK C Ci u v || inSK C Ci v u)) L) L

theorem list_of (hC : enc c = C) (hCi : enc c⁻¹ = Ci) (hE : enc (1 : Perm (Fin 6)) = E)
    (hL : l.map enc = L) (h : listK C Ci E L = true) :
    (∀ u ∈ l, u * u = 1 ∧ u ≠ 1 ∧ c * u * c⁻¹ ∈ l ∧
      u * (c * u * c⁻¹) = c * (c * u * c⁻¹) * c⁻¹ ∧ u * (c * u * c⁻¹) = c * u * c⁻¹ * u) ∧
    (∀ u ∈ l, ∀ v ∈ l, (v = u ∨ v = c * u * c⁻¹ ∨ v = u * (c * u * c⁻¹)) ∨
      (u * v ≠ 1 ∧ u * v ∉ l)) ∧
    (∀ u ∈ l, ∀ v ∈ l, (v = u ∨ v = c * u * c⁻¹ ∨ v = u * (c * u * c⁻¹)) →
      (u = v ∨ u = c * v * c⁻¹ ∨ u = v * (c * v * c⁻¹))) := by
  have hm : ∀ {a : Perm (Fin 6)}, a ∈ l → enc a ∈ L := fun h' => by
    rw [← hL]
    exact List.mem_map_of_mem h'
  have H : ∀ u ∈ l, ∀ v ∈ l, (u * u = 1 ∧ u ≠ 1 ∧ c * u * c⁻¹ ∈ l ∧
      u * (c * u * c⁻¹) = c * (c * u * c⁻¹) * c⁻¹ ∧ u * (c * u * c⁻¹) = c * u * c⁻¹ * u) ∧
      ((v = u ∨ v = c * u * c⁻¹ ∨ v = u * (c * u * c⁻¹)) ∨ (u * v ≠ 1 ∧ u * v ∉ l)) ∧
      ((v = u ∨ v = c * u * c⁻¹ ∨ v = u * (c * u * c⁻¹)) →
        (u = v ∨ u = c * v * c⁻¹ ∨ u = v * (c * v * c⁻¹))) := by
    intro u hu v hv
    have hx := allK_iff.1 h (enc u) (hm hu)
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, hx⟩ := hx
    have hy := allK_iff.1 hx (enc v) (hm hv)
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hy
    obtain ⟨h6, h7⟩ := hy
    rw [← enc_mul h16, ← hE, beq_enc_iff h16] at h1
    rw [← hE] at h2
    rw [cjK_enc hC hCi] at h3
    rw [cjK_enc hC hCi, cjK_enc hC hCi, ← enc_mul h16, beq_enc_iff h16] at h4
    rw [cjK_enc hC hCi, ← enc_mul h16, ← enc_mul h16, beq_enc_iff h16] at h5
    refine ⟨⟨h1, ne_of_beq h2, (memK_enc hL _).1 h3, h4, h5⟩, ?_, ?_⟩
    · rcases h6 with e | ⟨e1, e2⟩
      · exact Or.inl ((inSK_iff hC hCi u v).1 e)
      · rw [← enc_mul h16, ← hE] at e1
        rw [← enc_mul h16] at e2
        refine Or.inr ⟨ne_of_beq e1, fun hm' => ?_⟩
        rw [(memK_enc hL _).2 hm'] at e2
        cases e2
    · intro hs
      rcases h7 with e | e
      · rw [(inSK_iff hC hCi u v).2 hs] at e
        cases e
      · exact (inSK_iff hC hCi v u).1 e
  exact ⟨fun u hu => (H u hu u hu).1, fun u hu v hv => (H u hu v hv).2.1,
    fun u hu v hv => (H u hu v hv).2.2⟩

end CFSG.RankThree.PartTwo.Sec14.Item148HJK
