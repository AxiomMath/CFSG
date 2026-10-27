module

public import Certificates.Kernel.Co2.Words
public import CFSG.Certificates.Kernel.Bounds.HSAlt.RelsTC
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Pair
public import CFSG.Certificates.Kernel.HOrbSound
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Checks.M
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Group

public section

namespace CertificateChecks.KernelHS

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.HSK CFSG.Certificates CFSG.Certificates.LCE
  CertificateChecks.KernelCo2

abbrev P : TauCeti.GroupPresentation := TauCeti.Sporadic.hsPresentation

noncomputable abbrev tg : ℕ → PresentedGroup P.relatorSet := pgen P.relatorSet

theorem gens_eq : P.generatorCount = 2 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.hsPresentation_generatorNames]

theorem wordNat_eq : ∀ w : List (ℕ × Bool), HSK.wordNat w = CFSG.KC.Co2B.wordNat w
  | [] => rfl
  | l :: w => by
    rw [HSK.wordNat, CFSG.KC.Co2B.wordNat, wordNat_eq w]
    rfl

theorem ent_eq (w : List (ℕ × Bool)) : HSK.ent w = CFSG.KC.Co2B.ent w := by
  rw [HSK.ent, CFSG.KC.Co2B.ent, wordNat_eq]

theorem rel_val : ∀ r < 13, bval tg (wWord (HSK.rel r)) (wLen (HSK.rel r)) = 1 := by
  have hl := HSK.relatorLetters_ent
  have hb : ∀ w ∈ P.relatorLetters, (∀ l ∈ w, l.1 < 127) ∧ w.length < 1024 := by
    rw [HSK.rels_eq]
    decide
  have hlen : (P.relatorLetters.map HSK.ent).length = 13 := by rw [hl]; rfl
  intro r hr
  have e : HSK.rel r = (P.relatorLetters.map HSK.ent)[r]'(by omega) := by
    rw [List.getElem_of_eq hl]
    interval_cases r <;> rfl
  rw [e, List.getElem_map, ent_eq]
  have hm := List.getElem_mem (l := P.relatorLetters) (n := r) (by
    rw [List.length_map] at hlen
    omega)
  rw [bval_ent _ _ (hb _ hm).1 (hb _ hm).2]
  exact swd_relatorLetters P _ hm

theorem beq_false {r i : ℕ} (h : i < r) : Nat.beq r i = false :=
  Bool.eq_false_iff.mpr fun h' => by
    have := Nat.eq_of_beq_eq_true h'
    omega

theorem rel_ge {r : ℕ} (h : 13 ≤ r) : HSK.rel r = 0 := by
  simp (disch := omega) only [HSK.rel, beq_false]

theorem subB_ge {j : ℕ} (h : 5 ≤ j) : HSK.subB j = 0 := by
  simp (disch := omega) only [HSK.subB, beq_false]

theorem bval_zero {G : Type*} [Group G] (gen : ℕ → G) : bval gen (wWord 0) (wLen 0) = 1 := rfl

theorem rel_norm : relsNorm HSK.rel (nat_lit 13) = true := by quickRfl

theorem rel_all : ∀ r, wWord (HSK.rel r) < 2 ^ (8 * wLen (HSK.rel r)) ∧
    bval tg (wWord (HSK.rel r)) (wLen (HSK.rel r)) = 1 := by
  intro r
  by_cases hr : r < 13
  · exact ⟨relsNorm_spec rel_norm r hr, rel_val r hr⟩
  · rw [rel_ge (by omega)]
    exact ⟨by decide, rfl⟩

theorem swd_append {G : Type*} [Group G] (gen : ℕ → G) (l1 l2 : List (ℕ × Bool)) :
    swd gen (l1 ++ l2) = swd gen l1 * swd gen l2 := by
  simp only [swd, List.map_append, List.prod_append]

@[expose] def rep (l : List (ℕ × Bool)) (n : ℕ) : List (ℕ × Bool) := (List.replicate n l).flatten

theorem swd_rep {G : Type*} [Group G] (gen : ℕ → G) (l : List (ℕ × Bool)) (n : ℕ) :
    swd gen (rep l n) = swd gen l ^ n := by
  induction n with
  | zero => simp [rep, swd]
  | succ n ih =>
    rw [rep, List.replicate_succ', List.flatten_append, ← rep, swd_append, ih, pow_succ]
    simp [swd]

theorem swd_rel (w : List (ℕ × Bool)) (h : w ∈ HSK.relsLit) : swd tg w = 1 :=
  swd_relatorLetters P w (by rw [HSK.rels_eq]; exact h)

theorem bval_lit (e : ℕ) (w : List (ℕ × Bool)) (he : Nat.beq e (HSK.ent w) = true)
    (hw : ∀ l ∈ w, l.1 < 127) (hlen : w.length < 1024) :
    bval tg (wWord e) (wLen e) = swd tg w := by
  rw [Nat.eq_of_beq_eq_true he, ent_eq, bval_ent _ _ hw hlen]

theorem a_sq : tg 0 * tg 0 = 1 := by
  have h := swd_rel [(0, true), (0, true)] (by decide)
  simpa [swd] using h

theorem a_inv : (tg 0)⁻¹ = tg 0 := inv_eq_of_mul_eq_one_right a_sq

theorem conj_comm {G : Type*} [Group G] {a : G} (ha : a⁻¹ = a) (y : G) :
    a * (a⁻¹ * y⁻¹ * a * y) * a⁻¹ = (a⁻¹ * y⁻¹ * a * y)⁻¹ :=
  calc a * (a⁻¹ * y⁻¹ * a * y) * a⁻¹ = y⁻¹ * a * y * a⁻¹ := by group
    _ = y⁻¹ * a⁻¹ * y * a := by rw [ha]
    _ = (a⁻¹ * y⁻¹ * a * y)⁻¹ := by group

theorem comm_cent {G : Type*} [Group G] {a : G} (ha : a⁻¹ = a) (y : G) (k : ℕ)
    (h : (a⁻¹ * y⁻¹ * a * y) ^ (2 * k + 1) = 1) :
    y * (a⁻¹ * y⁻¹ * a * y) ^ k * a = a * (y * (a⁻¹ * y⁻¹ * a * y) ^ k) := by
  obtain ⟨c, hc⟩ : ∃ c, a⁻¹ * y⁻¹ * a * y = c := ⟨_, rfl⟩
  have h1 : a * c * a⁻¹ = c⁻¹ := by
    rw [← hc]
    exact conj_comm ha y
  have hy : y * a * c = a * y := by
    rw [← hc]
    group
  rw [hc] at h ⊢
  have h2 : a * c ^ (k + 1) * a⁻¹ = (c ^ (k + 1))⁻¹ := by
    rw [← conj_pow, h1, inv_pow]
  have h3 : (c ^ (k + 1))⁻¹ = c ^ k := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 1 + k = 2 * k + 1 by ring]
    exact h
  calc y * c ^ k * a = y * (a * c ^ (k + 1) * a⁻¹) * a := by rw [h2, h3]
    _ = y * a * c * c ^ k := by
      rw [pow_succ']
      group
    _ = a * (y * c ^ k) := by rw [hy, mul_assoc]

theorem comm3_cent {G : Type*} [Group G] {a : G} (ha : a⁻¹ = a) (y : G)
    (h : (a⁻¹ * y⁻¹ * a * y) ^ 6 = 1) :
    (a⁻¹ * y⁻¹ * a * y) ^ 3 * a = a * (a⁻¹ * y⁻¹ * a * y) ^ 3 := by
  have h2 : a * (a⁻¹ * y⁻¹ * a * y) ^ 3 * a⁻¹ = (a⁻¹ * y⁻¹ * a * y) ^ 3 := by
    rw [← conj_pow, conj_comm ha, inv_pow, inv_eq_iff_mul_eq_one, ← pow_add]
    exact h
  calc (a⁻¹ * y⁻¹ * a * y) ^ 3 * a = a * (a⁻¹ * y⁻¹ * a * y) ^ 3 * a⁻¹ * a := by rw [h2]
    _ = a * (a⁻¹ * y⁻¹ * a * y) ^ 3 := by group

theorem r4 : ((tg 0)⁻¹ * (tg 1)⁻¹ * tg 0 * tg 1) ^ 5 = 1 := by
  have h := swd_rel (rep [(0, false), (1, false), (0, true), (1, true)] 5) (by decide)
  rw [swd_rep] at h
  simpa [swd, mul_assoc] using h

theorem r5 : ((tg 0)⁻¹ * (tg 1 * tg 0 * tg 1)⁻¹ * tg 0 * (tg 1 * tg 0 * tg 1)) ^ 3 = 1 := by
  have h := swd_rel (rep [(0, false), (1, false), (0, false), (1, false), (0, true), (1, true),
    (0, true), (1, true)] 3) (by decide)
  rw [swd_rep] at h
  simpa [swd, mul_assoc] using h

theorem r6 : ((tg 0)⁻¹ * (tg 1 * tg 1)⁻¹ * tg 0 * (tg 1 * tg 1)) ^ 6 = 1 := by
  have h := swd_rel (rep [(0, false), (1, false), (1, false), (0, true), (1, true), (1, true)] 6)
    (by decide)
  rw [swd_rep] at h
  simpa [swd, mul_assoc] using h

theorem r6' : ((tg 0)⁻¹ * ((tg 1)⁻¹ * (tg 1)⁻¹)⁻¹ * tg 0 * ((tg 1)⁻¹ * (tg 1)⁻¹)) ^ 6 = 1 := by
  have e : (tg 0)⁻¹ * ((tg 1)⁻¹ * (tg 1)⁻¹)⁻¹ * tg 0 * ((tg 1)⁻¹ * (tg 1)⁻¹) =
      (tg 1 * tg 1) * ((tg 0)⁻¹ * (tg 1 * tg 1)⁻¹ * tg 0 * (tg 1 * tg 1))⁻¹ * (tg 1 * tg 1)⁻¹ := by
    group
  rw [e, conj_pow, inv_pow, r6, inv_one, mul_one, mul_inv_cancel]

theorem bray_cent : ∀ j, bval tg (wWord (HSK.subB j)) (wLen (HSK.subB j)) * tg 0 =
    tg 0 * bval tg (wWord (HSK.subB j)) (wLen (HSK.subB j)) := by
  intro j
  by_cases hj : j < 5
  · interval_cases j
    · rw [bval_lit (HSK.subB 0) [(0, true)] (by quickRfl) (by decide) (by decide)]
      simp [swd]
    · rw [bval_lit (HSK.subB 1) [(1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false),
        (0, true), (1, true)] (by quickRfl) (by decide) (by decide)]
      have h := comm_cent a_inv (tg 1) 2 r4
      simp only [swd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Bool.false_eq_true, ↓reduceIte, mul_one]
      calc _ = tg 1 * ((tg 0)⁻¹ * (tg 1)⁻¹ * tg 0 * tg 1) ^ 2 * tg 0 := by
            simp only [pow_succ, pow_zero, one_mul]
            group
        _ = tg 0 * (tg 1 * ((tg 0)⁻¹ * (tg 1)⁻¹ * tg 0 * tg 1) ^ 2) := h
        _ = _ := by
            simp only [pow_succ, pow_zero, one_mul]
            group
    · rw [bval_lit (HSK.subB 2) [(1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false),
        (0, true), (1, true), (0, true), (1, true)] (by quickRfl) (by decide) (by decide)]
      have h := comm_cent a_inv (tg 1 * tg 0 * tg 1) 1 r5
      simp only [swd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Bool.false_eq_true, ↓reduceIte, mul_one]
      calc _ = (tg 1 * tg 0 * tg 1) *
            ((tg 0)⁻¹ * (tg 1 * tg 0 * tg 1)⁻¹ * tg 0 * (tg 1 * tg 0 * tg 1)) ^ 1 * tg 0 := by
            simp only [pow_one, mul_inv_rev]
            group
        _ = tg 0 * ((tg 1 * tg 0 * tg 1) *
            ((tg 0)⁻¹ * (tg 1 * tg 0 * tg 1)⁻¹ * tg 0 * (tg 1 * tg 0 * tg 1)) ^ 1) := h
        _ = _ := by
            simp only [pow_one, mul_inv_rev]
            group
    · rw [bval_lit (HSK.subB 3) (rep [(0, false), (1, false), (1, false), (0, true), (1, true), (1, true)] 3)
        (by quickRfl) (by decide) (by decide), swd_rep]
      have h := comm3_cent a_inv (tg 1 * tg 1) r6
      have e : swd tg [(0, false), (1, false), (1, false), (0, true), (1, true), (1, true)] =
          (tg 0)⁻¹ * (tg 1 * tg 1)⁻¹ * tg 0 * (tg 1 * tg 1) := by
        simp only [swd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          Bool.false_eq_true, ↓reduceIte, mul_one, mul_inv_rev, mul_assoc]
      rw [e]
      exact h
    · rw [bval_lit (HSK.subB 4) (rep [(0, false), (1, true), (1, true), (0, true), (1, false), (1, false)] 3)
        (by quickRfl) (by decide) (by decide), swd_rep]
      have h := comm3_cent a_inv ((tg 1)⁻¹ * (tg 1)⁻¹) r6'
      have e : swd tg [(0, false), (1, true), (1, true), (0, true), (1, false), (1, false)] =
          (tg 0)⁻¹ * ((tg 1)⁻¹ * (tg 1)⁻¹)⁻¹ * tg 0 * ((tg 1)⁻¹ * (tg 1)⁻¹) := by
        simp only [swd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          Bool.false_eq_true, ↓reduceIte, mul_one, mul_inv_rev, inv_inv, mul_assoc]
      rw [e]
      exact h
  · rw [subB_ge (by omega), bval_zero, one_mul, mul_one]

theorem root_rel {U m k : ℕ} (hk : k < 13) (hb : Nat.beq (commPow U m) (HSK.rel k) = true)
    (he : HO.entOK U (nat_lit 254) (nat_lit 510) = true)
    (hwf : Nat.blt (wWord (commEnt U)) (2 ^ (8 * wLen (commEnt U))) = true)
    (hm : Nat.blt (m * wLen (commEnt U)) 1024 = true) :
    ((tg 0)⁻¹ * (bval tg (wWord U) (wLen U))⁻¹ * tg 0 * bval tg (wWord U) (wLen U)) ^ m = 1 := by
  have hv := rel_val k hk
  rw [← Nat.eq_of_beq_eq_true hb, show commPow U m = powEnt (commEnt U) m from rfl,
    HO.bval_powEnt tg (by simpa using hwf) (by simpa using hm), HO.bval_commEnt tg he] at hv
  exact hv

theorem u4_rel : ((tg 0)⁻¹ * (bval tg (wWord HSK.U4) (wLen HSK.U4))⁻¹ * tg 0 *
    bval tg (wWord HSK.U4) (wLen HSK.U4)) ^ 2 = 1 := by
  rw [bval_lit (HSK.U4) [(1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true),
    (1, true)] (by quickRfl) (by decide) (by decide)]
  have e : swd tg [(1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true),
      (1, true)] = tg 1 * tg 1 * tg 0 * (tg 1)⁻¹ * (tg 1)⁻¹ * tg 0 * tg 1 * tg 1 := by
    simp only [swd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, ↓reduceIte, mul_one]
    group
  have key : (tg 0)⁻¹ * (tg 1 * tg 1 * tg 0 * (tg 1)⁻¹ * (tg 1)⁻¹ * tg 0 * tg 1 * tg 1)⁻¹ * tg 0 *
      (tg 1 * tg 1 * tg 0 * (tg 1)⁻¹ * (tg 1)⁻¹ * tg 0 * tg 1 * tg 1) =
      ((tg 0)⁻¹ * (tg 1 * tg 1)⁻¹ * tg 0 * (tg 1 * tg 1)) ^ 3 := by
    simp only [mul_inv_rev, inv_inv, a_inv, pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e, key, ← pow_mul]
  exact r6

theorem root_val : ∀ ρ, 1 ≤ ρ → ρ ≤ 4 →
    HO.entOK (rootWord ρ) (nat_lit 4) (nat_lit 16) = true ∧
    ((tg 0)⁻¹ * (bval tg (wWord (rootWord ρ)) (wLen (rootWord ρ)))⁻¹ * tg 0 *
      bval tg (wWord (rootWord ρ)) (wLen (rootWord ρ))) ^ rootExp ρ = 1 := by
  intro ρ h1 h4
  interval_cases ρ
  · exact ⟨by quickRfl, root_rel (k := 4) (by norm_num) CFSG.KD.HSKM.root1 (by quickRfl)
      (by quickRfl) (by quickRfl)⟩
  · exact ⟨by quickRfl, root_rel (k := 5) (by norm_num) CFSG.KD.HSKM.root2 (by quickRfl)
      (by quickRfl) (by quickRfl)⟩
  · exact ⟨by quickRfl, root_rel (k := 6) (by norm_num) CFSG.KD.HSKM.root3 (by quickRfl)
      (by quickRfl) (by quickRfl)⟩
  · exact ⟨by quickRfl, u4_rel⟩

end CertificateChecks.KernelHS

end
