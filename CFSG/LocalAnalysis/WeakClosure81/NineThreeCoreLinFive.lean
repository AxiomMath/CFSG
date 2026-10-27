module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private def nine3_la5_tau : Fin 3 → Fin 5 := ![2, 3, 4]

private lemma nine3_la5_tau_zero : nine3_la5_tau 0 = 2 := rfl
private lemma nine3_la5_tau_one : nine3_la5_tau 1 = 3 := rfl
private lemma nine3_la5_tau_two : nine3_la5_tau 2 = 4 := rfl

private def nine3_la5_e0 : Fin 3 → Bool := fun s => decide (s = 0)
private def nine3_la5_e1 : Fin 3 → Bool := fun s => decide (s = 1)
private def nine3_la5_e2 : Fin 3 → Bool := fun s => decide (s = 2)
private def nine3_la5_p01 : Fin 3 → Bool := fun s => decide (s = 0) || decide (s = 1)
private def nine3_la5_p02 : Fin 3 → Bool := fun s => decide (s = 0) || decide (s = 2)
private def nine3_la5_p12 : Fin 3 → Bool := fun s => decide (s = 1) || decide (s = 2)
private def nine3_la5_gzero : Fin 3 → Bool := fun _ => false
private def nine3_la5_gtop : Fin 3 → Bool := fun _ => true

private lemma nine3_la5_classify {c : Fin 3 → Bool} (hc : c ≠ nine3_la5_gzero) :
    c = nine3_la5_e0 ∨ c = nine3_la5_e1 ∨ c = nine3_la5_e2 ∨ c = nine3_la5_p01 ∨
      c = nine3_la5_p02 ∨ c = nine3_la5_p12 ∨ c = nine3_la5_gtop := by
  revert c
  decide

private def nine3_la5_Phi {T W : Type} [CommGroup T] [CommGroup W]
    (φ : Fin 5 → T →* W) (c : Fin 3 → Bool) (i : T) : W :=
  ∏ t : Fin 3, (if c t then φ (nine3_la5_tau t) i else 1)

private def nine3_la5_Psi {T' W : Type} [CommGroup T'] [CommGroup W]
    (ψ : Fin 5 → T' →* W) (d : Fin 3 → Bool) (j : T') : W :=
  ∏ t : Fin 3, (if d t then ψ (nine3_la5_tau t) j else 1)

private lemma nine3_la5_Phi_e0 {T W : Type} [CommGroup T] [CommGroup W]
    (φ : Fin 5 → T →* W) (i : T) : nine3_la5_Phi φ nine3_la5_e0 i = φ 2 i := by
  simp [nine3_la5_Phi, nine3_la5_e0, nine3_la5_tau, Fin.prod_univ_three]

private lemma nine3_la5_Phi_e1 {T W : Type} [CommGroup T] [CommGroup W]
    (φ : Fin 5 → T →* W) (i : T) : nine3_la5_Phi φ nine3_la5_e1 i = φ 3 i := by
  simp [nine3_la5_Phi, nine3_la5_e1, nine3_la5_tau, Fin.prod_univ_three]

private lemma nine3_la5_Phi_e2 {T W : Type} [CommGroup T] [CommGroup W]
    (φ : Fin 5 → T →* W) (i : T) : nine3_la5_Phi φ nine3_la5_e2 i = φ 4 i := by
  simp [nine3_la5_Phi, nine3_la5_e2, nine3_la5_tau, Fin.prod_univ_three]

private lemma nine3_la5_Phi_p01 {T W : Type} [CommGroup T] [CommGroup W]
    (φ : Fin 5 → T →* W) (i : T) :
    nine3_la5_Phi φ nine3_la5_p01 i = φ 2 i * φ 3 i := by
  simp [nine3_la5_Phi, nine3_la5_p01, nine3_la5_tau, Fin.prod_univ_three, mul_assoc]

private lemma nine3_la5_Phi_p02 {T W : Type} [CommGroup T] [CommGroup W]
    (φ : Fin 5 → T →* W) (i : T) :
    nine3_la5_Phi φ nine3_la5_p02 i = φ 2 i * φ 4 i := by
  simp [nine3_la5_Phi, nine3_la5_p02, nine3_la5_tau, Fin.prod_univ_three, mul_assoc]

private lemma nine3_la5_Phi_p12 {T W : Type} [CommGroup T] [CommGroup W]
    (φ : Fin 5 → T →* W) (i : T) :
    nine3_la5_Phi φ nine3_la5_p12 i = φ 3 i * φ 4 i := by
  simp [nine3_la5_Phi, nine3_la5_p12, nine3_la5_tau, Fin.prod_univ_three, mul_assoc]

private lemma nine3_la5_Phi_top {T W : Type} [CommGroup T] [CommGroup W]
    (φ : Fin 5 → T →* W) (i : T) :
    nine3_la5_Phi φ nine3_la5_gtop i = φ 2 i * φ 3 i * φ 4 i := by
  simp [nine3_la5_Phi, nine3_la5_gtop, nine3_la5_tau, Fin.prod_univ_three, mul_assoc]

private lemma nine3_la5_Phi_zero {T W : Type} [CommGroup T] [CommGroup W]
    (φ : Fin 5 → T →* W) (i : T) : nine3_la5_Phi φ nine3_la5_gzero i = 1 := by
  simp [nine3_la5_Phi, nine3_la5_gzero]

private lemma nine3_la5_Psi_e0 {T' W : Type} [CommGroup T'] [CommGroup W]
    (ψ : Fin 5 → T' →* W) (j : T') : nine3_la5_Psi ψ nine3_la5_e0 j = ψ 2 j := by
  simp [nine3_la5_Psi, nine3_la5_e0, nine3_la5_tau, Fin.prod_univ_three]

private lemma nine3_la5_Psi_e1 {T' W : Type} [CommGroup T'] [CommGroup W]
    (ψ : Fin 5 → T' →* W) (j : T') : nine3_la5_Psi ψ nine3_la5_e1 j = ψ 3 j := by
  simp [nine3_la5_Psi, nine3_la5_e1, nine3_la5_tau, Fin.prod_univ_three]

private lemma nine3_la5_Psi_e2 {T' W : Type} [CommGroup T'] [CommGroup W]
    (ψ : Fin 5 → T' →* W) (j : T') : nine3_la5_Psi ψ nine3_la5_e2 j = ψ 4 j := by
  simp [nine3_la5_Psi, nine3_la5_e2, nine3_la5_tau, Fin.prod_univ_three]

private lemma nine3_la5_Psi_p01 {T' W : Type} [CommGroup T'] [CommGroup W]
    (ψ : Fin 5 → T' →* W) (j : T') :
    nine3_la5_Psi ψ nine3_la5_p01 j = ψ 2 j * ψ 3 j := by
  simp [nine3_la5_Psi, nine3_la5_p01, nine3_la5_tau, Fin.prod_univ_three, mul_assoc]

private lemma nine3_la5_Psi_p02 {T' W : Type} [CommGroup T'] [CommGroup W]
    (ψ : Fin 5 → T' →* W) (j : T') :
    nine3_la5_Psi ψ nine3_la5_p02 j = ψ 2 j * ψ 4 j := by
  simp [nine3_la5_Psi, nine3_la5_p02, nine3_la5_tau, Fin.prod_univ_three, mul_assoc]

private lemma nine3_la5_Psi_p12 {T' W : Type} [CommGroup T'] [CommGroup W]
    (ψ : Fin 5 → T' →* W) (j : T') :
    nine3_la5_Psi ψ nine3_la5_p12 j = ψ 3 j * ψ 4 j := by
  simp [nine3_la5_Psi, nine3_la5_p12, nine3_la5_tau, Fin.prod_univ_three, mul_assoc]

private lemma nine3_la5_Psi_top {T' W : Type} [CommGroup T'] [CommGroup W]
    (ψ : Fin 5 → T' →* W) (j : T') :
    nine3_la5_Psi ψ nine3_la5_gtop j = ψ 2 j * ψ 3 j * ψ 4 j := by
  simp [nine3_la5_Psi, nine3_la5_gtop, nine3_la5_tau, Fin.prod_univ_three, mul_assoc]

private lemma nine3_la5_Psi_zero {T' W : Type} [CommGroup T'] [CommGroup W]
    (ψ : Fin 5 → T' →* W) (j : T') : nine3_la5_Psi ψ nine3_la5_gzero j = 1 := by
  simp [nine3_la5_Psi, nine3_la5_gzero]

private lemma nine3_la5_Phi_add {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (φ : Fin 5 → T →* W) (c d : Fin 3 → Bool) (i : T) :
    nine3_la5_Phi φ c i * nine3_la5_Phi φ d i =
      nine3_la5_Phi φ (fun t => c t ^^ d t) i := by
  rw [nine3_la5_Phi, nine3_la5_Phi, nine3_la5_Phi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro t _
  cases hc : c t <;> cases hd : d t <;> simp [hc, hd, hW]

private lemma nine3_la5_Psi_add {T' W : Type} [CommGroup T'] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (ψ : Fin 5 → T' →* W) (c d : Fin 3 → Bool) (j : T') :
    nine3_la5_Psi ψ c j * nine3_la5_Psi ψ d j =
      nine3_la5_Psi ψ (fun t => c t ^^ d t) j := by
  rw [nine3_la5_Psi, nine3_la5_Psi, nine3_la5_Psi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro t _
  cases hc : c t <;> cases hd : d t <;> simp [hc, hd, hW]

private lemma nine3_la5_eq_one {W : Type} [CommMonoid W] (hW : ∀ w : W, w * w = 1)
    {a b : W} (h : a * b = 1) : a = b := by
  calc a = a * 1 := (mul_one a).symm
    _ = a * (b * b) := by rw [hW b]
    _ = (a * b) * b := by rw [mul_assoc]
    _ = 1 * b := by rw [h]
    _ = b := one_mul b

private lemma nine3_la5_eq_mul_of_eq_mul {W : Type} [CommMonoid W]
    (hW : ∀ w : W, w * w = 1) {a b c : W} (h : a = b * c) : c = a * b := by
  rw [h]
  calc c = 1 * c := (one_mul c).symm
    _ = (b * b) * c := by rw [hW b]
    _ = b * (b * c) := by rw [← mul_assoc]
    _ = b * (c * b) := by rw [mul_comm b c]
    _ = b * c * b := by rw [mul_assoc]

private lemma nine3_la5_phi_special {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (φ : Fin 5 → T →* W)
    (hφ0 : ∀ i, φ 0 i = 1) (hφsum : ∀ i, ∏ k : Fin 5, φ k i = 1) (i : T) :
    φ 1 i = φ 2 i * φ 3 i * φ 4 i := by
  have h := hφsum i
  rw [Fin.prod_univ_five] at h
  simp only [hφ0 i, one_mul] at h
  have h' : φ 1 i * (φ 2 i * φ 3 i * φ 4 i) = 1 := by
    simpa [mul_assoc] using h
  exact nine3_la5_eq_one hW h'

private lemma nine3_la5_psi_special {T' W : Type} [CommGroup T'] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (ψ : Fin 5 → T' →* W)
    (hψ1 : ∀ j, ψ 1 j = 1) (hψsum : ∀ j, ∏ l : Fin 5, ψ l j = 1) (j : T') :
    ψ 0 j = ψ 2 j * ψ 3 j * ψ 4 j := by
  have h := hψsum j
  rw [Fin.prod_univ_five] at h
  simp only [hψ1 j, one_mul] at h
  have h' : ψ 0 j * (ψ 2 j * ψ 3 j * ψ 4 j) = 1 := by
    simpa [mul_assoc] using h
  exact nine3_la5_eq_one hW h'

private lemma nine3_la5_Phi_comp {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (φ : Fin 5 → T →* W)
    (hφ0 : ∀ i, φ 0 i = 1) (hφsum : ∀ i, ∏ k : Fin 5, φ k i = 1)
    (c : Fin 3 → Bool) (i : T) :
    nine3_la5_Phi φ (fun t => !(c t)) i = φ 1 i * nine3_la5_Phi φ c i := by
  have hterm : ∀ t : Fin 3,
      (if !(c t) then φ (nine3_la5_tau t) i else 1) =
        φ (nine3_la5_tau t) i * (if c t then φ (nine3_la5_tau t) i else 1) := by
    intro t
    cases c t <;> simp [hW]
  rw [nine3_la5_Phi, Finset.prod_congr rfl (fun t _ => hterm t), Finset.prod_mul_distrib,
    nine3_la5_Phi]
  rw [nine3_la5_phi_special hW φ hφ0 hφsum i, Fin.prod_univ_three]
  simp only [nine3_la5_tau_zero, nine3_la5_tau_one, nine3_la5_tau_two, mul_assoc]

private lemma nine3_la5_Psi_comp {T' W : Type} [CommGroup T'] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (ψ : Fin 5 → T' →* W)
    (hψ1 : ∀ j, ψ 1 j = 1) (hψsum : ∀ j, ∏ l : Fin 5, ψ l j = 1)
    (c : Fin 3 → Bool) (j : T') :
    nine3_la5_Psi ψ (fun t => !(c t)) j = ψ 0 j * nine3_la5_Psi ψ c j := by
  have hterm : ∀ t : Fin 3,
      (if !(c t) then ψ (nine3_la5_tau t) j else 1) =
        ψ (nine3_la5_tau t) j * (if c t then ψ (nine3_la5_tau t) j else 1) := by
    intro t
    cases c t <;> simp [hW]
  rw [nine3_la5_Psi, Finset.prod_congr rfl (fun t _ => hterm t), Finset.prod_mul_distrib,
    nine3_la5_Psi]
  rw [nine3_la5_psi_special hW ψ hψ1 hψsum j, Fin.prod_univ_three]
  simp only [nine3_la5_tau_zero, nine3_la5_tau_one, nine3_la5_tau_two, mul_assoc]

private lemma nine3_la5_Phi_rep {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (φ : Fin 5 → T →* W)
    (hφ0 : ∀ i, φ 0 i = 1) (hφsum : ∀ i, ∏ k : Fin 5, φ k i = 1)
    (ε : Fin 5 → Bool) (i : T) :
    nine3_la5_Phi φ (fun t => ε (nine3_la5_tau t) ^^ ε 1) i =
      ∏ k : Fin 5, (if ε k then φ k i else 1) := by
  have h5 : (∏ k : Fin 5, (if ε k then φ k i else 1)) =
      (if ε 0 then φ 0 i else 1) * (if ε 1 then φ 1 i else 1) *
        nine3_la5_Phi φ (fun t => ε (nine3_la5_tau t)) i := by
    rw [nine3_la5_Phi, Fin.prod_univ_five, Fin.prod_univ_three]
    simp only [nine3_la5_tau_zero, nine3_la5_tau_one, nine3_la5_tau_two, mul_assoc]
    rfl
  have h0 : (if ε 0 then φ 0 i else 1) = 1 := by cases ε 0 <;> simp [hφ0 i]
  rw [h5, h0, one_mul]
  rcases Bool.dichotomy (ε 1) with h1 | h1
  · rw [h1, if_neg (by decide), one_mul]
    simp only [Bool.xor_false]
  · rw [h1, if_pos rfl]
    have hr : (fun t => ε (nine3_la5_tau t) ^^ true) =
        fun t => !(ε (nine3_la5_tau t)) := by
      funext t
      rw [Bool.xor_true]
    rw [hr, nine3_la5_Phi_comp hW φ hφ0 hφsum]

private lemma nine3_la5_Psi_rep {T' W : Type} [CommGroup T'] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (ψ : Fin 5 → T' →* W)
    (hψ1 : ∀ j, ψ 1 j = 1) (hψsum : ∀ j, ∏ l : Fin 5, ψ l j = 1)
    (π : Fin 5 → Bool) (j : T') :
    nine3_la5_Psi ψ (fun t => π (nine3_la5_tau t) ^^ π 0) j =
      ∏ l : Fin 5, (if π l then ψ l j else 1) := by
  have h5 : (∏ l : Fin 5, (if π l then ψ l j else 1)) =
      (if π 0 then ψ 0 j else 1) * (if π 1 then ψ 1 j else 1) *
        nine3_la5_Psi ψ (fun t => π (nine3_la5_tau t)) j := by
    rw [nine3_la5_Psi, Fin.prod_univ_five, Fin.prod_univ_three]
    simp only [nine3_la5_tau_zero, nine3_la5_tau_one, nine3_la5_tau_two, mul_assoc]
    rfl
  have h1 : (if π 1 then ψ 1 j else 1) = 1 := by cases π 1 <;> simp [hψ1 j]
  rw [h5, h1, mul_one]
  rcases Bool.dichotomy (π 0) with h0 | h0
  · rw [h0, if_neg (by decide), one_mul]
    simp only [Bool.xor_false]
  · rw [h0, if_pos rfl]
    have hr : (fun t => π (nine3_la5_tau t) ^^ true) =
        fun t => !(π (nine3_la5_tau t)) := by
      funext t
      rw [Bool.xor_true]
    rw [hr, nine3_la5_Psi_comp hW ψ hψ1 hψsum]

private lemma nine3_la5_Phi_ne_one {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (φ : Fin 5 → T →* W) (hφ0 : ∀ i, φ 0 i = 1) (hφP : ∀ k i, φ k i ∈ P k)
    (iφ : ∀ k, k ≠ 0 → Function.Injective (φ k))
    (hφsum : ∀ i, ∏ k : Fin 5, φ k i = 1)
    {c : Fin 3 → Bool} (hc : c ≠ nine3_la5_gzero) {i : T} (hi : i ≠ 1) :
    nine3_la5_Phi φ c i ≠ 1 := by
  intro h
  have hclass := nine3_la5_classify hc
  rcases hclass with h0 | h0 | h0 | h0 | h0 | h0 | h0
  · rw [h0, nine3_la5_Phi_e0] at h
    exact hi (iφ 2 (by decide) (by rw [h, map_one]))
  · rw [h0, nine3_la5_Phi_e1] at h
    exact hi (iφ 3 (by decide) (by rw [h, map_one]))
  · rw [h0, nine3_la5_Phi_e2] at h
    exact hi (iφ 4 (by decide) (by rw [h, map_one]))
  · rw [h0, nine3_la5_Phi_p01] at h
    have heq : φ 2 i = φ 3 i := nine3_la5_eq_one hW h
    have hmem : φ 2 i ∈ P 2 ⊓ P 3 := ⟨hφP 2 i, by rw [heq]; exact hφP 3 i⟩
    rw [hP 2 3 (by decide), Subgroup.mem_bot] at hmem
    exact hi (iφ 2 (by decide) (by rw [hmem, map_one]))
  · rw [h0, nine3_la5_Phi_p02] at h
    have heq : φ 2 i = φ 4 i := nine3_la5_eq_one hW h
    have hmem : φ 2 i ∈ P 2 ⊓ P 4 := ⟨hφP 2 i, by rw [heq]; exact hφP 4 i⟩
    rw [hP 2 4 (by decide), Subgroup.mem_bot] at hmem
    exact hi (iφ 2 (by decide) (by rw [hmem, map_one]))
  · rw [h0, nine3_la5_Phi_p12] at h
    have heq : φ 3 i = φ 4 i := nine3_la5_eq_one hW h
    have hmem : φ 3 i ∈ P 3 ⊓ P 4 := ⟨hφP 3 i, by rw [heq]; exact hφP 4 i⟩
    rw [hP 3 4 (by decide), Subgroup.mem_bot] at hmem
    exact hi (iφ 3 (by decide) (by rw [hmem, map_one]))
  · rw [h0, nine3_la5_Phi_top] at h
    have hspec := nine3_la5_phi_special hW φ hφ0 hφsum i
    have h1' : φ 1 i = 1 := by rw [hspec]; exact h
    exact hi (iφ 1 (by decide) (by rw [h1', map_one]))

private lemma nine3_la5_Psi_ne_one {T' W : Type} [CommGroup T'] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (ψ : Fin 5 → T' →* W) (hψ1 : ∀ j, ψ 1 j = 1) (hψP : ∀ l j, ψ l j ∈ P l)
    (iψ : ∀ l, l ≠ 1 → Function.Injective (ψ l))
    (hψsum : ∀ j, ∏ l : Fin 5, ψ l j = 1)
    {c : Fin 3 → Bool} (hc : c ≠ nine3_la5_gzero) {j : T'} (hj : j ≠ 1) :
    nine3_la5_Psi ψ c j ≠ 1 := by
  intro h
  have hclass := nine3_la5_classify hc
  rcases hclass with h0 | h0 | h0 | h0 | h0 | h0 | h0
  · rw [h0, nine3_la5_Psi_e0] at h
    exact hj (iψ 2 (by decide) (by rw [h, map_one]))
  · rw [h0, nine3_la5_Psi_e1] at h
    exact hj (iψ 3 (by decide) (by rw [h, map_one]))
  · rw [h0, nine3_la5_Psi_e2] at h
    exact hj (iψ 4 (by decide) (by rw [h, map_one]))
  · rw [h0, nine3_la5_Psi_p01] at h
    have heq : ψ 2 j = ψ 3 j := nine3_la5_eq_one hW h
    have hmem : ψ 2 j ∈ P 2 ⊓ P 3 := ⟨hψP 2 j, by rw [heq]; exact hψP 3 j⟩
    rw [hP 2 3 (by decide), Subgroup.mem_bot] at hmem
    exact hj (iψ 2 (by decide) (by rw [hmem, map_one]))
  · rw [h0, nine3_la5_Psi_p02] at h
    have heq : ψ 2 j = ψ 4 j := nine3_la5_eq_one hW h
    have hmem : ψ 2 j ∈ P 2 ⊓ P 4 := ⟨hψP 2 j, by rw [heq]; exact hψP 4 j⟩
    rw [hP 2 4 (by decide), Subgroup.mem_bot] at hmem
    exact hj (iψ 2 (by decide) (by rw [hmem, map_one]))
  · rw [h0, nine3_la5_Psi_p12] at h
    have heq : ψ 3 j = ψ 4 j := nine3_la5_eq_one hW h
    have hmem : ψ 3 j ∈ P 3 ⊓ P 4 := ⟨hψP 3 j, by rw [heq]; exact hψP 4 j⟩
    rw [hP 3 4 (by decide), Subgroup.mem_bot] at hmem
    exact hj (iψ 3 (by decide) (by rw [hmem, map_one]))
  · rw [h0, nine3_la5_Psi_top] at h
    have hspec := nine3_la5_psi_special hW ψ hψ1 hψsum j
    have h0' : ψ 0 j = 1 := by rw [hspec]; exact h
    exact hj (iψ 0 (by decide) (by rw [h0', map_one]))

private lemma nine3_la5_Phi_ext {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (φ : Fin 5 → T →* W) (hφ0 : ∀ i, φ 0 i = 1) (hφP : ∀ k i, φ k i ∈ P k)
    (iφ : ∀ k, k ≠ 0 → Function.Injective (φ k))
    (hφsum : ∀ i, ∏ k : Fin 5, φ k i = 1)
    (hnt : ∃ i : T, i ≠ 1) {a b : Fin 3 → Bool}
    (h : ∀ i, nine3_la5_Phi φ a i = nine3_la5_Phi φ b i) : a = b := by
  by_contra hne
  have hw : (fun t => a t ^^ b t) ≠ nine3_la5_gzero := by
    intro hz
    have hz' : (fun t => a t ^^ b t) = fun _ => false := hz
    apply hne
    funext t
    have h' := congrFun hz' t
    cases ha : a t <;> cases hb : b t <;> simp_all
  obtain ⟨i, hi⟩ := hnt
  apply nine3_la5_Phi_ne_one hW P hP φ hφ0 hφP iφ hφsum hw hi
  rw [← nine3_la5_Phi_add hW φ a b i, h i, hW]

private lemma nine3_la5_Psi_ext {T' W : Type} [CommGroup T'] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (ψ : Fin 5 → T' →* W) (hψ1 : ∀ j, ψ 1 j = 1) (hψP : ∀ l j, ψ l j ∈ P l)
    (iψ : ∀ l, l ≠ 1 → Function.Injective (ψ l))
    (hψsum : ∀ j, ∏ l : Fin 5, ψ l j = 1)
    (hnt : ∃ j : T', j ≠ 1) {a b : Fin 3 → Bool}
    (h : ∀ j, nine3_la5_Psi ψ a j = nine3_la5_Psi ψ b j) : a = b := by
  by_contra hne
  have hw : (fun t => a t ^^ b t) ≠ nine3_la5_gzero := by
    intro hz
    have hz' : (fun t => a t ^^ b t) = fun _ => false := hz
    apply hne
    funext t
    have h' := congrFun hz' t
    cases ha : a t <;> cases hb : b t <;> simp_all
  obtain ⟨j, hj⟩ := hnt
  apply nine3_la5_Psi_ne_one hW P hP ψ hψ1 hψP iψ hψsum hw hj
  rw [← nine3_la5_Psi_add hW ψ a b j, h j, hW]

private lemma nine3_la5_cross_single {T' W : Type} [CommGroup T'] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (ψ : Fin 5 → T' →* W) (hψP : ∀ l j, ψ l j ∈ P l)
    (iψ : ∀ l, l ≠ 1 → Function.Injective (ψ l))
    {x y : Fin 5} (hxy : x ≠ y) (hy1 : y ≠ 1) {j : T'} {a : W}
    (hax : a ∈ P x) (h : a = ψ y j) : j = 1 := by
  have hmem : ψ y j ∈ P x ⊓ P y := ⟨by rw [← h]; exact hax, hψP y j⟩
  rw [hP x y hxy, Subgroup.mem_bot] at hmem
  exact iψ y hy1 (by rw [hmem, map_one])

private lemma nine3_la5_cross_pair {T' W : Type} [CommGroup T'] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (ψ : Fin 5 → T' →* W) (hψP : ∀ l j, ψ l j ∈ P l)
    (iψ : ∀ l, l ≠ 1 → Function.Injective (ψ l))
    {x y : Fin 5} (hxy : x ≠ y) (hy1 : y ≠ 1) {j : T'} {a : W}
    (hax : a ∈ P x) (h : a = ψ x j * ψ y j) : j = 1 := by
  have hmem : ψ y j ∈ P x ⊓ P y := by
    refine ⟨?_, hψP y j⟩
    rw [nine3_la5_eq_mul_of_eq_mul hW h]
    exact Subgroup.mul_mem _ hax (hψP x j)
  rw [hP x y hxy, Subgroup.mem_bot] at hmem
  exact iψ y hy1 (by rw [hmem, map_one])

private lemma nine3_la5_cross_top {T' W : Type} [CommGroup T'] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (ψ : Fin 5 → T' →* W) (hψP : ∀ l j, ψ l j ∈ P l)
    (iψ : ∀ l, l ≠ 1 → Function.Injective (ψ l))
    {x : Fin 5} (hx0 : x ≠ 0) {j : T'} {a : W}
    (hax : a ∈ P x) (h : a = ψ 0 j) : j = 1 := by
  have hmem : ψ 0 j ∈ P x ⊓ P 0 := ⟨by rw [← h]; exact hax, hψP 0 j⟩
  rw [hP x 0 hx0, Subgroup.mem_bot] at hmem
  exact iψ 0 (by decide) (by rw [hmem, map_one])

private lemma nine3_la5_cross_compl {T' W : Type} [CommGroup T'] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (ψ : Fin 5 → T' →* W) (hψP : ∀ l j, ψ l j ∈ P l)
    (iψ : ∀ l, l ≠ 1 → Function.Injective (ψ l))
    {x : Fin 5} (hx0 : x ≠ 0) {j : T'} {a : W}
    (hax : a ∈ P x) (h : ψ 0 j = a * ψ x j) : j = 1 := by
  have hmem : ψ 0 j ∈ P x ⊓ P 0 :=
    ⟨by rw [h]; exact Subgroup.mul_mem _ hax (hψP x j), hψP 0 j⟩
  rw [hP x 0 hx0, Subgroup.mem_bot] at hmem
  exact iψ 0 (by decide) (by rw [hmem, map_one])

private lemma nine3_la5_cover {u v w h : Fin 3 → Bool}
    (hu : u = nine3_la5_p01 ∨ u = nine3_la5_p02 ∨ u = nine3_la5_p12)
    (hv : v = nine3_la5_p01 ∨ v = nine3_la5_p02 ∨ v = nine3_la5_p12)
    (hw : w = nine3_la5_p01 ∨ w = nine3_la5_p02 ∨ w = nine3_la5_p12)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hh : h = nine3_la5_p01 ∨ h = nine3_la5_p02 ∨ h = nine3_la5_p12) :
    h = u ∨ h = v ∨ h = w := by
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl <;>
    first | decide | (exfalso; simp_all)

private lemma nine3_la5_eq_of_mul_eq_one' {G : Type} [CommGroup G] (hG : ∀ x : G, x * x = 1)
    {a b : G} (h : a * b = 1) : b = a := by
  calc b = 1 * b := (one_mul b).symm
    _ = (a * a) * b := by rw [hG a]
    _ = a * (a * b) := by rw [mul_assoc]
    _ = a * 1 := by rw [h]
    _ = a := mul_one a

private lemma nine3_la5_pair_terms {T T' W : Type} [CommGroup T] [CommGroup T']
    [CommGroup W] (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (φ : Fin 5 → T →* W) (ψ : Fin 5 → T' →* W)
    (hφP : ∀ k i, φ k i ∈ P k) (hψP : ∀ l j, ψ l j ∈ P l)
    {a b : Fin 5} (hab : a ≠ b) {i : T} {j : T'}
    (h : φ a i * φ b i = ψ a j * ψ b j) :
    φ a i = ψ a j ∧ φ b i = ψ b j := by
  have h1 : (φ a i * ψ a j) * (φ b i * ψ b j) = 1 := by
    calc (φ a i * ψ a j) * (φ b i * ψ b j)
        = (φ a i * φ b i) * (ψ a j * ψ b j) := by ac_rfl
      _ = (ψ a j * ψ b j) * (ψ a j * ψ b j) := by rw [h]
      _ = 1 := hW _
  have h2 : φ a i * ψ a j = φ b i * ψ b j := nine3_la5_eq_one hW h1
  have hmem : φ a i * ψ a j ∈ P a ⊓ P b :=
    ⟨Subgroup.mul_mem _ (hφP a i) (hψP a j),
      by rw [h2]; exact Subgroup.mul_mem _ (hφP b i) (hψP b j)⟩
  rw [hP a b hab, Subgroup.mem_bot] at hmem
  refine ⟨nine3_la5_eq_one hW hmem, ?_⟩
  have h3 : φ b i * ψ b j = 1 := by rw [← h2]; exact hmem
  exact nine3_la5_eq_one hW h3

private lemma nine3_la5_cross_single_L {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (φ : Fin 5 → T →* W) (hφP : ∀ k i, φ k i ∈ P k)
    (iφ : ∀ k, k ≠ 0 → Function.Injective (φ k))
    {x y : Fin 5} (hxy : x ≠ y) (hx0 : x ≠ 0) (hy0 : y ≠ 0) {i : T} {a : W}
    (hax : a ∈ P x) (h : a = φ y i) : i = 1 := by
  have hmem : φ y i ∈ P x ⊓ P y := ⟨by rw [← h]; exact hax, hφP y i⟩
  rw [hP x y hxy, Subgroup.mem_bot] at hmem
  exact iφ y hy0 (by rw [hmem, map_one])

private lemma nine3_la5_cross_pair_L {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (φ : Fin 5 → T →* W) (hφP : ∀ k i, φ k i ∈ P k)
    (iφ : ∀ k, k ≠ 0 → Function.Injective (φ k))
    {x y : Fin 5} (hxy : x ≠ y) (hx0 : x ≠ 0) (hy0 : y ≠ 0) {i : T} {a : W}
    (hax : a ∈ P x) (h : a = φ x i * φ y i) : i = 1 := by
  have hmem : φ y i ∈ P x ⊓ P y := by
    refine ⟨?_, hφP y i⟩
    rw [nine3_la5_eq_mul_of_eq_mul hW h]
    exact Subgroup.mul_mem _ hax (hφP x i)
  rw [hP x y hxy, Subgroup.mem_bot] at hmem
  exact iφ y hy0 (by rw [hmem, map_one])

private lemma nine3_la5_cross_special {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (φ : Fin 5 → T →* W) (hφP : ∀ k i, φ k i ∈ P k)
    (iφ : ∀ k, k ≠ 0 → Function.Injective (φ k))
    {x : Fin 5} (hx1 : x ≠ 1) {i : T} {a : W}
    (hax : a ∈ P x) (h : a = φ 1 i) : i = 1 := by
  have hmem : φ 1 i ∈ P x ⊓ P 1 := ⟨by rw [← h]; exact hax, hφP 1 i⟩
  rw [hP x 1 hx1, Subgroup.mem_bot] at hmem
  exact iφ 1 (by decide) (by rw [hmem, map_one])

private lemma nine3_la5_cross_compl_L {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 5 → Subgroup W)
    (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (φ : Fin 5 → T →* W) (hφP : ∀ k i, φ k i ∈ P k)
    (iφ : ∀ k, k ≠ 0 → Function.Injective (φ k))
    {x : Fin 5} (hx1 : x ≠ 1) {i : T} {a : W}
    (hax : a ∈ P x) (h : φ 1 i = a * φ x i) : i = 1 := by
  have hmem : φ 1 i ∈ P x ⊓ P 1 :=
    ⟨by rw [h]; exact Subgroup.mul_mem _ hax (hφP x i), hφP 1 i⟩
  rw [hP x 1 hx1, Subgroup.mem_bot] at hmem
  exact iφ 1 (by decide) (by rw [hmem, map_one])

private def nine3_la5_pt (t : Fin 3) : Fin 3 → Bool := fun s => decide (s ≠ t)

private lemma nine3_la5_pt_zero : nine3_la5_pt 0 = nine3_la5_p12 := by decide
private lemma nine3_la5_pt_one : nine3_la5_pt 1 = nine3_la5_p02 := by decide
private lemma nine3_la5_pt_two : nine3_la5_pt 2 = nine3_la5_p01 := by decide

private lemma nine3_la5_pt_mem (t : Fin 3) :
    nine3_la5_pt t = nine3_la5_p01 ∨ nine3_la5_pt t = nine3_la5_p02 ∨
      nine3_la5_pt t = nine3_la5_p12 := by
  revert t
  decide

private lemma nine3_la5_pt_ne_gzero (t : Fin 3) : nine3_la5_pt t ≠ nine3_la5_gzero := by
  revert t
  decide

theorem nine3_la_five {T T' W : Type} [CommGroup T] [CommGroup T'] [CommGroup W]
    (hT : ∀ i : T, i * i = 1) (hT' : ∀ j : T', j * j = 1) (hW : ∀ w : W, w * w = 1)
    (P : Fin 5 → Subgroup W) (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (φ : Fin 5 → T →* W) (ψ : Fin 5 → T' →* W) (hφ0 : ∀ i, φ 0 i = 1) (hψ1 : ∀ j, ψ 1 j = 1)
    (hφP : ∀ k i, φ k i ∈ P k) (hψP : ∀ l j, ψ l j ∈ P l)
    (iφ : ∀ k, k ≠ 0 → Function.Injective (φ k)) (iψ : ∀ l, l ≠ 1 → Function.Injective (ψ l))
    (hφsum : ∀ i, ∏ k, φ k i = 1) (hψsum : ∀ j, ∏ l, ψ l j = 1)
    (hrank : ∃ i₁ i₂ : T, i₁ ≠ 1 ∧ i₂ ≠ 1 ∧ i₁ ≠ i₂)
    (hrank' : ∃ j₁ j₂ : T', j₁ ≠ 1 ∧ j₂ ≠ 1 ∧ j₁ ≠ j₂) (β : T → T' → W)
    (hs : ∀ j, ∃ ε : Fin 5 → Bool, ∀ i, β i j = ∏ k, (if ε k then φ k i else 1))
    (hp : ∀ i, ∃ π : Fin 5 → Bool, ∀ j, β i j = ∏ l, (if π l then ψ l j else 1)) :
    ∀ (j : T') (ε : Fin 5 → Bool), (∀ i, β i j = ∏ k, (if ε k then φ k i else 1)) →
      ε 1 = ε 2 ∧ ε 2 = ε 3 ∧ ε 3 = ε 4 := by
  classical
  have hntT : ∃ i : T, i ≠ 1 := by
    obtain ⟨a, b, ha, hb, hab⟩ := hrank
    exact ⟨a, ha⟩
  have hntT' : ∃ j : T', j ≠ 1 := by
    obtain ⟨a, b, ha, hb, hab⟩ := hrank'
    exact ⟨a, ha⟩
  obtain ⟨i0, hi0⟩ := hntT
  obtain ⟨j0, hj0⟩ := hntT'
  let E : T' → Fin 5 → Bool := fun j => Classical.choose (hs j)
  have hE : ∀ j i, β i j = ∏ k : Fin 5, (if E j k then φ k i else 1) :=
    fun j i => Classical.choose_spec (hs j) i
  let Θ : T → Fin 5 → Bool := fun i => Classical.choose (hp i)
  have hΘ : ∀ i j, β i j = ∏ l : Fin 5, (if Θ i l then ψ l j else 1) :=
    fun i j => Classical.choose_spec (hp i) j
  let c : T' → Fin 3 → Bool := fun j t => E j (nine3_la5_tau t) ^^ E j 1
  let d : T → Fin 3 → Bool := fun i t => Θ i (nine3_la5_tau t) ^^ Θ i 0
  have hcE : ∀ j i, β i j = nine3_la5_Phi φ (c j) i := by
    intro j i
    rw [hE j i]
    exact (nine3_la5_Phi_rep hW φ hφ0 hφsum (E j) i).symm
  have hdP : ∀ i j, β i j = nine3_la5_Psi ψ (d i) j := by
    intro i j
    rw [hΘ i j]
    exact (nine3_la5_Psi_rep hW ψ hψ1 hψsum (Θ i) j).symm
  have hpair : ∀ i j, nine3_la5_Phi φ (c j) i = nine3_la5_Psi ψ (d i) j := by
    intro i j
    rw [← hcE j i, hdP i j]
  have hc_zero : c 1 = nine3_la5_gzero := by
    by_contra hne
    have h1 : nine3_la5_Phi φ (c 1) i0 = 1 := by
      rw [hpair i0 1]
      simp [nine3_la5_Psi]
    exact nine3_la5_Phi_ne_one hW P hP φ hφ0 hφP iφ hφsum hne hi0 h1
  have hd_zero : d 1 = nine3_la5_gzero := by
    by_contra hne
    have h1 : nine3_la5_Psi ψ (d 1) j0 = 1 := by
      rw [← hpair 1 j0]
      simp [nine3_la5_Phi]
    exact nine3_la5_Psi_ne_one hW P hP ψ hψ1 hψP iψ hψsum hne hj0 h1
  have hconst : ∀ ε : Fin 5 → Bool,
      (fun t => ε (nine3_la5_tau t) ^^ ε 1) = nine3_la5_gzero →
      ε 1 = ε 2 ∧ ε 2 = ε 3 ∧ ε 3 = ε 4 := by
    intro ε h
    have hrep : (fun t => ε (nine3_la5_tau t) ^^ ε 1) = fun _ => false := h
    have hh : ∀ t : Fin 3, ε (nine3_la5_tau t) = ε 1 := by
      intro t
      have h' := congrFun hrep t
      cases h2 : ε (nine3_la5_tau t) <;> cases h1 : ε 1 <;> simp_all
    have e2 : ε 2 = ε 1 := by simpa [nine3_la5_tau] using hh 0
    have e3 : ε 3 = ε 1 := by simpa [nine3_la5_tau] using hh 1
    have e4 : ε 4 = ε 1 := by simpa [nine3_la5_tau] using hh 2
    exact ⟨e2.symm, e2.trans e3.symm, e3.trans e4.symm⟩
  by_cases hA : ∃ j : T', j ≠ 1 ∧ c j = nine3_la5_gzero
  · obtain ⟨jA, hjA, hcA⟩ := hA
    have hd_all : ∀ i : T, d i = nine3_la5_gzero := by
      intro i
      by_contra hne
      have hz : nine3_la5_Psi ψ (d i) jA = 1 := by
        rw [← hpair i jA, hcA, nine3_la5_Phi_zero]
      exact nine3_la5_Psi_ne_one hW P hP ψ hψ1 hψP iψ hψsum hne hjA hz
    have hbeta1 : ∀ i j, β i j = 1 := by
      intro i j
      rw [hdP i j, hd_all i, nine3_la5_Psi_zero]
    intro j ε hε
    have hcj : c j = nine3_la5_gzero := by
      by_contra hne
      have hz : nine3_la5_Phi φ (c j) i0 = 1 := by
        rw [← hcE j i0, hbeta1 i0 j]
      exact nine3_la5_Phi_ne_one hW P hP φ hφ0 hφP iφ hφsum hne hi0 hz
    have hrep : (fun t => ε (nine3_la5_tau t) ^^ ε 1) = c j := by
      refine nine3_la5_Phi_ext hW P hP φ hφ0 hφP iφ hφsum ⟨i0, hi0⟩ ?_
      intro i
      rw [nine3_la5_Phi_rep hW φ hφ0 hφsum ε i, ← hε i, hcE j i]
    exact hconst ε (by rw [hrep, hcj])
  · by_cases hB : ∃ i : T, i ≠ 1 ∧ d i = nine3_la5_gzero
    · obtain ⟨iB, hiB, hdB⟩ := hB
      have hc_all : ∀ j : T', c j = nine3_la5_gzero := by
        intro j
        by_contra hne
        have hz : nine3_la5_Phi φ (c j) iB = 1 := by
          rw [hpair iB j, hdB, nine3_la5_Psi_zero]
        exact nine3_la5_Phi_ne_one hW P hP φ hφ0 hφP iφ hφsum hne hiB hz
      have hbeta1 : ∀ i j, β i j = 1 := by
        intro i j
        rw [hcE j i, hc_all j, nine3_la5_Phi_zero]
      intro j ε hε
      have hcj : c j = nine3_la5_gzero := hc_all j
      have hrep : (fun t => ε (nine3_la5_tau t) ^^ ε 1) = c j := by
        refine nine3_la5_Phi_ext hW P hP φ hφ0 hφP iφ hφsum ⟨i0, hi0⟩ ?_
        intro i
        rw [nine3_la5_Phi_rep hW φ hφ0 hφsum ε i, ← hε i, hcE j i]
      exact hconst ε (by rw [hrep, hcj])
    · have hne_c : ∀ j : T', j ≠ 1 → c j ≠ nine3_la5_gzero := by
        intro j hj h
        exact hA ⟨j, hj, h⟩
      have hne_d : ∀ i : T, i ≠ 1 → d i ≠ nine3_la5_gzero := by
        intro i hi h
        exact hB ⟨i, hi, h⟩
      have hbeta_mul : ∀ i j j', β i (j * j') = β i j * β i j' := by
        intro i j j'
        rw [hdP i (j * j'), hdP i j, hdP i j']
        simp only [nine3_la5_Psi]
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun t _ => by
          cases h : d i t <;> simp [h, map_mul])
      have hbeta_mul_left : ∀ i i' j, β (i * i') j = β i j * β i' j := by
        intro i i' j
        rw [hcE j (i * i'), hcE j i, hcE j i']
        simp only [nine3_la5_Phi]
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun t _ => by
          cases h : c j t <;> simp [h, map_mul])
      have hc_add : ∀ j j', c (j * j') = fun t => c j t ^^ c j' t := by
        intro j j'
        refine nine3_la5_Phi_ext hW P hP φ hφ0 hφP iφ hφsum ⟨i0, hi0⟩ ?_
        intro i
        rw [← hcE (j * j') i, hbeta_mul i j j', hcE j i, hcE j' i]
        exact nine3_la5_Phi_add hW φ (c j) (c j') i
      have hd_add : ∀ i i', d (i * i') = fun t => d i t ^^ d i' t := by
        intro i i'
        refine nine3_la5_Psi_ext hW P hP ψ hψ1 hψP iψ hψsum ⟨j0, hj0⟩ ?_
        intro j
        rw [← hdP (i * i') j, hbeta_mul_left i i' j, hdP i j, hdP i' j]
        exact nine3_la5_Psi_add hW ψ (d i) (d i') j
      have hc_inj : Function.Injective c := by
        intro j j' h
        by_contra hne
        have h1 : c (j * j') = nine3_la5_gzero := by
          rw [hc_add j j', h]
          funext t
          simp [nine3_la5_gzero, Bool.xor_self]
        have hjj : j * j' ≠ 1 := by
          intro hh
          exact hne (nine3_la5_eq_of_mul_eq_one' hT' hh).symm
        exact hne_c (j * j') hjj h1
      have hd_inj : Function.Injective d := by
        intro i i' h
        by_contra hne
        have h1 : d (i * i') = nine3_la5_gzero := by
          rw [hd_add i i', h]
          funext t
          simp [nine3_la5_gzero, Bool.xor_self]
        have hii : i * i' ≠ 1 := by
          intro hh
          exact hne (nine3_la5_eq_of_mul_eq_one' hT hh).symm
        exact hne_d (i * i') hii h1
      have hex_i : ∀ v : Fin 3 → Bool, ∃ i : T, i ≠ 1 ∧ d i ≠ v := by
        intro v
        obtain ⟨a, b, ha, hb, hab⟩ := hrank
        by_cases h : d a = v
        · exact ⟨b, hb, by intro hh; exact hab (hd_inj (h.trans hh.symm))⟩
        · exact ⟨a, ha, h⟩
      have hex_j : ∀ v : Fin 3 → Bool, ∃ j : T', j ≠ 1 ∧ c j ≠ v := by
        intro v
        obtain ⟨a, b, ha, hb, hab⟩ := hrank'
        by_cases h : c a = v
        · exact ⟨b, hb, by intro hh; exact hab (hc_inj (h.trans hh.symm))⟩
        · exact ⟨a, ha, h⟩
      have hc_no_e0 : ∀ j : T', j ≠ 1 → c j ≠ nine3_la5_e0 := by
        intro j hj hcj
        obtain ⟨i, hi, hdi⟩ := hex_i nine3_la5_e0
        have hEq := hpair i j
        rw [hcj, nine3_la5_Phi_e0] at hEq
        have hclass := nine3_la5_classify (hne_d i hi)
        rcases hclass with hd | hd | hd | hd | hd | hd | hd
        · exact hdi hd
        · rw [hd, nine3_la5_Psi_e1] at hEq
          exact hj (nine3_la5_cross_single hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 2 i) hEq)
        · rw [hd, nine3_la5_Psi_e2] at hEq
          exact hj (nine3_la5_cross_single hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 2 i) hEq)
        · rw [hd, nine3_la5_Psi_p01] at hEq
          exact hj (nine3_la5_cross_pair (x := 2) (y := 3) hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 2 i) hEq)
        · rw [hd, nine3_la5_Psi_p02] at hEq
          exact hj (nine3_la5_cross_pair (x := 2) (y := 4) hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 2 i) hEq)
        · rw [hd, nine3_la5_Psi_p12] at hEq
          have hprod : ψ 0 j = φ 2 i * ψ 2 j := by
            rw [nine3_la5_psi_special hW ψ hψ1 hψsum j, hEq]
            ac_rfl
          exact hj (nine3_la5_cross_compl hW P hP ψ hψP iψ (by decide)
            (hφP 2 i) hprod)
        · rw [hd, nine3_la5_Psi_top, ← nine3_la5_psi_special hW ψ hψ1 hψsum j] at hEq
          exact hj (nine3_la5_cross_top hW P hP ψ hψP iψ (by decide)
            (hφP 2 i) hEq)
      have hc_no_e1 : ∀ j : T', j ≠ 1 → c j ≠ nine3_la5_e1 := by
        intro j hj hcj
        obtain ⟨i, hi, hdi⟩ := hex_i nine3_la5_e1
        have hEq := hpair i j
        rw [hcj, nine3_la5_Phi_e1] at hEq
        have hclass := nine3_la5_classify (hne_d i hi)
        rcases hclass with hd | hd | hd | hd | hd | hd | hd
        · rw [hd, nine3_la5_Psi_e0] at hEq
          exact hj (nine3_la5_cross_single hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 3 i) hEq)
        · exact hdi hd
        · rw [hd, nine3_la5_Psi_e2] at hEq
          exact hj (nine3_la5_cross_single hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 3 i) hEq)
        · rw [hd, nine3_la5_Psi_p01] at hEq
          exact hj (nine3_la5_cross_pair (x := 3) (y := 2) hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 3 i) (by rw [hEq]; ac_rfl))
        · rw [hd, nine3_la5_Psi_p02] at hEq
          have hprod : ψ 0 j = φ 3 i * ψ 3 j := by
            rw [nine3_la5_psi_special hW ψ hψ1 hψsum j, hEq]
            ac_rfl
          exact hj (nine3_la5_cross_compl hW P hP ψ hψP iψ (by decide)
            (hφP 3 i) hprod)
        · rw [hd, nine3_la5_Psi_p12] at hEq
          exact hj (nine3_la5_cross_pair (x := 3) (y := 4) hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 3 i) hEq)
        · rw [hd, nine3_la5_Psi_top, ← nine3_la5_psi_special hW ψ hψ1 hψsum j] at hEq
          exact hj (nine3_la5_cross_top hW P hP ψ hψP iψ (by decide)
            (hφP 3 i) hEq)
      have hc_no_e2 : ∀ j : T', j ≠ 1 → c j ≠ nine3_la5_e2 := by
        intro j hj hcj
        obtain ⟨i, hi, hdi⟩ := hex_i nine3_la5_e2
        have hEq := hpair i j
        rw [hcj, nine3_la5_Phi_e2] at hEq
        have hclass := nine3_la5_classify (hne_d i hi)
        rcases hclass with hd | hd | hd | hd | hd | hd | hd
        · rw [hd, nine3_la5_Psi_e0] at hEq
          exact hj (nine3_la5_cross_single hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 4 i) hEq)
        · rw [hd, nine3_la5_Psi_e1] at hEq
          exact hj (nine3_la5_cross_single hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 4 i) hEq)
        · exact hdi hd
        · rw [hd, nine3_la5_Psi_p01] at hEq
          have hprod : ψ 0 j = φ 4 i * ψ 4 j := by
            rw [nine3_la5_psi_special hW ψ hψ1 hψsum j, hEq]
          exact hj (nine3_la5_cross_compl hW P hP ψ hψP iψ (by decide)
            (hφP 4 i) hprod)
        · rw [hd, nine3_la5_Psi_p02] at hEq
          exact hj (nine3_la5_cross_pair (x := 4) (y := 2) hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 4 i) (by rw [hEq]; ac_rfl))
        · rw [hd, nine3_la5_Psi_p12] at hEq
          exact hj (nine3_la5_cross_pair (x := 4) (y := 3) hW P hP ψ hψP iψ (by decide) (by decide)
            (hφP 4 i) (by rw [hEq]; ac_rfl))
        · rw [hd, nine3_la5_Psi_top, ← nine3_la5_psi_special hW ψ hψ1 hψsum j] at hEq
          exact hj (nine3_la5_cross_top hW P hP ψ hψP iψ (by decide)
            (hφP 4 i) hEq)
      have hc_no_top : ∀ j : T', c j ≠ nine3_la5_gtop := by
        intro jZ hjZ
        obtain ⟨a, b, ha, hb, hab⟩ := hrank'
        have hjW' : ∃ j : T', j ≠ 1 ∧ j ≠ jZ := by
          by_cases h : a = jZ
          · exact ⟨b, hb, by intro hh; exact hab (h.trans hh.symm)⟩
          · exact ⟨a, ha, h⟩
        obtain ⟨jW, hjW, hjWZ⟩ := hjW'
        have hclass := nine3_la5_classify (hne_c jW hjW)
        have hjj : jZ * jW ≠ 1 := by
          intro hh
          exact hjWZ (nine3_la5_eq_of_mul_eq_one' hT' hh)
        rcases hclass with h | h | h | h | h | h | h
        · exact hc_no_e0 jW hjW h
        · exact hc_no_e1 jW hjW h
        · exact hc_no_e2 jW hjW h
        · have hval : c (jZ * jW) = nine3_la5_e2 := by
            rw [hc_add jZ jW, hjZ, h]
            decide
          exact hc_no_e2 (jZ * jW) hjj hval
        · have hval : c (jZ * jW) = nine3_la5_e1 := by
            rw [hc_add jZ jW, hjZ, h]
            decide
          exact hc_no_e1 (jZ * jW) hjj hval
        · have hval : c (jZ * jW) = nine3_la5_e0 := by
            rw [hc_add jZ jW, hjZ, h]
            decide
          exact hc_no_e0 (jZ * jW) hjj hval
        · exact hjWZ (hc_inj (hjZ.trans h.symm)).symm
      have hd_no_e0 : ∀ i : T, i ≠ 1 → d i ≠ nine3_la5_e0 := by
        intro i hi hdi
        obtain ⟨j, hj, hdj⟩ := hex_j nine3_la5_e0
        have hEq := hpair i j
        rw [hdi, nine3_la5_Psi_e0] at hEq
        have hclass := nine3_la5_classify (hne_c j hj)
        rcases hclass with hc | hc | hc | hc | hc | hc | hc
        · exact hdj hc
        · rw [hc, nine3_la5_Phi_e1] at hEq
          exact hi (nine3_la5_cross_single_L hW P hP φ hφP iφ (by decide) (by decide)
            (by decide) (hψP 2 j) hEq.symm)
        · rw [hc, nine3_la5_Phi_e2] at hEq
          exact hi (nine3_la5_cross_single_L hW P hP φ hφP iφ (by decide) (by decide)
            (by decide) (hψP 2 j) hEq.symm)
        · rw [hc, nine3_la5_Phi_p01] at hEq
          exact hi (nine3_la5_cross_pair_L hW P hP φ hφP iφ (by decide) (by decide)
            (by decide) (hψP 2 j) hEq.symm)
        · rw [hc, nine3_la5_Phi_p02] at hEq
          exact hi (nine3_la5_cross_pair_L hW P hP φ hφP iφ (by decide) (by decide)
            (by decide) (hψP 2 j) hEq.symm)
        · rw [hc, nine3_la5_Phi_p12] at hEq
          have hprod : φ 1 i = ψ 2 j * φ 2 i := by
            rw [nine3_la5_phi_special hW φ hφ0 hφsum i, ← hEq]
            ac_rfl
          exact hi (nine3_la5_cross_compl_L hW P hP φ hφP iφ (by decide)
            (hψP 2 j) hprod)
        · rw [hc, nine3_la5_Phi_top, ← nine3_la5_phi_special hW φ hφ0 hφsum i] at hEq
          exact hi (nine3_la5_cross_special hW P hP φ hφP iφ (by decide)
            (hψP 2 j) hEq.symm)
      have hd_no_e1 : ∀ i : T, i ≠ 1 → d i ≠ nine3_la5_e1 := by
        intro i hi hdi
        obtain ⟨j, hj, hdj⟩ := hex_j nine3_la5_e1
        have hEq := hpair i j
        rw [hdi, nine3_la5_Psi_e1] at hEq
        have hclass := nine3_la5_classify (hne_c j hj)
        rcases hclass with hc | hc | hc | hc | hc | hc | hc
        · rw [hc, nine3_la5_Phi_e0] at hEq
          exact hi (nine3_la5_cross_single_L hW P hP φ hφP iφ (by decide) (by decide)
            (by decide) (hψP 3 j) hEq.symm)
        · exact hdj hc
        · rw [hc, nine3_la5_Phi_e2] at hEq
          exact hi (nine3_la5_cross_single_L hW P hP φ hφP iφ (by decide) (by decide)
            (by decide) (hψP 3 j) hEq.symm)
        · rw [hc, nine3_la5_Phi_p01] at hEq
          have hpair' : ψ 3 j = φ 3 i * φ 2 i := by
            rw [← hEq]
            ac_rfl
          exact hi (nine3_la5_cross_pair_L hW P hP φ hφP iφ (by decide) (by decide)
            (by decide) (hψP 3 j) hpair')
        · rw [hc, nine3_la5_Phi_p02] at hEq
          have hprod : φ 1 i = ψ 3 j * φ 3 i := by
            rw [nine3_la5_phi_special hW φ hφ0 hφsum i, ← hEq]
            ac_rfl
          exact hi (nine3_la5_cross_compl_L hW P hP φ hφP iφ (by decide)
            (hψP 3 j) hprod)
        · rw [hc, nine3_la5_Phi_p12] at hEq
          exact hi (nine3_la5_cross_pair_L hW P hP φ hφP iφ (by decide) (by decide)
            (by decide) (hψP 3 j) hEq.symm)
        · rw [hc, nine3_la5_Phi_top, ← nine3_la5_phi_special hW φ hφ0 hφsum i] at hEq
          exact hi (nine3_la5_cross_special hW P hP φ hφP iφ (by decide)
            (hψP 3 j) hEq.symm)
      have hd_no_e2 : ∀ i : T, i ≠ 1 → d i ≠ nine3_la5_e2 := by
        intro i hi hdi
        obtain ⟨j, hj, hdj⟩ := hex_j nine3_la5_e2
        have hEq := hpair i j
        rw [hdi, nine3_la5_Psi_e2] at hEq
        have hclass := nine3_la5_classify (hne_c j hj)
        rcases hclass with hc | hc | hc | hc | hc | hc | hc
        · rw [hc, nine3_la5_Phi_e0] at hEq
          exact hi (nine3_la5_cross_single_L hW P hP φ hφP iφ (by decide) (by decide)
            (by decide) (hψP 4 j) hEq.symm)
        · rw [hc, nine3_la5_Phi_e1] at hEq
          exact hi (nine3_la5_cross_single_L hW P hP φ hφP iφ (by decide) (by decide)
            (by decide) (hψP 4 j) hEq.symm)
        · exact hdj hc
        · rw [hc, nine3_la5_Phi_p01] at hEq
          have hprod : φ 1 i = ψ 4 j * φ 4 i := by
            rw [nine3_la5_phi_special hW φ hφ0 hφsum i, ← hEq]
          exact hi (nine3_la5_cross_compl_L hW P hP φ hφP iφ (by decide)
            (hψP 4 j) hprod)
        · rw [hc, nine3_la5_Phi_p02] at hEq
          exact hi (nine3_la5_cross_pair_L (x := 4) (y := 2) hW P hP φ hφP iφ
            (by decide) (by decide) (by decide) (hψP 4 j) (by rw [← hEq]; ac_rfl))
        · rw [hc, nine3_la5_Phi_p12] at hEq
          exact hi (nine3_la5_cross_pair_L (x := 4) (y := 3) hW P hP φ hφP iφ
            (by decide) (by decide) (by decide) (hψP 4 j) (by rw [← hEq]; ac_rfl))
        · rw [hc, nine3_la5_Phi_top, ← nine3_la5_phi_special hW φ hφ0 hφsum i] at hEq
          exact hi (nine3_la5_cross_special hW P hP φ hφP iφ (by decide)
            (hψP 4 j) hEq.symm)
      have hd_no_top : ∀ i : T, d i ≠ nine3_la5_gtop := by
        intro iZ hiZ
        obtain ⟨a, b, ha, hb, hab⟩ := hrank
        have hiW' : ∃ i : T, i ≠ 1 ∧ i ≠ iZ := by
          by_cases h : a = iZ
          · exact ⟨b, hb, by intro hh; exact hab (h.trans hh.symm)⟩
          · exact ⟨a, ha, h⟩
        obtain ⟨iW, hiW, hiWZ⟩ := hiW'
        have hclass := nine3_la5_classify (hne_d iW hiW)
        have hii : iZ * iW ≠ 1 := by
          intro hh
          exact hiWZ (nine3_la5_eq_of_mul_eq_one' hT hh)
        rcases hclass with h | h | h | h | h | h | h
        · exact hd_no_e0 iW hiW h
        · exact hd_no_e1 iW hiW h
        · exact hd_no_e2 iW hiW h
        · have hval : d (iZ * iW) = nine3_la5_e2 := by
            rw [hd_add iZ iW, hiZ, h]
            decide
          exact hd_no_e2 (iZ * iW) hii hval
        · have hval : d (iZ * iW) = nine3_la5_e1 := by
            rw [hd_add iZ iW, hiZ, h]
            decide
          exact hd_no_e1 (iZ * iW) hii hval
        · have hval : d (iZ * iW) = nine3_la5_e0 := by
            rw [hd_add iZ iW, hiZ, h]
            decide
          exact hd_no_e0 (iZ * iW) hii hval
        · exact hiWZ (hd_inj (hiZ.trans h.symm)).symm
      have hc_pair : ∀ j : T', j ≠ 1 →
          c j = nine3_la5_p01 ∨ c j = nine3_la5_p02 ∨ c j = nine3_la5_p12 := by
        intro j hj
        have hclass := nine3_la5_classify (hne_c j hj)
        rcases hclass with h | h | h | h | h | h | h
        · exact absurd h (hc_no_e0 j hj)
        · exact absurd h (hc_no_e1 j hj)
        · exact absurd h (hc_no_e2 j hj)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact absurd h (hc_no_top j)
      have hd_pair : ∀ i : T, i ≠ 1 →
          d i = nine3_la5_p01 ∨ d i = nine3_la5_p02 ∨ d i = nine3_la5_p12 := by
        intro i hi
        have hclass := nine3_la5_classify (hne_d i hi)
        rcases hclass with h | h | h | h | h | h | h
        · exact absurd h (hd_no_e0 i hi)
        · exact absurd h (hd_no_e1 i hi)
        · exact absurd h (hd_no_e2 i hi)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact absurd h (hd_no_top i)
      obtain ⟨iA, iB, hiA, hiB, hiAB⟩ := hrank
      let iC : T := iA * iB
      have hiC : iC ≠ 1 := by
        intro h
        have h' : iA * iB = 1 := h
        exact hiAB (nine3_la5_eq_of_mul_eq_one' hT h').symm
      have hiCA : iC ≠ iA := by
        intro h
        have h2 : iB = 1 := by
          apply mul_left_cancel (a := iA)
          simpa [iC, mul_one] using h
        exact hiB h2
      have hiCB : iC ≠ iB := by
        intro h
        have h2 : iA = 1 := by
          apply mul_right_cancel (b := iB)
          simpa [iC, one_mul] using h
        exact hiA h2
      have hcover_d : ∀ h : Fin 3 → Bool,
          (h = nine3_la5_p01 ∨ h = nine3_la5_p02 ∨ h = nine3_la5_p12) →
          ∃ i : T, d i = h := by
        intro h hh
        have hres := nine3_la5_cover (u := d iA) (v := d iB) (w := d iC)
          (hd_pair iA hiA) (hd_pair iB hiB) (hd_pair iC hiC)
          (by intro he; exact hiAB (hd_inj he))
          (by intro he; exact hiCA (hd_inj he).symm)
          (by intro he; exact hiCB (hd_inj he).symm) hh
        rcases hres with rfl | rfl | rfl
        · exact ⟨iA, rfl⟩
        · exact ⟨iB, rfl⟩
        · exact ⟨iC, rfl⟩
      obtain ⟨jA, jB, hjA, hjB, hjAB⟩ := hrank'
      let jC : T' := jA * jB
      have hjC : jC ≠ 1 := by
        intro h
        have h' : jA * jB = 1 := h
        exact hjAB (nine3_la5_eq_of_mul_eq_one' hT' h').symm
      have hjCA : jC ≠ jA := by
        intro h
        have h2 : jB = 1 := by
          apply mul_left_cancel (a := jA)
          simpa [jC, mul_one] using h
        exact hjB h2
      have hjCB : jC ≠ jB := by
        intro h
        have h2 : jA = 1 := by
          apply mul_right_cancel (b := jB)
          simpa [jC, one_mul] using h
        exact hjA h2
      have hcover_c : ∀ h : Fin 3 → Bool,
          (h = nine3_la5_p01 ∨ h = nine3_la5_p02 ∨ h = nine3_la5_p12) →
          ∃ j : T', c j = h := by
        intro h hh
        have hres := nine3_la5_cover (u := c jA) (v := c jB) (w := c jC)
          (hc_pair jA hjA) (hc_pair jB hjB) (hc_pair jC hjC)
          (by intro he; exact hjAB (hc_inj he))
          (by intro he; exact hjCA (hc_inj he).symm)
          (by intro he; exact hjCB (hc_inj he).symm) hh
        rcases hres with rfl | rfl | rfl
        · exact ⟨jA, rfl⟩
        · exact ⟨jB, rfl⟩
        · exact ⟨jC, rfl⟩
      have hd_exists : ∀ t : Fin 3, ∃ i : T, d i = nine3_la5_pt t :=
        fun t => hcover_d (nine3_la5_pt t) (nine3_la5_pt_mem t)
      have hc_exists : ∀ t : Fin 3, ∃ j : T', c j = nine3_la5_pt t :=
        fun t => hcover_c (nine3_la5_pt t) (nine3_la5_pt_mem t)
      let iOf : Fin 3 → T := fun t => Classical.choose (hd_exists t)
      have hiOf : ∀ t, d (iOf t) = nine3_la5_pt t :=
        fun t => Classical.choose_spec (hd_exists t)
      let jOf : Fin 3 → T' := fun t => Classical.choose (hc_exists t)
      have hjOf : ∀ t, c (jOf t) = nine3_la5_pt t :=
        fun t => Classical.choose_spec (hc_exists t)
      have hiOf_ne : ∀ t : Fin 3, iOf t ≠ 1 := by
        intro t h
        have h0 : d (iOf t) = nine3_la5_gzero := by rw [h, hd_zero]
        rw [hiOf t] at h0
        exact nine3_la5_pt_ne_gzero t h0
      have hjOf_ne : ∀ t : Fin 3, jOf t ≠ 1 := by
        intro t h
        have h0 : c (jOf t) = nine3_la5_gzero := by rw [h, hc_zero]
        rw [hjOf t] at h0
        exact nine3_la5_pt_ne_gzero t h0
      have hiOf_prod : iOf 0 * iOf 1 * iOf 2 = 1 := by
        have h : d (iOf 0 * iOf 1 * iOf 2) = d 1 := by
          rw [hd_add (iOf 0 * iOf 1) (iOf 2), hd_add (iOf 0) (iOf 1),
            hiOf 0, hiOf 1, hiOf 2, hd_zero]
          decide
        exact hd_inj h
      have hjOf_prod : jOf 0 * jOf 1 * jOf 2 = 1 := by
        have h : c (jOf 0 * jOf 1 * jOf 2) = c 1 := by
          rw [hc_add (jOf 0 * jOf 1) (jOf 2), hc_add (jOf 0) (jOf 1),
            hjOf 0, hjOf 1, hjOf 2, hc_zero]
          decide
        exact hc_inj h
      have hiOf_eq : iOf 0 = iOf 1 * iOf 2 := by
        have h : iOf 0 * (iOf 1 * iOf 2) = 1 := by
          rw [← mul_assoc]
          exact hiOf_prod
        exact nine3_la5_eq_one hT h
      have hjOf_eq : jOf 0 = jOf 1 * jOf 2 := by
        have h : jOf 0 * (jOf 1 * jOf 2) = 1 := by
          rw [← mul_assoc]
          exact hjOf_prod
        exact nine3_la5_eq_one hT' h
      have hp0 : φ 3 (iOf 0) = ψ 3 (jOf 0) ∧ φ 4 (iOf 0) = ψ 4 (jOf 0) := by
        have hp := hpair (iOf 0) (jOf 0)
        rw [hiOf 0, hjOf 0, nine3_la5_pt_zero, nine3_la5_Phi_p12,
          nine3_la5_Psi_p12] at hp
        exact nine3_la5_pair_terms hW P hP φ ψ hφP hψP (by decide) hp
      have hp1 : φ 2 (iOf 1) = ψ 2 (jOf 1) ∧ φ 4 (iOf 1) = ψ 4 (jOf 1) := by
        have hp := hpair (iOf 1) (jOf 1)
        rw [hiOf 1, hjOf 1, nine3_la5_pt_one, nine3_la5_Phi_p02,
          nine3_la5_Psi_p02] at hp
        exact nine3_la5_pair_terms hW P hP φ ψ hφP hψP (by decide) hp
      have hp2 : φ 2 (iOf 2) = ψ 2 (jOf 2) ∧ φ 3 (iOf 2) = ψ 3 (jOf 2) := by
        have hp := hpair (iOf 2) (jOf 2)
        rw [hiOf 2, hjOf 2, nine3_la5_pt_two, nine3_la5_Phi_p01,
          nine3_la5_Psi_p01] at hp
        exact nine3_la5_pair_terms hW P hP φ ψ hφP hψP (by decide) hp
      have h2eq : φ 2 (iOf 0) = ψ 2 (jOf 0) := by
        rw [hiOf_eq, hjOf_eq, map_mul, map_mul, hp1.1, hp2.1]
      have h1eq : φ 1 (iOf 0) = ψ 0 (jOf 0) := by
        rw [nine3_la5_phi_special hW φ hφ0 hφsum (iOf 0),
          nine3_la5_psi_special hW ψ hψ1 hψsum (jOf 0), h2eq, hp0.1, hp0.2]
      have hmem : φ 1 (iOf 0) ∈ P 1 ⊓ P 0 :=
        ⟨hφP 1 (iOf 0), by rw [h1eq]; exact hψP 0 (jOf 0)⟩
      rw [hP 1 0 (by decide), Subgroup.mem_bot] at hmem
      exfalso
      exact hiOf_ne 0 (iφ 1 (by decide) (by rw [hmem, map_one]))

end CFSG.LocalAnalysis.WeakClosure81
