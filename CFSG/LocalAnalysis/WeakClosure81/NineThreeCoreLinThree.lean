module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private lemma nine3_eq_of_mul_eq_one {W : Type} [Monoid W] (hW : ∀ w : W, w * w = 1)
    {a b : W} (h : a * b = 1) : a = b := by
  calc a = a * 1 := (mul_one a).symm
    _ = a * (b * b) := by rw [hW b]
    _ = (a * b) * b := (mul_assoc a b b).symm
    _ = 1 * b := by rw [h]
    _ = b := one_mul b

private lemma nine3_eq_mul_of_mul_eq {W : Type} [Monoid W] {a b c : W}
    (h : a * c = b) (hc : c * c = 1) : a = b * c := by
  calc a = a * 1 := (mul_one a).symm
    _ = a * (c * c) := by rw [hc]
    _ = (a * c) * c := (mul_assoc a c c).symm
    _ = b * c := by rw [h]

private lemma nine3_eq_mul_of_eq_mul {W : Type} [Monoid W] {a b c : W}
    (h : a = b * c) (hc : c * c = 1) : b = a * c := by
  calc b = b * 1 := (mul_one b).symm
    _ = b * (c * c) := by rw [hc]
    _ = (b * c) * c := (mul_assoc b c c).symm
    _ = a * c := by rw [← h]

private lemma nine3_ne_one_of_injective {T W : Type} [Group T] [Group W] (f : T →* W)
    (hf : Function.Injective f) {i : T} (hi : i ≠ 1) : f i ≠ 1 := by
  intro h
  exact hi (hf (by rw [h, map_one]))

private lemma nine3_ite_mul_ite {W : Type} [CommMonoid W] (hW : ∀ w : W, w * w = 1)
    (x : W) (a b : Bool) :
    (if a then x else 1) * (if b then x else 1) = (if Bool.xor a b then x else 1) := by
  cases a <;> cases b <;> simp [Bool.xor, hW x]

private lemma nine3_prod_phi_three {T W : Type} [MulOneClass T] [CommMonoid W] (φ : Fin 3 → T →* W)
    (hφ0 : ∀ i, φ 0 i = 1) (ε : Fin 3 → Bool) (i : T) :
    (∏ k : Fin 3, (if ε k then φ k i else 1)) =
      (if ε 1 then φ 1 i else 1) * (if ε 2 then φ 2 i else 1) := by
  rw [Fin.prod_univ_three]
  cases h0 : ε 0 <;> simp [h0, hφ0 i]

private lemma nine3_prod_psi_three {T' W : Type} [MulOneClass T'] [CommMonoid W]
    (ψ : Fin 3 → T' →* W)
    (hψ1 : ∀ j, ψ 1 j = 1) (π : Fin 3 → Bool) (j : T') :
    (∏ l : Fin 3, (if π l then ψ l j else 1)) =
      (if π 0 then ψ 0 j else 1) * (if π 2 then ψ 2 j else 1) := by
  rw [Fin.prod_univ_three]
  cases h1 : π 1 <;> simp [h1, hψ1 j]

private lemma nine3_phiProd_mul {T W : Type} [MulOneClass T] [CommMonoid W]
    (hW : ∀ w : W, w * w = 1)
    (φ : Fin 3 → T →* W) (ε ε' : Fin 3 → Bool) (i : T) :
    (∏ k : Fin 3, (if ε k then φ k i else 1)) *
      (∏ k : Fin 3, (if ε' k then φ k i else 1)) =
      ∏ k : Fin 3, (if Bool.xor (ε k) (ε' k) then φ k i else 1) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro k _
  exact nine3_ite_mul_ite hW (φ k i) (ε k) (ε' k)

private lemma nine3_psiProd_mul_same {T' W : Type} [MulOneClass T'] [CommMonoid W]
    (ψ : Fin 3 → T' →* W) (π : Fin 3 → Bool) (j j' : T') :
    (∏ l : Fin 3, (if π l then ψ l (j * j') else 1)) =
      (∏ l : Fin 3, (if π l then ψ l j else 1)) *
        (∏ l : Fin 3, (if π l then ψ l j' else 1)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro l _
  cases hπ : π l <;> simp [hπ, map_mul]

private lemma nine3_psiProd_one {T' W : Type} [MulOneClass T'] [CommMonoid W] (ψ : Fin 3 → T' →* W)
    (π : Fin 3 → Bool) : (∏ l : Fin 3, (if π l then ψ l 1 else 1)) = 1 := by
  simp

private lemma nine3_bool_dichotomy (b : Bool) : b = false ∨ b = true := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma nine3_eq_of_xor_eq_false {a b : Bool} (h : Bool.xor a b = false) : a = b := by
  cases a <;> cases b <;> simp_all [Bool.xor]

private lemma nine3_kernel_phi {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 3 → Subgroup W) (hP12 : P 1 ⊓ P 2 = ⊥)
    (φ : Fin 3 → T →* W) (hφ0 : ∀ i, φ 0 i = 1) (hφP : ∀ k i, φ k i ∈ P k)
    (iφ1 : Function.Injective (φ 1)) (iφ2 : Function.Injective (φ 2))
    (hnt : ∃ i : T, i ≠ 1) (ε : Fin 3 → Bool)
    (h : ∀ i, (∏ k : Fin 3, (if ε k then φ k i else 1)) = 1) :
    ε 1 = false ∧ ε 2 = false := by
  obtain ⟨i0, hi0⟩ := hnt
  have h01 : (if ε 1 then φ 1 i0 else 1) * (if ε 2 then φ 2 i0 else 1) = 1 := by
    rw [← nine3_prod_phi_three φ hφ0 ε i0]
    exact h i0
  rcases nine3_bool_dichotomy (ε 1) with h1 | h1
  · rcases nine3_bool_dichotomy (ε 2) with h2 | h2
    · exact ⟨h1, h2⟩
    · exfalso
      rw [h1, h2] at h01
      simp at h01
      exact hi0 (iφ2 (by rw [h01, map_one]))
  · rcases nine3_bool_dichotomy (ε 2) with h2 | h2
    · exfalso
      rw [h1, h2] at h01
      simp at h01
      exact hi0 (iφ1 (by rw [h01, map_one]))
    · exfalso
      rw [h1, h2] at h01
      simp at h01
      have heq : φ 1 i0 = φ 2 i0 := nine3_eq_of_mul_eq_one hW h01
      have hmem : φ 1 i0 ∈ P 1 ⊓ P 2 := ⟨hφP 1 i0, by rw [heq]; exact hφP 2 i0⟩
      rw [hP12] at hmem
      rw [Subgroup.mem_bot] at hmem
      exact hi0 (iφ1 (by rw [hmem, map_one]))

private lemma nine3_rep_unique {T W : Type} [CommGroup T] [CommGroup W]
    (hW : ∀ w : W, w * w = 1) (P : Fin 3 → Subgroup W) (hP12 : P 1 ⊓ P 2 = ⊥)
    (φ : Fin 3 → T →* W) (hφ0 : ∀ i, φ 0 i = 1) (hφP : ∀ k i, φ k i ∈ P k)
    (iφ1 : Function.Injective (φ 1)) (iφ2 : Function.Injective (φ 2))
    (hnt : ∃ i : T, i ≠ 1) (ε ε' : Fin 3 → Bool)
    (h : ∀ i, (∏ k : Fin 3, (if ε k then φ k i else 1)) =
      (∏ k : Fin 3, (if ε' k then φ k i else 1))) :
    ε 1 = ε' 1 ∧ ε 2 = ε' 2 := by
  have hker : ∀ i,
      (∏ k : Fin 3, (if Bool.xor (ε k) (ε' k) then φ k i else 1)) = 1 := by
    intro i
    rw [← nine3_phiProd_mul hW φ ε ε' i, h i]
    exact hW _
  obtain ⟨h1, h2⟩ := nine3_kernel_phi hW P hP12 φ hφ0 hφP iφ1 iφ2 hnt
    (fun k => Bool.xor (ε k) (ε' k)) hker
  exact ⟨nine3_eq_of_xor_eq_false h1, nine3_eq_of_xor_eq_false h2⟩

private lemma nine3_ite_pair_eq_fst {W : Type} [Group W] (hW : ∀ w : W, w * w = 1)
    (P : Fin 3 → Subgroup W)
    (hP02 : P 0 ⊓ P 2 = ⊥) (hP12 : P 1 ⊓ P 2 = ⊥)
    {x1 x2 y0 y2 : W} (hx1P : x1 ∈ P 1) (hx2P : x2 ∈ P 2)
    (hy0P : y0 ∈ P 0) (hy2P : y2 ∈ P 2) (hx1ne : x1 ≠ 1) (hy0ne : y0 ≠ 1)
    (a1 a2 b0 b2 : Bool)
    (h : (if a1 then x1 else 1) * (if a2 then x2 else 1) =
         (if b0 then y0 else 1) * (if b2 then y2 else 1)) :
    a1 = b0 := by
  have hA2 : (if a2 then x2 else 1) ∈ P 2 := by cases a2 <;> simp [hx2P]
  have hB2 : (if b2 then y2 else 1) ∈ P 2 := by cases b2 <;> simp [hy2P]
  have hAsq : (if a2 then x2 else 1) * (if a2 then x2 else 1) = 1 := by
    cases a2 <;> simp [hW x2]
  have hBsq : (if b2 then y2 else 1) * (if b2 then y2 else 1) = 1 := by
    cases b2 <;> simp [hW y2]
  cases a1 <;> cases b0
  · rfl
  · exfalso
    have h' : (if a2 then x2 else 1) = y0 * (if b2 then y2 else 1) := by simpa using h
    have hy0eq : y0 = (if a2 then x2 else 1) * (if b2 then y2 else 1) :=
      nine3_eq_mul_of_eq_mul h' hBsq
    have hy02 : y0 ∈ P 2 := by
      rw [hy0eq]
      exact Subgroup.mul_mem _ hA2 hB2
    have hmem : y0 ∈ P 0 ⊓ P 2 := ⟨hy0P, hy02⟩
    rw [hP02, Subgroup.mem_bot] at hmem
    exact hy0ne hmem
  · exfalso
    have h' : x1 * (if a2 then x2 else 1) = (if b2 then y2 else 1) := by simpa using h
    have hx1eq : x1 = (if b2 then y2 else 1) * (if a2 then x2 else 1) :=
      nine3_eq_mul_of_mul_eq h' hAsq
    have hx12 : x1 ∈ P 2 := by
      rw [hx1eq]
      exact Subgroup.mul_mem _ hB2 hA2
    have hmem : x1 ∈ P 1 ⊓ P 2 := ⟨hx1P, hx12⟩
    rw [hP12, Subgroup.mem_bot] at hmem
    exact hx1ne hmem
  · rfl

private lemma nine3_ite_pair_eq_snd {W : Type} [Group W]
    {x2 y2 : W} (hx2ne : x2 ≠ 1) (hy2ne : y2 ≠ 1) (a2 b2 : Bool)
    (h : (if a2 then x2 else 1) = (if b2 then y2 else 1)) : a2 = b2 := by
  cases a2 <;> cases b2
  · rfl
  · exfalso
    have h' : (1 : W) = y2 := by simpa using h
    exact hy2ne h'.symm
  · exfalso
    have h' : x2 = 1 := by simpa using h
    exact hx2ne h'
  · rfl

theorem nine3_la_three {T T' W : Type} [CommGroup T] [CommGroup T'] [CommGroup W]
    (hT : ∀ i : T, i * i = 1) (hT' : ∀ j : T', j * j = 1) (hW : ∀ w : W, w * w = 1)
    (P : Fin 3 → Subgroup W) (hP : ∀ k l, k ≠ l → P k ⊓ P l = ⊥)
    (φ : Fin 3 → T →* W) (ψ : Fin 3 → T' →* W) (hφ0 : ∀ i, φ 0 i = 1) (hψ1 : ∀ j, ψ 1 j = 1)
    (hφP : ∀ k i, φ k i ∈ P k) (hψP : ∀ l j, ψ l j ∈ P l)
    (iφ : ∀ k, k ≠ 0 → Function.Injective (φ k)) (iψ : ∀ l, l ≠ 1 → Function.Injective (ψ l))
    (hnt : ∃ i : T, i ≠ 1) (hrank : ∃ j₁ j₂ : T', j₁ ≠ 1 ∧ j₂ ≠ 1 ∧ j₁ ≠ j₂)
    (β : T → T' → W)
    (hs : ∀ j, ∃ ε : Fin 3 → Bool, ∀ i, β i j = ∏ k, (if ε k then φ k i else 1))
    (hp : ∀ i, ∃ π : Fin 3 → Bool, ∀ j, β i j = ∏ l, (if π l then ψ l j else 1)) :
    ∀ (j : T') (ε : Fin 3 → Bool), (∀ i, β i j = ∏ k, (if ε k then φ k i else 1)) →
      ε 1 = false ∧ ε 2 = false := by
  classical
  let E : T' → Fin 3 → Bool := fun j => Classical.choose (hs j)
  have hE : ∀ j i, β i j = ∏ k : Fin 3, (if E j k then φ k i else 1) := by
    intro j i
    exact Classical.choose_spec (hs j) i
  let Θ : T → Fin 3 → Bool := fun i => Classical.choose (hp i)
  have hΘ : ∀ i j, β i j = ∏ l : Fin 3, (if Θ i l then ψ l j else 1) := by
    intro i j
    exact Classical.choose_spec (hp i) j
  have hP12 : P 1 ⊓ P 2 = ⊥ := hP 1 2 (by decide)
  have hP02 : P 0 ⊓ P 2 = ⊥ := hP 0 2 (by decide)
  have hiφ1 : Function.Injective (φ 1) := iφ 1 (by decide)
  have hiφ2 : Function.Injective (φ 2) := iφ 2 (by decide)
  have hiψ0 : Function.Injective (ψ 0) := iψ 0 (by decide)
  have hiψ2 : Function.Injective (ψ 2) := iψ 2 (by decide)
  have hβ : ∀ i j j', β i (j * j') = β i j * β i j' := by
    intro i j j'
    rw [hΘ i (j * j'), hΘ i j, hΘ i j']
    exact nine3_psiProd_mul_same ψ (Θ i) j j'
  have huniq : ∀ (j : T') (ε ε' : Fin 3 → Bool),
      (∀ i, β i j = ∏ k : Fin 3, (if ε k then φ k i else 1)) →
      (∀ i, β i j = ∏ k : Fin 3, (if ε' k then φ k i else 1)) →
      ε 1 = ε' 1 ∧ ε 2 = ε' 2 := by
    intro j ε ε' hε hε'
    refine nine3_rep_unique hW P hP12 φ hφ0 hφP hiφ1 hiφ2 hnt ε ε' ?_
    intro i
    exact (hε i).symm.trans (hε' i)
  have hEadd : ∀ j j', E (j * j') 1 = Bool.xor (E j 1) (E j' 1) ∧
      E (j * j') 2 = Bool.xor (E j 2) (E j' 2) := by
    intro j j'
    have hrep : ∀ i, (∏ k : Fin 3, (if E (j * j') k then φ k i else 1)) =
        (∏ k : Fin 3, (if Bool.xor (E j k) (E j' k) then φ k i else 1)) := by
      intro i
      rw [← hE (j * j') i, hβ i j j', hE j i, hE j' i,
        nine3_phiProd_mul hW φ (E j) (E j') i]
    exact nine3_rep_unique hW P hP12 φ hφ0 hφP hiφ1 hiφ2 hnt
      (E (j * j')) (fun k => Bool.xor (E j k) (E j' k)) hrep
  obtain ⟨j1, j2, hj1, hj2, hj12⟩ := hrank
  have hj1j2 : j1 * j2 ≠ 1 := by
    intro h
    have hji : j2 = j1 := by
      calc j2 = 1 * j2 := (one_mul j2).symm
        _ = (j1 * j1) * j2 := by rw [hT' j1]
        _ = j1 * (j1 * j2) := by rw [mul_assoc]
        _ = j1 * 1 := by rw [h]
        _ = j1 := mul_one j1
    exact hj12 hji.symm
  obtain ⟨i0, hi0⟩ := hnt
  have hpair : ∀ i j, i ≠ 1 → j ≠ 1 →
      (if E j 1 then φ 1 i else 1) * (if E j 2 then φ 2 i else 1) =
      (if Θ i 0 then ψ 0 j else 1) * (if Θ i 2 then ψ 2 j else 1) := by
    intro i j hi hj
    have h1 := hE j i
    have h2 := hΘ i j
    rw [nine3_prod_phi_three φ hφ0 (E j) i] at h1
    rw [nine3_prod_psi_three ψ hψ1 (Θ i) j] at h2
    exact h1.symm.trans h2
  have hcoord1 : ∀ i j, i ≠ 1 → j ≠ 1 → E j 1 = Θ i 0 := by
    intro i j hi hj
    exact nine3_ite_pair_eq_fst hW P hP02 hP12 (hφP 1 i) (hφP 2 i) (hψP 0 j) (hψP 2 j)
      (nine3_ne_one_of_injective (φ 1) hiφ1 hi) (nine3_ne_one_of_injective (ψ 0) hiψ0 hj)
      (E j 1) (E j 2) (Θ i 0) (Θ i 2) (hpair i j hi hj)
  have hE1 : ∀ j, E j 1 = false := by
    have h1one : E 1 1 = false := by
      have hker : ∀ i, (∏ k : Fin 3, (if E 1 k then φ k i else 1)) = 1 := by
        intro i
        rw [← hE 1 i, hΘ i 1]
        exact nine3_psiProd_one ψ (Θ i)
      exact (nine3_kernel_phi hW P hP12 φ hφ0 hφP hiφ1 hiφ2 ⟨i0, hi0⟩ (E 1) hker).1
    have hc : Θ i0 0 = false := by
      have h1 : E (j1 * j2) 1 = Θ i0 0 := hcoord1 i0 (j1 * j2) hi0 hj1j2
      have hadd := (hEadd j1 j2).1
      have e1 : E j1 1 = Θ i0 0 := hcoord1 i0 j1 hi0 hj1
      have e2 : E j2 1 = Θ i0 0 := hcoord1 i0 j2 hi0 hj2
      rw [e1, e2, Bool.xor_self] at hadd
      exact h1.symm.trans hadd
    intro j
    by_cases hj : j = 1
    · rw [hj]; exact h1one
    · rw [hcoord1 i0 j hi0 hj, hc]
  have hΘ0 : ∀ i, i ≠ 1 → Θ i 0 = false := by
    intro i hi
    have h := hcoord1 i j1 hi hj1
    rw [hE1 j1] at h
    exact h.symm
  have hcoord2 : ∀ i j, i ≠ 1 → j ≠ 1 → E j 2 = Θ i 2 := by
    intro i j hi hj
    have hp' := hpair i j hi hj
    rw [hE1 j, hΘ0 i hi] at hp'
    simp at hp'
    exact nine3_ite_pair_eq_snd (nine3_ne_one_of_injective (φ 2) hiφ2 hi)
      (nine3_ne_one_of_injective (ψ 2) hiψ2 hj) (E j 2) (Θ i 2) hp'
  have hE2 : ∀ j, E j 2 = false := by
    have h2one : E 1 2 = false := by
      have hker : ∀ i, (∏ k : Fin 3, (if E 1 k then φ k i else 1)) = 1 := by
        intro i
        rw [← hE 1 i, hΘ i 1]
        exact nine3_psiProd_one ψ (Θ i)
      exact (nine3_kernel_phi hW P hP12 φ hφ0 hφP hiφ1 hiφ2 ⟨i0, hi0⟩ (E 1) hker).2
    have hc : Θ i0 2 = false := by
      have h1 : E (j1 * j2) 2 = Θ i0 2 := hcoord2 i0 (j1 * j2) hi0 hj1j2
      have hadd := (hEadd j1 j2).2
      have e1 : E j1 2 = Θ i0 2 := hcoord2 i0 j1 hi0 hj1
      have e2 : E j2 2 = Θ i0 2 := hcoord2 i0 j2 hi0 hj2
      rw [e1, e2, Bool.xor_self] at hadd
      exact h1.symm.trans hadd
    intro j
    by_cases hj : j = 1
    · rw [hj]; exact h2one
    · rw [hcoord2 i0 j hi0 hj, hc]
  intro j ε hε
  obtain ⟨h1, h2⟩ := huniq j ε (E j) hε (hE j)
  exact ⟨h1.trans (hE1 j), h2.trans (hE2 j)⟩

end CFSG.LocalAnalysis.WeakClosure81
