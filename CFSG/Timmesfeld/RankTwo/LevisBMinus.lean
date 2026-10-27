module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Universal.Spin.Twisted.Datum

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg
open scoped commutatorElement

section Helpers

variable (n : ℕ) {F : Type} [Field F] (b c : F)

@[expose] noncomputable def mlr (i j : Fin (n - 1)) (s t : Bool) (a : F) :
    spinGroup (quadMinus n F b c) :=
  if h : i = j then 1 else (minusFrame n b c).longRoot h s t (.ofAdd a)

variable {b c}

noncomputable abbrev msr (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) (s : Bool)
    (p : Fin 2 → F) : spinGroup (quadMinus n F b c) :=
  twShortRoot n hirr i s (.ofAdd p)

variable {n}

theorem mlr_of_ne {i j : Fin (n - 1)} (h : i ≠ j) (s t : Bool) (a : F) :
    mlr n b c i j s t a = (minusFrame n b c).longRoot h s t (.ofAdd a) := by
  rw [mlr, dite_eq_right h]

theorem mlr_add {i j : Fin (n - 1)} (h : i ≠ j) (s t : Bool) (a a' : F) :
    mlr n b c i j s t (a + a') = mlr n b c i j s t a * mlr n b c i j s t a' := by
  rw [mlr_of_ne h, mlr_of_ne h, mlr_of_ne h, ofAdd_add, map_mul]

theorem mlr_swap [CharP F 2] (i j : Fin (n - 1)) (s t : Bool) (a : F) :
    mlr n b c i j s t a = mlr n b c j i t s a := by
  by_cases h : i = j
  · subst h
    simp [mlr]
  · rw [mlr_of_ne h, mlr_of_ne (Ne.symm h), HypFrame.longRoot_swap, CharTwo.neg_eq]

theorem msr_add (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) (s : Bool)
    (p q : Fin 2 → F) : msr n hirr i s (p + q) = msr n hirr i s p * msr n hirr i s q := by
  rw [msr, msr, msr, ofAdd_add, map_mul]

theorem longWeylSign_charTwo [CharP F 2] {m : ℕ} (i k : Fin m) : (longWeylSign i k : F) = 1 := by
  unfold longWeylSign
  split_ifs
  · exact CharTwo.neg_eq 1
  · rfl

theorem longWeyl_conj_mlr [CharP F 2] {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool)
    {k l : Fin (n - 1)} (hkl : k ≠ l) (u v : Bool) (a : F) :
    (minusFrame n b c).longWeyl hij s t * mlr n b c k l u v a *
        ((minusFrame n b c).longWeyl hij s t)⁻¹ =
      mlr n b c (Equiv.swap i j k) (Equiv.swap i j l) (longWeylBool i j s t k u)
        (longWeylBool i j s t l v) a := by
  rw [mlr_of_ne hkl, HypFrame.longWeyl_conj_longRoot,
    mlr_of_ne ((Equiv.swap i j).injective.ne hkl), longWeylSign_charTwo, longWeylSign_charTwo,
    one_mul, one_mul]

theorem longWeyl_conj_msr [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (k : Fin (n - 1)) (u : Bool)
    (p : Fin 2 → F) :
    (minusFrame n b c).longWeyl hij s t * msr n hirr k u p *
        ((minusFrame n b c).longWeyl hij s t)⁻¹ =
      msr n hirr (Equiv.swap i j k) (longWeylBool i j s t k u) p := by
  rw [msr, longWeyl_conj_twShortRoot, longWeylSign_charTwo, one_smul]

theorem shortWeyl_conj_mlr [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) {k l : Fin (n - 1)} (hkl : k ≠ l) (u v : Bool) (a : F) :
    shortWeyl n hirr i * mlr n b c k l u v a * (shortWeyl n hirr i)⁻¹ =
      mlr n b c k l (shortWeylBool i k u) (shortWeylBool i l v) a := by
  rw [mlr_of_ne hkl, shortWeyl_conj_longRoot, mlr_of_ne hkl, longWeylSign_charTwo,
    longWeylSign_charTwo, one_mul, one_mul]

theorem shortWeyl_conj_msr [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (i k : Fin (n - 1)) (u : Bool) (p : Fin 2 → F) :
    shortWeyl n hirr i * msr n hirr k u p * (shortWeyl n hirr i)⁻¹ =
      msr n hirr k (shortWeylBool i k u) (planeRefl b c planeOne p) := by
  rw [msr, shortWeyl_conj_twShortRoot, longWeylSign_charTwo, one_smul]

end Helpers

section B3

@[expose] def b3r : Fin 12 → Fin 3 → ℤ :=
  ![![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1], ![0, 0, -1], ![1, 1, 0],
    ![-1, -1, 0], ![0, 1, 1], ![0, -1, -1], ![0, 1, 2], ![0, -1, -2]]

@[expose] def b3Short : Fin 12 → Bool :=
  ![false, false, false, false, true, true, false, false, true, true, false, false]

@[expose] def b3Li : Fin 12 → Fin 3 := ![0, 1, 1, 2, 0, 0, 0, 2, 0, 0, 1, 1]

@[expose] def b3Lj : Fin 12 → Fin 3 := ![1, 0, 2, 1, 1, 1, 2, 0, 1, 1, 2, 2]

@[expose] def b3Ls : Fin 12 → Bool :=
  ![true, true, true, true, true, true, true, true, true, true, true, false]

@[expose] def b3Lt : Fin 12 → Bool :=
  ![false, false, false, false, false, false, false, false, false, false, true, false]

@[expose] def b3Si : Fin 12 → Fin 3 := ![0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 0, 0]

@[expose] def b3Ss : Fin 12 → Bool :=
  ![true, true, true, true, true, false, true, true, true, false, true, true]

theorem b3r_injective : Function.Injective b3r := by decide

theorem b3Li_ne_b3Lj (a : Fin 12) : b3Li a ≠ b3Lj a := by
  fin_cases a <;> decide

theorem b3_toStdB_long : ∀ a, b3Short a = false →
    toStdB 3 (b3r a) = Pi.single (b3Li a) (boolSign (b3Ls a)) +
      Pi.single (b3Lj a) (boolSign (b3Lt a)) := by
  decide

theorem b3_toStdB_short : ∀ a, b3Short a = true →
    toStdB 3 (b3r a) = Pi.single (b3Si a) (boolSign (b3Ss a)) := by
  decide

theorem b3r_mem_roots (a : Fin 12) :
    b3r a ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanB 3) ∅ := by
  cases ha : b3Short a
  · exact mem_roots_of_toStdB_eq_long 4 (b3Li_ne_b3Lj a) (b3Ls a) (b3Lt a)
      (b3_toStdB_long a ha)
  · exact mem_roots_of_toStdB_eq_short 4 (b3Si a) (b3Ss a) (b3_toStdB_short a ha)

@[expose] def b3Roots : List (Fin 3 → ℤ) :=
  [![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![0, 1, 1], ![1, 1, 1], ![0, 1, 2],
    ![1, 1, 2], ![1, 2, 2], ![-1, 0, 0], ![0, -1, 0], ![0, 0, -1], ![-1, -1, 0], ![0, -1, -1],
    ![-1, -1, -1], ![0, -1, -2], ![-1, -1, -2], ![-1, -2, -2]]

theorem mem_b3Roots {γ : Fin 3 → ℤ}
    (hγ : γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanB 3) ∅) : γ ∈ b3Roots := by
  have hL : ∀ (i j : Fin 3) (s t : Bool), i ≠ j →
      ofStdB 3 (Pi.single i (boolSign s) + Pi.single j (boolSign t)) ∈ b3Roots := by
    decide
  have hS : ∀ (i : Fin 3) (s : Bool), ofStdB 3 (Pi.single i (boolSign s)) ∈ b3Roots := by
    decide
  rcases exists_toStdB_eq_of_mem_roots 4 hγ with ⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩
  · rw [← ofStdB_toStdB 3 γ]
    exact (congrArg (ofStdB 3) h).symm ▸ hL i j s t hij
  · rw [← ofStdB_toStdB 3 γ]
    exact (congrArg (ofStdB 3) h).symm ▸ hS i s

variable {F : Type} [Field F] {b c : F}

variable (b c) in
@[expose] noncomputable def b3xL (a : Fin 12) (x : F) : spinGroup (quadMinus 4 F b c) :=
  mlr 4 b c (b3Li a) (b3Lj a) (b3Ls a) (b3Lt a) x

@[expose] noncomputable def b3xS (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (a : Fin 12)
    (p : Fin 2 → F) : spinGroup (quadMinus 4 F b c) :=
  msr 4 hirr (b3Si a) (b3Ss a) p

variable (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem rootGroup_b3r_long {a : Fin 12} (ha : b3Short a = false) :
    (minusDatum 4 hirr).rootGroup (b3r a) =
      ((minusFrame 4 b c).longRoot (b3Li_ne_b3Lj a) (b3Ls a) (b3Lt a)).range :=
  minusRootGroup_eq_long 4 hirr (b3Li_ne_b3Lj a) (b3Ls a) (b3Lt a) (b3_toStdB_long a ha)

theorem rootGroup_b3r_short {a : Fin 12} (ha : b3Short a = true) :
    (minusDatum 4 hirr).rootGroup (b3r a) = (twShortRoot 4 hirr (b3Si a) (b3Ss a)).range :=
  minusRootGroup_eq_short 4 hirr (b3Si a) (b3Ss a) (b3_toStdB_short a ha)

theorem b3xL_mem {a : Fin 12} (ha : b3Short a = false) (x : F) :
    b3xL b c a x ∈ (minusDatum 4 hirr).rootGroup (b3r a) := by
  rw [rootGroup_b3r_long hirr ha, b3xL, mlr_of_ne (b3Li_ne_b3Lj a)]
  exact ⟨_, rfl⟩

theorem b3xS_mem {a : Fin 12} (ha : b3Short a = true) (p : Fin 2 → F) :
    b3xS hirr a p ∈ (minusDatum 4 hirr).rootGroup (b3r a) := by
  rw [rootGroup_b3r_short hirr ha]
  exact ⟨_, rfl⟩

theorem exists_b3xL_eq {a : Fin 12} (ha : b3Short a = false) {y : spinGroup (quadMinus 4 F b c)}
    (hy : y ∈ (minusDatum 4 hirr).rootGroup (b3r a)) : ∃ x, b3xL b c a x = y := by
  rw [rootGroup_b3r_long hirr ha] at hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨Multiplicative.toAdd x, by rw [b3xL, mlr_of_ne (b3Li_ne_b3Lj a), ofAdd_toAdd]⟩

theorem exists_b3xS_eq {a : Fin 12} (ha : b3Short a = true) {y : spinGroup (quadMinus 4 F b c)}
    (hy : y ∈ (minusDatum 4 hirr).rootGroup (b3r a)) : ∃ p, b3xS hirr a p = y := by
  rw [rootGroup_b3r_short hirr ha] at hy
  obtain ⟨p, rfl⟩ := hy
  exact ⟨Multiplicative.toAdd p, by rw [b3xS, msr, ofAdd_toAdd]⟩

omit hirr in
theorem b3xL_injective (a : Fin 12) : Function.Injective (b3xL b c a) := by
  intro x y h
  rw [b3xL, b3xL, mlr_of_ne (b3Li_ne_b3Lj a), mlr_of_ne (b3Li_ne_b3Lj a)] at h
  exact Multiplicative.ofAdd.injective ((minusFrame 4 b c).longRoot_injective _ _ _ h)

theorem b3xS_injective (a : Fin 12) : Function.Injective (b3xS hirr a) := by
  intro p q h
  exact Multiplicative.ofAdd.injective (twShortRoot_injective 4 hirr _ _ h)

omit hirr in
theorem b3xL_add (a : Fin 12) (x y : F) : b3xL b c a (x + y) = b3xL b c a x * b3xL b c a y :=
  mlr_add (b3Li_ne_b3Lj a) _ _ x y

theorem b3xS_add (a : Fin 12) (p q : Fin 2 → F) :
    b3xS hirr a (p + q) = b3xS hirr a p * b3xS hirr a q :=
  msr_add hirr _ _ p q

abbrev SL2E (b c : F) [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] : Type :=
  @Matrix.SpecialLinearGroup (Fin 2) _ _ (ShortField b c)
    (@Field.toCommRing (ShortField b c) inferInstance)

open Classical in
@[expose] noncomputable def b3PhiOf {G : Type*} [Group G] (fL : Fin 12 → F → G)
    (fS : Fin 12 → (Fin 2 → F) → G) : ∀ γ, (minusDatum 4 hirr).rootGroup γ → G :=
  fun γ y => if h : ∃ a, b3r a = γ then
      if b3Short h.choose then
        (if h' : ∃ p, b3xS hirr h.choose p = y then fS h.choose h'.choose else 1)
      else (if h' : ∃ x, b3xL b c h.choose x = y then fL h.choose h'.choose else 1)
    else 1

variable {G : Type*} [Group G] (fL : Fin 12 → F → G) (fS : Fin 12 → (Fin 2 → F) → G)

theorem b3PhiOf_long {a : Fin 12} (ha : b3Short a = false) (x : F) (hy) :
    b3PhiOf hirr fL fS (b3r a) ⟨b3xL b c a x, hy⟩ = fL a x := by
  classical
  have h : ∃ a', b3r a' = b3r a := ⟨a, rfl⟩
  have hch : h.choose = a := b3r_injective h.choose_spec
  simp only [b3PhiOf, dite_eq_left h]
  generalize h.choose = a' at hch ⊢
  subst hch
  have h' : ∃ x', b3xL b c a' x' = b3xL b c a' x := ⟨x, rfl⟩
  rw [ite_eq_right (by rw [ha]; decide), dite_eq_left h']
  exact congrArg (fL a') (b3xL_injective a' h'.choose_spec)

theorem b3PhiOf_short {a : Fin 12} (ha : b3Short a = true) (p : Fin 2 → F) (hy) :
    b3PhiOf hirr fL fS (b3r a) ⟨b3xS hirr a p, hy⟩ = fS a p := by
  classical
  have h : ∃ a', b3r a' = b3r a := ⟨a, rfl⟩
  have hch : h.choose = a := b3r_injective h.choose_spec
  simp only [b3PhiOf, dite_eq_left h]
  generalize h.choose = a' at hch ⊢
  subst hch
  have h' : ∃ p', b3xS hirr a' p' = b3xS hirr a' p := ⟨p, rfl⟩
  rw [ite_eq_left (by rw [ha]), dite_eq_left h']
  exact congrArg (fS a') (b3xS_injective hirr a' h'.choose_spec)

end B3

end CFSG.Timmesfeld.RankTwo
