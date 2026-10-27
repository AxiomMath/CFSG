module

public import CFSG.LieType.Chevalley.KernelComponentRoots
import CFSG.LocalAnalysis.StandardType.GGHdRo7ExcLin
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcRootReflectionRelations

public section

namespace CFSG.StandardType.E6D4Refl

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.SimplyLacedCover

@[expose] def d4Map : Fin 4 → Fin 6 := ![2, 3, 4, 1]

@[expose] def e6Index (i : Fin 6) : Fin Tag.E6.rank := i

@[expose] def e6Word (l : List (Fin 6)) : List (Fin Tag.E6.rank) := l

@[expose] def e6vec (i : Fin 6) : Fin Tag.E6.rank → ℤ := Pi.single (e6Index i) 1

@[expose] def act (l : List (Fin 6)) (v : Fin Tag.E6.rank → ℤ) :
    Fin Tag.E6.rank → ℤ :=
  (e6Word l).foldr (reflect Tag.E6) v

@[expose] def e6Root (k : Fin 72) : Fin Tag.E6.rank → ℤ := e6Certificate.root k

abbrev SameSign {α : Type*} [InvolutiveNeg α] (a b : α) : Prop := a = b ∨ a = -b

namespace SameSign

variable {α : Type*} [InvolutiveNeg α] {a b c : α}

theorem symm (h : SameSign a b) : SameSign b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

theorem trans (h₁ : SameSign a b) (h₂ : SameSign b c) : SameSign a c := by
  rcases h₁ with rfl | h₁
  · exact h₂
  · rcases h₂ with rfl | h₂
    · exact Or.inr h₁
    · exact Or.inl (by rw [h₁, h₂, neg_neg])

theorem map {β : Type*} [InvolutiveNeg β] (f : α → β) (hf : ∀ x, f (-x) = -f x)
    (h : SameSign a b) : SameSign (f a) (f b) := by
  rcases h with h | h
  · rw [h]
    exact Or.inl rfl
  · rw [h, hf]
    exact Or.inr rfl

end SameSign

theorem act_eq_smul (l : List (Fin 6)) (v : Fin Tag.E6.rank → ℤ) :
    act l v = (coxeterSystem Tag.E6).wordProd (e6Word l) • v :=
  (excWordProd_smul (τ := Tag.E6) (e6Word l) v).symm

theorem act_neg (l : List (Fin 6)) (v : Fin Tag.E6.rank → ℤ) :
    act l (-v) = -act l v := by
  rw [act_eq_smul, act_eq_smul]
  exact smul_neg _ _

theorem act_sameSign (l : List (Fin 6)) {a b : Fin Tag.E6.rank → ℤ}
    (h : SameSign a b) : SameSign (act l a) (act l b) :=
  h.map (act l) (act_neg l)

theorem iform_act
    (l : List (Fin 6)) (x y : Fin Tag.E6.rank → ℤ) :
    iform (τ := Tag.E6) (act l x) (act l y) = iform x y := by
  rw [act_eq_smul, act_eq_smul, iform_smul (τ := Tag.E6)]

theorem iform_sameSign_right
    (x : Fin Tag.E6.rank → ℤ) {a b : Fin Tag.E6.rank → ℤ} (h : SameSign a b) :
    SameSign (iform x a) (iform x b) :=
  h.map (fun y => iform x y) (fun y => by
    rw [← neg_one_smul ℤ y, iform_smul_right (τ := Tag.E6), neg_one_mul])

theorem sameSign_eq_zero {a : ℤ} (h : SameSign a 0) : a = 0 := by
  rcases h with h | h
  · exact h
  · rwa [neg_zero] at h

@[expose] def wordATable : List (List (Fin 6)) :=
  [[2, 3, 0, 2],
    [1, 3],
    [2, 3],
    [],
    [4, 3],
    [4, 5, 3, 4],
    [2, 3, 0, 2],
    [2, 3, 0],
    [1, 3],
    [1],
    [2, 3],
    [2],
    [],
    [4],
    [4, 3],
    [4, 5, 3],
    [4, 5, 3, 4],
    [2, 3, 0],
    [2, 0],
    [1],
    [2, 1],
    [4, 1],
    [2],
    [4, 2],
    [4],
    [4, 5],
    [4, 5, 3],
    [2, 0],
    [2, 1, 0],
    [4, 2, 0],
    [2, 1],
    [4, 1],
    [4, 2, 1],
    [4, 5, 1],
    [4, 2],
    [4, 5, 2],
    [4, 5],
    [2, 1, 0],
    [4, 2, 0],
    [4, 2, 1, 0],
    [4, 5, 2, 0],
    [4, 2, 1],
    [4, 5, 1],
    [4, 2, 1, 3],
    [4, 5, 2, 1],
    [4, 5, 2],
    [4, 2, 1, 0],
    [4, 5, 2, 0],
    [4, 2, 1, 3, 0],
    [4, 5, 2, 1, 0],
    [4, 2, 1, 3],
    [4, 5, 2, 1],
    [4, 5, 2, 1, 3],
    [4, 2, 1, 3, 0],
    [4, 5, 2, 1, 0],
    [4, 2, 1, 3, 0, 2],
    [4, 5, 2, 1, 3, 0],
    [4, 5, 2, 1, 3],
    [4, 5, 2, 1, 3, 4],
    [4, 2, 1, 3, 0, 2],
    [4, 5, 2, 1, 3, 0],
    [4, 5, 2, 1, 3, 0, 2],
    [4, 5, 2, 1, 3, 4, 0],
    [4, 5, 2, 1, 3, 4],
    [4, 5, 2, 1, 3, 0, 2],
    [4, 5, 2, 1, 3, 4, 0],
    [4, 5, 2, 1, 3, 4, 0, 2],
    [4, 5, 2, 1, 3, 4, 0, 2],
    [4, 5, 2, 1, 3, 4, 0, 2, 3],
    [4, 5, 2, 1, 3, 4, 0, 2, 3],
    [4, 5, 2, 1, 3, 4, 0, 2, 3, 1],
    [4, 5, 2, 1, 3, 4, 0, 2, 3, 1]]

@[expose] def wordBTable : List (List (Fin 6)) :=
  [[],
    [3, 2, 1, 3, 2, 1],
    [],
    [],
    [1, 3, 4, 2, 3, 1],
    [],
    [],
    [0],
    [3, 2, 1, 3, 2, 1],
    [2, 1, 3, 2, 1],
    [],
    [3],
    [],
    [2, 3, 4, 3, 2],
    [1, 3, 4, 2, 3, 1],
    [1, 3, 4, 5, 2, 3, 1],
    [],
    [0],
    [3, 0],
    [2, 1, 3, 2, 1],
    [],
    [],
    [3],
    [],
    [2, 3, 4, 3, 2],
    [2, 3, 4, 5, 3, 2],
    [1, 3, 4, 5, 2, 3, 1],
    [3, 0],
    [],
    [],
    [],
    [],
    [1, 3, 4, 3, 1],
    [],
    [],
    [],
    [2, 3, 4, 5, 3, 2],
    [],
    [],
    [1, 3, 4, 3, 1, 0],
    [],
    [1, 3, 4, 3, 1],
    [],
    [1, 3, 4, 1, 3, 1],
    [1, 3, 4, 5, 3, 1],
    [],
    [1, 3, 4, 3, 1, 0],
    [],
    [1, 3, 4, 1, 3, 1, 0],
    [1, 3, 4, 5, 3, 1, 0],
    [1, 3, 4, 1, 3, 1],
    [1, 3, 4, 5, 3, 1],
    [1, 3, 4, 5, 1, 3, 1],
    [1, 3, 4, 1, 3, 1, 0],
    [1, 3, 4, 5, 3, 1, 0],
    [],
    [1, 3, 4, 5, 1, 3, 1, 0],
    [1, 3, 4, 5, 1, 3, 1],
    [],
    [],
    [1, 3, 4, 5, 1, 3, 1, 0],
    [],
    [],
    [],
    [],
    [],
    [1, 3, 4, 5, 3, 0, 2, 1, 3, 4, 3, 2],
    [1, 3, 4, 5, 3, 0, 2, 1, 3, 4, 3, 2],
    [2, 3, 4, 5, 0, 2, 1, 3, 4, 2, 3, 0, 2],
    [2, 3, 4, 5, 0, 2, 1, 3, 4, 2, 3, 0, 2],
    [],
    []]

@[expose] def wordCTable : List (List (Fin 6)) :=
  [[],
    [0, 2, 3, 4, 1, 3, 2, 0],
    [],
    [],
    [],
    [],
    [],
    [],
    [0, 2, 3, 4, 1, 3, 2, 0],
    [],
    [],
    [],
    [],
    [],
    [],
    [5],
    [],
    [],
    [0, 2, 3, 4, 3, 2, 0],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [5],
    [0, 2, 3, 4, 3, 2, 0],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [0, 2, 1, 3, 2, 1, 0],
    [],
    [],
    [],
    [5, 4, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 2, 1],
    [],
    [],
    [0, 2, 1, 3, 2, 1, 0],
    [],
    [],
    [5, 0, 2, 1, 3, 2, 1, 0],
    [5, 4, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 2, 1],
    [],
    [5, 4, 3, 2, 1, 3, 4, 3, 2, 1, 3, 2, 1],
    [],
    [5, 0, 2, 1, 3, 2, 1, 0],
    [],
    [],
    [5, 4, 3, 2, 1, 3, 4, 3, 2, 1, 3, 2, 1],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 2],
    [5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 2],
    [],
    []]

@[expose] def wordDTable : List (List (Fin 6)) :=
  [[],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 0, 2, 1, 3, 2, 1, 0],
    [],
    [],
    [],
    [],
    [],
    [0, 2, 3, 4, 5, 4, 3, 2, 0],
    [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 0, 2, 1, 3, 2, 1, 0],
    [],
    [],
    [],
    [0, 2, 3, 4, 5, 4, 3, 2, 0],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [0, 2, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 2, 1],
    [0, 2, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 2, 1],
    [],
    []]

@[expose] def wordA (k : Fin 72) : List (Fin 6) := wordATable.getD k.val []

@[expose] def wordB (k : Fin 72) : List (Fin 6) := wordBTable.getD k.val []

@[expose] def wordC (k : Fin 72) : List (Fin 6) := wordCTable.getD k.val []

@[expose] def wordD (k : Fin 72) : List (Fin 6) := wordDTable.getD k.val []

theorem wordA_spec : ∀ k : Fin 72, SameSign (act (wordA k) (e6Root k)) (e6vec 3) := by
  decide +kernel

theorem wordB_spec : ∀ k : Fin 72,
    SameSign (iform (τ := Tag.E6) (e6Root k) (e6vec 3)) 1 →
      SameSign (act (wordB k) (e6vec 3)) (e6vec 3) ∧
        SameSign (act (wordB k) (e6Root k)) (e6vec 2) := by
  decide +kernel

theorem wordC_spec : ∀ k : Fin 72,
    SameSign (iform (τ := Tag.E6) (e6Root k) (e6vec 3)) 1 →
      iform (τ := Tag.E6) (e6Root k) (e6vec 2) = 0 →
        SameSign (act (wordC k) (e6vec 3)) (e6vec 3) ∧
          SameSign (act (wordC k) (e6vec 2)) (e6vec 2) ∧
            SameSign (act (wordC k) (e6Root k)) (e6vec 4) := by
  decide +kernel

theorem wordD_spec : ∀ k : Fin 72,
    SameSign (iform (τ := Tag.E6) (e6Root k) (e6vec 3)) 1 →
      iform (τ := Tag.E6) (e6Root k) (e6vec 2) = 0 →
        iform (τ := Tag.E6) (e6Root k) (e6vec 4) = 0 →
          SameSign (act (wordD k) (e6vec 3)) (e6vec 3) ∧
            SameSign (act (wordD k) (e6vec 2)) (e6vec 2) ∧
              SameSign (act (wordD k) (e6vec 4)) (e6vec 4) ∧
                SameSign (act (wordD k) (e6Root k)) (e6vec 1) := by
  decide +kernel

theorem isRoot_e6vec (j : Fin 6) : IsRoot Tag.E6 (e6vec j) := by
  simpa [e6vec, e6Index] using isRoot_single Tag.E6 (e6Index j)

theorem rootReflection_e6vec
    (j : Fin 6) : rootReflection (e6vec j) = simple Tag.E6 (e6Index j) := by
  rw [rootReflection_eq_conj (w := 1) (j := e6Index j) (β := e6vec j) (by simp [e6vec])]
  simp

theorem exists_conj_eq_simple_d4Map
    (t : Fin 4 → WeylGroup Tag.E6)
    (hrefl : ∀ k, ∃ (w : WeylGroup Tag.E6) (i : Fin Tag.E6.rank), t k = w * simple Tag.E6 i * w⁻¹)
    (hord : ∀ k l, orderOf (t k * t l) = ggCoxeterMatrixD 4 k l) :
    ∃ u : WeylGroup Tag.E6, ∀ k, u * t k * u⁻¹ = simple Tag.E6 (d4Map k) := by
  classical
  choose w idx hw using hrefl
  let β : Fin 4 → Fin Tag.E6.rank → ℤ := fun k => w k • (Pi.single (idx k) 1)
  have hβroot : ∀ k, IsRoot Tag.E6 (β k) := fun k =>
    IsRoot.smul (isRoot_single Tag.E6 (idx k)) (w k)
  have htβ : ∀ k, t k = rootReflection (β k) := fun k => by
    rw [hw k]
    exact (rootReflection_eq_conj (β := β k) (w := w k) (j := idx k) rfl).symm
  have ht_inv : ∀ k, t k * t k = 1 := fun k => by
    rw [htβ k]
    exact rootReflection_mul_self (hβroot k)
  have hτ : ∀ i : Fin Tag.E6.rank, Tag.E6.symmetrizer i i = 1 := by
    intro i
    simp [Tag.symmetrizer]
  have hne_one : ∀ k l : Fin 4, k ≠ l → ggCoxeterMatrixD 4 k l ≠ 1 := by
    intro k l hkl
    revert hkl
    fin_cases k <;> fin_cases l <;> decide
  have ht_ne : ∀ k l, k ≠ l → t k ≠ t l := by
    intro k l hkl h
    have h1 : t k * t l = 1 := by simpa [h] using ht_inv l
    have h2 : orderOf (t k * t l) = 1 := by rw [h1]; simp
    have h3 := hord k l
    rw [h2] at h3
    exact hne_one k l hkl h3.symm
  have hβne : ∀ k l, k ≠ l → β k ≠ β l := by
    intro k l hkl h
    exact ht_ne k l hkl (by rw [htβ k, htβ l, h])
  have hβne' : ∀ k l, k ≠ l → β l ≠ -β k := by
    intro k l hkl h
    exact ht_ne l k (Ne.symm hkl)
      (by rw [htβ l, htβ k, h, rootReflection_neg (hβroot k)])
  have key2 : ∀ k l : Fin 4, k ≠ l → ggCoxeterMatrixD 4 k l = 2 →
      iform (τ := Tag.E6) (β k) (β l) = 0 := by
    intro k l hkl hc
    have h2 : (t k * t l) * (t k * t l) = 1 := by
      have h := pow_orderOf_eq_one (t k * t l)
      rw [hord k l, hc, pow_two] at h
      exact h
    have hcomm : Commute (t k) (t l) := by
      rw [Commute]
      calc t k * t l = (t k * t l)⁻¹ := (inv_eq_of_mul_eq_one_right h2).symm
        _ = (t l)⁻¹ * (t k)⁻¹ := mul_inv_rev (t k) (t l)
        _ = t l * t k := by
          rw [inv_eq_of_mul_eq_one_right (ht_inv k), inv_eq_of_mul_eq_one_right (ht_inv l)]
    have hcomm' : Commute (rootReflection (β k)) (rootReflection (β l)) := by
      simpa only [htβ k, htβ l] using hcomm
    exact iform_eq_zero_of_commute_rootReflection hτ (hβroot k) (hβroot l)
      (Ne.symm (hβne k l hkl)) (hβne' k l hkl) hcomm'
  have key3 : ∀ k l : Fin 4, k ≠ l → ggCoxeterMatrixD 4 k l = 3 →
      SameSign (iform (τ := Tag.E6) (β k) (β l)) 1 := by
    intro k l hkl hc
    have h0 : iform (τ := Tag.E6) (β k) (β l) ≠ 0 := by
      intro hz
      have hcomm : Commute (t k) (t l) := by
        rw [htβ k, htβ l]
        exact rootReflection_commute_of_iform_eq_zero (hβroot k) (hβroot l) hz
      have h2 : (t k * t l) * (t k * t l) = 1 := by
        calc (t k * t l) * (t k * t l) = t k * (t l * t k) * t l := by group
          _ = t k * (t k * t l) * t l := by rw [hcomm.eq]
          _ = (t k * t k) * (t l * t l) := by group
          _ = 1 := by rw [ht_inv k, ht_inv l, one_mul]
      have hdvd : orderOf (t k * t l) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
      rw [hord k l, hc] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hkl' : β k ≠ -β l := by
      intro hkl''
      exact hβne' k l hkl (by rw [hkl'', neg_neg])
    rcases iform_mem hτ (hβroot k) (hβroot l) (hβne k l hkl) hkl' with h | h | h
    · exact Or.inr h
    · exact absurd h h0
    · exact Or.inl h
  have hlen : e6Certificate.roots.length = 72 := by decide
  obtain ⟨k1, hk1lt, hk1⟩ := RootCertificate.exists_root_eq e6Certificate_check (hβroot 1)
  let K1 : Fin 72 := ⟨k1, hlen ▸ hk1lt⟩
  have hK1 : e6Root K1 = β 1 := hk1
  let lA : List (Fin Tag.E6.rank) := wordA K1
  let vA : Fin 4 → Fin Tag.E6.rank → ℤ := fun k => act lA (β k)
  have vA_def : ∀ k, vA k = act lA (β k) := fun _ => rfl
  have hvA1 : SameSign (vA 1) (e6vec 3) := by
    have h := wordA_spec K1
    rw [show wordA K1 = lA from rfl, hK1] at h
    simpa [vA_def] using h
  have hrootA : ∀ k, IsRoot Tag.E6 (vA k) := fun k => by
    rw [vA_def k, act_eq_smul]
    exact IsRoot.smul (hβroot k) _
  have hAform : ∀ k, SameSign (iform (τ := Tag.E6) (vA k) (e6vec 3)) (iform (τ := Tag.E6) (β k) (β 1)) := by
    intro k
    have h1 : SameSign (iform (τ := Tag.E6) (vA k) (e6vec 3)) (iform (τ := Tag.E6) (vA k) (vA 1)) :=
      iform_sameSign_right (vA k) hvA1.symm
    have h2 : iform (τ := Tag.E6) (vA k) (vA 1) = iform (τ := Tag.E6) (β k) (β 1) := by
      have h := iform_act lA (β k) (β 1)
      rw [vA_def k, vA_def 1]
      exact h
    exact h1.trans (Or.inl h2)
  have hA01 : SameSign (iform (τ := Tag.E6) (vA 0) (e6vec 3)) 1 :=
    (hAform 0).trans (key3 0 1 (by decide) (by decide))
  have hA21 : SameSign (iform (τ := Tag.E6) (vA 2) (e6vec 3)) 1 :=
    (hAform 2).trans (key3 2 1 (by decide) (by decide))
  have hA31 : SameSign (iform (τ := Tag.E6) (vA 3) (e6vec 3)) 1 :=
    (hAform 3).trans (key3 3 1 (by decide) (by decide))
  obtain ⟨k0, hk0lt, hk0⟩ := RootCertificate.exists_root_eq e6Certificate_check (hrootA 0)
  let K0 : Fin 72 := ⟨k0, hlen ▸ hk0lt⟩
  have hK0 : e6Root K0 = vA 0 := hk0
  let lB : List (Fin Tag.E6.rank) := wordB K0
  let vB : Fin 4 → Fin Tag.E6.rank → ℤ := fun k => act lB (vA k)
  have vB_def : ∀ k, vB k = act lB (vA k) := fun _ => rfl
  have hB := wordB_spec K0
  rw [hK0] at hB
  obtain ⟨hBfix3', hB0'⟩ := hB hA01
  have hBfix3 : SameSign (act lB (e6vec 3)) (e6vec 3) := by simpa [lB] using hBfix3'
  have hB0 : SameSign (vB 0) (e6vec 2) := by simpa [vB_def] using hB0'
  have hrootB : ∀ k, IsRoot Tag.E6 (vB k) := fun k => by
    rw [vB_def k, act_eq_smul]
    exact IsRoot.smul (hrootA k) _
  have hB1 : SameSign (vB 1) (e6vec 3) := (act_sameSign lB hvA1).trans hBfix3
  have form_act_fix : ∀ (l : List (Fin Tag.E6.rank)) (x : Fin Tag.E6.rank → ℤ),
      ∀ w : Fin Tag.E6.rank → ℤ, SameSign (act l w) w →
        SameSign (iform (τ := Tag.E6) (act l x) w) (iform x w) := by
    intro l x w h
    have h1 : SameSign (iform (τ := Tag.E6) (act l x) w) (iform (τ := Tag.E6) (act l x) (act l w)) :=
      iform_sameSign_right (act l x) h.symm
    exact h1.trans (Or.inl (iform_act l x w))
  have hB2e3 : SameSign (iform (τ := Tag.E6) (vB 2) (e6vec 3)) 1 :=
    (form_act_fix lB (vA 2) (e6vec 3) hBfix3).trans hA21
  have hB3e3 : SameSign (iform (τ := Tag.E6) (vB 3) (e6vec 3)) 1 :=
    (form_act_fix lB (vA 3) (e6vec 3) hBfix3).trans hA31
  have hB2e2 : SameSign (iform (τ := Tag.E6) (vB 2) (e6vec 2)) 0 := by
    have h1 : SameSign (iform (τ := Tag.E6) (vB 2) (e6vec 2)) (iform (τ := Tag.E6) (vB 2) (vB 0)) :=
      iform_sameSign_right (vB 2) hB0.symm
    have h2 : iform (τ := Tag.E6) (vB 2) (vB 0) = 0 := by
      have h := iform_act lB (vA 2) (vA 0)
      rw [vB_def 2, vB_def 0]
      rw [h]
      have h' := iform_act lA (β 2) (β 0)
      rw [vA_def 2, vA_def 0]
      rw [h']
      exact key2 2 0 (by decide) (by decide)
    exact h1.trans (Or.inl h2)
  have hB3e2 : SameSign (iform (τ := Tag.E6) (vB 3) (e6vec 2)) 0 := by
    have h1 : SameSign (iform (τ := Tag.E6) (vB 3) (e6vec 2)) (iform (τ := Tag.E6) (vB 3) (vB 0)) :=
      iform_sameSign_right (vB 3) hB0.symm
    have h2 : iform (τ := Tag.E6) (vB 3) (vB 0) = 0 := by
      have h := iform_act lB (vA 3) (vA 0)
      rw [vB_def 3, vB_def 0]
      rw [h]
      have h' := iform_act lA (β 3) (β 0)
      rw [vA_def 3, vA_def 0]
      rw [h']
      exact key2 3 0 (by decide) (by decide)
    exact h1.trans (Or.inl h2)
  obtain ⟨k2, hk2lt, hk2⟩ := RootCertificate.exists_root_eq e6Certificate_check (hrootB 2)
  let K2 : Fin 72 := ⟨k2, hlen ▸ hk2lt⟩
  have hK2 : e6Root K2 = vB 2 := hk2
  let lC : List (Fin Tag.E6.rank) := wordC K2
  let vC : Fin 4 → Fin Tag.E6.rank → ℤ := fun k => act lC (vB k)
  have vC_def : ∀ k, vC k = act lC (vB k) := fun _ => rfl
  have hC := wordC_spec K2
  rw [hK2] at hC
  obtain ⟨hCfix3', hCfix2', hC2'⟩ := hC hB2e3 (sameSign_eq_zero hB2e2)
  have hCfix3 : SameSign (act lC (e6vec 3)) (e6vec 3) := by simpa [lC] using hCfix3'
  have hCfix2 : SameSign (act lC (e6vec 2)) (e6vec 2) := by simpa [lC] using hCfix2'
  have hC2 : SameSign (vC 2) (e6vec 4) := by simpa [vC_def] using hC2'
  have hrootC : ∀ k, IsRoot Tag.E6 (vC k) := fun k => by
    rw [vC_def k, act_eq_smul]
    exact IsRoot.smul (hrootB k) _
  have hC0 : SameSign (vC 0) (e6vec 2) := (act_sameSign lC hB0).trans hCfix2
  have hC1 : SameSign (vC 1) (e6vec 3) := (act_sameSign lC hB1).trans hCfix3
  have hC3e3 : SameSign (iform (τ := Tag.E6) (vC 3) (e6vec 3)) 1 :=
    (form_act_fix lC (vB 3) (e6vec 3) hCfix3).trans hB3e3
  have hC3e2 : iform (τ := Tag.E6) (vC 3) (e6vec 2) = 0 :=
    sameSign_eq_zero ((form_act_fix lC (vB 3) (e6vec 2) hCfix2).trans hB3e2)
  have hC3e4 : iform (τ := Tag.E6) (vC 3) (e6vec 4) = 0 := by
    have h1 : SameSign (iform (τ := Tag.E6) (vC 3) (e6vec 4)) (iform (τ := Tag.E6) (vC 3) (vC 2)) :=
      iform_sameSign_right (vC 3) hC2.symm
    have h2 : iform (τ := Tag.E6) (vC 3) (vC 2) = 0 := by
      have h := iform_act lC (vB 3) (vB 2)
      rw [vC_def 3, vC_def 2]
      rw [h]
      have h' := iform_act lB (vA 3) (vA 2)
      rw [vB_def 3, vB_def 2]
      rw [h']
      have h'' := iform_act lA (β 3) (β 2)
      rw [vA_def 3, vA_def 2]
      rw [h'']
      exact key2 3 2 (by decide) (by decide)
    exact sameSign_eq_zero (h1.trans (Or.inl h2))
  obtain ⟨k3, hk3lt, hk3⟩ := RootCertificate.exists_root_eq e6Certificate_check (hrootC 3)
  let K3 : Fin 72 := ⟨k3, hlen ▸ hk3lt⟩
  have hK3 : e6Root K3 = vC 3 := hk3
  let lD : List (Fin Tag.E6.rank) := wordD K3
  let vD : Fin 4 → Fin Tag.E6.rank → ℤ := fun k => act lD (vC k)
  have vD_def : ∀ k, vD k = act lD (vC k) := fun _ => rfl
  have hD := wordD_spec K3
  rw [hK3] at hD
  obtain ⟨hDfix3', hDfix2', hDfix4', hD3'⟩ := hD hC3e3 hC3e2 hC3e4
  have hDfix3 : SameSign (act lD (e6vec 3)) (e6vec 3) := by simpa [lD] using hDfix3'
  have hDfix2 : SameSign (act lD (e6vec 2)) (e6vec 2) := by simpa [lD] using hDfix2'
  have hDfix4 : SameSign (act lD (e6vec 4)) (e6vec 4) := by simpa [lD] using hDfix4'
  have hD3 : SameSign (vD 3) (e6vec 1) := by simpa [vD_def] using hD3'
  have hD0 : SameSign (vD 0) (e6vec 2) := (act_sameSign lD hC0).trans hDfix2
  have hD1 : SameSign (vD 1) (e6vec 3) := (act_sameSign lD hC1).trans hDfix3
  have hD2 : SameSign (vD 2) (e6vec 4) := (act_sameSign lD hC2).trans hDfix4
  let u : WeylGroup Tag.E6 :=
    (coxeterSystem Tag.E6).wordProd (e6Word lD) * (coxeterSystem Tag.E6).wordProd (e6Word lC) *
      (coxeterSystem Tag.E6).wordProd (e6Word lB) * (coxeterSystem Tag.E6).wordProd (e6Word lA)
  have u_def : u = (coxeterSystem Tag.E6).wordProd (e6Word lD) *
      (coxeterSystem Tag.E6).wordProd (e6Word lC) *
        (coxeterSystem Tag.E6).wordProd (e6Word lB) *
          (coxeterSystem Tag.E6).wordProd (e6Word lA) := rfl
  refine ⟨u, fun k => ?_⟩
  have huV : u • β k = vD k := by
    have hA : (coxeterSystem Tag.E6).wordProd (e6Word lA) • β k = vA k := by
      rw [← act_eq_smul lA (β k), vA_def k]
    have hB : (coxeterSystem Tag.E6).wordProd (e6Word lB) • vA k = vB k := by
      rw [← act_eq_smul lB (vA k), vB_def k]
    have hC : (coxeterSystem Tag.E6).wordProd (e6Word lC) • vB k = vC k := by
      rw [← act_eq_smul lC (vB k), vC_def k]
    have hD : (coxeterSystem Tag.E6).wordProd (e6Word lD) • vC k = vD k := by
      rw [← act_eq_smul lD (vC k), vD_def k]
    calc u • β k
        = (coxeterSystem Tag.E6).wordProd (e6Word lD) •
            ((coxeterSystem Tag.E6).wordProd (e6Word lC) •
              ((coxeterSystem Tag.E6).wordProd (e6Word lB) •
                ((coxeterSystem Tag.E6).wordProd (e6Word lA) • β k))) := by
          rw [u_def, mul_smul, mul_smul, mul_smul]
      _ = vD k := by rw [hA, hB, hC, hD]
  have hu : SameSign (u • β k) (e6vec (d4Map k)) := by
    rw [huV]
    fin_cases k
    · simpa [d4Map] using hD0
    · simpa [d4Map] using hD1
    · simpa [d4Map] using hD2
    · simpa [d4Map] using hD3
  rw [htβ k, ← rootReflection_smul_root u (hβroot k)]
  rcases hu with h | h
  · rw [h]
    exact rootReflection_e6vec (d4Map k)
  · rw [h, rootReflection_neg (isRoot_e6vec (d4Map k))]
    exact rootReflection_e6vec (d4Map k)

end CFSG.StandardType.E6D4Refl

end
