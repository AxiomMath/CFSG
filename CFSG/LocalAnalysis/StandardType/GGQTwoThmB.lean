module

public import CFSG.LocalAnalysis.StandardType.GGQTwoConnectivity
public import CFSG.LocalAnalysis.StandardType.GGQTwoInvForm
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmA
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmBA
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCThmB
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmBBC4
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmBDa1
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmBDaN
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmBD5
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmBE7
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmBE8
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmBF4
public import CFSG.LocalAnalysis.StandardType.GGQTwoParabA3
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2xTL_nbr_iff (D : GGQ2Lin 3) {i j : D.ι} (hij : i ≠ j) :
    D.cartan i j ≠ 0 ↔ D.coxeter i j ≠ 2 := by
  rcases D.isCartan.2 i j hij with ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, -, h2, -⟩ | ⟨hm, -, h2, -⟩
  · rw [h1, hm]; simp
  · rw [h1, hm]; simp
  · rw [hm]; constructor <;> intro _ <;> omega
  · rw [hm]; constructor <;> intro _ <;> omega

private theorem ggQ2xTL_leaf_unique (D : GGQ2Lin 3) {j k : D.ι} (hj : j ≠ D.a) (hk : k ≠ D.a)
    (hj' : D.cartan D.a j ≠ 0) (hk' : D.cartan D.a k ≠ 0) : j = k := by
  obtain ⟨c, -, hu⟩ := D.a_leaf
  exact (hu j ⟨hj, hj'⟩).trans (hu k ⟨hk, hk'⟩).symm

private theorem ggQ2xTL_weyl_le_reflGp (D : GGQ2Lin 3) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW : D.weyl ≤ A) : D.weyl ≤ reflGp A := by
  unfold GGQ2Lin.weyl GGQ2Lin.parab
  rw [Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact Subgroup.subset_closure ⟨hW (Subgroup.subset_closure ⟨k, Set.mem_univ k, rfl⟩),
    D.coroot k, D.root k, D.root_coroot_self k, rfl⟩

private theorem ggQ2xTL_P3_of_le (D : GGQ2Lin 3) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW : D.weyl ≤ A) (x : D.V) (h : A ≤ D.weyl) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x} :=
  fun φ hφ => ⟨φ, ggQ2xTL_weyl_le_reflGp D A hW (h hφ), rfl⟩

private theorem ggQ2xTLa_cartan_A (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e) (i j : Fin n) :
    D.cartan (e i) (e j) = CartanMatrix.A n i j := by
  by_cases hij : i = j
  · subst hij
    rw [D.isCartan.1 (e i)]
    simp [CartanMatrix.A]
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hcox : D.coxeter (e i) (e j) = (CoxeterMatrix.A n) i j := by
      rw [hA, CoxeterMatrix.reindex_apply]
      simp
    have hlabel : (CoxeterMatrix.A n) i j = 2 ∨ (CoxeterMatrix.A n) i j = 3 := by
      simp only [CoxeterMatrix.A, Matrix.of_apply]
      rw [if_neg hij]
      by_cases h : (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)
      · exact Or.inr (if_pos h)
      · exact Or.inl (if_neg h)
    rcases hlabel with h2 | h3
    · have hA0 : CartanMatrix.A n i j = 0 := by
        simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij]
        split_ifs with hh
        · exfalso
          have hcontra : (CoxeterMatrix.A n) i j = 3 := by
            simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hij]
            exact if_pos (Or.symm hh)
          omega
        · rfl
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · rw [h1, hA0]
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
    · have hadj : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) := by
        by_contra hh
        have hcontra : (CoxeterMatrix.A n) i j = 2 := by
          simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hij]
          exact if_neg (fun hD => hh (Or.symm hD))
        omega
      have hAneg : CartanMatrix.A n i j = -1 := by
        simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij]
        exact if_pos hadj
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · rw [hcox] at hm; omega
      · rw [h1, hAneg]
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega

private theorem ggQ2xTLa_leaf (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e) (hn : 2 ≤ n) :
    D.a = e ⟨0, by omega⟩ ∨ D.a = e ⟨n - 1, by omega⟩ := by
  let i : Fin n := e.symm D.a
  have hDa : D.a = e i := (Equiv.apply_symm_apply e D.a).symm
  by_cases h0 : (i : ℕ) = 0
  · left
    rw [hDa]
    exact congrArg e (Fin.ext h0)
  · by_cases hlast : (i : ℕ) = n - 1
    · right
      rw [hDa]
      exact congrArg e (Fin.ext hlast)
    · exfalso
      have hi0 : 0 < (i : ℕ) := Nat.pos_of_ne_zero h0
      have hilt : (i : ℕ) + 1 < n := by
        have := i.isLt
        omega
      let j : Fin n := ⟨(i : ℕ) - 1, by omega⟩
      let k : Fin n := ⟨(i : ℕ) + 1, by omega⟩
      have hjv : (j : ℕ) + 1 = (i : ℕ) := by simp only [j]; omega
      have hkv : (i : ℕ) + 1 = (k : ℕ) := by simp only [k]
      have hcoxj : D.coxeter (e i) (e j) = 3 := by
        rw [hA, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rw [ggQ2_A_label]
        have hne : i ≠ j := by
          intro h
          have hval := congrArg Fin.val h
          simp only [j] at hval
          omega
        rw [if_neg hne, if_pos (Or.inr hjv)]
      have hcoxk : D.coxeter (e i) (e k) = 3 := by
        rw [hA, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rw [ggQ2_A_label]
        have hne : i ≠ k := by
          intro h
          have hval := congrArg Fin.val h
          simp only [k] at hval
          omega
        rw [if_neg hne, if_pos (Or.inl hkv)]
      have hneij : e i ≠ e j := by
        intro h
        have hval := congrArg Fin.val (e.injective h)
        simp only [j] at hval
        omega
      have hneik : e i ≠ e k := by
        intro h
        have hval := congrArg Fin.val (e.injective h)
        simp only [k] at hval
        omega
      have hj' : D.cartan D.a (e j) ≠ 0 := by
        rw [hDa]
        exact (ggQ2xTL_nbr_iff D hneij).mpr (by rw [hcoxj]; decide)
      have hk' : D.cartan D.a (e k) ≠ 0 := by
        rw [hDa]
        exact (ggQ2xTL_nbr_iff D hneik).mpr (by rw [hcoxk]; decide)
      have hj : e j ≠ D.a := by
        intro h
        have hji : j = i := e.injective (h.trans hDa)
        have hval := congrArg Fin.val hji
        simp only [j] at hval
        omega
      have hk : e k ≠ D.a := by
        intro h
        have hki : k = i := e.injective (h.trans hDa)
        have hval := congrArg Fin.val hki
        simp only [k] at hval
        omega
      have heq := ggQ2xTL_leaf_unique D hj hk hj' hk'
      have hjk : j = k := e.injective heq
      have hval := congrArg Fin.val hjk
      simp only [j, k] at hval
      omega

private theorem ggQ2xTLa_det_eq (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e) :
    (D.cartan.det : ZMod 3) = ((n : ZMod 3) + 1) := by
  have hsub : D.cartan = (CartanMatrix.A n).submatrix e.symm e.symm := by
    ext i j
    simpa using (ggQ2xTLa_cartan_A D e hA (e.symm i) (e.symm j))
  have h1 : D.cartan.det = (CartanMatrix.A n).det := by
    rw [hsub, Matrix.det_submatrix_equiv_self e.symm (CartanMatrix.A n)]
  rw [h1, CartanMatrix.A_det]
  push_cast
  ring

private theorem ggQ2xTL_typeA (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (hbas : D.Basis) (hnd : (D.cartan.det : ZMod 3) ≠ 0)
    (h4 : 4 ≤ Fintype.card D.ι) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24)) :
    (∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x}) ∨ D.FCell A := by
  have hcard : Fintype.card D.ι = n := by
    rw [← Fintype.card_fin n, Fintype.card_congr e]
  have hn4 : 4 ≤ n := by omega
  have hleaf := ggQ2xTLa_leaf D e hA (by omega)
  by_cases hn : n = 4
  · subst hn
    exact absurd ⟨hcard, ggQ2_parab_card_A3 D e (Or.inl ⟨hA, hleaf⟩)⟩ hA3
  · have hn5 : 5 ≤ n := by omega
    by_cases h3 : (n + 1) % 3 = 0
    · exfalso
      have hzero : ((n + 1 : ℕ) : ZMod 3) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod 3) 3 (n + 1)).mpr (Nat.dvd_iff_mod_eq_zero.mpr h3)
      have h0 : (n : ZMod 3) + 1 = 0 := by
        simpa using hzero
      exact hnd (by rw [ggQ2xTLa_det_eq D e hA]; exact h0)
    · left
      exact ggQ2_thmB_A D hbas hn5 h3 e hA hleaf x hx A hW hTF hHL

private lemma ggQ2xTLb_B_apply (n : ℕ) (i j : Fin n) :
    (CoxeterMatrix.B n) i j =
      (if i = j then 1
        else if ((i:ℕ) = n-1 ∧ (j:ℕ) = n-2) ∨ ((j:ℕ) = n-1 ∧ (i:ℕ) = n-2) then 4
        else if ((j:ℕ)+1 = (i:ℕ)) ∨ ((i:ℕ)+1 = (j:ℕ)) then 3 else 2) := by
  rw [CoxeterMatrix.B]
  simp only [Matrix.of_apply]

private lemma ggQ2xTLb_B_succ_ne_two {n : ℕ} (hn : 3 ≤ n) (i : Fin n) (h : (i:ℕ)+1 < n) :
    (CoxeterMatrix.B n) i (⟨(i:ℕ)+1, h⟩ : Fin n) ≠ 2 := by
  rw [ggQ2xTLb_B_apply]
  have hne : i ≠ (⟨(i:ℕ)+1, h⟩ : Fin n) := by
    intro hh; have h' := congrArg Fin.val hh; change (i:ℕ) = (i:ℕ)+1 at h'; omega
  rw [if_neg hne]
  by_cases hd : ((i:ℕ) = n-1 ∧ ((⟨(i:ℕ)+1, h⟩ : Fin n):ℕ) = n-2) ∨
      (((⟨(i:ℕ)+1, h⟩ : Fin n):ℕ) = n-1 ∧ (i:ℕ) = n-2)
  · rw [if_pos hd]; decide
  · rw [if_neg hd]
    by_cases ha : (((⟨(i:ℕ)+1, h⟩ : Fin n):ℕ)+1 = (i:ℕ)) ∨
        ((i:ℕ)+1 = ((⟨(i:ℕ)+1, h⟩ : Fin n):ℕ))
    · rw [if_pos ha]; decide
    · exfalso
      apply ha; right
      simp only [Fin.val_mk]

private lemma ggQ2xTLb_B_pred_ne_two {n : ℕ} (hn : 3 ≤ n) (i : Fin n) (h : 0 < (i:ℕ)) :
    (CoxeterMatrix.B n) i (⟨(i:ℕ)-1, by omega⟩ : Fin n) ≠ 2 := by
  rw [ggQ2xTLb_B_apply]
  have hne : i ≠ (⟨(i:ℕ)-1, by omega⟩ : Fin n) := by
    intro hh; have h' := congrArg Fin.val hh; change (i:ℕ) = (i:ℕ)-1 at h'; omega
  rw [if_neg hne]
  by_cases hd : ((i:ℕ) = n-1 ∧ ((⟨(i:ℕ)-1, by omega⟩ : Fin n):ℕ) = n-2) ∨
      (((⟨(i:ℕ)-1, by omega⟩ : Fin n):ℕ) = n-1 ∧ (i:ℕ) = n-2)
  · rw [if_pos hd]; decide
  · rw [if_neg hd]
    by_cases ha : (((⟨(i:ℕ)-1, by omega⟩ : Fin n):ℕ)+1 = (i:ℕ)) ∨
        ((i:ℕ)+1 = ((⟨(i:ℕ)-1, by omega⟩ : Fin n):ℕ))
    · rw [if_pos ha]; decide
    · exfalso
      apply ha; left
      simp only [Fin.val_mk]
      omega

private theorem ggQ2xTLb_leaf {n : ℕ} [NeZero n] (hn : 4 ≤ n) (D : GGQ2Lin 3)
    (e : Fin n ≃ D.ι) (hB : D.coxeter = (CoxeterMatrix.B n).reindex e) :
    D.a = e 0 ∨ D.a = e ⟨n - 1, by omega⟩ := by
  have hn3 : 3 ≤ n := by omega
  let k : Fin n := e.symm D.a
  have hk : e k = D.a := e.apply_symm_apply D.a
  have hcoe : ∀ j : Fin n, D.coxeter (e k) (e j) = (CoxeterMatrix.B n) k j := by
    intro j
    rw [hB, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  by_cases hk0 : (k:ℕ) = 0
  · left
    rw [← hk]; congr 1; exact Fin.ext hk0
  · right
    have hkpos : 0 < (k:ℕ) := by omega
    have hklast : (k:ℕ) = n - 1 := by
      by_contra hne
      have hklt' : (k:ℕ) < n - 1 := by have := k.isLt; omega
      let j1 : Fin n := ⟨(k:ℕ)-1, by omega⟩
      let j2 : Fin n := ⟨(k:ℕ)+1, by omega⟩
      have hj1k : j1 ≠ k := by
        intro hh; have h := congrArg Fin.val hh; change (k:ℕ)-1 = (k:ℕ) at h; omega
      have hj2k : j2 ≠ k := by
        intro hh; have h := congrArg Fin.val hh; change (k:ℕ)+1 = (k:ℕ) at h; omega
      have hcart1 : D.cartan (e k) (e j1) ≠ 0 := by
        rw [ggQ2xTL_nbr_iff D (fun hh => (Ne.symm hj1k) (e.injective hh))]
        rw [hcoe j1]
        exact ggQ2xTLb_B_pred_ne_two hn3 k hkpos
      have hcart2 : D.cartan (e k) (e j2) ≠ 0 := by
        rw [ggQ2xTL_nbr_iff D (fun hh => (Ne.symm hj2k) (e.injective hh))]
        rw [hcoe j2]
        exact ggQ2xTLb_B_succ_ne_two hn3 k (by omega)
      have hcart1' : D.cartan D.a (e j1) ≠ 0 := by rwa [hk] at hcart1
      have hcart2' : D.cartan D.a (e j2) ≠ 0 := by rwa [hk] at hcart2
      have hne1 : e j1 ≠ D.a := by
        intro hh; exact hj1k (e.injective (hh.trans hk.symm))
      have hne2 : e j2 ≠ D.a := by
        intro hh; exact hj2k (e.injective (hh.trans hk.symm))
      have hjj : j1 = j2 := e.injective (ggQ2xTL_leaf_unique D hne1 hne2 hcart1' hcart2')
      have hval : (j1:ℕ) = (j2:ℕ) := congrArg Fin.val hjj
      change (k:ℕ)-1 = (k:ℕ)+1 at hval
      omega
    rw [← hk]; congr 1; exact Fin.ext hklast

private theorem ggQ2xTL_typeB (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hB : D.coxeter = (CoxeterMatrix.B n).reindex e)
    (hbas : D.Basis) (hnd : (D.cartan.det : ZMod 3) ≠ 0)
    (h4 : 4 ≤ Fintype.card D.ι) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24)) :
    (∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x}) ∨ D.FCell A := by
  have _ := hnd
  have hn4 : 4 ≤ n := by
    rw [← Fintype.card_fin n, Fintype.card_congr e]
    exact h4
  by_cases hn5 : 5 ≤ n
  · have h : A ≤ D.weyl :=
      ggQ2_thmB_BC (p := 3) rfl D hbas hn5 e hB x hx A hW hTF hHL
    exact Or.inl (ggQ2xTL_P3_of_le D A hW x h)
  · have hn : n = 4 := by omega
    subst hn
    have hleaf : D.a = e 0 ∨ D.a = e 3 := by
      have h := ggQ2xTLb_leaf (n := 4) (by omega) D e hB
      simpa using h
    rcases hleaf with ha | ha
    · rcases ggQ2_thmB_BC4 D hbas e hB A hW hTF with h | h
      · exact Or.inl (ggQ2xTL_P3_of_le D A hW x h)
      · exact Or.inr h
    · exact absurd ⟨by rw [← Fintype.card_congr e, Fintype.card_fin],
        ggQ2_parab_card_A3 D e (Or.inr (Or.inr ⟨hB, ha⟩))⟩ hA3

private theorem ggQ2xTLd_cartanD_ne_zero (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    CartanMatrix.D n i j ≠ 0 ↔
      (i.val + 1 = j.val ∧ j.val + 2 < n) ∨ (j.val + 1 = i.val ∧ i.val + 2 < n) ∨
      (i.val + 3 = n ∧ (j.val + 2 = n ∨ j.val + 1 = n)) ∨
      (j.val + 3 = n ∧ (i.val + 2 = n ∨ i.val + 1 = n)) := by
  simp only [CartanMatrix.D, Matrix.of_apply, if_neg hij]
  by_cases hn2 : n ≤ 2
  · have hi := i.isLt
    have hj := j.isLt
    simp only [if_pos hn2]
    constructor
    · intro h; exact absurd rfl h
    · rintro (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩) <;> omega
  · simp only [if_neg hn2]
    split_ifs with h1 h2 h3 h4
    · exact ⟨fun _ => Or.inl h1, fun _ => by norm_num⟩
    · exact ⟨fun _ => Or.inr (Or.inl h2), fun _ => by norm_num⟩
    · exact ⟨fun _ => Or.inr (Or.inr (Or.inl h3)), fun _ => by norm_num⟩
    · exact ⟨fun _ => Or.inr (Or.inr (Or.inr h4)), fun _ => by norm_num⟩
    · constructor
      · intro h; exact absurd rfl h
      · rintro (h | h | h | h) <;> omega

private theorem ggQ2xTLd_ne_of_val {n : ℕ} {i j : Fin n} (h : i.val ≠ j.val) : i ≠ j :=
  fun hh => h (congrArg Fin.val hh)

private theorem ggQ2xTLd_D_edge (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD n).reindex e) {i j : Fin n} (hij : i ≠ j)
    (h : CartanMatrix.D n i j ≠ 0) : D.cartan (e i) (e j) ≠ 0 := by
  rw [ggQ2xTL_nbr_iff D (by intro hh; exact hij (e.injective hh)), hD,
    CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    ggCoxeterMatrixD_apply, if_neg hij, if_neg h]
  norm_num

private theorem ggQ2xTLd_D_leaf (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD n).reindex e) (hn : 4 ≤ n) :
    D.a = e ⟨0, by omega⟩ ∨ D.a = e ⟨n - 2, by omega⟩ ∨
      D.a = e ⟨n - 1, by omega⟩ := by
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨h0, h2, h1⟩ := hcon
  set i : Fin n := e.symm D.a with hi
  have hDa : D.a = e i := by rw [hi, Equiv.apply_symm_apply]
  have hi0 : i ≠ ⟨0, by omega⟩ := by intro hh; exact h0 (by rw [hDa, hh])
  have hi2 : i ≠ ⟨n - 2, by omega⟩ := by intro hh; exact h2 (by rw [hDa, hh])
  have hi1 : i ≠ ⟨n - 1, by omega⟩ := by intro hh; exact h1 (by rw [hDa, hh])
  have hiv0 : i.val ≠ 0 := fun hh => hi0 (Fin.ext (by simpa using hh))
  have hiv2 : i.val ≠ n - 2 := fun hh => hi2 (Fin.ext (by simpa using hh))
  have hiv1 : i.val ≠ n - 1 := fun hh => hi1 (Fin.ext (by simpa using hh))
  have hlt : i.val < n := i.isLt
  by_cases hc : i.val = n - 3
  ·
    have hj : D.cartan (e i) (e ⟨n - 2, by omega⟩) ≠ 0 :=
      ggQ2xTLd_D_edge D e hD (ggQ2xTLd_ne_of_val hiv2)
        ((ggQ2xTLd_cartanD_ne_zero n i ⟨n - 2, by omega⟩ (ggQ2xTLd_ne_of_val hiv2)).mpr
          (Or.inr (Or.inr (Or.inl ⟨by omega, Or.inl (by simp only [Fin.val_mk]; omega)⟩))))
    have hk : D.cartan (e i) (e ⟨n - 1, by omega⟩) ≠ 0 :=
      ggQ2xTLd_D_edge D e hD (ggQ2xTLd_ne_of_val hiv1)
        ((ggQ2xTLd_cartanD_ne_zero n i ⟨n - 1, by omega⟩ (ggQ2xTLd_ne_of_val hiv1)).mpr
          (Or.inr (Or.inr (Or.inl ⟨by omega, Or.inr (by simp only [Fin.val_mk]; omega)⟩))))
    have hji : e ⟨n - 2, by omega⟩ ≠ D.a := by
      rw [hDa]; intro hh
      have hv : n - 2 = i.val := by simpa using congrArg Fin.val (e.injective hh)
      omega
    have hki : e ⟨n - 1, by omega⟩ ≠ D.a := by
      rw [hDa]; intro hh
      have hv : n - 1 = i.val := by simpa using congrArg Fin.val (e.injective hh)
      omega
    have hEq : e ⟨n - 2, by omega⟩ = e ⟨n - 1, by omega⟩ :=
      ggQ2xTL_leaf_unique D hji hki (by rw [hDa]; exact hj) (by rw [hDa]; exact hk)
    have hv : n - 2 = n - 1 := by simpa using congrArg Fin.val (e.injective hEq)
    omega
  ·
    have hlo : 1 ≤ i.val := by omega
    have hhi : i.val + 4 ≤ n := by omega
    let j1 : Fin n := ⟨i.val - 1, by omega⟩
    let j2 : Fin n := ⟨i.val + 1, by omega⟩
    have hj1 : i ≠ j1 := ggQ2xTLd_ne_of_val (by simp only [j1]; omega)
    have hj2 : i ≠ j2 := ggQ2xTLd_ne_of_val (by simp only [j2]; omega)
    have e1 : D.cartan (e i) (e j1) ≠ 0 :=
      ggQ2xTLd_D_edge D e hD hj1 ((ggQ2xTLd_cartanD_ne_zero n i j1 hj1).mpr
        (Or.inr (Or.inl ⟨by simp only [j1]; omega, by omega⟩)))
    have e2 : D.cartan (e i) (e j2) ≠ 0 :=
      ggQ2xTLd_D_edge D e hD hj2 ((ggQ2xTLd_cartanD_ne_zero n i j2 hj2).mpr
        (Or.inl ⟨by simp only [j2], by simp only [j2]; omega⟩))
    have h1i : e j1 ≠ D.a := by
      rw [hDa]; intro hh; exact (Ne.symm hj1) (e.injective hh)
    have h2i : e j2 ≠ D.a := by
      rw [hDa]; intro hh; exact (Ne.symm hj2) (e.injective hh)
    have h12 : j1 = j2 :=
      e.injective (ggQ2xTL_leaf_unique D h1i h2i (by rw [hDa]; exact e1)
        (by rw [hDa]; exact e2))
    have hv : i.val - 1 = i.val + 1 := by
      simpa only [j1, j2] using congrArg Fin.val h12
    omega

private theorem ggQ2xTL_typeD (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD n).reindex e)
    (hbas : D.Basis) (hnd : (D.cartan.det : ZMod 3) ≠ 0)
    (h4 : 4 ≤ Fintype.card D.ι) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24)) :
    (∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x}) ∨ D.FCell A := by
  have hcard : Fintype.card D.ι = n :=
    (Fintype.card_congr e).symm.trans (Fintype.card_fin n)
  have hn : 4 ≤ n := by omega
  have hleaf := ggQ2xTLd_D_leaf D e hD hn
  have _ := hnd
  rcases lt_or_ge n 5 with h5 | h5
  · have hn4 : n = 4 := by omega
    subst hn4
    have ha : D.a = e 0 ∨ D.a = e 2 ∨ D.a = e 3 := hleaf
    exact absurd ⟨hcard, ggQ2_parab_card_A3 D e (Or.inr (Or.inl ⟨hD, ha⟩))⟩ hA3
  · rcases lt_or_ge n 6 with h6 | h6
    · have hn5 : n = 5 := by omega
      subst hn5
      rcases hleaf with ha | ha | ha
      · exact Or.inl (ggQ2_thmB_D5 D hbas e hD ha x hx A hW hTF)
      · exact Or.inl (ggQ2_thmB_D_aN D hbas (by omega) e hD (Or.inl ha) x hx A hW hTF hHL)
      · exact Or.inl (ggQ2_thmB_D_aN D hbas (by omega) e hD (Or.inr ha) x hx A hW hTF hHL)
    · rcases hleaf with ha | ha | ha
      · exact Or.inl (ggQ2_thmB_D_a1 D hbas h6 e hD ha x hx A hW hTF hHL)
      · exact Or.inl (ggQ2_thmB_D_aN D hbas (by omega) e hD (Or.inl ha) x hx A hW hTF hHL)
      · exact Or.inl (ggQ2_thmB_D_aN D hbas (by omega) e hD (Or.inr ha) x hx A hW hTF hHL)

private theorem ggQ2xTLe_cartan_of_labels (D : GGQ2Lin 3) {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Γ ≃ D.ι) {M : CoxeterMatrix Γ} (hM : D.coxeter = M.reindex e)
    (hM23 : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3) (C : Matrix Γ Γ ℤ)
    (hC0 : ∀ i j, i ≠ j → M i j = 2 → C i j = 0)
    (hC3 : ∀ i j, i ≠ j → M i j = 3 → C i j = -1) (hCii : ∀ i, C i i = 2) (i j : Γ) :
    D.cartan (e i) (e j) = C i j := by
  by_cases hij : i = j
  · subst hij
    rw [D.isCartan.1, hCii]
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hcox : D.coxeter (e i) (e j) = M i j := by
      rw [hM, CoxeterMatrix.reindex_apply]
      simp
    rcases hM23 i j hij with h2 | h3
    · rw [hC0 i j hij h2]
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · exact h1
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
    · rw [hC3 i j hij h3]
      rcases D.isCartan.2 (e i) (e j) hne with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · rw [hcox] at hm; omega
      · exact h1
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega

private theorem ggQ2xTLe_cartan_E6 (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (i j : Fin 6) :
    D.cartan (e i) (e j) = CartanMatrix.E 6 i j :=
  ggQ2xTLe_cartan_of_labels D e hE
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆])
    (CartanMatrix.E 6)
    (by
      intro i j hij h
      fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆, CartanMatrix.E])
    (by
      intro i j hij h
      fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆, CartanMatrix.E])
    (by intro i; fin_cases i <;> decide) i j

private theorem ggQ2xTL_E6 (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e)
    (hbas : D.Basis) (hnd : (D.cartan.det : ZMod 3) ≠ 0)
    (h4 : 4 ≤ Fintype.card D.ι) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24)) :
    (∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x}) ∨ D.FCell A := by
  have _ := hbas
  have _ := h4
  have _ := x
  have _ := hx
  have _ := A
  have _ := hW
  have _ := hTF
  have _ := hHL
  have _ := hA3
  exfalso
  have h1 : (D.cartan.det : ZMod 3)
      = ((CartanMatrix.E 6).map fun x : ℤ => (x : ZMod 3)).det := by
    rw [Int.cast_det]
    have heq : (D.cartan.map fun x : ℤ => (x : ZMod 3)).submatrix e e
        = (CartanMatrix.E 6).map fun x : ℤ => (x : ZMod 3) := by
      ext i j
      rw [Matrix.submatrix_apply, Matrix.map_apply, Matrix.map_apply,
        ggQ2xTLe_cartan_E6 D e hE i j]
    rw [← Matrix.det_submatrix_equiv_self e (D.cartan.map fun x : ℤ => (x : ZMod 3)), heq]
  have h2 : ((CartanMatrix.E 6).map fun x : ℤ => (x : ZMod 3)).det = 0 := by
    rw [← Int.cast_det, CartanMatrix.E₆_det]
    decide
  exact hnd (h1.trans h2)

private theorem ggQ2xTLe_cox_nbr (D : GGQ2Lin 3) {i j : D.ι} (hij : i ≠ j)
    (h : D.coxeter i j ≠ 2) : D.cartan i j ≠ 0 :=
  (ggQ2xTL_nbr_iff D hij).2 h

private theorem ggQ2xTLe_ne_leaf {Γ : Type} {D : GGQ2Lin 3} {e : Γ ≃ D.ι} {i j : Γ}
    (hi : e i = D.a) (hij : j ≠ i) : e j ≠ D.a := by
  rw [← hi]
  exact e.injective.ne hij

private theorem ggQ2xTLe_E7_cox (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) {i j : Fin 7}
    (h : CoxeterMatrix.E₇ i j ≠ 2) : D.coxeter (e i) (e j) ≠ 2 := by
  rw [hE, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact h

private theorem ggQ2xTLe_E7_cartan (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) {i j : Fin 7} (hij : i ≠ j)
    (h : CoxeterMatrix.E₇ i j ≠ 2) : D.cartan (e i) (e j) ≠ 0 :=
  ggQ2xTLe_cox_nbr D (e.injective.ne hij) (ggQ2xTLe_E7_cox D e hE h)

private theorem ggQ2xTLe_E7_leaf (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) :
    D.a = e 0 ∨ D.a = e 1 ∨ D.a = e 6 := by
  have hmem : ∀ i : Fin 7, e i = D.a → i = 0 ∨ i = 1 ∨ i = 6 := by
    intro i hi'
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have h0 : D.cartan D.a (e (0 : Fin 7)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E7_cartan D e hE (i := (2 : Fin 7)) (j := (0 : Fin 7))
          (by decide) (by decide)
      have h3 : D.cartan D.a (e (3 : Fin 7)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E7_cartan D e hE (i := (2 : Fin 7)) (j := (3 : Fin 7))
          (by decide) (by decide)
      exact (by decide : (0 : Fin 7) ≠ 3)
        (e.injective (ggQ2xTL_leaf_unique D
          (ggQ2xTLe_ne_leaf hi' (by decide : (0 : Fin 7) ≠ 2))
          (ggQ2xTLe_ne_leaf hi' (by decide : (3 : Fin 7) ≠ 2))
          h0 h3))
    · exfalso
      have h2 : D.cartan D.a (e (2 : Fin 7)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E7_cartan D e hE (i := (3 : Fin 7)) (j := (2 : Fin 7))
          (by decide) (by decide)
      have h4 : D.cartan D.a (e (4 : Fin 7)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E7_cartan D e hE (i := (3 : Fin 7)) (j := (4 : Fin 7))
          (by decide) (by decide)
      exact (by decide : (2 : Fin 7) ≠ 4)
        (e.injective (ggQ2xTL_leaf_unique D
          (ggQ2xTLe_ne_leaf hi' (by decide : (2 : Fin 7) ≠ 3))
          (ggQ2xTLe_ne_leaf hi' (by decide : (4 : Fin 7) ≠ 3))
          h2 h4))
    · exfalso
      have h3 : D.cartan D.a (e (3 : Fin 7)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E7_cartan D e hE (i := (4 : Fin 7)) (j := (3 : Fin 7))
          (by decide) (by decide)
      have h5 : D.cartan D.a (e (5 : Fin 7)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E7_cartan D e hE (i := (4 : Fin 7)) (j := (5 : Fin 7))
          (by decide) (by decide)
      exact (by decide : (3 : Fin 7) ≠ 5)
        (e.injective (ggQ2xTL_leaf_unique D
          (ggQ2xTLe_ne_leaf hi' (by decide : (3 : Fin 7) ≠ 4))
          (ggQ2xTLe_ne_leaf hi' (by decide : (5 : Fin 7) ≠ 4))
          h3 h5))
    · exfalso
      have h4 : D.cartan D.a (e (4 : Fin 7)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E7_cartan D e hE (i := (5 : Fin 7)) (j := (4 : Fin 7))
          (by decide) (by decide)
      have h6 : D.cartan D.a (e (6 : Fin 7)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E7_cartan D e hE (i := (5 : Fin 7)) (j := (6 : Fin 7))
          (by decide) (by decide)
      exact (by decide : (4 : Fin 7) ≠ 6)
        (e.injective (ggQ2xTL_leaf_unique D
          (ggQ2xTLe_ne_leaf hi' (by decide : (4 : Fin 7) ≠ 5))
          (ggQ2xTLe_ne_leaf hi' (by decide : (6 : Fin 7) ≠ 5))
          h4 h6))
    · exact Or.inr (Or.inr rfl)
  rcases hmem (e.symm D.a) (e.apply_symm_apply D.a) with h | h | h
  · left; rw [← e.apply_symm_apply D.a, h]
  · right; left; rw [← e.apply_symm_apply D.a, h]
  · right; right; rw [← e.apply_symm_apply D.a, h]

private theorem ggQ2xTL_E7 (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e)
    (hbas : D.Basis) (hnd : (D.cartan.det : ZMod 3) ≠ 0)
    (h4 : 4 ≤ Fintype.card D.ι) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24)) :
    (∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x}) ∨ D.FCell A := by
  have _ := hnd
  have _ := h4
  have _ := hA3
  exact Or.inl (ggQ2_thmB_E7 D hbas e hE (ggQ2xTLe_E7_leaf D e hE) x hx A hW hTF hHL)

private theorem ggQ2xTLe_E8_cox (D : GGQ2Lin 3) (e : Fin 8 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₈.reindex e) {i j : Fin 8}
    (h : CoxeterMatrix.E₈ i j ≠ 2) : D.coxeter (e i) (e j) ≠ 2 := by
  rw [hE, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact h

private theorem ggQ2xTLe_E8_cartan (D : GGQ2Lin 3) (e : Fin 8 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₈.reindex e) {i j : Fin 8} (hij : i ≠ j)
    (h : CoxeterMatrix.E₈ i j ≠ 2) : D.cartan (e i) (e j) ≠ 0 :=
  ggQ2xTLe_cox_nbr D (e.injective.ne hij) (ggQ2xTLe_E8_cox D e hE h)

private theorem ggQ2xTLe_E8_leaf (D : GGQ2Lin 3) (e : Fin 8 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₈.reindex e) :
    D.a = e 0 ∨ D.a = e 1 ∨ D.a = e 7 := by
  have hmem : ∀ i : Fin 8, e i = D.a → i = 0 ∨ i = 1 ∨ i = 7 := by
    intro i hi'
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have h0 : D.cartan D.a (e (0 : Fin 8)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E8_cartan D e hE (i := (2 : Fin 8)) (j := (0 : Fin 8))
          (by decide) (by decide)
      have h3 : D.cartan D.a (e (3 : Fin 8)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E8_cartan D e hE (i := (2 : Fin 8)) (j := (3 : Fin 8))
          (by decide) (by decide)
      exact (by decide : (0 : Fin 8) ≠ 3)
        (e.injective (ggQ2xTL_leaf_unique D
          (ggQ2xTLe_ne_leaf hi' (by decide : (0 : Fin 8) ≠ 2))
          (ggQ2xTLe_ne_leaf hi' (by decide : (3 : Fin 8) ≠ 2))
          h0 h3))
    · exfalso
      have h2 : D.cartan D.a (e (2 : Fin 8)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E8_cartan D e hE (i := (3 : Fin 8)) (j := (2 : Fin 8))
          (by decide) (by decide)
      have h4 : D.cartan D.a (e (4 : Fin 8)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E8_cartan D e hE (i := (3 : Fin 8)) (j := (4 : Fin 8))
          (by decide) (by decide)
      exact (by decide : (2 : Fin 8) ≠ 4)
        (e.injective (ggQ2xTL_leaf_unique D
          (ggQ2xTLe_ne_leaf hi' (by decide : (2 : Fin 8) ≠ 3))
          (ggQ2xTLe_ne_leaf hi' (by decide : (4 : Fin 8) ≠ 3))
          h2 h4))
    · exfalso
      have h3 : D.cartan D.a (e (3 : Fin 8)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E8_cartan D e hE (i := (4 : Fin 8)) (j := (3 : Fin 8))
          (by decide) (by decide)
      have h5 : D.cartan D.a (e (5 : Fin 8)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E8_cartan D e hE (i := (4 : Fin 8)) (j := (5 : Fin 8))
          (by decide) (by decide)
      exact (by decide : (3 : Fin 8) ≠ 5)
        (e.injective (ggQ2xTL_leaf_unique D
          (ggQ2xTLe_ne_leaf hi' (by decide : (3 : Fin 8) ≠ 4))
          (ggQ2xTLe_ne_leaf hi' (by decide : (5 : Fin 8) ≠ 4))
          h3 h5))
    · exfalso
      have h4 : D.cartan D.a (e (4 : Fin 8)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E8_cartan D e hE (i := (5 : Fin 8)) (j := (4 : Fin 8))
          (by decide) (by decide)
      have h6 : D.cartan D.a (e (6 : Fin 8)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E8_cartan D e hE (i := (5 : Fin 8)) (j := (6 : Fin 8))
          (by decide) (by decide)
      exact (by decide : (4 : Fin 8) ≠ 6)
        (e.injective (ggQ2xTL_leaf_unique D
          (ggQ2xTLe_ne_leaf hi' (by decide : (4 : Fin 8) ≠ 5))
          (ggQ2xTLe_ne_leaf hi' (by decide : (6 : Fin 8) ≠ 5))
          h4 h6))
    · exfalso
      have h5 : D.cartan D.a (e (5 : Fin 8)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E8_cartan D e hE (i := (6 : Fin 8)) (j := (5 : Fin 8))
          (by decide) (by decide)
      have h7 : D.cartan D.a (e (7 : Fin 8)) ≠ 0 := by
        rw [← hi']
        exact ggQ2xTLe_E8_cartan D e hE (i := (6 : Fin 8)) (j := (7 : Fin 8))
          (by decide) (by decide)
      exact (by decide : (5 : Fin 8) ≠ 7)
        (e.injective (ggQ2xTL_leaf_unique D
          (ggQ2xTLe_ne_leaf hi' (by decide : (5 : Fin 8) ≠ 6))
          (ggQ2xTLe_ne_leaf hi' (by decide : (7 : Fin 8) ≠ 6))
          h5 h7))
    · exact Or.inr (Or.inr rfl)
  rcases hmem (e.symm D.a) (e.apply_symm_apply D.a) with h | h | h
  · left; rw [← e.apply_symm_apply D.a, h]
  · right; left; rw [← e.apply_symm_apply D.a, h]
  · right; right; rw [← e.apply_symm_apply D.a, h]

private theorem ggQ2xTL_E8 (D : GGQ2Lin 3) (e : Fin 8 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₈.reindex e)
    (hbas : D.Basis) (hnd : (D.cartan.det : ZMod 3) ≠ 0)
    (h4 : 4 ≤ Fintype.card D.ι) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24)) :
    (∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x}) ∨ D.FCell A := by
  have _ := hnd
  have _ := h4
  have _ := hA3
  exact Or.inl (ggQ2_thmB_E8 D hbas e hE (ggQ2xTLe_E8_leaf D e hE) x hx A hW hTF hHL)

private theorem ggQ2xTL_F4 (D : GGQ2Lin 3) (e : Fin 4 ≃ D.ι)
    (hF : D.coxeter = CoxeterMatrix.F₄.reindex e)
    (hbas : D.Basis) (hnd : (D.cartan.det : ZMod 3) ≠ 0)
    (h4 : 4 ≤ Fintype.card D.ι) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24)) :
    (∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x}) ∨ D.FCell A := by
  have _ := hnd
  have _ := h4
  have _ := x
  have _ := hx
  have _ := hHL
  have _ := hA3
  exact Or.inr (ggQ2_thmB_F4 D hbas e hF A hW hTF)

private theorem ggQ2xTL_G2 (D : GGQ2Lin 3) (e : Fin 2 ≃ D.ι)
    (hG : D.coxeter = CoxeterMatrix.G₂.reindex e)
    (hbas : D.Basis) (hnd : (D.cartan.det : ZMod 3) ≠ 0)
    (h4 : 4 ≤ Fintype.card D.ι) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24)) :
    (∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x}) ∨ D.FCell A := by
  have _ := hG
  have _ := hbas
  have _ := hnd
  have _ := x
  have _ := hx
  have _ := A
  have _ := hW
  have _ := hTF
  have _ := hHL
  have _ := hA3
  exfalso
  have hc := Fintype.card_congr e
  rw [Fintype.card_fin] at hc
  omega

theorem ggQ2_thmB_lin {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (hbas : D.Basis)
    (hnd : (D.cartan.det : ZMod p) ≠ 0) (h4 : 4 ≤ Fintype.card D.ι)
    (x : D.V) (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod p] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod p) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod p] D.V)))
    (hA3 : ¬ (Fintype.card D.ι = 4 ∧ Nat.card (D.parab {k | k ≠ D.a}) = 24)) :
    (∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod p) {φ x} = Submodule.span (ZMod p) {r x}) ∨ D.FCell A := by
  subst hp
  rcases D.isWeyl with ⟨n, e, hn1, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ |
    ⟨e, hF⟩ | ⟨e, hG⟩
  · exact ggQ2xTL_typeA D e hA hbas hnd h4 x hx A hW hTF hHL hA3
  · exact ggQ2xTL_typeB D e hB hbas hnd h4 x hx A hW hTF hHL hA3
  · exact ggQ2xTL_typeD D e hD hbas hnd h4 x hx A hW hTF hHL hA3
  · exact ggQ2xTL_E6 D e hE hbas hnd h4 x hx A hW hTF hHL hA3
  · exact ggQ2xTL_E7 D e hE hbas hnd h4 x hx A hW hTF hHL hA3
  · exact ggQ2xTL_E8 D e hE hbas hnd h4 x hx A hW hTF hHL hA3
  · exact ggQ2xTL_F4 D e hF hbas hnd h4 x hx A hW hTF hHL hA3
  · exact ggQ2xTL_G2 D e hG hbas hnd h4 x hx A hW hTF hHL hA3

end CFSG.StandardType

end
