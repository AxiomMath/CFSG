module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoAHL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def ggQ2_AH_sum (m : ℕ) : GGBCV m →ₗ[ZMod 3] ZMod 3 where
  toFun v := ∑ i, v i
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

@[expose] noncomputable def ggQ2_AH_H (m : ℕ) : Submodule (ZMod 3) (GGBCV m) :=
  LinearMap.ker (ggQ2_AH_sum m)

lemma ggQ2_AH_mem_H {m : ℕ} {v : GGBCV m} :
    v ∈ ggQ2_AH_H m ↔ ∑ i, v i = 0 :=
  LinearMap.mem_ker

@[expose] def ggQ2_AH_one (m : ℕ) : GGBCV m := fun _ => 1

private lemma ggQ2_AH_sum_single {m : ℕ} (i : Fin m) (c : ZMod 3) :
    ∑ j, (Pi.single i c : GGBCV m) j = c := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma ggQ2_AH_sum_single' {m : ℕ} (i : Fin m) (c : ZMod 3) :
    ggQ2_AH_sum m (Pi.single i c : GGBCV m) = c := by
  show (∑ j, (Pi.single i c : GGBCV m) j) = c
  exact ggQ2_AH_sum_single i c

lemma ggQ2_AH_sum_one (m : ℕ) : ggQ2_AH_sum m (ggQ2_AH_one m) = (m : ZMod 3) := by
  simp [ggQ2_AH_sum, ggQ2_AH_one]

private lemma ggQ2_AH_sum_ne_zero {m : ℕ} (hm : m ≠ 0) : ggQ2_AH_sum m ≠ 0 := by
  intro h
  have h1 := congrArg (fun f => f (Pi.single (⟨0, Nat.pos_of_ne_zero hm⟩ : Fin m) (1 : ZMod 3))) h
  simp [ggQ2_AH_sum] at h1

@[expose] noncomputable def ggQ2_AH_root (n : ℕ) (i : Fin n) : GGBCV (n + 1) :=
  (Pi.single ⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩ (1 : ZMod 3)) -
    (Pi.single ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ (1 : ZMod 3))

lemma ggQ2_AH_root_mem (n : ℕ) (i : Fin n) :
    ggQ2_AH_root n i ∈ ggQ2_AH_H (n + 1) := by
  rw [ggQ2_AH_mem_H, ggQ2_AH_root]
  have h1 : (∑ x : Fin (n + 1),
        ((Pi.single ⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩ (1 : ZMod 3) : GGBCV (n + 1)) x -
          (Pi.single ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ (1 : ZMod 3) : GGBCV (n + 1)) x)) =
      (∑ x : Fin (n + 1),
        (Pi.single ⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩ (1 : ZMod 3) : GGBCV (n + 1)) x) -
      (∑ x : Fin (n + 1),
        (Pi.single ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ (1 : ZMod 3) : GGBCV (n + 1)) x) :=
    Finset.sum_sub_distrib _ _
  simp only [Pi.sub_apply]
  rw [h1, ggQ2_AH_sum_single, ggQ2_AH_sum_single, sub_self]

private noncomputable def ggQ2_AH_prefixSum (m : ℕ) (i : Fin m) : GGBCV m →ₗ[ZMod 3] ZMod 3 :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), LinearMap.proj j

private lemma ggQ2_AH_prefixSum_single {m : ℕ} (i j : Fin m) (c : ZMod 3) :
    ggQ2_AH_prefixSum m i (Pi.single j c : GGBCV m) = if j ≤ i then c else 0 := by
  simp only [ggQ2_AH_prefixSum, LinearMap.sum_apply, LinearMap.proj_apply]
  by_cases h : j ≤ i
  · rw [if_pos h]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      have hne : j ≠ b := fun hbj => hb hbj.symm
      simp [Pi.single_apply, hne]
    · intro hj
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩) hj
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b hb
    have hb' : b ≤ i := (Finset.mem_filter.mp hb).2
    have hne : j ≠ b := by intro hbj; exact h (hbj ▸ hb')
    simp [Pi.single_apply, hne]

private lemma ggQ2_AH_fin_eq_nat {n : ℕ} {i j : Fin n} : i = j ↔ (i : ℕ) = (j : ℕ) :=
  Fin.ext_iff

private lemma ggQ2_AH_fin_cast_eq {n : ℕ} {i j : Fin n} :
    ((⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) =
      ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩) ↔ (i : ℕ) = (j : ℕ) := by
  simp [Fin.ext_iff]

private lemma ggQ2_AH_fin_cast_eq_succ {n : ℕ} {i j : Fin n} :
    ((⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) =
      ⟨(j : ℕ) + 1, Nat.succ_lt_succ j.isLt⟩) ↔ (i : ℕ) = (j : ℕ) + 1 := by
  simp [Fin.ext_iff]

private lemma ggQ2_AH_fin_succ_eq_cast {n : ℕ} {i j : Fin n} :
    ((⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) =
      ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩) ↔ (i : ℕ) + 1 = (j : ℕ) := by
  simp [Fin.ext_iff]

private lemma ggQ2_AH_fin_succ_eq_succ {n : ℕ} {i j : Fin n} :
    ((⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) =
      ⟨(j : ℕ) + 1, Nat.succ_lt_succ j.isLt⟩) ↔ (i : ℕ) = (j : ℕ) := by
  simp [Fin.ext_iff]

private lemma ggQ2_AH_fin_le {n : ℕ} {i j : Fin n} :
    ((⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) ≤
      ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩) ↔ (i : ℕ) ≤ (j : ℕ) :=
  Fin.le_iff_val_le_val

private lemma ggQ2_AH_fin_succ_le {n : ℕ} {i j : Fin n} :
    ((⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) ≤
      ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩) ↔ (i : ℕ) + 1 ≤ (j : ℕ) :=
  Fin.le_iff_val_le_val

private lemma ggQ2_AH_prefixSum_root (n : ℕ) (i j : Fin n) :
    ggQ2_AH_prefixSum (n + 1) ⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩ (ggQ2_AH_root n j) =
      if i = j then 1 else 0 := by
  rw [ggQ2_AH_root, map_sub, ggQ2_AH_prefixSum_single, ggQ2_AH_prefixSum_single]
  simp only [ggQ2_AH_fin_le, ggQ2_AH_fin_succ_le, ggQ2_AH_fin_eq_nat]
  by_cases hij : (i : ℕ) = (j : ℕ)
  · have h : ¬ ((j : ℕ) + 1 ≤ (i : ℕ)) := by omega
    rw [if_pos (le_of_eq hij.symm), if_neg h, if_pos hij]
    decide
  · rw [if_neg hij]
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
    · have h1 : ¬ ((j : ℕ) ≤ (i : ℕ)) := by omega
      have h2 : ¬ ((j : ℕ) + 1 ≤ (i : ℕ)) := by omega
      rw [if_neg h1, if_neg h2]
      decide
    · exact absurd h hij
    · have h1 : (j : ℕ) ≤ (i : ℕ) := by omega
      have h2 : (j : ℕ) + 1 ≤ (i : ℕ) := by omega
      rw [if_pos h1, if_pos h2]
      decide

private lemma ggQ2_AH_prefix_det_ne_zero (n : ℕ) :
    (Matrix.of fun i j : Fin n =>
      ggQ2_AH_prefixSum (n + 1) ⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩
        (ggQ2_AH_root n j)).det ≠ 0 := by
  have hM : (Matrix.of fun i j : Fin n =>
      ggQ2_AH_prefixSum (n + 1) ⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩
        (ggQ2_AH_root n j)) = 1 := by
    ext i j
    rw [Matrix.of_apply, Matrix.one_apply, ggQ2_AH_prefixSum_root]
  rw [hM, Matrix.det_one]
  exact one_ne_zero

private lemma ggQ2_AH_root_linearIndependent (n : ℕ) :
    LinearIndependent (ZMod 3) (ggQ2_AH_root n) := by
  apply linearIndependent_of_det_ne_zero (h := ggQ2_AH_root n)
    (α := fun i => ggQ2_AH_prefixSum (n + 1) ⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩)
  exact ggQ2_AH_prefix_det_ne_zero n

private lemma ggQ2_AH_finrank_H (n : ℕ) :
    finrank (ZMod 3) ↥(ggQ2_AH_H (n + 1)) = n := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (K := ZMod 3)
    (V₁ := GGBCV (n + 1)) (f := ggQ2_AH_sum (n + 1)) (ggQ2_AH_sum_ne_zero (Nat.succ_ne_zero n))
  have hpi : finrank (ZMod 3) (GGBCV (n + 1)) = n + 1 := by
    change finrank (ZMod 3) (Fin (n + 1) → ZMod 3) = n + 1
    rw [Module.finrank_pi, Fintype.card_fin]
  have h2 : finrank (ZMod 3) ↥(ggQ2_AH_H (n + 1)) + 1 = n + 1 := h.trans hpi
  omega

private lemma ggQ2_AH_root_linearIndependent_H (n : ℕ) :
    LinearIndependent (ZMod 3)
      (fun i => (⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩ : ↥(ggQ2_AH_H (n + 1)))) :=
  (ggQ2_AH_root_linearIndependent n).codRestrict (ggQ2_AH_H (n + 1))
    (fun i => ggQ2_AH_root_mem n i)

private lemma ggQ2_AH_card_H (n : ℕ) :
    Fintype.card (Fin n) = finrank (ZMod 3) ↥(ggQ2_AH_H (n + 1)) := by
  rw [Fintype.card_fin, ggQ2_AH_finrank_H n]

private noncomputable def ggQ2_AH_rootBasis (n : ℕ) (hn : 1 ≤ n) :
    Basis (Fin n) (ZMod 3) ↥(ggQ2_AH_H (n + 1)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact basisOfLinearIndependentOfCardEqFinrank (ggQ2_AH_root_linearIndependent_H n)
    (ggQ2_AH_card_H n)

private lemma ggQ2_AH_rootBasis_coe (n : ℕ) (hn : 1 ≤ n) :
    ⇑(ggQ2_AH_rootBasis n hn) = fun i => ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact coe_basisOfLinearIndependentOfCardEqFinrank _ _

lemma ggQ2_AH_coxeter_apply {D : GGQ2Lin 3} {n : ℕ} (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e) (i j : Fin n) :
    D.coxeter (e i) (e j) = (CoxeterMatrix.A n) i j := by
  rw [hA, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

private lemma ggQ2_AH_cartan_of_label2 {D : GGQ2Lin 3} {n : ℕ} (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e) {i j : Fin n} (hij : i ≠ j)
    (hlab : (CoxeterMatrix.A n) i j = 2) : D.cartan (e i) (e j) = 0 := by
  have hM : D.coxeter (e i) (e j) = 2 := by rw [ggQ2_AH_coxeter_apply e hA, hlab]
  have heij : e i ≠ e j := fun h => hij (e.injective h)
  rcases D.isCartan.2 (e i) (e j) heij with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
    ⟨hm, -, -, -⟩
  · exact h1
  · rw [hm] at hM; norm_num at hM
  · rw [hm] at hM; norm_num at hM
  · rw [hm] at hM; norm_num at hM

private lemma ggQ2_AH_cartan_of_label3 {D : GGQ2Lin 3} {n : ℕ} (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e) {i j : Fin n} (hij : i ≠ j)
    (hlab : (CoxeterMatrix.A n) i j = 3) : D.cartan (e i) (e j) = -1 := by
  have hM : D.coxeter (e i) (e j) = 3 := by rw [ggQ2_AH_coxeter_apply e hA, hlab]
  have heij : e i ≠ e j := fun h => hij (e.injective h)
  rcases D.isCartan.2 (e i) (e j) heij with ⟨hm, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, -, -, -⟩ |
    ⟨hm, -, -, -⟩
  · rw [hm] at hM; norm_num at hM
  · exact h1
  · rw [hm] at hM; norm_num at hM
  · rw [hm] at hM; norm_num at hM

lemma ggQ2_AH_single_dot {m : ℕ} (a b : Fin m) :
    (Pi.single a (1 : ZMod 3) : GGBCV m) ⬝ᵥ (Pi.single b (1 : ZMod 3) : GGBCV m) =
      if a = b then 1 else 0 := by
  rw [dotProduct_single]
  by_cases h : a = b
  · subst h; simp
  · simp [Pi.single_apply, h, Ne.symm h]

lemma ggQ2_AH_dot_root_root (n : ℕ) (i j : Fin n) :
    ggQ2_AH_root n i ⬝ᵥ ggQ2_AH_root n j =
      (if i = j then (2 : ZMod 3)
        else if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then -1 else 0) := by
  rw [ggQ2_AH_root, ggQ2_AH_root, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    ggQ2_AH_single_dot, ggQ2_AH_single_dot, ggQ2_AH_single_dot, ggQ2_AH_single_dot]
  simp only [ggQ2_AH_fin_cast_eq, ggQ2_AH_fin_cast_eq_succ, ggQ2_AH_fin_succ_eq_cast,
    ggQ2_AH_fin_succ_eq_succ, ggQ2_AH_fin_eq_nat]
  by_cases hij : (i : ℕ) = (j : ℕ)
  · rw [if_pos hij, if_neg (by omega : ¬ (i : ℕ) = (j : ℕ) + 1),
      if_neg (by omega : ¬ (i : ℕ) + 1 = (j : ℕ)),
      if_pos (by omega : (i : ℕ) + 1 = (j : ℕ) + 1), if_pos hij]
    decide
  · by_cases hB : (i : ℕ) + 1 = (j : ℕ)
    · rw [if_neg hij, if_neg (by omega : ¬ (i : ℕ) = (j : ℕ) + 1), if_pos hB,
        if_neg (by omega : ¬ (i : ℕ) + 1 = (j : ℕ) + 1), if_neg hij, if_pos (Or.inl hB)]
      decide
    · by_cases hC : (j : ℕ) + 1 = (i : ℕ)
      · rw [if_neg hij, if_pos hC.symm, if_neg (by omega : ¬ (i : ℕ) + 1 = (j : ℕ)),
          if_neg (by omega : ¬ (i : ℕ) + 1 = (j : ℕ) + 1), if_neg hij, if_pos (Or.inr hC)]
        decide
      · rw [if_neg hij, if_neg (by omega : ¬ (i : ℕ) = (j : ℕ) + 1), if_neg hB,
          if_neg (by omega : ¬ (i : ℕ) + 1 = (j : ℕ) + 1), if_neg hij,
          if_neg (by omega : ¬ ((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)))]
        decide

lemma ggQ2_AH_dot_root_cartan {D : GGQ2Lin 3} {n : ℕ} (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e) (i j : Fin n) :
    ggQ2_AH_root n i ⬝ᵥ ggQ2_AH_root n j = (D.cartan (e i) (e j) : ZMod 3) := by
  rw [ggQ2_AH_dot_root_root]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, D.isCartan.1 (e i)]
    norm_num
  · rw [if_neg hij]
    by_cases hlab : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)
    · rw [if_pos hlab]
      have hA2 : (CoxeterMatrix.A n) i j = 3 := by
        rw [ggQ2_A_label, if_neg hij, if_pos hlab]
      have hc := ggQ2_AH_cartan_of_label3 e hA hij hA2
      rw [hc]; decide
    · rw [if_neg hlab]
      have hA2 : (CoxeterMatrix.A n) i j = 2 := by
        rw [ggQ2_A_label, if_neg hij, if_neg hlab]
      have hc := ggQ2_AH_cartan_of_label2 e hA hij hA2
      rw [hc]; decide

lemma ggQ2_AH_dot_apply {m : ℕ} (c v : GGBCV m) :
    ggBCDot c v = c ⬝ᵥ v := by
  simp [ggBCDot, LinearMap.sum_apply, LinearMap.proj_apply, dotProduct]

theorem ggQ2_AH_coord (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn1 : 1 ≤ n)
    (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e) :
    ∃ τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)),
      (∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩) ∧
      (∀ i v, D.root (e i) v =
        ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) := by
  classical
  haveI : Nonempty D.ι := ⟨e ⟨0, by omega⟩⟩
  let b0 : Basis D.ι (ZMod 3) D.V := basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  have hb0 : ⇑b0 = D.coroot := coe_basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  let b : Basis (Fin n) (ZMod 3) D.V := b0.reindex e.symm
  have hb : ∀ i, b i = D.coroot (e i) := by
    intro i
    change (b0.reindex e.symm) i = D.coroot (e i)
    rw [Module.Basis.reindex_apply, Equiv.symm_symm]
    exact congrFun hb0 (e i)
  let bu := ggQ2_AH_rootBasis n hn1
  have hbu : ⇑bu = fun i => (⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩ :
      ↥(ggQ2_AH_H (n + 1))) := ggQ2_AH_rootBasis_coe n hn1
  let τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)) := b.equiv bu (Equiv.refl _)
  refine ⟨τ, ?_, ?_⟩
  · intro i
    rw [show D.coroot (e i) = b i from (hb i).symm]
    rw [Module.Basis.equiv_apply]
    exact congrFun hbu i
  · intro i v
    have hroot : D.root (e i) =
        ((ggBCDot (ggQ2_AH_root n i)).comp
          (Submodule.subtype (ggQ2_AH_H (n + 1)))).comp
          (τ : D.V →ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))) := by
      apply b.ext
      intro j
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      have hbτ : (Submodule.subtype (ggQ2_AH_H (n + 1)))
          ((τ : D.V →ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))) (b j)) = ggQ2_AH_root n j := by
        have hτj : (b.equiv bu (Equiv.refl (Fin n)) : D.V →ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
            (b j) = bu j := by
          change (b.equiv bu (Equiv.refl (Fin n))) (b j) = bu j
          rw [Module.Basis.equiv_apply]
          rfl
        rw [hτj, congrFun hbu j]
        rfl
      have h1 : D.root (e i) (b j) = (D.cartan (e i) (e j) : ZMod 3) := by
        rw [hb j, D.pairing]
      rw [h1, hbτ]
      change (D.cartan (e i) (e j) : ZMod 3) =
        ggBCDot (ggQ2_AH_root n i) (ggQ2_AH_root n j)
      rw [ggQ2_AH_dot_apply]
      exact (ggQ2_AH_dot_root_cartan e hA i j).symm
    rw [hroot]
    simp only [LinearMap.comp_apply]
    rw [ggQ2_AH_dot_apply]
    rfl

end CFSG.StandardType

end
