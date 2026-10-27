module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDWeyl
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

public section

namespace CFSG.StandardType

open Module

private lemma ggQ2sw_dsimple_eq (m : ℕ) (hm : 4 ≤ m) (i : Fin m) :
    ggDSimple 3 m i = fun j => (TauCeti.DynkinType.typeDSimpleRoot m hm i j : ZMod 3) := by
  funext j
  by_cases hi : (i : ℕ) + 1 < m
  · rw [ggDSimple, if_pos hi, TauCeti.DynkinType.typeDSimpleRoot_of_add_one_lt hm hi]
    simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> simp_all <;> omega
  · rw [ggDSimple, if_neg hi, TauCeti.DynkinType.typeDSimpleRoot_of_not_add_one_lt hm hi]
    simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> simp_all <;> omega

private noncomputable def ggQ2sw_kappa (m : ℕ) :
    (Fin m → ZMod 3) →ₗ[ZMod 3] (Fin m → ZMod 3) where
  toFun v := ∑ i, v i • ggDSimple 3 m i
  map_add' v w := by
    ext k
    simp only [Pi.add_apply, Finset.sum_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext k
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl (fun i _ => by ring)

private lemma ggQ2sw_kappa_apply (m : ℕ) (v : Fin m → ZMod 3) (k : Fin m) :
    ggQ2sw_kappa m v k = ∑ i, v i * ggDSimple 3 m i k := by
  change (∑ i, v i • ggDSimple 3 m i) k = _
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [Pi.smul_apply, smul_eq_mul])

private lemma ggQ2sw_kappa_single (m : ℕ) (i : Fin m) :
    ggQ2sw_kappa m (Pi.single i 1) = ggDSimple 3 m i := by
  funext k
  rw [ggQ2sw_kappa_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma ggQ2sw_kappa_injective (m : ℕ) (hm : 4 ≤ m) :
    Function.Injective (ggQ2sw_kappa m) := by
  have h2 : IsRightRegular (2 : ZMod 3) := by
    intro b c hbc
    change b * 2 = c * 2 at hbc
    have hz : (b - c) * 2 = 0 := by rw [sub_mul, hbc, sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (by decide)
  have hLI := TauCeti.DynkinType.linearIndependent_typeDSimpleRoot_cast (R := ZMod 3) h2 hm
  have hker := Fintype.linearIndependent_iff.mp hLI
  intro v w hvw
  have h0 : ggQ2sw_kappa m (v - w) = 0 := by
    rw [map_sub, hvw]
    exact sub_self _
  have h0' : (∑ k, (v - w) k • ggDSimple 3 m k : Fin m → ZMod 3) = 0 := h0
  have hsum : ∑ k, (v - w) k •
      (fun j => (TauCeti.DynkinType.typeDSimpleRoot m hm k j : ZMod 3)) = 0 := by
    simpa only [ggQ2sw_dsimple_eq m hm] using h0'
  funext i
  exact sub_eq_zero.mp (hker (fun k => (v - w) k) hsum i)

private noncomputable def ggQ2sw_kappaEquiv (m : ℕ) (hm : 4 ≤ m) :
    (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3) :=
  LinearEquiv.ofBijective (ggQ2sw_kappa m)
    ⟨ggQ2sw_kappa_injective m hm,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (ggQ2sw_kappa_injective m hm)⟩

private def ggQ2sw_R (m : ℕ) (j : Fin m) (v : Fin m → ZMod 3) : Fin m → ZMod 3 :=
  v - (∑ l, ((CartanMatrix.D m j l : ℤ) : ZMod 3) * v l) • Pi.single j 1

private lemma ggQ2sw_dotLin_eq (m : ℕ) (hm : 4 ≤ m) (j : Fin m) (v : Fin m → ZMod 3) :
    ggQ2_DW_dotLin 3 m (ggDSimple 3 m j) (ggQ2sw_kappa m v) =
      ∑ l, ((CartanMatrix.D m j l : ℤ) : ZMod 3) * v l := by
  rw [ggQ2_DW_dotLin_apply]
  calc ∑ x, ggDSimple 3 m j x * (ggQ2sw_kappa m v) x
      = ∑ x, ∑ l, ggDSimple 3 m j x * (v l * ggDSimple 3 m l x) := by
          apply Finset.sum_congr rfl; intro x _
          rw [ggQ2sw_kappa_apply, Finset.mul_sum]
    _ = ∑ l, ∑ x, ggDSimple 3 m j x * (v l * ggDSimple 3 m l x) := Finset.sum_comm
    _ = ∑ l, v l * (∑ x, ggDSimple 3 m j x * ggDSimple 3 m l x) := by
          apply Finset.sum_congr rfl; intro l _
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x _ => by ring)
    _ = ∑ l, v l * ((CartanMatrix.D m j l : ℤ) : ZMod 3) := by
          apply Finset.sum_congr rfl; intro l _
          rw [ggQ2_DW_simple_dot 3 m hm j l]
    _ = ∑ l, ((CartanMatrix.D m j l : ℤ) : ZMod 3) * v l := by
          exact Finset.sum_congr rfl (fun l _ => by ring)

private lemma ggQ2sw_kappa_refl (m : ℕ) (hm : 4 ≤ m) (j : Fin m)
    (v : Fin m → ZMod 3) :
    ggQ2sw_kappa m (ggQ2sw_R m j v) = ggQ2_DW_r 3 m hm j (ggQ2sw_kappa m v) := by
  rw [ggQ2_DW_r_apply, ggQ2sw_R, map_sub, map_smul, ggQ2sw_kappa_single,
    ggQ2sw_dotLin_eq m hm j v]
  rfl

private noncomputable def ggQ2sw_theta (D : GGQ2Lin 3) {m : ℕ}
    (f : Fin m ≃ {k // k ≠ D.a}) : (Fin m → ZMod 3) →ₗ[ZMod 3] D.V where
  toFun v := ∑ i, v i • D.coroot (f i)
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [smul_smul, RingHom.id_apply])

private lemma ggQ2sw_theta_single (D : GGQ2Lin 3) {m : ℕ}
    (f : Fin m ≃ {k // k ≠ D.a}) (i : Fin m) :
    ggQ2sw_theta D f (Pi.single i 1) = D.coroot (f i) := by
  change (∑ k, (Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) k • D.coroot (f k)) =
    D.coroot (f i)
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma ggQ2sw_theta_root (D : GGQ2Lin 3) {m : ℕ}
    (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D m i j) (j : Fin m)
    (v : Fin m → ZMod 3) :
    D.root (f j) (ggQ2sw_theta D f v) =
      ∑ l, ((CartanMatrix.D m j l : ℤ) : ZMod 3) * v l := by
  change D.root (f j) (∑ i, v i • D.coroot (f i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, D.pairing, hf j i]
  simp only [smul_eq_mul]
  ring

private lemma ggQ2sw_theta_refl (D : GGQ2Lin 3) {m : ℕ}
    (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D m i j) (j : Fin m)
    (v : Fin m → ZMod 3) :
    D.simpleRefl (f j) (ggQ2sw_theta D f v) =
      ggQ2sw_theta D f (ggQ2sw_R m j v) := by
  rw [show D.simpleRefl (f j) = Module.reflection (D.root_coroot_self (f j)) from rfl,
    Module.reflection_apply, ggQ2sw_theta_root D f hf j v, ggQ2sw_R]
  rw [map_sub, map_smul, ggQ2sw_theta_single]

private noncomputable def ggQ2sw_good (D : GGQ2Lin 3) {m : ℕ} (hm : 4 ≤ m)
    (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D m i j) :
    Subgroup ((Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3)) where
  carrier := {W' | ∃ w ∈ D.parab {k | k ≠ D.a}, ∀ v,
    w (ggQ2sw_theta D f v) =
      ggQ2sw_theta D f ((ggQ2sw_kappaEquiv m hm).symm (W' ((ggQ2sw_kappaEquiv m hm) v)))}
  one_mem' := by
    refine ⟨1, Subgroup.one_mem _, fun v => ?_⟩
    simp [LinearEquiv.symm_apply_apply]
  mul_mem' := by
    rintro W1' W2' ⟨w1, hw1, h1⟩ ⟨w2, hw2, h2⟩
    refine ⟨w1 * w2, Subgroup.mul_mem _ hw1 hw2, fun v => ?_⟩
    rw [LinearEquiv.mul_apply]
    rw [h2 v, h1 ((ggQ2sw_kappaEquiv m hm).symm (W2' ((ggQ2sw_kappaEquiv m hm) v)))]
    simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
  inv_mem' := by
    rintro W' ⟨w, hw, h⟩
    refine ⟨w⁻¹, Subgroup.inv_mem _ hw, fun v => ?_⟩
    have key : w (ggQ2sw_theta D f ((ggQ2sw_kappaEquiv m hm).symm
        (W'⁻¹ ((ggQ2sw_kappaEquiv m hm) v)))) = ggQ2sw_theta D f v := by
      have h0 := h ((ggQ2sw_kappaEquiv m hm).symm (W'⁻¹ ((ggQ2sw_kappaEquiv m hm) v)))
      have hW : W' (W'⁻¹ ((ggQ2sw_kappaEquiv m hm) v)) = (ggQ2sw_kappaEquiv m hm) v := by
        rw [← LinearEquiv.mul_apply, mul_inv_cancel]
        rfl
      rw [LinearEquiv.apply_symm_apply, hW] at h0
      rw [LinearEquiv.symm_apply_apply] at h0
      exact h0
    have hfinal := congrArg (fun x => w⁻¹ x) key
    rw [show w⁻¹ (w (ggQ2sw_theta D f ((ggQ2sw_kappaEquiv m hm).symm
        (W'⁻¹ ((ggQ2sw_kappaEquiv m hm) v))))) = ggQ2sw_theta D f
        ((ggQ2sw_kappaEquiv m hm).symm (W'⁻¹ ((ggQ2sw_kappaEquiv m hm) v))) from
      LinearEquiv.symm_apply_apply w _] at hfinal
    exact hfinal.symm

private lemma ggQ2sw_good_generator (D : GGQ2Lin 3) {m : ℕ} (hm : 4 ≤ m)
    (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D m i j) (j : Fin m) :
    ggQ2_DW_r 3 m hm j ∈ ggQ2sw_good D hm f hf := by
  refine ⟨D.simpleRefl (f j), Subgroup.subset_closure ⟨f j, (f j).2, rfl⟩, fun v => ?_⟩
  rw [ggQ2sw_theta_refl D f hf j]
  congr 1
  change ggQ2sw_R m j v = (ggQ2sw_kappaEquiv m hm).symm
    (ggQ2_DW_r 3 m hm j (ggQ2sw_kappa m v))
  rw [← ggQ2sw_kappa_refl m hm j v]
  exact (LinearEquiv.symm_apply_apply (ggQ2sw_kappaEquiv m hm) (ggQ2sw_R m j v)).symm

private lemma ggQ2sw_Wc_le_good (D : GGQ2Lin 3) {m : ℕ} (hm : 4 ≤ m)
    (f : Fin m ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D m i j) :
    ggQ2_DW_Wc 3 m hm ≤ ggQ2sw_good D hm f hf := by
  rw [ggQ2_DW_Wc, Subgroup.closure_le]
  rintro x ⟨j, rfl⟩
  exact ggQ2sw_good_generator D hm f hf j

private noncomputable def ggQ2sw_pf (m : ℕ) (hm4 : 4 ≤ m) (i j : Fin m) (hij : i ≠ j) :
    (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3) :=
  ggBCRefl ((Pi.single i 1 : Fin m → ZMod 3) - Pi.single j 1)
      (by rw [ggQ2_DW_sub_norm i j hij]; decide) *
    ggBCRefl ((Pi.single i 1 : Fin m → ZMod 3) + Pi.single j 1)
      (by rw [ggQ2_DW_add_norm i j hij]; decide)

private lemma ggQ2sw_dot_sub {m : ℕ} (i j : Fin m) (v : Fin m → ZMod 3) :
    ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) - Pi.single j 1) ⬝ᵥ v = v i - v j := by
  rw [show ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) - Pi.single j 1) ⬝ᵥ v =
    ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i - ggQ2_DW_fvec 3 m j) v from rfl,
    ggQ2_DW_dotLin_fvec_sub]

private lemma ggQ2sw_dot_add {m : ℕ} (i j : Fin m) (v : Fin m → ZMod 3) :
    ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) + Pi.single j 1) ⬝ᵥ v = v i + v j := by
  rw [show ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) + Pi.single j 1) ⬝ᵥ v =
    ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i + ggQ2_DW_fvec 3 m j) v from rfl,
    ggQ2_DW_dotLin_apply]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single i]
    · simp [ggQ2_DW_fvec, Pi.single_apply]
    · intro b _ hb; simp [ggQ2_DW_fvec, Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [Finset.sum_eq_single j]
    · simp [ggQ2_DW_fvec, Pi.single_apply]
    · intro b _ hb; simp [ggQ2_DW_fvec, Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ j) h

private lemma ggQ2sw_dot_sub_add {m : ℕ} (i j : Fin m) :
    ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) - Pi.single j 1) ⬝ᵥ
      ((Pi.single i 1 : Fin m → ZMod 3) + Pi.single j 1) = 0 := by
  rw [ggQ2sw_dot_sub]
  by_cases hij : i = j
  · subst hij; simp [Pi.add_apply, Pi.single_apply]
  · simp [Pi.add_apply, Pi.single_apply, hij, Ne.symm hij]

private lemma ggQ2sw_dot_add_right {m : ℕ} (c v w : Fin m → ZMod 3) :
    c ⬝ᵥ (v + w) = c ⬝ᵥ v + c ⬝ᵥ w := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma ggQ2sw_dot_smul_right {m : ℕ} (c w : Fin m → ZMod 3) (a : ZMod 3) :
    c ⬝ᵥ (a • w) = a * (c ⬝ᵥ w) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

private lemma ggQ2sw_scalar_five (x : ZMod 3) : x * 5 = -x := by
  revert x; decide

private lemma ggQ2sw_pf_mem (m : ℕ) (hm4 : 4 ≤ m) (i j : Fin m) (hij : i ≠ j) :
    ggQ2sw_pf m hm4 i j hij ∈ ggQ2_DW_Wc 3 m hm4 := by
  rw [ggQ2sw_pf]
  exact Subgroup.mul_mem _
    (ggQ2_DW_Droot_refl_mem_Wc m hm4
      (by rw [ggDRoots]; exact ggQ2_DW_Wt_sub_single i j hij)
      (by rw [ggQ2_DW_sub_norm i j hij]; decide))
    (ggQ2_DW_Droot_refl_mem_Wc m hm4
      (by rw [ggDRoots]; exact ggQ2_DW_Wt_add_single i j hij)
      (by rw [ggQ2_DW_add_norm i j hij]; decide))

private lemma ggQ2sw_pf_apply (m : ℕ) (hm4 : 4 ≤ m) (i j : Fin m) (hij : i ≠ j)
    (v : Fin m → ZMod 3) (l : Fin m) :
    ggQ2sw_pf m hm4 i j hij v l = if l = i ∨ l = j then - v l else v l := by
  have hsub : ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) - Pi.single j 1) ⬝ᵥ v =
      v i - v j := ggQ2sw_dot_sub i j v
  have hadd : ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) + Pi.single j 1) ⬝ᵥ v =
      v i + v j := ggQ2sw_dot_add i j v
  have hza : ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) - Pi.single j 1) ⬝ᵥ
      ((Pi.single i 1 : Fin m → ZMod 3) + Pi.single j 1) = 0 := ggQ2sw_dot_sub_add i j
  have hinner : ((Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) - Pi.single j 1) ⬝ᵥ
      (v + ((v i + v j) * 2) • ((Pi.single i 1 : Fin m → ZMod 3) + Pi.single j 1)) =
      v i - v j := by
    rw [ggQ2sw_dot_add_right, ggQ2sw_dot_smul_right, hsub, hza, mul_zero, add_zero]
  rw [ggQ2sw_pf, LinearEquiv.mul_apply, ggQ2_DW_bc_apply', ggQ2_DW_bc_apply',
    ggQ2_DW_add_norm i j hij, ggQ2_DW_sub_norm i j hij, hadd, hinner]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hli : l = i
  · rw [hli]
    have hps_i : (Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) i = 1 := by
      simp [Pi.single_apply]
    have hps_j : (Pi.single j (1 : ZMod 3) : Fin m → ZMod 3) i = 0 := by
      simp [Pi.single_apply, Ne.symm hij]
    rw [hps_i, hps_j, if_pos (Or.inl rfl)]
    ring_nf
    exact ggQ2sw_scalar_five (v i)
  · by_cases hlj : l = j
    · rw [hlj]
      have hps_i : (Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) j = 0 := by
        simp [Pi.single_apply, Ne.symm hij]
      have hps_j : (Pi.single j (1 : ZMod 3) : Fin m → ZMod 3) j = 1 := by
        simp [Pi.single_apply]
      rw [hps_i, hps_j, if_pos (Or.inr rfl)]
      ring_nf
      exact ggQ2sw_scalar_five (v j)
    · rw [if_neg (fun h => h.elim hli hlj)]
      have hps_i : (Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) l = 0 := by
        simp [Pi.single_apply, hli]
      have hps_j : (Pi.single j (1 : ZMod 3) : Fin m → ZMod 3) l = 0 := by
        simp [Pi.single_apply, hlj]
      rw [hps_i, hps_j]
      ring_nf

private lemma ggQ2sw_signFlip_exists (m : ℕ) (hm4 : 4 ≤ m) :
    ∀ k, ∀ S : Finset (Fin m), S.card = 2 * k →
      ∃ W ∈ ggQ2_DW_Wc 3 m hm4,
        ∀ v l, W v l = if l ∈ S then - v l else v l := by
  intro k
  induction k with
  | zero =>
    intro S hS
    have h0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨1, Subgroup.one_mem _, fun v l => ?_⟩
    simp [h0]
  | succ k ih =>
    intro S hS
    have hpos : 0 < S.card := by omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    have hpos' : 0 < (S.erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos'
    have hjS : j ∈ S := Finset.mem_of_mem_erase hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hij : i ≠ j := fun h => hji h.symm
    have hS'' : ((S.erase i).erase j).card = 2 * k := by
      rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi]; omega
    obtain ⟨W', hW'c, hW'⟩ := ih ((S.erase i).erase j) hS''
    refine ⟨ggQ2sw_pf m hm4 i j hij * W',
      Subgroup.mul_mem _ (ggQ2sw_pf_mem m hm4 i j hij) hW'c, fun v l => ?_⟩
    have hS_eq : insert i (insert j ((S.erase i).erase j)) = S := by
      rw [Finset.insert_erase hj, Finset.insert_erase hi]
    have hni : i ∉ (S.erase i).erase j :=
      fun h => Finset.notMem_erase i S (Finset.mem_of_mem_erase h)
    rw [LinearEquiv.mul_apply, ggQ2sw_pf_apply, hW' v l, ← hS_eq]
    simp only [Finset.mem_insert]
    by_cases h1 : l = i
    · simp [h1, hni, hij]
    · by_cases h2 : l = j
      · have hnj : j ∉ (S.erase i).erase j := Finset.notMem_erase j (S.erase i)
        simp [h1, h2, hnj, Ne.symm hij, hij]
      · by_cases h3 : l ∈ (S.erase i).erase j
        · have hmem : l ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h3)
          simp [h1, h2, h3, hmem]
        · have hmem : l ∉ S := by
            intro h
            rw [← hS_eq, Finset.mem_insert, Finset.mem_insert] at h
            rcases h with h' | h' | h'
            · exact h1 h'
            · exact h2 h'
            · exact h3 h'
          simp [h1, h2, h3, hmem]

private lemma ggQ2sw_last_flip (m : ℕ) (hm4 : 4 ≤ m) (hodd : Odd m) :
    ∃ W ∈ ggQ2_DW_Wc 3 m hm4, ∀ v l,
      W v l = if l = (⟨m - 1, by omega⟩ : Fin m) then v l else - v l := by
  obtain ⟨t, ht⟩ := hodd
  have hcard : (Finset.univ.erase (⟨m - 1, by omega⟩ : Fin m)).card = 2 * t := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨W, hWc, hW⟩ := ggQ2sw_signFlip_exists m hm4 t _ hcard
  refine ⟨W, hWc, fun v l => ?_⟩
  rw [hW v l]
  by_cases hl : l = (⟨m - 1, by omega⟩ : Fin m)
  · rw [if_neg (by rw [Finset.mem_erase]; exact fun h => h.1 hl), if_pos hl]
  · rw [if_pos (by rw [Finset.mem_erase]; exact ⟨hl, Finset.mem_univ l⟩), if_neg hl]

private lemma ggQ2sw_dsimple_lt (m : ℕ) {i : Fin m} (hi : (i : ℕ) + 2 < m) (l : Fin m) :
    ggDSimple 3 m i l =
      if (l : ℕ) = (i : ℕ) then 1 else if (l : ℕ) = (i : ℕ) + 1 then -1 else 0 := by
  rw [ggDSimple, if_pos (by omega : (i : ℕ) + 1 < m)]
  rfl

private lemma ggQ2sw_dsimple_a (m : ℕ) (hm4 : 4 ≤ m) (l : Fin m) :
    ggDSimple 3 m (⟨m - 2, by omega⟩ : Fin m) l =
      if (l : ℕ) = m - 2 then 1 else if (l : ℕ) = m - 2 + 1 then -1 else 0 := by
  rw [ggDSimple, if_pos (show (⟨m - 2, by omega⟩ : Fin m).val + 1 < m by
    simp only [Fin.val_mk]; omega)]
  rfl

private lemma ggQ2sw_dsimple_last (m : ℕ) (hm4 : 4 ≤ m) (l : Fin m) :
    ggDSimple 3 m (⟨m - 1, by omega⟩ : Fin m) l =
      if (l : ℕ) + 2 = m ∨ (l : ℕ) + 1 = m then 1 else 0 := by
  rw [ggDSimple, if_neg (show ¬ (⟨m - 1, by omega⟩ : Fin m).val + 1 < m by
    simp only [Fin.val_mk]; omega)]

private lemma ggQ2sw_dsimple_last' (m : ℕ) (hm4 : 4 ≤ m) (l : Fin m) :
    ggDSimple 3 m (⟨m - 1, by omega⟩ : Fin m) l =
      if (l : ℕ) = m - 2 ∨ (l : ℕ) = m - 1 then 1 else 0 := by
  rw [ggQ2sw_dsimple_last m hm4 l]
  by_cases h : (l : ℕ) + 2 = m ∨ (l : ℕ) + 1 = m
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

private lemma ggQ2sw_last_flip_lt (m : ℕ) (hm4 : 4 ≤ m)
    (W : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3))
    (hW : ∀ v l, W v l = if l = (⟨m - 1, by omega⟩ : Fin m) then v l else - v l)
    {i : Fin m} (hi : (i : ℕ) + 2 < m) :
    W (ggDSimple 3 m i) =
      - ggDSimple 3 m (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i) := by
  have htau : Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i = i :=
    Equiv.swap_apply_of_ne_of_ne
      (fun h => by have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
      (fun h => by have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
  rw [htau]
  funext l
  rw [hW, Pi.neg_apply, ggQ2sw_dsimple_lt m hi l]
  by_cases hl : l = (⟨m - 1, by omega⟩ : Fin m)
  · have e1 : (↑(⟨m - 1, by omega⟩ : Fin m) : ℕ) ≠ (i : ℕ) := by
      simp only [Fin.val_mk]; omega
    have e2 : (↑(⟨m - 1, by omega⟩ : Fin m) : ℕ) ≠ (i : ℕ) + 1 := by
      simp only [Fin.val_mk]; omega
    rw [if_pos hl, hl, if_neg e1, if_neg e2]
    decide
  · rw [if_neg hl]

private lemma ggQ2sw_last_flip_a (m : ℕ) (hm4 : 4 ≤ m)
    (W : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3))
    (hW : ∀ v l, W v l = if l = (⟨m - 1, by omega⟩ : Fin m) then v l else - v l) :
    W (ggDSimple 3 m (⟨m - 2, by omega⟩ : Fin m)) =
      - ggDSimple 3 m (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m)
          (⟨m - 2, by omega⟩ : Fin m)) := by
  rw [Equiv.swap_apply_left]
  funext l
  rw [hW, Pi.neg_apply, ggQ2sw_dsimple_a m hm4 l, ggQ2sw_dsimple_last' m hm4 l]
  by_cases h1 : (l : ℕ) = m - 2
  · have hl : l ≠ (⟨m - 1, by omega⟩ : Fin m) := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    have hq : ¬ (l : ℕ) = m - 2 + 1 := by omega
    have hr : (l : ℕ) = m - 2 ∨ (l : ℕ) = m - 1 := Or.inl h1
    rw [if_neg hl]
    simp [h1, hq, hr, show m - 2 + 1 = m - 1 by omega, show m - 1 ≠ m - 2 by omega, neg_neg]
  · by_cases h2 : (l : ℕ) = m - 1
    · have hl : l = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext h2
      have hq : (l : ℕ) = m - 2 + 1 := by omega
      have hr : (l : ℕ) = m - 2 ∨ (l : ℕ) = m - 1 := Or.inr h2
      rw [if_pos hl]
      simp [h1, hq, hr, show m - 2 + 1 = m - 1 by omega, show m - 1 ≠ m - 2 by omega, neg_neg]
    · have hl : l ≠ (⟨m - 1, by omega⟩ : Fin m) := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
      have hq : ¬ (l : ℕ) = m - 2 + 1 := by omega
      have hr : ¬ ((l : ℕ) = m - 2 ∨ (l : ℕ) = m - 1) := by rintro (h | h) <;> omega
      rw [if_neg hl]
      simp [h1, h2, hq, hr, show m - 2 + 1 = m - 1 by omega, show m - 1 ≠ m - 2 by omega, neg_neg]

private lemma ggQ2sw_last_flip_last (m : ℕ) (hm4 : 4 ≤ m)
    (W : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3))
    (hW : ∀ v l, W v l = if l = (⟨m - 1, by omega⟩ : Fin m) then v l else - v l) :
    W (ggDSimple 3 m (⟨m - 1, by omega⟩ : Fin m)) =
      - ggDSimple 3 m (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m)
          (⟨m - 1, by omega⟩ : Fin m)) := by
  rw [Equiv.swap_apply_right]
  funext l
  rw [hW, Pi.neg_apply, ggQ2sw_dsimple_last' m hm4 l, ggQ2sw_dsimple_a m hm4 l]
  by_cases h1 : (l : ℕ) = m - 2
  · have hl : l ≠ (⟨m - 1, by omega⟩ : Fin m) := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    have hr : (l : ℕ) = m - 2 ∨ (l : ℕ) = m - 1 := Or.inl h1
    have hq : ¬ (l : ℕ) = m - 2 + 1 := by omega
    rw [if_neg hl]
    simp [h1, hr, hq, show m - 2 + 1 = m - 1 by omega, show m - 1 ≠ m - 2 by omega, neg_neg]
  · by_cases h2 : (l : ℕ) = m - 1
    · have hl : l = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext h2
      have hq : (l : ℕ) = m - 2 + 1 := by omega
      have hr : (l : ℕ) = m - 2 ∨ (l : ℕ) = m - 1 := Or.inr h2
      rw [if_pos hl]
      simp [h1, hq, hr, show m - 2 + 1 = m - 1 by omega, show m - 1 ≠ m - 2 by omega, neg_neg]
      decide
    · have hl : l ≠ (⟨m - 1, by omega⟩ : Fin m) := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
      have hr : ¬ ((l : ℕ) = m - 2 ∨ (l : ℕ) = m - 1) := by rintro (h | h) <;> omega
      have hq : ¬ (l : ℕ) = m - 2 + 1 := by omega
      rw [if_neg hl]
      simp [h1, h2, hr, hq, show m - 2 + 1 = m - 1 by omega, show m - 1 ≠ m - 2 by omega, neg_neg]

private lemma ggQ2sw_last_flip_dsimple (m : ℕ) (hm4 : 4 ≤ m)
    (W : (Fin m → ZMod 3) ≃ₗ[ZMod 3] (Fin m → ZMod 3))
    (hW : ∀ v l, W v l = if l = (⟨m - 1, by omega⟩ : Fin m) then v l else - v l)
    (i : Fin m) :
    W (ggDSimple 3 m i) =
      - ggDSimple 3 m (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i) := by
  rcases lt_trichotomy (i : ℕ) (m - 2) with hlt | heq | hgt
  · exact ggQ2sw_last_flip_lt m hm4 W hW (by omega)
  · rw [show i = (⟨m - 2, by omega⟩ : Fin m) from Fin.ext heq]
    exact ggQ2sw_last_flip_a m hm4 W hW
  · rw [show i = (⟨m - 1, by omega⟩ : Fin m) from
      Fin.ext (by simp only [Fin.val_mk]; omega)]
    exact ggQ2sw_last_flip_last m hm4 W hW

theorem ggQ2s5_dodd_w0 (D : GGQ2Lin 3) {m : ℕ} (hm : 5 ≤ m) (hodd : Odd m)
    (f : Fin m ≃ {k // k ≠ D.a}) (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D m i j) :
    ∃ w ∈ D.parab {k | k ≠ D.a}, ∀ i : Fin m, w (D.coroot (f i)) =
      - D.coroot (f (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ i)) := by
  have hm4 : 4 ≤ m := by omega
  obtain ⟨W, hWc, hW⟩ := ggQ2sw_last_flip m hm4 hodd
  have hWds : ∀ i : Fin m, W (ggDSimple 3 m i) =
      - ggDSimple 3 m (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i) :=
    fun i => ggQ2sw_last_flip_dsimple m hm4 W hW i
  obtain ⟨w, hwparab, hwact⟩ := ggQ2sw_Wc_le_good D hm4 f hf hWc
  refine ⟨w, hwparab, fun i => ?_⟩
  have h1 := hwact (Pi.single i 1)
  rw [ggQ2sw_theta_single D f i] at h1
  have hk : (ggQ2sw_kappaEquiv m hm4) (Pi.single i 1) = ggDSimple 3 m i :=
    ggQ2sw_kappa_single m i
  rw [hk, hWds i] at h1
  have hsym : (ggQ2sw_kappaEquiv m hm4).symm
      (- ggDSimple 3 m (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i)) =
      - Pi.single (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i) 1 := by
    have hmap : (ggQ2sw_kappaEquiv m hm4).symm
        (- ggDSimple 3 m (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i)) =
        - (ggQ2sw_kappaEquiv m hm4).symm
          (ggDSimple 3 m (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i)) :=
      map_neg _ _
    rw [hmap]
    have h1' : (ggQ2sw_kappaEquiv m hm4)
        (Pi.single (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i)
          (1 : ZMod 3) : Fin m → ZMod 3) =
        ggDSimple 3 m (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i) :=
      ggQ2sw_kappa_single m _
    rw [← h1']
    exact congrArg Neg.neg (LinearEquiv.symm_apply_apply (ggQ2sw_kappaEquiv m hm4)
      (Pi.single (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i)
        (1 : ZMod 3) : Fin m → ZMod 3))
  rw [hsym] at h1
  have hneg : (ggQ2sw_theta D f)
      (- (Pi.single (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i)
        (1 : ZMod 3) : Fin m → ZMod 3)) =
      - D.coroot (f (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i)) := by
    have hmap : (ggQ2sw_theta D f)
        (- (Pi.single (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i)
          (1 : ZMod 3) : Fin m → ZMod 3)) =
        - (ggQ2sw_theta D f)
          (Pi.single (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) (⟨m - 1, by omega⟩ : Fin m) i)
            (1 : ZMod 3) : Fin m → ZMod 3) :=
      map_neg _ _
    rw [hmap, ggQ2sw_theta_single]
  rw [hneg] at h1
  exact h1

end CFSG.StandardType

end
