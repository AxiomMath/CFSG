module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerPhi
public import CFSG.LocalAnalysis.StandardType.GGQTwoCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_A_label (n : ℕ) (i j : Fin n) :
    (CoxeterMatrix.A n) i j =
      (if i = j then 1
        else if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then 3 else 2) := by
  rw [CoxeterMatrix.A]
  simp only [CoxeterMatrix.M, Matrix.of_apply]
  split_ifs <;> omega

theorem ggQ2_reindex_trans {B B' B'' : Type*} (M : CoxeterMatrix B) (e : B ≃ B')
    (f : B' ≃ B'') : (M.reindex e).reindex f = M.reindex (e.trans f) := by
  ext i j
  rw [CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply]
  rfl

theorem ggQ2_A_rev (n : ℕ) :
    (CoxeterMatrix.A n).reindex Fin.revPerm = CoxeterMatrix.A n := by
  ext i j
  rw [CoxeterMatrix.reindex_apply, ggQ2_A_label, ggQ2_A_label]
  simp only [Fin.revPerm_symm, Fin.revPerm_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hre : Fin.rev i ≠ Fin.rev j := fun h => hij (Fin.rev_injective h)
    rw [if_neg hij, if_neg hre]
    congr 1
    apply propext
    constructor <;> intro h <;>
      (simp only [Fin.rev] at *; omega)

theorem ggQ2_A_leaf_reverse (D : GGQ2Lin 3) {n : ℕ} (hn : 1 ≤ n) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e) (ha : D.a = e ⟨n - 1, by omega⟩) :
    ∃ e' : Fin n ≃ D.ι, D.coxeter = (CoxeterMatrix.A n).reindex e' ∧
      D.a = e' ⟨0, by omega⟩ := by
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨Fin.revPerm.trans e, ?_, ?_⟩
  · rw [hA, ← ggQ2_reindex_trans (CoxeterMatrix.A n) Fin.revPerm e, ggQ2_A_rev]
  · rw [ha, Equiv.trans_apply, Fin.revPerm_apply]
    exact (congrArg e Fin.rev_bot).symm

private lemma ggQ2xAH_refl_apply {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    ggBCRefl c hc v = v + ((c ⬝ᵥ c) * (c ⬝ᵥ v)) • c := by
  rw [ggQ2x_ggBCRefl_apply, mul_comm (c ⬝ᵥ v) (c ⬝ᵥ c)]

private lemma ggQ2xAH_iso_scalar : ∀ r d p q : ZMod 3, d * d = 1 →
    r + d * p * q + d * q * (p + d * p * d) = r := by decide

private lemma ggQ2xAH_refl_isometry {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0)
    (x y : GGBCV n) :
    (ggBCRefl c hc x) ⬝ᵥ (ggBCRefl c hc y) = x ⬝ᵥ y := by
  have hcast : ∀ z : ZMod 3, z ≠ 0 → z * z = 1 := by decide
  have hdd : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := hcast _ hc
  rw [ggQ2xAH_refl_apply, ggQ2xAH_refl_apply]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (c : GGBCV n) x, dotProduct_comm (c : GGBCV n) y]
  rw [ggQ2xAH_iso_scalar (x ⬝ᵥ y) (c ⬝ᵥ c) (x ⬝ᵥ c) (y ⬝ᵥ c) hdd]

private lemma ggQ2xAH_conj_refl {n : ℕ} (b : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (hb : ∀ x y, (b x) ⬝ᵥ (b y) = x ⬝ᵥ y)
    (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (hc' : (b c) ⬝ᵥ (b c) ≠ 0) :
    b * ggBCRefl c hc * b.symm = ggBCRefl (b c) hc' := by
  have hbc : (b c) ⬝ᵥ (b c) = c ⬝ᵥ c := hb c c
  ext v
  have hbv : (b c) ⬝ᵥ v = c ⬝ᵥ (b.symm v) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply b v]
    rw [hb c (b.symm v)]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2xAH_refl_apply, ggQ2xAH_refl_apply,
    map_add, map_smul, LinearEquiv.apply_symm_apply]
  rw [hbc, hbv]

private lemma ggQ2xAH_inv_eq_symm {n : ℕ} (b : GGBCV n ≃ₗ[ZMod 3] GGBCV n) :
    b⁻¹ = b.symm := by
  ext v
  rfl

private lemma ggQ2xAH_wt_smul {n : ℕ} (a : ZMod 3) (ha : a ≠ 0) (v : GGBCV n) :
    ggBCWt (a • v) = ggBCWt v := by
  unfold ggBCWt
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h hv
    exact h (by rw [hv, mul_zero])
  · intro hv
    exact mul_ne_zero ha hv

private lemma ggQ2xAH_sum_single {n : ℕ} (i : Fin n) :
    (∑ x, (Pi.single i (1 : ZMod 3) : GGBCV n) x) = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma ggQ2xAH_sum_smul_single {n : ℕ} (i : Fin n) (a : ZMod 3) :
    (∑ x, (a • (Pi.single i (1 : ZMod 3) : GGBCV n)) x) = a := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, ggQ2xAH_sum_single, mul_one]

private lemma ggQ2xAH_sum_pair {n : ℕ} (k l : Fin n) (a b : ZMod 3) :
    (∑ i, (a • (Pi.single k 1 : GGBCV n) + b • (Pi.single l 1 : GGBCV n)) i) = a + b := by
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, ggQ2xAH_sum_smul_single, ggQ2xAH_sum_smul_single]

private lemma ggQ2xAH_perm_single {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    ggPermHom m σ (Pi.single i (1 : ZMod 3) : GGBCV m) = Pi.single (σ i) 1 := by
  funext j
  rw [ggPermHom_apply]
  by_cases h : j = σ i
  · subst h
    rw [Equiv.symm_apply_apply, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) h,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3)
        (fun hc => h (by rw [← hc, Equiv.apply_symm_apply]))]

private lemma ggQ2xAH_weight_two {m : ℕ} {v : GGBCV m} (hv : ggBCWt v = 2) :
    ∃ (i j : Fin m) (a b : ZMod 3), i ≠ j ∧ a ≠ 0 ∧ b ≠ 0 ∧
      v = a • (Pi.single i 1 : GGBCV m) + b • (Pi.single j 1 : GGBCV m) := by
  unfold ggBCWt at hv
  obtain ⟨i, j, hij, hS⟩ := Finset.card_eq_two.mp hv
  have hvi : v i ≠ 0 := by
    have hmem : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hS]; simp
    simpa using hmem
  have hvj : v j ≠ 0 := by
    have hmem : j ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hS]; simp
    simpa using hmem
  refine ⟨i, j, v i, v j, hij, hvi, hvj, ?_⟩
  funext k
  by_cases hki : k = i
  · subst hki
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij, smul_eq_mul, mul_one, mul_zero, add_zero]
  · by_cases hkj : k = j
    · subst hkj
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij), smul_eq_mul, mul_one,
        mul_zero, zero_add]
    · have hvk : v k = 0 := by
        by_contra hne
        have hmem : k ∈ Finset.univ.filter (fun k => v k ≠ 0) := by simp [hne]
        rw [hS] at hmem
        simp [hki, hkj] at hmem
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hki,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkj, smul_zero, smul_zero, add_zero]
      exact hvk

private lemma ggQ2xAH_neg_one_smul {n : ℕ} (v : GGBCV n) :
    (-1 : ZMod 3) • v = -v := by
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply, neg_one_mul]

private lemma ggQ2xAH_neg_one_smul_sub {n : ℕ} (a b : Fin n) :
    (-1 : ZMod 3) • (Pi.single a 1 - Pi.single b 1 : GGBCV n) =
      Pi.single b 1 - Pi.single a 1 := by
  rw [ggQ2xAH_neg_one_smul]
  funext k
  simp only [Pi.neg_apply, Pi.sub_apply]
  ring

private lemma ggQ2xAH_aroot_lam1_classify {m : ℕ} [NeZero m] {v : GGBCV m}
    (hv : v ∈ ggARootsLam1 m) :
    ∃ i j : Fin m, i ≠ j ∧ i ≠ 0 ∧ j ≠ 0 ∧
      v = (Pi.single i 1 - Pi.single j 1 : GGBCV m) := by
  obtain ⟨⟨hwt, hsum⟩, hv0⟩ := hv
  obtain ⟨i, j, a, b, hij, ha, hb, hvij⟩ := ggQ2xAH_weight_two hwt
  have hab : a + b = 0 := by
    have h := hsum
    rw [hvij] at h
    rwa [ggQ2xAH_sum_pair] at h
  have hi0 : i ≠ 0 := by
    intro hi
    have hjne : j ≠ 0 := fun hj => hij (hi.trans hj.symm)
    have h : v 0 = a := by
      rw [hvij, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hi]
      simp [Pi.single_apply, hjne]
    rw [hv0] at h
    exact ha h.symm
  have hj0 : j ≠ 0 := by
    intro hj
    have hine : i ≠ 0 := fun hi => hij (hi.trans hj.symm)
    have h : v 0 = b := by
      rw [hvij, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hj]
      simp [Pi.single_apply, hine]
    rw [hv0] at h
    exact hb h.symm
  have hb_eq : b = -a := (neg_eq_of_add_eq_zero_right hab).symm
  have hva : v = a • (Pi.single i 1 - Pi.single j 1 : GGBCV m) := by
    rw [hvij, hb_eq, smul_sub, sub_eq_add_neg]
    congr 1
    exact neg_smul a (Pi.single j 1 : GGBCV m)
  rcases (by decide : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1) a ha with h1 | h1
  · exact ⟨i, j, hij, hi0, hj0, by rw [hva, h1, one_smul]⟩
  · refine ⟨j, i, hij.symm, hj0, hi0, ?_⟩
    rw [hva, h1]
    exact ggQ2xAH_neg_one_smul_sub i j

theorem ggQ2_A_refl_perm_root (m : ℕ) [NeZero m] (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0)
    (hsum : ∑ i, c i = 0) (σ : Equiv.Perm (Fin m)) (hσ : σ 0 = 0)
    (h : ∀ w : GGBCV m, ∑ i, w i = 0 → ggBCRefl c hc w = ggPermHom m σ w) :
    c ∈ ggARootsLam1 m := by
  have hσne : σ ≠ 1 := by
    intro hσ1
    have hfix : ggBCRefl c hc c = c := by
      rw [h c hsum, hσ1, map_one]; rfl
    have hcc : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := ggQ2x_mul_self_eq_one _ hc
    have hval : ggBCRefl c hc c = c + c := by
      rw [ggQ2xAH_refl_apply, hcc, one_smul]
    rw [hval] at hfix
    have hzero : c = 0 := by
      have h1 : c + c = c + 0 := by rw [hfix, add_zero]
      exact add_left_cancel h1
    exact hc (by rw [hzero]; simp)
  obtain ⟨k, hk⟩ : ∃ k : Fin m, σ k ≠ k := by
    by_contra hcon
    push Not at hcon
    exact hσne (Equiv.ext (fun i => hcon i))
  have hk0 : k ≠ 0 := fun hk0 => hk (by rw [hk0, hσ])
  have hσk0 : σ k ≠ 0 := fun h => hk0 (σ.injective (by rw [h, hσ]))
  have hwk_sum : ∑ i, (Pi.single k (1 : ZMod 3) - Pi.single 0 1 : GGBCV m) i = 0 := by
    rw [show (∑ x, (Pi.single k (1 : ZMod 3) - Pi.single 0 1 : GGBCV m) x)
        = (∑ x, (Pi.single k (1 : ZMod 3) : GGBCV m) x) -
          (∑ x, (Pi.single 0 (1 : ZMod 3) : GGBCV m) x) from
      Finset.sum_sub_distrib _ _]
    rw [ggQ2xAH_sum_single, ggQ2xAH_sum_single, sub_self]
  have hperm_w : ggPermHom m σ (Pi.single k (1 : ZMod 3) - Pi.single 0 1 : GGBCV m)
      = Pi.single (σ k) 1 - Pi.single 0 1 := by
    rw [map_sub, ggQ2xAH_perm_single, ggQ2xAH_perm_single, hσ]
  set lam : ZMod 3 := (c ⬝ᵥ c) *
    (c ⬝ᵥ (Pi.single k (1 : ZMod 3) - Pi.single 0 1 : GGBCV m)) with hlam_def
  have hval : lam • c = Pi.single (σ k) 1 - Pi.single k 1 := by
    have hkey : ggBCRefl c hc (Pi.single k (1 : ZMod 3) - Pi.single 0 1 : GGBCV m)
        = ggPermHom m σ (Pi.single k (1 : ZMod 3) - Pi.single 0 1 : GGBCV m) :=
      h _ hwk_sum
    rw [ggQ2xAH_refl_apply, ← hlam_def, hperm_w] at hkey
    have h2 : lam • c = (Pi.single (σ k) 1 - Pi.single 0 1)
        - (Pi.single k 1 - Pi.single 0 1 : GGBCV m) := by
      rw [← hkey]
      abel
    rw [h2]; abel
  have hlam_ne : lam ≠ 0 := by
    intro h0
    have hzero : (Pi.single (σ k) 1 - Pi.single k 1 : GGBCV m) = 0 := by
      rw [← hval, h0, zero_smul]
    have heq : (Pi.single (σ k) (1 : ZMod 3) : GGBCV m) = Pi.single k 1 :=
      sub_eq_zero.mp hzero
    have h2 := congrFun heq (σ k)
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk] at h2
    exact (by decide : (1 : ZMod 3) ≠ 0) h2
  have hc_eq : c = lam⁻¹ • (Pi.single (σ k) 1 - Pi.single k 1 : GGBCV m) := by
    rw [← hval, smul_smul, inv_mul_cancel₀ hlam_ne, one_smul]
  refine ⟨⟨?_, hsum⟩, ?_⟩
  · rw [hc_eq, ggQ2xAH_wt_smul _ (inv_ne_zero hlam_ne), ggQ2x_wt_sub_single _ _ hk]
  · rw [hc_eq, Pi.smul_apply, smul_eq_mul]
    have hz : (Pi.single (σ k) 1 - Pi.single k 1 : GGBCV m) 0 = 0 := by
      simp [Pi.sub_apply, Pi.single_apply, hσk0, hk0]
    rw [hz, mul_zero]

private lemma ggQ2xAH_refl_sum {n : ℕ} (z : GGBCV n) (hz : z ⬝ᵥ z ≠ 0)
    (hsum : ∑ i, z i = 0) {v : GGBCV n} (hv : ∑ i, v i = 0) :
    ∑ i, ggBCRefl z hz v i = 0 := by
  rw [ggQ2xAH_refl_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, hv, zero_add]
  rw [← Finset.mul_sum, hsum, mul_zero]

theorem ggQ2_A_HL_of_perm (m : ℕ) [NeZero m] (z : GGBCV m) (hz : z ⬝ᵥ z ≠ 0)
    (hsum : ∑ i, z i = 0)
    (hperm : ∀ ρ ∈ ggARootsLam1 m, ∀ hρ : ggBCRefl z hz ρ ⬝ᵥ ggBCRefl z hz ρ ≠ 0,
      ∃ σ : Equiv.Perm (Fin m), σ 0 = 0 ∧
        ∀ w : GGBCV m, ∑ i, w i = 0 → ggBCRefl (ggBCRefl z hz ρ) hρ w = ggPermHom m σ w) :
    ∀ ρ ∈ ggARootsLam1 m, ggBCRefl z hz ρ ∈ ggARootsLam1 m := by
  intro ρ hρ
  have hρroot : ρ ∈ ggARoots m := hρ.1
  have hρ_nn : ρ ⬝ᵥ ρ ≠ 0 := by
    rw [ggQ2x_dot_self_eq_wt, hρroot.1]; decide
  have hρ' : ggBCRefl z hz ρ ⬝ᵥ ggBCRefl z hz ρ ≠ 0 := by
    rw [ggQ2xAH_refl_isometry z hz ρ ρ]; exact hρ_nn
  obtain ⟨σ, hσ0, hσeq⟩ := hperm ρ hρ hρ'
  exact ggQ2_A_refl_perm_root m (ggBCRefl z hz ρ) hρ'
    (ggQ2xAH_refl_sum z hz hsum hρroot.2) σ hσ0 hσeq

private lemma ggQ2xAH_closure_perm {m : ℕ} [NeZero m]
    (p : GGBCV m ≃ₗ[ZMod 3] GGBCV m)
    (hp : p ∈ Subgroup.closure (ggBCReflSet (ggARootsLam1 m))) :
    ∃ σ : Equiv.Perm (Fin m), σ 0 = 0 ∧ p = ggPermHom m σ := by
  refine Subgroup.closure_induction
    (p := fun x _ => ∃ σ : Equiv.Perm (Fin m), σ 0 = 0 ∧ x = ggPermHom m σ)
    ?_ ?_ ?_ ?_ hp
  · rintro x ⟨ρ, hρ, hρc, ht⟩
    obtain ⟨i, j, hij, hi0, hj0, hρeq⟩ := ggQ2xAH_aroot_lam1_classify hρ
    subst hρeq
    refine ⟨Equiv.swap i j, ?_, ?_⟩
    · rw [Equiv.swap_apply_of_ne_of_ne (show (0 : Fin m) ≠ i from Ne.symm hi0)
        (show (0 : Fin m) ≠ j from Ne.symm hj0)]
    · rw [ht]
      exact (ggPermHom_swap i j hij hρc).symm
  · exact ⟨1, rfl, (map_one (ggPermHom m)).symm⟩
  · intro x y hx hy ihx ihy
    obtain ⟨σ, hσ0, hxσ⟩ := ihx
    obtain ⟨τ, hτ0, hyτ⟩ := ihy
    refine ⟨σ * τ, ?_, ?_⟩
    · simp [hσ0, hτ0]
    · rw [hxσ, hyτ, map_mul]
  · intro x hx ihx
    obtain ⟨σ, hσ0, hxσ⟩ := ihx
    refine ⟨σ⁻¹, ?_, ?_⟩
    · rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]; exact hσ0.symm
    · rw [hxσ, map_inv]

theorem ggQ2_A_HL_of_normalizer (m : ℕ) [NeZero m] (z : GGBCV m) (hz : z ⬝ᵥ z ≠ 0)
    (hsum : ∑ i, z i = 0)
    (hN : ggBCRefl z hz ∈ Subgroup.normalizer
      (Subgroup.closure (ggBCReflSet (ggARootsLam1 m)) : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))) :
    ∀ ρ ∈ ggARootsLam1 m, ggBCRefl z hz ρ ∈ ggARootsLam1 m := by
  refine ggQ2_A_HL_of_perm m z hz hsum ?_
  intro ρ hρ hρ'
  have hρroot : ρ ∈ ggARoots m := hρ.1
  have hρ_nn : ρ ⬝ᵥ ρ ≠ 0 := by
    rw [ggQ2x_dot_self_eq_wt, hρroot.1]; decide
  have hs_mem : ggBCRefl ρ hρ_nn ∈
      Subgroup.closure (ggBCReflSet (ggARootsLam1 m)) :=
    Subgroup.subset_closure ⟨ρ, hρ, hρ_nn, rfl⟩
  have hconj_mem : ggBCRefl z hz * ggBCRefl ρ hρ_nn * (ggBCRefl z hz)⁻¹ ∈
      Subgroup.closure (ggBCReflSet (ggARootsLam1 m)) :=
    (Subgroup.mem_normalizer_iff.mp hN (ggBCRefl ρ hρ_nn)).mp hs_mem
  obtain ⟨σ, hσ0, hσeq⟩ := ggQ2xAH_closure_perm _ hconj_mem
  refine ⟨σ, hσ0, ?_⟩
  intro w hw
  have hconj := ggQ2xAH_conj_refl (ggBCRefl z hz)
    (fun x y => ggQ2xAH_refl_isometry z hz x y) ρ hρ_nn hρ'
  rw [ggQ2xAH_inv_eq_symm] at hσeq
  rw [← hconj, hσeq]

end CFSG.StandardType

end
