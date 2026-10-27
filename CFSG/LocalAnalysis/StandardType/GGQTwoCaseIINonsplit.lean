module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIITypes
public import CFSG.LocalAnalysis.StandardType.GGQTwoAHL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private abbrev ggQ2xCN_Lam (D : GGQ2Lin 3) : Type := {k : D.ι // k ≠ D.a}

private noncomputable def ggQ2xCN_toU (D : GGQ2Lin 3) :
    (ggQ2xCN_Lam D → ZMod 3) →ₗ[ZMod 3] D.V :=
  Fintype.linearCombination (ZMod 3) (fun k : ggQ2xCN_Lam D => D.coroot k.1)

private theorem ggQ2xCN_toU_apply (D : GGQ2Lin 3) (u : ggQ2xCN_Lam D → ZMod 3) :
    ggQ2xCN_toU D u = ∑ k, u k • D.coroot k.1 :=
  Fintype.linearCombination_apply (ZMod 3) _ u

private theorem ggQ2xCN_toU_injective (D : GGQ2Lin 3) (hII : D.CaseII) :
    Function.Injective (ggQ2xCN_toU D) := by
  intro u v huv
  have h0 : ggQ2xCN_toU D (u - v) = 0 := by rw [map_sub, huv, sub_self]
  rw [ggQ2xCN_toU_apply] at h0
  have hg := (Fintype.linearIndependent_iff.mp hII.2.1)
    (fun k : ggQ2xCN_Lam D => u k - v k) (by simpa only [Pi.sub_apply] using h0)
  ext k
  exact sub_eq_zero.mp (hg k)

private theorem ggQ2xCN_toU_single (D : GGQ2Lin 3) (k : ggQ2xCN_Lam D) (x : ZMod 3) :
    ggQ2xCN_toU D (Pi.single k x) = x • D.coroot k.1 := by
  rw [ggQ2xCN_toU_apply, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private theorem ggQ2xCN_simpleRefl_apply (D : GGQ2Lin 3) (k : D.ι) (v : D.V) :
    D.simpleRefl k v = v - D.root k v • D.coroot k := by
  rw [show D.simpleRefl k = Module.reflection (D.root_coroot_self k) from rfl]
  exact Module.reflection_apply v (D.root_coroot_self k)

private theorem ggQ2xCN_simpleRefl_symm (D : GGQ2Lin 3) (k : D.ι) :
    (D.simpleRefl k)⁻¹ = D.simpleRefl k := by
  rw [show D.simpleRefl k = Module.reflection (D.root_coroot_self k) from rfl]
  exact Module.reflection_symm _

private noncomputable def ggQ2xCN_refAct (D : GGQ2Lin 3) (k : ggQ2xCN_Lam D) :
    (ggQ2xCN_Lam D → ZMod 3) →ₗ[ZMod 3] (ggQ2xCN_Lam D → ZMod 3) :=
  ((LinearMap.id : (ggQ2xCN_Lam D → ZMod 3) →ₗ[ZMod 3] (ggQ2xCN_Lam D → ZMod 3)) -
    ((Fintype.linearCombination (ZMod 3)
      (fun j : ggQ2xCN_Lam D => (D.cartan k.1 j.1 : ZMod 3))).smulRight
      (Pi.single k (1 : ZMod 3) : ggQ2xCN_Lam D → ZMod 3) :
      (ggQ2xCN_Lam D → ZMod 3) →ₗ[ZMod 3] (ggQ2xCN_Lam D → ZMod 3)))

private theorem ggQ2xCN_refAct_apply (D : GGQ2Lin 3) (k : ggQ2xCN_Lam D)
    (u : ggQ2xCN_Lam D → ZMod 3) :
    ggQ2xCN_refAct D k u =
      u - (∑ j, (D.cartan k.1 j.1 : ZMod 3) * u j) • Pi.single k 1 := by
  rw [ggQ2xCN_refAct, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    Fintype.linearCombination_apply]
  have hcoef : (∑ j, u j • (D.cartan k.1 j.1 : ZMod 3)) =
      ∑ j, (D.cartan k.1 j.1 : ZMod 3) * u j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hcoef]

private theorem ggQ2xCN_toU_refAct (D : GGQ2Lin 3) (k : ggQ2xCN_Lam D)
    (u : ggQ2xCN_Lam D → ZMod 3) :
    ggQ2xCN_toU D (ggQ2xCN_refAct D k u) = D.simpleRefl k.1 (ggQ2xCN_toU D u) := by
  have hroot : D.root k.1 (ggQ2xCN_toU D u) = ∑ j, (D.cartan k.1 j.1 : ZMod 3) * u j := by
    rw [ggQ2xCN_toU_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, D.pairing, smul_eq_mul]
    ring
  rw [ggQ2xCN_refAct_apply, map_sub, map_smul, ggQ2xCN_toU_single, one_smul,
    ggQ2xCN_simpleRefl_apply, hroot]

private theorem ggQ2xCN_conj_reflection {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (a : V ≃ₗ[ZMod 3] V) {c : V} {φ : Dual (ZMod 3) V} (h : φ c = 2) :
    a * Module.reflection h * a⁻¹ =
      Module.reflection (show (φ.comp (a.symm : V →ₗ[ZMod 3] V)) (a c) = 2 by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        exact h) := by
  change a * Module.reflection h * a.symm =
      Module.reflection (show (φ.comp (a.symm : V →ₗ[ZMod 3] V)) (a c) = 2 by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        exact h)
  ext w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Module.reflection_apply (a.symm w) h,
    Module.reflection_apply w]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub, map_smul,
    LinearEquiv.apply_symm_apply]

private theorem ggQ2xCN_mul_refl_coroot (D : GGQ2Lin 3) (b : D.ι)
    (hab : D.cartan D.a b = -1) (hba : D.cartan b D.a = -1) :
    (D.simpleRefl b * D.simpleRefl D.a) (D.coroot b) = D.coroot D.a := by
  rw [LinearEquiv.mul_apply, ggQ2xCN_simpleRefl_apply, ggQ2xCN_simpleRefl_apply,
    map_sub, map_smul]
  simp only [D.root_coroot_self, D.pairing, smul_eq_mul]
  rw [hab, hba]
  module

private theorem ggQ2xCN_rootb_inv (D : GGQ2Lin 3) (b : D.ι)
    (hab : D.cartan D.a b = -1) (hba : D.cartan b D.a = -1) (v : D.V) :
    D.root b ((D.simpleRefl b * D.simpleRefl D.a)⁻¹ v) = D.root D.a v := by
  have hg : (D.simpleRefl b * D.simpleRefl D.a)⁻¹ =
      D.simpleRefl D.a * D.simpleRefl b := by
    rw [mul_inv_rev, ggQ2xCN_simpleRefl_symm, ggQ2xCN_simpleRefl_symm]
  rw [hg, LinearEquiv.mul_apply, ggQ2xCN_simpleRefl_apply, ggQ2xCN_simpleRefl_apply]
  simp only [map_sub, map_smul, D.root_coroot_self, D.pairing]
  rw [hab, hba]
  ring

private theorem ggQ2xCN_conj_refl (D : GGQ2Lin 3) (b : D.ι)
    (hab : D.cartan D.a b = -1) (hba : D.cartan b D.a = -1) :
    (D.simpleRefl b * D.simpleRefl D.a) * D.simpleRefl b *
        (D.simpleRefl b * D.simpleRefl D.a)⁻¹ = D.simpleRefl D.a := by
  have hconj := ggQ2xCN_conj_reflection (D.simpleRefl b * D.simpleRefl D.a)
    (D.root_coroot_self b)
  simp only [GGQ2Lin.simpleRefl] at hconj ⊢
  rw [hconj]
  apply LinearEquiv.ext
  intro w
  rw [Module.reflection_apply w, Module.reflection_apply w]
  have h1 : ∀ x, D.root b ((Module.reflection (D.root_coroot_self b) *
        Module.reflection (D.root_coroot_self D.a)).symm x) = D.root D.a x := by
    intro x
    exact ggQ2xCN_rootb_inv D b hab hba x
  have h2 : (Module.reflection (D.root_coroot_self b) *
      Module.reflection (D.root_coroot_self D.a)) (D.coroot b) = D.coroot D.a := by
    simpa only [GGQ2Lin.simpleRefl] using ggQ2xCN_mul_refl_coroot D b hab hba
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h2]
  rw [h1 w]

private theorem ggQ2xCN_parab_stable (D : GGQ2Lin 3)
    {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    (toW : W →ₗ[ZMod 3] D.V) (act : ggQ2xCN_Lam D → W → W)
    (hact : ∀ k w, toW (act k w) = D.simpleRefl k.1 (toW w))
    (I : Set W) (hI : ∀ k w, w ∈ I → act k w ∈ I) :
    ∀ g ∈ D.parab {k | k ≠ D.a},
      (∀ w ∈ I, ∃ w' ∈ I, g (toW w) = toW w') ∧
      (∀ w ∈ I, ∃ w' ∈ I, g⁻¹ (toW w) = toW w') := by
  have key : ∀ g ∈ D.parab {k | k ≠ D.a},
      (∀ w ∈ I, ∃ w' ∈ I, g (toW w) = toW w') ∧
      (∀ w ∈ I, ∃ w' ∈ I, g⁻¹ (toW w) = toW w') := by
    intro g hg
    have hg' : g ∈ Subgroup.closure (D.simpleRefl '' {k | k ≠ D.a}) := by
      simpa only [GGQ2Lin.parab] using hg
    refine Subgroup.closure_induction
      (p := fun x _ =>
        (∀ w ∈ I, ∃ w' ∈ I, x (toW w) = toW w') ∧
        (∀ w ∈ I, ∃ w' ∈ I, x⁻¹ (toW w) = toW w')) ?_ ?_ ?_ ?_ hg'
    · rintro x ⟨k, hk, hkx⟩
      rw [← hkx]
      refine ⟨?_, ?_⟩
      · intro w hw
        exact ⟨act ⟨k, hk⟩ w, hI ⟨k, hk⟩ w hw, (hact ⟨k, hk⟩ w).symm⟩
      · intro w hw
        refine ⟨act ⟨k, hk⟩ w, hI ⟨k, hk⟩ w hw, ?_⟩
        rw [ggQ2xCN_simpleRefl_symm, hact]
    · refine ⟨?_, ?_⟩
      · intro w hw; exact ⟨w, hw, rfl⟩
      · intro w hw; exact ⟨w, hw, rfl⟩
    · intro x y hx hy hPx hPy
      refine ⟨?_, ?_⟩
      · intro w hw
        obtain ⟨w1, hw1, h1⟩ := hPy.1 w hw
        obtain ⟨w2, hw2, h2⟩ := hPx.1 w1 hw1
        exact ⟨w2, hw2, by rw [LinearEquiv.mul_apply, h1, h2]⟩
      · intro w hw
        obtain ⟨w1, hw1, h1⟩ := hPx.2 w hw
        obtain ⟨w2, hw2, h2⟩ := hPy.2 w1 hw1
        exact ⟨w2, hw2, by rw [mul_inv_rev, LinearEquiv.mul_apply, h1, h2]⟩
    · intro x hx hPx
      refine ⟨hPx.2, ?_⟩
      intro w hw
      simpa using hPx.1 w hw
  exact key

private theorem ggQ2xCN_leaf_not_normalizer_abstract (D : GGQ2Lin 3)
    (b : D.ι) (hne : b ≠ D.a)
    (hab : D.cartan D.a b = -1) (hba : D.cartan b D.a = -1)
    {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    (toW : W →ₗ[ZMod 3] D.V) (htoW : Function.Injective toW)
    (hb dW : W) (htob : toW hb = D.coroot b) (htod : toW dW = D.coroot D.a)
    (act : ggQ2xCN_Lam D → W → W)
    (hact : ∀ k w, toW (act k w) = D.simpleRefl k.1 (toW w))
    (I : Set W) (hI : ∀ k w, w ∈ I → act k w ∈ I) (hbI : hb ∈ I) (hdI : dW ∉ I) :
    D.simpleRefl D.a ∉
      Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)) := by
  intro hN
  set g : D.V ≃ₗ[ZMod 3] D.V := D.simpleRefl b * D.simpleRefl D.a with hg
  have hrb : D.simpleRefl b ∈ D.parab {k | k ≠ D.a} := by
    rw [GGQ2Lin.parab]
    exact Subgroup.subset_closure ⟨b, by simpa [ne_comm] using hne, rfl⟩
  have hgN : g ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)) := by
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hrb) hN
  have hra : D.simpleRefl D.a ∈ D.parab {k | k ≠ D.a} := by
    have hconj : g * D.simpleRefl b * g⁻¹ = D.simpleRefl D.a := by
      rw [hg]
      exact ggQ2xCN_conj_refl D b hab hba
    have hmem : g * D.simpleRefl b * g⁻¹ ∈ D.parab {k | k ≠ D.a} :=
      (Subgroup.mem_normalizer_iff.mp hgN (D.simpleRefl b)).mp hrb
    rwa [hconj] at hmem
  have hgW : g ∈ D.parab {k | k ≠ D.a} := by
    rw [hg]
    exact Subgroup.mul_mem _ hrb hra
  have horb := (ggQ2xCN_parab_stable D toW act hact I hI g hgW).1 hb hbI
  obtain ⟨u, huI, hu⟩ := horb
  have hto : toW u = toW dW := by
    rw [← hu, hg, show (D.simpleRefl b * D.simpleRefl D.a) (toW hb) =
      D.coroot D.a from by rw [htob]; exact ggQ2xCN_mul_refl_coroot D b hab hba, htod]
  exact hdI ((htoW hto) ▸ huI)

private noncomputable def ggQ2xCN_dvec (D : GGQ2Lin 3) (c : D.ι → ZMod 3) :
    ggQ2xCN_Lam D → ZMod 3 :=
  fun k => -(c k.1 / c D.a)

private theorem ggQ2xCN_toU_dvec (D : GGQ2Lin 3) (c : D.ι → ZMod 3)
    (hrel : ∑ k, c k • D.coroot k = 0) (hca : c D.a ≠ 0) :
    ggQ2xCN_toU D (ggQ2xCN_dvec D c) = D.coroot D.a := by
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun k => c k • D.coroot k) D.a] at hrel
  have hsum : ∑ i : ggQ2xCN_Lam D, c i.1 • D.coroot i.1 = -(c D.a • D.coroot D.a) :=
    (eq_neg_iff_add_eq_zero).mpr (by rw [add_comm]; exact hrel)
  have h1 : ggQ2xCN_toU D (fun i : ggQ2xCN_Lam D => c i.1) = -(c D.a • D.coroot D.a) := by
    rw [ggQ2xCN_toU_apply]; exact hsum
  have hd : ggQ2xCN_dvec D c = -(c D.a)⁻¹ • (fun i : ggQ2xCN_Lam D => c i.1) := by
    funext i
    rw [ggQ2xCN_dvec, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hd, map_smul, h1, ← neg_smul, smul_smul, neg_mul_neg, inv_mul_cancel₀ hca, one_smul]

private def ggQ2xCNa_pos (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    (k : ggQ2xCN_Lam D) : ℕ :=
  (e.symm k.1).val

private theorem ggQ2xCNa_pos_inj (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    {k j : ggQ2xCN_Lam D} (h : ggQ2xCNa_pos D e k = ggQ2xCNa_pos D e j) : k = j := by
  apply Subtype.ext
  have h2 : e (e.symm k.1) = e (e.symm j.1) := congrArg e (Fin.ext h)
  simpa using h2

private theorem ggQ2xCNa_pos_bounds (D : GGQ2Lin 3) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (ha : D.a = e ⟨0, by omega⟩) (k : ggQ2xCN_Lam D) :
    1 ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k < m := by
  refine ⟨?_, (e.symm k.1).isLt⟩
  by_contra h
  push_neg at h
  have h0 : (e.symm k.1).val = 0 := by
    have : ggQ2xCNa_pos D e k = 0 := by omega
    simpa only [ggQ2xCNa_pos] using this
  have hm0 : 0 < m := by omega
  have hf : e.symm k.1 = ⟨0, hm0⟩ := Fin.ext h0
  have hk : k.1 = D.a := by
    rw [← Equiv.apply_symm_apply e k.1, hf, ha]
  exact k.2 hk

private theorem ggQ2xCNa_exists_pos (D : GGQ2Lin 3) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (ha : D.a = e ⟨0, by omega⟩) {r : ℕ} (hr1 : 1 ≤ r) (hrm : r < m) :
    ∃ k : ggQ2xCN_Lam D, ggQ2xCNa_pos D e k = r := by
  refine ⟨⟨e ⟨r, hrm⟩, ?_⟩, ?_⟩
  · intro h
    have h2 : e ⟨r, hrm⟩ = e ⟨0, by omega⟩ := by rw [← ha]; exact h
    have h3 : r = 0 := by simpa using congrArg Fin.val (e.injective h2)
    omega
  · simp only [ggQ2xCNa_pos, Equiv.symm_apply_apply, Fin.val_mk]

private theorem ggQ2xCNa_coxeter (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A m).reindex e) (k j : ggQ2xCN_Lam D) :
    D.coxeter k.1 j.1 =
      (if ggQ2xCNa_pos D e k = ggQ2xCNa_pos D e j then 1
        else if ggQ2xCNa_pos D e k + 1 = ggQ2xCNa_pos D e j ∨
          ggQ2xCNa_pos D e j + 1 = ggQ2xCNa_pos D e k then 3 else 2) := by
  rw [hA, CoxeterMatrix.reindex_apply, ggQ2_A_label]
  exact if_congr (by rw [Fin.ext_iff]; rfl) rfl (by rfl)

private theorem ggQ2xCNa_cartan (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A m).reindex e) (k j : ggQ2xCN_Lam D) :
    D.cartan k.1 j.1 =
      (if ggQ2xCNa_pos D e k = ggQ2xCNa_pos D e j then 2
        else if ggQ2xCNa_pos D e k + 1 = ggQ2xCNa_pos D e j ∨
          ggQ2xCNa_pos D e j + 1 = ggQ2xCNa_pos D e k then -1 else 0) := by
  by_cases hkj : k = j
  · subst hkj
    rw [if_pos rfl, D.isCartan.1]
  · have hne : k.1 ≠ j.1 := fun h => hkj (Subtype.ext h)
    have hpos : ¬ (ggQ2xCNa_pos D e k = ggQ2xCNa_pos D e j) :=
      fun h => hkj (ggQ2xCNa_pos_inj D e h)
    rw [if_neg hpos]
    have hlab := ggQ2xCNa_coxeter D e hA k j
    rcases D.isCartan.2 k.1 j.1 hne with ⟨hl, h1, -⟩ | ⟨hl, h1, -⟩ | ⟨hl, -, -⟩ | ⟨hl, -, -⟩
    · have hna : ¬ (ggQ2xCNa_pos D e k + 1 = ggQ2xCNa_pos D e j ∨
          ggQ2xCNa_pos D e j + 1 = ggQ2xCNa_pos D e k) := by
        intro hcon
        rw [hlab, if_neg hpos, if_pos hcon] at hl
        omega
      rw [if_neg hna, h1]
    · have hadj : (ggQ2xCNa_pos D e k + 1 = ggQ2xCNa_pos D e j ∨
          ggQ2xCNa_pos D e j + 1 = ggQ2xCNa_pos D e k) := by
        by_contra hcon
        rw [hlab, if_neg hpos, if_neg hcon] at hl
        omega
      rw [if_pos hadj, h1]
    · exfalso
      rw [hlab] at hl
      split_ifs at hl <;> omega
    · exfalso
      rw [hlab] at hl
      split_ifs at hl <;> omega

private def ggQ2xCNa_ind (s : ZMod 3) (i j : ℕ) : ℕ → ZMod 3 :=
  fun r => s * (if i ≤ r ∧ r ≤ j then 1 else 0)

private theorem ggQ2xCNa_ind_zero (s : ZMod 3) (i j : ℕ) (hi : 1 ≤ i) :
    ggQ2xCNa_ind s i j 0 = 0 := by
  simp only [ggQ2xCNa_ind]
  rw [if_neg (by omega : ¬ (i ≤ 0 ∧ 0 ≤ j)), mul_zero]

private theorem ggQ2xCNa_ind_m (s : ZMod 3) (i j m : ℕ) (hj : j < m) :
    ggQ2xCNa_ind s i j m = 0 := by
  simp only [ggQ2xCNa_ind]
  rw [if_neg (by omega : ¬ (i ≤ m ∧ m ≤ j)), mul_zero]

private theorem ggQ2xCNa_sum_cartan (D : GGQ2Lin 3) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hA : D.coxeter = (CoxeterMatrix.A m).reindex e)
    (ha : D.a = e ⟨0, by omega⟩) (k : ggQ2xCN_Lam D)
    (g : ℕ → ZMod 3) (hg0 : g 0 = 0) (hgm : g m = 0) :
    (∑ j' : ggQ2xCN_Lam D, (D.cartan k.1 j'.1 : ZMod 3) * g (ggQ2xCNa_pos D e j'))
      = 2 * g (ggQ2xCNa_pos D e k) - g (ggQ2xCNa_pos D e k - 1)
        - g (ggQ2xCNa_pos D e k + 1) := by
  obtain ⟨hp1, hpm⟩ := ggQ2xCNa_pos_bounds D hm e ha k
  have hpoint : ∀ j' : ggQ2xCN_Lam D,
      (D.cartan k.1 j'.1 : ZMod 3) * g (ggQ2xCNa_pos D e j')
        = 2 * (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k
            then g (ggQ2xCNa_pos D e k) else 0)
          - (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k - 1
            then g (ggQ2xCNa_pos D e k - 1) else 0)
          - (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k + 1
            then g (ggQ2xCNa_pos D e k + 1) else 0) := by
    intro j'
    rw [ggQ2xCNa_cartan D e hA k j']
    by_cases heq : ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k
    · rw [if_pos heq.symm, heq, if_pos rfl,
        if_neg (by omega : ¬ (ggQ2xCNa_pos D e k = ggQ2xCNa_pos D e k - 1)),
        if_neg (by omega : ¬ (ggQ2xCNa_pos D e k = ggQ2xCNa_pos D e k + 1))]
      ring
    · rw [if_neg (fun h => heq h.symm)]
      by_cases hpre : ggQ2xCNa_pos D e j' + 1 = ggQ2xCNa_pos D e k
      · rw [if_pos (Or.inr hpre),
          show ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k - 1 by omega,
          if_pos rfl,
          if_neg (by omega : ¬ (ggQ2xCNa_pos D e k - 1 = ggQ2xCNa_pos D e k)),
          if_neg (by omega : ¬ (ggQ2xCNa_pos D e k - 1 = ggQ2xCNa_pos D e k + 1))]
        ring
      · by_cases hsuc : ggQ2xCNa_pos D e k + 1 = ggQ2xCNa_pos D e j'
        · rw [if_pos (Or.inl hsuc),
            show ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k + 1 by omega,
            if_neg (by omega : ¬ (ggQ2xCNa_pos D e k + 1 = ggQ2xCNa_pos D e k)),
            if_neg (by omega : ¬ (ggQ2xCNa_pos D e k + 1 = ggQ2xCNa_pos D e k - 1)),
            if_pos rfl]
          ring
        · rw [if_neg (fun hc => hc.elim hsuc hpre), if_neg heq,
            if_neg (by omega : ¬ (ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k - 1)),
            if_neg (by omega : ¬ (ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k + 1))]
          ring
  have hSp : (∑ j' : ggQ2xCN_Lam D,
      (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k then g (ggQ2xCNa_pos D e k) else 0))
      = g (ggQ2xCNa_pos D e k) := by
    rw [Fintype.sum_ite_eq_ite_exists
      (fun j' : ggQ2xCN_Lam D => ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k)
      (fun a b ha hb => ggQ2xCNa_pos_inj D e (ha.trans hb.symm)) (g (ggQ2xCNa_pos D e k))]
    rw [if_pos ⟨k, rfl⟩]
  have hSpred : (∑ j' : ggQ2xCN_Lam D,
      (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k - 1
        then g (ggQ2xCNa_pos D e k - 1) else 0))
      = g (ggQ2xCNa_pos D e k - 1) := by
    rw [Fintype.sum_ite_eq_ite_exists
      (fun j' : ggQ2xCN_Lam D => ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k - 1)
      (fun a b ha hb => ggQ2xCNa_pos_inj D e (ha.trans hb.symm))
      (g (ggQ2xCNa_pos D e k - 1))]
    by_cases hex : ∃ j' : ggQ2xCN_Lam D, ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k - 1
    · rw [if_pos hex]
    · rw [if_neg hex]
      have hr : ggQ2xCNa_pos D e k - 1 = 0 := by
        by_contra hne
        obtain ⟨j', hj'⟩ := ggQ2xCNa_exists_pos D hm e ha (r := ggQ2xCNa_pos D e k - 1)
          (by omega) (by omega)
        exact hex ⟨j', hj'⟩
      rw [hr, hg0]
  have hSsucc : (∑ j' : ggQ2xCN_Lam D,
      (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k + 1
        then g (ggQ2xCNa_pos D e k + 1) else 0))
      = g (ggQ2xCNa_pos D e k + 1) := by
    rw [Fintype.sum_ite_eq_ite_exists
      (fun j' : ggQ2xCN_Lam D => ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k + 1)
      (fun a b ha hb => ggQ2xCNa_pos_inj D e (ha.trans hb.symm))
      (g (ggQ2xCNa_pos D e k + 1))]
    by_cases hex : ∃ j' : ggQ2xCN_Lam D, ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k + 1
    · rw [if_pos hex]
    · rw [if_neg hex]
      have hr : ggQ2xCNa_pos D e k + 1 = m := by
        by_contra hne
        obtain ⟨j', hj'⟩ := ggQ2xCNa_exists_pos D hm e ha (r := ggQ2xCNa_pos D e k + 1)
          (by omega) (by omega)
        exact hex ⟨j', hj'⟩
      rw [hr, hgm]
  calc (∑ j' : ggQ2xCN_Lam D, (D.cartan k.1 j'.1 : ZMod 3) * g (ggQ2xCNa_pos D e j'))
      = ∑ j' : ggQ2xCN_Lam D,
          (2 * (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k
              then g (ggQ2xCNa_pos D e k) else 0)
            - (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k - 1
              then g (ggQ2xCNa_pos D e k - 1) else 0)
            - (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k + 1
              then g (ggQ2xCNa_pos D e k + 1) else 0)) :=
        Finset.sum_congr rfl (fun j' _ => hpoint j')
    _ = 2 * (∑ j' : ggQ2xCN_Lam D,
            (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k
              then g (ggQ2xCNa_pos D e k) else 0))
          - (∑ j' : ggQ2xCN_Lam D,
            (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k - 1
              then g (ggQ2xCNa_pos D e k - 1) else 0))
          - (∑ j' : ggQ2xCN_Lam D,
            (if ggQ2xCNa_pos D e j' = ggQ2xCNa_pos D e k + 1
              then g (ggQ2xCNa_pos D e k + 1) else 0)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 2 * g (ggQ2xCNa_pos D e k) - g (ggQ2xCNa_pos D e k - 1)
          - g (ggQ2xCNa_pos D e k + 1) := by rw [hSp, hSpred, hSsucc]

private theorem ggQ2xCNa_coxeter_a (D : GGQ2Lin 3) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hA : D.coxeter = (CoxeterMatrix.A m).reindex e)
    (ha : D.a = e ⟨0, by omega⟩) (i : Fin m) :
    D.coxeter D.a (e i) =
      (if i = ⟨0, by omega⟩ then 1 else if (i : ℕ) = 1 then 3 else 2) := by
  have h := ggQ2_A_label m (⟨0, by omega⟩ : Fin m) i
  rw [hA, CoxeterMatrix.reindex_apply, ha, Equiv.symm_apply_apply, Equiv.symm_apply_apply, h]
  by_cases hi : i = ⟨0, by omega⟩
  · rw [hi]
    simp
  · rw [if_neg (fun hc => hi hc.symm), if_neg hi]
    simp only [Fin.val_mk, zero_add]
    by_cases hi1 : (i : ℕ) = 1
    · rw [if_pos (Or.inl (by omega)), if_pos hi1]
    · rw [if_neg (fun hc => hc.elim (by omega) (by omega)), if_neg hi1]

private theorem ggQ2xCNa_cartan_a (D : GGQ2Lin 3) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hA : D.coxeter = (CoxeterMatrix.A m).reindex e)
    (ha : D.a = e ⟨0, by omega⟩) (b : ggQ2xCN_Lam D) (hb : D.cartan D.a b.1 ≠ 0) :
    ggQ2xCNa_pos D e b = 1 := by
  have hb0 : e.symm b.1 ≠ (⟨0, by omega⟩ : Fin m) := by
    intro hh
    have : b.1 = D.a := by rw [← Equiv.apply_symm_apply e b.1, hh, ha]
    exact b.2 this
  have hlab := ggQ2xCNa_coxeter_a D hm e hA ha (e.symm b.1)
  rw [Equiv.apply_symm_apply, if_neg hb0] at hlab
  have hneab : D.a ≠ b.1 := fun h => b.2 h.symm
  rcases D.isCartan.2 D.a b.1 hneab with ⟨hl, h1, -⟩ | ⟨hl, h1, -⟩ | ⟨hl, -, -⟩ | ⟨hl, -, -⟩
  · exact absurd h1 hb
  · by_contra hne1
    rw [hlab, if_neg (by simpa only [ggQ2xCNa_pos] using hne1)] at hl
    omega
  · rw [hlab] at hl
    split_ifs at hl <;> omega
  · rw [hlab] at hl
    split_ifs at hl <;> omega

private theorem ggQ2xCN_stable_A (D : GGQ2Lin 3) {m : ℕ} (hm : 5 ≤ m) (e : Fin m ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A m).reindex e) (ha : D.a = e ⟨0, by omega⟩)
    (c : D.ι → ZMod 3) (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (hca : c D.a ≠ 0) :
    ∃ I : Set (ggQ2xCN_Lam D → ZMod 3),
      (∀ (k : ggQ2xCN_Lam D) (w : ggQ2xCN_Lam D → ZMod 3), w ∈ I → ggQ2xCN_refAct D k w ∈ I) ∧
      (∀ b : ggQ2xCN_Lam D, D.cartan D.a b.1 ≠ 0 → Pi.single b (1 : ZMod 3) ∈ I) ∧
      ggQ2xCN_dvec D c ∉ I := by
  refine ⟨{w | ∃ s : ZMod 3, (s = 1 ∨ s = -1) ∧
      ∃ i j : ℕ, 1 ≤ i ∧ i ≤ j ∧ j < m ∧
        ∀ k, w k = if i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j then s else 0},
    ?_, ?_, ?_⟩
  · rintro k w ⟨s, hs, i, j, hi, hij, hj, hw⟩
    obtain ⟨hp1, hpm⟩ := ggQ2xCNa_pos_bounds D hm e ha k
    have hsum : (∑ j' : ggQ2xCN_Lam D, (D.cartan k.1 j'.1 : ZMod 3) * w j')
        = 2 * (if i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j then s else 0)
          - (if i ≤ ggQ2xCNa_pos D e k - 1 ∧ ggQ2xCNa_pos D e k - 1 ≤ j then s else 0)
          - (if i ≤ ggQ2xCNa_pos D e k + 1 ∧ ggQ2xCNa_pos D e k + 1 ≤ j then s else 0) := by
      have hT := ggQ2xCNa_sum_cartan D hm e hA ha k (ggQ2xCNa_ind s i j)
        (ggQ2xCNa_ind_zero s i j hi) (ggQ2xCNa_ind_m s i j m hj)
      have hcongr : (∑ j' : ggQ2xCN_Lam D, (D.cartan k.1 j'.1 : ZMod 3) * w j')
          = ∑ j' : ggQ2xCN_Lam D,
              (D.cartan k.1 j'.1 : ZMod 3) * ggQ2xCNa_ind s i j (ggQ2xCNa_pos D e j') := by
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [hw j']
        simp only [ggQ2xCNa_ind]
        by_cases hmem : i ≤ ggQ2xCNa_pos D e j' ∧ ggQ2xCNa_pos D e j' ≤ j
        · rw [if_pos hmem, if_pos hmem]; ring
        · rw [if_neg hmem, if_neg hmem]; ring
      rw [hcongr, hT]
      simp only [ggQ2xCNa_ind, mul_ite, mul_one, mul_zero]
    have hcoord : ∀ k' : ggQ2xCN_Lam D,
        ggQ2xCN_refAct D k w k'
          = if k' = k then w k' - (∑ j', (D.cartan k.1 j'.1 : ZMod 3) * w j') else w k' := by
      intro k'
      rw [ggQ2xCN_refAct_apply, Pi.sub_apply, Pi.smul_apply]
      by_cases hk' : k' = k
      · subst hk'
        rw [if_pos rfl, Pi.single_eq_same, smul_eq_mul, mul_one]
      · rw [if_neg hk', Pi.single_eq_of_ne hk', smul_zero, sub_zero]
    by_cases h1 : ggQ2xCNa_pos D e k < i
    · by_cases h1a : ggQ2xCNa_pos D e k + 1 = i
      · refine ⟨s, hs, i - 1, j, by omega, by omega, hj, ?_⟩
        intro k'
        rw [hcoord k']
        by_cases hk' : k' = k
        · rw [if_pos hk', hk', hw k, hsum,
            if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j)),
            if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k - 1 ∧ ggQ2xCNa_pos D e k - 1 ≤ j)),
            if_pos (by omega : i ≤ ggQ2xCNa_pos D e k + 1 ∧ ggQ2xCNa_pos D e k + 1 ≤ j),
            if_pos (by omega : i - 1 ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j)]
          ring
        · rw [if_neg hk', hw k']
          have hne : ggQ2xCNa_pos D e k' ≠ ggQ2xCNa_pos D e k :=
            fun h => hk' (ggQ2xCNa_pos_inj D e h)
          have hiff : (i ≤ ggQ2xCNa_pos D e k' ∧ ggQ2xCNa_pos D e k' ≤ j) ↔
              (i - 1 ≤ ggQ2xCNa_pos D e k' ∧ ggQ2xCNa_pos D e k' ≤ j) := by
            constructor
            · intro hc; exact ⟨by omega, hc.2⟩
            · intro hc; exact ⟨by omega, hc.2⟩
          rw [if_congr hiff rfl rfl]
      · refine ⟨s, hs, i, j, hi, hij, hj, ?_⟩
        intro k'
        rw [hcoord k']
        by_cases hk' : k' = k
        · rw [if_pos hk', hk', hw k, hsum,
            if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j)),
            if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k - 1 ∧ ggQ2xCNa_pos D e k - 1 ≤ j)),
            if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k + 1 ∧ ggQ2xCNa_pos D e k + 1 ≤ j))]
          ring
        · rw [if_neg hk', hw k']
    · by_cases h2 : ggQ2xCNa_pos D e k ≤ j
      · by_cases h2a : ggQ2xCNa_pos D e k = i
        · by_cases h2b : ggQ2xCNa_pos D e k = j
          · have hs' : (-s : ZMod 3) = 1 ∨ -s = -1 := by
              rcases hs with hs1 | hs1
              · rw [hs1]; right; ring
              · rw [hs1]; left; ring
            refine ⟨-s, hs', i, i, hi, le_rfl, by omega, ?_⟩
            intro k'
            rw [hcoord k']
            by_cases hk' : k' = k
            · rw [if_pos hk', hk', hw k, hsum,
                if_pos (by omega : i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j),
                if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k - 1 ∧ ggQ2xCNa_pos D e k - 1 ≤ j)),
                if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k + 1 ∧ ggQ2xCNa_pos D e k + 1 ≤ j)),
                if_pos (by omega : i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ i)]
              ring
            · rw [if_neg hk', hw k']
              have hne : ggQ2xCNa_pos D e k' ≠ ggQ2xCNa_pos D e k :=
                fun h => hk' (ggQ2xCNa_pos_inj D e h)
              have hf1 : ¬ (i ≤ ggQ2xCNa_pos D e k' ∧ ggQ2xCNa_pos D e k' ≤ j) := by
                intro hc; exact hne (by omega)
              have hf2 : ¬ (i ≤ ggQ2xCNa_pos D e k' ∧ ggQ2xCNa_pos D e k' ≤ i) := by
                intro hc; exact hne (by omega)
              rw [if_neg hf1, if_neg hf2]
          · refine ⟨s, hs, i + 1, j, by omega, by omega, hj, ?_⟩
            intro k'
            rw [hcoord k']
            by_cases hk' : k' = k
            · rw [if_pos hk', hk', hw k, hsum,
                if_pos (by omega : i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j),
                if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k - 1 ∧ ggQ2xCNa_pos D e k - 1 ≤ j)),
                if_pos (by omega : i ≤ ggQ2xCNa_pos D e k + 1 ∧ ggQ2xCNa_pos D e k + 1 ≤ j),
                if_neg (by omega : ¬ (i + 1 ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j))]
              ring
            · rw [if_neg hk', hw k']
              have hne : ggQ2xCNa_pos D e k' ≠ ggQ2xCNa_pos D e k :=
                fun h => hk' (ggQ2xCNa_pos_inj D e h)
              have hiff : (i ≤ ggQ2xCNa_pos D e k' ∧ ggQ2xCNa_pos D e k' ≤ j) ↔
                  (i + 1 ≤ ggQ2xCNa_pos D e k' ∧ ggQ2xCNa_pos D e k' ≤ j) := by
                constructor
                · intro hc; exact ⟨by omega, hc.2⟩
                · intro hc; exact ⟨by omega, hc.2⟩
              rw [if_congr hiff rfl rfl]
        · by_cases h2b : ggQ2xCNa_pos D e k = j
          · refine ⟨s, hs, i, j - 1, hi, by omega, by omega, ?_⟩
            intro k'
            rw [hcoord k']
            by_cases hk' : k' = k
            · rw [if_pos hk', hk', hw k, hsum,
                if_pos (by omega : i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j),
                if_pos (by omega : i ≤ ggQ2xCNa_pos D e k - 1 ∧ ggQ2xCNa_pos D e k - 1 ≤ j),
                if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k + 1 ∧ ggQ2xCNa_pos D e k + 1 ≤ j)),
                if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j - 1))]
              ring
            · rw [if_neg hk', hw k']
              have hne : ggQ2xCNa_pos D e k' ≠ ggQ2xCNa_pos D e k :=
                fun h => hk' (ggQ2xCNa_pos_inj D e h)
              have hiff : (i ≤ ggQ2xCNa_pos D e k' ∧ ggQ2xCNa_pos D e k' ≤ j) ↔
                  (i ≤ ggQ2xCNa_pos D e k' ∧ ggQ2xCNa_pos D e k' ≤ j - 1) := by
                constructor
                · intro hc; exact ⟨hc.1, by omega⟩
                · intro hc; exact ⟨hc.1, by omega⟩
              rw [if_congr hiff rfl rfl]
          · refine ⟨s, hs, i, j, hi, hij, hj, ?_⟩
            intro k'
            rw [hcoord k']
            by_cases hk' : k' = k
            · rw [if_pos hk', hk', hw k, hsum,
                if_pos (by omega : i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j),
                if_pos (by omega : i ≤ ggQ2xCNa_pos D e k - 1 ∧ ggQ2xCNa_pos D e k - 1 ≤ j),
                if_pos (by omega : i ≤ ggQ2xCNa_pos D e k + 1 ∧ ggQ2xCNa_pos D e k + 1 ≤ j)]
              ring
            · rw [if_neg hk', hw k']
      · by_cases h3 : ggQ2xCNa_pos D e k - 1 = j
        · refine ⟨s, hs, i, j + 1, hi, by omega, by omega, ?_⟩
          intro k'
          rw [hcoord k']
          by_cases hk' : k' = k
          · rw [if_pos hk', hk', hw k, hsum,
              if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j)),
              if_pos (by omega : i ≤ ggQ2xCNa_pos D e k - 1 ∧ ggQ2xCNa_pos D e k - 1 ≤ j),
              if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k + 1 ∧ ggQ2xCNa_pos D e k + 1 ≤ j)),
              if_pos (by omega : i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j + 1)]
            ring
          · rw [if_neg hk', hw k']
            have hne : ggQ2xCNa_pos D e k' ≠ ggQ2xCNa_pos D e k :=
              fun h => hk' (ggQ2xCNa_pos_inj D e h)
            have hiff : (i ≤ ggQ2xCNa_pos D e k' ∧ ggQ2xCNa_pos D e k' ≤ j) ↔
                (i ≤ ggQ2xCNa_pos D e k' ∧ ggQ2xCNa_pos D e k' ≤ j + 1) := by
              constructor
              · intro hc; exact ⟨hc.1, by omega⟩
              · intro hc; exact ⟨hc.1, by omega⟩
            rw [if_congr hiff rfl rfl]
        · refine ⟨s, hs, i, j, hi, hij, hj, ?_⟩
          intro k'
          rw [hcoord k']
          by_cases hk' : k' = k
          · rw [if_pos hk', hk', hw k, hsum,
              if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k ∧ ggQ2xCNa_pos D e k ≤ j)),
              if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k - 1 ∧ ggQ2xCNa_pos D e k - 1 ≤ j)),
              if_neg (by omega : ¬ (i ≤ ggQ2xCNa_pos D e k + 1 ∧ ggQ2xCNa_pos D e k + 1 ≤ j))]
            ring
          · rw [if_neg hk', hw k']
  · intro b hb
    have hpb : ggQ2xCNa_pos D e b = 1 := ggQ2xCNa_cartan_a D hm e hA ha b hb
    refine ⟨1, Or.inl rfl, 1, 1, le_rfl, le_rfl, by omega, ?_⟩
    intro k
    by_cases hk : k = b
    · subst hk
      rw [Pi.single_eq_same, if_pos (by omega)]
    · rw [Pi.single_eq_of_ne hk,
        if_neg (fun hc => hk (ggQ2xCNa_pos_inj D e ((le_antisymm hc.2 hc.1).trans hpb.symm)))]
  · rintro ⟨s, hs, i, j, hi, hij, hj, hw⟩
    have hkey : ∀ k : ggQ2xCN_Lam D,
        ggQ2xCN_dvec D c k = -(((ggQ2xCNa_pos D e k + 1 : ℕ)) : ZMod 3) := by
      intro k
      have hk := ggQ2_caseII_kernel_A D e hA c hc (e.symm k.1)
      rw [Equiv.apply_symm_apply] at hk
      have hfin : e ⟨0, Fin.pos (e.symm k.1)⟩ = D.a :=
        (congrArg e (Fin.ext rfl)).trans ha.symm
      simp only [ggQ2xCN_dvec]
      rw [hk, hfin, mul_div_assoc, div_self hca, mul_one]
      simp only [ggQ2xCNa_pos]
    obtain ⟨k1, hk1⟩ := ggQ2xCNa_exists_pos D hm e ha (r := 1) (by omega) (by omega)
    obtain ⟨k3, hk3⟩ := ggQ2xCNa_exists_pos D hm e ha (r := 3) (by omega) (by omega)
    have hk1v : ggQ2xCN_dvec D c k1 = 1 := by
      rw [hkey k1, hk1]
      decide
    have hk3v : ggQ2xCN_dvec D c k3 = 2 := by
      rw [hkey k3, hk3]
      decide
    have hs1 : s = 1 := by
      have h := hw k1
      rw [hk1v] at h
      by_cases hc1 : i ≤ ggQ2xCNa_pos D e k1 ∧ ggQ2xCNa_pos D e k1 ≤ j
      · rw [if_pos hc1] at h
        exact h.symm
      · rw [if_neg hc1] at h
        exact absurd h (by decide : ¬ ((1 : ZMod 3) = 0))
    have hs2 : s = 2 := by
      have h := hw k3
      rw [hk3v] at h
      by_cases hc3 : i ≤ ggQ2xCNa_pos D e k3 ∧ ggQ2xCNa_pos D e k3 ≤ j
      · rw [if_pos hc3] at h
        exact h.symm
      · rw [if_neg hc3] at h
        exact absurd h (by decide : ¬ ((2 : ZMod 3) = 0))
    rw [hs2] at hs1
    exact (by decide : ¬ ((2 : ZMod 3) = 1)) hs1

private theorem ggQ2xCNe_cartan_of_labels (D : GGQ2Lin 3) {Γ : Type} [Fintype Γ] [DecidableEq Γ]
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

private theorem ggQ2xCNe_cartan_E6 (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (i j : Fin 6) :
    D.cartan (e i) (e j) = CartanMatrix.E 6 i j :=
  ggQ2xCNe_cartan_of_labels D e hE
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆])
    (CartanMatrix.E 6)
    (by intro i j hij h; fin_cases i <;> fin_cases j <;>
      simp_all [CoxeterMatrix.E₆, CartanMatrix.E])
    (by intro i j hij h; fin_cases i <;> fin_cases j <;>
      simp_all [CoxeterMatrix.E₆, CartanMatrix.E])
    (by intro i; fin_cases i <;> decide) i j

private noncomputable def ggQ2xCNe_node (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) (ha : D.a = e 0) :
    Fin 5 → ggQ2xCN_Lam D :=
  fun i => ⟨e (Fin.succ i),
    fun h => Fin.succ_ne_zero i (e.injective (by rw [h, ha]))⟩

private noncomputable def ggQ2xCNe_toFin (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) (ha : D.a = e 0) :
    ggQ2xCN_Lam D → Fin 5 :=
  fun k => ⟨(e.symm k.1).val - 1, by
    have hne : e.symm k.1 ≠ 0 := fun h =>
      k.2 (by rw [← Equiv.apply_symm_apply e k.1, h, ha])
    have hpos : (e.symm k.1).val ≠ 0 := fun h => hne (Fin.ext h)
    have hlt := (e.symm k.1).isLt
    omega⟩

private theorem ggQ2xCNe_node_injective (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) (ha : D.a = e 0) :
    Function.Injective (ggQ2xCNe_node D e ha) := by
  intro i j h
  have h1 : e (Fin.succ i) = e (Fin.succ j) := Subtype.ext_iff.mp h
  exact Fin.succ_inj.mp (e.injective h1)

private theorem ggQ2xCNe_node_toFin (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) (ha : D.a = e 0)
    (k : ggQ2xCN_Lam D) :
    ggQ2xCNe_node D e ha (ggQ2xCNe_toFin D e ha k) = k := by
  apply Subtype.ext
  show e (Fin.succ (ggQ2xCNe_toFin D e ha k)) = k.1
  rw [← Equiv.apply_symm_apply e k.1]
  congr 1
  apply Fin.ext
  show (ggQ2xCNe_toFin D e ha k).val + 1 = (e.symm k.1).val
  have hne : e.symm k.1 ≠ 0 := fun h =>
    k.2 (by rw [← Equiv.apply_symm_apply e k.1, h, ha])
  have hpos : (e.symm k.1).val ≠ 0 := fun h => hne (Fin.ext h)
  simp only [ggQ2xCNe_toFin]
  omega

private theorem ggQ2xCNe_toFin_node (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) (ha : D.a = e 0)
    (i : Fin 5) :
    ggQ2xCNe_toFin D e ha (ggQ2xCNe_node D e ha i) = i := by
  apply Fin.ext
  show (e.symm (e (Fin.succ i))).val - 1 = i.val
  rw [Equiv.symm_apply_apply]
  show (Fin.succ i).val - 1 = i.val
  rw [Fin.val_succ]
  omega

private noncomputable def ggQ2xCNe_nodeEquiv (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (ha : D.a = e 0) : Fin 5 ≃ ggQ2xCN_Lam D where
  toFun := ggQ2xCNe_node D e ha
  invFun := ggQ2xCNe_toFin D e ha
  left_inv := ggQ2xCNe_toFin_node D e ha
  right_inv := ggQ2xCNe_node_toFin D e ha

private theorem ggQ2xCNe_single_node (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) (ha : D.a = e 0)
    (i j : Fin 5) :
    Pi.single (M := fun _ : ggQ2xCN_Lam D => ZMod 3) (ggQ2xCNe_node D e ha i) 1
        (ggQ2xCNe_node D e ha j) =
      Pi.single (M := fun _ : Fin 5 => ZMod 3) i 1 j := by
  by_cases hji : j = i
  · subst hji
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · have hne : ggQ2xCNe_node D e ha j ≠ ggQ2xCNe_node D e ha i :=
      fun hh => hji (ggQ2xCNe_node_injective D e ha hh)
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hji]

private def ggQ2xCNe_C (i j : Fin 5) : ZMod 3 :=
  (CartanMatrix.E 6 (Fin.succ i) (Fin.succ j) : ZMod 3)

private def ggQ2xCNe_refl (i : Fin 5) (v : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 :=
  v - (∑ l, ggQ2xCNe_C i l * v l) • Pi.single i (1 : ZMod 3)

private def ggQ2xCNe_posL : List (Fin 5 → ZMod 3) :=
  [![0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0],
    ![0, 0, 0, 1, 1],
    ![0, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0],
    ![0, 0, 1, 1, 1],
    ![0, 1, 0, 0, 0],
    ![0, 1, 1, 0, 0],
    ![0, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1],
    ![1, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0],
    ![1, 0, 1, 1, 0],
    ![1, 0, 1, 1, 1],
    ![1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 0],
    ![1, 1, 1, 1, 1],
    ![1, 1, 2, 1, 0],
    ![1, 1, 2, 1, 1],
    ![1, 1, 2, 2, 1]]

private abbrev ggQ2xCNe_L : Set (Fin 5 → ZMod 3) :=
  {v | v ∈ ggQ2xCNe_posL ∨ -v ∈ ggQ2xCNe_posL}

private theorem ggQ2xCNe_L_stable : ∀ (i : Fin 5) (v : Fin 5 → ZMod 3),
    v ∈ ggQ2xCNe_L → ggQ2xCNe_refl i v ∈ ggQ2xCNe_L := by
  decide +kernel

private theorem ggQ2xCNe_dvec_not_mem :
    (![0, 1, 0, 2, 1] : Fin 5 → ZMod 3) ∉ ggQ2xCNe_L := by
  decide

private theorem ggQ2xCNe_sum_reindex (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (ha : D.a = e 0)
    (i : Fin 5) (w : ggQ2xCN_Lam D → ZMod 3) :
    (∑ l : ggQ2xCN_Lam D, (D.cartan (ggQ2xCNe_node D e ha i).1 l.1 : ZMod 3) * w l) =
      ∑ j : Fin 5, ggQ2xCNe_C i j * w (ggQ2xCNe_node D e ha j) := by
  rw [← Equiv.sum_comp (ggQ2xCNe_nodeEquiv D e ha)
    (fun l : ggQ2xCN_Lam D => (D.cartan (ggQ2xCNe_node D e ha i).1 l.1 : ZMod 3) * w l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (D.cartan (e (Fin.succ i)) (e (Fin.succ j)) : ZMod 3) *
      w (ggQ2xCNe_node D e ha j) = ggQ2xCNe_C i j * w (ggQ2xCNe_node D e ha j)
  rw [ggQ2xCNe_cartan_E6 D e hE (Fin.succ i) (Fin.succ j)]
  rfl

private theorem ggQ2xCNe_refAct_node (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (ha : D.a = e 0)
    (i : Fin 5) (w : ggQ2xCN_Lam D → ZMod 3) :
    (fun j => ggQ2xCN_refAct D (ggQ2xCNe_node D e ha i) w (ggQ2xCNe_node D e ha j)) =
      ggQ2xCNe_refl i (fun j => w (ggQ2xCNe_node D e ha j)) := by
  funext j
  rw [ggQ2xCN_refAct_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, ggQ2xCNe_sum_reindex D e hE ha i w,
    ggQ2xCNe_single_node D e ha i j, ggQ2xCNe_refl]

private theorem ggQ2xCNe_neighbour (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (ha : D.a = e 0)
    (b : ggQ2xCN_Lam D) (hb : D.cartan D.a b.1 ≠ 0) :
    b = ggQ2xCNe_node D e ha (1 : Fin 5) := by
  apply Subtype.ext
  have hne0 : e.symm b.1 ≠ 0 := fun h =>
    b.2 (by rw [← Equiv.apply_symm_apply e b.1, h, ha])
  have hrow : CartanMatrix.E 6 0 (e.symm b.1) ≠ 0 := by
    have h := ggQ2xCNe_cartan_E6 D e hE 0 (e.symm b.1)
    rw [Equiv.apply_symm_apply] at h
    rw [← h, ← ha]
    exact hb
  have h2 : e.symm b.1 = 2 := by
    generalize hk : (e.symm b.1 : Fin 6) = k
    fin_cases k <;> simp_all [CartanMatrix.E]
  show b.1 = e (Fin.succ (1 : Fin 5))
  rw [← Equiv.apply_symm_apply e b.1, h2]
  rfl

private theorem ggQ2xCNe_single_mem (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) (ha : D.a = e 0) :
    (fun j => Pi.single (M := fun _ : ggQ2xCN_Lam D => ZMod 3)
      (ggQ2xCNe_node D e ha (1 : Fin 5)) 1 (ggQ2xCNe_node D e ha j)) ∈ ggQ2xCNe_L := by
  have hfun : (fun j => Pi.single (M := fun _ : ggQ2xCN_Lam D => ZMod 3)
      (ggQ2xCNe_node D e ha (1 : Fin 5)) 1 (ggQ2xCNe_node D e ha j)) = ![0, 1, 0, 0, 0] := by
    funext j
    rw [ggQ2xCNe_single_node D e ha 1 j]
    fin_cases j <;> decide
  rw [hfun]
  decide

private theorem ggQ2xCNe_dvec_eq (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (ha : D.a = e 0)
    (c : D.ι → ZMod 3) (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0)
    (hca : c D.a ≠ 0) :
    (fun j => ggQ2xCN_dvec D c (ggQ2xCNe_node D e ha j)) = ![0, 1, 0, 2, 1] := by
  obtain ⟨hk1, hk3, hk2, hk4, hk5⟩ := ggQ2_caseII_kernel_E6 D e hE c hc
  have hca0 : c (e 0) ≠ 0 := by rwa [ha] at hca
  funext j
  fin_cases j
  · show -(c (e (Fin.succ (0 : Fin 5))) / c D.a) = (0 : ZMod 3)
    rw [Fin.succ_zero_eq_one, hk1, ha]
    simp
  · show -(c (e (Fin.succ (1 : Fin 5))) / c D.a) = (1 : ZMod 3)
    rw [show (Fin.succ (1 : Fin 5) : Fin 6) = 2 from rfl, hk2, ha,
      mul_div_assoc, div_self hca0, mul_one]
    decide
  · show -(c (e (Fin.succ (2 : Fin 5))) / c D.a) = (0 : ZMod 3)
    rw [show (Fin.succ (2 : Fin 5) : Fin 6) = 3 from rfl, hk3, ha]
    simp
  · show -(c (e (Fin.succ (3 : Fin 5))) / c D.a) = (2 : ZMod 3)
    rw [show (Fin.succ (3 : Fin 5) : Fin 6) = 4 from rfl, hk4, ha,
      div_self hca0]
    decide
  · show -(c (e (Fin.succ (4 : Fin 5))) / c D.a) = (1 : ZMod 3)
    rw [show (Fin.succ (4 : Fin 5) : Fin 6) = 5 from rfl, hk5, ha,
      mul_div_assoc, div_self hca0, mul_one]
    decide

private theorem ggQ2xCN_stable_E6 (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (ha : D.a = e 0)
    (c : D.ι → ZMod 3) (hc : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0) (hca : c D.a ≠ 0) :
    ∃ I : Set (ggQ2xCN_Lam D → ZMod 3),
      (∀ (k : ggQ2xCN_Lam D) (w : ggQ2xCN_Lam D → ZMod 3), w ∈ I → ggQ2xCN_refAct D k w ∈ I) ∧
      (∀ b : ggQ2xCN_Lam D, D.cartan D.a b.1 ≠ 0 → Pi.single b (1 : ZMod 3) ∈ I) ∧
      ggQ2xCN_dvec D c ∉ I := by
  refine ⟨{w | (fun j => w (ggQ2xCNe_node D e ha j)) ∈ ggQ2xCNe_L}, ?_, ?_, ?_⟩
  · intro k w hw
    obtain ⟨i, rfl⟩ := (ggQ2xCNe_nodeEquiv D e ha).surjective k
    show (fun j => ggQ2xCN_refAct D (ggQ2xCNe_node D e ha i) w
      (ggQ2xCNe_node D e ha j)) ∈ ggQ2xCNe_L
    rw [ggQ2xCNe_refAct_node D e hE ha i w]
    exact ggQ2xCNe_L_stable i _ hw
  · intro b hb
    rw [ggQ2xCNe_neighbour D e hE ha b hb]
    exact ggQ2xCNe_single_mem D e ha
  · intro hmem
    change (fun j => ggQ2xCN_dvec D c (ggQ2xCNe_node D e ha j)) ∈ ggQ2xCNe_L at hmem
    rw [ggQ2xCNe_dvec_eq D e hE ha c hc hca] at hmem
    exact ggQ2xCNe_dvec_not_mem hmem

private theorem ggQ2xCNm_coxeter_reindex (D : GGQ2Lin 3) {Γ : Type} [Fintype Γ]
    [DecidableEq Γ] (e : Γ ≃ D.ι) {M : CoxeterMatrix Γ}
    (hM : D.coxeter = M.reindex e) (i j : Γ) : D.coxeter (e i) (e j) = M i j := by
  rw [hM, CoxeterMatrix.reindex_apply]
  simp

private theorem ggQ2xCNm_cartan_of_label3 (D : GGQ2Lin 3) {i j : D.ι} (hij : i ≠ j)
    (h : D.coxeter i j = 3) : D.cartan i j = -1 := by
  rcases D.isCartan.2 i j hij with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, -, -, -⟩ |
    ⟨hm, -, -, -⟩
  · rw [h] at hm; omega
  · exact h1
  · rw [h] at hm; omega
  · rw [h] at hm; omega

private theorem ggQ2xCNm_A_label_adj {m : ℕ} (i j : Fin m) (h : (i : ℕ) + 1 = (j : ℕ)) :
    (CoxeterMatrix.A m) i j = 3 := by
  rw [ggQ2_A_label, if_neg (by intro hij; have := congrArg Fin.val hij; omega),
    if_pos (Or.inl h)]

private def ggQ2xCNm_E6swap : Fin 6 ≃ Fin 6 :=
  (Equiv.swap 0 5).trans (Equiv.swap 2 4)

private theorem ggQ2xCNm_E6swap_zero : ggQ2xCNm_E6swap 0 = 5 := by decide

private theorem ggQ2xCNm_E6swap_coxeter :
    CoxeterMatrix.E₆.reindex ggQ2xCNm_E6swap = CoxeterMatrix.E₆ := by
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  fin_cases i <;> fin_cases j <;> decide

private theorem ggQ2xCN_nonsplit_of_data (D : GGQ2Lin 3) (hII : D.CaseII)
    (c : D.ι → ZMod 3) (hrel : ∑ k, c k • D.coroot k = 0) (hca : c D.a ≠ 0)
    (b : D.ι) (hne : b ≠ D.a)
    (hab : D.cartan D.a b = -1) (hba : D.cartan b D.a = -1)
    (I : Set (ggQ2xCN_Lam D → ZMod 3))
    (hI : ∀ k w, w ∈ I → ggQ2xCN_refAct D k w ∈ I)
    (hbI : ∀ b' : ggQ2xCN_Lam D, D.cartan D.a b'.1 ≠ 0 → Pi.single b' (1 : ZMod 3) ∈ I)
    (hdI : ggQ2xCN_dvec D c ∉ I)
    (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ v : D.V, (∀ k, D.root k v = 0) → v = 0 := by
  intro v hv
  by_contra hvne
  have hfix : ∀ g ∈ D.parab {k | k ≠ D.a}, g v = v := by
    intro g hg
    have hg' : g ∈ Subgroup.closure (D.simpleRefl '' {k | k ≠ D.a}) := by
      simpa only [GGQ2Lin.parab] using hg
    refine Subgroup.closure_induction (p := fun x _ => x v = v) ?_ ?_ ?_ ?_ hg'
    · rintro x ⟨k, hk, rfl⟩
      rw [ggQ2xCN_simpleRefl_apply, hv k, zero_smul, sub_zero]
    · rfl
    · intro x y _ _ hx' hy'
      rw [LinearEquiv.mul_apply, hy', hx']
    · intro x _ hx'
      apply x.injective
      rw [hx']
      exact x.apply_symm_apply v
  have hvx : v ∈ Submodule.span (ZMod 3) {x} := (hx v).mp hfix
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hvx
  have ht0 : t ≠ 0 := by
    intro ht0
    exact hvne (by rw [← ht, ht0, zero_smul])
  have hxa : D.root D.a x = 0 := by
    have h0 : D.root D.a (t • x) = 0 := by rw [ht]; exact hv D.a
    rw [map_smul, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left ht0
  have hraA : D.simpleRefl D.a ∈ A :=
    hW (by rw [GGQ2Lin.weyl]; exact Subgroup.subset_closure ⟨D.a, Set.mem_univ _, rfl⟩)
  have hrax : D.simpleRefl D.a x ∈ Submodule.span (ZMod 3) {x} := by
    rw [ggQ2xCN_simpleRefl_apply, hxa, zero_smul, sub_zero]
    exact Submodule.subset_span (Set.mem_singleton x)
  exact (ggQ2xCN_leaf_not_normalizer_abstract D b hne hab hba
    (ggQ2xCN_toU D) (ggQ2xCN_toU_injective D hII)
    (Pi.single ⟨b, hne⟩ (1 : ZMod 3)) (ggQ2xCN_dvec D c)
    (by rw [ggQ2xCN_toU_single, one_smul]) (ggQ2xCN_toU_dvec D c hrel hca)
    (fun k w => ggQ2xCN_refAct D k w) (ggQ2xCN_toU_refAct D) I hI
    (hbI ⟨b, hne⟩ (by rw [hab]; norm_num)) hdI) (hHL _ hraA hrax)

theorem ggQ2_caseII_nonsplit (D : GGQ2Lin 3) (hII : D.CaseII) (h4 : 4 ≤ Fintype.card D.ι)
    (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ v : D.V, (∀ k, D.root k v = 0) → v = 0 := by
  obtain ⟨c, hrel, hca, hc⟩ := ggQ2_caseII_relation D hII
  have hsym := ggQ2_caseII_cartan_symm D hII h4
  rcases ggQ2_caseII_types D hII h4 with
      ⟨m, e, hm, _hmod, hA, ha | ha⟩ | ⟨e, hE, ha | ha⟩
  · obtain ⟨I, hI, hbI, hdI⟩ := ggQ2xCN_stable_A D hm e hA ha c hc hca
    have h0 : 0 < m := by omega
    have h1 : 1 < m := by omega
    have ha0 : D.a = e ⟨0, h0⟩ := by rw [ha]
    have hlab : D.coxeter (e ⟨0, h0⟩) (e ⟨1, h1⟩) = 3 := by
      rw [ggQ2xCNm_coxeter_reindex D e hA]
      exact ggQ2xCNm_A_label_adj _ _ (by simp)
    have hne : e ⟨1, h1⟩ ≠ D.a := by
      rw [ha0]
      exact fun h => by have h' := congrArg Fin.val (e.injective h); simp at h'
    have hab : D.cartan D.a (e ⟨1, h1⟩) = -1 := by
      rw [ha0]
      exact ggQ2xCNm_cartan_of_label3 D
        (fun h => by have h' := congrArg Fin.val (e.injective h); simp at h') hlab
    exact ggQ2xCN_nonsplit_of_data D hII c hrel hca (e ⟨1, h1⟩) hne hab
      (by rw [hsym]; exact hab) I hI hbI hdI x hx A hW hHL
  · obtain ⟨e', hA', ha'⟩ := ggQ2_A_leaf_reverse D (by omega : 1 ≤ m) e hA ha
    obtain ⟨I, hI, hbI, hdI⟩ := ggQ2xCN_stable_A D hm e' hA' ha' c hc hca
    have h0 : 0 < m := by omega
    have h1 : 1 < m := by omega
    have ha0 : D.a = e' ⟨0, h0⟩ := by rw [ha']
    have hlab : D.coxeter (e' ⟨0, h0⟩) (e' ⟨1, h1⟩) = 3 := by
      rw [ggQ2xCNm_coxeter_reindex D e' hA']
      exact ggQ2xCNm_A_label_adj _ _ (by simp)
    have hne : e' ⟨1, h1⟩ ≠ D.a := by
      rw [ha0]
      exact fun h => by have h' := congrArg Fin.val (e'.injective h); simp at h'
    have hab : D.cartan D.a (e' ⟨1, h1⟩) = -1 := by
      rw [ha0]
      exact ggQ2xCNm_cartan_of_label3 D
        (fun h => by have h' := congrArg Fin.val (e'.injective h); simp at h') hlab
    exact ggQ2xCN_nonsplit_of_data D hII c hrel hca (e' ⟨1, h1⟩) hne hab
      (by rw [hsym]; exact hab) I hI hbI hdI x hx A hW hHL
  · obtain ⟨I, hI, hbI, hdI⟩ := ggQ2xCN_stable_E6 D e hE ha c hc hca
    have hlab : D.coxeter (e 0) (e 2) = 3 := by
      rw [ggQ2xCNm_coxeter_reindex D e hE]; decide
    have hne : e 2 ≠ D.a := by
      rw [ha]
      exact fun h => by have h' := congrArg Fin.val (e.injective h); simp at h'
    have hab : D.cartan D.a (e 2) = -1 := by
      rw [ha]
      exact ggQ2xCNm_cartan_of_label3 D
        (fun h => by have h' := congrArg Fin.val (e.injective h); simp at h') hlab
    exact ggQ2xCN_nonsplit_of_data D hII c hrel hca (e 2) hne hab
      (by rw [hsym]; exact hab) I hI hbI hdI x hx A hW hHL
  · set e' : Fin 6 ≃ D.ι := ggQ2xCNm_E6swap.trans e with he'
    have hE' : D.coxeter = CoxeterMatrix.E₆.reindex e' := by
      rw [he', hE, ← ggQ2_reindex_trans CoxeterMatrix.E₆ ggQ2xCNm_E6swap e,
        ggQ2xCNm_E6swap_coxeter]
    have ha' : D.a = e' 0 := by
      rw [he', ha, Equiv.trans_apply, ggQ2xCNm_E6swap_zero]
    obtain ⟨I, hI, hbI, hdI⟩ := ggQ2xCN_stable_E6 D e' hE' ha' c hc hca
    have hlab : D.coxeter (e' 0) (e' 2) = 3 := by
      rw [ggQ2xCNm_coxeter_reindex D e' hE']; decide
    have hne : e' 2 ≠ D.a := by
      rw [ha']
      exact fun h => by have h' := congrArg Fin.val (e'.injective h); simp at h'
    have hab : D.cartan D.a (e' 2) = -1 := by
      rw [ha']
      exact ggQ2xCNm_cartan_of_label3 D
        (fun h => by have h' := congrArg Fin.val (e'.injective h); simp at h') hlab
    exact ggQ2xCN_nonsplit_of_data D hII c hrel hca (e' 2) hne hab
      (by rw [hsym]; exact hab) I hI hbI hdI x hx A hW hHL

end CFSG.StandardType

end
