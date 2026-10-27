module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoE7Core
public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoS1Transport
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2xE7_finiteGL (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι) :
    Finite (D.V ≃ₗ[ZMod 3] D.V) := by
  haveI : Nonempty D.ι := ⟨e 0⟩
  let b0 : Basis D.ι (ZMod 3) D.V := basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  haveI : Fintype D.V := Fintype.ofEquiv (D.ι → ZMod 3) b0.equivFun.symm
  exact Finite.of_injective (fun f : D.V ≃ₗ[ZMod 3] D.V => (f : D.V → D.V))
    (fun f g h => LinearEquiv.ext (congrFun h))

private theorem ggQ2xE7_innerE (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) :
    GGQ2QuandleInner (ggQ2xQ_isConjRefl D) (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V)) := by
  intro π hπT hinj hπ
  haveI : Finite (D.V ≃ₗ[ZMod 3] D.V) := ggQ2xE7_finiteGL D hbas e
  have hfin : (ggQ2xQ_isConjRefl D).Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  have hsurj : Set.SurjOn π (ggQ2xQ_isConjRefl D) (ggQ2xQ_isConjRefl D) :=
    ((hfin.injOn_iff_bijOn_of_mapsTo hπT).mp hinj).surjOn
  exact ggQ2_quandle_aut_E D hbas (Or.inr (Or.inl ⟨e, hE⟩)) π hπT hinj hsurj hπ

private noncomputable def ggQ2xE7_basis (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι) :
    Basis (Fin 7) (ZMod 3) D.V :=
  basisOfLinearIndependentOfCardEqFinrank (hbas.1.comp e e.injective) (by
    rw [← hbas.2]
    exact Fintype.card_congr e)

private lemma ggQ2xE7_basis_apply (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (i : Fin 7) : ggQ2xE7_basis D hbas e i = D.coroot (e i) :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i

private noncomputable def ggQ2xE7_tauC (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι) :
    D.V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3) :=
  (ggQ2xE7_basis D hbas e).equivFun

private lemma ggQ2xE7_tau_coroot (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (i : Fin 7) : ggQ2xE7_tauC D hbas e (D.coroot (e i)) = Pi.single i 1 := by
  unfold ggQ2xE7_tauC
  rw [← ggQ2xE7_basis_apply D hbas e i]
  ext j
  rw [Basis.equivFun_self]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]

private lemma ggQ2xE7_cartan_eq (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (i j : Fin 7) :
    (D.cartan (e i) (e j) : ZMod 3) = ggECartan 7 i j := by
  rw [ggQ2xQ_cartan_E7 D e hE i j]
  rfl

private lemma ggQ2xE7_root (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (i : Fin 7) (v : D.V) :
    D.root (e i) v = ((ggECartan 7).mulVec (ggQ2xE7_tauC D hbas e v)) i := by
  have hv : v = ∑ j : Fin 7, (ggQ2xE7_tauC D hbas e v) j • D.coroot (e j) := by
    conv_lhs => rw [← (ggQ2xE7_basis D hbas e).equivFun.symm_apply_apply v]
    rw [Basis.equivFun_symm_apply]
    exact Finset.sum_congr rfl (fun j _ => by
      rw [ggQ2xE7_basis_apply D hbas e j]
      rfl)
  conv_lhs => rw [hv]
  rw [map_sum, Matrix.mulVec_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, D.pairing, ggQ2xE7_cartan_eq D e hE, Matrix.row_apply, smul_eq_mul, mul_comm]

private lemma ggQ2xE7_cartan_symm (i j : Fin 7) : ggECartan 7 i j = ggECartan 7 j i := by
  fin_cases i <;> fin_cases j <;> decide

private lemma ggQ2xE7_cartan_diag (j : Fin 7) : ggECartan 7 j j = 2 := by
  fin_cases j <;> decide

private lemma ggQ2xE7a_mulVec_sum (M : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (v : Fin 7 → ZMod 3) (i : Fin 7) :
    M.mulVec v i = ∑ j : Fin 7, M i j * v j := by
  rw [Matrix.mulVec_apply, dotProduct]
  simp [Matrix.row]

private lemma ggQ2xE7a_bil_sum (u v : Fin 7 → ZMod 3) :
    ggEBil 7 u v = ∑ i : Fin 7, u i * ∑ j : Fin 7, ggECartan 7 i j * v j := by
  rw [ggEBil, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [ggQ2xE7a_mulVec_sum]

private lemma ggQ2xE7a_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private lemma ggQ2xE7a_two_mul_div_two (A : ZMod 3) : (2 * A) / 2 = A :=
  mul_div_cancel_left₀ A ggQ2xE7a_two_ne_zero

private lemma ggQ2xE7a_mulVec_single (k : Fin 7) :
    (ggECartan 7).mulVec (Pi.single k 1) k = 2 := by
  rw [ggQ2xE7a_mulVec_sum, Finset.sum_eq_single k]
  · rw [ggQ2xE7_cartan_diag]; simp
  · intro i _ hi; rw [Pi.single_eq_of_ne hi, mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma ggQ2xE7_bil_symm (u v : Fin 7 → ZMod 3) : ggEBil 7 u v = ggEBil 7 v u := by
  rw [ggQ2xE7a_bil_sum, ggQ2xE7a_bil_sum]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [ggQ2xE7_cartan_symm b a]
  ring

private lemma ggQ2xE7_bil_sub_left (u u' v : Fin 7 → ZMod 3) :
    ggEBil 7 (u - u') v = ggEBil 7 u v - ggEBil 7 u' v := by
  unfold ggEBil
  rw [sub_dotProduct]

private lemma ggQ2xE7_bil_sub_right (u v v' : Fin 7 → ZMod 3) :
    ggEBil 7 u (v - v') = ggEBil 7 u v - ggEBil 7 u v' := by
  unfold ggEBil
  rw [Matrix.mulVec_sub, dotProduct_sub]

private lemma ggQ2xE7_bil_smul_left (c : ZMod 3) (u v : Fin 7 → ZMod 3) :
    ggEBil 7 (c • u) v = c * ggEBil 7 u v := by
  unfold ggEBil
  rw [smul_dotProduct, smul_eq_mul]

private lemma ggQ2xE7_bil_smul_right (c : ZMod 3) (u v : Fin 7 → ZMod 3) :
    ggEBil 7 u (c • v) = c * ggEBil 7 u v := by
  unfold ggEBil
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma ggQ2xE7_bil_single (k : Fin 7) (v : Fin 7 → ZMod 3) :
    ggEBil 7 (Pi.single k 1) v = (ggECartan 7).mulVec v k := by
  rw [ggQ2xE7a_bil_sum, ggQ2xE7a_mulVec_sum (ggECartan 7) v k]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi; rw [Pi.single_eq_of_ne hi, zero_mul]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma ggQ2xE7a_bil_single' (k : Fin 7) (v : Fin 7 → ZMod 3) :
    ggEBil 7 v (Pi.single k 1) = (ggECartan 7).mulVec v k :=
  (ggQ2xE7_bil_symm v (Pi.single k 1)).trans (ggQ2xE7_bil_single k v)

private lemma ggQ2xE7_bil_single_self (k : Fin 7) :
    ggEBil 7 (Pi.single k 1) (Pi.single k 1) = 2 := by
  rw [ggQ2xE7_bil_single k (Pi.single k 1), ggQ2xE7a_mulVec_single]

private lemma ggQ2xE7_simple_iso (j : Fin 7) (u v : Fin 7 → ZMod 3) :
    ggEBil 7 (ggESimple 7 j u) (ggESimple 7 j v) = ggEBil 7 u v := by
  unfold ggESimple
  simp only [ggQ2xE7_bil_sub_left, ggQ2xE7_bil_sub_right,
      ggQ2xE7_bil_smul_left, ggQ2xE7_bil_smul_right]
  rw [ggQ2xE7_bil_single_self, ggQ2xE7_bil_single, ggQ2xE7a_bil_single']
  ring

private lemma ggQ2xE7_refl_iso (z : Fin 7 → ZMod 3) (hz : ggEBil 7 z z ≠ 0)
    (u v : Fin 7 → ZMod 3) :
    ggEBil 7 (ggERefl 7 z u) (ggERefl 7 z v) = ggEBil 7 u v := by
  set a : ZMod 3 := 2 / ggEBil 7 z z with ha
  have hzz : a * ggEBil 7 z z = 2 := by rw [ha]; exact div_mul_cancel₀ 2 hz
  have hzu : 2 * ggEBil 7 z u / ggEBil 7 z z = a * ggEBil 7 z u := by rw [ha]; ring
  have hzv : 2 * ggEBil 7 z v / ggEBil 7 z z = a * ggEBil 7 z v := by rw [ha]; ring
  have hρu : ggERefl 7 z u = u - (a * ggEBil 7 z u) • z := by unfold ggERefl; rw [hzu]
  have hρv : ggERefl 7 z v = v - (a * ggEBil 7 z v) • z := by unfold ggERefl; rw [hzv]
  rw [hρu, hρv]
  simp only [ggQ2xE7_bil_sub_left, ggQ2xE7_bil_sub_right,
      ggQ2xE7_bil_smul_left, ggQ2xE7_bil_smul_right]
  rw [ggQ2xE7_bil_symm u z]
  have h2 : a * (a * ggEBil 7 z z) = 2 * a := by rw [hzz]; ring
  linear_combination (ggEBil 7 z u * ggEBil 7 z v) * h2

private lemma ggQ2xE7_refl_invol (z : Fin 7 → ZMod 3) (hz : ggEBil 7 z z ≠ 0)
    (v : Fin 7 → ZMod 3) : ggERefl 7 z (ggERefl 7 z v) = v := by
  set a : ZMod 3 := 2 / ggEBil 7 z z with ha
  have hzz : a * ggEBil 7 z z = 2 := by rw [ha]; exact div_mul_cancel₀ 2 hz
  have hzv : 2 * ggEBil 7 z v / ggEBil 7 z z = a * ggEBil 7 z v := by rw [ha]; ring
  have hzX : ∀ A : ZMod 3, (a * A) * ggEBil 7 z z = 2 * A := by
    intro A
    rw [show (a * A) * ggEBil 7 z z = A * (a * ggEBil 7 z z) by ring, hzz]
    ring
  rw [show ggERefl 7 z v = v - (a * ggEBil 7 z v) • z by unfold ggERefl; rw [hzv]]
  unfold ggERefl
  rw [ggQ2xE7_bil_sub_right, ggQ2xE7_bil_smul_right, hzX]
  rw [show ggEBil 7 z v - 2 * ggEBil 7 z v = -ggEBil 7 z v by ring]
  rw [show 2 * - ggEBil 7 z v / ggEBil 7 z z = -(a * ggEBil 7 z v) by rw [ha]; ring]
  rw [neg_smul, sub_neg_eq_add, sub_add_cancel]

private lemma ggQ2xE7_refl_single (k : Fin 7) (v : Fin 7 → ZMod 3) :
    ggERefl 7 (Pi.single k 1) v = ggESimple 7 k v := by
  unfold ggERefl ggESimple
  rw [ggQ2xE7_bil_single_self k, ggQ2xE7_bil_single k v, ggQ2xE7a_two_mul_div_two]

private lemma ggQ2xE7a_refl_sub (z x y : Fin 7 → ZMod 3) :
    ggERefl 7 z (x - y) = ggERefl 7 z x - ggERefl 7 z y := by
  unfold ggERefl
  rw [ggQ2xE7_bil_sub_right]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply]
  ring

private lemma ggQ2xE7a_refl_smul (z : Fin 7 → ZMod 3) (c : ZMod 3) (x : Fin 7 → ZMod 3) :
    ggERefl 7 z (c • x) = c • ggERefl 7 z x := by
  unfold ggERefl
  rw [ggQ2xE7_bil_smul_right]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply]
  ring

private lemma ggQ2xE7_refl_refl_conj (z w : Fin 7 → ZMod 3) (hz : ggEBil 7 z z ≠ 0)
    (v : Fin 7 → ZMod 3) :
    ggERefl 7 z (ggERefl 7 w (ggERefl 7 z v)) = ggERefl 7 (ggERefl 7 z w) v := by
  set b : ZMod 3 := 2 / ggEBil 7 w w with hb
  have hρw : ∀ u, ggERefl 7 w u = u - (b * ggEBil 7 w u) • w := by
    intro u; unfold ggERefl
    rw [show 2 * ggEBil 7 w u / ggEBil 7 w w = b * ggEBil 7 w u by rw [hb]; ring]
  have hww' : ggEBil 7 (ggERefl 7 z w) (ggERefl 7 z w) = ggEBil 7 w w :=
    ggQ2xE7_refl_iso z hz w w
  have hE : ∀ u, ggEBil 7 (ggERefl 7 z w) u = ggEBil 7 w (ggERefl 7 z u) := by
    intro u
    have h := ggQ2xE7_refl_iso z hz w (ggERefl 7 z u)
    rw [ggQ2xE7_refl_invol z hz u] at h
    exact h
  have hρzw : ∀ u, ggERefl 7 (ggERefl 7 z w) u
      = u - (b * ggEBil 7 w (ggERefl 7 z u)) • (ggERefl 7 z w) := by
    intro u
    change u - (2 * ggEBil 7 (ggERefl 7 z w) u
        / ggEBil 7 (ggERefl 7 z w) (ggERefl 7 z w)) • (ggERefl 7 z w)
      = u - (b * ggEBil 7 w (ggERefl 7 z u)) • (ggERefl 7 z w)
    rw [hww', hE u]
    rw [show 2 * ggEBil 7 w (ggERefl 7 z u) / ggEBil 7 w w
        = b * ggEBil 7 w (ggERefl 7 z u) by rw [hb]; ring]
  rw [hρzw, hρw, ggQ2xE7a_refl_sub, ggQ2xE7a_refl_smul, ggQ2xE7_refl_invol z hz v]

private lemma ggQ2xE7_refl_fix_of_orth (z w : Fin 7 → ZMod 3) (h : ggEBil 7 z w = 0) :
    ggERefl 7 z w = w := by
  unfold ggERefl
  rw [h]
  simp

private lemma ggQ2xE7_closure_simple (S : Set (Fin 7)) {j : Fin 7} (hj : j ∈ S)
    {ρ : Fin 7 → ZMod 3} (hρ : ρ ∈ ggEClosure 7 S) : ggESimple 7 j ρ ∈ ggEClosure 7 S :=
  fun T h1 h2 => h2 j hj ρ (hρ T h1 h2)

private lemma ggQ2xE7_closure_ind (S : Set (Fin 7)) (P : (Fin 7 → ZMod 3) → Prop)
    (h1 : ∀ k ∈ S, P (Pi.single k 1)) (h2 : ∀ j ∈ S, ∀ w, P w → P (ggESimple 7 j w))
    {ρ : Fin 7 → ZMod 3} (hρ : ρ ∈ ggEClosure 7 S) : P ρ :=
  hρ {w | P w} h1 h2

private lemma ggQ2xE7_closure_bil (S : Set (Fin 7)) {ρ : Fin 7 → ZMod 3}
    (hρ : ρ ∈ ggEClosure 7 S) : ggEBil 7 ρ ρ = 2 := by
  refine ggQ2xE7_closure_ind S (fun w => ggEBil 7 w w = 2) ?_ ?_ hρ
  · intro k _
    exact ggQ2xE7_bil_single_self k
  · intro j _ w hw
    rw [ggQ2xE7_simple_iso, hw]

private lemma ggQ2xE7_simple_coord (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (j : Fin 7) (v : Fin 7 → ZMod 3) :
    ggLinConj (ggQ2xE7_tauC D hbas e) (D.simpleRefl (e j)) v = ggESimple 7 j v := by
  rw [ggLinConj_apply]
  unfold GGQ2Lin.simpleRefl ggESimple
  rw [Module.reflection_apply, map_sub, map_smul]
  rw [ggQ2xE7_root D hbas e hE j ((ggQ2xE7_tauC D hbas e).symm v),
    ggQ2xE7_tau_coroot D hbas e j]
  simp

private lemma ggQ2xE7_parab_action (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (S : Set (Fin 7))
    {g : D.V ≃ₗ[ZMod 3] D.V} (hg : g ∈ D.parab (e '' S)) {v : Fin 7 → ZMod 3}
    (hv : v ∈ ggEClosure 7 S) :
    ggLinConj (ggQ2xE7_tauC D hbas e) g v ∈ ggEClosure 7 S := by
  unfold GGQ2Lin.parab at hg
  let τ := ggQ2xE7_tauC D hbas e
  have hmain : (∀ v ∈ ggEClosure 7 S, ggLinConj τ g v ∈ ggEClosure 7 S) ∧
      (∀ v ∈ ggEClosure 7 S, ggLinConj τ g⁻¹ v ∈ ggEClosure 7 S) := by
    refine Subgroup.closure_induction (p := fun w _ =>
      (∀ v ∈ ggEClosure 7 S, ggLinConj τ w v ∈ ggEClosure 7 S) ∧
      (∀ v ∈ ggEClosure 7 S, ggLinConj τ w⁻¹ v ∈ ggEClosure 7 S)) ?_ ?_ ?_ ?_ hg
    · rintro r ⟨y, ⟨j, hj, rfl⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · intro v hv
        rw [ggQ2xE7_simple_coord D hbas e hE j v]
        exact ggQ2xE7_closure_simple S hj hv
      · intro v hv
        rw [ggQ2xQ_inv_simpleRefl D (e j), ggQ2xE7_simple_coord D hbas e hE j v]
        exact ggQ2xE7_closure_simple S hj hv
    · refine ⟨?_, ?_⟩
      · intro v hv
        simpa [map_one] using hv
      · intro v hv
        simpa [inv_one, map_one] using hv
    · intro x y hx hy hpx hpy
      refine ⟨?_, ?_⟩
      · intro v hv
        rw [map_mul, LinearEquiv.mul_apply]
        exact hpx.1 _ (hpy.1 v hv)
      · intro v hv
        rw [mul_inv_rev, map_mul, LinearEquiv.mul_apply]
        exact hpy.2 _ (hpx.2 v hv)
    · intro x hx hpx
      refine ⟨hpx.2, ?_⟩
      intro v hv
      rw [inv_inv]
      exact hpx.1 v hv
  exact hmain.1 v hv

private lemma ggQ2xE7b_conj_act (D : GGQ2Lin 3) (τ : D.V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    {g h : D.V ≃ₗ[ZMod 3] D.V} {z w : Fin 7 → ZMod 3} (hz : ggEBil 7 z z ≠ 0)
    (hg : ∀ v, ggLinConj τ g v = ggERefl 7 z v) (hh : ∀ v, ggLinConj τ h v = ggERefl 7 w v)
    (v : Fin 7 → ZMod 3) :
    ggLinConj τ (g * h * g⁻¹) v = ggERefl 7 (ggERefl 7 z w) v := by
  have hginv : ∀ v, (ggLinConj τ g)⁻¹ v = ggERefl 7 z v := by
    intro v
    change (ggLinConj τ g).symm v = ggERefl 7 z v
    rw [LinearEquiv.symm_apply_eq]
    have h1 : ggLinConj τ g (ggERefl 7 z v) = v := by
      rw [hg (ggERefl 7 z v), ggQ2xE7_refl_invol z hz v]
    exact h1.symm
  rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [hginv v, hh (ggERefl 7 z v), hg (ggERefl 7 w (ggERefl 7 z v)),
    ggQ2xE7_refl_refl_conj z w hz v]

private lemma ggQ2xE7_refl_mem (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (S : Set (Fin 7)) {ρ : Fin 7 → ZMod 3}
    (hρ : ρ ∈ ggEClosure 7 S) :
    ∃ k ∈ S, ∃ w ∈ D.parab (e '' S), ∀ v,
      ggLinConj (ggQ2xE7_tauC D hbas e) (w * D.simpleRefl (e k) * w⁻¹) v = ggERefl 7 ρ v := by
  let τ := ggQ2xE7_tauC D hbas e
  refine ggQ2xE7_closure_ind S (fun ρ => ∃ k ∈ S, ∃ w ∈ D.parab (e '' S), ∀ v,
    ggLinConj τ (w * D.simpleRefl (e k) * w⁻¹) v = ggERefl 7 ρ v) ?_ ?_ hρ
  · intro k hk
    refine ⟨k, hk, 1, Subgroup.one_mem _, ?_⟩
    intro v
    rw [one_mul, inv_one, mul_one, ggQ2xE7_simple_coord D hbas e hE k v,
      ggQ2xE7_refl_single k v]
  · intro j hj σ hσ
    obtain ⟨k, hk, u, hu, hu_eq⟩ := hσ
    refine ⟨k, hk, D.simpleRefl (e j) * u, ?_, ?_⟩
    · have hgen : D.simpleRefl (e j) ∈ D.parab (e '' S) :=
        Subgroup.subset_closure (show D.simpleRefl (e j) ∈ D.simpleRefl '' (e '' S) from
          ⟨e j, ⟨j, hj, rfl⟩, rfl⟩)
      exact Subgroup.mul_mem _ hgen hu
    · intro v
      have hz : ggEBil 7 (Pi.single j 1) (Pi.single j 1) ≠ 0 := by
        rw [ggQ2xE7_bil_single_self]; decide
      have hg : ∀ v, ggLinConj τ (D.simpleRefl (e j)) v =
          ggERefl 7 (Pi.single j 1) v := by
        intro v
        rw [ggQ2xE7_simple_coord D hbas e hE j v, ggQ2xE7_refl_single j v]
      have hw : (D.simpleRefl (e j) * u) * D.simpleRefl (e k) *
            (D.simpleRefl (e j) * u)⁻¹ =
          D.simpleRefl (e j) * (u * D.simpleRefl (e k) * u⁻¹) *
            (D.simpleRefl (e j))⁻¹ := by
        group
      rw [hw, ggQ2xE7b_conj_act D τ hz hg hu_eq v, ggQ2xE7_refl_single j σ]

private lemma ggQ2xE7_conj_act (D : GGQ2Lin 3) (τ : D.V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))
    {g h : D.V ≃ₗ[ZMod 3] D.V} {z w : Fin 7 → ZMod 3} (hz : ggEBil 7 z z ≠ 0)
    (hg : ∀ v, ggLinConj τ g v = ggERefl 7 z v) (hh : ∀ v, ggLinConj τ h v = ggERefl 7 w v)
    (v : Fin 7 → ZMod 3) :
    ggLinConj τ (g * h * g⁻¹) v = ggERefl 7 (ggERefl 7 z w) v :=
  ggQ2xE7b_conj_act D τ hz hg hh v

private lemma ggQ2xE7_x_cartan (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (k : Fin 7) (hk : e k ≠ D.a) :
    (ggECartan 7).mulVec (ggQ2xE7_tauC D hbas e x) k = 0 := by
  have hfix : ∀ g ∈ D.parab {k | k ≠ D.a}, g x = x :=
    (hx x).2 (Submodule.mem_span_singleton_self x)
  have hmem : D.simpleRefl (e k) ∈ D.parab {k | k ≠ D.a} :=
    Subgroup.subset_closure ⟨e k, hk, rfl⟩
  have h1 : D.simpleRefl (e k) x = x := hfix _ hmem
  rw [GGQ2Lin.simpleRefl, Module.reflection_apply] at h1
  have h2 : D.root (e k) x • D.coroot (e k) = 0 := sub_eq_self.mp h1
  have h3 : D.root (e k) x = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h (LinearIndependent.ne_zero (e k) hbas.1)
  rw [← ggQ2xE7_root D hbas e hE k x]
  exact h3

private lemma ggQ2xE7_refl_fix (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    {z : Fin 7 → ZMod 3} (hza : z (e.symm D.a) = 0) :
    ggERefl 7 z (ggQ2xE7_tauC D hbas e x) = ggQ2xE7_tauC D hbas e x := by
  apply ggQ2xE7_refl_fix_of_orth
  rw [ggQ2xE7a_bil_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [← ggQ2xE7a_mulVec_sum (ggECartan 7) (ggQ2xE7_tauC D hbas e x) k]
  by_cases hk : k = e.symm D.a
  · rw [hk, hza, zero_mul]
  · have hk' : e k ≠ D.a := by
      intro h
      exact hk (by rw [← e.symm_apply_apply k, h])
    rw [ggQ2xE7_x_cartan D hbas e hE x hx k hk', mul_zero]

private lemma ggQ2xE7_image_ne (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι) :
    e '' {k : Fin 7 | k ≠ e.symm D.a} = {k | k ≠ D.a} := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩ h
    rw [← e.apply_symm_apply D.a] at h
    exact hk (e.injective h)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro h
    exact hx (by
      calc x = e (e.symm x) := (e.apply_symm_apply x).symm
        _ = e (e.symm D.a) := by rw [h]
        _ = D.a := e.apply_symm_apply D.a)

private noncomputable def ggQ2xE7_Z (D : GGQ2Lin 3)
    (τ : D.V ≃ₗ[ZMod 3] (Fin 7 → ZMod 3)) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) :
    Set (Fin 7 → ZMod 3) :=
  {z | ggEBil 7 z z ≠ 0 ∧ ∃ g ∈ A, ∀ v, ggLinConj τ g v = ggERefl 7 z v}

private lemma ggQ2xE7_Z_roots (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW : D.weyl ≤ A) :
    ggEClosure 7 Set.univ ⊆ ggQ2xE7_Z D (ggQ2xE7_tauC D hbas e) A := by
  intro ρ hρ
  refine ⟨?_, ?_⟩
  · rw [ggQ2xE7_closure_bil Set.univ hρ]; decide
  · obtain ⟨k, -, w, hw, hwz⟩ := ggQ2xE7_refl_mem D hbas e hE Set.univ hρ
    have hparab : D.parab (e '' (Set.univ : Set (Fin 7))) = D.weyl := by
      rw [Set.image_univ_of_surjective e.surjective]; rfl
    have hwA : w ∈ A := hW (by rwa [hparab] at hw)
    have hskA : D.simpleRefl (e k) ∈ A := hW (ggQ2xQ_simpleRefl_mem_weyl D (e k))
    exact ⟨w * D.simpleRefl (e k) * w⁻¹,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hwA hskA) (Subgroup.inv_mem _ hwA), hwz⟩

private lemma ggQ2xE7_Z_closed (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) :
    ∀ z ∈ ggQ2xE7_Z D (ggQ2xE7_tauC D hbas e) A, ∀ w ∈ ggQ2xE7_Z D (ggQ2xE7_tauC D hbas e) A,
      ggERefl 7 z w ∈ ggQ2xE7_Z D (ggQ2xE7_tauC D hbas e) A := by
  intro z hz w hw
  obtain ⟨hz0, gz, hgzA, hgz⟩ := hz
  obtain ⟨hw0, gw, hgwA, hgw⟩ := hw
  refine ⟨?_, gz * gw * gz⁻¹,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgzA hgwA) (Subgroup.inv_mem _ hgzA), ?_⟩
  · rw [ggQ2xE7_refl_iso z hz0 w w]; exact hw0
  · exact ggQ2xE7_conj_act D (ggQ2xE7_tauC D hbas e) hz0 hgz hgw

private lemma ggQ2xE7_Z_HL (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ z ∈ ggQ2xE7_Z D (ggQ2xE7_tauC D hbas e) A, z (e.symm D.a) = 0 →
      ∀ ρ ∈ ggEClosure 7 {k | k ≠ e.symm D.a}, ∀ ρ' ∈ ggEClosure 7 {k | k ≠ e.symm D.a},
        ggERefl 7 (ggERefl 7 z ρ) ρ' ∈ ggEClosure 7 {k | k ≠ e.symm D.a} := by
  intro z hz hza ρ hρ ρ' hρ'
  obtain ⟨hz0, gz, hgzA, hgz⟩ := hz
  have hfix : ggERefl 7 z (ggQ2xE7_tauC D hbas e x) = ggQ2xE7_tauC D hbas e x :=
    ggQ2xE7_refl_fix D hbas e hE x hx hza
  have h1 : ggLinConj (ggQ2xE7_tauC D hbas e) gz (ggQ2xE7_tauC D hbas e x)
      = ggQ2xE7_tauC D hbas e x := by rw [hgz, hfix]
  rw [ggLinConj_apply] at h1
  simp only [LinearEquiv.symm_apply_apply] at h1
  have hgzx : gz x = x := (ggQ2xE7_tauC D hbas e).injective h1
  have hspan : gz x ∈ Submodule.span (ZMod 3) {x} := by
    rw [hgzx]; exact Submodule.mem_span_singleton_self x
  have hnorm : gz ∈ Subgroup.normalizer
      (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)) := hHL gz hgzA hspan
  obtain ⟨k, hk, w, hw, hwz⟩ :=
    ggQ2xE7_refl_mem D hbas e hE {k : Fin 7 | k ≠ e.symm D.a} hρ
  have hk' : e k ≠ D.a := by
    intro h; exact hk (by rw [← e.symm_apply_apply k, h])
  have hw' : w ∈ D.parab {k | k ≠ D.a} := by
    rwa [ggQ2xE7_image_ne D e] at hw
  have hsk : D.simpleRefl (e k) ∈ D.parab {k | k ≠ D.a} :=
    Subgroup.subset_closure ⟨e k, hk', rfl⟩
  have hs : w * D.simpleRefl (e k) * w⁻¹ ∈ D.parab {k | k ≠ D.a} :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hw' hsk) (Subgroup.inv_mem _ hw')
  have hconj : gz * (w * D.simpleRefl (e k) * w⁻¹) * gz⁻¹ ∈ D.parab {k | k ≠ D.a} :=
    (Subgroup.mem_normalizer_iff.mp hnorm (w * D.simpleRefl (e k) * w⁻¹)).mp hs
  have hconj' : gz * (w * D.simpleRefl (e k) * w⁻¹) * gz⁻¹
      ∈ D.parab (e '' {k : Fin 7 | k ≠ e.symm D.a}) := by
    rw [ggQ2xE7_image_ne D e]; exact hconj
  have hconj_eq : ∀ v, ggLinConj (ggQ2xE7_tauC D hbas e)
      (gz * (w * D.simpleRefl (e k) * w⁻¹) * gz⁻¹) v
      = ggERefl 7 (ggERefl 7 z ρ) v :=
    ggQ2xE7_conj_act D (ggQ2xE7_tauC D hbas e) hz0 hgz hwz
  rw [← hconj_eq ρ']
  exact ggQ2xE7_parab_action D hbas e hE {k : Fin 7 | k ≠ e.symm D.a} hconj' hρ'

private lemma ggQ2xE7_Z_eq (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (ha : D.a = e 0 ∨ D.a = e 1 ∨ D.a = e 6)
    (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ggQ2xE7_Z D (ggQ2xE7_tauC D hbas e) A = ggEClosure 7 Set.univ := by
  have ha7 : e.symm D.a = 0 ∨ e.symm D.a = 1 ∨ e.symm D.a = 6 := by
    rcases ha with h | h | h
    · left; rw [h, Equiv.symm_apply_apply]
    · right; left; rw [h, Equiv.symm_apply_apply]
    · right; right; rw [h, Equiv.symm_apply_apply]
  refine Set.Subset.antisymm ?_ (ggQ2xE7_Z_roots D hbas e hE A hW)
  exact ggQ2_E7_Z (e.symm D.a) ha7 _ (fun z hz => hz.1) (ggQ2xE7_Z_roots D hbas e hE A hW)
    (ggQ2xE7_Z_closed D hbas e A) (ggQ2xE7_Z_HL D hbas e hE x hx A hHL)

private lemma ggQ2xE7_refl_centre (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW : D.weyl ≤ A) (hTF : TransvectionFree A) {t : D.V ≃ₗ[ZMod 3] D.V}
    (ht : t ∈ ggReflSet A) :
    ∃ z, ggEBil 7 z z ≠ 0 ∧ ∀ v, ggLinConj (ggQ2xE7_tauC D hbas e) t v = ggERefl 7 z v := by
  obtain ⟨c, φ, hφ, ht_eq⟩ := ht.2
  have h4 : 4 ≤ Fintype.card D.ι := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  have hsym : ∀ i j, D.cartan i j = D.cartan j i :=
    ggQ2xQ_cartan_symm_of_reindex CoxeterMatrix.E₇
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) D e hE
  have hφ' : (φ.comp ((ggQ2xE7_tauC D hbas e).symm :
      (Fin 7 → ZMod 3) ≃ₗ[ZMod 3] D.V).toLinearMap)
      (ggQ2xE7_tauC D hbas e c) = 2 := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hφ
  have heq : Module.reflection hφ' = ggLinConj (ggQ2xE7_tauC D hbas e) t := by
    rw [ht_eq]
    apply LinearEquiv.ext; intro v
    rw [ggLinConj_apply, Module.reflection_apply, Module.reflection_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply, map_sub, map_smul]
  have ht' : Module.reflection hφ'
      ∈ A.map (ggLinConj (ggQ2xE7_tauC D hbas e)).toMonoidHom := by
    rw [heq]
    exact Subgroup.mem_map.mpr ⟨t, ht.1, rfl⟩
  have hB' : ∀ i j, (Matrix.toBilin' (ggECartan 7))
      ((ggQ2xE7_tauC D hbas e) (D.coroot i)) ((ggQ2xE7_tauC D hbas e) (D.coroot j))
      = (D.cartan i j : ZMod 3) := by
    intro i j
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    rw [ggQ2xE7_tau_coroot, ggQ2xE7_tau_coroot, Matrix.toBilin'_single,
      ggQ2xE7_cartan_eq D e hE]
  obtain ⟨ε, hε, horth⟩ := ggQ2_S1_transport D hbas h4 hsym (ggQ2xE7_tauC D hbas e)
    (Matrix.toBilin' (ggECartan 7)) hB' A hW hTF hφ' ht'
  have hB'_apply : ∀ u v : Fin 7 → ZMod 3,
      (Matrix.toBilin' (ggECartan 7)) u v = ggEBil 7 u v :=
    fun u v => Matrix.toBilin'_apply' (ggECartan 7) u v
  have horthv : ∀ w : D.V, φ w
      = ε * ggEBil 7 (ggQ2xE7_tauC D hbas e c) (ggQ2xE7_tauC D hbas e w) := by
    intro w
    have h1 := horth (ggQ2xE7_tauC D hbas e w)
    rw [hB'_apply] at h1
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      using h1
  have hcc : ggEBil 7 (ggQ2xE7_tauC D hbas e c) (ggQ2xE7_tauC D hbas e c) ≠ 0 := by
    intro h0
    have h1 : φ c = 2 := hφ
    rw [horthv c, h0, mul_zero] at h1
    exact (by decide : (2 : ZMod 3) ≠ 0) h1.symm
  have hε2 : ε = 2 / ggEBil 7 (ggQ2xE7_tauC D hbas e c)
      (ggQ2xE7_tauC D hbas e c) := by
    rw [eq_div_iff hcc]
    have h1 : φ c = ε * ggEBil 7 (ggQ2xE7_tauC D hbas e c)
        (ggQ2xE7_tauC D hbas e c) := horthv c
    rw [hφ] at h1
    exact h1.symm
  refine ⟨ggQ2xE7_tauC D hbas e c, hcc, ?_⟩
  intro v
  rw [← heq, Module.reflection_apply]
  unfold ggERefl
  have hφ'v : (φ.comp ((ggQ2xE7_tauC D hbas e).symm :
      (Fin 7 → ZMod 3) ≃ₗ[ZMod 3] D.V).toLinearMap) v
      = ε * ggEBil 7 (ggQ2xE7_tauC D hbas e c) v := by
    rw [horth v, hB'_apply]
  rw [hφ'v, hε2]
  ring_nf

private lemma ggQ2xE7_reflSet (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (ha : D.a = e 0 ∨ D.a = e 1 ∨ D.a = e 6)
    (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ggReflSet A = ggQ2xQ_isConjRefl D := by
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨z, hz0, hzt⟩ := ggQ2xE7_refl_centre D hbas e hE A hW hTF ht
    have hzZ : z ∈ ggQ2xE7_Z D (ggQ2xE7_tauC D hbas e) A := ⟨hz0, t, ht.1, hzt⟩
    rw [ggQ2xE7_Z_eq D hbas e hE ha x hx A hW hHL] at hzZ
    obtain ⟨k, -, w, hw, hwz⟩ := ggQ2xE7_refl_mem D hbas e hE Set.univ hzZ
    have hwW : w ∈ D.weyl := by
      have h1 : D.parab (e '' (Set.univ : Set (Fin 7))) = D.weyl := by
        rw [Set.image_univ_of_surjective e.surjective]
        rfl
      rwa [h1] at hw
    refine ⟨e k, w, hwW, ?_⟩
    apply (ggLinConj (ggQ2xE7_tauC D hbas e)).injective
    apply LinearEquiv.ext
    intro v
    rw [hzt v, hwz v]
  · rintro t ⟨k, w, hw, rfl⟩
    have hCsym : ∀ i j, D.cartan i j = D.cartan j i :=
      ggQ2xQ_cartan_symm_of_reindex CoxeterMatrix.E₇
        (by intro a b; fin_cases a <;> fin_cases b <;> decide) D e hE
    refine ⟨hW (Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (ggQ2xQ_simpleRefl_mem_weyl D k))
      (Subgroup.inv_mem _ hw)), ?_⟩
    obtain ⟨h, heq⟩ := ggQ2xQ_conj_simpleRefl D hbas hCsym k hw
    exact ⟨w (D.coroot k), ggQ2xQ_form D hbas (w (D.coroot k)), h, heq⟩

private lemma ggQ2xE7_weyl_le_reflGp (D : GGQ2Lin 3) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW : D.weyl ≤ A) : D.weyl ≤ reflGp A := by
  unfold GGQ2Lin.weyl GGQ2Lin.parab
  rw [Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact Subgroup.subset_closure ⟨hW (Subgroup.subset_closure ⟨k, Set.mem_univ k, rfl⟩),
    D.coroot k, D.root k, D.root_coroot_self k, rfl⟩

private theorem ggQ2xE7_inner (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (ha : D.a = e 0 ∨ D.a = e 1 ∨ D.a = e 6)
    (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    GGQ2QuandleInner (ggReflSet A) (reflGp A) := by
  have h0 := ggQ2xE7_innerE D hbas e hE
  rw [← ggQ2xE7_reflSet D hbas e hE ha x hx A hW hTF hHL] at h0
  intro π hπT hinj hπ
  obtain ⟨g, hg, hgt⟩ := h0 π hπT hinj hπ
  exact ⟨g, ggQ2xE7_weyl_le_reflGp D A hW hg, hgt⟩

theorem ggQ2_thmB_E7 (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 7 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₇.reindex e) (ha : D.a = e 0 ∨ D.a = e 1 ∨ D.a = e 6)
    (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x} := by
  have h4 : 4 ≤ Fintype.card D.ι := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  have hinner : GGQ2QuandleInner (ggReflSet A) (reflGp A) :=
    ggQ2xE7_inner D hbas e hE ha x hx A hW hTF hHL
  exact ggQ2_P3_of_pm A x (ggQ2_transfer (p := 3) rfl D hbas h4 A hW (reflGp A) hinner)

end CFSG.StandardType

end
