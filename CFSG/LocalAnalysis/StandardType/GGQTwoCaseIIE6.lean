module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoE7Core
public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoS1Transport
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleE
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIIDual
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIINonsplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2xE6_finiteGL (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι) :
    Finite (D.V ≃ₗ[ZMod 3] D.V) := by
  haveI : Nonempty D.ι := ⟨e 0⟩
  let b0 : Basis D.ι (ZMod 3) D.V := basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  haveI : Fintype D.V := Fintype.ofEquiv (D.ι → ZMod 3) b0.equivFun.symm
  exact Finite.of_injective (fun f : D.V ≃ₗ[ZMod 3] D.V => (f : D.V → D.V))
    (fun f g h => LinearEquiv.ext (congrFun h))

private noncomputable def ggQ2xE6_basis (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι) :
    Basis (Fin 6) (ZMod 3) D.V :=
  basisOfLinearIndependentOfCardEqFinrank (hbas.1.comp e e.injective) (by
    rw [← hbas.2]
    exact Fintype.card_congr e)

private lemma ggQ2xE6_basis_apply (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (i : Fin 6) : ggQ2xE6_basis D hbas e i = D.coroot (e i) :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i

private noncomputable def ggQ2xE6_tauC (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι) :
    D.V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
  (ggQ2xE6_basis D hbas e).equivFun

private lemma ggQ2xE6_tau_coroot (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (i : Fin 6) : ggQ2xE6_tauC D hbas e (D.coroot (e i)) = Pi.single i 1 := by
  unfold ggQ2xE6_tauC
  rw [← ggQ2xE6_basis_apply D hbas e i]
  ext j
  rw [Basis.equivFun_self]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]

private lemma ggQ2xE6_cartan_eq (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (i j : Fin 6) :
    (D.cartan (e i) (e j) : ZMod 3) = ggECartan 6 i j := by
  rw [ggQ2xQ_cartan_E6 D e hE i j]
  rfl

private lemma ggQ2xE6_root (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (i : Fin 6) (v : D.V) :
    D.root (e i) v = ((ggECartan 6).mulVec (ggQ2xE6_tauC D hbas e v)) i := by
  have hv : v = ∑ j : Fin 6, (ggQ2xE6_tauC D hbas e v) j • D.coroot (e j) := by
    conv_lhs => rw [← (ggQ2xE6_basis D hbas e).equivFun.symm_apply_apply v]
    rw [Basis.equivFun_symm_apply]
    exact Finset.sum_congr rfl (fun j _ => by
      rw [ggQ2xE6_basis_apply D hbas e j]
      rfl)
  conv_lhs => rw [hv]
  rw [map_sum, Matrix.mulVec_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, D.pairing, ggQ2xE6_cartan_eq D e hE, Matrix.row_apply, smul_eq_mul, mul_comm]

private lemma ggQ2xE6_cartan_symm (i j : Fin 6) : ggECartan 6 i j = ggECartan 6 j i := by
  fin_cases i <;> fin_cases j <;> decide

private lemma ggQ2xE6_cartan_diag (j : Fin 6) : ggECartan 6 j j = 2 := by
  fin_cases j <;> decide

private lemma ggQ2xE6a_mulVec_sum (M : Matrix (Fin 6) (Fin 6) (ZMod 3))
    (v : Fin 6 → ZMod 3) (i : Fin 6) :
    M.mulVec v i = ∑ j : Fin 6, M i j * v j := by
  rw [Matrix.mulVec_apply, dotProduct]
  simp [Matrix.row]

private lemma ggQ2xE6a_bil_sum (u v : Fin 6 → ZMod 3) :
    ggEBil 6 u v = ∑ i : Fin 6, u i * ∑ j : Fin 6, ggECartan 6 i j * v j := by
  rw [ggEBil, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [ggQ2xE6a_mulVec_sum]

private lemma ggQ2xE6a_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private lemma ggQ2xE6a_two_mul_div_two (A : ZMod 3) : (2 * A) / 2 = A :=
  mul_div_cancel_left₀ A ggQ2xE6a_two_ne_zero

private lemma ggQ2xE6a_mulVec_single (k : Fin 6) :
    (ggECartan 6).mulVec (Pi.single k 1) k = 2 := by
  rw [ggQ2xE6a_mulVec_sum, Finset.sum_eq_single k]
  · rw [ggQ2xE6_cartan_diag]; simp
  · intro i _ hi; rw [Pi.single_eq_of_ne hi, mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma ggQ2xE6_bil_symm (u v : Fin 6 → ZMod 3) : ggEBil 6 u v = ggEBil 6 v u := by
  rw [ggQ2xE6a_bil_sum, ggQ2xE6a_bil_sum]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [ggQ2xE6_cartan_symm b a]
  ring

private lemma ggQ2xE6_bil_sub_left (u u' v : Fin 6 → ZMod 3) :
    ggEBil 6 (u - u') v = ggEBil 6 u v - ggEBil 6 u' v := by
  unfold ggEBil
  rw [sub_dotProduct]

private lemma ggQ2xE6_bil_sub_right (u v v' : Fin 6 → ZMod 3) :
    ggEBil 6 u (v - v') = ggEBil 6 u v - ggEBil 6 u v' := by
  unfold ggEBil
  rw [Matrix.mulVec_sub, dotProduct_sub]

private lemma ggQ2xE6_bil_smul_left (c : ZMod 3) (u v : Fin 6 → ZMod 3) :
    ggEBil 6 (c • u) v = c * ggEBil 6 u v := by
  unfold ggEBil
  rw [smul_dotProduct, smul_eq_mul]

private lemma ggQ2xE6_bil_smul_right (c : ZMod 3) (u v : Fin 6 → ZMod 3) :
    ggEBil 6 u (c • v) = c * ggEBil 6 u v := by
  unfold ggEBil
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma ggQ2xE6_bil_single (k : Fin 6) (v : Fin 6 → ZMod 3) :
    ggEBil 6 (Pi.single k 1) v = (ggECartan 6).mulVec v k := by
  rw [ggQ2xE6a_bil_sum, ggQ2xE6a_mulVec_sum (ggECartan 6) v k]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi; rw [Pi.single_eq_of_ne hi, zero_mul]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma ggQ2xE6a_bil_single' (k : Fin 6) (v : Fin 6 → ZMod 3) :
    ggEBil 6 v (Pi.single k 1) = (ggECartan 6).mulVec v k :=
  (ggQ2xE6_bil_symm v (Pi.single k 1)).trans (ggQ2xE6_bil_single k v)

private lemma ggQ2xE6_bil_single_self (k : Fin 6) :
    ggEBil 6 (Pi.single k 1) (Pi.single k 1) = 2 := by
  rw [ggQ2xE6_bil_single k (Pi.single k 1), ggQ2xE6a_mulVec_single]

private lemma ggQ2xE6_simple_iso (j : Fin 6) (u v : Fin 6 → ZMod 3) :
    ggEBil 6 (ggESimple 6 j u) (ggESimple 6 j v) = ggEBil 6 u v := by
  unfold ggESimple
  simp only [ggQ2xE6_bil_sub_left, ggQ2xE6_bil_sub_right,
      ggQ2xE6_bil_smul_left, ggQ2xE6_bil_smul_right]
  rw [ggQ2xE6_bil_single_self, ggQ2xE6_bil_single, ggQ2xE6a_bil_single']
  ring

private lemma ggQ2xE6_refl_iso (z : Fin 6 → ZMod 3) (hz : ggEBil 6 z z ≠ 0)
    (u v : Fin 6 → ZMod 3) :
    ggEBil 6 (ggERefl 6 z u) (ggERefl 6 z v) = ggEBil 6 u v := by
  set a : ZMod 3 := 2 / ggEBil 6 z z with ha
  have hzz : a * ggEBil 6 z z = 2 := by rw [ha]; exact div_mul_cancel₀ 2 hz
  have hzu : 2 * ggEBil 6 z u / ggEBil 6 z z = a * ggEBil 6 z u := by rw [ha]; ring
  have hzv : 2 * ggEBil 6 z v / ggEBil 6 z z = a * ggEBil 6 z v := by rw [ha]; ring
  have hρu : ggERefl 6 z u = u - (a * ggEBil 6 z u) • z := by unfold ggERefl; rw [hzu]
  have hρv : ggERefl 6 z v = v - (a * ggEBil 6 z v) • z := by unfold ggERefl; rw [hzv]
  rw [hρu, hρv]
  simp only [ggQ2xE6_bil_sub_left, ggQ2xE6_bil_sub_right,
      ggQ2xE6_bil_smul_left, ggQ2xE6_bil_smul_right]
  rw [ggQ2xE6_bil_symm u z]
  have h2 : a * (a * ggEBil 6 z z) = 2 * a := by rw [hzz]; ring
  linear_combination (ggEBil 6 z u * ggEBil 6 z v) * h2

private lemma ggQ2xE6_refl_invol (z : Fin 6 → ZMod 3) (hz : ggEBil 6 z z ≠ 0)
    (v : Fin 6 → ZMod 3) : ggERefl 6 z (ggERefl 6 z v) = v := by
  set a : ZMod 3 := 2 / ggEBil 6 z z with ha
  have hzz : a * ggEBil 6 z z = 2 := by rw [ha]; exact div_mul_cancel₀ 2 hz
  have hzv : 2 * ggEBil 6 z v / ggEBil 6 z z = a * ggEBil 6 z v := by rw [ha]; ring
  have hzX : ∀ A : ZMod 3, (a * A) * ggEBil 6 z z = 2 * A := by
    intro A
    rw [show (a * A) * ggEBil 6 z z = A * (a * ggEBil 6 z z) by ring, hzz]
    ring
  rw [show ggERefl 6 z v = v - (a * ggEBil 6 z v) • z by unfold ggERefl; rw [hzv]]
  unfold ggERefl
  rw [ggQ2xE6_bil_sub_right, ggQ2xE6_bil_smul_right, hzX]
  rw [show ggEBil 6 z v - 2 * ggEBil 6 z v = -ggEBil 6 z v by ring]
  rw [show 2 * - ggEBil 6 z v / ggEBil 6 z z = -(a * ggEBil 6 z v) by rw [ha]; ring]
  rw [neg_smul, sub_neg_eq_add, sub_add_cancel]

private lemma ggQ2xE6_refl_single (k : Fin 6) (v : Fin 6 → ZMod 3) :
    ggERefl 6 (Pi.single k 1) v = ggESimple 6 k v := by
  unfold ggERefl ggESimple
  rw [ggQ2xE6_bil_single_self k, ggQ2xE6_bil_single k v, ggQ2xE6a_two_mul_div_two]

private lemma ggQ2xE6a_simple_smul (j : Fin 6) (c : ZMod 3) (x : Fin 6 → ZMod 3) :
    ggESimple 6 j (c • x) = c • ggESimple 6 j x := by
  unfold ggESimple
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_sub, smul_eq_mul, smul_smul]

private lemma ggQ2xE6a_refl_sub (z x y : Fin 6 → ZMod 3) :
    ggERefl 6 z (x - y) = ggERefl 6 z x - ggERefl 6 z y := by
  unfold ggERefl
  rw [ggQ2xE6_bil_sub_right]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply]
  ring

private lemma ggQ2xE6a_refl_smul (z : Fin 6 → ZMod 3) (c : ZMod 3) (x : Fin 6 → ZMod 3) :
    ggERefl 6 z (c • x) = c • ggERefl 6 z x := by
  unfold ggERefl
  rw [ggQ2xE6_bil_smul_right]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply]
  ring

private lemma ggQ2xE6_refl_refl_conj (z w : Fin 6 → ZMod 3) (hz : ggEBil 6 z z ≠ 0)
    (v : Fin 6 → ZMod 3) :
    ggERefl 6 z (ggERefl 6 w (ggERefl 6 z v)) = ggERefl 6 (ggERefl 6 z w) v := by
  set b : ZMod 3 := 2 / ggEBil 6 w w with hb
  have hρw : ∀ u, ggERefl 6 w u = u - (b * ggEBil 6 w u) • w := by
    intro u; unfold ggERefl
    rw [show 2 * ggEBil 6 w u / ggEBil 6 w w = b * ggEBil 6 w u by rw [hb]; ring]
  have hww' : ggEBil 6 (ggERefl 6 z w) (ggERefl 6 z w) = ggEBil 6 w w :=
    ggQ2xE6_refl_iso z hz w w
  have hE : ∀ u, ggEBil 6 (ggERefl 6 z w) u = ggEBil 6 w (ggERefl 6 z u) := by
    intro u
    have h := ggQ2xE6_refl_iso z hz w (ggERefl 6 z u)
    rw [ggQ2xE6_refl_invol z hz u] at h
    exact h
  have hρzw : ∀ u, ggERefl 6 (ggERefl 6 z w) u
      = u - (b * ggEBil 6 w (ggERefl 6 z u)) • (ggERefl 6 z w) := by
    intro u
    change u - (2 * ggEBil 6 (ggERefl 6 z w) u
        / ggEBil 6 (ggERefl 6 z w) (ggERefl 6 z w)) • (ggERefl 6 z w)
      = u - (b * ggEBil 6 w (ggERefl 6 z u)) • (ggERefl 6 z w)
    rw [hww', hE u]
    rw [show 2 * ggEBil 6 w (ggERefl 6 z u) / ggEBil 6 w w
        = b * ggEBil 6 w (ggERefl 6 z u) by rw [hb]; ring]
  rw [hρzw, hρw, ggQ2xE6a_refl_sub, ggQ2xE6a_refl_smul, ggQ2xE6_refl_invol z hz v]

private lemma ggQ2xE6_closure_single (S : Set (Fin 6)) {k : Fin 6} (hk : k ∈ S) :
    (Pi.single k 1 : Fin 6 → ZMod 3) ∈ ggEClosure 6 S :=
  fun _ h1 _ => h1 k hk

private lemma ggQ2xE6_closure_simple (S : Set (Fin 6)) {j : Fin 6} (hj : j ∈ S)
    {ρ : Fin 6 → ZMod 3} (hρ : ρ ∈ ggEClosure 6 S) : ggESimple 6 j ρ ∈ ggEClosure 6 S :=
  fun T h1 h2 => h2 j hj ρ (hρ T h1 h2)

private lemma ggQ2xE6_closure_ind (S : Set (Fin 6)) (P : (Fin 6 → ZMod 3) → Prop)
    (h1 : ∀ k ∈ S, P (Pi.single k 1)) (h2 : ∀ j ∈ S, ∀ w, P w → P (ggESimple 6 j w))
    {ρ : Fin 6 → ZMod 3} (hρ : ρ ∈ ggEClosure 6 S) : P ρ :=
  hρ {w | P w} h1 h2

private lemma ggQ2xE6_closure_bil (S : Set (Fin 6)) {ρ : Fin 6 → ZMod 3}
    (hρ : ρ ∈ ggEClosure 6 S) : ggEBil 6 ρ ρ = 2 := by
  refine ggQ2xE6_closure_ind S (fun w => ggEBil 6 w w = 2) ?_ ?_ hρ
  · intro k _
    exact ggQ2xE6_bil_single_self k
  · intro j _ w hw
    rw [ggQ2xE6_simple_iso, hw]

private lemma ggQ2xE6_simple_coord (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (j : Fin 6) (v : Fin 6 → ZMod 3) :
    ggLinConj (ggQ2xE6_tauC D hbas e) (D.simpleRefl (e j)) v = ggESimple 6 j v := by
  rw [ggLinConj_apply]
  unfold GGQ2Lin.simpleRefl ggESimple
  rw [Module.reflection_apply, map_sub, map_smul]
  rw [ggQ2xE6_root D hbas e hE j ((ggQ2xE6_tauC D hbas e).symm v),
    ggQ2xE6_tau_coroot D hbas e j]
  simp

private lemma ggQ2xE6b_conj_act (D : GGQ2Lin 3) (τ : D.V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3))
    {g h : D.V ≃ₗ[ZMod 3] D.V} {z w : Fin 6 → ZMod 3} (hz : ggEBil 6 z z ≠ 0)
    (hg : ∀ v, ggLinConj τ g v = ggERefl 6 z v) (hh : ∀ v, ggLinConj τ h v = ggERefl 6 w v)
    (v : Fin 6 → ZMod 3) :
    ggLinConj τ (g * h * g⁻¹) v = ggERefl 6 (ggERefl 6 z w) v := by
  have hginv : ∀ v, (ggLinConj τ g)⁻¹ v = ggERefl 6 z v := by
    intro v
    change (ggLinConj τ g).symm v = ggERefl 6 z v
    rw [LinearEquiv.symm_apply_eq]
    have h1 : ggLinConj τ g (ggERefl 6 z v) = v := by
      rw [hg (ggERefl 6 z v), ggQ2xE6_refl_invol z hz v]
    exact h1.symm
  rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [hginv v, hh (ggERefl 6 z v), hg (ggERefl 6 w (ggERefl 6 z v)),
    ggQ2xE6_refl_refl_conj z w hz v]

private lemma ggQ2xE6_refl_mem (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (S : Set (Fin 6)) {ρ : Fin 6 → ZMod 3}
    (hρ : ρ ∈ ggEClosure 6 S) :
    ∃ k ∈ S, ∃ w ∈ D.parab (e '' S), ∀ v,
      ggLinConj (ggQ2xE6_tauC D hbas e) (w * D.simpleRefl (e k) * w⁻¹) v = ggERefl 6 ρ v := by
  let τ := ggQ2xE6_tauC D hbas e
  refine ggQ2xE6_closure_ind S (fun ρ => ∃ k ∈ S, ∃ w ∈ D.parab (e '' S), ∀ v,
    ggLinConj τ (w * D.simpleRefl (e k) * w⁻¹) v = ggERefl 6 ρ v) ?_ ?_ hρ
  · intro k hk
    refine ⟨k, hk, 1, Subgroup.one_mem _, ?_⟩
    intro v
    rw [one_mul, inv_one, mul_one, ggQ2xE6_simple_coord D hbas e hE k v,
      ggQ2xE6_refl_single k v]
  · intro j hj σ hσ
    obtain ⟨k, hk, u, hu, hu_eq⟩ := hσ
    refine ⟨k, hk, D.simpleRefl (e j) * u, ?_, ?_⟩
    · have hgen : D.simpleRefl (e j) ∈ D.parab (e '' S) :=
        Subgroup.subset_closure (show D.simpleRefl (e j) ∈ D.simpleRefl '' (e '' S) from
          ⟨e j, ⟨j, hj, rfl⟩, rfl⟩)
      exact Subgroup.mul_mem _ hgen hu
    · intro v
      have hz : ggEBil 6 (Pi.single j 1) (Pi.single j 1) ≠ 0 := by
        rw [ggQ2xE6_bil_single_self]; decide
      have hg : ∀ v, ggLinConj τ (D.simpleRefl (e j)) v =
          ggERefl 6 (Pi.single j 1) v := by
        intro v
        rw [ggQ2xE6_simple_coord D hbas e hE j v, ggQ2xE6_refl_single j v]
      have hw : (D.simpleRefl (e j) * u) * D.simpleRefl (e k) *
            (D.simpleRefl (e j) * u)⁻¹ =
          D.simpleRefl (e j) * (u * D.simpleRefl (e k) * u⁻¹) *
            (D.simpleRefl (e j))⁻¹ := by
        group
      rw [hw, ggQ2xE6b_conj_act D τ hz hg hu_eq v, ggQ2xE6_refl_single j σ]

private lemma ggQ2xE6_conj_act (D : GGQ2Lin 3) (τ : D.V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3))
    {g h : D.V ≃ₗ[ZMod 3] D.V} {z w : Fin 6 → ZMod 3} (hz : ggEBil 6 z z ≠ 0)
    (hg : ∀ v, ggLinConj τ g v = ggERefl 6 z v) (hh : ∀ v, ggLinConj τ h v = ggERefl 6 w v)
    (v : Fin 6 → ZMod 3) :
    ggLinConj τ (g * h * g⁻¹) v = ggERefl 6 (ggERefl 6 z w) v :=
  ggQ2xE6b_conj_act D τ hz hg hh v

private noncomputable def ggQ2xE6_Z (D : GGQ2Lin 3)
    (τ : D.V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) :
    Set (Fin 6 → ZMod 3) :=
  {z | ggEBil 6 z z ≠ 0 ∧ ∃ g ∈ A, ∀ v, ggLinConj τ g v = ggERefl 6 z v}

private lemma ggQ2xE6_Z_roots (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW : D.weyl ≤ A) :
    ggEClosure 6 Set.univ ⊆ ggQ2xE6_Z D (ggQ2xE6_tauC D hbas e) A := by
  intro ρ hρ
  refine ⟨?_, ?_⟩
  · rw [ggQ2xE6_closure_bil Set.univ hρ]; decide
  · obtain ⟨k, -, w, hw, hwz⟩ := ggQ2xE6_refl_mem D hbas e hE Set.univ hρ
    have hparab : D.parab (e '' (Set.univ : Set (Fin 6))) = D.weyl := by
      rw [Set.image_univ_of_surjective e.surjective]; rfl
    have hwA : w ∈ A := hW (by rwa [hparab] at hw)
    have hskA : D.simpleRefl (e k) ∈ A := hW (ggQ2xQ_simpleRefl_mem_weyl D (e k))
    exact ⟨w * D.simpleRefl (e k) * w⁻¹,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hwA hskA) (Subgroup.inv_mem _ hwA), hwz⟩

private lemma ggQ2xE6_Z_closed (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) :
    ∀ z ∈ ggQ2xE6_Z D (ggQ2xE6_tauC D hbas e) A, ∀ w ∈ ggQ2xE6_Z D (ggQ2xE6_tauC D hbas e) A,
      ggERefl 6 z w ∈ ggQ2xE6_Z D (ggQ2xE6_tauC D hbas e) A := by
  intro z hz w hw
  obtain ⟨hz0, gz, hgzA, hgz⟩ := hz
  obtain ⟨hw0, gw, hgwA, hgw⟩ := hw
  refine ⟨?_, gz * gw * gz⁻¹,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgzA hgwA) (Subgroup.inv_mem _ hgzA), ?_⟩
  · rw [ggQ2xE6_refl_iso z hz0 w w]; exact hw0
  · exact ggQ2xE6_conj_act D (ggQ2xE6_tauC D hbas e) hz0 hgz hgw

private lemma ggQ2xE6_refl_centre (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW : D.weyl ≤ A) (hTF : TransvectionFree A) {t : D.V ≃ₗ[ZMod 3] D.V}
    (ht : t ∈ ggReflSet A) :
    ∃ z, ggEBil 6 z z ≠ 0 ∧ ∀ v, ggLinConj (ggQ2xE6_tauC D hbas e) t v = ggERefl 6 z v := by
  obtain ⟨c, φ, hφ, ht_eq⟩ := ht.2
  have h4 : 4 ≤ Fintype.card D.ι := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  have hsym : ∀ i j, D.cartan i j = D.cartan j i :=
    ggQ2xQ_cartan_symm_of_reindex CoxeterMatrix.E₆
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) D e hE
  have hφ' : (φ.comp ((ggQ2xE6_tauC D hbas e).symm :
      (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] D.V).toLinearMap)
      (ggQ2xE6_tauC D hbas e c) = 2 := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hφ
  have heq : Module.reflection hφ' = ggLinConj (ggQ2xE6_tauC D hbas e) t := by
    rw [ht_eq]
    apply LinearEquiv.ext; intro v
    rw [ggLinConj_apply, Module.reflection_apply, Module.reflection_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply, map_sub, map_smul]
  have ht' : Module.reflection hφ'
      ∈ A.map (ggLinConj (ggQ2xE6_tauC D hbas e)).toMonoidHom := by
    rw [heq]
    exact Subgroup.mem_map.mpr ⟨t, ht.1, rfl⟩
  have hB' : ∀ i j, (Matrix.toBilin' (ggECartan 6))
      ((ggQ2xE6_tauC D hbas e) (D.coroot i)) ((ggQ2xE6_tauC D hbas e) (D.coroot j))
      = (D.cartan i j : ZMod 3) := by
    intro i j
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    rw [ggQ2xE6_tau_coroot, ggQ2xE6_tau_coroot, Matrix.toBilin'_single,
      ggQ2xE6_cartan_eq D e hE]
  obtain ⟨ε, hε, horth⟩ := ggQ2_S1_transport D hbas h4 hsym (ggQ2xE6_tauC D hbas e)
    (Matrix.toBilin' (ggECartan 6)) hB' A hW hTF hφ' ht'
  have hB'_apply : ∀ u v : Fin 6 → ZMod 3,
      (Matrix.toBilin' (ggECartan 6)) u v = ggEBil 6 u v :=
    fun u v => Matrix.toBilin'_apply' (ggECartan 6) u v
  have horthv : ∀ w : D.V, φ w
      = ε * ggEBil 6 (ggQ2xE6_tauC D hbas e c) (ggQ2xE6_tauC D hbas e w) := by
    intro w
    have h1 := horth (ggQ2xE6_tauC D hbas e w)
    rw [hB'_apply] at h1
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      using h1
  have hcc : ggEBil 6 (ggQ2xE6_tauC D hbas e c) (ggQ2xE6_tauC D hbas e c) ≠ 0 := by
    intro h0
    have h1 : φ c = 2 := hφ
    rw [horthv c, h0, mul_zero] at h1
    exact (by decide : (2 : ZMod 3) ≠ 0) h1.symm
  have hε2 : ε = 2 / ggEBil 6 (ggQ2xE6_tauC D hbas e c)
      (ggQ2xE6_tauC D hbas e c) := by
    rw [eq_div_iff hcc]
    have h1 : φ c = ε * ggEBil 6 (ggQ2xE6_tauC D hbas e c)
        (ggQ2xE6_tauC D hbas e c) := horthv c
    rw [hφ] at h1
    exact h1.symm
  refine ⟨ggQ2xE6_tauC D hbas e c, hcc, ?_⟩
  intro v
  rw [← heq, Module.reflection_apply]
  unfold ggERefl
  have hφ'v : (φ.comp ((ggQ2xE6_tauC D hbas e).symm :
      (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] D.V).toLinearMap) v
      = ε * ggEBil 6 (ggQ2xE6_tauC D hbas e c) v := by
    rw [horth v, hB'_apply]
  rw [hφ'v, hε2]
  ring_nf

private theorem ggQ2xE6_innerE (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) :
    GGQ2QuandleInner (ggQ2xQ_isConjRefl D) (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V)) := by
  intro π hπT hinj hπ
  haveI : Finite (D.V ≃ₗ[ZMod 3] D.V) := ggQ2xE6_finiteGL D hbas e
  have hfin : (ggQ2xQ_isConjRefl D).Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  have hsurj : Set.SurjOn π (ggQ2xQ_isConjRefl D) (ggQ2xQ_isConjRefl D) :=
    ((hfin.injOn_iff_bijOn_of_mapsTo hπT).mp hinj).surjOn
  exact ggQ2_quandle_aut_E D hbas (Or.inl ⟨e, hE⟩) π hπT hinj hsurj hπ

private def ggQ2xE6_rho : Fin 6 → ZMod 3 := ![1, 0, 2, 0, 1, 2]

private lemma ggQ2xE6a_mulVec_rho_zero : (ggECartan 6).mulVec ggQ2xE6_rho = 0 := by
  decide +kernel

private lemma ggQ2xE6z_rho_ne_zero : ggQ2xE6_rho ≠ 0 := by
  decide +kernel

private lemma ggQ2xE6a_cartan_isSymm : (ggECartan 6).IsSymm := by
  decide +kernel

private lemma ggQ2xE6_rho_rad (v : Fin 6 → ZMod 3) : ggEBil 6 ggQ2xE6_rho v = 0 := by
  unfold ggEBil
  rw [Matrix.IsSymm.dotProduct_mulVec_comm ggQ2xE6a_cartan_isSymm,
    ggQ2xE6a_mulVec_rho_zero]
  simp

private lemma ggQ2xE6z_bil_add_right (u v v' : Fin 6 → ZMod 3) :
    ggEBil 6 u (v + v') = ggEBil 6 u v + ggEBil 6 u v' := by
  unfold ggEBil
  rw [Matrix.mulVec_add, dotProduct_add]

private lemma ggQ2xE6z_bil_add_left (u u' v : Fin 6 → ZMod 3) :
    ggEBil 6 (u + u') v = ggEBil 6 u v + ggEBil 6 u' v := by
  unfold ggEBil
  rw [add_dotProduct]

private lemma ggQ2xE6z_bil_rho_right (u : Fin 6 → ZMod 3) :
    ggEBil 6 u ggQ2xE6_rho = 0 :=
  (ggQ2xE6_bil_symm u ggQ2xE6_rho).trans (ggQ2xE6_rho_rad u)

private lemma ggQ2xE6z_shift_self_iso (z : Fin 6 → ZMod 3) (l : ZMod 3) :
    ggEBil 6 (z + l • ggQ2xE6_rho) (z + l • ggQ2xE6_rho) = ggEBil 6 z z := by
  rw [ggQ2xE6z_bil_add_left, ggQ2xE6z_bil_add_right, ggQ2xE6z_bil_add_right]
  rw [ggQ2xE6_bil_smul_left, ggQ2xE6_bil_smul_right, ggQ2xE6_bil_smul_right]
  simp only [ggQ2xE6_rho_rad, ggQ2xE6z_bil_rho_right, mul_zero, zero_add, add_zero]

private lemma ggQ2xE6z_shift_bil (z : Fin 6 → ZMod 3) (l : ZMod 3) (v : Fin 6 → ZMod 3) :
    ggEBil 6 (z + l • ggQ2xE6_rho) v = ggEBil 6 z v := by
  rw [ggQ2xE6z_bil_add_left, ggQ2xE6_bil_smul_left, ggQ2xE6_rho_rad v, mul_zero, add_zero]

private lemma ggQ2xE6z_refl_refl (z : Fin 6 → ZMod 3) (hz : ggEBil 6 z z ≠ 0) (c : ZMod 3)
    (hc : c * ggEBil 6 z z = 2) (l : ZMod 3) (v : Fin 6 → ZMod 3) :
    ggERefl 6 z (ggERefl 6 (z + l • ggQ2xE6_rho) v)
      = v + (-(c * l) * ggEBil 6 z v) • ggQ2xE6_rho := by
  have hdiv : ∀ A : ZMod 3, 2 * A / ggEBil 6 z z = c * A := by
    intro A
    rw [eq_comm, eq_div_iff hz]
    rw [show c * A * ggEBil 6 z z = 2 * A by
      rw [show c * A * ggEBil 6 z z = A * (c * ggEBil 6 z z) by ring, hc]
      ring]
  have hρ' : ∀ u : Fin 6 → ZMod 3, ggERefl 6 (z + l • ggQ2xE6_rho) u
      = u - (c * ggEBil 6 z u) • (z + l • ggQ2xE6_rho) := by
    intro u
    unfold ggERefl
    rw [ggQ2xE6z_shift_self_iso z l, ggQ2xE6z_shift_bil z l u, hdiv (ggEBil 6 z u)]
  have hzX : ggEBil 6 z (v - (c * ggEBil 6 z v) • (z + l • ggQ2xE6_rho))
      = -ggEBil 6 z v := by
    rw [ggQ2xE6_bil_sub_right, ggQ2xE6_bil_smul_right]
    rw [show ggEBil 6 z (z + l • ggQ2xE6_rho) = ggEBil 6 z z by
      rw [ggQ2xE6z_bil_add_right, ggQ2xE6_bil_smul_right, ggQ2xE6z_bil_rho_right, mul_zero,
        add_zero]]
    rw [show ggEBil 6 z v - (c * ggEBil 6 z v) * ggEBil 6 z z = -ggEBil 6 z v by
      rw [show (c * ggEBil 6 z v) * ggEBil 6 z z
          = ggEBil 6 z v * (c * ggEBil 6 z z) by ring, hc]
      ring]
  rw [hρ' v]
  unfold ggERefl
  rw [hdiv (ggEBil 6 z (v - (c * ggEBil 6 z v) • (z + l • ggQ2xE6_rho))), hzX]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply]
  ring

private noncomputable def ggQ2xE6z_psiCoord (z : Fin 6 → ZMod 3) (c l : ZMod 3) :
    Module.Dual (ZMod 3) (Fin 6 → ZMod 3) where
  toFun v := -(c * l) * ggEBil 6 z v
  map_add' u v := by rw [ggQ2xE6z_bil_add_right]; ring
  map_smul' a u := by
    rw [ggQ2xE6_bil_smul_right]
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

private noncomputable def ggQ2xE6z_psiD (D : GGQ2Lin 3)
    (τ : D.V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)) (z : Fin 6 → ZMod 3) (c l : ZMod 3) :
    Module.Dual (ZMod 3) D.V :=
  (ggQ2xE6z_psiCoord z c l).comp τ.toLinearMap

private lemma ggQ2xE6_Z_lift (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hTF : TransvectionFree A) {z : Fin 6 → ZMod 3}
    (hz : z ∈ ggQ2xE6_Z D (ggQ2xE6_tauC D hbas e) A) {l : ZMod 3} (hl : l ≠ 0) :
    z + l • ggQ2xE6_rho ∉ ggQ2xE6_Z D (ggQ2xE6_tauC D hbas e) A := by
  intro hz'
  obtain ⟨hz0, g, hgA, hg⟩ := hz
  obtain ⟨-, g', hg'A, hg'⟩ := hz'
  let τ := ggQ2xE6_tauC D hbas e
  let c : ZMod 3 := 2 / ggEBil 6 z z
  have hc : c * ggEBil 6 z z = 2 := by
    change 2 / ggEBil 6 z z * ggEBil 6 z z = 2
    exact div_mul_cancel₀ 2 hz0
  let ψ : Module.Dual (ZMod 3) (Fin 6 → ZMod 3) := ggQ2xE6z_psiCoord z c l
  let ψD : Module.Dual (ZMod 3) D.V := ggQ2xE6z_psiD D τ z c l
  have hψD : ∀ w : D.V, ψD w = ψ (τ w) := fun w => rfl
  have hcoord : ∀ v : Fin 6 → ZMod 3, ggLinConj τ (g * g') v = v + ψ v • ggQ2xE6_rho := by
    intro v
    calc ggLinConj τ (g * g') v
        = ggLinConj τ g (ggLinConj τ g' v) := by rw [map_mul, LinearEquiv.mul_apply]
      _ = ggLinConj τ g (ggERefl 6 (z + l • ggQ2xE6_rho) v) := by rw [hg']
      _ = ggERefl 6 z (ggERefl 6 (z + l • ggQ2xE6_rho) v) := by rw [hg]
      _ = v + ψ v • ggQ2xE6_rho := by
          rw [ggQ2xE6z_refl_refl z hz0 c hc l v]
          rfl
  refine hTF (g * g') (mul_mem hgA hg'A) ?_
  refine ⟨τ.symm ggQ2xE6_rho, ψD, ?_, ?_, ?_, ?_⟩
  · intro h0
    have h1 : ggQ2xE6_rho = 0 := by
      have h := congrArg (fun w : D.V => τ w) h0
      simpa using h
    exact ggQ2xE6z_rho_ne_zero h1
  · have hzτ : τ (τ.symm z) = z := LinearEquiv.apply_symm_apply τ z
    have hval : ψD (τ.symm z) = -(2 * l) := by
      rw [hψD, hzτ]
      change -(c * l) * ggEBil 6 z z = -(2 * l)
      rw [show -(c * l) * ggEBil 6 z z = -(l * (c * ggEBil 6 z z)) by ring, hc]
      ring
    have hne : ψD (τ.symm z) ≠ 0 := by
      rw [hval]
      exact neg_ne_zero.mpr (mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) hl)
    intro h0
    rw [h0] at hne
    simpa using hne
  · have hρτ : τ (τ.symm ggQ2xE6_rho) = ggQ2xE6_rho :=
      LinearEquiv.apply_symm_apply τ ggQ2xE6_rho
    rw [hψD, hρτ]
    change -(c * l) * ggEBil 6 z ggQ2xE6_rho = 0
    rw [ggQ2xE6z_bil_rho_right, mul_zero]
  · intro w
    have h := hcoord (τ w)
    rw [ggLinConj_apply, LinearEquiv.symm_apply_apply] at h
    apply τ.injective
    rw [h, map_add, map_smul, LinearEquiv.apply_symm_apply, ← hψD]

private def ggQ2xE6d_roots : List (Fin 6 → ZMod 3) :=
  [![1, 0, 0, 0, 0, 0],
   ![0, 1, 0, 0, 0, 0],
   ![0, 0, 1, 0, 0, 0],
   ![0, 0, 0, 1, 0, 0],
   ![0, 0, 0, 0, 1, 0],
   ![0, 0, 0, 0, 0, 1],
   ![2, 0, 0, 0, 0, 0],
   ![1, 0, 1, 0, 0, 0],
   ![0, 2, 0, 0, 0, 0],
   ![0, 1, 0, 1, 0, 0],
   ![0, 0, 2, 0, 0, 0],
   ![0, 0, 1, 1, 0, 0],
   ![0, 0, 0, 2, 0, 0],
   ![0, 0, 0, 1, 1, 0],
   ![0, 0, 0, 0, 2, 0],
   ![0, 0, 0, 0, 1, 1],
   ![0, 0, 0, 0, 0, 2],
   ![2, 0, 2, 0, 0, 0],
   ![1, 0, 1, 1, 0, 0],
   ![0, 2, 0, 2, 0, 0],
   ![0, 1, 1, 1, 0, 0],
   ![0, 1, 0, 1, 1, 0],
   ![0, 0, 2, 2, 0, 0],
   ![0, 0, 1, 1, 1, 0],
   ![0, 0, 0, 2, 2, 0],
   ![0, 0, 0, 1, 1, 1],
   ![0, 0, 0, 0, 2, 2],
   ![2, 0, 2, 2, 0, 0],
   ![1, 1, 1, 1, 0, 0],
   ![1, 0, 1, 1, 1, 0],
   ![0, 2, 2, 2, 0, 0],
   ![0, 2, 0, 2, 2, 0],
   ![0, 1, 1, 1, 1, 0],
   ![0, 1, 0, 1, 1, 1],
   ![0, 0, 2, 2, 2, 0],
   ![0, 0, 1, 1, 1, 1],
   ![0, 0, 0, 2, 2, 2],
   ![2, 2, 2, 2, 0, 0],
   ![2, 0, 2, 2, 2, 0],
   ![1, 1, 1, 1, 1, 0],
   ![1, 0, 1, 1, 1, 1],
   ![0, 2, 2, 2, 2, 0],
   ![0, 2, 0, 2, 2, 2],
   ![0, 1, 1, 2, 1, 0],
   ![0, 1, 1, 1, 1, 1],
   ![0, 0, 2, 2, 2, 2],
   ![2, 2, 2, 2, 2, 0],
   ![2, 0, 2, 2, 2, 2],
   ![1, 1, 1, 2, 1, 0],
   ![1, 1, 1, 1, 1, 1],
   ![0, 2, 2, 1, 2, 0],
   ![0, 2, 2, 2, 2, 2],
   ![0, 1, 1, 2, 1, 1],
   ![2, 2, 2, 1, 2, 0],
   ![2, 2, 2, 2, 2, 2],
   ![1, 1, 2, 2, 1, 0],
   ![1, 1, 1, 2, 1, 1],
   ![0, 2, 2, 1, 2, 2],
   ![0, 1, 1, 2, 2, 1],
   ![2, 2, 1, 1, 2, 0],
   ![2, 2, 2, 1, 2, 2],
   ![1, 1, 2, 2, 1, 1],
   ![1, 1, 1, 2, 2, 1],
   ![0, 2, 2, 1, 1, 2],
   ![2, 2, 1, 1, 2, 2],
   ![2, 2, 2, 1, 1, 2],
   ![1, 1, 2, 2, 2, 1],
   ![2, 2, 1, 1, 1, 2],
   ![1, 1, 2, 0, 2, 1],
   ![2, 2, 1, 0, 1, 2],
   ![1, 2, 2, 0, 2, 1],
   ![2, 1, 1, 0, 1, 2]]

private def ggQ2xE6d_parents : List (ℕ × ℕ) :=
  [(0, 0), (2, 0), (1, 1), (3, 1), (2, 2), (3, 2), (3, 3), (4, 3), (4, 4), (5, 4), (5, 5), (2, 6), (3, 7), (3, 8), (2, 9), (4, 9), (3, 10), (4, 11), (4, 12), (5, 13), (5, 14), (3, 17), (1, 18), (4, 18), (2, 19), (4, 19), (4, 20), (5, 21), (4, 22), (5, 23), (5, 24), (1, 27), (4, 27), (4, 28), (5, 29), (4, 30), (5, 31), (3, 32), (5, 32), (5, 34), (4, 37), (5, 38), (3, 39), (5, 39), (3, 41), (5, 41), (5, 43), (3, 46), (5, 46), (2, 48), (5, 48), (5, 50), (4, 52), (2, 53), (5, 53), (5, 55), (4, 56), (4, 57), (5, 59), (4, 60), (4, 61), (4, 64), (3, 66), (3, 67), (1, 68), (1, 69)]

private def ggQ2xE6d_tab2 : List ((Fin 6 → ZMod 3) × ℕ × ZMod 3 × ZMod 3) :=
  [(![0, 0, 0, 0, 0, 1], 5, 1, 0),
   (![0, 0, 0, 0, 0, 2], 5, 2, 0),
   (![0, 0, 0, 0, 1, 0], 4, 1, 0),
   (![0, 0, 0, 0, 1, 1], 15, 1, 0),
   (![0, 0, 0, 0, 2, 0], 4, 2, 0),
   (![0, 0, 0, 0, 2, 2], 15, 2, 0),
   (![0, 0, 0, 1, 0, 0], 3, 1, 0),
   (![0, 0, 0, 1, 1, 0], 13, 1, 0),
   (![0, 0, 0, 1, 1, 1], 25, 1, 0),
   (![0, 0, 0, 2, 0, 0], 3, 2, 0),
   (![0, 0, 0, 2, 2, 0], 13, 2, 0),
   (![0, 0, 0, 2, 2, 2], 25, 2, 0),
   (![0, 0, 1, 0, 0, 0], 2, 1, 0),
   (![0, 0, 1, 0, 1, 2], 7, 2, 1),
   (![0, 0, 1, 0, 2, 1], 0, 1, 2),
   (![0, 0, 1, 1, 0, 0], 11, 1, 0),
   (![0, 0, 1, 1, 1, 0], 23, 1, 0),
   (![0, 0, 1, 1, 1, 1], 35, 1, 0),
   (![0, 0, 1, 2, 0, 1], 40, 2, 1),
   (![0, 0, 1, 2, 0, 2], 29, 2, 1),
   (![0, 0, 1, 2, 1, 2], 18, 2, 1),
   (![0, 0, 2, 0, 0, 0], 2, 2, 0),
   (![0, 0, 2, 0, 1, 2], 0, 2, 1),
   (![0, 0, 2, 0, 2, 1], 7, 1, 2),
   (![0, 0, 2, 1, 0, 1], 29, 1, 2),
   (![0, 0, 2, 1, 0, 2], 40, 1, 2),
   (![0, 0, 2, 1, 2, 1], 18, 1, 2),
   (![0, 0, 2, 2, 0, 0], 11, 2, 0),
   (![0, 0, 2, 2, 2, 0], 23, 2, 0),
   (![0, 0, 2, 2, 2, 2], 35, 2, 0),
   (![0, 1, 0, 0, 0, 0], 1, 1, 0),
   (![0, 1, 0, 0, 1, 2], 68, 1, 2),
   (![0, 1, 0, 0, 2, 1], 70, 2, 1),
   (![0, 1, 0, 1, 0, 0], 9, 1, 0),
   (![0, 1, 0, 1, 1, 0], 21, 1, 0),
   (![0, 1, 0, 1, 1, 1], 33, 1, 0),
   (![0, 1, 0, 2, 0, 1], 55, 1, 2),
   (![0, 1, 0, 2, 0, 2], 61, 1, 2),
   (![0, 1, 0, 2, 1, 2], 66, 1, 2),
   (![0, 1, 1, 1, 0, 0], 20, 1, 0),
   (![0, 1, 1, 1, 1, 0], 32, 1, 0),
   (![0, 1, 1, 1, 1, 1], 44, 1, 0),
   (![0, 1, 1, 2, 1, 0], 43, 1, 0),
   (![0, 1, 1, 2, 1, 1], 52, 1, 0),
   (![0, 1, 1, 2, 2, 1], 58, 1, 0),
   (![0, 1, 2, 1, 0, 1], 39, 1, 2),
   (![0, 1, 2, 1, 0, 2], 49, 1, 2),
   (![0, 1, 2, 1, 2, 1], 28, 1, 2),
   (![0, 1, 2, 2, 0, 1], 48, 1, 2),
   (![0, 1, 2, 2, 0, 2], 56, 1, 2),
   (![0, 1, 2, 2, 1, 2], 62, 1, 2),
   (![0, 2, 0, 0, 0, 0], 1, 2, 0),
   (![0, 2, 0, 0, 1, 2], 70, 1, 2),
   (![0, 2, 0, 0, 2, 1], 68, 2, 1),
   (![0, 2, 0, 1, 0, 1], 61, 2, 1),
   (![0, 2, 0, 1, 0, 2], 55, 2, 1),
   (![0, 2, 0, 1, 2, 1], 66, 2, 1),
   (![0, 2, 0, 2, 0, 0], 9, 2, 0),
   (![0, 2, 0, 2, 2, 0], 21, 2, 0),
   (![0, 2, 0, 2, 2, 2], 33, 2, 0),
   (![0, 2, 1, 1, 0, 1], 56, 2, 1),
   (![0, 2, 1, 1, 0, 2], 48, 2, 1),
   (![0, 2, 1, 1, 2, 1], 62, 2, 1),
   (![0, 2, 1, 2, 0, 1], 49, 2, 1),
   (![0, 2, 1, 2, 0, 2], 39, 2, 1),
   (![0, 2, 1, 2, 1, 2], 28, 2, 1),
   (![0, 2, 2, 1, 1, 2], 58, 2, 0),
   (![0, 2, 2, 1, 2, 0], 43, 2, 0),
   (![0, 2, 2, 1, 2, 2], 52, 2, 0),
   (![0, 2, 2, 2, 0, 0], 20, 2, 0),
   (![0, 2, 2, 2, 2, 0], 32, 2, 0),
   (![0, 2, 2, 2, 2, 2], 44, 2, 0),
   (![1, 0, 0, 0, 0, 0], 0, 1, 0),
   (![1, 0, 0, 0, 1, 2], 2, 1, 1),
   (![1, 0, 0, 0, 2, 1], 7, 2, 2),
   (![1, 0, 0, 1, 1, 2], 11, 1, 1),
   (![1, 0, 0, 1, 2, 0], 35, 1, 1),
   (![1, 0, 0, 1, 2, 2], 23, 1, 1),
   (![1, 0, 0, 2, 1, 0], 40, 2, 2),
   (![1, 0, 0, 2, 1, 1], 29, 2, 2),
   (![1, 0, 0, 2, 2, 1], 18, 2, 2),
   (![1, 0, 1, 0, 0, 0], 7, 1, 0),
   (![1, 0, 1, 0, 1, 2], 2, 2, 1),
   (![1, 0, 1, 0, 2, 1], 0, 2, 2),
   (![1, 0, 1, 1, 0, 0], 18, 1, 0),
   (![1, 0, 1, 1, 1, 0], 29, 1, 0),
   (![1, 0, 1, 1, 1, 1], 40, 1, 0),
   (![1, 0, 1, 2, 0, 1], 35, 2, 1),
   (![1, 0, 1, 2, 0, 2], 23, 2, 1),
   (![1, 0, 1, 2, 1, 2], 11, 2, 1),
   (![1, 0, 2, 0, 0, 1], 15, 2, 1),
   (![1, 0, 2, 0, 0, 2], 4, 2, 1),
   (![1, 0, 2, 0, 1, 0], 5, 1, 1),
   (![1, 0, 2, 0, 1, 1], 5, 2, 1),
   (![1, 0, 2, 0, 2, 0], 15, 1, 1),
   (![1, 0, 2, 0, 2, 2], 4, 1, 1),
   (![1, 0, 2, 1, 1, 2], 3, 1, 1),
   (![1, 0, 2, 1, 2, 0], 25, 1, 1),
   (![1, 0, 2, 1, 2, 2], 13, 1, 1),
   (![1, 0, 2, 2, 0, 1], 25, 2, 1),
   (![1, 0, 2, 2, 0, 2], 13, 2, 1),
   (![1, 0, 2, 2, 1, 2], 3, 2, 1),
   (![1, 1, 0, 1, 1, 2], 20, 1, 1),
   (![1, 1, 0, 1, 2, 0], 44, 1, 1),
   (![1, 1, 0, 1, 2, 2], 32, 1, 1),
   (![1, 1, 0, 2, 0, 0], 58, 1, 1),
   (![1, 1, 0, 2, 2, 0], 52, 1, 1),
   (![1, 1, 0, 2, 2, 2], 43, 1, 1),
   (![1, 1, 1, 1, 0, 0], 28, 1, 0),
   (![1, 1, 1, 1, 1, 0], 39, 1, 0),
   (![1, 1, 1, 1, 1, 1], 49, 1, 0),
   (![1, 1, 1, 2, 1, 0], 48, 1, 0),
   (![1, 1, 1, 2, 1, 1], 56, 1, 0),
   (![1, 1, 1, 2, 2, 1], 62, 1, 0),
   (![1, 1, 2, 0, 0, 0], 70, 2, 2),
   (![1, 1, 2, 0, 1, 2], 1, 1, 1),
   (![1, 1, 2, 0, 2, 1], 68, 1, 0),
   (![1, 1, 2, 1, 1, 2], 9, 1, 1),
   (![1, 1, 2, 1, 2, 0], 33, 1, 1),
   (![1, 1, 2, 1, 2, 2], 21, 1, 1),
   (![1, 1, 2, 2, 1, 0], 55, 1, 0),
   (![1, 1, 2, 2, 1, 1], 61, 1, 0),
   (![1, 1, 2, 2, 2, 1], 66, 1, 0),
   (![1, 2, 0, 1, 0, 0], 62, 2, 2),
   (![1, 2, 0, 1, 1, 0], 56, 2, 2),
   (![1, 2, 0, 1, 1, 1], 48, 2, 2),
   (![1, 2, 0, 2, 1, 0], 49, 2, 2),
   (![1, 2, 0, 2, 1, 1], 39, 2, 2),
   (![1, 2, 0, 2, 2, 1], 28, 2, 2),
   (![1, 2, 1, 1, 0, 1], 52, 2, 1),
   (![1, 2, 1, 1, 0, 2], 43, 2, 1),
   (![1, 2, 1, 1, 2, 1], 58, 2, 1),
   (![1, 2, 1, 2, 0, 1], 44, 2, 1),
   (![1, 2, 1, 2, 0, 2], 32, 2, 1),
   (![1, 2, 1, 2, 1, 2], 20, 2, 1),
   (![1, 2, 2, 0, 0, 0], 68, 2, 2),
   (![1, 2, 2, 0, 1, 2], 1, 2, 1),
   (![1, 2, 2, 0, 2, 1], 70, 1, 0),
   (![1, 2, 2, 1, 0, 0], 66, 2, 2),
   (![1, 2, 2, 1, 1, 0], 61, 2, 2),
   (![1, 2, 2, 1, 1, 1], 55, 2, 2),
   (![1, 2, 2, 2, 0, 1], 33, 2, 1),
   (![1, 2, 2, 2, 0, 2], 21, 2, 1),
   (![1, 2, 2, 2, 1, 2], 9, 2, 1),
   (![2, 0, 0, 0, 0, 0], 0, 2, 0),
   (![2, 0, 0, 0, 1, 2], 7, 1, 1),
   (![2, 0, 0, 0, 2, 1], 2, 2, 2),
   (![2, 0, 0, 1, 1, 2], 18, 1, 1),
   (![2, 0, 0, 1, 2, 0], 40, 1, 1),
   (![2, 0, 0, 1, 2, 2], 29, 1, 1),
   (![2, 0, 0, 2, 1, 0], 35, 2, 2),
   (![2, 0, 0, 2, 1, 1], 23, 2, 2),
   (![2, 0, 0, 2, 2, 1], 11, 2, 2),
   (![2, 0, 1, 0, 0, 1], 4, 1, 2),
   (![2, 0, 1, 0, 0, 2], 15, 1, 2),
   (![2, 0, 1, 0, 1, 0], 15, 2, 2),
   (![2, 0, 1, 0, 1, 1], 4, 2, 2),
   (![2, 0, 1, 0, 2, 0], 5, 2, 2),
   (![2, 0, 1, 0, 2, 2], 5, 1, 2),
   (![2, 0, 1, 1, 0, 1], 13, 1, 2),
   (![2, 0, 1, 1, 0, 2], 25, 1, 2),
   (![2, 0, 1, 1, 2, 1], 3, 1, 2),
   (![2, 0, 1, 2, 1, 0], 25, 2, 2),
   (![2, 0, 1, 2, 1, 1], 13, 2, 2),
   (![2, 0, 1, 2, 2, 1], 3, 2, 2),
   (![2, 0, 2, 0, 0, 0], 7, 2, 0),
   (![2, 0, 2, 0, 1, 2], 0, 1, 1),
   (![2, 0, 2, 0, 2, 1], 2, 1, 2),
   (![2, 0, 2, 1, 0, 1], 23, 1, 2),
   (![2, 0, 2, 1, 0, 2], 35, 1, 2),
   (![2, 0, 2, 1, 2, 1], 11, 1, 2),
   (![2, 0, 2, 2, 0, 0], 18, 2, 0),
   (![2, 0, 2, 2, 2, 0], 29, 2, 0),
   (![2, 0, 2, 2, 2, 2], 40, 2, 0),
   (![2, 1, 0, 1, 1, 2], 28, 1, 1),
   (![2, 1, 0, 1, 2, 0], 49, 1, 1),
   (![2, 1, 0, 1, 2, 2], 39, 1, 1),
   (![2, 1, 0, 2, 0, 0], 62, 1, 1),
   (![2, 1, 0, 2, 2, 0], 56, 1, 1),
   (![2, 1, 0, 2, 2, 2], 48, 1, 1),
   (![2, 1, 1, 0, 0, 0], 68, 1, 1),
   (![2, 1, 1, 0, 1, 2], 70, 2, 0),
   (![2, 1, 1, 0, 2, 1], 1, 1, 2),
   (![2, 1, 1, 1, 0, 1], 21, 1, 2),
   (![2, 1, 1, 1, 0, 2], 33, 1, 2),
   (![2, 1, 1, 1, 2, 1], 9, 1, 2),
   (![2, 1, 1, 2, 0, 0], 66, 1, 1),
   (![2, 1, 1, 2, 2, 0], 61, 1, 1),
   (![2, 1, 1, 2, 2, 2], 55, 1, 1),
   (![2, 1, 2, 1, 0, 1], 32, 1, 2),
   (![2, 1, 2, 1, 0, 2], 44, 1, 2),
   (![2, 1, 2, 1, 2, 1], 20, 1, 2),
   (![2, 1, 2, 2, 0, 1], 43, 1, 2),
   (![2, 1, 2, 2, 0, 2], 52, 1, 2),
   (![2, 1, 2, 2, 1, 2], 58, 1, 2),
   (![2, 2, 0, 1, 0, 0], 58, 2, 2),
   (![2, 2, 0, 1, 1, 0], 52, 2, 2),
   (![2, 2, 0, 1, 1, 1], 43, 2, 2),
   (![2, 2, 0, 2, 1, 0], 44, 2, 2),
   (![2, 2, 0, 2, 1, 1], 32, 2, 2),
   (![2, 2, 0, 2, 2, 1], 20, 2, 2),
   (![2, 2, 1, 0, 0, 0], 70, 1, 1),
   (![2, 2, 1, 0, 1, 2], 68, 2, 0),
   (![2, 2, 1, 0, 2, 1], 1, 2, 2),
   (![2, 2, 1, 1, 1, 2], 66, 2, 0),
   (![2, 2, 1, 1, 2, 0], 55, 2, 0),
   (![2, 2, 1, 1, 2, 2], 61, 2, 0),
   (![2, 2, 1, 2, 1, 0], 33, 2, 2),
   (![2, 2, 1, 2, 1, 1], 21, 2, 2),
   (![2, 2, 1, 2, 2, 1], 9, 2, 2),
   (![2, 2, 2, 1, 1, 2], 62, 2, 0),
   (![2, 2, 2, 1, 2, 0], 48, 2, 0),
   (![2, 2, 2, 1, 2, 2], 56, 2, 0),
   (![2, 2, 2, 2, 0, 0], 28, 2, 0),
   (![2, 2, 2, 2, 2, 0], 39, 2, 0),
   (![2, 2, 2, 2, 2, 2], 49, 2, 0)]

private def ggQ2xE6d_tab1 : List ((Fin 6 → ZMod 3) × ℕ × ℕ × ZMod 3 × ZMod 3) :=
  [(![0, 0, 0, 1, 0, 1], 1, 64, 1, 1),
   (![0, 0, 0, 1, 0, 2], 1, 59, 1, 1),
   (![0, 0, 0, 1, 2, 1], 1, 67, 1, 1),
   (![0, 0, 0, 2, 0, 1], 1, 59, 2, 1),
   (![0, 0, 0, 2, 0, 2], 1, 64, 2, 1),
   (![0, 0, 0, 2, 1, 2], 1, 67, 2, 1),
   (![0, 0, 1, 0, 0, 1], 0, 4, 1, 2),
   (![0, 0, 1, 0, 0, 2], 0, 15, 1, 2),
   (![0, 0, 1, 0, 1, 0], 0, 26, 1, 2),
   (![0, 0, 1, 0, 1, 1], 0, 14, 1, 2),
   (![0, 0, 1, 0, 2, 0], 0, 16, 1, 2),
   (![0, 0, 1, 0, 2, 2], 0, 5, 1, 2),
   (![0, 0, 1, 1, 0, 1], 0, 13, 1, 2),
   (![0, 0, 1, 1, 0, 2], 0, 25, 1, 2),
   (![0, 0, 1, 1, 2, 1], 0, 3, 1, 2),
   (![0, 0, 1, 2, 1, 0], 0, 36, 1, 2),
   (![0, 0, 1, 2, 1, 1], 0, 24, 1, 2),
   (![0, 0, 1, 2, 2, 1], 0, 12, 1, 2),
   (![0, 0, 2, 0, 0, 1], 0, 15, 2, 2),
   (![0, 0, 2, 0, 0, 2], 0, 4, 2, 2),
   (![0, 0, 2, 0, 1, 0], 0, 16, 2, 2),
   (![0, 0, 2, 0, 1, 1], 0, 5, 2, 2),
   (![0, 0, 2, 0, 2, 0], 0, 26, 2, 2),
   (![0, 0, 2, 0, 2, 2], 0, 14, 2, 2),
   (![0, 0, 2, 1, 1, 2], 0, 12, 2, 2),
   (![0, 0, 2, 1, 2, 0], 0, 36, 2, 2),
   (![0, 0, 2, 1, 2, 2], 0, 24, 2, 2),
   (![0, 0, 2, 2, 0, 1], 0, 25, 2, 2),
   (![0, 0, 2, 2, 0, 2], 0, 13, 2, 2),
   (![0, 0, 2, 2, 1, 2], 0, 3, 2, 2),
   (![0, 1, 0, 0, 0, 1], 3, 55, 1, 2),
   (![0, 1, 0, 0, 0, 2], 3, 61, 1, 2),
   (![0, 1, 0, 0, 1, 0], 5, 68, 1, 2),
   (![0, 1, 0, 0, 1, 1], 4, 70, 2, 2),
   (![0, 1, 0, 0, 2, 0], 5, 70, 2, 2),
   (![0, 1, 0, 0, 2, 2], 4, 68, 1, 2),
   (![0, 1, 0, 1, 0, 1], 1, 61, 2, 2),
   (![0, 1, 0, 1, 0, 2], 1, 55, 2, 2),
   (![0, 1, 0, 1, 2, 1], 1, 66, 2, 2),
   (![0, 1, 0, 2, 1, 0], 5, 66, 1, 2),
   (![0, 1, 0, 2, 1, 1], 4, 55, 1, 2),
   (![0, 1, 0, 2, 2, 1], 3, 70, 2, 2),
   (![0, 1, 1, 0, 0, 0], 0, 68, 1, 1),
   (![0, 1, 1, 0, 1, 2], 1, 17, 1, 1),
   (![0, 1, 1, 0, 2, 1], 0, 1, 1, 2),
   (![0, 1, 1, 1, 0, 1], 0, 21, 1, 2),
   (![0, 1, 1, 1, 0, 2], 0, 33, 1, 2),
   (![0, 1, 1, 1, 2, 1], 0, 9, 1, 2),
   (![0, 1, 1, 2, 0, 0], 0, 66, 1, 1),
   (![0, 1, 1, 2, 2, 0], 0, 61, 1, 1),
   (![0, 1, 1, 2, 2, 2], 0, 55, 1, 1),
   (![0, 1, 2, 0, 0, 0], 0, 70, 2, 1),
   (![0, 1, 2, 0, 1, 2], 0, 8, 2, 2),
   (![0, 1, 2, 0, 2, 1], 1, 7, 1, 2),
   (![0, 1, 2, 1, 1, 2], 0, 19, 2, 2),
   (![0, 1, 2, 1, 2, 0], 0, 42, 2, 2),
   (![0, 1, 2, 1, 2, 2], 0, 31, 2, 2),
   (![0, 1, 2, 2, 1, 0], 5, 62, 1, 2),
   (![0, 1, 2, 2, 1, 1], 4, 48, 1, 2),
   (![0, 1, 2, 2, 2, 1], 3, 28, 1, 2),
   (![0, 2, 0, 0, 0, 1], 3, 61, 2, 2),
   (![0, 2, 0, 0, 0, 2], 3, 55, 2, 2),
   (![0, 2, 0, 0, 1, 0], 5, 70, 1, 2),
   (![0, 2, 0, 0, 1, 1], 4, 68, 2, 2),
   (![0, 2, 0, 0, 2, 0], 5, 68, 2, 2),
   (![0, 2, 0, 0, 2, 2], 4, 70, 1, 2),
   (![0, 2, 0, 1, 1, 2], 3, 70, 1, 2),
   (![0, 2, 0, 1, 2, 0], 5, 66, 2, 2),
   (![0, 2, 0, 1, 2, 2], 4, 55, 2, 2),
   (![0, 2, 0, 2, 0, 1], 1, 55, 1, 2),
   (![0, 2, 0, 2, 0, 2], 1, 61, 1, 2),
   (![0, 2, 0, 2, 1, 2], 1, 66, 1, 2),
   (![0, 2, 1, 0, 0, 0], 0, 70, 1, 1),
   (![0, 2, 1, 0, 1, 2], 1, 7, 2, 2),
   (![0, 2, 1, 0, 2, 1], 0, 8, 1, 2),
   (![0, 2, 1, 1, 1, 2], 3, 28, 2, 2),
   (![0, 2, 1, 1, 2, 0], 5, 62, 2, 2),
   (![0, 2, 1, 1, 2, 2], 4, 48, 2, 2),
   (![0, 2, 1, 2, 1, 0], 0, 42, 1, 2),
   (![0, 2, 1, 2, 1, 1], 0, 31, 1, 2),
   (![0, 2, 1, 2, 2, 1], 0, 19, 1, 2),
   (![0, 2, 2, 0, 0, 0], 0, 68, 2, 1),
   (![0, 2, 2, 0, 1, 2], 0, 1, 2, 2),
   (![0, 2, 2, 0, 2, 1], 1, 17, 2, 1),
   (![0, 2, 2, 1, 0, 0], 0, 66, 2, 1),
   (![0, 2, 2, 1, 1, 0], 0, 61, 2, 1),
   (![0, 2, 2, 1, 1, 1], 0, 55, 2, 1),
   (![0, 2, 2, 2, 0, 1], 0, 33, 2, 2),
   (![0, 2, 2, 2, 0, 2], 0, 21, 2, 2),
   (![0, 2, 2, 2, 1, 2], 0, 9, 2, 2),
   (![1, 0, 0, 0, 0, 1], 2, 26, 1, 1),
   (![1, 0, 0, 0, 0, 2], 2, 14, 1, 1),
   (![1, 0, 0, 0, 1, 0], 2, 5, 1, 1),
   (![1, 0, 0, 0, 1, 1], 2, 16, 1, 1),
   (![1, 0, 0, 0, 2, 0], 2, 15, 1, 1),
   (![1, 0, 0, 0, 2, 2], 2, 4, 1, 1),
   (![1, 0, 0, 1, 0, 0], 1, 65, 1, 2),
   (![1, 0, 0, 1, 1, 0], 1, 60, 1, 2),
   (![1, 0, 0, 1, 1, 1], 1, 53, 1, 2),
   (![1, 0, 0, 2, 0, 0], 1, 63, 2, 2),
   (![1, 0, 0, 2, 2, 0], 1, 57, 2, 2),
   (![1, 0, 0, 2, 2, 2], 1, 50, 2, 2),
   (![1, 0, 1, 0, 0, 1], 0, 14, 2, 1),
   (![1, 0, 1, 0, 0, 2], 0, 26, 2, 1),
   (![1, 0, 1, 0, 1, 0], 0, 15, 2, 1),
   (![1, 0, 1, 0, 1, 1], 0, 4, 2, 1),
   (![1, 0, 1, 0, 2, 0], 0, 5, 2, 1),
   (![1, 0, 1, 0, 2, 2], 0, 16, 2, 1),
   (![1, 0, 1, 1, 0, 1], 0, 24, 2, 1),
   (![1, 0, 1, 1, 0, 2], 0, 36, 2, 1),
   (![1, 0, 1, 1, 2, 1], 0, 12, 2, 1),
   (![1, 0, 1, 2, 1, 0], 0, 25, 2, 1),
   (![1, 0, 1, 2, 1, 1], 0, 13, 2, 1),
   (![1, 0, 1, 2, 2, 1], 0, 3, 2, 1),
   (![1, 0, 2, 1, 0, 0], 1, 67, 1, 2),
   (![1, 0, 2, 1, 1, 0], 1, 64, 1, 2),
   (![1, 0, 2, 1, 1, 1], 1, 59, 1, 2),
   (![1, 0, 2, 2, 1, 0], 2, 40, 2, 1),
   (![1, 0, 2, 2, 1, 1], 2, 29, 2, 1),
   (![1, 0, 2, 2, 2, 1], 2, 18, 2, 1),
   (![1, 1, 0, 0, 0, 0], 2, 71, 1, 2),
   (![1, 1, 0, 0, 1, 2], 0, 68, 1, 2),
   (![1, 1, 0, 0, 2, 1], 0, 71, 1, 1),
   (![1, 1, 0, 1, 0, 0], 1, 62, 2, 1),
   (![1, 1, 0, 1, 1, 0], 1, 56, 2, 1),
   (![1, 1, 0, 1, 1, 1], 1, 48, 2, 1),
   (![1, 1, 0, 2, 0, 1], 0, 55, 1, 2),
   (![1, 1, 0, 2, 0, 2], 0, 61, 1, 2),
   (![1, 1, 0, 2, 1, 2], 0, 66, 1, 2),
   (![1, 1, 1, 0, 0, 0], 0, 69, 2, 2),
   (![1, 1, 1, 0, 1, 2], 1, 10, 1, 1),
   (![1, 1, 1, 0, 2, 1], 0, 8, 2, 1),
   (![1, 1, 1, 1, 0, 1], 0, 31, 2, 1),
   (![1, 1, 1, 1, 0, 2], 0, 42, 2, 1),
   (![1, 1, 1, 1, 2, 1], 0, 19, 2, 1),
   (![1, 1, 1, 2, 0, 0], 0, 67, 2, 2),
   (![1, 1, 1, 2, 2, 0], 0, 64, 2, 2),
   (![1, 1, 1, 2, 2, 2], 0, 59, 2, 2),
   (![1, 1, 2, 0, 0, 1], 1, 26, 1, 1),
   (![1, 1, 2, 0, 0, 2], 1, 14, 1, 1),
   (![1, 1, 2, 0, 1, 0], 1, 5, 1, 1),
   (![1, 1, 2, 0, 1, 1], 1, 16, 1, 1),
   (![1, 1, 2, 0, 2, 0], 1, 15, 1, 1),
   (![1, 1, 2, 0, 2, 2], 1, 4, 1, 1),
   (![1, 1, 2, 1, 0, 0], 1, 66, 2, 1),
   (![1, 1, 2, 1, 1, 0], 1, 61, 2, 1),
   (![1, 1, 2, 1, 1, 1], 1, 55, 2, 1),
   (![1, 1, 2, 2, 0, 0], 2, 63, 2, 2),
   (![1, 1, 2, 2, 2, 0], 2, 57, 2, 2),
   (![1, 1, 2, 2, 2, 2], 2, 50, 2, 2),
   (![1, 2, 0, 0, 0, 0], 2, 69, 1, 2),
   (![1, 2, 0, 0, 1, 2], 0, 70, 1, 2),
   (![1, 2, 0, 0, 2, 1], 0, 69, 1, 1),
   (![1, 2, 0, 1, 0, 1], 0, 64, 1, 1),
   (![1, 2, 0, 1, 0, 2], 0, 59, 1, 1),
   (![1, 2, 0, 1, 2, 1], 0, 67, 1, 1),
   (![1, 2, 0, 2, 0, 0], 1, 58, 1, 1),
   (![1, 2, 0, 2, 2, 0], 1, 52, 1, 1),
   (![1, 2, 0, 2, 2, 2], 1, 43, 1, 1),
   (![1, 2, 1, 0, 0, 0], 0, 71, 2, 2),
   (![1, 2, 1, 0, 1, 2], 1, 2, 2, 2),
   (![1, 2, 1, 0, 2, 1], 0, 1, 2, 1),
   (![1, 2, 1, 1, 1, 2], 3, 20, 2, 2),
   (![1, 2, 1, 1, 2, 0], 5, 58, 2, 2),
   (![1, 2, 1, 1, 2, 2], 4, 43, 2, 2),
   (![1, 2, 1, 2, 1, 0], 0, 33, 2, 1),
   (![1, 2, 1, 2, 1, 1], 0, 21, 2, 1),
   (![1, 2, 1, 2, 2, 1], 0, 9, 2, 1),
   (![1, 2, 2, 0, 0, 1], 1, 15, 2, 2),
   (![1, 2, 2, 0, 0, 2], 1, 4, 2, 2),
   (![1, 2, 2, 0, 1, 0], 1, 16, 2, 2),
   (![1, 2, 2, 0, 1, 1], 1, 5, 2, 2),
   (![1, 2, 2, 0, 2, 0], 1, 26, 2, 2),
   (![1, 2, 2, 0, 2, 2], 1, 14, 2, 2),
   (![1, 2, 2, 1, 0, 1], 2, 57, 1, 1),
   (![1, 2, 2, 1, 0, 2], 2, 50, 1, 1),
   (![1, 2, 2, 1, 2, 1], 2, 63, 1, 1),
   (![1, 2, 2, 2, 1, 0], 2, 49, 2, 1),
   (![1, 2, 2, 2, 1, 1], 2, 39, 2, 1),
   (![1, 2, 2, 2, 2, 1], 2, 28, 2, 1),
   (![2, 0, 0, 0, 0, 1], 2, 14, 2, 1),
   (![2, 0, 0, 0, 0, 2], 2, 26, 2, 1),
   (![2, 0, 0, 0, 1, 0], 2, 15, 2, 1),
   (![2, 0, 0, 0, 1, 1], 2, 4, 2, 1),
   (![2, 0, 0, 0, 2, 0], 2, 5, 2, 1),
   (![2, 0, 0, 0, 2, 2], 2, 16, 2, 1),
   (![2, 0, 0, 1, 0, 0], 1, 63, 1, 2),
   (![2, 0, 0, 1, 1, 0], 1, 57, 1, 2),
   (![2, 0, 0, 1, 1, 1], 1, 50, 1, 2),
   (![2, 0, 0, 2, 0, 0], 1, 65, 2, 2),
   (![2, 0, 0, 2, 2, 0], 1, 60, 2, 2),
   (![2, 0, 0, 2, 2, 2], 1, 53, 2, 2),
   (![2, 0, 1, 1, 1, 2], 2, 18, 1, 1),
   (![2, 0, 1, 1, 2, 0], 2, 40, 1, 1),
   (![2, 0, 1, 1, 2, 2], 2, 29, 1, 1),
   (![2, 0, 1, 2, 0, 0], 1, 67, 2, 2),
   (![2, 0, 1, 2, 2, 0], 1, 64, 2, 2),
   (![2, 0, 1, 2, 2, 2], 1, 59, 2, 2),
   (![2, 0, 2, 0, 0, 1], 0, 26, 1, 1),
   (![2, 0, 2, 0, 0, 2], 0, 14, 1, 1),
   (![2, 0, 2, 0, 1, 0], 0, 5, 1, 1),
   (![2, 0, 2, 0, 1, 1], 0, 16, 1, 1),
   (![2, 0, 2, 0, 2, 0], 0, 15, 1, 1),
   (![2, 0, 2, 0, 2, 2], 0, 4, 1, 1),
   (![2, 0, 2, 1, 1, 2], 0, 3, 1, 1),
   (![2, 0, 2, 1, 2, 0], 0, 25, 1, 1),
   (![2, 0, 2, 1, 2, 2], 0, 13, 1, 1),
   (![2, 0, 2, 2, 0, 1], 0, 36, 1, 1),
   (![2, 0, 2, 2, 0, 2], 0, 24, 1, 1),
   (![2, 0, 2, 2, 1, 2], 0, 12, 1, 1),
   (![2, 1, 0, 0, 0, 0], 2, 69, 2, 2),
   (![2, 1, 0, 0, 1, 2], 0, 69, 2, 1),
   (![2, 1, 0, 0, 2, 1], 0, 70, 2, 2),
   (![2, 1, 0, 1, 0, 0], 1, 58, 2, 1),
   (![2, 1, 0, 1, 1, 0], 1, 52, 2, 1),
   (![2, 1, 0, 1, 1, 1], 1, 43, 2, 1),
   (![2, 1, 0, 2, 0, 1], 0, 59, 2, 1),
   (![2, 1, 0, 2, 0, 2], 0, 64, 2, 1),
   (![2, 1, 0, 2, 1, 2], 0, 67, 2, 1),
   (![2, 1, 1, 0, 0, 1], 1, 4, 1, 2),
   (![2, 1, 1, 0, 0, 2], 1, 15, 1, 2),
   (![2, 1, 1, 0, 1, 0], 1, 26, 1, 2),
   (![2, 1, 1, 0, 1, 1], 1, 14, 1, 2),
   (![2, 1, 1, 0, 2, 0], 1, 16, 1, 2),
   (![2, 1, 1, 0, 2, 2], 1, 5, 1, 2),
   (![2, 1, 1, 1, 1, 2], 2, 28, 1, 1),
   (![2, 1, 1, 1, 2, 0], 2, 49, 1, 1),
   (![2, 1, 1, 1, 2, 2], 2, 39, 1, 1),
   (![2, 1, 1, 2, 0, 1], 2, 50, 2, 1),
   (![2, 1, 1, 2, 0, 2], 2, 57, 2, 1),
   (![2, 1, 1, 2, 1, 2], 2, 63, 2, 1),
   (![2, 1, 2, 0, 0, 0], 0, 71, 1, 2),
   (![2, 1, 2, 0, 1, 2], 0, 1, 1, 1),
   (![2, 1, 2, 0, 2, 1], 1, 2, 1, 2),
   (![2, 1, 2, 1, 1, 2], 0, 9, 1, 1),
   (![2, 1, 2, 1, 2, 0], 0, 33, 1, 1),
   (![2, 1, 2, 1, 2, 2], 0, 21, 1, 1),
   (![2, 1, 2, 2, 1, 0], 5, 58, 1, 2),
   (![2, 1, 2, 2, 1, 1], 4, 43, 1, 2),
   (![2, 1, 2, 2, 2, 1], 3, 20, 1, 2),
   (![2, 2, 0, 0, 0, 0], 2, 71, 2, 2),
   (![2, 2, 0, 0, 1, 2], 0, 71, 2, 1),
   (![2, 2, 0, 0, 2, 1], 0, 68, 2, 2),
   (![2, 2, 0, 1, 0, 1], 0, 61, 2, 2),
   (![2, 2, 0, 1, 0, 2], 0, 55, 2, 2),
   (![2, 2, 0, 1, 2, 1], 0, 66, 2, 2),
   (![2, 2, 0, 2, 0, 0], 1, 62, 1, 1),
   (![2, 2, 0, 2, 2, 0], 1, 56, 1, 1),
   (![2, 2, 0, 2, 2, 2], 1, 48, 1, 1),
   (![2, 2, 1, 0, 0, 1], 1, 14, 2, 1),
   (![2, 2, 1, 0, 0, 2], 1, 26, 2, 1),
   (![2, 2, 1, 0, 1, 0], 1, 15, 2, 1),
   (![2, 2, 1, 0, 1, 1], 1, 4, 2, 1),
   (![2, 2, 1, 0, 2, 0], 1, 5, 2, 1),
   (![2, 2, 1, 0, 2, 2], 1, 16, 2, 1),
   (![2, 2, 1, 1, 0, 0], 2, 63, 1, 2),
   (![2, 2, 1, 1, 1, 0], 2, 57, 1, 2),
   (![2, 2, 1, 1, 1, 1], 2, 50, 1, 2),
   (![2, 2, 1, 2, 0, 0], 1, 66, 1, 1),
   (![2, 2, 1, 2, 2, 0], 1, 61, 1, 1),
   (![2, 2, 1, 2, 2, 2], 1, 55, 1, 1),
   (![2, 2, 2, 0, 0, 0], 0, 69, 1, 2),
   (![2, 2, 2, 0, 1, 2], 0, 8, 1, 1),
   (![2, 2, 2, 0, 2, 1], 1, 10, 2, 1),
   (![2, 2, 2, 1, 0, 0], 0, 67, 1, 2),
   (![2, 2, 2, 1, 1, 0], 0, 64, 1, 2),
   (![2, 2, 2, 1, 1, 1], 0, 59, 1, 2),
   (![2, 2, 2, 2, 0, 1], 0, 42, 1, 1),
   (![2, 2, 2, 2, 0, 2], 0, 31, 1, 1),
   (![2, 2, 2, 2, 1, 2], 0, 19, 1, 1)]

private lemma ggQ2xE6d_roots_single : ∀ k : Fin 6,
    ggQ2xE6d_roots.getD k.val 0 = (Pi.single k 1 : Fin 6 → ZMod 3) := by
  decide +kernel

private lemma ggQ2xE6d_parents_ok : ∀ j : Fin 66,
    ggQ2xE6d_roots.getD (j.val + 6) 0 =
      ggESimple 6 (Fin.ofNat 6 (ggQ2xE6d_parents.getD j.val (0, 0)).1)
        (ggQ2xE6d_roots.getD (ggQ2xE6d_parents.getD j.val (0, 0)).2 0) ∧
    (ggQ2xE6d_parents.getD j.val (0, 0)).2 < j.val + 6 := by
  decide +kernel

private lemma ggQ2xE6d_tab2_ok : ∀ w ∈ ggQ2xE6d_tab2,
    w.2.1 < 72 ∧ ggEBil 6 w.1 w.1 = 2 ∧
    w.1 = w.2.2.1 • ggQ2xE6d_roots.getD w.2.1 0 + w.2.2.2 • ggQ2xE6_rho ∧
    (w.2.2.1 = 1 ∨ w.2.2.1 = -1) := by
  decide +kernel

private lemma ggQ2xE6d_tab1_ok : ∀ w ∈ ggQ2xE6d_tab1,
    w.2.1 < 72 ∧ w.2.2.1 < 72 ∧ ggEBil 6 w.1 w.1 = 1 ∧
    ggEBil 6 (ggQ2xE6d_roots.getD w.2.1 0) (ggQ2xE6d_roots.getD w.2.2.1 0) = 0 ∧
    w.1 = w.2.2.2.1 • (ggQ2xE6d_roots.getD w.2.1 0 + ggQ2xE6d_roots.getD w.2.2.1 0
        + w.2.2.2.2 • ggQ2xE6_rho) ∧
    w.2.2.2.2 ≠ 0 ∧ (w.2.2.2.1 = 1 ∨ w.2.2.2.1 = -1) := by
  decide +kernel

private lemma ggQ2xE6d_cover2_decide : ∀ z : Fin 6 → ZMod 3, ggEBil 6 z z = 2 →
    ∃ w ∈ ggQ2xE6d_tab2, w.1 = z := by
  decide +kernel

private lemma ggQ2xE6d_cover1_decide : ∀ z : Fin 6 → ZMod 3, ggEBil 6 z z = 1 →
    ∃ w ∈ ggQ2xE6d_tab1, w.1 = z := by
  decide +kernel

private lemma ggQ2xE6d_roots_mem_aux : ∀ n : ℕ, n < 72 →
    ggQ2xE6d_roots.getD n 0 ∈ ggEClosure 6 Set.univ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h6 : n < 6
    · have hk : ggQ2xE6d_roots.getD n 0 = (Pi.single ⟨n, h6⟩ 1 : Fin 6 → ZMod 3) :=
        ggQ2xE6d_roots_single ⟨n, h6⟩
      rw [hk]
      exact ggQ2xE6_closure_single Set.univ (Set.mem_univ _)
    · have h6ge : 6 ≤ n := by omega
      have hj : n - 6 < 66 := by omega
      have hp := ggQ2xE6d_parents_ok ⟨n - 6, hj⟩
      simp only [Fin.val_mk] at hp
      have h6' : n - 6 + 6 = n := by omega
      have hroot : ggQ2xE6d_roots.getD n 0 =
          ggESimple 6 (Fin.ofNat 6 (ggQ2xE6d_parents.getD (n - 6) (0, 0)).1)
            (ggQ2xE6d_roots.getD (ggQ2xE6d_parents.getD (n - 6) (0, 0)).2 0) := by
        have := hp.1
        rwa [h6'] at this
      have hlt : (ggQ2xE6d_parents.getD (n - 6) (0, 0)).2 < n := by
        have := hp.2
        omega
      rw [hroot]
      exact ggQ2xE6_closure_simple Set.univ (Set.mem_univ _)
        (ih _ hlt (by omega))

private lemma ggQ2xE6d_roots_mem (i : Fin 72) :
    ggQ2xE6d_roots.getD i.val 0 ∈ ggEClosure 6 Set.univ :=
  ggQ2xE6d_roots_mem_aux i.val i.isLt

private lemma ggQ2xE6_cover2 : ∀ z : Fin 6 → ZMod 3, ggEBil 6 z z = 2 →
    ∃ γ ∈ ggEClosure 6 Set.univ, ∃ s l : ZMod 3, (s = 1 ∨ s = -1) ∧
      z = s • γ + l • ggQ2xE6_rho := by
  intro z hz
  obtain ⟨w, hw, hwz⟩ := ggQ2xE6d_cover2_decide z hz
  obtain ⟨hgi, -, hdec, hs⟩ := ggQ2xE6d_tab2_ok w hw
  refine ⟨ggQ2xE6d_roots.getD w.2.1 0, ggQ2xE6d_roots_mem ⟨w.2.1, hgi⟩,
    w.2.2.1, w.2.2.2, hs, ?_⟩
  rw [← hwz, hdec]

private lemma ggQ2xE6_cover1 : ∀ z : Fin 6 → ZMod 3, ggEBil 6 z z = 1 →
    ∃ γ ∈ ggEClosure 6 Set.univ, ∃ δ ∈ ggEClosure 6 Set.univ, ggEBil 6 γ δ = 0 ∧
      ∃ s μ : ZMod 3, (s = 1 ∨ s = -1) ∧ μ ≠ 0 ∧ z = s • (γ + δ + μ • ggQ2xE6_rho) := by
  intro z hz
  obtain ⟨w, hw, hwz⟩ := ggQ2xE6d_cover1_decide z hz
  obtain ⟨hgi, hdi, -, horth, hdec, hmu, hs⟩ := ggQ2xE6d_tab1_ok w hw
  refine ⟨ggQ2xE6d_roots.getD w.2.1 0, ggQ2xE6d_roots_mem ⟨w.2.1, hgi⟩,
    ggQ2xE6d_roots.getD w.2.2.1 0, ggQ2xE6d_roots_mem ⟨w.2.2.1, hdi⟩,
    horth, w.2.2.2.1, w.2.2.2.2, hs, hmu, ?_⟩
  rw [← hwz, hdec]

private lemma ggQ2xE6c_bil_add_right (u v v' : Fin 6 → ZMod 3) :
    ggEBil 6 u (v + v') = ggEBil 6 u v + ggEBil 6 u v' := by
  have hneg : ggEBil 6 u (-v') = - ggEBil 6 u v' := by
    rw [show -v' = (-1 : ZMod 3) • v' by simp, ggQ2xE6_bil_smul_right]
    ring
  rw [show v + v' = v - (-v') by abel, ggQ2xE6_bil_sub_right, hneg]
  ring

private lemma ggQ2xE6c_bil_neg_right (u v : Fin 6 → ZMod 3) :
    ggEBil 6 u (-v) = - ggEBil 6 u v := by
  rw [show -v = (-1 : ZMod 3) • v by simp, ggQ2xE6_bil_smul_right]
  ring

private lemma ggQ2xE6c_refl_of_norm2 (z w : Fin 6 → ZMod 3) (hz : ggEBil 6 z z = 2) :
    ggERefl 6 z w = w - ggEBil 6 z w • z := by
  unfold ggERefl
  rw [hz, ggQ2xE6a_two_mul_div_two]

private lemma ggQ2xE6_lemE (γ δ : Fin 6 → ZMod 3) (hγ : ggEBil 6 γ γ = 2) (hδ : ggEBil 6 δ δ = 2)
    (h0 : ggEBil 6 γ δ = 0) (μ : ZMod 3) :
    ggERefl 6 δ (ggERefl 6 γ (γ + δ + μ • ggQ2xE6_rho)) = -(γ + δ - μ • ggQ2xE6_rho) := by
  have hγr : ∀ w, ggERefl 6 γ w = w - ggEBil 6 γ w • γ :=
    fun w => ggQ2xE6c_refl_of_norm2 γ w hγ
  have hδr : ∀ w, ggERefl 6 δ w = w - ggEBil 6 δ w • δ :=
    fun w => ggQ2xE6c_refl_of_norm2 δ w hδ
  have hγρ : ggEBil 6 γ ggQ2xE6_rho = 0 :=
    (ggQ2xE6_bil_symm γ ggQ2xE6_rho).trans (ggQ2xE6_rho_rad γ)
  have hδρ : ggEBil 6 δ ggQ2xE6_rho = 0 :=
    (ggQ2xE6_bil_symm δ ggQ2xE6_rho).trans (ggQ2xE6_rho_rad δ)
  have hv : ggEBil 6 γ (γ + δ + μ • ggQ2xE6_rho) = 2 := by
    rw [ggQ2xE6c_bil_add_right, ggQ2xE6c_bil_add_right, hγ, h0,
      ggQ2xE6_bil_smul_right, hγρ, mul_zero]
    ring
  have hw : ggEBil 6 δ (-γ + δ + μ • ggQ2xE6_rho) = 2 := by
    rw [ggQ2xE6c_bil_add_right, ggQ2xE6c_bil_add_right, ggQ2xE6c_bil_neg_right,
      (ggQ2xE6_bil_symm δ γ).trans h0, hδ, ggQ2xE6_bil_smul_right, hδρ, mul_zero]
    ring
  have h1 : ggERefl 6 γ (γ + δ + μ • ggQ2xE6_rho) = -γ + δ + μ • ggQ2xE6_rho := by
    rw [hγr, hv]
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1, hδr, hw]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma ggQ2xE6c_refl_self (z : Fin 6 → ZMod 3) (hz : ggEBil 6 z z ≠ 0) :
    ggERefl 6 z z = -z := by
  unfold ggERefl
  rw [show 2 * ggEBil 6 z z / ggEBil 6 z z = 2 by
    rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hz, mul_one]]
  funext i
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma ggQ2xE6_closure_neg {γ : Fin 6 → ZMod 3} (hγ : γ ∈ ggEClosure 6 Set.univ) :
    -γ ∈ ggEClosure 6 Set.univ := by
  refine ggQ2xE6_closure_ind Set.univ (fun w => -w ∈ ggEClosure 6 Set.univ) ?_ ?_ hγ
  · intro k _
    have hz : ggEBil 6 (Pi.single k 1) (Pi.single k 1) ≠ 0 := by
      rw [ggQ2xE6_bil_single_self]; decide
    have h : -(Pi.single k 1 : Fin 6 → ZMod 3) = ggESimple 6 k (Pi.single k 1) := by
      rw [← ggQ2xE6c_refl_self (Pi.single k 1) hz, ggQ2xE6_refl_single k (Pi.single k 1)]
    rw [h]
    exact ggQ2xE6_closure_simple Set.univ (Set.mem_univ k)
      (ggQ2xE6_closure_single Set.univ (Set.mem_univ k))
  · intro j _ w hw
    have h : -(ggESimple 6 j w) = ggESimple 6 j (-w) := by
      rw [show -w = (-1 : ZMod 3) • w by simp, ggQ2xE6a_simple_smul]
      simp
    rw [h]
    exact ggQ2xE6_closure_simple Set.univ (Set.mem_univ j) hw

private lemma ggQ2xE6c_zmod3_cases (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  revert a
  decide

private lemma ggQ2xE6_core (Z : Set (Fin 6 → ZMod 3)) (hZ0 : ∀ z ∈ Z, ggEBil 6 z z ≠ 0)
    (hZroots : ggEClosure 6 Set.univ ⊆ Z) (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ggERefl 6 z w ∈ Z)
    (hlift : ∀ z ∈ Z, ∀ l : ZMod 3, l ≠ 0 → z + l • ggQ2xE6_rho ∉ Z) :
    Z ⊆ ggEClosure 6 Set.univ := by
  intro z hz
  have hzz : ggEBil 6 z z ≠ 0 := hZ0 z hz
  rcases ggQ2xE6c_zmod3_cases (ggEBil 6 z z) with h0 | h1 | h2
  · exact absurd h0 hzz
  · obtain ⟨γ, hγΦ, δ, hδΦ, hγδ, s, μ, hs, hμ, hzγδ⟩ := ggQ2xE6_cover1 z h1
    have hγγ : ggEBil 6 γ γ = 2 := ggQ2xE6_closure_bil Set.univ hγΦ
    have hδδ : ggEBil 6 δ δ = 2 := ggQ2xE6_closure_bil Set.univ hδΦ
    have hγZ : γ ∈ Z := hZroots hγΦ
    have hδZ : δ ∈ Z := hZroots hδΦ
    have hwZ : ggERefl 6 δ (ggERefl 6 γ z) ∈ Z :=
      hZcl δ hδZ (ggERefl 6 γ z) (hZcl γ hγZ z hz)
    have hw : ggERefl 6 δ (ggERefl 6 γ z) = -(s • (γ + δ - μ • ggQ2xE6_rho)) := by
      rw [hzγδ, ggQ2xE6a_refl_smul γ s (γ + δ + μ • ggQ2xE6_rho),
        ggQ2xE6a_refl_smul δ s (ggERefl 6 γ (γ + δ + μ • ggQ2xE6_rho)),
        ggQ2xE6_lemE γ δ hγγ hδδ hγδ μ, smul_neg]
    have hw0 : ggEBil 6 (ggERefl 6 δ (ggERefl 6 γ z))
        (ggERefl 6 δ (ggERefl 6 γ z)) ≠ 0 := hZ0 _ hwZ
    have hnegwZ : -(ggERefl 6 δ (ggERefl 6 γ z)) ∈ Z := by
      have h := hZcl (ggERefl 6 δ (ggERefl 6 γ z)) hwZ
        (ggERefl 6 δ (ggERefl 6 γ z)) hwZ
      rwa [ggQ2xE6c_refl_self _ hw0] at h
    have hsμ : s * μ ≠ 0 := by
      apply mul_ne_zero _ hμ
      rcases hs with hs | hs <;> rw [hs] <;> decide
    have hneg_eq : -(ggERefl 6 δ (ggERefl 6 γ z)) = z + (s * μ) • ggQ2xE6_rho := by
      rw [hw, hzγδ, neg_neg]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      have h3 : (3 : ZMod 3) = 0 := by decide
      linear_combination (-(s * μ * ggQ2xE6_rho i)) * h3
    exact absurd (hneg_eq ▸ hnegwZ) (hlift z hz (s * μ) hsμ)
  · obtain ⟨γ, hγΦ, s, l, hs, hzγ⟩ := ggQ2xE6_cover2 z h2
    have hsγΦ : s • γ ∈ ggEClosure 6 Set.univ := by
      rcases hs with hs | hs
      · rw [hs, one_smul]; exact hγΦ
      · rw [hs, show (-1 : ZMod 3) • γ = -γ by simp]; exact ggQ2xE6_closure_neg hγΦ
    have hsγZ : s • γ ∈ Z := hZroots hsγΦ
    by_cases hl : l = 0
    · rw [hzγ, hl, zero_smul, add_zero]; exact hsγΦ
    · exact absurd (show s • γ + l • ggQ2xE6_rho ∈ Z by rw [← hzγ]; exact hz)
        (hlift (s • γ) hsγZ l hl)

private lemma ggQ2xE6_Z_eq (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ggQ2xE6_Z D (ggQ2xE6_tauC D hbas e) A = ggEClosure 6 Set.univ := by
  refine Set.Subset.antisymm ?_ (ggQ2xE6_Z_roots D hbas e hE A hW)
  exact ggQ2xE6_core _ (fun z hz => hz.1) (ggQ2xE6_Z_roots D hbas e hE A hW)
    (ggQ2xE6_Z_closed D hbas e A) (fun z hz l hl => ggQ2xE6_Z_lift D hbas e hE A hTF hz hl)

private lemma ggQ2xE6_reflSet (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ggReflSet A = ggQ2xQ_isConjRefl D := by
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨z, hz0, hzt⟩ := ggQ2xE6_refl_centre D hbas e hE A hW hTF ht
    have hzZ : z ∈ ggQ2xE6_Z D (ggQ2xE6_tauC D hbas e) A := ⟨hz0, t, ht.1, hzt⟩
    rw [ggQ2xE6_Z_eq D hbas e hE A hW hTF] at hzZ
    obtain ⟨k, -, w, hw, hwz⟩ := ggQ2xE6_refl_mem D hbas e hE Set.univ hzZ
    have hwW : w ∈ D.weyl := by
      have h1 : D.parab (e '' (Set.univ : Set (Fin 6))) = D.weyl := by
        rw [Set.image_univ_of_surjective e.surjective]
        rfl
      rwa [h1] at hw
    refine ⟨e k, w, hwW, ?_⟩
    apply (ggLinConj (ggQ2xE6_tauC D hbas e)).injective
    apply LinearEquiv.ext
    intro v
    rw [hzt v, hwz v]
  · rintro t ⟨k, w, hw, rfl⟩
    have hCsym : ∀ i j, D.cartan i j = D.cartan j i :=
      ggQ2xQ_cartan_symm_of_reindex CoxeterMatrix.E₆
        (by intro a b; fin_cases a <;> fin_cases b <;> decide) D e hE
    refine ⟨hW (Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (ggQ2xQ_simpleRefl_mem_weyl D k))
      (Subgroup.inv_mem _ hw)), ?_⟩
    obtain ⟨h, heq⟩ := ggQ2xQ_conj_simpleRefl D hbas hCsym k hw
    exact ⟨w (D.coroot k), ggQ2xQ_form D hbas (w (D.coroot k)), h, heq⟩

theorem ggQ2xE6_main (D : GGQ2Lin 3) (hbas : D.Basis) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ∀ a ∈ A, ∃ g ∈ D.weyl, (∀ v, a v = g v) ∨ (∀ v, a v = -(g v)) := by
  have h4 : 4 ≤ Fintype.card D.ι := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  have hinner : GGQ2QuandleInner (ggReflSet A) (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V)) := by
    have h0 := ggQ2xE6_innerE D hbas e hE
    rwa [← ggQ2xE6_reflSet D hbas e hE A hW hTF] at h0
  exact ggQ2_transfer (p := 3) rfl D hbas h4 A hW (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V)) hinner

theorem ggQ2_caseII_E6_pm (D : GGQ2Lin 3) (hsym : ∀ i j, D.cartan i j = D.cartan j i)
    (hII : D.CaseII) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (ha : D.a = e 0 ∨ D.a = e 5) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ a ∈ A.map ggContra, ∃ g ∈ (D.dual hsym).weyl,
      (∀ f, a f = g f) ∨ (∀ f, a f = -(g f)) := by
  have h4 : 4 ≤ Fintype.card D.ι := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  have hnon := ggQ2_caseII_nonsplit D hII h4 x hx A hW hHL
  haveI : FiniteDimensional (ZMod 3) D.V :=
    Module.finite_of_finrank_pos (by rw [← hII.1]; omega)
  have hbas' : (D.dual hsym).Basis := (ggQ2_dual_basis_iff D hsym hII.1).mpr hnon
  have hWd : (D.dual hsym).weyl ≤ A.map ggContra := by
    rw [← ggContra_weyl D hsym]
    exact Subgroup.map_mono hW
  exact ggQ2xE6_main (D.dual hsym) hbas' e hE (A.map ggContra) hWd
    (ggContra_transvectionFree hTF)

end CFSG.StandardType

end
