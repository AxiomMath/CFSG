module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivKindDiag
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerCenter
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux3

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open scoped Matrix

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}

noncomputable def qTwoChartMatch_permHom : Equiv.Perm (Fin m) →* Su F0 2 1 m where
  toFun σ := ggPermSU σ⁻¹
  map_one' := by
    rw [inv_one]
    apply Subtype.ext
    apply Units.ext
    change ((1 : Equiv.Perm (Fin m)).permMatrix F0) = 1
    rw [Matrix.permMatrix_one]
  map_mul' σ τ := by
    rw [mul_inv_rev]
    exact ggNSPosPA_permSU_mul_anti' (K := F0) (f := 1) τ⁻¹ σ⁻¹

private theorem qTwoChartMatch_permHom_coe (σ : Equiv.Perm (Fin m)) :
    (((qTwoChartMatch_permHom (F0 := F0) σ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = (σ⁻¹).permMatrix F0 := rfl

private theorem qTwoChartMatch_permHom_inv_coe (σ : Equiv.Perm (Fin m)) :
    (((qTwoChartMatch_permHom (F0 := F0) σ : GL (Fin m) F0)⁻¹ :
      GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = σ.permMatrix F0 := by
  rw [← Subgroup.coe_inv, ← map_inv, qTwoChartMatch_permHom_coe, inv_inv]

theorem qTwoChartMatch_permHom_mulVec (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (((qTwoChartMatch_permHom (F0 := F0) σ : Su F0 2 1 m) : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 = Pi.single (σ i) 1 := by
  rw [qTwoChartMatch_permHom_coe, Matrix.permMatrix_mulVec]
  funext k
  rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : k = σ i
  · rw [if_pos (Equiv.Perm.inv_eq_iff_eq.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (Equiv.Perm.inv_eq_iff_eq.mp h')), if_neg h]

theorem qTwoChartMatch_diag_commute {g h : GL (Fin m) F0} (hg : ggIsDiagMat g)
    (hh : ggIsDiagMat h) : g * h = h * g := by
  obtain ⟨d, hd⟩ := hg
  obtain ⟨e, he⟩ := hh
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hd, he, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm (d i) (e i)

theorem qTwoChartMatch_conj_diag (σ : Equiv.Perm (Fin m)) {g : GL (Fin m) F0}
    {d : Fin m → F0} (hd : (g : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal d) :
    (((qTwoChartMatch_permHom (F0 := F0) σ : GL (Fin m) F0) * g *
        (qTwoChartMatch_permHom (F0 := F0) σ : GL (Fin m) F0)⁻¹ : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = Matrix.diagonal (fun i => d (σ⁻¹ i)) := by
  rw [Units.val_mul, Units.val_mul, qTwoChartMatch_permHom_coe, hd,
    qTwoChartMatch_permHom_inv_coe]
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [Matrix.submatrix, Matrix.diagonal_apply]

private theorem qTwoChartMatch_commutator_GL_coe (σ : Equiv.Perm (Fin m))
    {g : GL (Fin m) F0} {e : Fin m → F0}
    (he : (g : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal e) :
    (((qTwoChartMatch_permHom (F0 := F0) σ : GL (Fin m) F0) * g *
        (qTwoChartMatch_permHom (F0 := F0) σ : GL (Fin m) F0)⁻¹ * g⁻¹ :
      GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (fun j => e (σ⁻¹ j) * Ring.inverse e j) := by
  rw [Units.val_mul, qTwoChartMatch_conj_diag σ he]
  have hginv : ((g⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (Ring.inverse e) := by
    rw [Matrix.coe_units_inv, he, Matrix.inv_diagonal]
  rw [hginv, Matrix.diagonal_mul_diagonal]

theorem qTwoChartMatch_isDiag_commutator (σ : Equiv.Perm (Fin m)) {g : GL (Fin m) F0}
    (hg : ggIsDiagMat g) :
    ggIsDiagMat ((qTwoChartMatch_permHom (F0 := F0) σ : GL (Fin m) F0) * g *
      (qTwoChartMatch_permHom (F0 := F0) σ : GL (Fin m) F0)⁻¹ * g⁻¹) := by
  obtain ⟨d, hd⟩ := hg
  exact ⟨fun i => d (σ⁻¹ i) * Ring.inverse d i, qTwoChartMatch_commutator_GL_coe σ hd⟩

private theorem qTwoChartMatch_prod_update_two {i k : Fin m} (hik : i ≠ k) (a b : F0) :
    ∏ x, Function.update (Function.update (1 : Fin m → F0) i a) k b x = a * b := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ k)]
  rw [Finset.prod_update_of_mem (by simp [hik])]
  simp [mul_comm]

private noncomputable def qTwoChartMatch_diagTwo (hF : Nat.card F0 = 4) {i k : Fin m}
    (hik : i ≠ k) (a : F0ˣ) : Su F0 2 1 m :=
  ggNSPosPB2_diagSU
    (Function.update (Function.update (1 : Fin m → F0) i (a : F0)) k
      ((a⁻¹ : F0ˣ) : F0))
    (by
      rw [qTwoChartMatch_prod_update_two hik]
      exact Units.val_inv a)
    (by
      intro x
      by_cases hxi : x = i
      · subst hxi
        rw [Function.update_of_ne hik, Function.update_self]
        exact qTwoLMDivKind_norm_eq_one hF a.ne_zero
      · by_cases hxk : x = k
        · subst hxk
          rw [Function.update_self]
          exact qTwoLMDivKind_norm_eq_one hF (Units.ne_zero (a⁻¹))
        · rw [Function.update_of_ne hxk, Function.update_of_ne hxi]
          simp)

private theorem qTwoChartMatch_diagTwo_coe (hF : Nat.card F0 = 4) {i k : Fin m}
    (hik : i ≠ k) (a : F0ˣ) :
    (((qTwoChartMatch_diagTwo hF hik a : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal (Function.update (Function.update (1 : Fin m → F0) i (a : F0)) k
        ((a⁻¹ : F0ˣ) : F0)) :=
  ggNSPosPB2_diagSU_coe _ _ _

private theorem qTwoChartMatch_swap_update_apply {i j : Fin m} (hij : i ≠ j) {e : Fin m → F0}
    (hene : ∀ x, e x ≠ 0) (c : F0ˣ) (hc : (c : F0) = e j / e i) :
    (fun x => e (Equiv.swap i j x) * Ring.inverse (e x)) =
      Function.update (Function.update (1 : Fin m → F0) i (c : F0)) j ((c⁻¹ : F0ˣ) : F0) := by
  funext x
  by_cases hxi : x = i
  · subst hxi
    rw [Equiv.swap_apply_left, Function.update_of_ne hij, Function.update_self]
    rw [Ring.inverse_eq_inv, hc, div_eq_mul_inv]
  · by_cases hxj : x = j
    · subst hxj
      rw [Equiv.swap_apply_right, Function.update_self]
      rw [Ring.inverse_eq_inv, Units.val_inv_eq_inv_val, hc, div_eq_mul_inv, mul_inv_rev,
        inv_inv]
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
      rw [Function.update_of_ne hxj, Function.update_of_ne hxi]
      rw [Ring.inverse_eq_inv]
      exact mul_inv_cancel₀ (hene x)

private theorem qTwoChartMatch_ringInverse_apply_eq {e : Fin m → F0} (he : IsUnit e) (x : Fin m) :
    Ring.inverse e x = Ring.inverse (e x) := by
  rw [Ring.inverse_of_isUnit he, Units.val_inv_eq_inv_val, Pi.inv_apply,
    IsUnit.unit_spec, Ring.inverse_eq_inv]

theorem qTwoChartMatch_exists_finset_swap_commutator (hF : Nat.card F0 = 4) {i j : Fin m}
    (hij : i ≠ j) :
    ∃ S : Finset (Su F0 2 1 m), S.card ≤ 3 ∧
      ∀ g : GL (Fin m) F0, ggIsDiagMat g → ∀ d : Su F0 2 1 m,
        (d : GL (Fin m) F0) =
            (qTwoChartMatch_permHom (F0 := F0) (Equiv.swap i j) : GL (Fin m) F0) * g *
              (qTwoChartMatch_permHom (F0 := F0) (Equiv.swap i j) : GL (Fin m) F0)⁻¹ * g⁻¹ →
          d ∈ S := by
  classical
  letI : Fintype F0 := Fintype.ofFinite F0
  letI : Fintype F0ˣ := Fintype.ofFinite F0ˣ
  let S : Finset (Su F0 2 1 m) :=
    Finset.univ.image (fun a : F0ˣ => qTwoChartMatch_diagTwo hF hij a)
  refine ⟨S, ?_, ?_⟩
  · have hcard : Nat.card F0ˣ = 3 := by rw [Nat.card_units, hF]
    calc S.card ≤ Finset.univ.card := Finset.card_image_le
      _ = Fintype.card F0ˣ := rfl
      _ = Nat.card F0ˣ := by rw [Nat.card_eq_fintype_card]
      _ = 3 := hcard
  · intro g hg d hd
    obtain ⟨e, he⟩ := hg
    have he_unit : IsUnit e := by
      rw [← Matrix.isUnit_diagonal, ← he]
      exact Units.isUnit g
    have he_ne : ∀ x, e x ≠ 0 := fun x => (Pi.isUnit_iff.mp he_unit x).ne_zero
    have hd_mat : ((d : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        Matrix.diagonal (fun x => e (Equiv.swap i j x) * Ring.inverse e x) := by
      rw [hd, qTwoChartMatch_commutator_GL_coe (Equiv.swap i j) he, Equiv.swap_inv]
    let c : F0 := e j / e i
    have hc : c ≠ 0 := div_ne_zero (he_ne j) (he_ne i)
    let a : F0ˣ := Units.mk0 c hc
    have ha : (a : F0) = c := Units.val_mk0 hc
    have h_eq : (fun x => e (Equiv.swap i j x) * Ring.inverse e x) =
        (fun x => e (Equiv.swap i j x) * Ring.inverse (e x)) := by
      funext x
      rw [qTwoChartMatch_ringInverse_apply_eq he_unit x]
    have hd_eq : d = qTwoChartMatch_diagTwo hF hij a := by
      apply Subtype.ext
      apply Units.ext
      rw [hd_mat, h_eq, qTwoChartMatch_swap_update_apply hij he_ne a ha,
        qTwoChartMatch_diagTwo_coe]
    rw [hd_eq]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩

private theorem qTwoChartMatch_exists_ne_four {m : ℕ} (hm : 5 ≤ m) (a b c d : Fin m) :
    ∃ r : Fin m, r ≠ a ∧ r ≠ b ∧ r ≠ c ∧ r ≠ d := by
  classical
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c, d} : Finset (Fin m))) (t := Finset.univ)
    (by
      rw [Finset.card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  exact ⟨r, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2⟩

private theorem qTwoChartMatch_diagTwo_commutator_not_mem_center
    (hF : Nat.card F0 = 4) (hm : 5 ≤ m) {σ : Equiv.Perm (Fin m)} {i k : Fin m}
    (hik : i ≠ k) (hi : σ i ≠ i) (hk : σ⁻¹ i ≠ k) {a : F0ˣ} (ha : a ≠ 1) :
    qTwoChartMatch_permHom σ * qTwoChartMatch_diagTwo hF hik a *
        (qTwoChartMatch_permHom σ)⁻¹ * (qTwoChartMatch_diagTwo hF hik a)⁻¹ ∉
      Subgroup.center (Su F0 2 1 m) := by
  classical
  intro hcenter
  obtain ⟨x0, hx0i, hx0k, hx0si, hx0sk⟩ :=
    qTwoChartMatch_exists_ne_four hm i k (σ i) (σ k)
  have hσx0i : σ⁻¹ x0 ≠ i := fun h => hx0si (by simpa using congrArg σ h)
  have hσx0k : σ⁻¹ x0 ≠ k := fun h => hx0sk (by simpa using congrArg σ h)
  let e : Fin m → F0 :=
    Function.update (Function.update (1 : Fin m → F0) i (a : F0)) k ((a⁻¹ : F0ˣ) : F0)
  let t : Su F0 2 1 m := qTwoChartMatch_diagTwo hF hik a
  have he_i : e i = (a : F0) := by
    dsimp only [e]
    rw [Function.update_of_ne hik, Function.update_self]
  have he_other : ∀ x : Fin m, x ≠ i → x ≠ k → e x = 1 := by
    intro x hxi hxk
    dsimp only [e]
    rw [Function.update_of_ne hxk, Function.update_of_ne hxi]
    simp
  have he_unit : IsUnit e := by
    rw [← Matrix.isUnit_diagonal, ← qTwoChartMatch_diagTwo_coe hF hik a]
    exact Units.isUnit (t : GL (Fin m) F0)
  have hinv_i : Ring.inverse (e i) = ((a⁻¹ : F0ˣ) : F0) := by
    rw [he_i, Ring.inverse_eq_inv, Units.val_inv_eq_inv_val]
  have hinv_x0 : Ring.inverse (e x0) = 1 := by
    rw [he_other x0 hx0i hx0k, Ring.inverse_one]
  obtain ⟨c0, hc0⟩ := qTwoLMDivCoordInner_center_scalar hF (by omega) hcenter
  have hcomm := qTwoChartMatch_commutator_GL_coe (F0 := F0) σ
    (g := (t : GL (Fin m) F0)) (e := e) (qTwoChartMatch_diagTwo_coe hF hik a)
  have hdiag : (fun _ : Fin m => c0) = fun x => e (σ⁻¹ x) * Ring.inverse e x := by
    apply Matrix.diagonal_injective
    rw [← hc0]
    exact hcomm
  have hji : σ⁻¹ i ≠ i := fun h => hi (by simpa using congrArg σ h.symm)
  have hc0_i : c0 = ((a⁻¹ : F0ˣ) : F0) := by
    have h := congrFun hdiag i
    rw [he_other (σ⁻¹ i) hji hk, qTwoChartMatch_ringInverse_apply_eq he_unit i,
      hinv_i] at h
    simpa using h
  have hc0_x0 : c0 = 1 := by
    have h := congrFun hdiag x0
    rw [he_other (σ⁻¹ x0) hσx0i hσx0k, qTwoChartMatch_ringInverse_apply_eq he_unit x0,
      hinv_x0] at h
    simpa using h
  have hainv : ((a⁻¹ : F0ˣ) : F0) = 1 := by rw [← hc0_i, hc0_x0]
  have hainv1 : a⁻¹ = 1 := Units.ext (by simpa using hainv)
  exact ha (by simpa using congrArg Inv.inv hainv1)

theorem qTwoChartMatch_exists_diag_not_mem_center (hF : Nat.card F0 = 4) (hm : 5 ≤ m)
    {σ : Equiv.Perm (Fin m)} (hσ : σ ≠ 1) :
    ∃ t ∈ qTwoLMDivKind_diag F0 m,
      qTwoChartMatch_permHom σ * t * (qTwoChartMatch_permHom σ)⁻¹ * t⁻¹ ∉
        Subgroup.center (Su F0 2 1 m) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin m, σ i ≠ i := by
    by_contra h
    push Not at h
    exact hσ (Equiv.ext h)
  obtain ⟨k, hki, hkj, -, -⟩ :=
    qTwoChartMatch_exists_ne_four hm i (σ⁻¹ i) (σ⁻¹ i) (σ⁻¹ i)
  letI : Fintype F0 := Fintype.ofFinite F0
  letI : Fintype F0ˣ := Fintype.ofFinite F0ˣ
  have hcard : Nat.card F0ˣ = 3 := by rw [Nat.card_units, hF]
  haveI : Nontrivial F0ˣ := by
    have h : 1 < Fintype.card F0ˣ := by
      rw [← Nat.card_eq_fintype_card, hcard]
      norm_num
    exact Fintype.one_lt_card_iff_nontrivial.mp h
  obtain ⟨a, ha⟩ := exists_ne (1 : F0ˣ)
  refine ⟨qTwoChartMatch_diagTwo hF hki.symm a, ?_, ?_⟩
  · exact ⟨_, qTwoChartMatch_diagTwo_coe hF hki.symm a⟩
  · exact qTwoChartMatch_diagTwo_commutator_not_mem_center hF hm hki.symm hi hkj.symm ha

end CFSG.StandardType.QTwo

end
