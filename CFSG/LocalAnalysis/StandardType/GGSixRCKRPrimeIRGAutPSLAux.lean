module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LieType.Universal.SpecialLinearRoots
public import CFSG.LieType.Universal.SpecialLinearExtras

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal CFSG.LieType.RootSystem Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearField
  (slFieldAut slFieldEquiv slFieldEquiv_entry)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (coe_slConjugation)

theorem irgL_exists_slAut_of_quotAut {m : ℕ} {F : Type} [Field F] [Finite F]
    (hn : 3 ≤ m + 1)
    (θ : MulAut (Matrix.SpecialLinearGroup (Fin (m + 1)) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))) :
    ∃ (A : GL (Fin (m + 1)) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      ∀ x : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
        θ (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
            x) =
          QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
            ((slConjugation (m + 1) F A * slFieldAut (Fin (m + 1)) F σ *
              slGraphAut (m + 1) F ^ ε) x) := by
  let SL := Matrix.SpecialLinearGroup (Fin (m + 1)) F
  haveI : (LinearFlag.scalars (m + 1) F).Normal := LinearFlag.scalars_normal (m + 1) F
  let ec : SL ⧸ Subgroup.center SL ≃* LinearFlag.projectiveSL (m + 1) F :=
    QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center (m + 1) F).symm
  let θ' : MulAut (LinearFlag.projectiveSL (m + 1) F) := ec.symm.trans (θ.trans ec)
  have hθ' : ∀ y, θ' (ec y) = ec (θ y) := by
    intro y
    rw [show θ' (ec y) = (θ.trans ec) (ec.symm (ec y)) from rfl, MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨A, σ, ε, hε, hα⟩ := (LinearFlag.automorphism_generation (K := F) (n := m + 1) hn).2 θ'
  let Φ : MulAut SL :=
    slConjugation (m + 1) F A * slFieldAut (Fin (m + 1)) F σ * slGraphAut (m + 1) F ^ ε
  have hΦ : LinearFlag.descendAut (m + 1) F Φ = θ' := by
    rw [hα]
    dsimp only [Φ]
    rw [map_mul, map_mul, map_pow]
    rfl
  have hec : ∀ y : SL,
      ec (QuotientGroup.mk' (Subgroup.center SL) y) = LinearFlag.proj (m + 1) F y :=
    fun y => QuotientGroup.quotientMulEquivOfEq_mk _ y
  have hθ : ∀ y : SL, θ (QuotientGroup.mk' (Subgroup.center SL) y) =
      QuotientGroup.mk' (Subgroup.center SL) (Φ y) := by
    intro y
    apply ec.injective
    rw [← hθ', hec y, hec (Φ y), ← hΦ, LinearFlag.descendAut_proj]
  exact ⟨A, σ, ε, hε, hθ⟩

theorem irgL_slFieldAut_transvection {m : ℕ} {F : Type} [Field F]
    (σ : F ≃+* F) {i j : Fin (m + 1)} (hij : i ≠ j) (c : F) :
    (slFieldAut (Fin (m + 1)) F σ).toMonoidHom
        (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij (σ c) := by
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  rw [show (slFieldAut (Fin (m + 1)) F σ).toMonoidHom
        (SpecialLinearGroup.transvection hij c) =
      slFieldEquiv (Fin (m + 1)) σ (SpecialLinearGroup.transvection hij c) from rfl,
    slFieldEquiv_entry, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij]
  · simp [h]

theorem irgL_slGraphAut_transvection {m : ℕ} {F : Type} [Field F]
    {i j : Fin (m + 1)} (hij : i ≠ j) (c : F) :
    (slGraphAut (m + 1) F).toMonoidHom (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij.symm (-c) := by
  refine Subtype.ext ?_
  rw [show (slGraphAut (m + 1) F).toMonoidHom
        (SpecialLinearGroup.transvection hij c) =
      slGraphAut (m + 1) F (SpecialLinearGroup.transvection hij c) from rfl,
    slGraphAut_matrix, SpecialLinearGroup.transvection_inv]
  change (Matrix.transvection i j (-c))ᵀ = Matrix.transvection j i (-c)
  rw [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single,
    Matrix.transvection]

theorem irgL_slConjugation_diagonal_transvection {m : ℕ} {F : Type} [Field F]
    {d : Fin (m + 1) → F} (hd : ∀ k, d k ≠ 0) {D : GL (Fin (m + 1)) F}
    (hD : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal d)
    {i j : Fin (m + 1)} (hij : i ≠ j) (c : F) :
    (slConjugation (m + 1) F D).toMonoidHom (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij (d i * c * (d j)⁻¹) := by
  have hinv : ((D⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal (fun k => (d k)⁻¹) := by
    have hmul : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((D⁻¹ : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_one,
        mul_inv_cancel]
    have h2 := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) F =>
      Matrix.diagonal (fun k => (d k)⁻¹) * M) hmul
    rw [← Matrix.mul_assoc, hD, Matrix.diagonal_mul_diagonal] at h2
    have hfun : (fun k => (d k)⁻¹ * d k) = (fun _ => 1) := by
      funext k
      exact inv_mul_cancel₀ (hd k)
    rw [hfun, Matrix.diagonal_one, Matrix.one_mul, Matrix.mul_one] at h2
    exact h2
  have hsingle : Matrix.diagonal d * Matrix.single i j c *
      Matrix.diagonal (fun k => (d k)⁻¹) = Matrix.single i j (d i * c * (d j)⁻¹) := by
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
    by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp [h]
  have hdiag : Matrix.diagonal d * Matrix.diagonal (fun k => (d k)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    have hfun : (fun k => d k * (d k)⁻¹) = (fun _ => 1) := by
      funext k
      exact mul_inv_cancel₀ (hd k)
    rw [hfun, Matrix.diagonal_one]
  refine Subtype.ext ?_
  rw [show (slConjugation (m + 1) F D).toMonoidHom
        (SpecialLinearGroup.transvection hij c) =
      slConjugation (m + 1) F D (SpecialLinearGroup.transvection hij c) from rfl,
    coe_slConjugation, hinv, hD, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hsingle,
    hdiag]

theorem irgL_rootSubgroup_map_slFieldAut {m : ℕ} {F : Type} [Field F]
    (σ : F ≃+* F) {i j : Fin (m + 1)} (hij : i ≠ j) :
    (SpecialLinear.rootSubgroup m F hij).map (slFieldAut (Fin (m + 1)) F σ).toMonoidHom =
      SpecialLinear.rootSubgroup m F hij := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij x).1 hx
    rw [Subgroup.mem_comap]
    exact (SpecialLinear.mem_rootSubgroup hij _).2
      ⟨σ c, (irgL_slFieldAut_transvection σ hij c).symm⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij x).1 hx
    have hx' : SpecialLinearGroup.transvection hij (σ.symm c) ∈
        SpecialLinear.rootSubgroup m F hij :=
      (SpecialLinear.mem_rootSubgroup hij _).2 ⟨σ.symm c, rfl⟩
    have h := Subgroup.mem_map_of_mem (slFieldAut (Fin (m + 1)) F σ).toMonoidHom hx'
    rw [irgL_slFieldAut_transvection σ hij (σ.symm c),
      RingEquiv.apply_symm_apply] at h
    exact h

theorem irgL_rootSubgroup_map_slGraphAut {m : ℕ} {F : Type} [Field F]
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    (SpecialLinear.rootSubgroup m F hij).map (slGraphAut (m + 1) F).toMonoidHom =
      SpecialLinear.rootSubgroup m F hij.symm := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij x).1 hx
    rw [Subgroup.mem_comap]
    exact (SpecialLinear.mem_rootSubgroup hij.symm _).2
      ⟨-c, (irgL_slGraphAut_transvection hij c).symm⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij.symm x).1 hx
    have hx' : SpecialLinearGroup.transvection hij (-c) ∈
        SpecialLinear.rootSubgroup m F hij :=
      (SpecialLinear.mem_rootSubgroup hij _).2 ⟨-c, rfl⟩
    have h := Subgroup.mem_map_of_mem (slGraphAut (m + 1) F).toMonoidHom hx'
    rw [irgL_slGraphAut_transvection hij (-c), neg_neg] at h
    exact h

theorem irgL_rootSubgroup_map_slConjugation_diagonal {m : ℕ} {F : Type} [Field F]
    {d : Fin (m + 1) → F} (hd : ∀ k, d k ≠ 0) {D : GL (Fin (m + 1)) F}
    (hD : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal d)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    (SpecialLinear.rootSubgroup m F hij).map (slConjugation (m + 1) F D).toMonoidHom =
      SpecialLinear.rootSubgroup m F hij := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij x).1 hx
    rw [Subgroup.mem_comap]
    exact (SpecialLinear.mem_rootSubgroup hij _).2
      ⟨_, (irgL_slConjugation_diagonal_transvection hd hD hij c).symm⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij x).1 hx
    have hx' : SpecialLinearGroup.transvection hij ((d i)⁻¹ * c * d j) ∈
        SpecialLinear.rootSubgroup m F hij :=
      (SpecialLinear.mem_rootSubgroup hij _).2 ⟨_, rfl⟩
    have h := Subgroup.mem_map_of_mem (slConjugation (m + 1) F D).toMonoidHom hx'
    rw [irgL_slConjugation_diagonal_transvection hd hD hij] at h
    have hc : d i * ((d i)⁻¹ * c * d j) * (d j)⁻¹ = c := by
      calc d i * ((d i)⁻¹ * c * d j) * (d j)⁻¹
          = (d i * (d i)⁻¹) * (c * d j) * (d j)⁻¹ := by ring
        _ = c := by
            rw [mul_inv_cancel₀ (hd i), one_mul, mul_assoc, mul_inv_cancel₀ (hd j), mul_one]
    rw [hc] at h
    exact h

theorem irgL_conj_slConjugation {m : ℕ} {F : Type} [Field F]
    (s : SpecialLinearGroup (Fin (m + 1)) F) :
    (slConjugation (m + 1) F (SpecialLinearGroup.toGL s)).toMonoidHom =
      (MulAut.conj s).toMonoidHom := by
  refine MonoidHom.ext fun x => ?_
  rw [show (slConjugation (m + 1) F (SpecialLinearGroup.toGL s)).toMonoidHom x =
      slConjugation (m + 1) F (SpecialLinearGroup.toGL s) x from rfl,
    show (MulAut.conj s).toMonoidHom x = MulAut.conj s x from rfl]
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem irgL_exists_eq_specialLinearGroup_mul_diagonal {m : ℕ} (hm : 0 < m)
    {F : Type} [Field F] (A : GL (Fin (m + 1)) F) :
    ∃ (s : SpecialLinearGroup (Fin (m + 1)) F) (d : Fin (m + 1) → F),
      (∀ k, d k ≠ 0) ∧
        ∃ D : GL (Fin (m + 1)) F,
          (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal d ∧
            A = SpecialLinearGroup.toGL s * D := by
  obtain ⟨k₀⟩ : Nonempty (Fin (m + 1)) := ⟨⟨0, by omega⟩⟩
  set d : Fin (m + 1) → F :=
    Function.update (fun _ => 1) k₀ (Matrix.GeneralLinearGroup.det A : F) with hddef
  have hd : ∀ k, d k ≠ 0 := by
    intro k
    by_cases hk : k = k₀
    · subst hk
      rw [hddef, Function.update_self]
      exact Matrix.GeneralLinearGroup.det_ne_zero A
    · rw [hddef]
      simp only [Function.update_of_ne hk]
      exact one_ne_zero
  have hdetd : (Matrix.diagonal d).det = (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det := by
    rw [Matrix.det_diagonal, hddef,
      Finset.prod_eq_single_of_mem k₀ (Finset.mem_univ k₀) (fun b _ hb => by
        simp only [Function.update_of_ne hb])]
    rw [Function.update_self]
    rfl
  let D : GL (Fin (m + 1)) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) (by
      rw [hdetd]
      exact Matrix.GeneralLinearGroup.det_ne_zero A)
  have hD : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal d := rfl
  let s : SpecialLinearGroup (Fin (m + 1)) F :=
    ⟨(A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((D⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F), by
      rw [Matrix.det_mul, Matrix.GeneralLinearGroup.coe_inv, hD, Matrix.det_nonsing_inv,
        hdetd, Ring.inverse_eq_inv]
      exact mul_inv_cancel₀ (Matrix.GeneralLinearGroup.det_ne_zero A)⟩
  have htoGL : SpecialLinearGroup.toGL s = A * D⁻¹ := by
    apply Units.ext
    rfl
  have hA : A = SpecialLinearGroup.toGL s * D := by
    rw [htoGL, mul_assoc, inv_mul_cancel, mul_one]
  exact ⟨s, d, hd, D, hD, hA⟩

theorem irgL_exists_conj_slConjugation {m : ℕ} (hm : 0 < m) {F : Type} [Field F]
    (A : GL (Fin (m + 1)) F) :
    ∃ v : SpecialLinearGroup (Fin (m + 1)) F,
      ∀ {i j : Fin (m + 1)} (hij : i ≠ j),
        (SpecialLinear.rootSubgroup m F hij).map (slConjugation (m + 1) F A).toMonoidHom =
          (SpecialLinear.rootSubgroup m F hij).map (MulAut.conj v).toMonoidHom := by
  obtain ⟨s, d, hd, D, hD, hA⟩ := irgL_exists_eq_specialLinearGroup_mul_diagonal hm A
  refine ⟨s, fun hij => ?_⟩
  have hnormal := irgL_rootSubgroup_map_slConjugation_diagonal (m := m) hd hD hij
  have hcomp : (slConjugation (m + 1) F A).toMonoidHom =
      (slConjugation (m + 1) F (SpecialLinearGroup.toGL s)).toMonoidHom.comp
        (slConjugation (m + 1) F D).toMonoidHom := by
    rw [hA, map_mul]
    rfl
  rw [hcomp, ← Subgroup.map_map, hnormal, irgL_conj_slConjugation]

theorem irgL_neg_mem_roots {m : ℕ} {γ : Fin m → ℤ}
    (hγ : γ ∈ roots (SpecialLinear.isFiniteType_A m) ∅) :
    -γ ∈ roots (SpecialLinear.isFiniteType_A m) ∅ := by
  rw [SpecialLinear.roots_eq] at hγ ⊢
  obtain ⟨i, j, hij, h⟩ := hγ
  exact ⟨j, i, hij.symm, by rw [SpecialLinear.toStd_neg, h, neg_sub]⟩

theorem irgL_rootGroup_map_slFieldAut {m : ℕ} {F : Type} [Field F]
    (σ : F ≃+* F) {γ : Fin m → ℤ}
    (hγ : γ ∈ roots (SpecialLinear.isFiniteType_A m) ∅) :
    (SpecialLinear.rootGroup m F γ).map (slFieldAut (Fin (m + 1)) F σ).toMonoidHom =
      SpecialLinear.rootGroup m F γ := by
  rw [SpecialLinear.roots_eq] at hγ
  obtain ⟨i, j, hij, hstd⟩ := hγ
  rw [SpecialLinear.rootGroup_eq m F hij hstd, irgL_rootSubgroup_map_slFieldAut σ hij,
    ← SpecialLinear.rootGroup_eq m F hij hstd]

theorem irgL_rootGroup_map_slGraphAut {m : ℕ} {F : Type} [Field F] {γ : Fin m → ℤ}
    (hγ : γ ∈ roots (SpecialLinear.isFiniteType_A m) ∅) :
    (SpecialLinear.rootGroup m F γ).map (slGraphAut (m + 1) F).toMonoidHom =
      SpecialLinear.rootGroup m F (-γ) := by
  rw [SpecialLinear.roots_eq] at hγ
  obtain ⟨i, j, hij, hstd⟩ := hγ
  rw [SpecialLinear.rootGroup_eq m F hij hstd, irgL_rootSubgroup_map_slGraphAut hij]
  have hneg : SpecialLinear.toStd m (-γ) = Pi.single j 1 - Pi.single i 1 := by
    rw [SpecialLinear.toStd_neg, hstd, neg_sub]
  exact (SpecialLinear.rootGroup_eq m F hij.symm hneg).symm

theorem irgL_exists_conj_rootGroup_slConjugation {m : ℕ} (hm : 0 < m) {F : Type} [Field F]
    (A : GL (Fin (m + 1)) F) :
    ∃ v : SpecialLinearGroup (Fin (m + 1)) F,
      ∀ {γ : Fin m → ℤ}, γ ∈ roots (SpecialLinear.isFiniteType_A m) ∅ →
        (SpecialLinear.rootGroup m F γ).map (slConjugation (m + 1) F A).toMonoidHom =
          (SpecialLinear.rootGroup m F γ).map (MulAut.conj v).toMonoidHom := by
  obtain ⟨v, hv⟩ := irgL_exists_conj_slConjugation hm A
  refine ⟨v, fun hγ => ?_⟩
  rw [SpecialLinear.roots_eq] at hγ
  obtain ⟨i, j, hij, hstd⟩ := hγ
  rw [SpecialLinear.rootGroup_eq m F hij hstd, hv hij,
    ← SpecialLinear.rootGroup_eq m F hij hstd]

theorem irgL_rootGroup_image_std {m : ℕ} (hm : 0 < m) {F : Type} [Field F]
    (A : GL (Fin (m + 1)) F) (σ : F ≃+* F) (ε : ℕ) (hε : ε ≤ 1)
    {β' : Fin m → ℤ} (hβ' : β' ∈ roots (SpecialLinear.isFiniteType_A m) ∅) :
    ∃ (β : Fin m → ℤ) (v : SpecialLinearGroup (Fin (m + 1)) F),
      β ∈ roots (SpecialLinear.isFiniteType_A m) ∅ ∧
        (SpecialLinear.rootGroup m F β').map
            (slConjugation (m + 1) F A * slFieldAut (Fin (m + 1)) F σ *
              slGraphAut (m + 1) F ^ ε).toMonoidHom =
          (SpecialLinear.rootGroup m F β).map (MulAut.conj v).toMonoidHom ∧
        (SpecialLinear.rootGroup m F (-β')).map
            (slConjugation (m + 1) F A * slFieldAut (Fin (m + 1)) F σ *
              slGraphAut (m + 1) F ^ ε).toMonoidHom =
          (SpecialLinear.rootGroup m F (-β)).map (MulAut.conj v).toMonoidHom := by
  obtain ⟨v, hv⟩ := irgL_exists_conj_rootGroup_slConjugation hm A
  have hneg := irgL_neg_mem_roots hβ'
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · refine ⟨β', v, hβ', ?_, ?_⟩
    · have hstep : (slConjugation (m + 1) F A * slFieldAut (Fin (m + 1)) F σ *
          slGraphAut (m + 1) F ^ 0).toMonoidHom =
          (slConjugation (m + 1) F A).toMonoidHom.comp
            (slFieldAut (Fin (m + 1)) F σ).toMonoidHom := by
        rw [pow_zero, mul_one]
        rfl
      rw [hstep, ← Subgroup.map_map, irgL_rootGroup_map_slFieldAut σ hβ']
      exact hv hβ'
    · have hstep : (slConjugation (m + 1) F A * slFieldAut (Fin (m + 1)) F σ *
          slGraphAut (m + 1) F ^ 0).toMonoidHom =
          (slConjugation (m + 1) F A).toMonoidHom.comp
            (slFieldAut (Fin (m + 1)) F σ).toMonoidHom := by
        rw [pow_zero, mul_one]
        rfl
      rw [hstep, ← Subgroup.map_map, irgL_rootGroup_map_slFieldAut σ hneg]
      exact hv hneg
  · refine ⟨-β', v, hneg, ?_, ?_⟩
    · have hstep : (slConjugation (m + 1) F A * slFieldAut (Fin (m + 1)) F σ *
          slGraphAut (m + 1) F ^ 1).toMonoidHom =
          ((slConjugation (m + 1) F A).toMonoidHom.comp
            (slFieldAut (Fin (m + 1)) F σ).toMonoidHom).comp
              (slGraphAut (m + 1) F).toMonoidHom := by
        rw [pow_one]
        rfl
      rw [hstep, ← Subgroup.map_map, ← Subgroup.map_map, irgL_rootGroup_map_slGraphAut hβ',
        irgL_rootGroup_map_slFieldAut σ hneg]
      exact hv hneg
    · have hstep : (slConjugation (m + 1) F A * slFieldAut (Fin (m + 1)) F σ *
          slGraphAut (m + 1) F ^ 1).toMonoidHom =
          ((slConjugation (m + 1) F A).toMonoidHom.comp
            (slFieldAut (Fin (m + 1)) F σ).toMonoidHom).comp
              (slGraphAut (m + 1) F).toMonoidHom := by
        rw [pow_one]
        rfl
      rw [hstep, ← Subgroup.map_map, ← Subgroup.map_map, irgL_rootGroup_map_slGraphAut hneg,
        neg_neg, irgL_rootGroup_map_slFieldAut σ hβ']
      exact hv hβ'

end CFSG.StandardType.RCKRP
