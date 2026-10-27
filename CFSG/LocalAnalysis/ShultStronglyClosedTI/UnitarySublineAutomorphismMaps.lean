module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismRealization

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {J : HermitianForm 3 K}

@[expose] def restrictMulAut {G : Type*} [Group G] (e : MulAut G) (H : Subgroup G)
    (h : H.map (e : G →* G) = H) : MulAut H :=
  (e.subgroupMap H).trans (MulEquiv.subgroupCongr h)

theorem coe_restrictMulAut {G : Type*} [Group G] (e : MulAut G) (H : Subgroup G)
    (h : H.map (e : G →* G) = H) (x : H) : (restrictMulAut e H h x : G) = e x :=
  rfl

theorem map_eq_of_le {G : Type*} [Group G] (e : MulAut G) {H : Subgroup G} [Finite H]
    (h : H.map (e : G →* G) ≤ H) : H.map (e : G →* G) = H :=
  Subgroup.eq_of_le_of_card_ge h (Subgroup.card_map_of_injective e.injective).ge

variable (J) in
abbrev conjGroup : Subgroup (K ≃+* K) := Subgroup.zpowers J.conj

theorem conj_sq : J.conj ^ 2 = 1 :=
  RingEquiv.ext fun x => J.conj_involutive x

theorem mem_conjGroup_iff {σ : K ≃+* K} : σ ∈ conjGroup J ↔ σ = 1 ∨ σ = J.conj := by
  constructor
  · rintro ⟨k, rfl⟩
    have h2 : J.conj ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, conj_sq]
    have hk : J.conj ^ k = J.conj ^ (k % 2) := by
      conv_lhs => rw [← Int.mul_ediv_add_emod k 2]
      rw [_root_.zpow_add, _root_.zpow_mul, h2, _root_.one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      simp only [hk, h, zpow_zero]
    · right
      simp only [hk, h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem conjGroup_commute {σ : K ≃+* K} (hσ : σ ∈ conjGroup J) (x : K) :
    σ (J.conj x) = J.conj (σ x) := by
  rcases mem_conjGroup_iff.mp hσ with rfl | rfl <;> rfl

theorem conjGroup_fix {σ : K ≃+* K} (hσ : σ ∈ conjGroup J) {x : K} (hx : J.conj x = x) :
    σ x = x := by
  rcases mem_conjGroup_iff.mp hσ with rfl | rfl
  · rfl
  · exact hx

theorem map_normOne_le [Finite K] {σ : K ≃+* K} (hσ : σ ∈ conjGroup J) :
    (normOne J).map (Units.mapEquiv σ.toMulEquiv : Kˣ →* Kˣ) ≤ normOne J := by
  rintro _ ⟨d, hd, rfl⟩
  change σ (d : K) * J.conj (σ (d : K)) = 1
  rw [← conjGroup_commute hσ, ← map_mul, hd, map_one]

variable (J) in
@[expose] def normOneAction [Finite K] : conjGroup J →* MulAut (normOne J) where
  toFun σ := restrictMulAut (Units.mapEquiv σ.1.toMulEquiv) (normOne J)
    (map_eq_of_le _ (map_normOne_le σ.2))
  map_one' := MulEquiv.ext fun _ => Subtype.ext (Units.ext rfl)
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext (Units.ext rfl)

theorem coe_normOneAction [Finite K] (σ : conjGroup J) (d : normOne J) :
    (((normOneAction J σ d : normOne J) : Kˣ) : K) = σ.1 ((d : Kˣ) : K) :=
  rfl

theorem coe_normOneAction_units [Finite K] (σ : conjGroup J) (d : normOne J) :
    ((normOneAction J σ d : normOne J) : Kˣ) = Units.mapEquiv σ.1.toMulEquiv (d : Kˣ) :=
  rfl

theorem normOneAction_conj [Finite K] (d : normOne J) :
    normOneAction J ⟨J.conj, Subgroup.mem_zpowers _⟩ d = d⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_normOneAction, conj_eq_inv_of_mem_normOne J d.2, InvMemClass.coe_inv,
    Units.val_inv_eq_inv_val]

theorem conj_mem_specialSubgroup {A : GL (Fin 3) K} (hA : A ∈ J.unitarySubgroup)
    {g : GL (Fin 3) K} (hg : g ∈ J.specialSubgroup) : A * g * A⁻¹ ∈ J.specialSubgroup := by
  refine ⟨J.unitarySubgroup.mul_mem (J.unitarySubgroup.mul_mem hA
    (J.specialSubgroup_le_unitarySubgroup hg)) (J.unitarySubgroup.inv_mem hA), ?_⟩
  have hdet : GeneralLinearGroup.det g = 1 := hg.2
  change GeneralLinearGroup.det (A * g * A⁻¹) = 1
  rw [map_mul, map_mul, map_inv, hdet, mul_one, mul_inv_cancel]

theorem glAut_mem_specialSubgroup (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {σ : K ≃+* K} (hσ : ∀ x, σ (J.conj x) = J.conj (σ x)) {g : GL (Fin 3) K}
    (hg : g ∈ J.specialSubgroup) : glAut σ g ∈ J.specialSubgroup := by
  obtain ⟨hgram, hdet⟩ := (J.mem_specialSubgroup_iff g).mp hg
  have hJσ : J.form.map σ = J.form := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hT : J.conjTranspose ((g : Matrix (Fin 3) (Fin 3) K).map σ) =
      (J.conjTranspose (g : Matrix (Fin 3) (Fin 3) K)).map σ := by
    ext i j
    simp [HermitianForm.conjTranspose, hσ]
  refine (J.mem_specialSubgroup_iff _).mpr ⟨?_, ?_⟩
  · rw [coe_glAut, hT, ← hJσ, ← map_mul_ringEquiv, ← map_mul_ringEquiv, hJσ, hgram, hJσ]
  · rw [Units.ext_iff, GeneralLinearGroup.val_det_apply, coe_glAut, Units.val_one]
    have h := congrArg Units.val hdet
    rw [GeneralLinearGroup.val_det_apply, Units.val_one] at h
    rw [show (g : Matrix (Fin 3) (Fin 3) K).map σ = (σ : K →+* K).mapMatrix g from rfl,
      ← RingHom.map_det, h, map_one]

theorem semiAut_map_le (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {A : GL (Fin 3) K}
    (hA : A ∈ J.unitarySubgroup) {σ : K ≃+* K} (hσ : ∀ x, σ (J.conj x) = J.conj (σ x)) :
    J.specialSubgroup.map ((MulAut.conj A * glAut σ : MulAut (GL (Fin 3) K)) :
      GL (Fin 3) K →* GL (Fin 3) K) ≤ J.specialSubgroup := by
  rintro _ ⟨g, hg, rfl⟩
  exact conj_mem_specialSubgroup hA (glAut_mem_specialSubgroup hJ hσ hg)

theorem glAut_scalar_val (σ : K ≃+* K) {g : GL (Fin 3) K} {c : K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) c) :
    ((glAut σ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (σ c) := by
  rw [coe_glAut, hg]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [scalar_apply]
  · simp [scalar_apply, hij]

theorem glAut_diag3_one (σ : K ≃+* K) (d : Kˣ) :
    glAut σ (diag3 1 d 1) = diag3 1 (Units.mapEquiv σ.toMulEquiv d) 1 := by
  apply Units.ext
  rw [coe_glAut, coe_diag3, coe_diag3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diag3_one_mul (a b : Kˣ) : diag3 1 (a * b) 1 = diag3 1 a 1 * diag3 (1 : Kˣ) b 1 := by
  rw [diag3_mul, one_mul]

variable [Finite K]

@[expose] def semiAutS (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {A : GL (Fin 3) K}
    (hA : A ∈ J.unitarySubgroup) {σ : K ≃+* K} (hσ : ∀ x, σ (J.conj x) = J.conj (σ x)) :
    MulAut J.specialSubgroup :=
  restrictMulAut (MulAut.conj A * glAut σ) J.specialSubgroup
    (map_eq_of_le _ (semiAut_map_le hJ hA hσ))

theorem coe_semiAutS (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {A : GL (Fin 3) K}
    (hA : A ∈ J.unitarySubgroup) {σ : K ≃+* K} (hσ : ∀ x, σ (J.conj x) = J.conj (σ x))
    (g : J.specialSubgroup) :
    ((semiAutS hJ hA hσ g : J.specialSubgroup) : GL (Fin 3) K) =
      A * glAut σ (g : GL (Fin 3) K) * A⁻¹ :=
  rfl

variable {C : Subgroup J.specialSubgroup} [C.Normal]

omit [C.Normal] in
theorem semiAutS_map_C_le (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) {A : GL (Fin 3) K} (hA : A ∈ J.unitarySubgroup) {σ : K ≃+* K}
    (hσ : σ ∈ conjGroup J) :
    C.map (semiAutS hJ hA (conjGroup_commute hσ) : J.specialSubgroup →* J.specialSubgroup) ≤
      C := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨c, hc, hcn, -⟩ := hC hg
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hcn
  have hval : ((semiAutS hJ hA (conjGroup_commute hσ) g : J.specialSubgroup) :
      GL (Fin 3) K) = glAut σ (g : GL (Fin 3) K) := by
    rw [coe_semiAutS]
    have hcomm : Commute A (glAut σ (g : GL (Fin 3) K)) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, glAut_scalar_val σ hc]
      exact ((Matrix.scalar_commute (σ c) (fun r => Commute.all (σ c) r) _)).eq.symm
    rw [hcomm.eq, mul_inv_cancel_right]
  show semiAutS hJ hA (conjGroup_commute hσ) g ∈ C
  rcases mem_conjGroup_iff.mp hσ with rfl | rfl
  · have : semiAutS hJ hA (conjGroup_commute hσ) g = g := Subtype.ext (by rw [hval]; rfl)
    rw [this]
    exact hg
  · have : semiAutS hJ hA (conjGroup_commute hσ) g = g⁻¹ := by
      apply Subtype.ext
      apply Units.ext
      have hcinv : J.conj c = c⁻¹ := eq_inv_of_mul_eq_one_right hcn
      rw [hval, glAut_scalar_val _ hc, hcinv]
      have hmul : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((g⁻¹ : J.specialSubgroup) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      rw [hc] at hmul
      calc scalar (Fin 3) c⁻¹
          = scalar (Fin 3) c⁻¹ * (scalar (Fin 3) c *
              (((g⁻¹ : J.specialSubgroup) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
            rw [hmul, Matrix.mul_one]
        _ = (((g⁻¹ : J.specialSubgroup) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
            rw [← Matrix.mul_assoc, scalar_apply, scalar_apply, diagonal_mul_diagonal,
              inv_mul_cancel₀ hc0, diagonal_one, Matrix.one_mul]
    rw [this]
    exact C.inv_mem hg

@[expose] def semiAutL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) {A : GL (Fin 3) K} (hA : A ∈ J.unitarySubgroup) {σ : K ≃+* K}
    (hσ : σ ∈ conjGroup J) : MulAut (J.specialSubgroup ⧸ C) :=
  QuotientGroup.congr C C (semiAutS hJ hA (conjGroup_commute hσ))
    (map_eq_of_le (semiAutS hJ hA (conjGroup_commute hσ)) (semiAutS_map_C_le hJ hC hA hσ))

theorem semiAutL_mk (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    {A : GL (Fin 3) K} (hA : A ∈ J.unitarySubgroup) {σ : K ≃+* K} (hσ : σ ∈ conjGroup J)
    (g : J.specialSubgroup) :
    semiAutL hJ hC hA hσ (g : J.specialSubgroup ⧸ C) =
      ((semiAutS hJ hA (conjGroup_commute hσ) g : J.specialSubgroup) :
        J.specialSubgroup ⧸ C) :=
  QuotientGroup.congr_mk _ _ _ _ g

variable (J C) in
@[expose] def sublineAutHom (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) :
    normOne J ⋊[normOneAction J] conjGroup J →* MulAut (J.specialSubgroup ⧸ C) where
  toFun x := semiAutL hJ hC (diag3_one_mem_unitary hJ x.left.2) x.right.2
  map_one' := by
    refine MulEquiv.ext fun z => QuotientGroup.induction_on z fun g => ?_
    rw [semiAutL_mk]
    congr 1
    apply Subtype.ext
    rw [coe_semiAutS]
    simp only [SemidirectProduct.one_left, SemidirectProduct.one_right, OneMemClass.coe_one,
      map_one, MulAut.one_apply, diag3_one, one_mul, inv_one, mul_one]
  map_mul' x y := by
    refine MulEquiv.ext fun z => QuotientGroup.induction_on z fun g => ?_
    rw [MulAut.mul_apply, semiAutL_mk, semiAutL_mk, semiAutL_mk]
    congr 1
    apply Subtype.ext
    rw [coe_semiAutS, coe_semiAutS, coe_semiAutS]
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, Subgroup.coe_mul,
      map_mul, map_inv, glAut_diag3_one, coe_normOneAction_units]
    rw [diag3_one_mul, MulAut.mul_apply]
    group

theorem sublineAutHom_mk (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (x : normOne J ⋊[normOneAction J] conjGroup J)
    (g : J.specialSubgroup) :
    ∃ hg : diag3 1 (x.left : Kˣ) 1 * glAut (x.right : K ≃+* K) (g : GL (Fin 3) K) *
        (diag3 1 (x.left : Kˣ) 1)⁻¹ ∈ J.specialSubgroup,
      sublineAutHom J C hJ hC x (g : J.specialSubgroup ⧸ C) =
        ((⟨_, hg⟩ : J.specialSubgroup) : J.specialSubgroup ⧸ C) :=
  ⟨(semiAutS hJ (diag3_one_mem_unitary hJ x.left.2) (conjGroup_commute x.right.2) g).2,
    semiAutL_mk hJ hC (diag3_one_mem_unitary hJ x.left.2) x.right.2 g⟩

theorem sublineAutHom_apply_of_mem [CharP K 2] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (x : normOne J ⋊[normOneAction J] conjGroup J)
    {y : J.specialSubgroup ⧸ C} (hy : y ∈ sublineL J C hJ) : sublineAutHom J C hJ hC x y = y := by
  obtain ⟨m, rfl⟩ := hy
  change semiAutL hJ hC (diag3_one_mem_unitary hJ x.left.2) x.right.2
    ((sublineHom J hJ m : J.specialSubgroup) : J.specialSubgroup ⧸ C) =
    ((sublineHom J hJ m : J.specialSubgroup) : J.specialSubgroup ⧸ C)
  rw [semiAutL_mk]
  congr 1
  apply Subtype.ext
  rw [coe_semiAutS]
  have hσ : glAut (x.right : K ≃+* K) ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) =
      ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) := by
    apply Units.ext
    rw [coe_glAut, coe_sublineHom]
    have hfix : ∀ t : unitaryCoverFixedField J, (x.right : K ≃+* K) (t : K) = t :=
      fun t => conjGroup_fix x.right.2 (conj_fixedToK t)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hfix]
  have hcomm : Commute (diag3 1 (x.left : Kˣ) 1)
      ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diag3, coe_sublineHom]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  rw [hσ, hcomm.eq, mul_inv_cancel_right]

theorem sublineAutHom_injective (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) {q : ℕ} (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) :
    Function.Injective (sublineAutHom J C hJ hC) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have key : ∀ a : K, (x.right : K ≃+* K) a = a * ((x.left : Kˣ) : K) := by
    intro a
    obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed (-(a * J.conj a))
      (by rw [map_neg, map_mul, J.conj_involutive, mul_comm])
    let z : hermitianUnipotentCoord J := ⟨(a, b), by linear_combination hb⟩
    set Q := hermitianUnipotentSU J hJ z
    obtain ⟨hg, h1⟩ := sublineAutHom_mk hJ hC x Q
    rw [hx, MulAut.one_apply] at h1
    obtain ⟨u, hu, -, -⟩ := exists_scalar_of_mk_eq hC h1
    have hQ : ((Q : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        !![1, a, b; 0, 1, -J.conj a; 0, 0, 1] := rfl
    have hR : ((diag3 1 (x.left : Kˣ) 1 * glAut (x.right : K ≃+* K) (Q : GL (Fin 3) K) *
        (diag3 1 (x.left : Kˣ) 1)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        !![1, (x.right : K ≃+* K) a * ((x.left : Kˣ) : K)⁻¹, (x.right : K ≃+* K) b;
          0, 1, ((x.left : Kˣ) : K) * (x.right : K ≃+* K) (-J.conj a); 0, 0, 1] := by
      have hσQ : (!![1, a, b; 0, 1, -J.conj a; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K).map
          (x.right : K ≃+* K) = !![1, (x.right : K ≃+* K) a, (x.right : K ≃+* K) b;
            0, 1, (x.right : K ≃+* K) (-J.conj a); 0, 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [Units.val_mul, Units.val_mul, coe_glAut, coe_diag3, coe_diag3_inv, hQ, hσQ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    change ((Q : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) u =
      ((diag3 1 (x.left : Kˣ) 1 * glAut (x.right : K ≃+* K) (Q : GL (Fin 3) K) *
        (diag3 1 (x.left : Kˣ) 1)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) at hu
    rw [hR, hQ] at hu
    have e00 := congrFun (congrFun hu 0) 0
    have e01 := congrFun (congrFun hu 0) 1
    simp [Matrix.mul_apply, scalar_apply, diagonal_apply] at e00 e01
    have hd0 : ((x.left : Kˣ) : K) ≠ 0 := (x.left : Kˣ).ne_zero
    rw [e00, mul_one, eq_mul_inv_iff_mul_eq₀ hd0] at e01
    exact e01.symm
  have hd : ((x.left : Kˣ) : K) = 1 := by
    have := key 1
    rw [map_one, one_mul] at this
    exact this.symm
  have hσ : (x.right : K ≃+* K) = 1 := RingEquiv.ext fun a => by
    rw [key a, hd, mul_one]
    rfl
  apply SemidirectProduct.ext
  · exact Subtype.ext (Units.ext hd)
  · exact Subtype.ext hσ

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
