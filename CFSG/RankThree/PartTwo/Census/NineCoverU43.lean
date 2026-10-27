module

public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
public import CFSG.LieType.Multipliers.U43
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.NineCover
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.Assembly.LowTwoRank CFSG.LieType.Multipliers.U43 Matrix
open CFSG.Assembly.RankThreeEven (projSU localRank)

namespace NineCoverU43

@[expose] def mat (a b : ZMod 3) : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, a⟩, ⟨a, a⟩, 0, 0;
    ⟨-a, a⟩, ⟨1, -a⟩, 0, 0;
    0, 0, ⟨1, b⟩, ⟨b, b⟩;
    0, 0, ⟨-b, b⟩, ⟨1, -b⟩]

theorem mat_mul : ∀ a b a' b' : ZMod 3, mat a b * mat a' b' = mat (a + a') (b + b') := by
  decide +kernel

theorem mat_zero : mat 0 0 = 1 := by
  decide +kernel

theorem det_mat : ∀ a b : ZMod 3, (mat a b).det = 1 := by
  decide +kernel

theorem mat_unitary : ∀ a b : ZMod 3, ((mat a b).map (· ^ 3))ᵀ * mat a b = 1 := by
  decide +kernel

@[expose] def pmat : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, 0, 1, 0;
    0, 0, 0, 1;
    1, 0, 0, 0;
    0, 1, 0, 0]

@[expose] def nmat : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, ⟨0, 1⟩, 0, 0;
    1, 0, 0, 0;
    0, 0, 0, 1;
    0, 0, ⟨0, 2⟩, 0]

@[expose] def tmat : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨2, 0⟩, 0, 0, 0;
    0, ⟨2, 0⟩, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1]

theorem det_pmat : pmat.det = 1 := by decide +kernel

theorem det_nmat : nmat.det = 1 := by decide +kernel

theorem det_tmat : tmat.det = 1 := by decide +kernel

theorem pmat_unitary : (pmat.map (· ^ 3))ᵀ * pmat = 1 := by decide +kernel

theorem nmat_unitary : (nmat.map (· ^ 3))ᵀ * nmat = 1 := by decide +kernel

theorem tmat_unitary : (tmat.map (· ^ 3))ᵀ * tmat = 1 := by decide +kernel

theorem pmat_mul_mat : ∀ a b : ZMod 3, pmat * mat a b = mat b a * pmat := by
  decide +kernel

theorem nmat_mul_mat : ∀ a b : ZMod 3, nmat * mat a b = mat (-a) (-b) * nmat := by
  decide +kernel

theorem tmat_mul_mat : ∀ a b : ZMod 3, tmat * mat a b = mat a b * tmat := by
  decide +kernel

theorem tmat_mul_tmat : tmat * tmat = 1 := by
  decide +kernel

@[expose] noncomputable def toSU (A : Matrix (Fin 4) (Fin 4) F9) (hdet : A.det = 1)
    (hu : (A.map (· ^ 3))ᵀ * A = 1) : StatedSU 4 3 F9 :=
  ⟨GeneralLinearGroup.mk'' A (by rw [hdet]; exact isUnit_one),
    Subgroup.subset_closure ⟨hdet, hu⟩⟩

theorem ext_matrix {x y : StatedSU 4 3 F9}
    (h : ((x : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      ((y : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)) : x = y :=
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six.ext_matrix h

@[expose] noncomputable def theta0 : Multiplicative (ZMod 3 × ZMod 3) →* StatedSU 4 3 F9 where
  toFun x := toSU (mat x.toAdd.1 x.toAdd.2) (det_mat _ _) (mat_unitary _ _)
  map_one' := ext_matrix mat_zero
  map_mul' _ _ := ext_matrix (mat_mul _ _ _ _).symm

theorem coe_theta0 (x : Multiplicative (ZMod 3 × ZMod 3)) :
    (((theta0 x : StatedSU 4 3 F9) : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      mat x.toAdd.1 x.toAdd.2 :=
  rfl

@[expose] noncomputable def pSU : StatedSU 4 3 F9 := toSU pmat det_pmat pmat_unitary

@[expose] noncomputable def nSU : StatedSU 4 3 F9 := toSU nmat det_nmat nmat_unitary

@[expose] noncomputable def tSU : StatedSU 4 3 F9 := toSU tmat det_tmat tmat_unitary

theorem pSU_mul_theta0 (a b : ZMod 3) :
    pSU * theta0 (Multiplicative.ofAdd (a, b)) = theta0 (Multiplicative.ofAdd (b, a)) * pSU :=
  ext_matrix (pmat_mul_mat a b)

theorem nSU_mul_theta0 (x : Multiplicative (ZMod 3 × ZMod 3)) :
    nSU * theta0 x = theta0 x⁻¹ * nSU :=
  ext_matrix (nmat_mul_mat _ _)

theorem tSU_mul_theta0 (x : Multiplicative (ZMod 3 × ZMod 3)) :
    tSU * theta0 x = theta0 x * tSU :=
  ext_matrix (tmat_mul_mat _ _)

theorem tSU_sq : tSU ^ 2 = 1 :=
  ext_matrix (by rw [pow_two]; exact tmat_mul_tmat)

@[expose] noncomputable def theta : Multiplicative (ZMod 3 × ZMod 3) →* X₀ :=
  (QuotientGroup.mk' _).comp theta0

theorem theta_injective : Function.Injective theta := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [theta, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have h01 := congrArg (fun A : GL (Fin 4) F9 => (A : Matrix (Fin 4) (Fin 4) F9) 0 1) hc
  have h23 := congrArg (fun A : GL (Fin 4) F9 => (A : Matrix (Fin 4) (Fin 4) F9) 2 3) hc
  simp only [GeneralLinearGroup.coe_scalar, coe_theta0, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ (show (0 : Fin 4) ≠ 1 by decide),
    Matrix.diagonal_apply_ne _ (show (2 : Fin 4) ≠ 3 by decide), mat, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h01 h23
  apply Multiplicative.toAdd.injective
  exact Prod.ext (congrArg F9.re h01).symm (congrArg F9.re h23).symm

theorem card_range_theta : Nat.card theta.range = 3 ^ 2 := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective theta_injective, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod, pow_two]

@[expose] noncomputable def u1 : X₀ := theta (Multiplicative.ofAdd (1, 0))

@[expose] noncomputable def u2 : X₀ := theta (Multiplicative.ofAdd (0, 1))

theorem eq_gen_mul_gen : ∀ x : Multiplicative (ZMod 3 × ZMod 3),
    x = Multiplicative.ofAdd (1, 0) ^ (Multiplicative.toAdd x).1.val *
      Multiplicative.ofAdd (0, 1) ^ (Multiplicative.toAdd x).2.val := by
  decide

theorem range_theta_le : theta.range ≤ Subgroup.closure {u1, u2} := by
  rintro _ ⟨x, rfl⟩
  have h1 : u1 ∈ Subgroup.closure ({u1, u2} : Set X₀) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h2 : u2 ∈ Subgroup.closure ({u1, u2} : Set X₀) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have e : theta x =
      u1 ^ (Multiplicative.toAdd x).1.val * u2 ^ (Multiplicative.toAdd x).2.val := by
    rw [u1, u2, ← map_pow theta, ← map_pow theta, ← map_mul theta, ← eq_gen_mul_gen x]
  rw [e]
  exact mul_mem (pow_mem h1 _) (pow_mem h2 _)

theorem pow_three_eq_one_gen : ∀ x : Multiplicative (ZMod 3 × ZMod 3), x ^ 3 = 1 := by
  decide

theorem theta_pow_three (x : Multiplicative (ZMod 3 × ZMod 3)) : theta x ^ 3 = 1 := by
  rw [← map_pow, pow_three_eq_one_gen, map_one]

@[expose] noncomputable def pBar : X₀ := QuotientGroup.mk pSU

@[expose] noncomputable def nBar : X₀ := QuotientGroup.mk nSU

@[expose] noncomputable def tBar : X₀ := QuotientGroup.mk tSU

theorem pBar_conj_theta (a b : ZMod 3) :
    pBar * theta (Multiplicative.ofAdd (a, b)) * pBar⁻¹ =
      theta (Multiplicative.ofAdd (b, a)) := by
  rw [mul_inv_eq_iff_eq_mul]
  show QuotientGroup.mk (pSU * theta0 (Multiplicative.ofAdd (a, b))) =
    (QuotientGroup.mk (theta0 (Multiplicative.ofAdd (b, a)) * pSU) : X₀)
  rw [pSU_mul_theta0]

theorem nBar_conj_theta (x : Multiplicative (ZMod 3 × ZMod 3)) :
    nBar * theta x * nBar⁻¹ = (theta x)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul, ← map_inv]
  show QuotientGroup.mk (nSU * theta0 x) = (QuotientGroup.mk (theta0 x⁻¹ * nSU) : X₀)
  rw [nSU_mul_theta0]

theorem commute_tBar {e : X₀} (he : e ∈ theta.range) : Commute tBar e := by
  obtain ⟨x, rfl⟩ := he
  show QuotientGroup.mk (tSU * theta0 x) = (QuotientGroup.mk (theta0 x * tSU) : X₀)
  rw [tSU_mul_theta0]

theorem tBar_sq : tBar ^ 2 = 1 := by
  rw [tBar, ← QuotientGroup.mk_pow, tSU_sq, QuotientGroup.mk_one]

theorem tBar_ne_one : tBar ≠ 1 := by
  intro h
  rw [tBar, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  have h1 := congrArg (fun A : GL (Fin 4) F9 => (A : Matrix (Fin 4) (Fin 4) F9) 0 0) hc
  have h2 := congrArg (fun A : GL (Fin 4) F9 => (A : Matrix (Fin 4) (Fin 4) F9) 2 2) hc
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    at h1 h2
  have e1 : ((tSU : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) 0 0 = ⟨2, 0⟩ := rfl
  have e2 : ((tSU : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) 2 2 = 1 := rfl
  rw [e1] at h1
  rw [e2, h1] at h2
  exact absurd h2 (by decide)

section Lifts

variable {G : Type} [Group G] {φ : G →* X₀}

theorem commute_of_gen (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (x y : G) (hx : φ x ∈ ({u1, u2} : Set X₀)) (hy : φ y ∈ ({u1, u2} : Set X₀))
    (hxy : φ x ≠ φ y) : x * y = y * x := by
  have hc : Commute (φ x) (φ y) := by
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;>
      exact (Commute.all _ _).map theta
  have hy3 : φ y ^ 3 = 1 := by
    rcases hy with hy | hy <;> rw [hy] <;> exact theta_pow_three _
  refine TripleCoverLift.commute_of_conj hφ hker (by decide) hc hy3 (n := pBar) (Or.inr ?_)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] at hxy ⊢
  · exact absurd rfl hxy
  · exact ⟨pBar_conj_theta 1 0, pBar_conj_theta 0 1⟩
  · exact ⟨pBar_conj_theta 0 1, pBar_conj_theta 1 0⟩
  · exact absurd rfl hxy

theorem commute_of_mem_range (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    {x y : G} (hx : φ x ∈ theta.range) (hy : φ y ∈ theta.range) : x * y = y * x :=
  TripleCoverLift.commute_of_mem_closure hφ hker (commute_of_gen hφ hker) (range_theta_le hx)
    (range_theta_le hy)

theorem exists_lift_of_mem_range (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) {e : X₀} (he : e ∈ theta.range) :
    ∃ y : G, φ y = e ∧ y ^ 3 = 1 := by
  refine TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure (E := theta.range)
    (fun x hx y hy => commute_of_mem_range hφ hker hx hy) (S := {u1, u2}) ?_ ?_
    (range_theta_le he)
  · rintro _ (rfl | rfl)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · rintro _ (rfl | rfl)
    · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (by decide)
        (theta_pow_three _) (nBar_conj_theta _)
    · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (by decide)
        (theta_pow_three _) (nBar_conj_theta _)

end Lifts

theorem four_le_localRank_of_cover {G : Type} [Group G] [Finite G] (φ : G →* X₀)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) {Z : Subgroup G}
    (hZk : Z ≤ φ.ker) (hZp : ∀ z ∈ Z, z ^ 3 = 1) (hZ : 3 ^ 2 ≤ Nat.card Z) :
    4 ≤ localRank 3 G :=
  TripleCoverLift.add_le_localRank_of_lift hφ hker Nat.prime_three (by norm_num) hZk hZp hZ
    (E := theta.range) (fun _ hx _ hy => commute_of_mem_range hφ hker hx hy)
    (fun _ he => exists_lift_of_mem_range hφ hker he) tBar_ne_one tBar_sq
    (fun _ he => commute_tBar he) (r := 2) card_range_theta.ge

theorem lieModel_U43 : Blueprint.LieModel (projSU 4 3 1) .PSU 4 3 1 := by
  have hadm : StatedLieAdmissible .PSU 4 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hcl : StatedClassicalModel (projSU 4 3 1) .PSU 4 3 1 := by
    rcases lieModel_projSU (n := 4) (p := 3) (e := 1) hadm with ⟨-, h | ⟨h0, -⟩⟩
    · exact h
    · exact absurd h0 (by norm_num)
  exact Or.inl ⟨by decide, hcl⟩

theorem pow_twelve_eq_one : ∀ w : Multiplicative (ZMod 4 × ZMod 3 × ZMod 3), w ^ 12 = 1 := by
  decide

theorem pow_twelve_eq_one_of_mem_center
    {X : Type} [Group X]
    [Finite X] (hq : IsQuasisimple X) (e : X ⧸ Subgroup.center X ≃* projSU 4 3 1) {z : X}
    (hz : z ∈ Subgroup.center X) : z ^ 12 = 1 := by
  obtain ⟨-, ⟨eM⟩⟩ := multiplier_PSU_four_three _ lieModel_U43
  have : Group.IsPerfect X := hq.1
  set q := CFSG.RankThree.PerfectCover.centralQuotientMap e
  have hqs : Function.Surjective q := CFSG.RankThree.PerfectCover.centralQuotientMap_surjective e
  have hk : q.ker = Subgroup.center X := CFSG.RankThree.PerfectCover.centralQuotientMap_ker e
  let ψ : Multiplicative (ZMod 4 × ZMod 3 × ZMod 3) →* q.ker :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hqs hk.le).comp
      ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toMonoidHom.comp
        eM.symm.toMonoidHom)
  have hψ : Function.Surjective ψ :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hqs hk.le).comp
      ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).surjective.comp
        eM.symm.surjective)
  obtain ⟨w, hw⟩ := hψ ⟨z, hk ▸ hz⟩
  have h := congrArg (fun c : q.ker => (c : X)) (congrArg ψ (pow_twelve_eq_one w))
  simpa only [map_pow, hw, map_one, Subgroup.coe_pow, OneMemClass.coe_one] using h

theorem pow_three_eq_one_of_mem_center
    {X : Type} [Group X]
    [Finite X] (hq : IsQuasisimple X) (h9 : Nat.card (Subgroup.center X) = 9)
    (e : X ⧸ Subgroup.center X ≃* projSU 4 3 1) {z : X} (hz : z ∈ Subgroup.center X) :
    z ^ 3 = 1 := by
  have h12 := pow_twelve_eq_one_of_mem_center hq e hz
  have h9' : z ^ 9 = 1 := by
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Subgroup.center X))
    rw [h9] at h
    exact congrArg Subtype.val h
  have h3 := (pow_gcd_eq_one (m := 12) (n := 9)).mpr ⟨h12, h9'⟩
  rwa [show Nat.gcd 12 9 = 3 by norm_num] at h3

end NineCoverU43

open NineCoverU43 in
theorem nineCoverU43RankFour :
    NineCoverU43RankFour := by
  intro X _ _ hq h9 ⟨e⟩
  obtain ⟨eX⟩ := nonempty_mulEquiv_X₀ lieModel_U43
  let φ : X →* X₀ := (e.trans eX).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hφ : Function.Surjective φ :=
    (e.trans eX).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center X := by
    ext g
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact four_le_localRank_of_cover φ hφ hker.le hker.ge
    (fun z hz => pow_three_eq_one_of_mem_center hq h9 e hz) (by norm_num [h9])

end CFSG.RankThree.PartTwo.Sec4.Census
