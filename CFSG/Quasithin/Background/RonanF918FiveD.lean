module

public import CFSG.Quasithin.Background.RonanF918FiveK
public import CFSG.Quasithin.Background.RonanD321ModelSchur

public section

namespace CFSG.Quasithin.RonanF918

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.RonanD321.SL2Model
open scoped Matrix

section Schur

variable {F : Type} [Field F]

theorem eq_mul_of_commute_sl (Φ : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F)
    (hΦ : ∀ γ : ↥(StatedSL 2 F), ∀ X, Φ (slm γ * X) = slm γ * Φ X) (X : Matrix (Fin 2) (Fin 2) F) :
    Φ X = X * Φ 1 := by
  let S : AddSubgroup (Matrix (Fin 2) (Fin 2) F) :=
    { carrier := {A | ∀ Y, Φ (A * Y) = A * Φ Y}
      zero_mem' := fun Y => by simp
      add_mem' := fun {A B} hA hB Y => by
        simp only [add_mul, map_add, hA Y, hB Y]
      neg_mem' := fun {A} hA Y => by
        simp only [neg_mul, map_neg, hA Y] }
  have hone : (1 : Matrix (Fin 2) (Fin 2) F) ∈ S := fun Y => by simp
  have hmul : ∀ {A B : Matrix (Fin 2) (Fin 2) F}, A ∈ S → B ∈ S → A * B ∈ S := by
    intro A B hA hB Y
    rw [mul_assoc, hA (B * Y), hB Y, mul_assoc]
  have hoff : ∀ (i j : Fin 2), i ≠ j → ∀ c : F, Matrix.single i j c ∈ S := by
    intro i j hij c
    have hdet := Matrix.det_transvection_of_ne i j hij c
    have hmem : slm (slOf (Matrix.transvection i j c) hdet) ∈ S := fun Y => by
      rw [slm_slOf]
      exact hΦ (slOf _ hdet) Y |>.trans (by rw [slm_slOf])
    rw [slm_slOf] at hmem
    have h2 : Matrix.transvection i j c - 1 ∈ S := S.sub_mem hmem hone
    have e : Matrix.transvection i j c - 1 = Matrix.single i j c := by
      simp [Matrix.transvection]
    rwa [e] at h2
  have hall : ∀ (i j : Fin 2) (c : F), Matrix.single i j c ∈ S := by
    intro i j c
    by_cases hij : i = j
    · subst hij
      obtain ⟨k, hk⟩ : ∃ k : Fin 2, k ≠ i := by
        by_cases h0 : i = 0
        · exact ⟨1, by rw [h0]; decide⟩
        · exact ⟨0, fun h => h0 h.symm⟩
      have e : Matrix.single i i c = Matrix.single i k c * Matrix.single k i (1 : F) := by
        rw [Matrix.single_mul_single_same]
        simp
      rw [e]
      exact hmul (hoff i k hk.symm c) (hoff k i hk 1)
    · exact hoff i j hij c
  have hX : X ∈ S := by
    rw [Matrix.matrix_eq_sum_single X]
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => hall i j _
  have := hX 1
  simpa using this

end Schur

section Commutant

variable {F : Type} [Field F]

@[expose] noncomputable def multOpU (F : Type) [Field F]
    (matrix : Matrix.GeneralLinearGroup (Fin 2) F)
    (vector : Multiplicative (Matrix (Fin 2) (Fin 2) F)) : Multiplicative (Matrix (Fin 2) (Fin 2) F) :=
  Multiplicative.ofAdd (Multiplicative.toAdd vector * Matrix.transpose (matrix : Matrix (Fin 2) (Fin 2) F))

theorem commutantCore (F : Type) [Field F]
    (operator : MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F)))
    (hcomm : ∀ element : ↥(StatedSL 2 F), ∀ matrix : Matrix (Fin 2) (Fin 2) F,
      operator (Multiplicative.ofAdd
        (((element : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * matrix)) =
      Multiplicative.ofAdd
        (((element : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Multiplicative.toAdd (operator (Multiplicative.ofAdd matrix)))) :
    ∃ uniqueMatrix : Matrix.GeneralLinearGroup (Fin 2) F,
      (∀ vector, operator vector = multOpU F uniqueMatrix vector) ∧
      ∀ otherMatrix : Matrix.GeneralLinearGroup (Fin 2) F,
        (∀ vector, operator vector = multOpU F otherMatrix vector) → otherMatrix = uniqueMatrix := by
  let Φ : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F :=
    AddMonoidHom.mk' (fun X => Multiplicative.toAdd (operator (Multiplicative.ofAdd X))) (fun X Y => by
      rw [ofAdd_add, map_mul, toAdd_mul])
  have hΦ : ∀ γ : ↥(StatedSL 2 F), ∀ X, Φ (slm γ * X) = slm γ * Φ X := fun γ X =>
    congrArg Multiplicative.toAdd (hcomm γ X)
  have hform : ∀ X, Φ X = X * Φ 1 := eq_mul_of_commute_sl Φ hΦ
  set C : Matrix (Fin 2) (Fin 2) F := Φ 1 with hC
  have hCu : IsUnit C := by
    obtain ⟨v, hv⟩ := operator.surjective (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) F))
    have h1 : Φ (Multiplicative.toAdd v) = 1 := by
      show Multiplicative.toAdd (operator (Multiplicative.ofAdd (Multiplicative.toAdd v))) = 1
      rw [ofAdd_toAdd, hv]
      rfl
    rw [hform] at h1
    have hdet := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    rw [Matrix.isUnit_iff_isUnit_det]
    exact IsUnit.of_mul_eq_one_right _ hdet
  have hCt : IsUnit (Cᵀ).det := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det C).1 hCu
  let B : Matrix.GeneralLinearGroup (Fin 2) F := Matrix.GeneralLinearGroup.mk'' Cᵀ hCt
  have hBc : ((B : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Cᵀ := rfl
  have hop : ∀ v, operator v = multOpU F B v := by
    intro v
    unfold multOpU
    rw [hBc, Matrix.transpose_transpose]
    have h1 := hform (Multiplicative.toAdd v)
    have h2 : Φ (Multiplicative.toAdd v) = Multiplicative.toAdd (operator v) := by
      show Multiplicative.toAdd (operator (Multiplicative.ofAdd (Multiplicative.toAdd v))) = _
      rw [ofAdd_toAdd]
    rw [h2] at h1
    rw [← h1, ofAdd_toAdd]
  refine ⟨B, hop, fun B' hB' => ?_⟩
  have h1 := hB' (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) F))
  rw [hop] at h1
  unfold multOpU at h1
  have h2 := congrArg Multiplicative.toAdd h1
  simp only [toAdd_ofAdd, Matrix.one_mul, hBc, Matrix.transpose_transpose] at h2
  apply Units.ext
  show ((B' : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Cᵀ
  rw [h2, Matrix.transpose_transpose]

theorem fullCommutantU (F : Type) [Field F]
    (operator : MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F)))
    (_hlin : ∀ (scalar : F) (matrix : Matrix (Fin 2) (Fin 2) F),
      operator (Multiplicative.ofAdd (scalar • matrix)) =
      Multiplicative.ofAdd (scalar • Multiplicative.toAdd (operator (Multiplicative.ofAdd matrix))))
    (hcomm : ∀ element : ↥(StatedSL 2 F), ∀ matrix : Matrix (Fin 2) (Fin 2) F,
      operator (Multiplicative.ofAdd
        (((element : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * matrix)) =
      Multiplicative.ofAdd
        (((element : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Multiplicative.toAdd (operator (Multiplicative.ofAdd matrix)))) :
    ∃ uniqueMatrix : Matrix.GeneralLinearGroup (Fin 2) F,
      (∀ vector, operator vector = multOpU F uniqueMatrix vector) ∧
      ∀ otherMatrix : Matrix.GeneralLinearGroup (Fin 2) F,
        (∀ vector, operator vector = multOpU F otherMatrix vector) → otherMatrix = uniqueMatrix :=
  commutantCore F operator hcomm

@[expose] noncomputable def multOpHom (B : Matrix.GeneralLinearGroup (Fin 2) F) :
    Multiplicative (Matrix (Fin 2) (Fin 2) F) →* Multiplicative (Matrix (Fin 2) (Fin 2) F) where
  toFun := multOpU F B
  map_one' := by
    show Multiplicative.ofAdd (Multiplicative.toAdd (1 : Multiplicative (Matrix (Fin 2) (Fin 2) F)) *
      Matrix.transpose (B : Matrix (Fin 2) (Fin 2) F)) = 1
    rw [show Multiplicative.toAdd (1 : Multiplicative (Matrix (Fin 2) (Fin 2) F)) = 0 from rfl, zero_mul]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (Multiplicative.toAdd (x * y) * Matrix.transpose (B : Matrix (Fin 2) (Fin 2) F)) =
      Multiplicative.ofAdd (Multiplicative.toAdd x * Matrix.transpose (B : Matrix (Fin 2) (Fin 2) F)) *
        Multiplicative.ofAdd (Multiplicative.toAdd y * Matrix.transpose (B : Matrix (Fin 2) (Fin 2) F))
    rw [toAdd_mul, add_mul]
    rfl

theorem multOpU_mul (B B' : Matrix.GeneralLinearGroup (Fin 2) F)
    (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) :
    multOpU F B (multOpU F B' Y) = multOpU F (B * B') Y := by
  unfold multOpU
  rw [toAdd_ofAdd, Units.val_mul, Matrix.transpose_mul, mul_assoc]

theorem multOpU_one (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) : multOpU F 1 Y = Y := by
  unfold multOpU
  rw [Units.val_one, Matrix.transpose_one, mul_one, ofAdd_toAdd]

@[expose] noncomputable def rmulAut (B : Matrix.GeneralLinearGroup (Fin 2) F) :
    MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F)) :=
  MonoidHom.toMulEquiv (multOpHom B) (multOpHom B⁻¹)
    (MonoidHom.ext fun Y => by
      show multOpU F B⁻¹ (multOpU F B Y) = Y
      rw [multOpU_mul, inv_mul_cancel, multOpU_one])
    (MonoidHom.ext fun Y => by
      show multOpU F B (multOpU F B⁻¹ Y) = Y
      rw [multOpU_mul, mul_inv_cancel, multOpU_one])

theorem rmulAut_apply (B : Matrix.GeneralLinearGroup (Fin 2) F)
    (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) : rmulAut B Y = multOpU F B Y := rfl

end Commutant

section Coord

variable {W : Type} [CommGroup W] {F : Type} [Field F]

theorem exists_coord_mod {n : ℕ} {L : Subgroup (MulAut W)} {U Z : Subgroup W} (π : ↥(StatedSL n F) →* ↥L)
    (hreal : (FFModel.nat (StatedSL n F)).RealizesVia L U Z π) :
    ∃ b : ↥U →* Multiplicative (Fin n → F), Function.Surjective b ∧ (∀ u : ↥U, b u = 1 ↔ (u : W) ∈ Z) ∧
      ∀ (γ : ↥(StatedSL n F)) (u : ↥U) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ U),
        b ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ = natAct (StatedSL n F) γ (b u) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hreal
  let q := topBotQuotEquiv (Multiplicative (Fin n → F))
  let b0 : ↥U →* Multiplicative (Fin n → F) := q.toMonoidHom.comp β
  refine ⟨b0, q.surjective.comp hβs, fun u => ?_, ?_⟩
  · exact (MulEquiv.map_eq_one_iff q).trans (hβk u)
  · intro γ u hu
    show b0 ⟨_, hu⟩ = natAct (StatedSL n F) γ (b0 u)
    have hum : β u = QuotientGroup.mk
        (⟨b0 u, trivial⟩ : ↥(⊤ : Subgroup (Multiplicative (Fin n → F)))) := by
      apply q.injective
      rfl
    exact congrArg q (hβe γ u ⟨b0 u, trivial⟩ hu trivial hum)

theorem liftOfSurjective_apply {G₁ G₂ G₃ : Type} [Group G₁] [Group G₂] [Group G₃] (f : G₁ →* G₂)
    (hf : Function.Surjective f) (g : {g : G₁ →* G₃ // f.ker ≤ g.ker}) (x : G₁) :
    (MonoidHom.liftOfSurjective f hf g) (f x) = g.1 x :=
  MonoidHom.liftOfRightInverse_comp_apply f _ _ g x

theorem exists_bq {L : Subgroup (MulAut W)} {U Z : Subgroup W} (I : Fin 2 → Subgroup W)
    (π : ↥(StatedSL 2 F) →* ↥L) (hZI : ∀ i, Z ≤ I i)
    (hind : ∀ i, I i ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), I j) = Z) (hU : Z ⊔ ⨆ i, I i = U)
    (hreal : ∀ i, (FFModel.nat (StatedSL 2 F)).RealizesVia L (I i) Z π) :
    ∃ bq : ↥U →* Multiplicative (Matrix (Fin 2) (Fin 2) F), Function.Surjective bq ∧
      (∀ u : ↥U, bq u = 1 ↔ (u : W) ∈ Z) ∧
      ∀ (γ : ↥(StatedSL 2 F)) (u : ↥U) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ U),
        bq ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
          Multiplicative.ofAdd (slm γ * Multiplicative.toAdd (bq u)) := by
  choose b hbs hbk hbe using fun i => exists_coord_mod π (hreal i)
  have hinv : ∀ (g : ↥L) i, ∀ u ∈ I i, (g : MulAut W) u ∈ I i :=
    fun g i u hu => (hreal i).2.2.2.1 g u hu
  let P : (∀ i, ↥(I i)) →* W := prodSubHom I
  have hrangeP : P.range = U := by
    refine (prodSubHom_range I).trans (le_antisymm ?_ ?_)
    · rw [← hU]
      exact le_sup_right
    · rw [← hU]
      exact sup_le (le_trans (hZI 0) (le_iSup I 0)) le_rfl
  have hmem : ∀ x, P x ∈ U := fun x => hrangeP ▸ (⟨x, rfl⟩ : P x ∈ P.range)
  let P' : (∀ i, ↥(I i)) →* ↥U := P.codRestrict U hmem
  have hP'val : ∀ x, ((P' x : ↥U) : W) = ∏ i, (x i : W) := fun x => rfl
  have hP's : Function.Surjective P' := by
    intro u
    obtain ⟨x, hx⟩ : (u : W) ∈ P.range := hrangeP ▸ u.2
    exact ⟨x, Subtype.ext hx⟩
  let Bmap : (∀ i, ↥(I i)) →* Multiplicative (Matrix (Fin 2) (Fin 2) F) :=
    (colsToMatrix 2 2 F).toMonoidHom.comp
      (Pi.monoidHom fun i => (b i).comp (Pi.evalMonoidHom (fun i => ↥(I i)) i))
  have hBmap : ∀ x, Bmap x = colsToMatrix 2 2 F (fun i => b i (x i)) := fun x => rfl
  have hI01 : I 0 ⊓ I 1 ≤ Z := by
    have h1 : I 1 ≤ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
      le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl
    have h2 : I 0 ⊓ I 1 ≤ I 0 ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j) :=
      inf_le_inf_left _ (le_sup_of_le_right h1)
    rwa [hind 0] at h2
  have hxZ : ∀ x : (∀ i, ↥(I i)), ((P' x : ↥U) : W) = 1 → ∀ i, (x i : W) ∈ Z := by
    intro x hx
    rw [hP'val, Fin.prod_univ_two] at hx
    have h0 : (x 0 : W) = ((x 1 : W))⁻¹ := eq_inv_of_mul_eq_one_left hx
    have h1 : (x 0 : W) ∈ I 1 := h0 ▸ (I 1).inv_mem (x 1).2
    have hz0 : (x 0 : W) ∈ Z := hI01 ⟨(x 0).2, h1⟩
    have hz1 : (x 1 : W) ∈ Z := by
      have : (x 1 : W) = ((x 0 : W))⁻¹ := by rw [h0, inv_inv]
      rw [this]
      exact Z.inv_mem hz0
    intro i
    fin_cases i
    · exact hz0
    · exact hz1
  have hker : P'.ker ≤ Bmap.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : ((P' x : ↥U) : W) = 1 := by rw [hx]; rfl
    have hz := hxZ x hx'
    rw [hBmap]
    have : (fun i => b i (x i)) = 1 := funext fun i => (hbk i (x i)).mpr (hz i)
    rw [this, map_one]
  let bq : ↥U →* Multiplicative (Matrix (Fin 2) (Fin 2) F) :=
    (MonoidHom.liftOfSurjective P' hP's) ⟨Bmap, hker⟩
  have hbq : ∀ x, bq (P' x) = Bmap x := fun x => liftOfSurjective_apply P' hP's ⟨Bmap, hker⟩ x
  refine ⟨bq, ?_, ?_, ?_⟩
  · intro Y
    let c := (colsToMatrix 2 2 F).symm Y
    choose x hx using fun i => hbs i (c i)
    refine ⟨P' x, ?_⟩
    rw [hbq, hBmap]
    have : (fun i => b i (x i)) = c := funext hx
    rw [this]
    exact (colsToMatrix 2 2 F).apply_symm_apply Y
  · intro u
    obtain ⟨x, rfl⟩ := hP's u
    rw [hbq, hBmap]
    constructor
    · intro h1
      have h2 : (fun i => b i (x i)) = 1 := by
        apply (colsToMatrix 2 2 F).injective
        rw [h1, map_one]
      have hz : ∀ i, (x i : W) ∈ Z := fun i => (hbk i (x i)).mp (congrFun h2 i)
      rw [hP'val, Fin.prod_univ_two]
      exact Z.mul_mem (hz 0) (hz 1)
    · intro hu
      rw [hP'val, Fin.prod_univ_two] at hu
      have h1 : I 1 ≤ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
        le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl
      have hx0 : (x 0 : W) ∈ Z := by
        have h2 : (x 0 : W) ∈ Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j := by
          have e : (x 0 : W) = ((x 0 : W) * (x 1 : W)) * ((x 1 : W))⁻¹ := by
            rw [mul_inv_cancel_right]
          rw [e]
          exact (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j).mul_mem (Subgroup.mem_sup_left hu)
            ((Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j).inv_mem (Subgroup.mem_sup_right (h1 (x 1).2)))
        have h3 : (x 0 : W) ∈ I 0 ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j) := ⟨(x 0).2, h2⟩
        rwa [hind 0] at h3
      have hx1 : (x 1 : W) ∈ Z := by
        have e : (x 1 : W) = ((x 0 : W))⁻¹ * ((x 0 : W) * (x 1 : W)) := by
          rw [inv_mul_cancel_left]
        rw [e]
        exact Z.mul_mem (Z.inv_mem hx0) hu
      have h2 : (fun i => b i (x i)) = 1 := funext fun i =>
        (hbk i (x i)).mpr (by
          fin_cases i
          · exact hx0
          · exact hx1)
      rw [h2, map_one]
  · intro γ u hu
    obtain ⟨x, rfl⟩ := hP's u
    let y : ∀ i, ↥(I i) := fun i => ⟨((π γ : ↥L) : MulAut W) (x i : W), hinv _ i _ (x i).2⟩
    have hy : (⟨((π γ : ↥L) : MulAut W) ((P' x : ↥U) : W), hu⟩ : ↥U) = P' y := by
      apply Subtype.ext
      show ((π γ : ↥L) : MulAut W) ((P' x : ↥U) : W) = ((P' y : ↥U) : W)
      rw [hP'val, hP'val, map_prod]
    rw [hy, hbq, hbq, hBmap, hBmap]
    have h1 : (fun i => b i (y i)) = fun i => natAct (StatedSL 2 F) γ (b i (x i)) := by
      funext i
      exact hbe i γ (x i) (hinv _ i _ (x i).2)
    rw [h1, colsToMatrix_natAct]

end Coord

section CoordData

variable {W : Type} [CommGroup W]

structure CoordData (L Mp : Subgroup (MulAut W)) (F : Type) [Field F] where
  pi : ↥(StatedSL 2 F) →* ↥L
  bq : ↥(commV L) →* Multiplicative (Matrix (Fin 2) (Fin 2) F)
  pi_surj : Function.Surjective pi
  pi_inj : Function.Injective pi
  bq_surj : Function.Surjective bq
  bq_ker : ∀ u : ↥(commV L), bq u = 1 ↔ (u : W) ∈ fixV Mp
  bq_equiv : ∀ (γ : ↥(StatedSL 2 F)) (u : ↥(commV L))
    (hu : ((pi γ : ↥L) : MulAut W) (u : W) ∈ commV L),
    bq ⟨((pi γ : ↥L) : MulAut W) (u : W), hu⟩ = Multiplicative.ofAdd (slm γ * Multiplicative.toAdd (bq u))

theorem coordData_of_d321Three [Finite W] {Mp L : Subgroup (MulAut W)} (h : D321Three Mp L) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧ 2 ≤ n ∧
      IsPSL 2 2 n ↥L ∧ Nonempty (CoordData L Mp F) := by
  obtain ⟨n, hpsl, F, hF, hFin, hcard, I, π0, hZI, hind, hsup, hreal⟩ := h
  let π : ↥(StatedSL 2 F) →* ↥L := π0
  have hn : 2 ≤ n := by
    obtain ⟨⟨-, hn1, -, hne, -⟩, -⟩ := hpsl
    by_contra hlt
    have h1 : n = 1 := by omega
    subst h1
    exact hne rfl
  obtain ⟨bq, hbs, hbk, hbe⟩ := exists_bq (L := L) (U := commV L) (Z := commV L ⊓ fixV Mp) I π hZI hind
    hsup hreal
  have hπs : Function.Surjective π := (hreal 0).1
  haveI : IsSimpleGroup ↥(StatedSL 2 F) := isSimpleGroup_statedSL_two hn hcard
  haveI : Nontrivial ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n hpsl).1
  have hπi : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hbot | htop
    · exact (MonoidHom.ker_eq_bot_iff π).mp hbot
    · exfalso
      obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
      obtain ⟨γ, rfl⟩ := hπs l
      exact hl (MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top γ))
  exact ⟨n, F, hF, hFin, hcard, hn, hpsl, ⟨⟨π, bq, hπs, hπi, hbs, fun u => (hbk u).trans
    ⟨fun hh => hh.2, fun hh => ⟨u.2, hh⟩⟩, hbe⟩⟩⟩

end CoordData

section Psi

variable {W : Type} [CommGroup W] [Finite W] {L Mp : Subgroup (MulAut W)} {F : Type} [Field F]

abbrev NLM (L Mp : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  Subgroup.normalizer (L : Set (MulAut W)) ⊓ Subgroup.normalizer (Mp : Set (MulAut W))

theorem apply_mem_commV {g : MulAut W} (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) {u : W}
    (hu : u ∈ commV L) : g u ∈ commV L := by
  have h1 : conjAutSub g L = L := A38.map_conj_eq_iff.mpr hg
  have h2 : commV (conjAutSub g L) = (commV L).map g.toMonoidHom := commV_map_conj_eq L g
  rw [h1] at h2
  have h3 : g u ∈ (commV L).map g.toMonoidHom := ⟨u, hu, rfl⟩
  rwa [← h2] at h3

@[expose] noncomputable def gU (g : ↥(NLM L Mp)) : ↥(commV L) →* ↥(commV L) :=
  (((g : ↥(NLM L Mp)) : MulAut W).toMonoidHom.comp (commV L).subtype).codRestrict (commV L)
    (fun u => apply_mem_commV g.2.1 u.2)

theorem gU_coe (g : ↥(NLM L Mp)) (u : ↥(commV L)) :
    ((gU g u : ↥(commV L)) : W) = ((g : ↥(NLM L Mp)) : MulAut W) (u : W) := rfl

variable (D : CoordData L Mp F)

@[expose] noncomputable def psi0 (g : ↥(NLM L Mp)) : Multiplicative (Matrix (Fin 2) (Fin 2) F) →*
    Multiplicative (Matrix (Fin 2) (Fin 2) F) :=
  (MonoidHom.liftOfSurjective D.bq D.bq_surj)
    ⟨D.bq.comp (gU g), fun u hu => by
      rw [MonoidHom.mem_ker] at hu ⊢
      have hu' : (u : W) ∈ fixV Mp := (D.bq_ker u).mp hu
      exact (D.bq_ker _).mpr (apply_mem_fixV_of_mem_normalizer g.2.2 hu')⟩

theorem psi0_apply (g : ↥(NLM L Mp)) (u : ↥(commV L)) : psi0 D g (D.bq u) = D.bq (gU g u) :=
  liftOfSurjective_apply D.bq D.bq_surj _ u

theorem psi0_mul (g g' : ↥(NLM L Mp)) (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) :
    psi0 D (g * g') Y = psi0 D g (psi0 D g' Y) := by
  obtain ⟨u, rfl⟩ := D.bq_surj Y
  rw [psi0_apply, psi0_apply, psi0_apply]
  congr 1

theorem psi0_one (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) : psi0 D 1 Y = Y := by
  obtain ⟨u, rfl⟩ := D.bq_surj Y
  rw [psi0_apply]
  rfl

@[expose] noncomputable def psi : ↥(NLM L Mp) →* MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F)) where
  toFun g := MonoidHom.toMulEquiv (psi0 D g) (psi0 D g⁻¹)
    (MonoidHom.ext fun Y => by
      show psi0 D g⁻¹ (psi0 D g Y) = Y
      rw [← psi0_mul, inv_mul_cancel, psi0_one])
    (MonoidHom.ext fun Y => by
      show psi0 D g (psi0 D g⁻¹ Y) = Y
      rw [← psi0_mul, mul_inv_cancel, psi0_one])
  map_one' := MulEquiv.ext fun Y => psi0_one D Y
  map_mul' g g' := MulEquiv.ext fun Y => psi0_mul D g g' Y

theorem psi_apply (g : ↥(NLM L Mp)) (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)) :
    psi D g Y = psi0 D g Y := rfl

theorem psi_comm_left (g : ↥(NLM L Mp)) (hg : ∀ l ∈ L, (g : MulAut W) * l = l * (g : MulAut W))
    (γ : ↥(StatedSL 2 F)) (X : Matrix (Fin 2) (Fin 2) F) :
    psi D g (Multiplicative.ofAdd (slm γ * X)) =
      Multiplicative.ofAdd (slm γ * Multiplicative.toAdd (psi D g (Multiplicative.ofAdd X))) := by
  obtain ⟨u, hu⟩ := D.bq_surj (Multiplicative.ofAdd X)
  have hπL : ((D.pi γ : ↥L) : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.le_normalizer (D.pi γ).2
  have hpu : ((D.pi γ : ↥L) : MulAut W) (u : W) ∈ commV L := apply_mem_commV hπL u.2
  have h1 := D.bq_equiv γ u hpu
  rw [hu, toAdd_ofAdd] at h1
  rw [← h1, psi_apply, psi0_apply]
  have hcomm : ((g : MulAut W)) (((D.pi γ : ↥L) : MulAut W) (u : W)) =
      ((D.pi γ : ↥L) : MulAut W) ((g : MulAut W) (u : W)) := by
    have := hg _ (D.pi γ).2
    exact congrArg (fun φ : MulAut W => φ (u : W)) this
  have hgu : (g : MulAut W) (u : W) ∈ commV L := apply_mem_commV g.2.1 u.2
  have hpgu : ((D.pi γ : ↥L) : MulAut W) ((g : MulAut W) (u : W)) ∈ commV L :=
    apply_mem_commV hπL hgu
  have h2 : gU g ⟨((D.pi γ : ↥L) : MulAut W) (u : W), hpu⟩ =
      ⟨((D.pi γ : ↥L) : MulAut W) ((g : MulAut W) (u : W)), hpgu⟩ := Subtype.ext hcomm
  rw [h2]
  have h3 : D.bq ⟨((D.pi γ : ↥L) : MulAut W) ((g : MulAut W) (u : W)), hpgu⟩ =
      Multiplicative.ofAdd (slm γ * Multiplicative.toAdd (D.bq (gU g u))) :=
    D.bq_equiv γ (gU g u) hpgu
  rw [h3, ← psi0_apply, hu]
  rfl

theorem centralizer_le_NLM (hLMp : L ≤ Mp) :
    Subgroup.centralizer (Mp : Set (MulAut W)) ≤ NLM L Mp := by
  intro g hg
  refine ⟨Subgroup.mem_normalizer_iff.mpr fun h => ?_,
    (Subgroup.centralizer_le_normalizer (Mp : Set (MulAut W))) hg⟩
  have hc : ∀ l' ∈ Mp, l' * g = g * l' := fun l' hl' => Subgroup.mem_centralizer_iff.mp hg l' hl'
  constructor
  · intro hl
    have h1 := hc h (hLMp hl)
    have e : g * h * g⁻¹ = h := by rw [← h1]; group
    rw [e]
    exact hl
  · intro hl
    have h1 := hc _ (hLMp hl)
    have e1 : g * h * g⁻¹ * g = g * h := by group
    rw [e1] at h1
    have e2 : h = g * h * g⁻¹ := mul_left_cancel h1
    rw [e2]
    exact hl

theorem exists_mult (hLMp : L ≤ Mp) :
    ∃ m : ↥(Subgroup.centralizer (Mp : Set (MulAut W))) →* Matrix.GeneralLinearGroup (Fin 2) F,
      ∀ (g : ↥(Subgroup.centralizer (Mp : Set (MulAut W))))
        (Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)),
        psi D (Subgroup.inclusion (centralizer_le_NLM hLMp) g) Y = multOpU F (m g) Y := by
  let ι := Subgroup.inclusion (centralizer_le_NLM (L := L) hLMp)
  have hex : ∀ g, ∃ B : Matrix.GeneralLinearGroup (Fin 2) F,
      (∀ Y, psi D (ι g) Y = multOpU F B Y) ∧
      ∀ B', (∀ Y, psi D (ι g) Y = multOpU F B' Y) → B' = B := by
    intro g
    refine commutantCore F (psi D (ι g)) ?_
    intro γ X
    exact psi_comm_left D (ι g) (fun l hl => (Subgroup.mem_centralizer_iff.mp g.2 l (hLMp hl)).symm) γ X
  choose m hm hu using hex
  refine ⟨{ toFun := m, map_one' := ?_, map_mul' := ?_ }, hm⟩
  · have h1 : ∀ Y, psi D (ι 1) Y = multOpU F 1 Y := fun Y => by
      rw [map_one ι, map_one (psi D), MulAut.one_apply, multOpU_one]
    exact (hu 1 1 h1).symm
  · intro g g'
    refine (hu (g * g') (m g * m g') ?_).symm
    intro Y
    rw [map_mul ι, map_mul (psi D), MulAut.mul_apply, hm g', hm g, multOpU_mul]

theorem psi_twist (g : ↥(NLM L Mp)) (δ : ↥(StatedSL 2 F)) :
    ∃ γ : ↥(StatedSL 2 F), ∀ X : Matrix (Fin 2) (Fin 2) F,
      psi D g (Multiplicative.ofAdd (slm γ * X)) =
        Multiplicative.ofAdd (slm δ * Multiplicative.toAdd (psi D g (Multiplicative.ofAdd X))) := by
  have hginv : (g : MulAut W)⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.inv_mem_iff _).mpr g.2.1
  have hmem : (g : MulAut W)⁻¹ * ((D.pi δ : ↥L) : MulAut W) * ((g : MulAut W)⁻¹)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hginv _).mp (D.pi δ).2
  obtain ⟨γ, hγ⟩ := D.pi_surj ⟨_, hmem⟩
  refine ⟨γ, fun X => ?_⟩
  have hγ' : ((D.pi γ : ↥L) : MulAut W) = (g : MulAut W)⁻¹ * ((D.pi δ : ↥L) : MulAut W) *
      ((g : MulAut W)⁻¹)⁻¹ := congrArg Subtype.val hγ
  obtain ⟨u, hu⟩ := D.bq_surj (Multiplicative.ofAdd X)
  have hπL : ∀ γ' : ↥(StatedSL 2 F), ((D.pi γ' : ↥L) : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    fun γ' => Subgroup.le_normalizer (D.pi γ').2
  have hpu : ((D.pi γ : ↥L) : MulAut W) (u : W) ∈ commV L := apply_mem_commV (hπL γ) u.2
  have h1 := D.bq_equiv γ u hpu
  rw [hu, toAdd_ofAdd] at h1
  rw [← h1, psi_apply, psi0_apply]
  have hgu : (g : MulAut W) (u : W) ∈ commV L := apply_mem_commV g.2.1 u.2
  have hpgu : ((D.pi δ : ↥L) : MulAut W) ((g : MulAut W) (u : W)) ∈ commV L :=
    apply_mem_commV (hπL δ) hgu
  have hcomm : (g : MulAut W) (((D.pi γ : ↥L) : MulAut W) (u : W)) =
      ((D.pi δ : ↥L) : MulAut W) ((g : MulAut W) (u : W)) := by
    rw [hγ']
    simp [MulAut.mul_apply]
  have h2 : gU g ⟨((D.pi γ : ↥L) : MulAut W) (u : W), hpu⟩ =
      ⟨((D.pi δ : ↥L) : MulAut W) ((g : MulAut W) (u : W)), hpgu⟩ := Subtype.ext hcomm
  rw [h2]
  have h3 : D.bq ⟨((D.pi δ : ↥L) : MulAut W) ((g : MulAut W) (u : W)), hpgu⟩ =
      Multiplicative.ofAdd (slm δ * Multiplicative.toAdd (D.bq (gU g u))) :=
    D.bq_equiv δ (gU g u) hpgu
  rw [h3, ← psi0_apply, hu]
  rfl

theorem psi_conj_rmul (g : ↥(NLM L Mp)) (B : Matrix.GeneralLinearGroup (Fin 2) F) :
    ∃ B' : Matrix.GeneralLinearGroup (Fin 2) F, ∀ Y : Multiplicative (Matrix (Fin 2) (Fin 2) F),
      psi D g (multOpU F B Y) = multOpU F B' (psi D g Y) := by
  have hex := commutantCore F ((psi D g) * rmulAut B * (psi D g)⁻¹) (by
    intro δ X
    obtain ⟨γ, hγ⟩ := psi_twist D g δ
    have hinv : ∀ Z : Matrix (Fin 2) (Fin 2) F,
        (psi D g)⁻¹ (Multiplicative.ofAdd (slm δ * Z)) =
          Multiplicative.ofAdd (slm γ * Multiplicative.toAdd ((psi D g)⁻¹ (Multiplicative.ofAdd Z))) := by
      intro Z
      apply (psi D g).injective
      rw [MulAut.apply_inv_self]
      have := hγ (Multiplicative.toAdd ((psi D g)⁻¹ (Multiplicative.ofAdd Z)))
      rw [ofAdd_toAdd, MulAut.apply_inv_self, toAdd_ofAdd] at this
      rw [this]
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hinv]
    have hZ' : (psi D g)⁻¹ (Multiplicative.ofAdd X) =
        Multiplicative.ofAdd (Multiplicative.toAdd ((psi D g)⁻¹ (Multiplicative.ofAdd X))) :=
      (ofAdd_toAdd _).symm
    rw [hZ']
    generalize Multiplicative.toAdd ((psi D g)⁻¹ (Multiplicative.ofAdd X)) = Z
    simp only [toAdd_ofAdd]
    have hρ : (rmulAut B) (Multiplicative.ofAdd (slm γ * Z)) =
        Multiplicative.ofAdd (slm γ * Multiplicative.toAdd ((rmulAut B) (Multiplicative.ofAdd Z))) := by
      rw [rmulAut_apply, rmulAut_apply]
      unfold multOpU
      simp only [toAdd_ofAdd, Matrix.mul_assoc]
    rw [hρ]
    have := hγ (Multiplicative.toAdd ((rmulAut B) (Multiplicative.ofAdd Z)))
    rw [ofAdd_toAdd] at this
    exact this)
  obtain ⟨B', hB', -⟩ := hex
  refine ⟨B', fun Y => ?_⟩
  have := hB' (psi D g Y)
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, rmulAut_apply] at this
  exact this

theorem psi_twist' [Finite F] (g : ↥(NLM L Mp)) (γ : ↥(StatedSL 2 F)) :
    ∃ δ : ↥(StatedSL 2 F), ∀ X : Matrix (Fin 2) (Fin 2) F,
      psi D g (Multiplicative.ofAdd (slm γ * X)) =
        Multiplicative.ofAdd (slm δ * Multiplicative.toAdd (psi D g (Multiplicative.ofAdd X))) := by
  obtain ⟨δ, hδ⟩ := psi_twist D g⁻¹ γ
  refine ⟨δ, fun X => ?_⟩
  have h1 := hδ (Multiplicative.toAdd (psi D g (Multiplicative.ofAdd X)))
  rw [ofAdd_toAdd, map_inv, MulAut.inv_apply_self, toAdd_ofAdd] at h1
  have h2 := congrArg (psi D g) h1
  rw [MulAut.apply_inv_self] at h2
  rw [← h2]

@[expose] def SemiWith (ψ : MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F))) (σ : F ≃+* F) : Prop :=
  ∀ (c : F) (X : Matrix (Fin 2) (Fin 2) F),
    Multiplicative.toAdd (ψ (Multiplicative.ofAdd (c • X))) =
      σ c • Multiplicative.toAdd (ψ (Multiplicative.ofAdd X))

theorem exists_semi_psi [Finite F] (g : ↥(NLM L Mp)) : ∃ σ : F ≃+* F, SemiWith (psi D g) σ := by
  let Φ : Matrix (Fin 2) (Fin 2) F →+ Matrix (Fin 2) (Fin 2) F :=
    AddMonoidHom.mk' (fun X => Multiplicative.toAdd (psi D g (Multiplicative.ofAdd X))) (fun X Y => by
      rw [ofAdd_add, map_mul, toAdd_mul])
  have hΦ : ∀ X, Φ X = Multiplicative.toAdd (psi D g (Multiplicative.ofAdd X)) := fun X => rfl
  have hΦi : Function.Injective Φ := by
    intro X Y h
    rw [hΦ, hΦ] at h
    have := (psi D g).injective (Multiplicative.toAdd.injective h)
    exact Multiplicative.ofAdd.injective this
  choose α hα using psi_twist' D g
  have hαs : Function.Surjective α := by
    intro δ
    obtain ⟨γ, hγ⟩ := psi_twist D g δ
    refine ⟨γ, ?_⟩
    apply slm_injective
    set Z0 := (psi D g).symm (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) F)) with hZ0def
    have hZ0 : psi D g (Multiplicative.ofAdd (Multiplicative.toAdd Z0)) = Multiplicative.ofAdd 1 := by
      rw [ofAdd_toAdd]
      exact (psi D g).apply_symm_apply _
    have h1 := (hα γ (Multiplicative.toAdd Z0)).symm.trans (hγ (Multiplicative.toAdd Z0))
    rw [hZ0, toAdd_ofAdd, mul_one, mul_one] at h1
    exact Multiplicative.ofAdd.injective h1
  have htw : ∀ γ X, Φ (slm γ * X) = slm (α γ) * Φ X := by
    intro γ X
    rw [hΦ, hΦ, hα γ X, toAdd_ofAdd]
  obtain ⟨σ, A, B, hA, hB, hform, -⟩ := exists_semilinear_form Φ hΦi hαs htw
  refine ⟨σ, fun c X => ?_⟩
  have h1 := hform (c • X)
  have h2 := hform X
  rw [hΦ] at h1 h2
  rw [h1, h2]
  have e : (c • X).map σ = σ c • X.map σ := by
    ext i j
    simp
  rw [e, Matrix.mul_smul, Matrix.smul_mul]

theorem SemiWith.one : SemiWith (1 : MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F))) (1 : F ≃+* F) :=
  fun c X => by
    rw [MulAut.one_apply, toAdd_ofAdd, MulAut.one_apply, toAdd_ofAdd]
    rfl

theorem SemiWith.mul {ψ ψ' : MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F))} {σ τ : F ≃+* F}
    (h : SemiWith ψ σ) (h' : SemiWith ψ' τ) : SemiWith (ψ * ψ') (σ * τ) := by
  intro c X
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have h1 : ψ' (Multiplicative.ofAdd (c • X)) =
      Multiplicative.ofAdd (τ c • Multiplicative.toAdd (ψ' (Multiplicative.ofAdd X))) := by
    rw [← h' c X, ofAdd_toAdd]
  rw [h1, h (τ c) _, ofAdd_toAdd]
  rfl

theorem SemiWith.unique {ψ : MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) F))} {σ τ : F ≃+* F}
    (h1 : SemiWith ψ σ) (h2 : SemiWith ψ τ) : σ = τ := by
  have hne : Multiplicative.toAdd (ψ (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) F))) ≠ 0 := by
    intro h0
    have h : ψ (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) F)) = 1 := by
      rw [← ofAdd_toAdd (ψ (Multiplicative.ofAdd (1 : Matrix (Fin 2) (Fin 2) F))), h0]
      rfl
    have h' := (ψ.injective (h.trans (map_one ψ).symm))
    exact one_ne_zero (Multiplicative.ofAdd.injective h')
  ext c
  have e1 := h1 c 1
  have e2 := h2 c 1
  rw [e2] at e1
  exact (smul_left_injective F hne e1).symm

theorem exists_fieldHom [Finite F] :
    ∃ s : ↥(NLM L Mp) →* (F ≃+* F), ∀ g, SemiWith (psi D g) (s g) := by
  choose s hs using exists_semi_psi D
  refine ⟨{ toFun := s, map_one' := ?_, map_mul' := ?_ }, hs⟩
  · have h1 : SemiWith (psi D 1) 1 := by
      rw [map_one]
      exact SemiWith.one
    exact (hs 1).unique h1
  · intro g g'
    have h1 := (hs g).mul (hs g')
    rw [← map_mul] at h1
    exact (hs (g * g')).unique h1

end Psi

end CFSG.Quasithin.RonanF918
