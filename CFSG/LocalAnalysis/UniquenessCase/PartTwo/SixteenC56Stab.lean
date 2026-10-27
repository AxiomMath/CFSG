module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.RankThree.PartOne.KF1514B.Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open CFSG.RankThree.PartOne.KF1514B
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem toMat_injective {K : Type} :
    Function.Injective (toMat : (OmI → K) → Matrix (Fin 2) (Fin 2) K) := by
  intro v v' h
  have h' := congrArg ofMat h
  rwa [ofMat_toMat, ofMat_toMat] at h'

private theorem toMat_zero {K : Type} [Zero K] :
    toMat (0 : OmI → K) = (0 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat]

private theorem orth_of_det_eq_zero {K : Type} [Field K] {L : Matrix (Fin 2) (Fin 2) K}
    (h : L.det = 0) : Orth L := by
  have h' : L 0 0 * L 1 1 - L 0 1 * L 1 0 = 0 := by
    rw [← Matrix.det_fin_two]
    exact h
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [det2]
  · show L 0 0 * L 0 1 - L 0 1 * L 0 0 = 0
    ring
  · show L 0 0 * L 1 1 - L 0 1 * L 1 0 = 0
    exact h'
  · show L 1 0 * L 0 1 - L 1 1 * L 0 0 = 0
    linear_combination -h'
  · show L 1 0 * L 1 1 - L 1 1 * L 1 0 = 0
    ring

private noncomputable def slConj {K : Type} [Field K] (X : Matrix (Fin 2) (Fin 2) K)
    (hX : IsUnit X.det) : SL(2, K) →* SL(2, K) where
  toFun b := ⟨X⁻¹ * (b : Matrix (Fin 2) (Fin 2) K) * X, by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one]
    exact Matrix.det_nonsing_inv_mul_det X hX⟩
  map_one' := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul X hX]
  map_mul' b b' := by
    apply Subtype.ext
    change X⁻¹ * ((b * b' : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * X =
      (X⁻¹ * (b : Matrix (Fin 2) (Fin 2) K) * X) *
        (X⁻¹ * (b' : Matrix (Fin 2) (Fin 2) K) * X)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left X ((b' : Matrix (Fin 2) (Fin 2) K) * X) hX]

private noncomputable def slStab {K : Type} [Field K] (X : Matrix (Fin 2) (Fin 2) K)
    (hX : IsUnit X.det) : SL(2, K) →* SL(2, K) where
  toFun b := Matrix.SpecialLinearGroup.transpose (slConj X hX (b⁻¹))
  map_one' := by
    apply Subtype.ext
    simp only [inv_one, map_one, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.transpose_one, Matrix.SpecialLinearGroup.coe_one]
  map_mul' b b' := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
      mul_inv_rev, map_mul, Matrix.transpose_mul]

theorem isPerfect_sl2 : Group.IsPerfect SL(2, S.K) :=
  CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card S.K S.four_le

theorem card_sl2 : Nat.card SL(2, S.K) = Nat.card S.K * (Nat.card S.K ^ 2 - 1) := by
  classical
  letI := Fintype.ofFinite S.K
  have h := Matrix.card_SL_field (n := 2) (𝔽 := S.K)
  have hq : Nat.card S.K = Fintype.card S.K := Nat.card_eq_fintype_card
  have h4 := S.four_le
  rw [h, hq]
  rw [hq] at h4
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Fintype.card S.K with hqdef
  have hq1 : 1 ≤ q := by omega
  have : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub, mul_one, pow_two]
  rw [this]
  exact Nat.div_eq_of_eq_mul_left (by omega) (by ring)

theorem exists_hom_ptCent_omega0 {w : W} (hw : S.Q w ≠ 0) :
    ∃ φ : SL(2, S.K) →* MulAut W, Function.Injective φ ∧ φ.range = ptCent S.omega0 w := by
  classical
  let X : Matrix (Fin 2) (Fin 2) S.K := toMat (S.vec w)
  have hXdet : X.det ≠ 0 := by
    rw [show X.det = S.Q w from (S.Q_eq_det w).symm]
    exact hw
  have hXunit : IsUnit X.det := isUnit_iff_ne_zero.mpr hXdet
  let ψ : SL(2, S.K) →* SL(2, S.K) × SL(2, S.K) := (MonoidHom.id _).prod (slStab X hXunit)
  let φ : SL(2, S.K) →* MulAut W := S.jHom.comp ψ
  have hφ : ∀ b : SL(2, S.K), φ b = S.jHom (b, slStab X hXunit b) := fun _ => rfl
  refine ⟨φ, ?_, ?_⟩
  · intro b b' h
    have h1 : ψ b = ψ b' := S.jHom_injective h
    simpa [ψ] using congrArg Prod.fst h1
  · apply le_antisymm
    · intro x hx
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact MonoidHom.mem_range.mpr ⟨(b, slStab X hXunit b), rfl⟩
      · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hφ b]
        apply S.vec_injective
        rw [S.vec_jHom]
        have hcb : ((slStab X hXunit b : SL(2, S.K)) :
              Matrix (Fin 2) (Fin 2) S.K)ᵀ =
            X⁻¹ * (((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K) * X) := by
          rw [show slStab X hXunit b =
            Matrix.SpecialLinearGroup.transpose (slConj X hXunit (b⁻¹)) from rfl,
            Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_transpose]
          exact Matrix.mul_assoc X⁻¹
            (((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K)) X
        have hbc : (b : Matrix (Fin 2) (Fin 2) S.K) * X *
            ((slStab X hXunit b : SL(2, S.K)) :
              Matrix (Fin 2) (Fin 2) S.K)ᵀ = X := by
          rw [hcb]
          calc (b : Matrix (Fin 2) (Fin 2) S.K) * X *
                (X⁻¹ * (((b⁻¹ : SL(2, S.K)) :
                  Matrix (Fin 2) (Fin 2) S.K) * X))
              = (b : Matrix (Fin 2) (Fin 2) S.K) *
                  ((X * X⁻¹) * (((b⁻¹ : SL(2, S.K)) :
                    Matrix (Fin 2) (Fin 2) S.K) * X)) := by
                simp only [Matrix.mul_assoc]
            _ = (b : Matrix (Fin 2) (Fin 2) S.K) *
                  (((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K) * X) := by
                rw [Matrix.mul_nonsing_inv X hXunit, Matrix.one_mul]
            _ = ((b : Matrix (Fin 2) (Fin 2) S.K) *
                  ((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K)) * X := by
                rw [Matrix.mul_assoc]
            _ = X := by
                rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
                  Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
        rw [hbc]
        exact ofMat_toMat (S.vec w)
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      have hx1' : x ∈ S.jHom.range := hx1
      obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hx1'
      obtain ⟨b, a⟩ := p
      have hx2' : S.jHom (b, a) w = w := by
        rw [← hp] at hx2
        rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hx2
      have hcoord : (b : Matrix (Fin 2) (Fin 2) S.K) * X *
          (a : Matrix (Fin 2) (Fin 2) S.K)ᵀ = X := by
        have h := congrArg (fun u : W => toMat (S.vec u)) hx2'
        rw [S.vec_jHom, toMat_ofMat] at h
        exact h
      have h2 : X * (a : Matrix (Fin 2) (Fin 2) S.K)ᵀ =
          ((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K) * X := by
        calc X * (a : Matrix (Fin 2) (Fin 2) S.K)ᵀ
            = (((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K) *
                (b : Matrix (Fin 2) (Fin 2) S.K)) *
                (X * (a : Matrix (Fin 2) (Fin 2) S.K)ᵀ) := by
              rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
                Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
          _ = ((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K) *
                ((b : Matrix (Fin 2) (Fin 2) S.K) * X *
                  (a : Matrix (Fin 2) (Fin 2) S.K)ᵀ) := by
              simp only [Matrix.mul_assoc]
          _ = ((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K) * X := by
              rw [hcoord]
      have h3 : (a : Matrix (Fin 2) (Fin 2) S.K)ᵀ =
          X⁻¹ * (((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K) * X) := by
        calc (a : Matrix (Fin 2) (Fin 2) S.K)ᵀ
            = X⁻¹ * (X * (a : Matrix (Fin 2) (Fin 2) S.K)ᵀ) := by
              rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul X hXunit, Matrix.one_mul]
          _ = X⁻¹ * (((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K) * X) := by
              rw [h2]
      have hcb : ((slStab X hXunit b : SL(2, S.K)) :
            Matrix (Fin 2) (Fin 2) S.K)ᵀ =
          X⁻¹ * (((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K) * X) := by
        rw [show slStab X hXunit b =
          Matrix.SpecialLinearGroup.transpose (slConj X hXunit (b⁻¹)) from rfl,
          Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_transpose]
        exact Matrix.mul_assoc X⁻¹
          (((b⁻¹ : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K)) X
      have ha : a = slStab X hXunit b := by
        refine Subtype.ext ?_
        have h4 := congrArg Matrix.transpose (h3.trans hcb.symm)
        simpa only [Matrix.transpose_transpose] using h4
      refine MonoidHom.mem_range.mpr ⟨b, ?_⟩
      rw [← hp]
      show S.jHom (b, slStab X hXunit b) = S.jHom (b, a)
      rw [ha]

theorem isPerfect_ptCent_omega0 {w : W} (hw : S.Q w ≠ 0) :
    Group.IsPerfect ↥(ptCent S.omega0 w) := by
  obtain ⟨φ, -, hφ⟩ := S.exists_hom_ptCent_omega0 hw
  haveI := S.isPerfect_sl2
  rw [← hφ]
  exact Group.IsPerfect.range (f := φ)

theorem card_ptCent_omega0 {w : W} (hw : S.Q w ≠ 0) :
    Nat.card ↥(ptCent S.omega0 w) = Nat.card S.K * (Nat.card S.K ^ 2 - 1) := by
  obtain ⟨φ, hinj, hφ⟩ := S.exists_hom_ptCent_omega0 hw
  rw [← hφ, ← S.card_sl2]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private lemma card_le_sq_of_exists {U : Subgroup W}
    {F : (Fin 2 → S.K) → Matrix (Fin 2) (Fin 2) S.K}
    (h : ∀ u ∈ U, ∃ y : Fin 2 → S.K, toMat (S.vec u) = F y) :
    Nat.card U ≤ Nat.card S.K ^ 2 := by
  classical
  let f : U → (Fin 2 → S.K) := fun u => Classical.choose (h u u.2)
  have hf : ∀ u : U, toMat (S.vec (u : W)) = F (f u) :=
    fun u => Classical.choose_spec (h u u.2)
  have hinj : Function.Injective f := by
    intro u u' hfu
    apply Subtype.ext
    apply S.vec_injective
    apply toMat_injective
    rw [hf u, hf u', hfu]
  calc Nat.card U ≤ Nat.card (Fin 2 → S.K) := Nat.card_le_card_of_injective f hinj
    _ = Nat.card S.K ^ 2 := card_fin_fun 2

theorem totallySingular_le_plane {U : Subgroup W} (hU : ∀ u ∈ U, S.Q u = 0) :
    ∃ z : Fin 2 → S.K,
      (∀ u ∈ U, ∃ y : Fin 2 → S.K, toMat (S.vec u) = Matrix.vecMulVec z y) ∨
      (∀ u ∈ U, ∃ x : Fin 2 → S.K, toMat (S.vec u) = Matrix.vecMulVec x z) := by
  classical
  let 𝓛 : AddSubgroup (Matrix (Fin 2) (Fin 2) S.K) :=
    { carrier := {M | ∃ u ∈ U, M = toMat (S.vec u)}
      zero_mem' := ⟨1, Subgroup.one_mem U, by rw [S.vec_one, toMat_zero]⟩
      add_mem' := by
        rintro M M' ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', Subgroup.mul_mem _ hu hu', by rw [S.vec_mul, toMat_add]⟩
      neg_mem' := by
        rintro M ⟨u, hu, rfl⟩
        refine ⟨u, hu, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [toMat, CharTwo.neg_eq] }
  have hOrth : ∀ L ∈ 𝓛, Orth L := by
    rintro L ⟨u, hu, rfl⟩
    exact orth_of_det_eq_zero (by rw [← S.Q_eq_det]; exact hU u hu)
  rcases rankOne_family (m := 2) 𝓛 hOrth with ⟨w, -, h⟩ | ⟨a₀, h⟩
  · refine ⟨w, Or.inr ?_⟩
    intro u hu
    obtain ⟨a, ha⟩ := h (toMat (S.vec u)) ⟨u, hu, rfl⟩
    exact ⟨a, funext fun i => funext fun j => by
      simpa [Matrix.vecMulVec_apply] using congrFun (ha i) j⟩
  · refine ⟨a₀, Or.inl ?_⟩
    intro u hu
    obtain ⟨w, hw⟩ := h (toMat (S.vec u)) ⟨u, hu, rfl⟩
    exact ⟨w, funext fun i => funext fun j => by
      simpa [Matrix.vecMulVec_apply] using congrFun (hw i) j⟩

theorem card_le_of_totallySingular {U : Subgroup W} (hU : ∀ u ∈ U, S.Q u = 0) :
    Nat.card U ≤ Nat.card S.K ^ 2 := by
  obtain ⟨z, h | h⟩ := S.totallySingular_le_plane hU
  · exact S.card_le_sq_of_exists (F := fun y => Matrix.vecMulVec z y) h
  · exact S.card_le_sq_of_exists (F := fun x => Matrix.vecMulVec x z) h

theorem exists_perfect_normalizing_of_totallySingular {U : Subgroup W}
    (hU : ∀ u ∈ U, S.Q u = 0) (hcard : Nat.card S.K ^ 2 ≤ Nat.card U) :
    ∃ P₀ : Subgroup (MulAut W), P₀ ≤ S.omega0 ∧ Group.IsPerfect ↥P₀ ∧
      Nat.card ↥P₀ = Nat.card S.K * (Nat.card S.K ^ 2 - 1) ∧ ∀ h ∈ P₀, ∀ u ∈ U, h u ∈ U := by
  classical
  haveI : Finite W := Finite.of_injective S.vec S.vec_injective
  obtain ⟨z, h | h⟩ := S.totallySingular_le_plane hU
  · let Plane : Subgroup W :=
      { carrier := {w : W | ∃ y : Fin 2 → S.K, toMat (S.vec w) = Matrix.vecMulVec z y}
        one_mem' := ⟨0, by rw [S.vec_one, toMat_zero, Matrix.vecMulVec_zero]⟩
        mul_mem' := by
          rintro a b ⟨y, hy⟩ ⟨y', hy'⟩
          exact ⟨y + y', by rw [S.vec_mul, toMat_add, hy, hy', Matrix.vecMulVec_add]⟩
        inv_mem' := by
          rintro a ⟨y, hy⟩
          refine ⟨y, ?_⟩
          rw [S.vec_inv]
          have hneg : (- S.vec a : OmI → S.K) = S.vec a :=
            funext fun i => CharTwo.neg_eq (S.vec a i)
          rw [hneg, hy] }
    have hle : U ≤ Plane := fun u hu => h u hu
    have hcardPlane : Nat.card Plane ≤ Nat.card S.K ^ 2 :=
      S.card_le_sq_of_exists (F := fun y => Matrix.vecMulVec z y) fun w hw => hw
    have hUne : U = Plane := Subgroup.eq_of_le_of_card_ge hle (le_trans hcardPlane hcard)
    let P₀ : Subgroup (MulAut W) :=
      (S.jHom.comp (MonoidHom.inr SL(2, S.K) SL(2, S.K))).range
    refine ⟨P₀, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
      exact MonoidHom.mem_range.mpr ⟨MonoidHom.inr SL(2, S.K) SL(2, S.K) a, rfl⟩
    · haveI : Group.IsPerfect SL(2, S.K) := S.isPerfect_sl2
      exact Group.IsPerfect.range
        (f := S.jHom.comp (MonoidHom.inr SL(2, S.K) SL(2, S.K)))
    · have hinj : Function.Injective
          (S.jHom.comp (MonoidHom.inr SL(2, S.K) SL(2, S.K))) :=
        S.jHom_injective.comp (fun a b hab => by
          have := congrArg Prod.snd hab
          simpa using this)
      rw [← S.card_sl2]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    · intro g hg u hu
      rw [hUne]
      have huPlane : u ∈ Plane := hle hu
      obtain ⟨y, hy⟩ := huPlane
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      refine ⟨a *ᵥ y, ?_⟩
      show toMat (S.vec (S.jHom (MonoidHom.inr SL(2, S.K) SL(2, S.K) a) u)) =
        Matrix.vecMulVec z (a *ᵥ y)
      rw [show MonoidHom.inr SL(2, S.K) SL(2, S.K) a = (1, a) from rfl, S.vec_jHom,
        toMat_ofMat]
      change (1 : Matrix (Fin 2) (Fin 2) S.K) * toMat (S.vec u) *
          (a : Matrix (Fin 2) (Fin 2) S.K)ᵀ = Matrix.vecMulVec z (a *ᵥ y)
      rw [Matrix.one_mul, hy, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  · let Plane : Subgroup W :=
      { carrier := {w : W | ∃ x : Fin 2 → S.K, toMat (S.vec w) = Matrix.vecMulVec x z}
        one_mem' := ⟨0, by rw [S.vec_one, toMat_zero, Matrix.zero_vecMulVec]⟩
        mul_mem' := by
          rintro a b ⟨y, hy⟩ ⟨y', hy'⟩
          exact ⟨y + y', by rw [S.vec_mul, toMat_add, hy, hy', Matrix.add_vecMulVec]⟩
        inv_mem' := by
          rintro a ⟨y, hy⟩
          refine ⟨y, ?_⟩
          rw [S.vec_inv]
          have hneg : (- S.vec a : OmI → S.K) = S.vec a :=
            funext fun i => CharTwo.neg_eq (S.vec a i)
          rw [hneg, hy] }
    have hle : U ≤ Plane := fun u hu => h u hu
    have hcardPlane : Nat.card Plane ≤ Nat.card S.K ^ 2 :=
      S.card_le_sq_of_exists (F := fun x => Matrix.vecMulVec x z) fun w hw => hw
    have hUne : U = Plane := Subgroup.eq_of_le_of_card_ge hle (le_trans hcardPlane hcard)
    let P₀ : Subgroup (MulAut W) :=
      (S.jHom.comp (MonoidHom.inl SL(2, S.K) SL(2, S.K))).range
    refine ⟨P₀, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
      exact MonoidHom.mem_range.mpr ⟨MonoidHom.inl SL(2, S.K) SL(2, S.K) a, rfl⟩
    · haveI : Group.IsPerfect SL(2, S.K) := S.isPerfect_sl2
      exact Group.IsPerfect.range
        (f := S.jHom.comp (MonoidHom.inl SL(2, S.K) SL(2, S.K)))
    · have hinj : Function.Injective
          (S.jHom.comp (MonoidHom.inl SL(2, S.K) SL(2, S.K))) :=
        S.jHom_injective.comp (fun a b hab => by
          have := congrArg Prod.fst hab
          simpa using this)
      rw [← S.card_sl2]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    · intro g hg u hu
      rw [hUne]
      have huPlane : u ∈ Plane := hle hu
      obtain ⟨x, hx⟩ := huPlane
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hg
      refine ⟨b *ᵥ x, ?_⟩
      show toMat (S.vec (S.jHom (MonoidHom.inl SL(2, S.K) SL(2, S.K) b) u)) =
        Matrix.vecMulVec (b *ᵥ x) z
      rw [show MonoidHom.inl SL(2, S.K) SL(2, S.K) b = (b, 1) from rfl, S.vec_jHom,
        toMat_ofMat]
      change (b : Matrix (Fin 2) (Fin 2) S.K) * toMat (S.vec u) *
          ((1 : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K)ᵀ =
        Matrix.vecMulVec (b *ᵥ x) z
      rw [show ((1 : SL(2, S.K)) : Matrix (Fin 2) (Fin 2) S.K) = 1 from rfl,
        Matrix.transpose_one, Matrix.mul_one, hx, Matrix.mul_vecMulVec]

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
