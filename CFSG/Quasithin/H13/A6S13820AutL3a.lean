module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelAut
public import CFSG.Quasithin.H13.A6S13816f

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.ComponentClassification

namespace Aut20

variable {F : Type} [Field F]

@[expose] def diagGL20 (v : Fin 3 → Fˣ) : GL (Fin 3) F :=
  ⟨diagonal fun i => (v i : F), diagonal fun i => (((v i)⁻¹ : Fˣ) : F), by
    rw [diagonal_mul_diagonal]
    simp, by
    rw [diagonal_mul_diagonal]
    simp⟩

theorem coe_diagGL20 (v : Fin 3 → Fˣ) :
    ((diagGL20 v : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal fun i => (v i : F) := rfl

theorem coe_diagGL20_inv (v : Fin 3 → Fˣ) :
    (((diagGL20 v)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal fun i => (((v i)⁻¹ : Fˣ) : F) := rfl

@[expose] def diagSL20 (w : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1) :
    SpecialLinearGroup (Fin 3) F :=
  ⟨diagonal w, by rw [det_diagonal, Fin.prod_univ_three, hw]⟩

theorem coe_diagSL20 (w : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1) :
    ((diagSL20 w hw : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal w := rfl

theorem diagSL20_mem_upperTriangular (w : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1) :
    diagSL20 w hw ∈ upperTriangular 3 F := fun i j hij => by
  rw [coe_diagSL20, diagonal_apply_ne _ (ne_of_gt hij)]

theorem diag_conj_apply20 (v : Fin 3 → Fˣ) (M : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    ((diagonal fun i => (v i : F)) * M * diagonal fun i => (((v i)⁻¹ : Fˣ) : F)) i j =
      (v i : F) * M i j * (((v j)⁻¹ : Fˣ) : F) := by
  rw [mul_diagonal, diagonal_mul]

theorem slConj_diagGL20_mem (v : Fin 3 → Fˣ) {u : SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ unitriangular 3 F) :
    CatalogueBHigherLinearAction.slConjugation 3 F (diagGL20 v) u ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_slConjugation, coe_diagGL20, coe_diagGL20_inv, diag_conj_apply20, hu.1 i j hij,
      mul_zero, zero_mul]
  · rw [coe_slConjugation, coe_diagGL20, coe_diagGL20_inv, diag_conj_apply20, hu.2 i, mul_one]
    simp

theorem conjAut_diagGL20_mem (v : Fin 3 → Fˣ) {x : projectiveSL 3 F}
    (hx : x ∈ projUnitriangular 3 F) :
    LinearFlag.conjAut 3 F (diagGL20 v) x ∈ projUnitriangular 3 F := by
  obtain ⟨u, hu, rfl⟩ := hx
  rw [conjAut_proj]
  exact ⟨_, slConj_diagGL20_mem v hu, rfl⟩

theorem conjAut_diagGL20_diagSL20 (v : Fin 3 → Fˣ) (w : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1) :
    LinearFlag.conjAut 3 F (diagGL20 v) (proj 3 F (diagSL20 w hw)) = proj 3 F (diagSL20 w hw) := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_diagGL20, coe_diagGL20_inv, coe_diagSL20, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_comm, ← mul_assoc]
  simp

theorem diagGL20_inv (v : Fin 3 → Fˣ) : (diagGL20 v)⁻¹ = diagGL20 (F := F) v⁻¹ := by
  apply Units.ext
  rw [coe_diagGL20_inv, coe_diagGL20]
  rfl

theorem comm_mem_unitriangular20 {b x : SpecialLinearGroup (Fin 3) F}
    (hb : b ∈ upperTriangular 3 F) (hx : x ∈ upperTriangular 3 F) :
    b * x * b⁻¹ * x⁻¹ ∈ unitriangular 3 F := by
  have hb' := mem_upperTriangular_iff_isUpperTriangular.mp hb
  have hx' := mem_upperTriangular_iff_isUpperTriangular.mp hx
  have hbi := coe_inv_isUpperTriangular hb'
  have hxi := coe_inv_isUpperTriangular hx'
  have hm : b * x * b⁻¹ * x⁻¹ ∈ upperTriangular 3 F :=
    (upperTriangular 3 F).mul_mem ((upperTriangular 3 F).mul_mem
      ((upperTriangular 3 F).mul_mem hb hx) ((upperTriangular 3 F).inv_mem hb))
      ((upperTriangular 3 F).inv_mem hx)
  refine ⟨hm, fun i => ?_⟩
  have h1 : ((b * x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.mp ((upperTriangular 3 F).mul_mem hb hx)
  have h2 : ((b * x * b⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.mp
      ((upperTriangular 3 F).mul_mem ((upperTriangular 3 F).mul_mem hb hx)
        ((upperTriangular 3 F).inv_mem hb))
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular h2 hxi,
    Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular h1 hbi,
    Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular hb' hx']
  have e1 := coe_inv_apply_self_of_isUpperTriangular hb' i
  have e2 := coe_inv_apply_self_of_isUpperTriangular hx' i
  calc (b : Matrix (Fin 3) (Fin 3) F) i i * (x : Matrix (Fin 3) (Fin 3) F) i i *
        ((b⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i *
        ((x⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i =
      ((b : Matrix (Fin 3) (Fin 3) F) i i *
          ((b⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i) *
        ((x : Matrix (Fin 3) (Fin 3) F) i i *
          ((x⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i) := by ring
    _ = 1 := by rw [e1, e2, one_mul]

theorem eq_of_proj_diag_mem20 (w : Fin 3 → F) (hw : w 0 * w 1 * w 2 = 1)
    (h : proj 3 F (diagSL20 w hw) ∈ projUnitriangular 3 F) : w 0 = w 1 ∧ w 1 = w 2 := by
  obtain ⟨u, hu, he⟩ := h
  obtain ⟨c, -, hc⟩ := proj_eq_proj_iff.mp he
  have hm : (diagonal w : Matrix (Fin 3) (Fin 3) F) =
      (u : Matrix (Fin 3) (Fin 3) F) * scalar (Fin 3) (c : F) := by
    rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rfl
  have hd : ∀ i : Fin 3, w i = (c : F) := by
    intro i
    have e := congrFun (congrFun hm i) i
    rw [diagonal_apply_eq, scalar_apply, mul_diagonal, hu.2 i, one_mul] at e
    exact e
  exact ⟨(hd 0).trans (hd 1).symm, (hd 1).trans (hd 2).symm⟩

theorem mem_normalizer_of_conj_le20 {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hcard : Nat.card H ≤ Nat.card (H.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hye⟩ := hx
  have : y = x := by
    have hye' : g * y * g⁻¹ = g * x * g⁻¹ := hye
    simpa using hye'
  exact this ▸ hy

theorem pow_three_mem20 {G : Type*} [Group G] {N C : Subgroup G}
    (hn : (C.subgroupOf N).Normal) (hidx : C.relIndex N ∣ 3) {s : G} (hs : s ∈ N) :
    s ^ 3 ∈ C := by
  have hcard : Nat.card (↥N ⧸ C.subgroupOf N) ∣ 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hfin : Finite (↥N ⧸ C.subgroupOf N) := by
    refine Nat.finite_of_card_ne_zero ?_
    intro h0
    rw [h0] at hcard
    norm_num at hcard
  have h1 : ((⟨s, hs⟩ : ↥N) : ↥N ⧸ C.subgroupOf N) ^ 3 = 1 := by
    obtain ⟨m, hm⟩ := hcard
    rw [hm, pow_mul, pow_card_eq_one', one_pow]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem exists_conjAut_eq20 [Finite F] [CharP F 2] (A : GL (Fin 3) F)
    (hA : ∀ x ∈ projUnitriangular 3 F, LinearFlag.conjAut 3 F A x ∈ projUnitriangular 3 F) :
    ∃ T ∈ upperTriangular 3 F, ∃ v : Fin 3 → Fˣ,
      LinearFlag.conjAut 3 F A =
        MulAut.conj (proj 3 F T) * LinearFlag.conjAut 3 F (diagGL20 v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set d : Fˣ := Matrix.GeneralLinearGroup.det A with hd
  set v : Fin 3 → Fˣ := ![d, 1, 1] with hv
  set A₁ : GL (Fin 3) F := A * (diagGL20 v)⁻¹ with hA₁
  have hdet : Matrix.GeneralLinearGroup.det A₁ = 1 := by
    rw [hA₁, map_mul, map_inv, ← hd]
    have : Matrix.GeneralLinearGroup.det (diagGL20 (F := F) v) = d := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagGL20, det_diagonal, Fin.prod_univ_three]
      simp [hv]
    rw [this, mul_inv_cancel]
  set T : SpecialLinearGroup (Fin 3) F := ⟨(A₁ : Matrix (Fin 3) (Fin 3) F), by
    have := congrArg Units.val hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this⟩ with hT
  have hTGL : SpecialLinearGroup.toGL T = A₁ := Units.ext rfl
  have hconjT : LinearFlag.conjAut 3 F A₁ = MulAut.conj (proj 3 F T) := by
    rw [← hTGL, conjAut_toGL]
  have hAeq : LinearFlag.conjAut 3 F A =
      MulAut.conj (proj 3 F T) * LinearFlag.conjAut 3 F (diagGL20 v) := by
    rw [← hconjT, ← map_mul, hA₁, inv_mul_cancel_right]
  refine ⟨T, ?_, v, hAeq⟩
  have hTU : ∀ x ∈ projUnitriangular 3 F,
      proj 3 F T * x * (proj 3 F T)⁻¹ ∈ projUnitriangular 3 F := by
    intro x hx
    have e : proj 3 F T * x * (proj 3 F T)⁻¹ =
        LinearFlag.conjAut 3 F A (LinearFlag.conjAut 3 F (diagGL20 v⁻¹) x) := by
      rw [← MulAut.conj_apply, ← hconjT, hA₁, map_mul, diagGL20_inv]
      rfl
    rw [e]
    exact hA _ (conjAut_diagGL20_mem _ hx)
  have hN := mem_normalizer_of_conj_le20 hTU
  rw [normalizer_projUnitriangular (K := F) (n := 3) 2] at hN
  obtain ⟨B, hB, hBT⟩ := hN
  have hz := proj_eq_proj_iff.mp hBT
  have e : T = B * (B⁻¹ * T) := by group
  rw [e]
  exact (upperTriangular 3 F).mul_mem hB (scalars_le_upperTriangular 3 F hz)

theorem sigma_eq_one_of_fix_cubes20 [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (σ : F ≃+* F) (h : ∀ a : Fˣ, σ ((a : F) ^ 3) = (a : F) ^ 3) : σ = 1 ∨ n = 2 := by
  by_cases hσ : σ = 1
  · exact Or.inl hσ
  right
  by_contra hn2
  have hn3 : 3 ≤ n := by omega
  have hfix := CFSG.LocalAnalysis.EvenBN.LinearThree.card_fix_mul_card_fix_le (by omega) hF hσ
  set φ : Fˣ →* Fˣ := powMonoidHom 3 with hφ
  have hker : Nat.card φ.ker ≤ 3 := by
    rw [hφ, ← rootsOfUnity_eq_ker]
    exact card_rootsOfUnity F 3
  have hunits : Nat.card Fˣ = 2 ^ n - 1 := by rw [Nat.card_units, hF]
  have hcard : Nat.card Fˣ = Nat.card φ.ker * Nat.card φ.range :=
    L2Case.card_eq_ker_mul_range φ
  have hy : ∀ y : φ.range, σ ((y : Fˣ) : F) = ((y : Fˣ) : F) := by
    rintro ⟨_, a, rfl⟩
    show σ ((φ a : Fˣ) : F) = ((φ a : Fˣ) : F)
    rw [hφ, powMonoidHom_apply, Units.val_pow_eq_pow_val]
    exact h a
  let f : Option φ.range → {t : F // σ t = t} := fun o => match o with
    | none => ⟨0, map_zero σ⟩
    | some y => ⟨((y : Fˣ) : F), hy y⟩
  have hf : Function.Injective f := by
    rintro (_ | y) (_ | z) hyz
    · rfl
    · have e : (0 : F) = ((z : Fˣ) : F) := congrArg Subtype.val hyz
      exact absurd e.symm (Units.ne_zero _)
    · have e : ((y : Fˣ) : F) = 0 := congrArg Subtype.val hyz
      exact absurd e (Units.ne_zero _)
    · have e : ((y : Fˣ) : F) = ((z : Fˣ) : F) := congrArg Subtype.val hyz
      exact congrArg some (Subtype.ext (Units.val_inj.mp e))
  have hle := Nat.card_le_card_of_injective f hf
  rw [Finite.card_option] at hle
  set r := Nat.card φ.range
  have h3r : 2 ^ n - 1 ≤ 3 * r := by
    rw [← hunits, hcard]
    exact Nat.mul_le_mul_right _ hker
  have hsq : (r + 1) * (r + 1) ≤ 2 ^ n := by
    rw [← hF]
    exact (Nat.mul_le_mul hle hle).trans hfix
  have hq : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  set q := 2 ^ n
  have hqr : q ≤ 3 * r + 1 := by omega
  have hr3 : 3 ≤ r := by omega
  nlinarith

theorem exists_conj_of_conjAut_pow20 [Finite F] (A : GL (Fin 3) F) {k : ℕ}
    (h : LinearFlag.conjAut 3 F A ^ 2 ^ k = 1) :
    ∃ g : projectiveSL 3 F, LinearFlag.conjAut 3 F A = MulAut.conj g := by
  rw [← map_pow, ProjectivePlane.conjAut_eq_one_iff (le_refl 3)] at h
  obtain ⟨u, hu⟩ := h
  set d : Fˣ := Matrix.GeneralLinearGroup.det A with hd
  have hdu : d ^ 2 ^ k = u ^ 3 := by
    have := congrArg Matrix.GeneralLinearGroup.det hu
    rwa [map_pow, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at this
  have h41 : 1 ≡ 4 ^ k [MOD 3] := by simpa using (show 1 ≡ 4 [MOD 3] by decide).pow k
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h41
  have h4 : 4 ^ k = 3 * j + 1 := by
    have : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
    omega
  set μ : Fˣ := u ^ 2 ^ k * (d ^ j)⁻¹ with hμ
  have hdμ : d = μ ^ 3 := by
    have h42 : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
    have e1 : d ^ 4 ^ k = (u ^ 2 ^ k) ^ 3 := by
      rw [h42, pow_mul, hdu, ← pow_mul, ← pow_mul, mul_comm]
    rw [hμ, mul_pow, inv_pow, ← e1, h4, pow_succ, ← pow_mul, mul_comm j 3, mul_comm (d ^ _) d,
      mul_assoc, mul_inv_cancel, mul_one]
  set T : SpecialLinearGroup (Fin 3) F := ⟨((μ⁻¹ : Fˣ) : F) • (A : Matrix (Fin 3) (Fin 3) F), by
    rw [det_smul, Fintype.card_fin]
    have := congrArg Units.val hdμ
    rw [hd, Matrix.GeneralLinearGroup.val_det_apply] at this
    rw [this, Units.val_pow_eq_pow_val, ← mul_pow, Units.inv_mul, one_pow]⟩ with hT
  refine ⟨proj 3 F T, CFSG.LocalAnalysis.EvenBN.LinearThree.conjAut_eq_conj_of_eq_smul A T
    (Units.ne_zero μ) ?_⟩
  rw [hT]
  show (A : Matrix (Fin 3) (Fin 3) F) = (μ : F) • ((((μ⁻¹ : Fˣ) : F)) •
    (A : Matrix (Fin 3) (Fin 3) F))
  rw [smul_smul, Units.mul_inv, one_smul]

end Aut20

end CFSG.Quasithin.H13.A6
