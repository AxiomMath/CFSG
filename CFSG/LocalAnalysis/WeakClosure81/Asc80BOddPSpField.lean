module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LieType.SeitzGeneration.LinearOuterLocal
import CFSG.LieType.SeitzGeneration.SymplecticOpposition
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpGspNil
import CFSG.LieType.SeitzGeneration.OuterLinearWide

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Subgroup Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical.SteinbergBY CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBSymplecticRepresentation

private lemma spScalars_le_center {r : ℕ} {K : Type} [Field K] :
    spScalars r K ≤ Subgroup.center (StatedSp r K) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hzmat : ((z : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := hc.symm
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hzmat,
    GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact mul_comm _ _

theorem planeGen_of_fixed_unipotent_sp {F : Type} [Field F] [Finite F] {r : ℕ}
    (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (StatedProj (StatedSp r F)))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) (X : StatedSp r F) (hX1 : X ≠ 1)
    (hX3 : (((X : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) - 1) ^ 3 = 0)
    (hfix : ∀ e ∈ E, e (proj r F X) = proj r F X) : PlaneGen E := by
  classical
  let ℓ := ringChar F
  have hℓ : ℓ.Prime := CharP.char_is_prime F ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := hF
  have hℓ3 : 3 ≤ ℓ := by
    have h2 := hℓ.two_le
    omega
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with rfl | h
    · exfalso
      apply hX1
      apply Subtype.ext
      apply Units.ext
      apply Matrix.ext
      intro i j
      rcases i with i | i <;> exact i.elim0
    · exact h
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, hr1⟩⟩
  have : Nontrivial (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
    refine ⟨0, 1, ?_⟩
    intro h
    have h00 := congrFun (congrFun h (Sum.inl ⟨0, hr1⟩)) (Sum.inl ⟨0, hr1⟩)
    exact zero_ne_one h00
  have : CharP F ℓ := ringChar.charP F
  have : CharP (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) ℓ :=
    charP_of_injective_algebraMap
      (algebraMap F (Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)).injective ℓ
  let N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
    ((X : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) - 1
  have hN3 : N ^ 3 = 0 := by simpa [N] using hX3
  have hXeq : ((X : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 + N := by
    simp [N]
  have hNℓ : N ^ ℓ = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, ℓ = 3 + k := ⟨ℓ - 3, by omega⟩
    rw [hk, pow_add, hN3, Matrix.zero_mul]
  have hXmat : ((X : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) ^ ℓ = 1 := by
    rw [hXeq, add_pow_char_of_commute ℓ (Commute.one_left N), hNℓ, add_zero, one_pow]
  have hXg : X ^ ℓ = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    simpa using hXmat
  have hπXpow : (proj r F X) ^ ℓ = 1 := by rw [← map_pow, hXg, map_one]
  have hπX1 : proj r F X ≠ 1 := by
    intro h
    have hker : X ∈ (proj r F).ker := MonoidHom.mem_ker.mpr h
    rw [ker_proj] at hker
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hker
    obtain ⟨c, hc⟩ := hker
    have hXc : ((X : StatedSp r F) : GL (Fin r ⊕ Fin r) F) =
        GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := hc.symm
    have hNscalar : N = Matrix.scalar (Fin r ⊕ Fin r) ((c : F) - 1) := by
      simp only [N, hXc, GeneralLinearGroup.coe_scalar, ← map_one (Matrix.scalar (Fin r ⊕ Fin r)),
        ← map_sub]
    have h3 : (Matrix.scalar (Fin r ⊕ Fin r) ((c : F) - 1)) ^ 3 = 0 := by
      rw [← hNscalar]
      exact hN3
    have h3' : Matrix.scalar (Fin r ⊕ Fin r) (((c : F) - 1) ^ 3) = 0 := by
      rw [map_pow]
      exact h3
    have hentry := congrFun (congrFun h3' (Sum.inl ⟨0, hr1⟩)) (Sum.inl ⟨0, hr1⟩)
    have hcube : ((c : F) - 1) ^ 3 = 0 := by
      simpa [Matrix.scalar_apply] using hentry
    have hc1 : (c : F) = 1 :=
      sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hcube)
    exact hX1 (Subtype.ext (Units.ext (by
      rw [hXc, GeneralLinearGroup.coe_scalar, hc1, map_one]
      simp)))
  have hord : orderOf (proj r F X) = ℓ := orderOf_eq_prime hπXpow hπX1
  let R : Subgroup (StatedProj (StatedSp r F)) := Subgroup.zpowers (proj r F X)
  have hRr : IsPGroup ℓ R := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  have hRne : R ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hπX1
  have hER : ∀ e ∈ E, R.map e.toMonoidHom = R := by
    intro e he
    rw [show R = Subgroup.zpowers (proj r F X) from rfl, MonoidHom.map_zpowers]
    show Subgroup.zpowers (e (proj r F X)) = Subgroup.zpowers (proj r F X)
    rw [hfix e he]
  have hgood : ∀ Q : Subgroup (StatedProj (StatedSp r F)), Q ≠ ⊥ →
      CFSG.GroupTheory.IsRadicalPGroup ℓ ⊤ Q →
      CFSG.GroupTheory.HasGoodOppositePRadicals ℓ ⊤ Q := by
    intro Q hQne hQ
    have htop : (proj r F).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (proj_surjective (r := r) (K := F))
    have hker : (proj r F).ker ≤ Subgroup.center (StatedSp r F) := by
      rw [ker_proj]
      exact spScalars_le_center
    rw [← htop] at hQ ⊢
    exact CFSG.LieType.SeitzGeneration.hasGoodOppositePRadicals_of_statedSp (proj r F) hker hQne hQ
  exact CFSG.LieType.SeitzGeneration.planeGen_of_normalized_rSubgroup_of_hasGoodOppositePRadicals
    hℓ2 hgood E hE h4 R hRne hRr hER

private theorem exists_rational_smul_sum {K : Type} [Field K] [Finite K] {ι : Type*}
    {ℓ e p : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ e)
    (σ : K ≃+* K) (hσ : orderOf σ = p) {X : Matrix ι ι K} (hX0 : X ≠ 0) {lam : K}
    (hX : X.map σ = lam • X) : ∃ c : K, c ≠ 0 ∧ (c • X).map σ = c • X := by
  have hit : ∀ j : ℕ, X.map ⇑(σ ^ j) = (∏ i ∈ Finset.range j, (σ ^ i) lam) • X := by
    intro j
    induction j with
    | zero =>
      ext a b
      simp
    | succ j ih =>
      have h1 : X.map ⇑(σ ^ (j + 1)) = (X.map ⇑(σ ^ j)).map σ := by
        ext a b
        simp only [Matrix.map_apply]
        rw [pow_succ']
        rfl
      rw [h1, ih, Finset.prod_range_succ']
      ext a b
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      have hab := congrFun (congrFun hX a) b
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hab
      rw [map_mul, map_prod, hab]
      have e1 : ∀ i, σ ((σ ^ i) lam) = (σ ^ (i + 1)) lam := fun i => by rw [pow_succ']; rfl
      simp only [e1, pow_zero]
      change _ = (∏ i ∈ Finset.range j, (σ ^ (i + 1)) lam) * lam * X a b
      ring
  have hN : ∏ i ∈ Finset.range p, (σ ^ i) lam = 1 := by
    have h1 := hit p
    have hpow : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    have h2 : X.map ⇑(σ ^ p) = X := by
      rw [hpow]
      ext a b
      simp
    rw [h2] at h1
    obtain ⟨a, b, hab⟩ : ∃ a b, X a b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hX0 (Matrix.ext hcon)
    have h3 := congrFun (congrFun h1 a) b
    simp only [Matrix.smul_apply, smul_eq_mul] at h3
    exact (mul_left_eq_self₀.mp h3.symm).resolve_right hab
  obtain ⟨c, hc0, hc⟩ := exists_hilbert90 hp hℓ he hK σ hσ lam hN
  refine ⟨c, hc0, ?_⟩
  ext a b
  have hab := congrFun (congrFun hX a) b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hab ⊢
  rw [map_mul, hab]
  calc σ c * (lam * X a b) = (lam * σ c) * X a b := by ring
    _ = c * X a b := by rw [hc]

theorem planeGen_of_not_spLinear {F : Type} [Field F] [Finite F] {r : ℕ} (hr : 2 ≤ r)
    (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (StatedProj (StatedSp r F)))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hσ : ∃ e ∈ E, e ∉ spLinearAutGroup r F) : PlaneGen E := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : NeZero r := ⟨by omega⟩
  have hr1 : 1 ≤ r := by omega
  obtain ⟨ℓ, hcharF⟩ := CharP.exists F
  have hℓ : ℓ.Prime := CharP.char_is_prime F ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP F ℓ := hcharF
  obtain ⟨f, -, hcard⟩ := FiniteField.card F ℓ
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have hcardNat : Nat.card F = ℓ ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hℓ2 : ℓ ≠ 2 := by
    rw [← ringChar.eq F ℓ]
    exact hF
  obtain ⟨e, heE, heNotLin⟩ := hσ
  have he2 : e ^ 2 = 1 := hE.2 e heE
  have he1 : e ≠ 1 := by
    intro h1
    apply heNotLin
    rw [h1]
    exact Subgroup.one_mem _
  have hord : orderOf e = 2 := orderOf_eq_prime he2 he1
  obtain ⟨Ae, σe, heform⟩ :=
    automorphism_standard hF hr e
  have heSemi : e ∈ spSemilinearAutGroup r F := by
    rw [heform]
    exact Subgroup.mul_mem _
      (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup Ae))
      (fieldAut_mem_spSemilinearAutGroup σe)
  obtain ⟨-, hinjField, -, -, -, -, -, -, -, hdesc⟩ :=
    symplectic_prime_semilinear_field_descent hℓ hf1 hr
      hcardNat
  obtain ⟨-, σ, hσord, -, ⟨h, -, heq⟩⟩ :=
    hdesc 2 Nat.prime_two e heSemi heNotLin hord
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσord
    omega
  have hσ2 : σ ^ 2 = 1 := by
    have h' := pow_orderOf_eq_one σ
    rwa [hσord] at h'
  let E' : Subgroup (MulAut (StatedProj (StatedSp r F))) := E.map (MulAut.congr h⁻¹).toMonoidHom
  have hcardE' : Nat.card E' = 4 := by
    rw [show E' = E.map (MulAut.congr h⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.congr h⁻¹).injective, h4]
  have hE' : IsElemAbelian 2 E' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 2 hE _
  have hfσmem : fieldAut r F σ ∈ E' := by
    refine Subgroup.mem_map.mpr ⟨h * fieldAut r F σ * h⁻¹, ?_, ?_⟩
    · rwa [← heq]
    · ext x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
  have hfσne : fieldAut r F σ ≠ 1 := by
    intro h1
    apply hσ1
    exact hinjField (by rw [h1, map_one])
  obtain ⟨y, hyE', hyzp⟩ :=
    exists_notMem_zpowers_of_card_sq Nat.prime_two hE'.2 (by rw [hcardE']; norm_num)
      hfσmem hfσne
  have hgen : E' = Subgroup.zpowers (fieldAut r F σ) ⊔ Subgroup.zpowers y :=
    (zpowers_sup_zpowers_eq_of_card_sq Nat.prime_two hE'.2 (by rw [hcardE']; norm_num)
      hfσmem hfσne hyE' hyzp).symm
  have hy2 : y ^ 2 = 1 := hE'.2 y hyE'
  obtain ⟨Ay, τ, hyform⟩ :=
    automorphism_standard hF hr y
  let Aym : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
    ((Ay : gsp r F) : GL (Fin r ⊕ Fin r) F)
  have hτsq : τ * τ = 1 := by
    have h2 : (conjAut r F Ay * fieldAut r F τ) * (conjAut r F Ay * fieldAut r F τ) = 1 := by
      rw [← hyform]
      exact hy2
    rw [conjAut_mul_fieldAut_mul_self]
      at h2
    exact ((conjAut_mul_fieldAut_eq_one_iff
      (K := F) hr1 (Ay * gspFieldMap τ Ay) (τ * τ)).mp h2).1
  have hσinv2 : (conjAut r F (1 : gsp r F) * fieldAut r F σ) *
      (conjAut r F (1 : gsp r F) * fieldAut r F σ) = 1 := by
    rw [map_one, one_mul, ← pow_two, ← map_pow, hσ2, map_one]
  have hσinv1 : conjAut r F (1 : gsp r F) * fieldAut r F σ ≠ 1 := by
    rw [map_one, one_mul]
    exact hfσne
  have huniq : ∀ τ : F ≃+* F, τ ^ 2 = 1 → τ ≠ 1 → τ = σ :=
    ((involution_facts (K := F) hr1
      (1 : gsp r F) σ hσinv2 hσinv1).2.2.2 hσ1).2
  have hτ : τ = 1 ∨ τ = σ := by
    by_cases hτ1 : τ = 1
    · exact Or.inl hτ1
    · exact Or.inr (huniq τ (by rw [pow_two]; exact hτsq) hτ1)
  let y' : MulAut (StatedProj (StatedSp r F)) := if τ = 1 then y else y * fieldAut r F σ
  have hy'E' : y' ∈ E' := by
    by_cases hτ1 : τ = 1
    · rw [show y' = y from by simp [y', hτ1]]
      exact hyE'
    · rw [show y' = y * fieldAut r F σ from by simp [y', hτ1]]
      exact Subgroup.mul_mem _ hyE' hfσmem
  have hy'notzp : y' ∉ Subgroup.zpowers (fieldAut r F σ) := by
    by_cases hτ1 : τ = 1
    · simpa [y', hτ1] using hyzp
    · intro hmem
      apply hyzp
      have hfσinv : (fieldAut r F σ)⁻¹ ∈ Subgroup.zpowers (fieldAut r F σ) :=
        Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      have hEq : y = y' * (fieldAut r F σ)⁻¹ := by
        simp [y', hτ1]
      rw [hEq]
      exact Subgroup.mul_mem _ hmem hfσinv
  have hy'2 : y' ^ 2 = 1 := hE'.2 y' hy'E'
  have hcomm : y' * fieldAut r F σ = fieldAut r F σ * y' := by
    simpa using hE'.1.is_comm.comm ⟨y', hy'E'⟩ ⟨fieldAut r F σ, hfσmem⟩
  have hy'eq : y' = conjAut r F Ay := by
    by_cases hτ1 : τ = 1
    · rw [show y' = y from by simp [y', hτ1], hyform, hτ1, map_one, mul_one]
    · have hτσ : τ = σ := hτ.resolve_left hτ1
      rw [show y' = y * fieldAut r F σ from by simp [y', hτ1], hyform, hτσ]
      rw [mul_assoc, ← map_mul, ← pow_two, hσ2, map_one, mul_one]
  have hcAfix : conjAut r F Ay = conjAut r F (gspFieldMap σ Ay) := by
    have h' := hcomm
    rw [hy'eq, fieldAut_mul_conjAut] at h'
    exact mul_right_cancel h'
  have hkernel : conjAut r F (Ay⁻¹ * gspFieldMap σ Ay) = 1 := by
    rw [map_mul, map_inv, hcAfix, inv_mul_cancel]
  have hscalar : ∃ cc : Fˣ, ((Ay⁻¹ * gspFieldMap σ Ay : gsp r F) : GL (Fin r ⊕ Fin r) F) =
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) cc := by
    have h' := (conjAut_mul_fieldAut_eq_one_iff
      (K := F) hr1 (Ay⁻¹ * gspFieldMap σ Ay) 1).mp (by rwa [map_one, mul_one])
    exact h'.2
  obtain ⟨cc, hcc⟩ := hscalar
  have hAymat_eq : Aym.map σ = (cc : F) • Aym := by
    have h2 : (((Ay : gsp r F) : GL (Fin r ⊕ Fin r) F))⁻¹ *
        (gspFieldMap σ Ay : GL (Fin r ⊕ Fin r) F) =
        GeneralLinearGroup.scalar (Fin r ⊕ Fin r) cc := by
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hcc
    have h3 : (((Ay : gsp r F) : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)⁻¹ *
        (((gspFieldMap σ Ay : gsp r F) : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
        Matrix.scalar (Fin r ⊕ Fin r) (cc : F) := by
      have h := congrArg (fun g : GL (Fin r ⊕ Fin r) F =>
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) h2
      simpa [GeneralLinearGroup.coe_scalar] using h
    have hgsp : (((gspFieldMap σ Ay : gsp r F) : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = Aym.map σ := by
      rw [coe_gspFieldMap]
      ext i j
      rw [glFieldEquiv_entry, Matrix.map_apply]
    rw [hgsp] at h3
    have hdet : IsUnit (Aym.det) := (Matrix.isUnit_iff_isUnit_det Aym).mp ⟨(Ay : gsp r F), rfl⟩
    calc Aym.map σ = Aym * (Aym⁻¹ * Aym.map σ) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
      _ = Aym * ((cc : F) • 1) := by
          rw [h3, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      _ = (cc : F) • Aym := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hAymat0 : Aym ≠ 0 := by
    intro h0
    have hunit : IsUnit Aym := ⟨(Ay : gsp r F), rfl⟩
    rw [h0] at hunit
    exact not_isUnit_zero hunit
  obtain ⟨c, hc0, hcrat⟩ :=
    exists_rational_smul_sum Nat.prime_two hℓ hf1 hcardNat σ hσord hAymat0 hAymat_eq
  let A'' : gsp r F := scalarGsp (Units.mk0 c hc0) * Ay
  let A''m : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
    ((A'' : gsp r F) : GL (Fin r ⊕ Fin r) F)
  have hA''coemat : A''m = c • Aym := by
    change (((A'' : gsp r F) : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = c • Aym
    have h' : ((A'' : gsp r F) : GL (Fin r ⊕ Fin r) F) =
        GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (Units.mk0 c hc0) *
          ((Ay : gsp r F) : GL (Fin r ⊕ Fin r) F) := by
      rw [show A'' = scalarGsp (Units.mk0 c hc0) * Ay from rfl, Subgroup.coe_mul, coe_scalarGsp]
    have h'' := congrArg (fun g : GL (Fin r ⊕ Fin r) F =>
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) h'
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar] at h''
    rw [h'', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hA''rat : A''m.map σ = A''m := by
    rw [hA''coemat]
    exact hcrat
  have hA''cA : conjAut r F A'' = conjAut r F Ay := by
    rw [show A'' = scalarGsp (Units.mk0 c hc0) * Ay from rfl, map_mul,
      conjAut_scalarGsp hr1, one_mul]
  have hy'eqA'' : y' = conjAut r F A'' := by
    rw [hy'eq, hA''cA]
  obtain ⟨u2, hu2⟩ := ((conjAut_mul_fieldAut_eq_one_iff
    (K := F) hr1 (A'' * A'') 1).mp (by
      have h2 := hy'2
      rw [hy'eqA'', pow_two, ← map_mul] at h2
      simpa using h2)).2
  have hA2 : A''m * A''m = (u2 : F) • 1 := by
    have h' : A''m * A''m = Matrix.scalar (Fin r ⊕ Fin r) (u2 : F) := by
      simpa [Subgroup.coe_mul, GeneralLinearGroup.coe_scalar] using
        congrArg (fun g : GL (Fin r ⊕ Fin r) F =>
          (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) hu2
    rw [h', Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hufix : σ (u2 : F) = (u2 : F) := by
    have hA2rat : (A''m * A''m).map σ = A''m * A''m := by
      rw [Matrix.map_mul, hA''rat]
    have h1 := congrFun (congrFun hA2rat (Sum.inl ⟨0, hr1⟩)) (Sum.inl ⟨0, hr1⟩)
    rw [hA2] at h1
    simpa [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] using h1
  let kk : Subfield F := CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ
  have hkk : ∀ x : F, x ∈ kk ↔ σ x = x := fun x => Iff.rfl
  have : CharP kk ℓ := Subfield.charP kk ℓ
  have : Finite kk := inferInstance
  have hkk2 : ringChar kk ≠ 2 := by
    rw [ringChar.eq kk ℓ]
    exact hℓ2
  let A0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) kk := Matrix.of fun i j =>
    ⟨A''m i j, (hkk _).mpr (by
      have h' := congrFun (congrFun hA''rat i) j
      simpa [Matrix.map_apply] using h')⟩
  have hA0map : A0.map (Subfield.subtype kk) = A''m := by
    ext i j
    simp [A0]
  have hA02 : A0 * A0 = (⟨(u2 : F), (hkk _).mpr hufix⟩ : kk) • 1 := by
    apply Matrix.map_injective (f := Subfield.subtype kk) (fun x y h => Subtype.ext h)
    change (A0 * A0).map (Subfield.subtype kk) =
      (((⟨(u2 : F), (hkk _).mpr hufix⟩ : kk) • 1 :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) kk)).map (Subfield.subtype kk)
    rw [Matrix.map_mul, hA0map]
    rw [Matrix.map_smul' (Subfield.subtype kk) (⟨(u2 : F), (hkk _).mpr hufix⟩ : kk)
      (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) kk) (map_mul _)]
    rw [Matrix.map_one (Subfield.subtype kk) (map_zero _) (map_one _)]
    rw [hA2]
    rfl
  have hA0ns : ∀ d : kk, A0 ≠ d • 1 := by
    intro d hd
    have hscal : A''m = (d : F) • 1 := by
      calc A''m = A0.map (Subfield.subtype kk) := hA0map.symm
        _ = ((d : kk) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) kk)).map
              (Subfield.subtype kk) := by rw [hd]
        _ = (d : F) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
            rw [Matrix.map_smul' (Subfield.subtype kk) d
              (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) kk) (map_mul _)]
            rw [Matrix.map_one (Subfield.subtype kk) (map_zero _) (map_one _)]
            rfl
    have hd0F : (d : F) ≠ 0 := by
      intro h0
      have hzero : A''m = 0 := by rw [hscal, h0, zero_smul]
      have hunit : IsUnit A''m := ⟨(A'' : gsp r F), rfl⟩
      rw [hzero] at hunit
      exact not_isUnit_zero hunit
    have hcA : conjAut r F A'' = 1 := by
      have hu : A'' = scalarGsp (Units.mk0 (d : F) hd0F) := by
        apply Subtype.ext
        apply Units.ext
        show A''m = (((scalarGsp (Units.mk0 (d : F) hd0F) : gsp r F) : GL (Fin r ⊕ Fin r) F) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
        rw [hscal, coe_scalarGsp, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.smul_one_eq_diagonal]
        simp
      rw [hu, conjAut_scalarGsp hr1]
    have hy1 : y' = 1 := by rw [hy'eqA'', hcA]
    exact hy'notzp (by rw [hy1]; exact Subgroup.one_mem _)
  have hνfix : σ ((multiplier r F A'' : F)) = (multiplier r F A'' : F) := by
    have hspec : A''mᵀ * formJ r F * A''m = (multiplier r F A'' : F) • formJ r F :=
      multiplier_spec (r := r) (K := F) A''
    have hmap : (A''mᵀ * formJ r F * A''m).map σ = A''mᵀ * formJ r F * A''m := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hA''rat, formJ_map]
    have h2 : ((multiplier r F A'' : F) • formJ r F).map σ =
        σ (multiplier r F A'' : F) • formJ r F := by
      rw [Matrix.map_smul' σ (multiplier r F A'' : F) (formJ r F) (map_mul σ)]
      rw [formJ_map]
    rw [hspec] at hmap
    rw [h2] at hmap
    exact smul_formJ_injective r hmap
  let ν0 : kk := ⟨(multiplier r F A'' : F), (hkk _).mpr hνfix⟩
  have hν0 : ν0 ≠ 0 := by
    intro h0
    have h1 : (multiplier r F A'' : F) = 0 := congrArg Subtype.val h0
    exact (Units.ne_zero (multiplier r F A'')) h1
  have hA0ν : A0ᵀ * formJ r kk * A0 = ν0 • formJ r kk := by
    apply Matrix.map_injective (f := Subfield.subtype kk) (fun x y h => Subtype.ext h)
    change (A0ᵀ * formJ r kk * A0).map (Subfield.subtype kk) =
      ((ν0 : kk) • formJ r kk).map (Subfield.subtype kk)
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hA0map]
    rw [Matrix.map_smul' (Subfield.subtype kk) (ν0 : kk) (formJ r kk) (map_mul _)]
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.formJ_map_ringHom (r := r) (K := F)
      (Subfield.subtype kk)]
    show A''mᵀ * formJ r F * A''m = (multiplier r F A'' : F) • formJ r F
    exact multiplier_spec (r := r) (K := F) A''
  obtain ⟨N0, hN0, hN02, hN0A, hN0J⟩ :=
    exists_sq_zero_commute_gsp hkk2 hr hν0 hA0ν hA02 hA0ns
  let N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F := N0.map (Subfield.subtype kk)
  have hN : N ≠ 0 := by
    intro h0
    apply hN0
    apply Matrix.map_injective (f := Subfield.subtype kk) (fun x y h => Subtype.ext h)
    simpa [N] using h0
  have hN2 : N * N = 0 := by
    have h' := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) kk =>
      M.map (Subfield.subtype kk)) hN02
    rw [Matrix.map_mul] at h'
    simpa [N] using h'
  have hNA : A''m * N = N * A''m := by
    have h' := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) kk =>
      M.map (Subfield.subtype kk)) hN0A
    rw [Matrix.map_mul, Matrix.map_mul, hA0map] at h'
    simpa [N] using h'
  have hNt : Nᵀ * formJ r F + formJ r F * N = 0 := by
    have h' := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) kk =>
      M.map (Subfield.subtype kk)) hN0J
    rw [Matrix.map_add (Subfield.subtype kk) (map_add _), Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.formJ_map_ringHom
        (r := r) (K := F) (Subfield.subtype kk)] at h'
    simpa [N] using h'
  let Xm : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F := 1 + N
  have hN3 : N ^ 3 = 0 := by
    calc N ^ 3 = N ^ 2 * N := by rw [pow_succ]
      _ = 0 := by rw [pow_two, hN2, Matrix.zero_mul]
  have hXinv : Xm * (1 - N) = 1 := by
    rw [show Xm = 1 + N from rfl, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hN2]
    abel
  have hXinv' : (1 - N) * Xm = 1 := by
    rw [show Xm = 1 + N from rfl, Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul,
      Matrix.one_mul, hN2]
    abel
  let Xgl : GL (Fin r ⊕ Fin r) F := ⟨Xm, 1 - N, hXinv, hXinv'⟩
  have hXgl : ((Xgl : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      1 + N := rfl
  have hNcross : Nᵀ * formJ r F * N = 0 := by
    have h1 : Nᵀ * formJ r F = -(formJ r F * N) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hNt
    rw [h1, Matrix.neg_mul, Matrix.mul_assoc, hN2, Matrix.mul_zero, neg_zero]
  have hspJ : ((Xgl : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ *
      formJ r F * ((Xgl : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = formJ r F := by
    rw [hXgl]
    calc (1 + N)ᵀ * formJ r F * (1 + N)
        = formJ r F + (Nᵀ * formJ r F + formJ r F * N) + Nᵀ * formJ r F * N := by
          rw [Matrix.transpose_add, Matrix.transpose_one]
          noncomm_ring
      _ = formJ r F := by rw [hNt, hNcross]; simp
  let Xsp : StatedSp r F := ⟨Xgl, by
    rw [SymplecticTorusWeyl.mem_statedSp_iff]
    exact hspJ⟩
  have hX1 : Xsp ≠ 1 := by
    intro h0
    apply hN
    have h1 : ((Xsp : StatedSp r F) : GL (Fin r ⊕ Fin r) F) = 1 := by rw [h0]; rfl
    have h2 : ((Xgl : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 :=
      congrArg (fun g : GL (Fin r ⊕ Fin r) F =>
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) h1
    rw [hXgl] at h2
    have h3 : 1 + N = 1 + (0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by simpa using h2
    exact add_left_cancel h3
  have hX3 : ((((Xsp : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) - 1) ^ 3 = 0 := by
    have h1 : (((Xsp : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 + N := by
      show ((Xgl : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 + N
      rw [hXgl]
    rw [h1]
    have h2 : (1 + N) - 1 = N := by abel
    rw [h2, hN3]
  have hNfix : N.map σ = N := by
    ext i j
    simp only [N, Matrix.map_apply]
    exact (hkk _).mp (N0 i j).2
  have hXfix : Xm.map σ = Xm := by
    change (1 + N).map σ = 1 + N
    rw [Matrix.map_add σ (map_add σ), hNfix, Matrix.map_one σ (map_zero σ) (map_one σ)]
  have hfσfix : fieldAut r F σ (proj r F Xsp) = proj r F Xsp := by
    rw [fieldAut_proj]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [coe_fieldSp]
    exact hXfix
  have hA''fix : conjAut r F A'' (proj r F Xsp) = proj r F Xsp := by
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_conjSp]
    have hAX : ((A'' : gsp r F) : GL (Fin r ⊕ Fin r) F) * Xgl =
        Xgl * ((A'' : gsp r F) : GL (Fin r ⊕ Fin r) F) := by
      apply Units.ext
      show A''m * Xm = Xm * A''m
      rw [show Xm = 1 + N from rfl, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
        Matrix.one_mul, hNA]
    rw [hAX, mul_assoc, mul_inv_cancel, mul_one]
  have hy'fix : y' (proj r F Xsp) = proj r F Xsp := by
    rw [hy'eqA'']
    exact hA''fix
  have hyfix : y (proj r F Xsp) = proj r F Xsp := by
    by_cases hτ1 : τ = 1
    · rwa [show y = y' from by simp [y', hτ1]]
    · have hys : y = y' * fieldAut r F σ := by
        simp only [y', if_neg hτ1]
        rw [mul_assoc, ← map_mul, ← pow_two, hσ2, map_one, mul_one]
      rw [hys, MulAut.mul_apply, hfσfix, hy'fix]
  have hstab : E' ≤ MulAction.stabilizer (MulAut (StatedProj (StatedSp r F))) (proj r F Xsp) := by
    rw [hgen]
    exact sup_le (Subgroup.zpowers_le.mpr (by simpa [MulAction.mem_stabilizer_iff] using hfσfix))
      (Subgroup.zpowers_le.mpr (by simpa [MulAction.mem_stabilizer_iff] using hyfix))
  have hfix : ∀ e ∈ E', e (proj r F Xsp) = proj r F Xsp := fun e he => hstab he
  exact (planeGen_map_congr h⁻¹ E).mp
    (planeGen_of_fixed_unipotent_sp hF hE' hcardE' Xsp hX1 hX3 hfix)

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
