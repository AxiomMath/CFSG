module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestOutdiag
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix
public import CFSG.RankThree.Classical2.MatrixFrobeniusLang
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace OrdPRest

theorem ringAut_fix_of_pow_eq_one {F : Type*} [Field F] {p : ℕ} (hp : p.Prime)
    {σ : F ≃+* F} (hσ : σ ^ p = 1) {x : F} (hx : x ^ p = 1) : σ x = x := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hx1 : x = 1
  · rw [hx1, map_one]
  have hprim : IsPrimitiveRoot x p := orderOf_eq_prime hx hx1 ▸ IsPrimitiveRoot.orderOf x
  have hσx : (σ x) ^ p = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hσx
  have hiter : ∀ k : ℕ, (σ ^ k) x = x ^ (i ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, pow_one, RingAut.one_apply]
    | succ k ih => rw [pow_succ', RingAut.mul_apply, ih, map_pow, ← hi, ← pow_mul, pow_succ']
  have key : ∀ a b : ℕ, a % p = b % p → x ^ a = x ^ b := fun a b h => by
    rw [← Nat.mod_add_div a p, ← Nat.mod_add_div b p, pow_add, pow_add, pow_mul, pow_mul, hx,
      one_pow, one_pow, h]
  have hferm : (i ^ p) % p = i % p := by
    have h1 := ZMod.pow_card (i : ZMod p)
    rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff'] at h1
    exact h1
  calc σ x = x ^ i := hi.symm
    _ = x ^ (i ^ p) := key _ _ hferm.symm
    _ = (σ ^ p) x := (hiter p).symm
    _ = x := by rw [hσ, RingAut.one_apply]

section Hilbert

variable {K : Type} [Field K] {n : ℕ}

theorem map_scalar (σ : K ≃+* K) (c : Kˣ) :
    GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →* K) c) := by
  apply Units.ext
  ext i j
  change (σ : K →+* K) ((GeneralLinearGroup.scalar (Fin n) c : Matrix (Fin n) (Fin n) K) i j) = _
  rw [GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply, scalar_apply,
    diagonal_apply, diagonal_apply]
  split_ifs <;> simp

theorem twistedProd_succ' (σ : K ≃+* K) (M : GL (Fin n) K) (k : ℕ) :
    ProjectivePlane.twistedProd σ M (k + 1) =
      M * GeneralLinearGroup.map (σ : K →+* K) (ProjectivePlane.twistedProd σ M k) := by
  induction k with
  | zero =>
    rw [ProjectivePlane.twistedProd_succ, ProjectivePlane.twistedProd_zero, pow_zero, map_one,
      one_mul, mul_one]
    exact Units.ext (Matrix.ext fun _ _ => rfl)
  | succ k ih =>
    calc ProjectivePlane.twistedProd σ M (k + 1 + 1) =
        ProjectivePlane.twistedProd σ M (k + 1) *
          GeneralLinearGroup.map ((σ ^ (k + 1) : K ≃+* K) : K →+* K) M :=
          ProjectivePlane.twistedProd_succ σ M (k + 1)
      _ = M * GeneralLinearGroup.map (σ : K →+* K) (ProjectivePlane.twistedProd σ M k) *
          GeneralLinearGroup.map ((σ ^ (k + 1) : K ≃+* K) : K →+* K) M := by rw [ih]
      _ = M * GeneralLinearGroup.map (σ : K →+* K) (ProjectivePlane.twistedProd σ M k *
          GeneralLinearGroup.map ((σ ^ k : K ≃+* K) : K →+* K) M) := by
          rw [map_mul, ProjectivePlane.map_map_ringEquiv, ← pow_succ', mul_assoc]
      _ = _ := by rw [ProjectivePlane.twistedProd_succ σ M k]

theorem twistedProd_scalar_mul (σ : K ≃+* K) (e : Kˣ) (M : GL (Fin n) K) (k : ℕ) :
    ProjectivePlane.twistedProd σ (GeneralLinearGroup.scalar (Fin n) e * M) k =
      GeneralLinearGroup.scalar (Fin n)
        (∏ i ∈ Finset.range k, Units.map ((σ ^ i : K ≃+* K) : K →* K) e) *
        ProjectivePlane.twistedProd σ M k := by
  induction k with
  | zero => rw [ProjectivePlane.twistedProd_zero, ProjectivePlane.twistedProd_zero,
      Finset.prod_range_zero, map_one, one_mul]
  | succ k ih =>
    rw [ProjectivePlane.twistedProd_succ, ProjectivePlane.twistedProd_succ, ih, map_mul,
      map_scalar, Finset.prod_range_succ, map_mul]
    have hc := (TypeA.PGLTor.commute_scalar (Units.map ((σ ^ k : K ≃+* K) : K →* K) e)
      (ProjectivePlane.twistedProd σ M k)).eq
    calc GeneralLinearGroup.scalar (Fin n)
          (∏ i ∈ Finset.range k, Units.map ((σ ^ i : K ≃+* K) : K →* K) e) *
          ProjectivePlane.twistedProd σ M k *
          (GeneralLinearGroup.scalar (Fin n) (Units.map ((σ ^ k : K ≃+* K) : K →* K) e) *
            GeneralLinearGroup.map ((σ ^ k : K ≃+* K) : K →+* K) M) =
        GeneralLinearGroup.scalar (Fin n)
          (∏ i ∈ Finset.range k, Units.map ((σ ^ i : K ≃+* K) : K →* K) e) *
          (ProjectivePlane.twistedProd σ M k *
            GeneralLinearGroup.scalar (Fin n) (Units.map ((σ ^ k : K ≃+* K) : K →* K) e)) *
          GeneralLinearGroup.map ((σ ^ k : K ≃+* K) : K →+* K) M := by group
      _ = _ := by rw [← hc]; group

theorem coe_twistedProd (σ : K ≃+* K) (M : GL (Fin n) K) (k : ℕ) :
    ((ProjectivePlane.twistedProd σ M k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      CFSG.RankThree.Classical2.twistedProd σ (M : Matrix (Fin n) (Fin n) K) k := by
  change _ = CFSG.RankThree.Classical2.twistedProd ((σ : K →+* K) : K → K) _ k
  induction k with
  | zero => rw [ProjectivePlane.twistedProd_zero, CFSG.RankThree.Classical2.twistedProd_zero,
      Units.val_one]
  | succ k ih =>
    rw [ProjectivePlane.twistedProd_succ, Units.val_mul, ih,
      CFSG.RankThree.Classical2.twistedProd_add (σ : K →+* K) _ k 1,
      CFSG.RankThree.Classical2.twistedProd_succ, CFSG.RankThree.Classical2.twistedProd_zero]
    congr 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    change (M : Matrix (Fin n) (Fin n) K).map ⇑(σ ^ k) = _
    rw [RingAut.coe_pow]
    rfl

theorem exists_hilbert90 [Finite K] (hn : 1 ≤ n) {σ : K ≃+* K} {h : ℕ} (hσ : orderOf σ = h)
    (A : GL (Fin n) K) {c : Kˣ}
    (hc : ProjectivePlane.twistedProd σ A h = GeneralLinearGroup.scalar (Fin n) c) :
    ∃ (H : GL (Fin n) K) (d : Kˣ), A * GeneralLinearGroup.map (σ : K →+* K) H =
      GeneralLinearGroup.scalar (Fin n) d * H := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    fun a b hab => RingEquiv.ext (congrFun hab)
  have hpos : 0 < h := hσ ▸ orderOf_pos σ
  have hσh : σ ^ h = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hcfix : σ (c : K) = c := by
    have h1 := twistedProd_succ' σ A h
    rw [ProjectivePlane.twistedProd_succ, hc, hσh, map_scalar] at h1
    have h2 : GeneralLinearGroup.map (((1 : K ≃+* K)) : K →+* K) A = A :=
      Units.ext (Matrix.ext fun _ _ => rfl)
    rw [h2, ← (TypeA.PGLTor.commute_scalar _ A).eq] at h1
    have h4 := TypeA.PGLTor.scalar_injective (mul_right_cancel h1)
    exact (congrArg (fun u : Kˣ => (u : K)) h4).symm
  obtain ⟨d, hd⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ hcfix
  rw [hσ] at hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h0 : ∏ i ∈ Finset.range h, (σ ^ i) (0 : K) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hpos) (map_zero _)
    rw [h0] at hd
    exact c.ne_zero hd.symm
  set du : Kˣ := Units.mk0 d hd0 with hdu
  set A' : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) du⁻¹ * A with hA'
  have hprod : (∏ i ∈ Finset.range h, Units.map ((σ ^ i : K ≃+* K) : K →* K) du⁻¹) * c = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.coe_prod, Units.val_one]
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_inv_eq_inv_val, hdu,
      Units.val_mk0, map_inv₀]
    rw [Finset.prod_inv_distrib, hd, inv_mul_cancel₀ c.ne_zero]
  have hT : ProjectivePlane.twistedProd σ A' h = 1 := by
    rw [hA', twistedProd_scalar_mul, hc, ← map_mul, hprod, map_one]
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, -, e, hℓ, hcard⟩ := FiniteField.card' K
  obtain ⟨B, hB, hfix⟩ := CFSG.RankThree.Classical2.exists_isUnit_det_fixed (n := n) hℓ e.pos
    (by rw [Nat.card_eq_fintype_card, hcard]) σ hσ (A' : Matrix (Fin n) (Fin n) K)
    (Matrix.isUnits_det_units A') fun v => by
      rw [← coe_twistedProd, hT, Units.val_one, Matrix.one_mulVec, ← RingAut.coe_pow, hσh]
      rfl
  refine ⟨((Matrix.isUnit_iff_isUnit_det B).mpr hB).unit, du, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
  change (A : Matrix (Fin n) (Fin n) K) *
      (((Matrix.isUnit_iff_isUnit_det B).mpr hB).unit : Matrix (Fin n) (Fin n) K).map σ = _
  rw [IsUnit.unit_spec]
  have hA'm : (A' : Matrix (Fin n) (Fin n) K) =
      scalar (Fin n) ((du⁻¹ : Kˣ) : K) * (A : Matrix (Fin n) (Fin n) K) := by
    rw [hA', Units.val_mul, GeneralLinearGroup.coe_scalar]
  rw [hA'm, Matrix.mul_assoc] at hfix
  calc (A : Matrix (Fin n) (Fin n) K) * B.map σ = scalar (Fin n) (du : K) *
      (scalar (Fin n) ((du⁻¹ : Kˣ) : K) * ((A : Matrix (Fin n) (Fin n) K) * B.map σ)) := by
        rw [← Matrix.mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          map_one, Matrix.one_mul]
    _ = scalar (Fin n) (du : K) * B := by rw [hfix]

theorem conjAut_mul_fieldAut_eq_conj' (A H : GL (Fin n) K) (σ : K ≃+* K) (d : Kˣ)
    (h : A * GeneralLinearGroup.map (σ : K →+* K) H = GeneralLinearGroup.scalar (Fin n) d * H) :
    conjAut n K A * fieldAut n K σ = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
  have hA : A = GeneralLinearGroup.scalar (Fin n) d * H *
      (GeneralLinearGroup.map (σ : K →+* K) H)⁻¹ := by
    rw [← h]
    group
  have hfc := fieldAut_mul_conjAut (n := n) σ H⁻¹
  rw [hA, map_mul, map_mul, conjAut_scalar, one_mul, map_inv, ← map_inv]
  calc conjAut n K H * conjAut n K (GeneralLinearGroup.map (σ : K →+* K) H⁻¹) *
        fieldAut n K σ = conjAut n K H * (fieldAut n K σ * conjAut n K H⁻¹) := by
        rw [hfc]
        group
    _ = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
        rw [map_inv]
        group

end Hilbert

section InnerDiag

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem ggPsiInnerDiag_of_conjAut (hm : 2 ≤ m) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) {A : GL (Fin (m + 1)) F}
    (hα : ∀ y y' : SpecialLinearGroup (Fin (m + 1)) F,
      ψ y' = c⁻¹ * ψ y * c → conjAut (m + 1) F A (proj (m + 1) F y) = proj (m + 1) F y') :
    GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ c := by
  set d : F := (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det with hd
  have hd0 : d ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  set e : Fin (m + 1) → F := fun l => if l = 0 then d else 1 with he
  have he0 : ∀ l, e l ≠ 0 := fun l => by
    simp only [e]
    split_ifs
    exacts [hd0, one_ne_zero]
  have hdetD : (Matrix.diagonal e).det = d := by
    rw [Matrix.det_diagonal]
    simp [e]
  set D : GL (Fin (m + 1)) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal e)
    (by rw [hdetD]; exact hd0)
  have hDval : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal e := rfl
  have hdet1 : Matrix.GeneralLinearGroup.det (A * D⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hDval,
      hdetD]
  obtain ⟨A₀, hA₀⟩ : A * D⁻¹ ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m + 1)) F →*
      GL (Fin (m + 1)) F).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet1
  have hlift := HypSixTypeA.conj_eq_of_conjAut hm hc hα hA₀
  refine ⟨ψ A₀, ⟨A₀, rfl⟩, fun γ' hγ' => ?_⟩
  have hij' : (SpecialLinear.idx m γ').1 ≠ (SpecialLinear.idx m γ').2 :=
    (SpecialLinear.idx_spec m hγ').1
  set i' := (SpecialLinear.idx m γ').1
  set j' := (SpecialLinear.idx m γ').2
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin (m + 1), k ≠ i' ∧ k ≠ j' := by
    by_contra hcon
    simp only [not_exists] at hcon
    have h0 := hcon ⟨0, by omega⟩
    have h1 := hcon ⟨1, by omega⟩
    have h2 := hcon ⟨2, by omega⟩
    simp only [ne_eq, Fin.ext_iff] at h0 h1 h2
    omega
  set lam : F := e i' * (e j')⁻¹
  have hlam : lam ≠ 0 := mul_ne_zero (he0 i') (inv_ne_zero (he0 j'))
  set e' : Fin (m + 1) → F := fun l => (if l = i' then lam else 1) * (if l = k then lam⁻¹ else 1)
  have he'0 : ∀ l, e' l ≠ 0 := fun l => by
    simp only [e']
    refine mul_ne_zero ?_ ?_ <;> split_ifs
    exacts [hlam, one_ne_zero, inv_ne_zero hlam, one_ne_zero]
  have hdet' : (Matrix.diagonal e').det = 1 := by
    rw [Matrix.det_diagonal]
    simp only [e', Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    exact mul_inv_cancel₀ hlam
  refine ⟨⟨Matrix.diagonal e', hdet'⟩, HypSixTypeA.mem_ggTorus_of_diagonal he'0 rfl,
    fun z hz => ?_⟩
  change z ∈ SpecialLinear.rootGroup m F γ' at hz
  rw [SpecialLinear.rootGroup_eq_idx m F hγ'] at hz
  obtain ⟨t, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij' z).mp hz
  rw [hlift, HypSixTypeA.slConjugation_diag_transvection he0 hDval hij' t,
    HypSixTypeA.sl_diag_conj_transvection (h := ⟨Matrix.diagonal e', hdet'⟩) he'0 rfl hij' t]
  congr 2
  have hei : e' i' = lam := by simp [e', Ne.symm hki]
  have hej : e' j' = 1 := by simp [e', Ne.symm hij', Ne.symm hkj]
  rw [hei, hej]
  simp only [lam]
  ring

end InnerDiag

section Split

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {m f : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

omit [Finite F] [CharP F 2] in
theorem map_eq_scalar_mul_of_diag {p : ℕ} (hp : p.Prime) {σ : F ≃+* F} (hσ : σ ^ p = 1)
    {D : GL (Fin (m + 1)) F} {t : Fin (m + 1) → F}
    (hD : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal t) {c : Fˣ}
    (hDp : D ^ p = GeneralLinearGroup.scalar (Fin (m + 1)) c) :
    ∃ l : Fˣ, GeneralLinearGroup.map (σ : F →+* F) D =
      GeneralLinearGroup.scalar (Fin (m + 1)) l * D := by
  have ht0 : ∀ i, t i ≠ 0 := TypeA.PGLTor.diag_ne_zero_of_eq_diagonal hD
  have htp : ∀ i, t i ^ p = c := fun i => by
    have h1 := congrArg
      (fun X : GL (Fin (m + 1)) F => (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i) hDp
    simp only [Units.val_pow_eq_pow_val, hD, diagonal_pow, diagonal_apply_eq,
      GeneralLinearGroup.coe_scalar, scalar_apply, Pi.pow_apply] at h1
    exact h1
  set l : F := σ (t 0) * (t 0)⁻¹ with hl
  have hl0 : l ≠ 0 := mul_ne_zero ((map_ne_zero σ).mpr (ht0 0)) (inv_ne_zero (ht0 0))
  have hσt : ∀ i, σ (t i) = l * t i := by
    intro i
    have h1 : (t i * (t 0)⁻¹) ^ p = 1 := by
      rw [mul_pow, inv_pow, htp i, htp 0, mul_inv_cancel₀ c.ne_zero]
    have h2 := ringAut_fix_of_pow_eq_one hp hσ h1
    rw [map_mul, map_inv₀] at h2
    have h3 : σ (t i) = t i * (t 0)⁻¹ * σ (t 0) := by
      rw [← h2]
      field_simp [(map_ne_zero σ).mpr (ht0 0)]
    rw [h3, hl]
    field_simp
  refine ⟨Units.mk0 l hl0, Units.ext ?_⟩
  change (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map σ = _
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hD, Units.val_mk0]
  ext i j
  rw [Matrix.map_apply, scalar_apply, diagonal_mul_diagonal, diagonal_apply, diagonal_apply]
  split_ifs with hij
  · subst hij
    exact hσt i
  · exact map_zero σ

theorem exists_conj_mem_centralizer_of_field
    (hS : GGSixFusionSetting p Bs G₀ (SpecialLinear.rootDatum m F) .PSL (m + 1) f ψ)
    (h24 : GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G))) (hpF : p ∣ Nat.card F - 1)
    {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : y ^ p = 1)
    (hyI : ¬ GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ y) :
    ∃ s : SpecialLinearGroup (Fin (m + 1)) F,
      (ψ s)⁻¹ * y * ψ s ∈ Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hm : 2 ≤ m := hrank
  have hn : 3 ≤ m + 1 := by omega
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  set N := Subgroup.normalizer (ψ.range : Set G) with hN
  set φN := ψ.range.normalizerMonoidHom
  have hφN : Function.Injective φN := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hCψ,
      Subgroup.bot_subgroupOf]
  set Θ := AutPSL.projEquiv (m := m) (K := F) hker hCψ
  set χ : N →* MulAut (projectiveSL (m + 1) F) := (MulAut.congr Θ).symm.toMonoidHom.comp φN
  have hχ : Function.Injective χ := (MulAut.congr Θ).symm.injective.comp hφN
  have hχα : ∀ (b : N) (u u' : SpecialLinearGroup (Fin (m + 1)) F),
      ψ u' = (b : G) * ψ u * (b : G)⁻¹ → χ b (proj (m + 1) F u) = proj (m + 1) F u' := by
    intro b u u' hu
    change Θ.symm (φN b (Θ (proj (m + 1) F u))) = proj (m + 1) F u'
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    change (b : G) * ψ u * (b : G)⁻¹ = ψ u'
    rw [hu]
  have hχA : ∀ (b : N) (A : GL (Fin (m + 1)) F),
      (∀ u, (b : G) * ψ u * (b : G)⁻¹ = ψ (InnerDiagA.conjSL A u)) →
        χ b = conjAut (m + 1) F A := by
    intro b A hA
    ext x
    obtain ⟨u, rfl⟩ := proj_surjective (m + 1) F x
    rw [hχα b u _ (hA u).symm, conjAut_proj, RootPlaneA.slConjugation_eq_conjSL]
  have hψN : ∀ s : SpecialLinearGroup (Fin (m + 1)) F, ψ s ∈ N := fun s =>
    Subgroup.le_normalizer ⟨s, rfl⟩
  have hχψ : ∀ s : SpecialLinearGroup (Fin (m + 1)) F,
      χ ⟨ψ s, hψN s⟩ = conjAut (m + 1) F (SpecialLinearGroup.toGL s) := by
    intro s
    refine hχA ⟨ψ s, hψN s⟩ _ fun u => ?_
    change ψ s * ψ u * (ψ s)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hyN : y ∈ N := by
    rw [hN, hrange]
    exact hyM
  set y' : N := ⟨y, hyN⟩ with hy'
  have hχp : χ y' ^ p = 1 := by
    rw [← map_pow]
    have : y' ^ p = 1 := Subtype.ext hyp
    rw [this, map_one]
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) hn).2 (χ y')
  have hε0 : ε = 0 := HypSixTypeA.graph_exp_eq_zero hn (hp.odd_of_ne_two hp2) hε
    (by rw [← hαeq]; exact hχp)
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hαeq
    apply hyI
    refine ggPsiInnerDiag_of_conjAut hm hyN (A := A⁻¹) fun u u' hu => ?_
    have h1 := hχα y' u' u (by
      change ψ u = y * ψ u' * y⁻¹
      rw [hu]
      group)
    rw [hαeq] at h1
    rw [map_inv]
    change (conjAut (m + 1) F A).symm (proj (m + 1) F u) = proj (m + 1) F u'
    rw [MulEquiv.symm_apply_eq]
    exact h1.symm
  have h1 := ProjectivePlane.conjAut_mul_fieldAut_pow σ A p
  rw [← hαeq, hχp] at h1
  obtain ⟨hσp, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1.symm
  have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨H, d, hH⟩ := exists_hilbert90 (by omega) hσo A hc.symm
  have hyH := conjAut_mul_fieldAut_eq_conj' A H σ d hH
  rw [← hαeq] at hyH
  obtain ⟨A₀, hA₀⟩ := bstar_toral hS h24 hpF
  set δ : Fˣ := (GeneralLinearGroup.det H * GeneralLinearGroup.det A₀)⁻¹ with hδ
  set T : GL (Fin (m + 1)) F := InnerDiagA.diagGL (Pi.mulSingle 0 δ) with hT
  have hTdiag : (T : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := by
    rw [hT, InnerDiagA.coe_diagGL]
    exact isDiag_diagonal _
  have hdetT : GeneralLinearGroup.det T = δ := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, hT, InnerDiagA.coe_diagGL, det_diagonal,
      ← Units.coe_prod, Finset.prod_pi_mulSingle', ite_eq_left (Finset.mem_univ _)]
  have hdet : GeneralLinearGroup.det (H * T * A₀) = 1 := by
    rw [map_mul, map_mul, hdetT, hδ, mul_right_comm, mul_inv_cancel]
  obtain ⟨s, hs⟩ : H * T * A₀ ∈ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  refine ⟨s, ?_⟩
  have hzN : (ψ s)⁻¹ * y * ψ s ∈ N := N.mul_mem (N.mul_mem (N.inv_mem (hψN s)) hyN) (hψN s)
  set z : N := ⟨(ψ s)⁻¹ * y * ψ s, hzN⟩ with hz
  have hzχ : χ z = (conjAut (m + 1) F A₀)⁻¹ * (conjAut (m + 1) F T)⁻¹ * fieldAut (m + 1) F σ *
      conjAut (m + 1) F T * conjAut (m + 1) F A₀ := by
    have e1 : z = (⟨ψ s, hψN s⟩ : N)⁻¹ * y' * ⟨ψ s, hψN s⟩ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv, hχψ s, hs, hyH, map_mul, map_mul]
    group
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbN : b ∈ N := by
    rw [hN, hrange]
    exact hS.bstar_le hb
  obtain ⟨Ab, hAb⟩ := RootPlaneA.exists_gl_of_psiInnerDiag hm hker
    (hS.innerDiag b⁻¹ (Bs.inv_mem hb))
  have hχb : χ ⟨b, hbN⟩ = conjAut (m + 1) F Ab :=
    hχA ⟨b, hbN⟩ Ab fun u => by
      rw [← hAb u, inv_inv]
  have hD := hA₀ b⁻¹ (Bs.inv_mem hb) Ab hAb
  set Db : GL (Fin (m + 1)) F := A₀ * Ab * A₀⁻¹ with hDb
  have hDbt : (Db : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      diagonal (Matrix.diag (Db : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) := hD.diagonal_diag.symm
  have hbp : b⁻¹ ^ p = 1 := by rw [inv_pow, hS.elem.2 b hb, inv_one]
  obtain ⟨c', hc'⟩ := exists_scalar_pow hker hAb hbp
  have hDbp : Db ^ p = GeneralLinearGroup.scalar (Fin (m + 1)) c' := by
    rw [hDb, _root_.conj_pow, hc', (TypeA.PGLTor.commute_scalar c' A₀).eq.symm,
      mul_inv_cancel_right]
  obtain ⟨l, hl⟩ := map_eq_scalar_mul_of_diag hp hσp hDbt hDbp
  have hFZ : fieldAut (m + 1) F σ * conjAut (m + 1) F Db =
      conjAut (m + 1) F Db * fieldAut (m + 1) F σ := by
    rw [fieldAut_mul_conjAut, hl, map_mul, conjAut_scalar, one_mul]
  have hYZ : conjAut (m + 1) F T * conjAut (m + 1) F Db =
      conjAut (m + 1) F Db * conjAut (m + 1) F T := by
    rw [← map_mul, ← map_mul, (RootPlaneA.commute_of_isDiag hTdiag hD).eq]
  have hYZ' : (conjAut (m + 1) F T)⁻¹ * conjAut (m + 1) F Db =
      conjAut (m + 1) F Db * (conjAut (m + 1) F T)⁻¹ := by
    calc (conjAut (m + 1) F T)⁻¹ * conjAut (m + 1) F Db =
        (conjAut (m + 1) F T)⁻¹ * (conjAut (m + 1) F Db * conjAut (m + 1) F T) *
          (conjAut (m + 1) F T)⁻¹ := by group
      _ = (conjAut (m + 1) F T)⁻¹ * (conjAut (m + 1) F T * conjAut (m + 1) F Db) *
          (conjAut (m + 1) F T)⁻¹ := by rw [hYZ]
      _ = _ := by group
  have hAbDb : conjAut (m + 1) F Ab =
      (conjAut (m + 1) F A₀)⁻¹ * conjAut (m + 1) F Db * conjAut (m + 1) F A₀ := by
    rw [hDb, map_mul, map_mul, map_inv]
    group
  have key : χ z * χ ⟨b, hbN⟩ = χ ⟨b, hbN⟩ * χ z := by
    rw [hzχ, hχb, hAbDb]
    calc (conjAut (m + 1) F A₀)⁻¹ * (conjAut (m + 1) F T)⁻¹ * fieldAut (m + 1) F σ *
          conjAut (m + 1) F T * conjAut (m + 1) F A₀ *
          ((conjAut (m + 1) F A₀)⁻¹ * conjAut (m + 1) F Db * conjAut (m + 1) F A₀) =
        (conjAut (m + 1) F A₀)⁻¹ * (conjAut (m + 1) F T)⁻¹ * fieldAut (m + 1) F σ *
          (conjAut (m + 1) F T * conjAut (m + 1) F Db) * conjAut (m + 1) F A₀ := by group
      _ = (conjAut (m + 1) F A₀)⁻¹ * (conjAut (m + 1) F T)⁻¹ *
          (fieldAut (m + 1) F σ * conjAut (m + 1) F Db) * conjAut (m + 1) F T *
          conjAut (m + 1) F A₀ := by rw [hYZ]; group
      _ = (conjAut (m + 1) F A₀)⁻¹ * ((conjAut (m + 1) F T)⁻¹ * conjAut (m + 1) F Db) *
          fieldAut (m + 1) F σ * conjAut (m + 1) F T * conjAut (m + 1) F A₀ := by
          rw [hFZ]; group
      _ = _ := by rw [hYZ']; group
  have hzb : z * ⟨b, hbN⟩ = ⟨b, hbN⟩ * z := hχ (by rw [map_mul, map_mul, key])
  exact (congrArg Subtype.val hzb).symm

end Split

end OrdPRest

section Family

theorem ggOrdPFieldConj_PSL_split : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSL n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSL n f).D .PSL n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      ¬ GGPsiInnerDiag (ggU .PSL n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f ψ hS h24 hpq y hyM hyo hyI
  obtain ⟨⟨hadm, -⟩, ⟨hrange, -⟩, -, -⟩ := hS.presents
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f (by omega)]
    exact hpq
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  obtain ⟨s, hs⟩ := OrdPRest.exists_conj_mem_centralizer_of_field (F := GaloisField 2 f) hS h24
    hpF hyM hyp hyI
  exact ⟨ψ s, Subgroup.le_normalizer (hrange ▸ ⟨s, rfl⟩), hs⟩

@[expose] def GGOrdPFieldConjPSLNonsplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .PSL n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSL n f).D .PSL n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → ¬ p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p → GGPsiDiagField (ggU .PSL n f).D ψ y →
      ¬ GGPsiInnerDiag (ggU .PSL n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

theorem ggOrdPFieldConjAt_PSL_of_nonsplit (h : GGOrdPFieldConjPSLNonsplit) :
    GGOrdPFieldConjAt .PSL := by
  intro G _ _ p Bs G₀ n f ψ hS h24 y hyM hyo hDF hyI
  by_cases hpq : p ∣ 2 ^ f - 1
  · exact ggOrdPFieldConj_PSL_split G p Bs G₀ n f ψ hS h24 hpq y hyM hyo hyI
  · exact h G p Bs G₀ n f ψ hS h24 hpq y hyM hyo hDF hyI

end Family

end CFSG.StandardType
