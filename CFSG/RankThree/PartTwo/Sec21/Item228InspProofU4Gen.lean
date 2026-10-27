module

public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
public import CFSG.RankThree.PartOne.K1320.SU4Gen

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228InspProof

open Matrix CFSG CFSG.RankThree
open CFSG.LieType.Universal.Unitary (SU mem_SU rootMatrix longRootMatrix rootHom longRootHom
  traceZero mem_traceZero eq_top_of_rootElements_le coe_rootHom coe_longRootHom)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive
  exists_add_unitaryInvolution_eq)
open CFSG.RankThree.PartOne.KFU (permGL coe_permGL coe_permGL_inv permGL_mem_SU)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (longSL shortSL iotaL iotaS coe_iotaL coe_iotaS blkL
  blkS weyl₁ weyl₂ torusD)

section Perm

variable {F : Type} [Field F]

theorem rootMatrix_submatrix (σ : F ≃+* F) {n : ℕ} (τ : Equiv.Perm (Fin n))
    (hτ : ∀ i, τ (Fin.rev i) = Fin.rev (τ i)) (i j : Fin n) (c : F) :
    (rootMatrix σ i j c).submatrix τ.symm τ.symm = rootMatrix σ (τ i) (τ j) c := by
  ext a b
  simp only [rootMatrix, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.single_apply, Matrix.one_apply, Equiv.eq_symm_apply, Equiv.apply_symm_apply, hτ]

theorem longRootMatrix_submatrix {n : ℕ} (τ : Equiv.Perm (Fin n))
    (hτ : ∀ i, τ (Fin.rev i) = Fin.rev (τ i)) (i : Fin n) (c : F) :
    (longRootMatrix i c).submatrix τ.symm τ.symm = longRootMatrix (τ i) c := by
  ext a b
  simp only [longRootMatrix, Matrix.submatrix_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.one_apply, Equiv.eq_symm_apply, Equiv.apply_symm_apply, hτ]

theorem coe_permGL_conj {n : ℕ} (τ : Equiv.Perm (Fin n)) (g : GL (Fin n) F) :
    ((permGL τ * g * (permGL τ)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F).submatrix τ.symm τ.symm := by
  rw [Units.val_mul, Units.val_mul, coe_permGL, coe_permGL_inv]
  have h1 : (τ⁻¹.permMatrix F) * (g : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F).submatrix (τ⁻¹ : Equiv.Perm (Fin n)) id :=
    PEquiv.toMatrix_toPEquiv_mul _ _
  have h2 : ((g : Matrix (Fin n) (Fin n) F).submatrix (τ⁻¹ : Equiv.Perm (Fin n)) id) *
      τ.permMatrix F = ((g : Matrix (Fin n) (Fin n) F).submatrix
        (τ⁻¹ : Equiv.Perm (Fin n)) id).submatrix id τ.symm :=
    PEquiv.mul_toMatrix_toPEquiv _ _
  rw [h1, h2]
  ext a b
  simp [Equiv.Perm.inv_def]

@[expose] def tau₁ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def tau₂ : Equiv.Perm (Fin 4) := Equiv.swap 1 2

theorem tau₁_facts : tau₁.symm = tau₁ ∧ (∀ i, tau₁ (Fin.rev i) = Fin.rev (tau₁ i)) ∧
    tau₁ 0 = 1 ∧ tau₁ 1 = 0 ∧ tau₁ 2 = 3 ∧ tau₁ 3 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem tau₂_facts : tau₂.symm = tau₂ ∧ (∀ i, tau₂ (Fin.rev i) = Fin.rev (tau₂ i)) ∧
    tau₂ 0 = 0 ∧ tau₂ 1 = 2 ∧ tau₂ 2 = 1 ∧ tau₂ 3 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem weyl₁_eq : (weyl₁ : GL (Fin 4) F) = permGL tau₁ := rfl

theorem weyl₂_eq : (weyl₂ : GL (Fin 4) F) = permGL tau₂ := rfl

end Perm

section Long

variable {F : Type} [Field F] (σ : F ≃+* F)

theorem blkL_mul_conj (M M' : Matrix (Fin 2) (Fin 2) F) :
    blkL M * (blkL M').submatrix tau₁.symm tau₁.symm =
      (blkL M').submatrix tau₁.symm tau₁.symm * blkL M := by
  obtain ⟨hs, -, h0, h1, h2, h3⟩ := tau₁_facts
  rw [hs]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blkL, Matrix.mul_apply, Fin.sum_univ_four, Matrix.submatrix_apply, h0, h1, h2, h3]

theorem commute_longSL_weyl₁ {x y : GL (Fin 4) F} (hx : x ∈ longSL σ)
    (hy : y ∈ (longSL σ).map (MulAut.conj weyl₁).toMonoidHom) : x * y = y * x := by
  obtain ⟨M, rfl⟩ := hx
  obtain ⟨_, ⟨M', rfl⟩, rfl⟩ := hy
  apply Units.ext
  change ((iotaL σ M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((weyl₁ * iotaL σ M' * weyl₁⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    ((weyl₁ * iotaL σ M' * weyl₁⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((iotaL σ M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  rw [weyl₁_eq, coe_permGL_conj, coe_iotaL, coe_iotaL]
  exact blkL_mul_conj _ _

theorem commutator_longSL_weyl₁ :
    ⁅longSL σ, (longSL σ).map (MulAut.conj (weyl₁ : GL (Fin 4) F)).toMonoidHom⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (commute_longSL_weyl₁ σ hx hy).symm

end Long

section Mixed

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

open CFSG.RankThree.PartOne.KFU (suBlock suBlockB blkB coe_suBlock coe_suBlockB b5 dvec4 diagU
  diagU_val d8Vec_four suBlock_mem_centralizer fixF)

omit [Finite F] [CharP F 2] in
theorem blkB_eq_blkS (σ : F ≃+* F) (X : Matrix (Fin 2) (Fin 2) F) : blkB σ X = blkS σ X := rfl

omit [Finite F] in
theorem map_range_suBlockB_le (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) :
    (suBlockB σ hσ).range.map (SU σ 4).subtype ≤ shortSL σ := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  refine ⟨A, Units.ext ?_⟩
  rw [coe_iotaS]
  change blkS σ (A : Matrix (Fin 2) (Fin 2) F) = (((suBlockB σ hσ A : SU σ 4) : GL (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F)
  rw [coe_suBlockB, blkB_eq_blkS]

theorem map_range_suBlock_le (hb : 2 ≤ b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ω : rootsOfUnity 3 F} (hfix : unitaryInvolution F 2 b ((ω : Fˣ) : F) = (ω : Fˣ)) :
    (suBlock (unitaryInvolution F 2 b)).range.map (SU (unitaryInvolution F 2 b) 4).subtype ≤
      inSubgroup perfectResidual (SU (unitaryInvolution F 2 b) 4 ⊓
        Subgroup.centralizer (Subgroup.zpowers (torusD (1, ω)) : Set (GL (Fin 4) F))) := by
  set σ := unitaryInvolution F 2 b with hσdef
  set f : Matrix.SpecialLinearGroup (Fin 2) (fixF σ) →* GL (Fin 4) F :=
    (SU σ 4).subtype.comp (suBlock σ) with hf
  have hrange : (suBlock σ).range.map (SU σ 4).subtype = f.range := by
    rw [hf, MonoidHom.range_comp]
  have hq : Nat.card (fixF σ) = 2 ^ b := CFSG.LieType.Steinberg.card_fixedSubfield hF
  have h4 : 4 ≤ Nat.card (fixF σ) := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have : Finite (fixF σ) := Finite.of_injective _ Subtype.val_injective
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (fixF σ)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ h4
  have hperf : Group.IsPerfect f.range :=
    Group.IsPerfect.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  rw [hrange]
  refine Sec18.le_inSubgroup_perfectResidual (Subgroup.isPerfect_iff.mp hperf) (le_inf ?_ ?_)
  · rintro _ ⟨A, rfl⟩
    exact (suBlock σ A).2
  · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp
      (suBlock_mem_centralizer σ (ζ := (ω : Fˣ)) hfix A)
    have h' := congrArg (fun g : SU σ 4 => (g : GL (Fin 4) F)) h
    simp only [Subgroup.coe_mul] at h'
    have hb5 : ((b5 σ (ω : Fˣ) hfix : SU σ 4) : GL (Fin 4) F) = torusD (1, ω) := by
      rw [CFSG.RankThree.PartOne.KFU.coe_b5, U4Lines.torusD_apply, d8Vec_four]
      rfl
    rw [hb5] at h'
    exact h'

theorem sup_shortSL_eq_SU_of (hb : 1 ≤ b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {S : Subgroup (GL (Fin 4) F)} (hSU : S ≤ SU (unitaryInvolution F 2 b) 4)
    (hS : (suBlock (unitaryInvolution F 2 b)).range.map (SU (unitaryInvolution F 2 b) 4).subtype ≤
      S) :
    S ⊔ shortSL (unitaryInvolution F 2 b) = SU (unitaryInvolution F 2 b) 4 := by
  set σ := unitaryInvolution F 2 b with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  apply le_antisymm (sup_le hSU (U4Lines.shortSL_le_SU σ hσ))
  have htop := CFSG.RankThree.PartOne.K1320.suBlock_sup_suBlockB_eq_top hF hb
  calc SU σ 4 = (⊤ : Subgroup (SU σ 4)).map (SU σ 4).subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = ((suBlock σ).range ⊔ (suBlockB σ hσ).range).map (SU σ 4).subtype := by rw [htop]
    _ = (suBlock σ).range.map (SU σ 4).subtype ⊔ (suBlockB σ hσ).range.map (SU σ 4).subtype :=
        Subgroup.map_sup _ _ _
    _ ≤ S ⊔ shortSL σ := sup_le_sup hS (map_range_suBlockB_le σ hσ)

end Mixed

section Short

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

open CFSG.RankThree.PartOne.K1320 (rootMatrix_01 rootMatrix_10 rootMatrix_23 rootMatrix_32)

omit [Finite F] [CharP F 2] in
@[expose] def upSL (c : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, c; 0, 1], by rw [Matrix.det_fin_two]; simp⟩

omit [Finite F] [CharP F 2] in
@[expose] def lowSL (c : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; c, 1], by rw [Matrix.det_fin_two]; simp⟩

omit [Finite F] in
@[expose] def jSL : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two]; simp [CharTwo.neg_eq]⟩

omit [Finite F] [CharP F 2] in
theorem rootMatrix_comm_long (σ : F ≃+* F) (c : F) :
    rootMatrix σ (1 : Fin 4) 0 c * rootMatrix σ (0 : Fin 4) 2 1 *
        rootMatrix σ (1 : Fin 4) 0 (-c) * rootMatrix σ (0 : Fin 4) 2 (-1) =
      longRootMatrix (1 : Fin 4) (c - σ c) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, longRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
      Matrix.one_apply, Fin.rev]; ring

omit [Finite F] in
theorem coe_weyl₁ (σ : F ≃+* F) :
    ((weyl₁ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blkS σ ((jSL : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨hs, -, h0, h1, h2, h3⟩ := tau₁_facts
  rw [weyl₁_eq, coe_permGL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blkS, jSL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.Perm.inv_def, hs, h0,
      h1, h2, h3]

theorem shortSL_sup_weyl₂_eq_SU (hb : 1 ≤ b) (hF : Nat.card F = (2 ^ b) ^ 2) :
    shortSL (unitaryInvolution F 2 b) ⊔ (shortSL (unitaryInvolution F 2 b)).map
        (MulAut.conj (weyl₂ : GL (Fin 4) F)).toMonoidHom = SU (unitaryInvolution F 2 b) 4 := by
  set σ := unitaryInvolution F 2 b with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 b F :=
    ⟨Nat.prime_two, hb, by rw [hF]; ring⟩
  set S := shortSL σ ⊔ (shortSL σ).map (MulAut.conj (weyl₂ : GL (Fin 4) F)).toMonoidHom
    with hSdef
  have hSU : S ≤ SU σ 4 := by
    refine sup_le (U4Lines.shortSL_le_SU σ hσ) ?_
    rintro _ ⟨x, hx, rfl⟩
    have hw : (weyl₂ : GL (Fin 4) F) ∈ SU σ 4 := permGL_mem_SU σ _ (by decide)
    exact (SU σ 4).mul_mem ((SU σ 4).mul_mem hw (U4Lines.shortSL_le_SU σ hσ hx))
      ((SU σ 4).inv_mem hw)
  apply le_antisymm hSU
  set R : Subgroup (SU σ 4) := S.subgroupOf (SU σ 4) with hR
  obtain ⟨hs₁, hr₁, -⟩ := tau₁_facts
  obtain ⟨hs₂, hr₂, h20, h21, h22, h23⟩ := tau₂_facts
  have hS₁ : ∀ (B : Matrix.SpecialLinearGroup (Fin 2) F) (x : SU σ 4),
      (((x : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) = blkS σ (B : Matrix (Fin 2) (Fin 2) F) →
      x ∈ R := by
    intro B x h
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left ⟨B, Units.ext ?_⟩)
    rw [coe_iotaS, h]
  have hS₂ : ∀ (B : Matrix.SpecialLinearGroup (Fin 2) F) (x : SU σ 4),
      (((x : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
        (blkS σ (B : Matrix (Fin 2) (Fin 2) F)).submatrix tau₂.symm tau₂.symm → x ∈ R := by
    intro B x h
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right ⟨iotaS σ B, ⟨B, rfl⟩, ?_⟩)
    apply Units.ext
    change ((weyl₂ * iotaS σ B * weyl₂⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = _
    rw [weyl₂_eq, coe_permGL_conj, coe_iotaS, h]
  have hconj : ∀ w y x : SU σ 4, w ∈ R → y ∈ R → w * y * w⁻¹ = x → x ∈ R := by
    rintro w y x hw hy rfl
    exact R.mul_mem (R.mul_mem hw hy) (R.inv_mem hw)
  have h01 : ∀ (c : F) (x : SU σ 4), (((x : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
      rootMatrix σ 0 1 c → x ∈ R := fun c x h =>
    hS₁ (upSL c) x (by rw [h, rootMatrix_01, blkB_eq_blkS]; rfl)
  have h10 : ∀ (c : F) (x : SU σ 4), (((x : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
      rootMatrix σ 1 0 c → x ∈ R := fun c x h =>
    hS₁ (lowSL c) x (by rw [h, rootMatrix_10, blkB_eq_blkS]; rfl)
  have h23' : ∀ (c : F) (x : SU σ 4), (((x : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
      rootMatrix σ 2 3 c → x ∈ R := fun c x h =>
    hS₁ (upSL (σ c)) x (by rw [h, rootMatrix_23 σ hσ, blkB_eq_blkS]; rfl)
  have h32 : ∀ (c : F) (x : SU σ 4), (((x : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
      rootMatrix σ 3 2 c → x ∈ R := fun c x h =>
    hS₁ (lowSL (σ c)) x (by rw [h, rootMatrix_32 σ hσ, blkB_eq_blkS]; rfl)
  have hW : ∀ (i j : Fin 4) (B : Matrix.SpecialLinearGroup (Fin 2) F) (c : F),
      rootMatrix σ i j c = blkS σ (B : Matrix (Fin 2) (Fin 2) F) →
      ∀ x : SU σ 4, (((x : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) =
        rootMatrix σ (tau₂ i) (tau₂ j) c → x ∈ R := by
    intro i j B c hB x h
    refine hS₂ B x ?_
    rw [h, ← hB, rootMatrix_submatrix σ tau₂ hr₂]
  have hfixc : ∀ c : Multiplicative (traceZero σ), σ ((c.toAdd : traceZero σ) : F) =
      ((c.toAdd : traceZero σ) : F) := by
    intro c
    have h1 := (mem_traceZero σ).1 c.toAdd.2
    rw [eq_neg_of_add_eq_zero_right h1, CharTwo.neg_eq]
  have hL1 : ∀ (h : (1 : Fin 4) ≠ Fin.rev 1) (c : Multiplicative (traceZero σ)),
      longRootHom σ h c ∈ R := by
    intro h c
    set e : F := ((c.toAdd : traceZero σ) : F)
    obtain ⟨d, hd⟩ := exists_add_unitaryInvolution_eq hF (hfixc c)
    have hij₁ : (1 : Fin 4) ≠ 0 := by decide
    have hij₂ : (0 : Fin 4) ≠ 2 := by decide
    have hr1 : (1 : Fin 4) ≠ Fin.rev 1 := by decide
    have hr0 : (0 : Fin 4) ≠ Fin.rev 0 := by decide
    have hr2 : (2 : Fin 4) ≠ Fin.rev 2 := by decide
    set x := rootHom σ hσ hij₁ hr1 hr0 (Multiplicative.ofAdd d) with hx
    set y := rootHom σ hσ hij₂ hr0 hr2 (Multiplicative.ofAdd 1) with hy
    have hxR : x ∈ R := h10 d x (by rw [hx, coe_rootHom]; rfl)
    have hyR : y ∈ R := hW 0 1 (upSL 1) 1 (by rw [rootMatrix_01, blkB_eq_blkS]; rfl) y
      (by rw [hy, coe_rootHom, h20, h21]; rfl)
    have hd' : d + σ d = e := hd
    have heq : longRootHom σ h c = x * y * x⁻¹ * y⁻¹ := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, coe_longRootHom, hx, hy, ← map_inv,
        coe_rootHom, toAdd_inv, toAdd_ofAdd]
      rw [rootMatrix_comm_long, CharTwo.sub_eq_add, hd']
    rw [heq]
    exact R.mul_mem (R.mul_mem (R.mul_mem hxR hyR) (R.inv_mem hxR)) (R.inv_mem hyR)
  have hw₁SU : (weyl₁ : GL (Fin 4) F) ∈ SU σ 4 := permGL_mem_SU σ _ (by decide)
  have hw₁R : (⟨weyl₁, hw₁SU⟩ : SU σ 4) ∈ R := hS₁ jSL _ (coe_weyl₁ σ)
  have hτ₃ : ∀ i, (tau₂ * tau₁ * tau₂⁻¹) (Fin.rev i) = Fin.rev ((tau₂ * tau₁ * tau₂⁻¹) i) := by
    decide
  have hw₃SU : (permGL (tau₂ * tau₁ * tau₂⁻¹) : GL (Fin 4) F) ∈ SU σ 4 :=
    permGL_mem_SU σ _ hτ₃
  have hw₃R : (⟨permGL (tau₂ * tau₁ * tau₂⁻¹), hw₃SU⟩ : SU σ 4) ∈ R := by
    refine hS₂ jSL _ ?_
    change ((permGL (tau₂ * tau₁ * tau₂⁻¹) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = _
    rw [map_mul, map_mul, map_inv, ← weyl₁_eq, ← coe_weyl₁ σ, ← coe_permGL_conj]
  have hlong : ∀ (τ : Equiv.Perm (Fin 4)) (hτ : ∀ i, τ (Fin.rev i) = Fin.rev (τ i)),
      (⟨permGL τ, permGL_mem_SU σ τ hτ⟩ : SU σ 4) ∈ R →
      ∀ (i : Fin 4) (hi : i ≠ Fin.rev i), τ 1 = i →
        ∀ c : Multiplicative (traceZero σ), longRootHom σ hi c ∈ R := by
    intro τ hτ hwR i hi hτi c
    refine hconj _ (longRootHom σ (by decide : (1 : Fin 4) ≠ Fin.rev 1) c) _ hwR
      (hL1 (by decide) c) ?_
    apply Subtype.ext
    apply Units.ext
    change ((permGL τ * _ * (permGL τ)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = _
    rw [coe_permGL_conj, coe_longRootHom, coe_longRootHom, longRootMatrix_submatrix τ hτ, hτi]
  have htop : R = ⊤ := by
    refine eq_top_of_rootElements_le (σ := σ) hσ ⟨1, one_ne_zero, ?_⟩
      (fun x hx => exists_add_unitaryInvolution_eq hF hx) (fun x hx => ?_) (by norm_num) R ?_ ?_
      ?_
    · rw [map_one]
      exact CharTwo.add_self_eq_zero 1
    · obtain ⟨l, hl⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_norm_eq hU
        (c := x) (by
          rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply,
            ← CFSG.LieType.BorelTits.unitaryInvolution_apply]
          exact hx)
      refine ⟨l, ?_⟩
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm,
        CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply,
        ← CFSG.LieType.BorelTits.unitaryInvolution_apply, mul_comm] at hl
      exact hl
    · intro i j hij hi hj hji c
      have hc := coe_rootHom σ hσ hij hi hj c
      fin_cases i <;> fin_cases j <;> simp [Fin.rev] at hij hi hj hji ⊢
      · exact h01 _ _ hc
      · exact hW 0 1 (upSL c.toAdd) c.toAdd (by rw [rootMatrix_01, blkB_eq_blkS]; rfl) _
          (by rw [hc, h20, h21]; rfl)
      · exact h10 _ _ hc
      · exact hW 2 3 (upSL (σ c.toAdd)) c.toAdd (by rw [rootMatrix_23 σ hσ, blkB_eq_blkS]; rfl)
          _ (by rw [hc, h22, h23]; rfl)
      · exact hW 1 0 (lowSL c.toAdd) c.toAdd (by rw [rootMatrix_10, blkB_eq_blkS]; rfl) _
          (by rw [hc, h20, h21]; rfl)
      · exact h23' _ _ hc
      · exact hW 3 2 (lowSL (σ c.toAdd)) c.toAdd (by rw [rootMatrix_32 σ hσ, blkB_eq_blkS]; rfl)
          _ (by rw [hc, h22, h23]; rfl)
      · exact h32 _ _ hc
    · intro i hi c
      fin_cases i <;> simp [Fin.rev] at hi ⊢
      · exact hlong tau₁ hr₁ hw₁R 0 _ (by decide) c
      · exact hL1 _ c
      · exact hlong (tau₁ * (tau₂ * tau₁ * tau₂⁻¹)) (by decide)
          (by
            have := R.mul_mem hw₁R hw₃R
            convert this using 1
            apply Subtype.ext
            change permGL (tau₁ * (tau₂ * tau₁ * tau₂⁻¹)) = permGL tau₁ * permGL _
            rw [map_mul])
          2 _ (by decide) c
      · exact hlong (tau₂ * tau₁ * tau₂⁻¹) hτ₃ hw₃R 3 _ (by decide) c
    · intro i k hi hik hk
      fin_cases k <;> simp [Fin.rev] at hk
  intro x hx
  have hmem : (⟨x, hx⟩ : SU σ 4) ∈ R := by rw [htop]; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

end Short

end CFSG.RankThree.PartTwo.Sec21.Item228InspProof
