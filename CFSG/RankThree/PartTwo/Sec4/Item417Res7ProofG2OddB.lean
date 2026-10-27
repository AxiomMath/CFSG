module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSplit
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofG2OddCommon

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley
  CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open scoped Matrix

namespace Res417Seven

@[expose] def blockThree {L : Type} [Field L] (B : Matrix (Fin 2) (Fin 2) L) (t u : L) :
    Matrix (Fin 3) (Fin 3) L :=
  !![t * B 0 0, t * B 0 1, 0; t * B 1 0, t * B 1 1, 0; 0, 0, u]

theorem blockThree_mul {L : Type} [Field L] (B B' : Matrix (Fin 2) (Fin 2) L) (t u t' u' : L) :
    blockThree B t u * blockThree B' t' u' = blockThree (B * B') (t * t') (u * u') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockThree, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two] <;> ring

theorem blockThree_one {L : Type} [Field L] :
    blockThree (1 : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockThree]

theorem det_blockThree {L : Type} [Field L] (B : Matrix (Fin 2) (Fin 2) L) (t u : L) :
    (blockThree B t u).det = t ^ 2 * B.det * u := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blockThree]
  ring

theorem conjTr_blockThree {L : Type} [Field L] (σ : L ≃+* L) (B : Matrix (Fin 2) (Fin 2) L)
    (t u : L) :
    CFSG.LieType.Universal.Unitary.conjTr σ (blockThree B t u) =
      blockThree (CFSG.LieType.Universal.Unitary.conjTr σ B) (σ t) (σ u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockThree, CFSG.LieType.Universal.Unitary.conjTr]

@[expose] noncomputable def blockThreeHom (L : Type) [Field L] :
    GL (Fin 2) L × Lˣ →* GL (Fin 3) L where
  toFun x := ⟨blockThree (x.1 : Matrix (Fin 2) (Fin 2) L) (x.2 : L) (((x.2⁻¹ : Lˣ) : L) ^ 2),
    blockThree ((x.1⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) ((x.2⁻¹ : Lˣ) : L)
      ((x.2 : L) ^ 2), by
      rw [blockThree_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, ← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_pow, blockThree_one], by
      rw [blockThree_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        one_pow, blockThree_one]⟩
  map_one' := Units.ext (by simp [blockThree_one])
  map_mul' x y := Units.ext (by
    change blockThree _ _ _ = blockThree _ _ _ * blockThree _ _ _
    rw [blockThree_mul]
    simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, mul_inv, mul_pow])

theorem blockThreeHom_mem_statedSU {L : Type} [Field L] {q : ℕ} (σ : L ≃+* L)
    (hσ : ∀ c, σ c = c ^ q) {B : GL (Fin 2) L} {t : Lˣ}
    (hB : CFSG.LieType.Universal.Unitary.conjTr σ (B : Matrix (Fin 2) (Fin 2) L) *
      (B : Matrix (Fin 2) (Fin 2) L) = 1) (hdet : (B : Matrix (Fin 2) (Fin 2) L).det = 1)
    (ht : σ (t : L) * t = 1) :
    blockThreeHom L (B, t) ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 q L := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · change (blockThree _ _ _).det = 1
    rw [det_blockThree, hdet, mul_one, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_pow]
  · have hmap : ∀ X : Matrix (Fin 3) (Fin 3) L, (X.map (· ^ q))ᵀ =
        CFSG.LieType.Universal.Unitary.conjTr σ X := fun X => by
      rw [CFSG.LieType.Universal.Unitary.conjTr]
      congr 1
      ext i j
      simp [hσ]
    rw [hmap]
    change CFSG.LieType.Universal.Unitary.conjTr σ (blockThree _ _ _) * blockThree _ _ _ = 1
    rw [conjTr_blockThree, blockThree_mul, hB, ht, map_pow, ← mul_pow]
    have hu : σ (((t⁻¹ : Lˣ) : L)) * ((t⁻¹ : Lˣ) : L) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, ht, inv_one]
    rw [hu, one_pow, blockThree_one]

theorem blockThreeHom_injective {L : Type} [Field L] [CharP L 2] :
    Function.Injective (blockThreeHom L) := by
  rintro ⟨B, t⟩ ⟨B', t'⟩ h
  have hm : blockThree (B : Matrix (Fin 2) (Fin 2) L) (t : L) (((t⁻¹ : Lˣ) : L) ^ 2) =
      blockThree (B' : Matrix (Fin 2) (Fin 2) L) (t' : L) (((t'⁻¹ : Lˣ) : L) ^ 2) :=
    congrArg (fun g : GL (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L)) h
  have h22 : ((t⁻¹ : Lˣ) : L) ^ 2 = ((t'⁻¹ : Lˣ) : L) ^ 2 := by
    have := congrFun (congrFun hm 2) 2
    simpa [blockThree] using this
  have htt : t = t' := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have hx : (((t⁻¹ : Lˣ) : L) - ((t'⁻¹ : Lˣ) : L)) ^ 2 = 0 := by
      linear_combination h22 + (((t'⁻¹ : Lˣ) : L) ^ 2 - ((t⁻¹ : Lˣ) : L) * ((t'⁻¹ : Lˣ) : L)) * h2
    have h3 : ((t⁻¹ : Lˣ) : L) = ((t'⁻¹ : Lˣ) : L) :=
      sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hx)
    exact inv_injective (Units.ext h3)
  subst htt
  refine Prod.ext (Units.ext ?_) rfl
  ext i j
  fin_cases i <;> fin_cases j
  · have := congrFun (congrFun hm 0) 0
    simpa [blockThree] using this
  · have := congrFun (congrFun hm 0) 1
    simpa [blockThree] using this
  · have := congrFun (congrFun hm 1) 0
    simpa [blockThree] using this
  · have := congrFun (congrFun hm 1) 1
    simpa [blockThree] using this

theorem conjTr_conj_mul_self {L : Type} [Field L] {n : ℕ} (σ : L ≃+* L)
    {G : Matrix (Fin n) (Fin n) L} {P A : GL (Fin n) L}
    (hP : CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L) * G *
      (P : Matrix (Fin n) (Fin n) L) = 1)
    (hA : CFSG.LieType.Universal.Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) L) * G *
      (A : Matrix (Fin n) (Fin n) L) = G) :
    CFSG.LieType.Universal.Unitary.conjTr σ ((P⁻¹ * A * P : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) * ((P⁻¹ * A * P : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      1 := by
  have hG : G = CFSG.LieType.Universal.Unitary.conjTr σ
      ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    have h1 : CFSG.LieType.Universal.Unitary.conjTr σ
        ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← CFSG.LieType.Universal.Unitary.conjTr_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, CFSG.LieType.Universal.Unitary.conjTr_one]
    calc G = (CFSG.LieType.Universal.Unitary.conjTr σ
          ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L)) * G *
          ((P : Matrix (Fin n) (Fin n) L) * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
          := by
          rw [h1, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_one]
      _ = CFSG.LieType.Universal.Unitary.conjTr σ
          ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L) * G *
            (P : Matrix (Fin n) (Fin n) L)) *
          ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]
  rw [Units.val_mul, Units.val_mul, CFSG.LieType.Universal.Unitary.conjTr_mul,
    CFSG.LieType.Universal.Unitary.conjTr_mul]
  calc CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L) *
        (CFSG.LieType.Universal.Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) L) *
          CFSG.LieType.Universal.Unitary.conjTr σ
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
        (((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (A : Matrix (Fin n) (Fin n) L) *
          (P : Matrix (Fin n) (Fin n) L)) =
      CFSG.LieType.Universal.Unitary.conjTr σ (P : Matrix (Fin n) (Fin n) L) *
        (CFSG.LieType.Universal.Unitary.conjTr σ (A : Matrix (Fin n) (Fin n) L) *
          (CFSG.LieType.Universal.Unitary.conjTr σ
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          (A : Matrix (Fin n) (Fin n) L)) * (P : Matrix (Fin n) (Fin n) L) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [← hG, hA, hP]

section ThreeB

variable (L : Type) [Field L]

@[expose] noncomputable def g2TorusA : Lˣ →* ModGL .G2 L :=
  (rootDiagUnitHom .G2 L).comp (MonoidHom.mulSingle (fun _ : Fin Tag.G2.rank => Lˣ) g2ia)

variable {L}

theorem g2TorusA_commute (A : SL2 L) (t : Lˣ) :
    simpleRootSL2 .G2 L g2ir A * g2TorusA L t = g2TorusA L t * simpleRootSL2 .G2 L g2ir A := by
  have hmem : simpleRootSL2 .G2 L g2ir A ∈ rootSpan .G2 L {g2r, -g2r} := by
    rw [rootSpan_pair, g2r_eq_single, ← range_simpleRootSL2_g2]
    exact ⟨A, rfl⟩
  have hS : ({g2r, -g2r} : Set (Fin Tag.G2.rank → ℤ)) ⊆
      rootCharKernel (Pi.mulSingle g2ia t) := by
    rintro α (rfl | rfl)
    · exact ⟨isRoot_g2r, by rw [rootChar_mulSingle_eq_zpow, g2r_ia, zpow_zero]⟩
    · refine ⟨IsRoot.neg isRoot_g2r, ?_⟩
      rw [rootChar_mulSingle_eq_zpow, Pi.neg_apply, g2r_ia, neg_zero, zpow_zero]
  have h := Subgroup.mem_centralizer_singleton_iff.mp (rootSpan_le_centralizer _ hS hmem)
  exact h

variable (L) in
@[expose] noncomputable def kappaB : SL2 L × Lˣ →* ModGL .G2 L :=
  MonoidHom.noncommCoprod (simpleRootSL2 .G2 L g2ir) (g2TorusA L) fun A t =>
    g2TorusA_commute A t

theorem kappaB_apply (A : SL2 L) (t : Lˣ) :
    kappaB L (A, t) = simpleRootSL2 .G2 L g2ir A * rootDiagUnit .G2 (Pi.mulSingle g2ia t) :=
  rfl

theorem sl2_eq_one_of_commute [CharP L 2] {A : SL2 L} (hu : A * uSL 1 = uSL 1 * A)
    (hv : A * vSL 1 = vSL 1 * A) : A = 1 := by
  have hu' := congrArg (fun M : SL2 L => (M : Matrix (Fin 2) (Fin 2) L)) hu
  have hv' := congrArg (fun M : SL2 L => (M : Matrix (Fin 2) (Fin 2) L)) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hu' hv'
  have e := fun i j => congrFun (congrFun hu' i) j
  have e' := fun i j => congrFun (congrFun hv' i) j
  simp only [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e e'
  have e00 := e 0 0
  have e01 := e 0 1
  have f00 := e' 0 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, one_mul, zero_mul,
    add_zero] at e00 e01 f00
  have hc : (A : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by linear_combination -e00
  have hb : (A : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by linear_combination f00
  have had : (A : Matrix (Fin 2) (Fin 2) L) 0 0 = (A : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    linear_combination e01
  have hdet := A.2
  rw [Matrix.det_fin_two, hb, hc, mul_zero, sub_zero, ← had] at hdet
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have ha : (A : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
    have h : ((A : Matrix (Fin 2) (Fin 2) L) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hdet + (1 - (A : Matrix (Fin 2) (Fin 2) L) 0 0) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, ← had]

theorem kappaB_injective [CharP L 2] : Function.Injective (kappaB L) := by
  refine (MonoidHom.noncommCoprod_injective _ _ _).mpr ⟨simpleRootSL2_injective_g2 g2ir,
    fun t t' h => Pi.mulSingle_injective (M := fun _ : Fin Tag.G2.rank => Lˣ) g2ia
      (rootDiagUnit_injective h), ?_⟩
  rw [Subgroup.disjoint_def]
  rintro x ⟨A, rfl⟩ ⟨t, ht⟩
  have hcomm : ∀ B : SL2 L, A * B = B * A := fun B => simpleRootSL2_injective_g2 g2ir (by
    rw [map_mul, map_mul, ← ht]
    exact (g2TorusA_commute B t).symm)
  rw [sl2_eq_one_of_commute (hcomm _) (hcomm _), map_one]

theorem torusGroup_le_range_kappaB [Finite L] [CharP L 2] :
    torusGroup .G2 L ≤ (kappaB L).range := by
  intro h hh
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hodd : Odd (Nat.card L - 1) := CFSG.LocalAnalysis.EvenBN.G2.card_sub_one_odd
  have hpos : 0 < Nat.card L := Nat.card_pos
  have heven : 2 * (Nat.card L / 2) = Nat.card L := by
    obtain ⟨k, hk⟩ := hodd
    omega
  set t := c g2ir ^ (Nat.card L / 2) with ht
  have ht2 : t ^ 2 = c g2ir := by
    rw [ht, ← pow_mul, mul_comm, heven]
    have h1 : c g2ir ^ (Nat.card L - 1) = 1 := by
      rw [← Nat.card_units]
      exact pow_card_eq_one'
    calc c g2ir ^ Nat.card L = c g2ir ^ (Nat.card L - 1) * c g2ir := by
          rw [← pow_succ, Nat.sub_add_cancel hpos]
      _ = c g2ir := by rw [h1, one_mul]
  refine ⟨(HSL t, c g2ia * t ^ 3), ?_⟩
  rw [kappaB_apply, simpleRootSL2_HSL, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext j
  have c0 : Tag.G2.cartan g2ir g2ia = -3 := by decide
  have c1 : Tag.G2.cartan g2ir g2ir = 2 := by decide
  have hne : g2ir ≠ g2ia := by decide
  rcases fin_G2_cases j with rfl | rfl
  · simp only [Pi.mul_apply, c0, Pi.mulSingle_eq_same]
    rw [mul_left_comm, zpow_neg, zpow_ofNat, inv_mul_cancel, mul_one]
  · simp only [Pi.mul_apply, c1, Pi.mulSingle_eq_of_ne hne, mul_one]
    rw [zpow_ofNat, ht2]

theorem toralCentralizer_threeB_le_range_kappaB [Finite L] [CharP L 2] {ζ : Lˣ}
    (hζ : orderOf ζ = 3) :
    toralCentralizer .G2 L (Pi.mulSingle g2ia ζ) ≤ (kappaB L).range := by
  rw [toralCentralizer_eq_toralRootGroup_of_le (stabilizer_le_threeB hζ), toralRootGroup,
    rootCharKernel_threeB hζ, rootSpan_pair, g2r_eq_single, ← range_simpleRootSL2_g2]
  refine sup_le torusGroup_le_range_kappaB ?_
  rintro _ ⟨A, rfl⟩
  refine ⟨(A, 1), ?_⟩
  rw [kappaB_apply, Pi.mulSingle_one, rootDiagUnit_one, mul_one]

variable (L) in
@[expose] noncomputable def twistB (σ : L →+* L) : SL2 L × Lˣ →* SL2 L × Lˣ :=
  MonoidHom.prodMap ((MulAut.conj (WSL : SL2 L)).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map σ)) ((invMonoidHom : Lˣ →* Lˣ).comp (Units.map (σ : L →* L)))

theorem wSL_conj_uSL_vSL [CharP L 2] (σ : L →+* L) (x : L) :
    (WSL : SL2 L) * uSL x * WSL⁻¹ = vSL x ∧ (WSL : SL2 L) * vSL x * WSL⁻¹ = uSL x ∧
      Matrix.SpecialLinearGroup.map σ (uSL x) = uSL (σ x) ∧
      Matrix.SpecialLinearGroup.map σ (vSL x) = vSL (σ x) := by
  have hneg : -x = x := CharTwo.neg_eq x
  have hWu : (WSL : SL2 L) * uSL x = vSL x * WSL := by
    apply Subtype.ext
    change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) L) * !![1, x; 0, 1] =
      !![1, 0; x, 1] * !![0, 1; -1, 0]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hneg]
  have hWv : (WSL : SL2 L) * vSL x = uSL x * WSL := by
    apply Subtype.ext
    change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) L) * !![1, 0; x, 1] =
      !![1, x; 0, 1] * !![0, 1; -1, 0]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hneg]
  refine ⟨by rw [mul_inv_eq_iff_eq_mul, hWu], by rw [mul_inv_eq_iff_eq_mul, hWv],
    Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uSL]
  · rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vSL]

theorem kappaB_twist [CharP L 2] (σ : L →+* L) (x : SL2 L × Lˣ) :
    kappaB L (twistB L σ x) =
      canonicalRep (coxeterSystem .G2) L g2LongestWeyl * baseChangeGL σ (kappaB L x) *
        (canonicalRep (coxeterSystem .G2) L g2LongestWeyl)⁻¹ := by
  set n₀ := canonicalRep (coxeterSystem .G2) L g2LongestWeyl with hn₀
  set F : ModGL .G2 L →* ModGL .G2 L :=
    (MulAut.conj n₀).toMonoidHom.comp (baseChangeGL σ) with hF
  have hFapp : ∀ y, F y = n₀ * baseChangeGL σ y * n₀⁻¹ := fun y => rfl
  have hSL : ∀ A : SL2 L, simpleRootSL2 .G2 L g2ir (WSL * Matrix.SpecialLinearGroup.map σ A *
      WSL⁻¹) = F (simpleRootSL2 .G2 L g2ir A) := by
    have key : (simpleRootSL2 .G2 L g2ir).comp ((MulAut.conj (WSL : SL2 L)).toMonoidHom.comp
        (Matrix.SpecialLinearGroup.map σ)) = F.comp (simpleRootSL2 .G2 L g2ir) := by
      have htop : Subgroup.closure (Set.range (uSL (K := L)) ∪ Set.range vSL) = ⊤ := by
        have h := CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := L)
        have e1 : CFSG.LocalAnalysis.ComponentInitial.sl2Upper L = uSL :=
          funext fun c => Subtype.ext rfl
        have e2 : CFSG.LocalAnalysis.ComponentInitial.sl2Lower L = vSL :=
          funext fun c => Subtype.ext rfl
        rwa [e1, e2] at h
      refine MonoidHom.eq_of_eqOn_dense htop ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · obtain ⟨-, -, h3, -⟩ := wSL_conj_uSL_vSL σ c
        obtain ⟨h1, -, -, -⟩ := wSL_conj_uSL_vSL σ (σ c)
        simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        rw [h3, h1, hFapp, simpleRootSL2_vSL, simpleRootSL2_uSL, ← pinnedX_single,
          ← pinnedX_neg_single, baseChangeGL_pinnedX, g2_longest_conj_pinnedX
            (isRoot_single .G2 g2ir)]
      · obtain ⟨-, -, -, h4⟩ := wSL_conj_uSL_vSL σ c
        obtain ⟨-, h2, -, -⟩ := wSL_conj_uSL_vSL σ (σ c)
        simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        rw [h4, h2, hFapp, simpleRootSL2_vSL, simpleRootSL2_uSL, ← pinnedX_single,
          ← pinnedX_neg_single, baseChangeGL_pinnedX, g2_longest_conj_pinnedX
            (IsRoot.neg (isRoot_single .G2 g2ir)), neg_neg]
    intro A
    exact DFunLike.congr_fun key A
  have hT : ∀ t : Lˣ, rootDiagUnit .G2 (Pi.mulSingle g2ia (Units.map (σ : L →* L) t)⁻¹) =
      F (rootDiagUnit .G2 (Pi.mulSingle g2ia t)) := by
    intro t
    rw [hFapp, baseChangeGL_rootDiagUnit, g2_longest_conj_rootDiagUnit]
    congr 1
    funext j
    by_cases hj : j = g2ia
    · subst hj
      simp only [Pi.mulSingle_eq_same, Pi.inv_apply]
      rfl
    · simp only [Pi.mulSingle_eq_of_ne hj, Pi.inv_apply, inv_one, map_one]
  obtain ⟨A, t⟩ := x
  have hx : ((A, t) : SL2 L × Lˣ) = (A, 1) * (1, t) := by simp
  have h1 : kappaB L (twistB L σ (A, 1)) = F (kappaB L (A, 1)) := by
    change kappaB L (WSL * Matrix.SpecialLinearGroup.map σ A * WSL⁻¹,
      (Units.map (σ : L →* L) 1)⁻¹) = _
    rw [kappaB_apply, kappaB_apply, map_one, inv_one, Pi.mulSingle_one, rootDiagUnit_one,
      mul_one, mul_one, hSL]
  have h2 : kappaB L (twistB L σ (1, t)) = F (kappaB L (1, t)) := by
    change kappaB L (WSL * Matrix.SpecialLinearGroup.map σ 1 * WSL⁻¹,
      (Units.map (σ : L →* L) t)⁻¹) = _
    simp only [kappaB_apply, map_one, mul_one, mul_inv_cancel, one_mul]
    exact hT t
  rw [hx, map_mul (twistB L σ), map_mul (kappaB L) (twistB L σ (A, 1)), h1, h2, ← map_mul F,
    ← map_mul (kappaB L)]
  exact hFapp _

theorem transpose_mul_wSL_mul (X : Matrix (Fin 2) (Fin 2) L) :
    Xᵀ * ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) * X =
      X.det • ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) := by
  change Xᵀ * !![0, 1; -1, 0] * X = X.det • !![0, 1; -1, 0]
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem wSL_facts [CharP L 2] (σ : L →+* L) :
    (((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L))ᵀ = ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) ∧
      (WSL : SL2 L) * WSL = 1 ∧ Matrix.SpecialLinearGroup.map σ (WSL : SL2 L) = WSL := by
  have hneg : (-1 : L) = 1 := CharTwo.neg_eq 1
  refine ⟨?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) L)ᵀ = !![0, 1; -1, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hneg]
  · change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) L) * !![0, 1; -1, 0] = 1
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hneg]
  · rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [WSL]

theorem conjTr_threeB_form [CharP L 2] (σ : L ≃+* L) {A₀ : SL2 L}
    (hcoc : A₀ * (WSL * Matrix.SpecialLinearGroup.map (σ : L →+* L) A₀ * WSL⁻¹) = 1) :
    CFSG.LieType.Universal.Unitary.conjTr σ
        (((A₀ * WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L)ᵀ *
          ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L)) =
      ((A₀ * WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L)ᵀ *
        ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) := by
  obtain ⟨hWt, hW2, hσW⟩ := wSL_facts (L := L) (σ : L →+* L)
  have hWinv : (WSL : SL2 L)⁻¹ = WSL := inv_eq_of_mul_eq_one_right hW2
  set M₀ : SL2 L := A₀ * WSL with hM₀
  have hMσ : Matrix.SpecialLinearGroup.map (σ : L →+* L) M₀ = M₀⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [hM₀, map_mul, hσW]
    calc A₀ * WSL * (Matrix.SpecialLinearGroup.map (σ : L →+* L) A₀ * WSL) =
        A₀ * (WSL * Matrix.SpecialLinearGroup.map (σ : L →+* L) A₀ * WSL⁻¹) := by
          rw [hWinv]; group
      _ = 1 := hcoc
  have hMW : (M₀ : Matrix (Fin 2) (Fin 2) L)ᵀ * ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) *
      (M₀ : Matrix (Fin 2) (Fin 2) L) = ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) := by
    rw [transpose_mul_wSL_mul, M₀.2, one_smul]
  have hMM : (M₀ : Matrix (Fin 2) (Fin 2) L) * ((M₀⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [CFSG.LieType.Universal.Unitary.conjTr, Matrix.map_mul, Matrix.transpose_mul,
    Matrix.transpose_map, Matrix.transpose_transpose]
  have h1 : (((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L).map σ)ᵀ =
      ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) := by
    rw [← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply,
      ← Matrix.SpecialLinearGroup.map_apply_coe, hσW, hWt]
  have h2 : (M₀ : Matrix (Fin 2) (Fin 2) L).map σ =
      ((M₀⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) := by
    rw [← RingEquiv.coe_toRingHom, ← RingHom.mapMatrix_apply,
      ← Matrix.SpecialLinearGroup.map_apply_coe, hMσ]
  rw [h1, h2]
  calc ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) * ((M₀⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
      (M₀ : Matrix (Fin 2) (Fin 2) L)ᵀ * ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) *
        ((M₀ : Matrix (Fin 2) (Fin 2) L) * ((M₀⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L)) := by
        rw [← Matrix.mul_assoc, hMW]
    _ = _ := by rw [hMM, Matrix.mul_one]

theorem conjTr_threeB_fixed (σ : L ≃+* L) {A₀ A : SL2 L}
    (hfix : A₀ * (WSL * Matrix.SpecialLinearGroup.map (σ : L →+* L) A * WSL⁻¹) * A₀⁻¹ = A) :
    CFSG.LieType.Universal.Unitary.conjTr σ (A : Matrix (Fin 2) (Fin 2) L) *
        (((A₀ * WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L)ᵀ *
          ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L)) * (A : Matrix (Fin 2) (Fin 2) L) =
      ((A₀ * WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L)ᵀ *
        ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) := by
  set M₀ : SL2 L := A₀ * WSL with hM₀
  have hσA : Matrix.SpecialLinearGroup.map (σ : L →+* L) A = M₀⁻¹ * A * M₀ := by
    have h1 : M₀ * Matrix.SpecialLinearGroup.map (σ : L →+* L) A * M₀⁻¹ = A := by
      rw [hM₀]
      calc A₀ * WSL * Matrix.SpecialLinearGroup.map (σ : L →+* L) A * (A₀ * WSL)⁻¹ =
          A₀ * (WSL * Matrix.SpecialLinearGroup.map (σ : L →+* L) A * WSL⁻¹) * A₀⁻¹ := by group
        _ = A := hfix
    calc Matrix.SpecialLinearGroup.map (σ : L →+* L) A =
        M₀⁻¹ * (M₀ * Matrix.SpecialLinearGroup.map (σ : L →+* L) A * M₀⁻¹) * M₀ := by group
      _ = M₀⁻¹ * A * M₀ := by rw [h1]
  have hc : CFSG.LieType.Universal.Unitary.conjTr σ (A : Matrix (Fin 2) (Fin 2) L) =
      ((M₀⁻¹ * A * M₀ : SL2 L) : Matrix (Fin 2) (Fin 2) L)ᵀ := by
    rw [CFSG.LieType.Universal.Unitary.conjTr, ← hσA, Matrix.SpecialLinearGroup.map_apply_coe]
    rfl
  have hMM : ((M₀⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L)ᵀ *
      (M₀ : Matrix (Fin 2) (Fin 2) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  rw [hc, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.transpose_mul, Matrix.transpose_mul]
  calc (M₀ : Matrix (Fin 2) (Fin 2) L)ᵀ * ((A : Matrix (Fin 2) (Fin 2) L)ᵀ *
        ((M₀⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L)ᵀ) *
        ((M₀ : Matrix (Fin 2) (Fin 2) L)ᵀ * ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L)) *
        (A : Matrix (Fin 2) (Fin 2) L) =
      (M₀ : Matrix (Fin 2) (Fin 2) L)ᵀ * ((A : Matrix (Fin 2) (Fin 2) L)ᵀ *
        (((M₀⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L)ᵀ * (M₀ : Matrix (Fin 2) (Fin 2) L)ᵀ) *
        ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) * (A : Matrix (Fin 2) (Fin 2) L)) := by
        simp only [Matrix.mul_assoc]
    _ = (M₀ : Matrix (Fin 2) (Fin 2) L)ᵀ * ((A : Matrix (Fin 2) (Fin 2) L)ᵀ *
        ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L) * (A : Matrix (Fin 2) (Fin 2) L)) := by
        rw [hMM, Matrix.mul_one]
    _ = _ := by rw [transpose_mul_wSL_mul, A.2, one_smul]

theorem exists_su3_of_threeB [Finite L] [CharP L 2] {f : ℕ} (hL : Nat.card L = (2 ^ f) ^ 2)
    {G : Type*} [Group G] (β : G →* adjointGroup .G2 L) (hβ : Function.Injective β)
    (hβσ : ∀ x, haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      baseChangeGL (CFSG.LieType.BorelTits.unitaryInvolution L 2 f : L →+* L)
        (β x : ModGL .G2 L) = β x)
    {e : G} {y : ModGL .G2 L} (hy : y ∈ adjointGroup .G2 L) {ζ : Lˣ} (hζ : orderOf ζ = 3)
    (hζq : (ζ : L) ^ (2 ^ f) = ((ζ⁻¹ : Lˣ) : L))
    (he : (β e : ModGL .G2 L) = y * rootDiagUnit .G2 (Pi.mulSingle g2ia ζ) * y⁻¹) :
    ∃ ι : Subgroup.centralizer ({e} : Set G) →* GL (Fin 3) L, Function.Injective ι ∧
      ∀ x, ι x ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := CFSG.LieType.BorelTits.unitaryInvolution L 2 f with hσdef
  have hσapp : ∀ c, σ c = c ^ (2 ^ f) := fun c =>
    CFSG.LieType.BorelTits.unitaryInvolution_apply L 2 f c
  have hσσ : ∀ c, (σ : L →+* L) ((σ : L →+* L) c) = c := fun c =>
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hL c
  set s := baseChangeGL (τ := .G2) (σ : L →+* L) with hsdef
  have hss : ∀ g, s (s g) = g := fun g => baseChangeGL_involutive hσσ g
  set n₀ := canonicalRep (coxeterSystem .G2) L g2LongestWeyl with hn₀
  have hn : s n₀ = n₀ := baseChangeGL_g2_longest _
  have hn2 : n₀ * n₀ = 1 := g2_longest_mul_self
  have hn₀C : n₀ ∈ adjointGroup .G2 L := canonicalRep_mem_adjointGroup _ L _
  set d := rootDiagUnit .G2 (Pi.mulSingle g2ia ζ) with hddef
  have hd : n₀ * d * n₀⁻¹ = s d := by
    rw [hddef, g2_longest_conj_rootDiagUnit, hsdef,
      baseChangeGL_rootDiagUnit_mulSingle (by rw [RingHom.coe_coe, hσapp]; exact hζq)]
  have hE : s (y * d * y⁻¹) = y * d * y⁻¹ := by rw [← he]; exact hβσ e
  obtain ⟨hc1, hc2, hc3⟩ := descent_of_fixed s hss hn hn2 hd hE
  set c := y⁻¹ * s y * n₀⁻¹ with hcdef
  have hκinj : Function.Injective (kappaB L) := kappaB_injective
  have hcen : ∀ w : ModGL .G2 L, w ∈ adjointGroup .G2 L → w * d = d * w →
      w ∈ (kappaB L).range := by
    intro w hw hwd
    refine toralCentralizer_threeB_le_range_kappaB hζ (mem_toralCentralizer.2 ⟨hw, ?_⟩)
    rw [← hwd, mul_inv_cancel_right]
  have hsC : ∀ g, g ∈ adjointGroup .G2 L → s g ∈ adjointGroup .G2 L := fun g hg =>
    baseChangeGL_mem_adjointGroup_G2 _ hg
  have hcC : c ∈ adjointGroup .G2 L :=
    mul_mem (mul_mem (inv_mem hy) (hsC y hy)) (inv_mem hn₀C)
  obtain ⟨⟨A₀, t₀⟩, hA₀⟩ := hcen c hcC hc1
  have htw : ∀ x, kappaB L (twistB L (σ : L →+* L) x) = n₀ * s (kappaB L x) * n₀⁻¹ := fun x =>
    kappaB_twist (σ : L →+* L) x
  have hcoc : (A₀, t₀) * twistB L (σ : L →+* L) (A₀, t₀) = 1 := by
    apply hκinj
    rw [map_mul, htw, hA₀, map_one]
    exact hc2
  have hcoc1 : A₀ * (WSL * Matrix.SpecialLinearGroup.map (σ : L →+* L) A₀ * WSL⁻¹) = 1 :=
    congrArg Prod.fst hcoc
  have hherm := conjTr_threeB_form σ hcoc1
  have hdet : (((A₀ * WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L)ᵀ *
      ((WSL : SL2 L) : Matrix (Fin 2) (Fin 2) L)).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe,
      Matrix.SpecialLinearGroup.det_coe, one_mul]
    exact one_ne_zero
  obtain ⟨P, hP⟩ := CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one hL hherm hdet
  set j : Subgroup.centralizer ({e} : Set G) →* ModGL .G2 L :=
    (MulAut.conj y⁻¹).toMonoidHom.comp
      ((adjointGroup .G2 L).subtype.comp (β.comp (Subgroup.centralizer ({e} : Set G)).subtype))
    with hjdef
  have hjapp : ∀ x, j x = y⁻¹ * (β x : ModGL .G2 L) * y := fun x => by
    simp [hjdef]
  have hjinj : Function.Injective j := by
    intro x x' h
    rw [hjapp, hjapp] at h
    exact Subtype.ext (hβ (Subtype.ext (by simpa using h)))
  have hjfix : ∀ x : Subgroup.centralizer ({e} : Set G),
      s (β x : ModGL .G2 L) = β x ∧ (β x : ModGL .G2 L) * (y * d * y⁻¹) =
        (y * d * y⁻¹) * β x := by
    intro x
    refine ⟨hβσ x, ?_⟩
    rw [← he, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_singleton_iff.mp x.2)]
  have hjmem : ∀ x, j x ∈ (kappaB L).range := by
    intro x
    obtain ⟨hx1, hx2⟩ := hjfix x
    rw [hjapp]
    refine hcen _ ?_ (hc3 _ hx1 hx2).1
    exact mul_mem (mul_mem (inv_mem hy) (β x).2) hy
  set j' : Subgroup.centralizer ({e} : Set G) →* (kappaB L).range := j.codRestrict _ hjmem
    with hj'
  set eκ := MonoidHom.ofInjective hκinj with heκ
  set k : Subgroup.centralizer ({e} : Set G) →* SL2 L × Lˣ := eκ.symm.toMonoidHom.comp j'
    with hkdef
  have hk : ∀ x, kappaB L (k x) = j x := fun x => by
    have h1 := congrArg Subtype.val (eκ.apply_symm_apply (j' x))
    rw [heκ, MonoidHom.ofInjective_apply] at h1
    exact h1
  have hkinj : Function.Injective k := fun x x' h => hjinj (by rw [← hk, ← hk, h])
  have hfixk : ∀ x, (A₀, t₀) * twistB L (σ : L →+* L) (k x) * (A₀, t₀)⁻¹ = k x := by
    intro x
    obtain ⟨hx1, hx2⟩ := hjfix x
    have hfix := (hc3 _ hx1 hx2).2
    rw [← hjapp, ← hk, ← hA₀, ← htw] at hfix
    apply hκinj
    rw [map_mul, map_mul, map_inv]
    exact hfix
  set Ψ : SL2 L × Lˣ →* GL (Fin 2) L × Lˣ :=
    MonoidHom.prodMap ((MulAut.conj P⁻¹).toMonoidHom.comp Matrix.SpecialLinearGroup.toGL)
      (MonoidHom.id _) with hΨ
  have hΨinj : Function.Injective Ψ := by
    rintro ⟨A, t⟩ ⟨A', t'⟩ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [hΨ, MonoidHom.coe_prodMap, Prod.map_apply, MonoidHom.coe_comp,
      Function.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply] at h1 h2
    exact Prod.ext (Matrix.SpecialLinearGroup.toGL_injective ((MulAut.conj P⁻¹).injective h1)) h2
  refine ⟨(blockThreeHom L).comp (Ψ.comp k),
    blockThreeHom_injective.comp (hΨinj.comp hkinj), fun x => ?_⟩
  rcases hkx : k x with ⟨A, t⟩
  have hfx := hfixk x
  rw [hkx] at hfx
  have hf1 : A₀ * (WSL * Matrix.SpecialLinearGroup.map (σ : L →+* L) A * WSL⁻¹) * A₀⁻¹ = A :=
    congrArg Prod.fst hfx
  have hf2 : t₀ * (Units.map (σ : L →* L) t)⁻¹ * t₀⁻¹ = t := congrArg Prod.snd hfx
  have ht : σ (t : L) * t = 1 := by
    have h0 : t₀ * (Units.map (σ : L →* L) t)⁻¹ * t₀⁻¹ = (Units.map (σ : L →* L) t)⁻¹ := by
      rw [mul_comm t₀, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : (Units.map (σ : L →* L) t)⁻¹ = t := h0.symm.trans hf2
    have h2 : Units.map (σ : L →* L) t * t = 1 := by
      calc Units.map (σ : L →* L) t * t =
          Units.map (σ : L →* L) t * (Units.map (σ : L →* L) t)⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel _
    exact congrArg Units.val h2
  have hu := conjTr_threeB_fixed σ hf1
  have hB := conjTr_conj_mul_self (A := Matrix.SpecialLinearGroup.toGL A) σ hP hu
  have hBdet : ((P⁻¹ * Matrix.SpecialLinearGroup.toGL A * P : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L).det = 1 := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
    change _ * (A : Matrix (Fin 2) (Fin 2) L).det * _ = 1
    rw [A.2, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one]
  have hmem := blockThreeHom_mem_statedSU σ hσapp hB hBdet ht
  simpa [hΨ, hkx, MulAut.conj_apply] using hmem

end ThreeB

end Res417Seven

end CFSG.RankThree.PartTwo.Sec4
