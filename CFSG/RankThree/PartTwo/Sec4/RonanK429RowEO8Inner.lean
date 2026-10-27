module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEBlock
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowESp6
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVO8p
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeD

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.Assembly.RankThreeEven (projOmegaPlus)
open CFSG.Open (StatedOmega StatedQuadPlus StatedScalars StatedProj)
open Matrix
open scoped Matrix

namespace O8

abbrev ι8 : Type := Fin 4 ⊕ Fin 4

abbrev Q8 : (ι8 → ZMod 2) → ZMod 2 := StatedQuadPlus 4 (ZMod 2)

abbrev OM : Type := ↥(StatedOmega Q8)

@[expose] def gM : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1, 1, 1, 0; 1, 0, 1, 0; 1, 0, 0, 1; 0, 0, 1, 0]
@[expose] def gMi : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0, 1, 0, 1; 1, 1, 0, 0; 0, 0, 0, 1; 0, 1, 1, 1]
@[expose] def hM : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0, 1, 0, 0; 1, 0, 1, 0; 1, 0, 1, 1; 0, 0, 1, 1]
@[expose] def hMi : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0, 0, 1, 1; 1, 0, 0, 0; 0, 1, 1, 1; 0, 1, 1, 0]
@[expose] def bpM : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]
@[expose] def bpMi : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1]

@[expose] def levi (A Ai : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix ι8 ι8 (ZMod 2) :=
  fromBlocks A 0 0 Aiᵀ

theorem levi_g_mul : levi gM gMi * levi gMi gM = 1 := by decide +kernel
theorem levi_g_mul' : levi gMi gM * levi gM gMi = 1 := by decide +kernel
theorem levi_h_mul : levi hM hMi * levi hMi hM = 1 := by decide +kernel
theorem levi_h_mul' : levi hMi hM * levi hM hMi = 1 := by decide +kernel

theorem levi_g_isom : ∀ v : ι8 → ZMod 2, Q8 (levi gM gMi *ᵥ v) = Q8 v := by decide +kernel

theorem levi_h_isom : ∀ v : ι8 → ZMod 2, Q8 (levi hM hMi *ᵥ v) = Q8 v := by decide +kernel

@[expose] def lg : GL ι8 (ZMod 2) := ⟨levi gM gMi, levi gMi gM, levi_g_mul, levi_g_mul'⟩

@[expose] def lh : GL ι8 (ZMod 2) := ⟨levi hM hMi, levi hMi hM, levi_h_mul, levi_h_mul'⟩

@[expose] def yM : Matrix ι8 ι8 (ZMod 2) := levi bpM bpMi

theorem commutator_levi : levi gM gMi * levi hM hMi * levi gMi gM * levi hMi hM = yM := by
  decide +kernel

theorem lg_mem : lg ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure levi_g_isom

theorem lh_mem : lh ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure levi_h_isom

@[expose] def y0 : OM :=
  ⟨lg * lh * lg⁻¹ * lh⁻¹, by
    unfold StatedOmega
    have h := Subgroup.commutator_mem_commutator lg_mem lh_mem
    rwa [commutatorElement_def] at h⟩

@[expose] def matO : OM →* Matrix ι8 ι8 (ZMod 2) :=
  (Units.coeHom (Matrix ι8 ι8 (ZMod 2))).comp (StatedOmega Q8).subtype

theorem matO_injective : Function.Injective matO := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem matO_y0 : matO y0 = yM := by
  rw [← commutator_levi]
  show ((lg * lh * lg⁻¹ * lh⁻¹ : GL ι8 (ZMod 2)) : Matrix ι8 ι8 (ZMod 2)) = _
  rw [Units.val_mul, Units.val_mul, Units.val_mul]
  rfl

theorem yM_pow_seven : yM ^ 7 = 1 := by decide +kernel

theorem yM_ne_one : yM ≠ 1 := by decide +kernel

theorem orderOf_y0 : orderOf y0 = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime (matO_injective ?_) fun h => yM_ne_one ?_
  · rw [map_pow, matO_y0, yM_pow_seven, map_one]
  · rw [← matO_y0, h, map_one]

@[expose] def e8 : ι8 ≃ (Fin 3 ⊕ Fin 3) ⊕ Fin 2 where
  toFun
    | Sum.inl i => if h : (i : ℕ) < 3 then Sum.inl (Sum.inl ⟨i, h⟩) else Sum.inr 0
    | Sum.inr i => if h : (i : ℕ) < 3 then Sum.inl (Sum.inr ⟨i, h⟩) else Sum.inr 1
  invFun
    | Sum.inl (Sum.inl i) => Sum.inl i.castSucc
    | Sum.inl (Sum.inr i) => Sum.inr i.castSucc
    | Sum.inr k => if k = 0 then Sum.inl 3 else Sum.inr 3
  left_inv := by decide
  right_inv := by decide

@[expose] def ext8 (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
    (D : Matrix (Fin 2) (Fin 2) (ZMod 2)) : Matrix ι8 ι8 (ZMod 2) :=
  Matrix.reindex e8.symm e8.symm (fromBlocks A 0 0 D)

theorem ext8_mul (A A' : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
    (D D' : Matrix (Fin 2) (Fin 2) (ZMod 2)) : ext8 A D * ext8 A' D' = ext8 (A * A') (D * D') := by
  simp only [ext8, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem ext8_one : ext8 1 1 = 1 := by
  simp only [ext8, fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem ext8_pow (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
    (D : Matrix (Fin 2) (Fin 2) (ZMod 2)) (n : ℕ) : ext8 A D ^ n = ext8 (A ^ n) (D ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, ext8_one]
  | succ n ih => rw [pow_succ, ih, ext8_mul, ← pow_succ, ← pow_succ]

theorem ext8_injective {A A' : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)}
    {D D' : Matrix (Fin 2) (Fin 2) (ZMod 2)} (h : ext8 A D = ext8 A' D') : A = A' ∧ D = D' := by
  have h' : fromBlocks A 0 0 D = fromBlocks A' 0 0 D' :=
    (Matrix.reindex e8.symm e8.symm).injective h
  exact ⟨(Matrix.fromBlocks_inj.mp h').1, (Matrix.fromBlocks_inj.mp h').2.2.2⟩

theorem yM_eq : yM = ext8 Sp6.y0M 1 := by decide +kernel

@[expose] def d8 : ι8 → ZMod 2 := fun i => if i = Sum.inl 3 ∨ i = Sum.inr 3 then 1 else 0

theorem diagonal_d8_eq : Matrix.diagonal d8 = ∑ i : Fin 7, yM ^ (i : ℕ) := by decide +kernel

theorem d8_inl : ∀ i, d8 (e8.symm (Sum.inl i)) = 0 := by decide

theorem d8_inr : ∀ k, d8 (e8.symm (Sum.inr k)) = 1 := by decide

theorem eq_ext8_of_commute {X : Matrix ι8 ι8 (ZMod 2)}
    (hX : X * Matrix.diagonal d8 = Matrix.diagonal d8 * X) :
    X = ext8 (Matrix.toBlocks₁₁ (Matrix.reindex e8 e8 X))
      (Matrix.toBlocks₂₂ (Matrix.reindex e8 e8 X)) := by
  have hij : ∀ i j, X i j * d8 j = d8 i * X i j := by
    intro i j
    have h := congrFun (congrFun hX i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hd : ∀ i : ι8, d8 i = 0 ∨ d8 i = 1 := by decide
  have h12 : Matrix.toBlocks₁₂ (Matrix.reindex e8 e8 X) = 0 := by
    ext i k
    simp only [Matrix.toBlocks₁₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.zero_apply]
    have h := hij (e8.symm (Sum.inl i)) (e8.symm (Sum.inr k))
    rw [d8_inl, d8_inr, mul_one, zero_mul] at h
    exact h
  have h21 : Matrix.toBlocks₂₁ (Matrix.reindex e8 e8 X) = 0 := by
    ext k i
    simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.zero_apply]
    have h := hij (e8.symm (Sum.inr k)) (e8.symm (Sum.inl i))
    rw [d8_inl, d8_inr, mul_zero, one_mul] at h
    exact h.symm
  have hb := Matrix.fromBlocks_toBlocks (Matrix.reindex e8 e8 X)
  rw [h12, h21] at hb
  rw [ext8, hb, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_submatrix]
  simp

theorem q8_ext8 : ∀ (D : Matrix (Fin 2) (Fin 2) (ZMod 2)) (w : Fin 2 → ZMod 2),
    Q8 (ext8 1 D *ᵥ (fun i => if i = Sum.inl 3 then w 0 else if i = Sum.inr 3 then w 1 else 0)) =
      (D *ᵥ w) 0 * (D *ᵥ w) 1 := by
  decide +kernel

theorem q8_two : ∀ w : Fin 2 → ZMod 2,
    Q8 (fun i => if i = Sum.inl 3 then w 0 else if i = Sum.inr 3 then w 1 else 0) = w 0 * w 1 := by
  decide +kernel

theorem two_check : ∀ D : Matrix (Fin 2) (Fin 2) (ZMod 2), D ^ 3 = 1 →
    (∀ w : Fin 2 → ZMod 2, (D *ᵥ w) 0 * (D *ᵥ w) 1 = w 0 * w 1) → D = 1 := by
  decide +kernel

theorem eq_one_of_commute_y0 (s : OM) (hs : s * y0 = y0 * s) (h3 : s ^ 3 = 1) : s = 1 := by
  set X := matO s with hXdef
  have hm : X * yM = yM * X := by
    rw [hXdef, ← matO_y0, ← map_mul, ← map_mul, hs]
  have hS : X * Matrix.diagonal d8 = Matrix.diagonal d8 * X := by
    rw [diagonal_d8_eq]
    exact commute_sum_pow hm 7
  set A := Matrix.toBlocks₁₁ (Matrix.reindex e8 e8 X) with hA
  set D := Matrix.toBlocks₂₂ (Matrix.reindex e8 e8 X) with hD
  have hXe : X = ext8 A D := eq_ext8_of_commute hS
  have hAy : A * Sp6.y0M = Sp6.y0M * A := by
    have h := hm
    rw [hXe, yM_eq, ext8_mul, ext8_mul] at h
    exact (ext8_injective h).1
  have h3' : ext8 (A ^ 3) (D ^ 3) = ext8 1 1 := by
    rw [← ext8_pow, ← hXe, hXdef, ← map_pow, h3, map_one, ext8_one]
  obtain ⟨hA3, hD3⟩ := ext8_injective h3'
  have hA1 : A = 1 := by
    have heq := eq_krylovPoly_of_commute (kr := Sp6.kr6) (kr' := Sp6.kr6i) (v := Sp6.v6)
      (e := Sp6.ex6) (fun _ _ => rfl) Sp6.kr6i_mul_kr6 hAy
    rw [heq]
    refine Sp6.commute_y0_check _ ?_
    rw [← heq, hA3]
  have hD1 : D = 1 := by
    refine two_check D hD3 fun w => ?_
    have hiso := CFSG.HardMathSupport.Malle.E27Lie.statedOmega_le_isometrySubgroup Q8 s.2
      (fun i => if i = Sum.inl 3 then w 0 else if i = Sum.inr 3 then w 1 else 0)
    have hX1 : (matO s) = ext8 1 D := by rw [← hXdef, hXe, hA1]
    change Q8 (matO s *ᵥ _) = Q8 _ at hiso
    rw [hX1, q8_ext8, q8_two] at hiso
    exact hiso
  apply matO_injective
  rw [map_one, ← hXdef, hXe, hA1, hD1, ext8_one]

theorem scalars_eq_bot : (StatedScalars ι8 (ZMod 2)).subgroupOf (StatedOmega Q8) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hs
  rw [Subgroup.mem_subgroupOf] at hs
  obtain ⟨l, hl⟩ := hs
  have hl1 : l = 1 := Subsingleton.elim _ _
  have : g = 1 := by
    have hl' : Matrix.GeneralLinearGroup.scalar ι8 l = g := hl
    rw [← hl', hl1, map_one]
  exact Subgroup.mem_bot.mpr (Subtype.ext this)

theorem quad_map (v : ι8 → GaloisField 2 1) :
    Q8 (Item434SmallTwoIII.gf21Equiv ∘ v) =
      Item434SmallTwoIII.gf21Equiv (StatedQuadPlus 4 (GaloisField 2 1) v) := by
  simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, map_sum, map_mul, Function.comp_apply]

noncomputable def projEquiv : projOmegaPlus 4 (GaloisField 2 1) ≃* OM :=
  Item434SmallTwoIV.statedOmegaPlusEquiv.symm.trans
    ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr Item434SmallTwoIII.gf21Equiv)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega Item434SmallTwoIII.gf21Equiv quad_map)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars
        Item434SmallTwoIII.gf21Equiv)).trans
      ((QuotientGroup.quotientMulEquivOfEq scalars_eq_bot).trans QuotientGroup.quotientBot))

theorem card_projOmegaPlus : Nat.card (projOmegaPlus 4 (GaloisField 2 1)) = 174182400 := by
  have hm : CFSG.Open.StatedClassicalModel (projOmegaPlus 4 (GaloisField 2 1)) .POmegaPlus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_refl 4⟩, GaloisField 2 1, inferInstance, inferInstance,
      GaloisField.card 2 1 one_ne_zero, ⟨Item434SmallTwoIV.statedOmegaPlusEquiv.symm⟩⟩
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.2.1 rfl]
  decide

theorem card_OM : Nat.card OM = 174182400 := by
  rw [← Nat.card_congr projEquiv.toEquiv, card_projOmegaPlus]

theorem not_sq_seven_dvd : ¬ 7 ^ 2 ∣ Nat.card OM := by
  rw [card_OM]
  norm_num

theorem good429_OM (x : OM) (hx : orderOf x = 3) :
    Good429 (Subgroup.centralizer ({x} : Set OM)) := by
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have h7 := not_dvd_card_centralizer_of_sylow (by norm_num) orderOf_y0 not_sq_seven_dvd
    eq_one_of_commute_y0 hx3 hx1
  refine good429_of_not_dvd (N := 174182400) (B := 559)
    (card_OM ▸ Subgroup.card_subgroup_dvd_card _) (by norm_num) (by norm_num) [7]
    (by simpa using h7) (by decide +kernel)

end O8

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
