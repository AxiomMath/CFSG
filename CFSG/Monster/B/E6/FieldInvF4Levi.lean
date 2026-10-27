module

public import CFSG.LieType.Chevalley.C2E6FieldExtensionFirst
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.Monster.B.E6.FieldInvF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem bar_algebraMap (x : ZMod 2) : bar (algebraMap (ZMod 2) K x) = algebraMap (ZMod 2) K x := by
  revert x
  decide

theorem algebraMap_t0_of_bar_eq {a : K} (h : bar a = a) : algebraMap (ZMod 2) K (t0 a) = a := by
  revert a
  decide

theorem eq_one_of_bar_eq_of_ne_zero {a : K} (h : bar a = a) (h0 : a ≠ 0) : a = 1 := by
  revert a
  decide

theorem eq_one_of_ne_zero_zmod {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert x
  decide

@[expose] def spIdx : Fin 3 ⊕ Fin 3 ≃ Fin 6 where
  toFun := Sum.elim (fun i => ⟨i, by omega⟩) fun i => ⟨5 - i, by omega⟩
  invFun a := if h : (a : ℕ) < 3 then Sum.inl ⟨a, h⟩ else Sum.inr ⟨5 - a, by omega⟩
  left_inv := by decide
  right_inv := by decide

@[expose] def liftMat (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    Matrix (Fin 6) (Fin 6) K :=
  (M.submatrix spIdx.symm spIdx.symm).map (algebraMap (ZMod 2) K)

theorem liftMat_mul (M N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    liftMat (M * N) = liftMat M * liftMat N := by
  rw [liftMat, liftMat, liftMat, ← Matrix.submatrix_mul_equiv M N spIdx.symm spIdx.symm spIdx.symm,
    Matrix.map_mul]

theorem liftMat_transpose (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (liftMat M)ᵀ = liftMat Mᵀ := by
  rw [liftMat, liftMat, ← Matrix.transpose_map, Matrix.transpose_submatrix]

theorem liftMat_map_bar (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (liftMat M).map bar = liftMat M := by
  ext a b
  exact bar_algebraMap _

theorem liftMat_J : liftMat (fromBlocks 0 1 (-1) 0) = J6 := by
  decide

theorem liftMat_injective : Function.Injective liftMat := by
  intro M N h
  ext i j
  have e := congrFun₂ h (spIdx i) (spIdx j)
  simp only [liftMat, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at e
  exact (algebraMap (ZMod 2) K).injective e

theorem det_liftMat (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (liftMat M).det = algebraMap (ZMod 2) K M.det := by
  rw [liftMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_submatrix_equiv_self]

theorem det_eq_one_of_GL (M : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).det = 1 :=
  eq_one_of_ne_zero_zmod (Matrix.isUnits_det_units M).ne_zero

@[expose] def spSL (M : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : SpecialLinearGroup (Fin 6) K :=
  ⟨liftMat M, by rw [det_liftMat, det_eq_one_of_GL, map_one]⟩

theorem coe_spSL (M : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (spSL M : Matrix (Fin 6) (Fin 6) K) = liftMat M :=
  rfl

theorem spSL_mem_SU6 {M : GL (Fin 3 ⊕ Fin 3) (ZMod 2)} (hM : M ∈ StatedSp 3 (ZMod 2)) :
    spSL M ∈ SU6 := by
  rw [mem_SU6_iff, coe_spSL, liftMat_map_bar, liftMat_transpose, ← liftMat_J, ← liftMat_mul,
    ← liftMat_mul, SymplecticTorusWeyl.mem_statedSp_iff.mp hM]

@[expose] def binSU : Subgroup SU6 := MonoidHom.eqLocus frobSU.toMonoidHom (MonoidHom.id SU6)

theorem mem_binSU {h : SU6} : h ∈ binSU ↔ barSU h = h :=
  Iff.rfl

theorem coe_barSU (h : SU6) :
    (((barSU h : SU6) : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map bar :=
  rfl

theorem barSU_spSL {M : GL (Fin 3 ⊕ Fin 3) (ZMod 2)} (hM : M ∈ StatedSp 3 (ZMod 2)) :
    barSU ⟨spSL M, spSL_mem_SU6 hM⟩ = ⟨spSL M, spSL_mem_SU6 hM⟩ :=
  Subtype.ext (Subtype.ext (liftMat_map_bar _))

@[expose] def spToBin (M : StatedSp 3 (ZMod 2)) : binSU :=
  ⟨⟨spSL M, spSL_mem_SU6 M.2⟩, barSU_spSL M.2⟩

theorem spToBin_injective : Function.Injective spToBin := by
  intro M N h
  have e : liftMat ((M : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix _ _ (ZMod 2)) =
      liftMat ((N : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix _ _ (ZMod 2)) :=
    congrArg (fun x : binSU =>
      (((x : SU6) : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) h
  exact Subtype.ext (Units.ext (liftMat_injective e))

theorem spToBin_surjective : Function.Surjective spToBin := by
  rintro ⟨h, hh⟩
  set A : Matrix (Fin 6) (Fin 6) K :=
    ((h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  have hbar : A.map bar = A := by
    have := congrArg (fun x : SU6 =>
      ((x : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) (mem_binSU.mp hh)
    exact this
  set M₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) := (A.submatrix spIdx spIdx).map t0
  have hlift : liftMat M₀ = A := by
    ext a b
    simp only [liftMat, M₀, Matrix.map_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply]
    exact algebraMap_t0_of_bar_eq (congrFun₂ hbar a b)
  have hdet : IsUnit M₀.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have h1 := det_liftMat M₀
    rw [hlift, h0, map_zero] at h1
    exact one_ne_zero (((h : SpecialLinearGroup (Fin 6) K)).2.symm.trans h1)
  set M : GL (Fin 3 ⊕ Fin 3) (ZMod 2) := ((Matrix.isUnit_iff_isUnit_det M₀).mpr hdet).unit
  have hM : (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = M₀ := rfl
  have hsp : M ∈ StatedSp 3 (ZMod 2) := by
    rw [SymplecticTorusWeyl.mem_statedSp_iff, hM]
    apply liftMat_injective
    rw [liftMat_mul, liftMat_mul, ← liftMat_transpose, hlift, liftMat_J]
    have := (mem_SU6_iff _).mp h.2
    rwa [hbar] at this
  exact ⟨⟨M, hsp⟩, Subtype.ext (Subtype.ext (Subtype.ext hlift))⟩

theorem card_binSU : Nat.card binSU = 1451520 := by
  rw [← Nat.card_eq_of_bijective spToBin ⟨spToBin_injective, spToBin_surjective⟩,
    SymplecticFlag.card_statedSp, Nat.card_zmod]
  decide

theorem barSU_of_mem_ZSU {z : SU6} (hz : z ∈ ZSU) : barSU z = z * z := by
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, -, hcz⟩ := LinearFlag.mem_scalars.mp hz
  refine Subtype.ext (Subtype.ext ?_)
  change ((z : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map bar =
    ((z : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((z : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  rw [hcz, scalar_apply, diagonal_map bar_zero, diagonal_mul_diagonal]
  simp only [bar, pow_two]

theorem eq_one_of_mem_ZSU_binSU {z : SU6} (hz : z ∈ ZSU) (hb : z ∈ binSU) : z = 1 := by
  have hz' := hz
  rw [Subgroup.mem_subgroupOf] at hz'
  obtain ⟨c, -, hcz⟩ := LinearFlag.mem_scalars.mp hz'
  have hb' := congrArg (fun x : SU6 =>
    ((x : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) 0 0) (mem_binSU.mp hb)
  simp only [coe_barSU, Matrix.map_apply, hcz, scalar_apply, diagonal_apply_eq] at hb'
  have hc1 : (c : K) = 1 := eq_one_of_bar_eq_of_ne_zero hb' c.ne_zero
  refine Subtype.ext (Subtype.ext ?_)
  change ((z : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1
  rw [hcz, hc1, map_one]

abbrev FixFrob : Type := {x : SU6 ⧸ ZSU // frobAut x = x}

@[expose] def binToFix (h : binSU) : FixFrob :=
  ⟨((h : SU6) : SU6 ⧸ ZSU), by rw [frobAut_mk, mem_binSU.mp h.2]⟩

theorem binToFix_injective : Function.Injective binToFix := by
  intro h h' e
  have e' : ((h : SU6) : SU6 ⧸ ZSU) = ((h' : SU6) : SU6 ⧸ ZSU) := congrArg Subtype.val e
  rw [QuotientGroup.eq] at e'
  have := eq_one_of_mem_ZSU_binSU e' (mul_mem (inv_mem h.2) h'.2)
  exact Subtype.ext (inv_mul_eq_one.mp this)

theorem binToFix_surjective : Function.Surjective binToFix := by
  rintro ⟨x, hx⟩
  induction x using QuotientGroup.induction_on with | H h => ?_
  rw [frobAut_mk] at hx
  have hz : h⁻¹ * barSU h ∈ ZSU := QuotientGroup.eq.mp hx.symm
  set z := h⁻¹ * barSU h
  have hbh : barSU h = h * z := by rw [mul_inv_cancel_left]
  have hmem : h * z⁻¹ ∈ binSU := by
    rw [mem_binSU, ← barSUHom_apply, map_mul, map_inv, barSUHom_apply, barSUHom_apply, hbh,
      barSU_of_mem_ZSU hz]
    group
  refine ⟨⟨h * z⁻¹, hmem⟩, Subtype.ext ?_⟩
  change ((h * z⁻¹ : SU6) : SU6 ⧸ ZSU) = (h : SU6 ⧸ ZSU)
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (inv_mem hz), mul_one]

theorem card_fixFrob : Nat.card FixFrob = 1451520 := by
  rw [← Nat.card_eq_of_bijective binToFix ⟨binToFix_injective, binToFix_surjective⟩, card_binSU]

theorem betaGL_eq_iff
    (l : stdLevi firstJ) :
    betaGL (l : ModGL Tag.E6 K) = l ↔ frobAut (leviSUEquiv l) = leviSUEquiv l := by
  rw [← leviSUEquiv_betaGL, leviSUEquiv.injective.eq_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem card_leviFix :
    Nat.card {l : stdLevi firstJ // betaGL (l : ModGL Tag.E6 K) = l} = 1451520 := by
  rw [← card_fixFrob]
  exact Nat.card_congr (leviSUEquiv.toEquiv.subtypeEquiv betaGL_eq_iff)

end CFSG.Monster.B.E6.FieldInvF4
