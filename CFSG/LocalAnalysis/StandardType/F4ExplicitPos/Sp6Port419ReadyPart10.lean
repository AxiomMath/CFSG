module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.GGSixTCKSpace
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart9

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section
open CFSG.Open
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Chevalley

public section

public section

public section
open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.TitsSimplicity CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section

public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.KF4

namespace CFSG.StandardType.F4ExplicitPos.ProductTrace

private theorem bc_yOp_aux
    {τ : Tag} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (i : Fin τ.rank) (c : R) : BaseChange f (yOp τ R i c) (yOp τ S i (f c)) := by
  rw [yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
  refine bc_sum_aux f _ fun k _ => ?_
  rw [← map_pow]
  exact bc_smul_aux f (bc_yCoeff_aux f i k) _

private theorem trace_eq_sum_label {τ : Tag} {L : Type*}
    [CommRing L] (f : Module.End L (RootModule τ L)) :
    LinearMap.trace L (RootModule τ L) f = ∑ b : Label τ, f (Finsupp.single b 1) b := by
  rw [LinearMap.trace_eq_matrix_trace L Finsupp.basisSingleOne, Matrix.trace]
  simp [LinearMap.toMatrix_apply]

theorem trace_transport_without117
    {τ : Tag} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) :
    f (LinearMap.trace R (RootModule τ R) A) = LinearMap.trace S (RootModule τ S) B := by
  rw [trace_eq_sum_label (τ := τ) A, trace_eq_sum_label (τ := τ) B, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb := congrArg (fun v : RootModule τ S => v b)
    (bc_apply_aux f h (Finsupp.single b 1))
  simpa using hb

private theorem trace_uSL_mul_vSL {K : Type} [Field K] [CharP K 2] (a b : K) :
    ((uSL a * vSL b : SL2 K) : Matrix (Fin 2) (Fin 2) K).trace = a * b := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hmat : ((uSL a * vSL b : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
      !![1 + a * b, a; b, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_uSL, coe_vSL]
  rw [hmat, Matrix.trace_fin_two]
  change (1 + a * b) + 1 = a * b
  calc (1 + a * b) + 1 = (a * b + 1) + 1 := by ring
    _ = a * b + (1 + 1) := by ring
    _ = a * b + 0 := by rw [h2]
    _ = a * b := by rw [add_zero]

private lemma trace_coeff_long {L : Type} [Field L] [CharP L 2] (t : L) :
    ((1 : ℕ) : L) * (t ^ 2 - 2) + ((14 : ℕ) : L) * t + ((22 : ℕ) : L) = t ^ 2 := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have h14 : ((14 : ℕ) : L) = 0 := by
    rw [show ((14 : ℕ) : L) = ((2 * 7 : ℕ) : L) by norm_num, Nat.cast_mul, Nat.cast_two,
      h2, zero_mul]
  have h22 : ((22 : ℕ) : L) = 0 := by
    rw [show ((22 : ℕ) : L) = ((2 * 11 : ℕ) : L) by norm_num, Nat.cast_mul, Nat.cast_two,
      h2, zero_mul]
  rw [h2, sub_zero, h14, h22]
  ring

private lemma trace_coeff_short {L : Type} [Field L] [CharP L 2] (t : L) :
    ((7 : ℕ) : L) * (t ^ 2 - 2) + ((8 : ℕ) : L) * t + ((22 : ℕ) : L) = t ^ 2 := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have h7 : ((7 : ℕ) : L) = 1 := by
    rw [show ((7 : ℕ) : L) = ((2 * 3 + 1 : ℕ) : L) by norm_num, Nat.cast_add, Nat.cast_mul,
      Nat.cast_two, h2, Nat.cast_one, zero_mul, zero_add]
  have h8 : ((8 : ℕ) : L) = 0 := by
    rw [show ((8 : ℕ) : L) = ((2 * 4 : ℕ) : L) by norm_num, Nat.cast_mul, Nat.cast_two,
      h2, zero_mul]
  have h22 : ((22 : ℕ) : L) = 0 := by
    rw [show ((22 : ℕ) : L) = ((2 * 11 : ℕ) : L) by norm_num, Nat.cast_mul, Nat.cast_two,
      h2, zero_mul]
  rw [h2, sub_zero, h7, h8, h22]
  ring

private lemma f4_rank_add_18_cast {L : Type} [Field L] :
    ((Tag.F4.rank : ℕ) : L) + ((18 : ℕ) : L) = ((22 : ℕ) : L) := by
  norm_num [Tag.rank]

theorem trace_simpleRootSL2_F4_charTwo_algClosed
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2]
    (i : Fin Tag.F4.rank) (A : SL2 L) :
    LinearMap.trace L (RootModule .F4 L)
        (simpleRootSL2 .F4 L i A : Module.End L (RootModule .F4 L)) =
      (A : Matrix (Fin 2) (Fin 2) L).trace ^ 2 := by
  obtain ⟨Q, hQ⟩ := CFSG.RankThree.Chevalley.exists_conj_lower_eq_zero_of_isAlgClosed A
  set B := Q⁻¹ * A * Q with hB
  have hA' : A = Q * B * Q⁻¹ := by rw [hB]; group
  have hBe := eq_HSL_mul_uSL hQ
  set u := Units.mk0 _ (SL2_apply_zero_zero_ne_zero hQ)
  set s := (B : Matrix (Fin 2) (Fin 2) L) 0 1 / (B : Matrix (Fin 2) (Fin 2) L) 0 0
  have htr : (A : Matrix (Fin 2) (Fin 2) L).trace = (u : L) + (u⁻¹ : Lˣ) := by
    have h2 : (A : Matrix (Fin 2) (Fin 2) L).trace = (B : Matrix (Fin 2) (Fin 2) L).trace := by
      rw [hA', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, one_mul]
    rw [h2, hBe, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two]
    simp [coe_HSL, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two]
  conv_lhs =>
    rw [hA', map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, LinearMap.trace_conj, hBe]
  have hcases : i = f4Index 0 ∨ i = f4Index 1 ∨ i = f4Index 2 ∨ i = f4Index 3 := by
    fin_cases i <;> decide
  rcases hcases with h | h | h | h
  · rw [h, trace_simpleRootSL2_HSL_mul_uSL' (τ := .F4) (a := 1) (b := 14) (m := 18)
        (f4Index 0) u s (rootExponents_F4_long (f4Index 0) (Or.inl rfl))]
    rw [htr, f4_rank_add_18_cast]
    exact trace_coeff_long _
  · rw [h, trace_simpleRootSL2_HSL_mul_uSL' (τ := .F4) (a := 1) (b := 14) (m := 18)
        (f4Index 1) u s (rootExponents_F4_long (f4Index 1) (Or.inr rfl))]
    rw [htr, f4_rank_add_18_cast]
    exact trace_coeff_long _
  · rw [h, trace_simpleRootSL2_HSL_mul_uSL' (τ := .F4) (a := 7) (b := 8) (m := 18)
        (f4Index 2) u s (rootExponents_F4_short (f4Index 2) (Or.inl rfl))]
    rw [htr, f4_rank_add_18_cast]
    exact trace_coeff_short _
  · rw [h, trace_simpleRootSL2_HSL_mul_uSL' (τ := .F4) (a := 7) (b := 8) (m := 18)
        (f4Index 3) u s (rootExponents_F4_short (f4Index 3) (Or.inr rfl))]
    rw [htr, f4_rank_add_18_cast]
    exact trace_coeff_short _

theorem trace_xUnit_mul_yUnit_F4_charTwo
    (K : Type) [Field K] [CharP K 2] (i : Fin Tag.F4.rank) (c d : K) :
    LinearMap.trace K (RootModule .F4 K)
      ((xUnit .F4 K i c * yUnit .F4 K i d : ModGL .F4 K) : Module.End K (RootModule .F4 K)) =
      (c * d) ^ 2 := by
  let L := AlgebraicClosure K
  have : IsAlgClosed L := inferInstance
  have : CharP L 2 := charP_of_injective_algebraMap
    (algebraMap K L).injective 2
  let f : K →+* L := algebraMap K L
  have hbc : BaseChange f (xOp .F4 K i c * yOp .F4 K i d)
      (xOp .F4 L i (f c) * yOp .F4 L i (f d)) :=
    bc_mul_aux f (bc_xOp_aux f i c) (bc_yOp_aux f i d)
  have hA : ((xUnit .F4 K i c * yUnit .F4 K i d : ModGL .F4 K) :
      Module.End K (RootModule .F4 K)) = xOp .F4 K i c * yOp .F4 K i d := by
    rw [Units.val_mul, coe_xUnit, coe_yUnit]
  rw [hA]
  apply f.injective
  conv_rhs => rw [map_pow, map_mul]
  rw [trace_transport_without117 f hbc]
  rw [show xOp .F4 L i (f c) * yOp .F4 L i (f d) =
      ((xUnit .F4 L i (f c) * yUnit .F4 L i (f d) : ModGL .F4 L) :
        Module.End L (RootModule .F4 L)) by
    rw [Units.val_mul, coe_xUnit, coe_yUnit]]
  rw [show xUnit .F4 L i (f c) * yUnit .F4 L i (f d) =
      simpleRootSL2 .F4 L i (uSL (f c) * vSL (f d)) by
    rw [map_mul, simpleRootSL2_uSL, simpleRootSL2_vSL]]
  rw [trace_simpleRootSL2_F4_charTwo_algClosed L i (uSL (f c) * vSL (f d)),
    trace_uSL_mul_vSL]

end CFSG.StandardType.F4ExplicitPos.ProductTrace

public section

open CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

namespace CFSG.StandardType.F4ExplicitPos.PairLift

theorem exists_common_root_pair_lift {X Y : Type} [Group X] [Group Y]
    (M : LieUniversal) (φ : M.K →* X) (η : X →* Y) (hη : Function.Injective η)
    (β : Fin M.D.rank → ℤ) (Uplus Uminus : Subgroup Y) (R Rm : Subgroup X) (v : Y)
    (hv : v ∈ (η.comp φ).range)
    (hplus : (M.D.rootGroup β).map (η.comp φ) = Uplus)
    (hminus : (M.D.rootGroup (-β)).map (η.comp φ) = Uminus)
    (hR : R.map η = Uplus.map (MulAut.conj v).toMonoidHom)
    (hRm : Rm.map η = Uminus.map (MulAut.conj v).toMonoidHom) :
    ∃ u : M.K, η (φ u) = v ∧
      R = ggRootSub M.D φ β u ∧ Rm = ggRootSub M.D φ (-β) u := by
  rw [MonoidHom.mem_range] at hv
  obtain ⟨u, hu⟩ := hv
  have hu' : η (φ u) = v := hu
  have hconj : (η.comp φ).comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj v).toMonoidHom.comp (η.comp φ) := by
    ext a
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hu]
    simp only [MonoidHom.comp_apply, map_mul, map_inv]
  have key : ∀ γ : Fin M.D.rank → ℤ,
      (ggRootSub M.D φ γ u).map η =
        ((M.D.rootGroup γ).map (η.comp φ)).map (MulAut.conj v).toMonoidHom := by
    intro γ
    calc
      (ggRootSub M.D φ γ u).map η
          = (((M.D.rootGroup γ).map (MulAut.conj u).toMonoidHom).map φ).map η := by
            rw [ggRootSub]
      _ = ((M.D.rootGroup γ).map (MulAut.conj u).toMonoidHom).map (η.comp φ) := by
            rw [Subgroup.map_map]
      _ = (M.D.rootGroup γ).map ((η.comp φ).comp (MulAut.conj u).toMonoidHom) := by
            rw [Subgroup.map_map]
      _ = (M.D.rootGroup γ).map ((MulAut.conj v).toMonoidHom.comp (η.comp φ)) := by
            rw [hconj]
      _ = ((M.D.rootGroup γ).map (η.comp φ)).map (MulAut.conj v).toMonoidHom := by
            rw [Subgroup.map_map]
  have hR' : R.map η =
      ((M.D.rootGroup β).map (η.comp φ)).map (MulAut.conj v).toMonoidHom := by
    rw [hR, ← hplus]
  have hRu : R = ggRootSub M.D φ β u :=
    Subgroup.map_injective (f := η) hη (by rw [hR', key β])
  have hRm' : Rm.map η =
      ((M.D.rootGroup (-β)).map (η.comp φ)).map (MulAut.conj v).toMonoidHom := by
    rw [hRm, ← hminus]
  have hRmu : Rm = ggRootSub M.D φ (-β) u :=
    Subgroup.map_injective (f := η) hη (by rw [hRm', key (-β)])
  exact ⟨u, hu', hRu, hRmu⟩

end CFSG.StandardType.F4ExplicitPos.PairLift

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

open CFSG.LieType.Universal CFSG.StandardType

namespace CFSG.StandardType.F4ExplicitPos.RootScalar

private theorem trace_conj_units {K : Type} [Field K] (g x : ModGL .F4 K) :
    LinearMap.trace K (RootModule .F4 K)
        ((g * x * g⁻¹ : ModGL .F4 K) : Module.End K (RootModule .F4 K)) =
      LinearMap.trace K (RootModule .F4 K) (x : Module.End K (RootModule .F4 K)) := by
  rw [Units.val_mul, Units.val_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mul]

theorem f4_simple_root_scalar_of_conj_mem
    (K : Type) [Field K] [CharP K 2] (i : Fin Tag.F4.rank)
    (h : ModGL .F4 K)
    (hpos : ∀ c : K, ∃ c' : K, h * xUnit .F4 K i c * h⁻¹ = xUnit .F4 K i c')
    (hneg : ∃ a : K, h * yUnit .F4 K i 1 * h⁻¹ = yUnit .F4 K i a) :
    ∃ χ : Kˣ, ∀ c : K, h * xUnit .F4 K i c * h⁻¹ = xUnit .F4 K i ((χ : K) * c) := by
  obtain ⟨a, ha⟩ := hneg
  have key : ∀ c : K, ∃ fc : K,
      h * xUnit .F4 K i c * h⁻¹ = xUnit .F4 K i fc ∧ fc * a = c := by
    intro c
    obtain ⟨fc, hfc⟩ := hpos c
    refine ⟨fc, hfc, ?_⟩
    have hconj : h * (xUnit .F4 K i c * yUnit .F4 K i 1) * h⁻¹ =
        xUnit .F4 K i fc * yUnit .F4 K i a := by
      rw [show h * (xUnit .F4 K i c * yUnit .F4 K i 1) * h⁻¹ =
          (h * xUnit .F4 K i c * h⁻¹) * (h * yUnit .F4 K i 1 * h⁻¹) by group, hfc, ha]
    have ht := trace_conj_units h (xUnit .F4 K i c * yUnit .F4 K i 1)
    have h2 : ((h * (xUnit .F4 K i c * yUnit .F4 K i 1) * h⁻¹ : ModGL .F4 K) :
        Module.End K (RootModule .F4 K)) =
        ((xUnit .F4 K i fc * yUnit .F4 K i a : ModGL .F4 K) :
          Module.End K (RootModule .F4 K)) := by
      rw [hconj]
    rw [h2,
      CFSG.StandardType.F4ExplicitPos.ProductTrace.trace_xUnit_mul_yUnit_F4_charTwo K i fc a,
      CFSG.StandardType.F4ExplicitPos.ProductTrace.trace_xUnit_mul_yUnit_F4_charTwo K i c 1] at ht
    have ht' : (fc * a) ^ 2 = c ^ 2 := by simpa using ht
    exact CharTwo.sq_injective ht'
  obtain ⟨f1, -, hf1a⟩ := key 1
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0, mul_zero] at hf1a
    exact one_ne_zero hf1a.symm
  refine ⟨(Units.mk0 a ha0)⁻¹, fun c => ?_⟩
  obtain ⟨fc, hfc, hfca⟩ := key c
  have hfc_eq : fc = (((Units.mk0 a ha0)⁻¹ : Kˣ) : K) * c := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
    calc fc = fc * 1 := (mul_one fc).symm
      _ = fc * (a * a⁻¹) := by rw [mul_inv_cancel₀ ha0]
      _ = (fc * a) * a⁻¹ := by rw [mul_assoc]
      _ = c * a⁻¹ := by rw [hfca]
      _ = a⁻¹ * c := by rw [mul_comm]
  rw [← hfc_eq]
  exact hfc

end CFSG.StandardType.F4ExplicitPos.RootScalar
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end
