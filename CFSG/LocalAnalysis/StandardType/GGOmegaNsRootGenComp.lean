module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFix
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.RankThree.PartOne.KC.OrthogonalNormPlanePrimary
import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Plane
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}
  {a b : Fin k} {s : Bool}

private theorem framePoly_monic (t : F) : (framePoly t).Monic := by
  unfold framePoly
  monicity!

private theorem framePoly_natDegree (t : F) : (framePoly t).natDegree = 2 := by
  unfold framePoly
  compute_degree!

private theorem framePoly_eval_one (t : F) : (framePoly t).eval 1 = t := by
  simp only [framePoly, eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_one]
  linear_combination CharTwo.add_self_eq_zero (1 : F)

theorem framePoly_ne_X_sub_one (t : F) : framePoly t ≠ X - 1 := by
  intro h
  have h2 := congrArg (fun q : F[X] => q.natDegree) h
  rw [framePoly_natDegree, show (X - 1 : F[X]).natDegree = 1 by
    simpa using natDegree_X_sub_C (1 : F)] at h2
  exact absurd h2 (by norm_num)

private theorem two_smul_eq_zero (x : V) : (2 : F) • x = 0 := by
  rw [CharTwo.two_eq_zero, zero_smul]

private theorem aeval_framePoly_apply (f : V ≃ₗ[F] V) (t : F) (v : V) :
    aeval f.toLinearMap (framePoly t) v = f (f v) + t • f v + v := by
  have h : aeval f.toLinearMap (framePoly t) =
      f.toLinearMap * f.toLinearMap + t • f.toLinearMap + 1 := by
    simp only [framePoly, map_add, map_mul, map_pow, pow_two, aeval_X, aeval_C, aeval_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [h, LinearMap.add_apply, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rfl

private theorem aeval_X_sub_one_apply (f : V ≃ₗ[F] V) (v : V) :
    aeval f.toLinearMap (X - 1 : F[X]) v = f v - v := by
  simp

private theorem framePoly_aeval_apply_eq_zero_of_rot {f : V ≃ₗ[F] V} {W : Submodule F V}
    (hW : Module.finrank F W = 2) {v : V} (hv : v ∈ W) (hfv : f v ∈ W)
    (hind : ∀ a b : F, a • v + b • f v = 0 → a = 0 ∧ b = 0)
    (hrot : f (f v) = t • f v + v) :
    ∀ x ∈ W, aeval f.toLinearMap (framePoly t) x = 0 := by
  have hli : LinearIndependent F ![v, f v] := LinearIndependent.pair_iff.2 hind
  have hspan : Submodule.span F {v, f v} = W := by
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
    · rintro _ (rfl | rfl)
      · exact hv
      · exact hfv
    · have h2 : Module.finrank F (Submodule.span F {v, f v}) = 2 := by
        rw [show ({v, f v} : Set V) = Set.range ![v, f v] by ext; simp [or_comm]]
        simpa using finrank_span_eq_card hli
      rw [h2, hW]
  have hv0 : aeval f.toLinearMap (framePoly t) v = 0 := by
    rw [aeval_framePoly_apply, hrot]
    calc t • f v + v + t • f v + v = (t • f v + t • f v) + (v + v) := by abel
      _ = 0 + 0 := by
        rw [← two_smul F (t • f v), ← two_smul F v, two_smul_eq_zero, two_smul_eq_zero]
      _ = 0 := by rw [add_zero]
  have hfv0 : aeval f.toLinearMap (framePoly t) (f v) = 0 := by
    have hcomm : (aeval f.toLinearMap (framePoly t)) * f.toLinearMap =
        f.toLinearMap * (aeval f.toLinearMap (framePoly t)) := by
      simpa using (commute_aeval (r := f.toLinearMap) (x := f.toLinearMap)
        (Commute.refl _) (framePoly t)).eq.symm
    calc aeval f.toLinearMap (framePoly t) (f v)
        = ((aeval f.toLinearMap (framePoly t)) * f.toLinearMap) v := by
          rw [Module.End.mul_apply]; rfl
      _ = (f.toLinearMap * (aeval f.toLinearMap (framePoly t))) v := by rw [hcomm]
      _ = f (aeval f.toLinearMap (framePoly t) v) := by rw [Module.End.mul_apply]; rfl
      _ = 0 := by rw [hv0, map_zero]
  have hker : Submodule.span F {v, f v} ≤ LinearMap.ker (aeval f.toLinearMap (framePoly t)) := by
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · exact LinearMap.mem_ker.mpr hv0
    · exact LinearMap.mem_ker.mpr hfv0
  intro x hx
  exact hker (hspan.symm ▸ hx)

private theorem inv_apply_eq_add_smul {f : V ≃ₗ[F] V} {v : V}
    (hrot : f (f v) = t • f v + v) : f.symm v = f v + t • v := by
  have h3 : f v = t • v + f.symm v := by
    have h := congrArg f.symm hrot
    simpa only [LinearEquiv.symm_apply_apply, map_add, map_smul] using h
  have h6 : t • v + (t • v + f.symm v) = f.symm v := by
    rw [← add_assoc, ← two_smul F (t • v), two_smul_eq_zero, zero_add]
  calc f.symm v = t • v + (t • v + f.symm v) := h6.symm
    _ = t • v + f v := by rw [← h3]
    _ = f v + t • v := add_comm _ _

private theorem rot_symm {f : V ≃ₗ[F] V} {v : V} (hrot : f (f v) = t • f v + v) :
    f.symm (f.symm v) = t • f.symm v + v := by
  have h1 : f.symm v = f v + t • v := inv_apply_eq_add_smul hrot
  calc f.symm (f.symm v) = f.symm (f v + t • v) := by rw [h1]
    _ = f.symm (f v) + t • f.symm v := by rw [map_add, map_smul]
    _ = v + t • f.symm v := by rw [LinearEquiv.symm_apply_apply]
    _ = t • f.symm v + v := add_comm _ _

private theorem independent_symm {f : V ≃ₗ[F] V} {v : V}
    (hrot : f (f v) = t • f v + v)
    (hind : ∀ a b : F, a • v + b • f v = 0 → a = 0 ∧ b = 0) :
    ∀ a b : F, a • v + b • f.symm v = 0 → a = 0 ∧ b = 0 := by
  intro a b hab
  have h1 : f.symm v = f v + t • v := inv_apply_eq_add_smul hrot
  have h2 : (a + b * t) • v + b • f v = 0 := by
    rw [h1] at hab
    have h3 : a • v + b • (f v + t • v) = (a + b * t) • v + b • f v := by module
    rwa [h3] at hab
  obtain ⟨ha, hb⟩ := hind (a + b * t) b h2
  refine ⟨?_, hb⟩
  rw [hb, zero_mul, add_zero] at ha
  exact ha

private theorem independent_u_e (hF : IsCoherentFrame Q p U e E u c t) (j : Fin k) :
    ∀ a b : F, a • u j + b • (e j : V ≃ₗ[F] V) (u j) = 0 → a = 0 ∧ b = 0 := by
  have hu0 : u j ≠ 0 := by
    intro h0
    have h1 := hF.quad_eq j
    rw [h0, map_zero] at h1
    exact hF.c_ne_zero h1.symm
  have hpol0 : QuadraticMap.polar Q (u j) (u j) = 0 := by
    rw [QuadraticMap.polar_self, CharTwo.two_nsmul]
  have htc : t * c ≠ 0 := mul_ne_zero hF.t_ne_zero hF.c_ne_zero
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    simp only [zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right hu0, rfl⟩
  · exfalso
    have h1 : b • (e j : V ≃ₗ[F] V) (u j) = -(a • u j) :=
      eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hab)
    have hfu : (e j : V ≃ₗ[F] V) (u j) = (-(a / b)) • u j := by
      calc (e j : V ≃ₗ[F] V) (u j) = b⁻¹ • (b • (e j : V ≃ₗ[F] V) (u j)) := by
            rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = b⁻¹ • (-(a • u j)) := by rw [h1]
        _ = (-(a / b)) • u j := by
            rw [smul_neg, smul_smul, ← neg_smul, div_eq_mul_inv]
            congr 1
            ring
    have h2 : QuadraticMap.polar Q (u j) ((e j : V ≃ₗ[F] V) (u j)) =
        (-(a / b)) * QuadraticMap.polar Q (u j) (u j) := by
      rw [hfu, QuadraticMap.polar_smul_right, smul_eq_mul]
    rw [hpol0, mul_zero, hF.polar_eq j] at h2
    exact htc h2

private theorem pow_apply_mem (hF : IsCoherentFrame Q p U e E u c t) (j : Fin k) :
    ∀ n : ℕ, ∀ x ∈ U j, ((e j : V ≃ₗ[F] V) ^ n) x ∈ U j := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ', LinearEquiv.mul_apply]
    exact hF.maps_to j _ (ih x hx)

private theorem inv_eq_pow (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime) (j : Fin k) :
    ((e j : V ≃ₗ[F] V))⁻¹ = (e j : V ≃ₗ[F] V) ^ (p - 1) := by
  have hjp : (e j : V ≃ₗ[F] V) ^ p = 1 := by
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (hF.orderOf_eq j ▸ pow_orderOf_eq_one (e j))
    simpa using h
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_one_add_one hp.ne_zero, hjp]

private theorem inv_apply_mem (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime) (j : Fin k) :
    ∀ x ∈ U j, ((e j : V ≃ₗ[F] V))⁻¹ x ∈ U j := by
  intro x hx
  rw [inv_eq_pow hF hp j]
  exact pow_apply_mem hF j (p - 1) x hx

private theorem cond_mem (hF : IsCoherentFrame Q p U e E u c t) (s : Bool) :
    (cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) ∈ E := by
  cases s
  · simpa using hF.toIsPlaneFrame.mem b
  · simpa using inv_mem (hF.toIsPlaneFrame.mem b)

private theorem cond_apply_eq_of_ne (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    {j : Fin k} (hj : j ≠ b) (s : Bool) {x : V} (hx : x ∈ U j) :
    ((cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
  have hxb : x ∈ polarPerp Q (U b) := mem_polarPerp_iff.mpr fun y hy => by
    rw [QuadraticMap.polar_comm]
    exact hF.perp j b hj x hx y hy
  cases s
  · simpa using hF.apply_of_perp b x hxb
  · rw [show ((cond true (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        = ((e b : V ≃ₗ[F] V))⁻¹ by simp]
    change ((e b : V ≃ₗ[F] V)).symm x = x
    rw [LinearEquiv.symm_apply_eq]
    exact (hF.apply_of_perp b x hxb).symm

private theorem y_apply_mem_U_a (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) {x : V} (hx : x ∈ U a) :
    ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      (e a : V ≃ₗ[F] V) x := by
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, cond_apply_eq_of_ne hF hp hab s hx]

private theorem y_false_apply_mem_U_b (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b)
    {x : V} (hx : x ∈ U b) :
    ((e a * e b : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = (e b : V ≃ₗ[F] V) x := by
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
  refine hF.apply_of_perp a _ (mem_polarPerp_iff.mpr fun y hy => ?_)
  rw [QuadraticMap.polar_comm]
  exact hF.perp b a (fun h => hab h.symm) _ (hF.maps_to b x hx) y hy

private theorem y_true_apply_mem_U_b (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) {x : V} (hx : x ∈ U b) :
    ((e a * (e b)⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = ((e b : V ≃ₗ[F] V))⁻¹ x := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply]
  refine hF.apply_of_perp a _ (mem_polarPerp_iff.mpr fun y hy => ?_)
  rw [QuadraticMap.polar_comm]
  exact hF.perp b a (fun h => hab h.symm) _ (inv_apply_mem hF hp b x hx) y hy

private theorem y_apply_mem_perp (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    {x : V} (hx : x ∈ polarPerp Q (U a ⊔ U b)) :
    ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
  have hxa : x ∈ polarPerp Q (U a) := fun y hy =>
    mem_polarPerp_iff.mp hx y (Submodule.mem_sup_left hy)
  have hxb : x ∈ polarPerp Q (U b) := fun y hy =>
    mem_polarPerp_iff.mp hx y (Submodule.mem_sup_right hy)
  have hx1 : ((cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
    cases s
    · simpa using hF.apply_of_perp b x hxb
    · rw [show ((cond true (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          = ((e b : V ≃ₗ[F] V))⁻¹ by simp]
      change ((e b : V ≃ₗ[F] V)).symm x = x
      rw [LinearEquiv.symm_apply_eq]
      exact (hF.apply_of_perp b x hxb).symm
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hx1]
  exact hF.apply_of_perp a x hxa

private theorem y_maps_U_pair (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) {x : V} (hx : x ∈ U a ⊔ U b) :
    ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x ∈ U a ⊔ U b := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  refine Submodule.add_mem _ ?_ ?_
  · rw [y_apply_mem_U_a hF hp hab hu]
    exact Submodule.mem_sup_left (hF.maps_to a u hu)
  · cases s
    · rw [show ((e a * cond false (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          = ((e a * e b : ↥(orthDerived Q)) : V ≃ₗ[F] V) by simp,
        y_false_apply_mem_U_b hF hab hw]
      exact Submodule.mem_sup_right (hF.maps_to b w hw)
    · rw [show ((e a * cond true (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          = ((e a * (e b)⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) by simp,
        y_true_apply_mem_U_b hF hp hab hw]
      exact Submodule.mem_sup_right (inv_apply_mem hF hp b w hw)

private theorem framePoly_y_kills_U_a (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) :
    ∀ x ∈ U a, aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
      (framePoly t) x = 0 := by
  have hfy : ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (u a) =
      (e a : V ≃ₗ[F] V) (u a) := y_apply_mem_U_a hF hp hab (hF.mem a)
  refine framePoly_aeval_apply_eq_zero_of_rot (t := t) (W := U a)
    (hF.finrank_eq a) (hF.mem a) ?_ ?_ ?_
  · rw [hfy]; exact hF.maps_to a _ (hF.mem a)
  · rw [hfy]; exact independent_u_e hF a
  · calc ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (u a))
        = ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
            ((e a : V ≃ₗ[F] V) (u a)) := by rw [hfy]
      _ = (e a : V ≃ₗ[F] V) ((e a : V ≃ₗ[F] V) (u a)) :=
          y_apply_mem_U_a hF hp hab (hF.maps_to a _ (hF.mem a))
      _ = t • (e a : V ≃ₗ[F] V) (u a) + u a := hF.rot a
      _ = t • (((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (u a)) + u a := by
          rw [hfy]

private theorem framePoly_y_kills_U_b (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) :
    ∀ x ∈ U b, aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
      (framePoly t) x = 0 := by
  cases s
  · have hfy : ((e a * cond false (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (u b) =
        (e b : V ≃ₗ[F] V) (u b) := y_false_apply_mem_U_b hF hab (hF.mem b)
    refine framePoly_aeval_apply_eq_zero_of_rot (t := t) (W := U b)
      (hF.finrank_eq b) (hF.mem b) ?_ ?_ ?_
    · rw [hfy]; exact hF.maps_to b _ (hF.mem b)
    · rw [hfy]; exact independent_u_e hF b
    · calc ((e a * cond false (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
            (((e a * cond false (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (u b))
          = ((e a * cond false (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
              ((e b : V ≃ₗ[F] V) (u b)) := by rw [hfy]
        _ = (e b : V ≃ₗ[F] V) ((e b : V ≃ₗ[F] V) (u b)) :=
            y_false_apply_mem_U_b hF hab (hF.maps_to b _ (hF.mem b))
        _ = t • (e b : V ≃ₗ[F] V) (u b) + u b := hF.rot b
        _ = t • (((e a * cond false (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (u b)) +
              u b := by rw [hfy]
  · have hfy : ((e a * cond true (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (u b) =
        ((e b : V ≃ₗ[F] V))⁻¹ (u b) := y_true_apply_mem_U_b hF hp hab (hF.mem b)
    refine framePoly_aeval_apply_eq_zero_of_rot (t := t) (W := U b)
      (hF.finrank_eq b) (hF.mem b) ?_ ?_ ?_
    · rw [hfy]; exact inv_apply_mem hF hp b _ (hF.mem b)
    · rw [hfy]
      exact independent_symm (t := t) (f := (e b : V ≃ₗ[F] V)) (hF.rot b)
        (independent_u_e hF b)
    · calc ((e a * cond true (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
            (((e a * cond true (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (u b))
          = ((e a * cond true (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
              (((e b : V ≃ₗ[F] V))⁻¹ (u b)) := by rw [hfy]
        _ = ((e b : V ≃ₗ[F] V))⁻¹ (((e b : V ≃ₗ[F] V))⁻¹ (u b)) :=
            y_true_apply_mem_U_b hF hp hab (inv_apply_mem hF hp b _ (hF.mem b))
        _ = t • (((e b : V ≃ₗ[F] V))⁻¹ (u b)) + u b :=
            rot_symm (t := t) (f := (e b : V ≃ₗ[F] V)) (hF.rot b)
        _ = t • (((e a * cond true (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (u b)) +
              u b := by rw [hfy]

private theorem framePoly_irreducible (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t) (j : Fin k) :
    Irreducible (framePoly t) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [framePoly_natDegree]; norm_num
  · intro lam hroot
    have hev : lam ^ 2 + t * lam + 1 = 0 := by
      simpa [framePoly] using hroot
    set f : V ≃ₗ[F] V := (e j : V ≃ₗ[F] V) with hf
    have hrot : f (f (u j)) = t • f (u j) + u j := by rw [hf]; exact hF.rot j
    have htu : f (u j) ∈ U j := by rw [hf]; exact hF.maps_to j (u j) (hF.mem j)
    have hmemv : u j + lam • f (u j) ∈ U j :=
      add_mem (hF.mem j) (Submodule.smul_mem _ _ htu)
    have hv0 : u j + lam • f (u j) ≠ 0 := by
      intro h0
      have h2 : (1 : F) • u j + lam • (e j : V ≃ₗ[F] V) (u j) = 0 := by
        simpa [hf] using h0
      exact one_ne_zero (independent_u_e hF j 1 lam h2).1
    have hlam2 : lam ^ 2 = t * lam + 1 := by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination hev - (t * lam + 1) * h2
    have heig : f (u j + lam • f (u j)) = lam • (u j + lam • f (u j)) := by
      have huu : f (u j) + lam • (t • f (u j) + u j) =
          lam • u j + (1 + lam * t) • f (u j) := by module
      calc f (u j + lam • f (u j)) = f (u j) + lam • f (f (u j)) := by rw [map_add, map_smul]
        _ = f (u j) + lam • (t • f (u j) + u j) := by rw [hrot]
        _ = lam • u j + (1 + lam * t) • f (u j) := huu
        _ = lam • u j + lam ^ 2 • f (u j) := by
            rw [show (1 : F) + lam * t = lam ^ 2 by rw [hlam2]; ring]
        _ = lam • (u j + lam • f (u j)) := by rw [smul_add, smul_smul, _root_.sq]
    have hiter : ∀ n : ℕ,
        (f ^ n) (u j + lam • f (u j)) = (lam ^ n) • (u j + lam • f (u j)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, heig, smul_smul, pow_succ]
    have hfp : f ^ p = 1 := by
      have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
        (hF.orderOf_eq j ▸ pow_orderOf_eq_one (e j))
      rw [hf]
      simpa using h
    have hlamp : lam ^ p = 1 := by
      have h1 : (lam ^ p) • (u j + lam • f (u j)) = u j + lam • f (u j) := by
        rw [← hiter p, hfp]
        simp
      have h2 : (lam ^ p - 1) • (u j + lam • f (u j)) = 0 := by
        rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd h3 hv0
    have hlam0 : lam ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero] at hlamp
      exact zero_ne_one hlamp
    set lamu : Fˣ := Units.mk0 lam hlam0 with hlamu
    have hval : (lamu : F) = lam := rfl
    have hlamup : lamu ^ p = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, hval]
      exact hlamp
    have hlamuq : lamu ^ (Nat.card F - 1) = 1 := by
      have h1 : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
      rw [← h1]
      exact pow_card_eq_one'
    have hcop : Nat.Coprime p (Nat.card F - 1) := by
      rw [hp.coprime_iff_not_dvd]
      intro hd
      have h2 : p ∣ 2 := by
        have h := Nat.dvd_sub hpq hd
        rwa [show Nat.card F + 1 - (Nat.card F - 1) = 2 by
          have := Nat.card_pos (α := F); omega] at h
      exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) h2) hp.two_le)
    have hord : orderOf lamu = 1 := by
      have h1 : orderOf lamu ∣ p := orderOf_dvd_of_pow_eq_one hlamup
      have h2 : orderOf lamu ∣ Nat.card F - 1 := orderOf_dvd_of_pow_eq_one hlamuq
      have h3 : orderOf lamu ∣ Nat.gcd p (Nat.card F - 1) := Nat.dvd_gcd h1 h2
      rwa [hcop.gcd_eq_one, Nat.dvd_one] at h3
    have hlam1 : lam = 1 := by
      have h1 : lamu = 1 := orderOf_eq_one_iff.mp hord
      simpa [hlamu] using congrArg Units.val h1
    have hfix : f (u j + lam • f (u j)) = u j + lam • f (u j) := by
      rw [heig, hlam1, one_smul]
    exact hv0 (hF.eq_zero_of_apply_eq j _ hmemv (by simpa [hf] using hfix))

private theorem iSup_pair_eq_sup :
    (⨆ j ∈ ({a, b} : Finset (Fin k)), U j) = U a ⊔ U b := by
  rw [Finset.iSup_insert, Finset.iSup_singleton]

private theorem nondeg_U_pair (hF : IsCoherentFrame Q p U e E u c t) :
    (QuadraticMap.polarBilin (Q.comp (U a ⊔ U b).subtype)).Nondegenerate := by
  rw [← iSup_pair_eq_sup (a := a) (b := b)]
  exact hF.toIsPlaneSystem.nondeg_biSup {a, b}

private theorem isCompl_U_pair_perp (hF : IsCoherentFrame Q p U e E u c t) :
    IsCompl (U a ⊔ U b) (polarPerp Q (U a ⊔ U b)) :=
  isCompl_polarPerp (nondeg_U_pair hF)

private theorem framePoly_y_kills_U_pair (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) :
    ∀ x ∈ U a ⊔ U b,
      aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
        (framePoly t) x = 0 := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, framePoly_y_kills_U_a hF hp hab u hu, framePoly_y_kills_U_b hF hp hab w hw,
    add_zero]

private theorem framePoly_y_apply_perp (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    {x : V} (hx : x ∈ polarPerp Q (U a ⊔ U b)) :
    aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
      (framePoly t) x = t • x := by
  have h1 : ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x :=
    y_apply_mem_perp hF hp hx
  rw [aeval_framePoly_apply]
  simp only [h1]
  calc x + t • x + x = (x + x) + t • x := by abel
    _ = 0 + t • x := by rw [← two_smul F x, two_smul_eq_zero]
    _ = t • x := zero_add _

theorem primaryComponent_pair (hp : p.Prime) (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (s : Bool) :
    primaryComponent ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
      (framePoly t) = U a ⊔ U b := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hc : x ∈ (U a ⊔ U b) ⊔ polarPerp Q (U a ⊔ U b) := by
      rw [(isCompl_U_pair_perp hF).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hc
    have h1 : aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
        (framePoly t) u = 0 := framePoly_y_kills_U_pair hF hp hab u hu
    have h2 : aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
        (framePoly t) w = t • w := framePoly_y_apply_perp hF hp hw
    have hx' : aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
        (framePoly t) (u + w) = 0 := hx
    rw [map_add, h1, h2, zero_add] at hx'
    rcases smul_eq_zero.mp hx' with h3 | h3
    · exact absurd h3 hF.t_ne_zero
    · rw [h3, add_zero]; exact hu
  · intro x hx
    exact framePoly_y_kills_U_pair hF hp hab x hx

theorem framePoly_mem_primaryFactors (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b)
    (s : Bool) :
    framePoly t ∈ primaryFactors
      ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap := by
  haveI : Fact (Irreducible (framePoly t)) := ⟨framePoly_irreducible hp hp2 hpq hF a⟩
  refine mem_primaryFactors_of_primaryComponent_ne_bot (Fact.out) (framePoly_monic t) ?_
  rw [primaryComponent_pair hp hF hab s]
  intro hbot
  have h1 : Module.finrank F (U a) = 0 := by
    rw [le_bot_iff.mp (le_trans le_sup_left (le_of_eq hbot)), finrank_bot]
  have h2 := hF.finrank_eq a
  omega

theorem primaryMultiplicity_pair (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b)
    (s : Bool) :
    primaryMultiplicity
      ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
      (framePoly t) = 2 := by
  haveI : Fact (Irreducible (framePoly t)) := ⟨framePoly_irreducible hp hp2 hpq hF a⟩
  have hpc : Module.finrank F
      (primaryComponent ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
        (framePoly t)) = 4 := by
    rw [primaryComponent_pair hp hF hab s, ← iSup_pair_eq_sup (a := a) (b := b),
      hF.toIsPlaneSystem.finrank_biSup, Finset.card_pair hab]
  have h := finrank_primaryComponent (x := ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
    V ≃ₗ[F] V).toLinearMap) (a := framePoly t)
  rw [hpc, framePoly_natDegree] at h
  show Module.finrank (AdjoinRoot (framePoly t))
    (primaryComponent ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
      (framePoly t)) = 2
  omega

private theorem fixedSpace_y_eq_perp (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) :
    fixedSpace ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
      polarPerp Q (U a ⊔ U b) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    have hvw : ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) v = v :=
      mem_fixedSpace.mp hv
    have hc : v ∈ (U a ⊔ U b) ⊔ polarPerp Q (U a ⊔ U b) := by
      rw [(isCompl_U_pair_perp hF).sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hc
    have h1 : ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (u + w) = u + w :=
      hvw
    rw [map_add, y_apply_mem_perp hF hp hw] at h1
    have h2 : ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) u = u :=
      add_right_cancel h1
    have h3 := framePoly_y_kills_U_pair (s := s) hF hp hab u hu
    have h4 : aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
        (framePoly t) u = t • u := by
      have hfix : ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap u =
          (1 : F) • u := by
        show ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) u = (1 : F) • u
        rw [h2, one_smul]
      rw [Module.End.aeval_apply_of_mem_apply_eq_smul (μ := (1 : F)) hfix, framePoly_eval_one]
    rw [h4] at h3
    rcases smul_eq_zero.mp h3 with h5 | h5
    · exact absurd h5 hF.t_ne_zero
    · rw [h5, zero_add]
      exact hw
  · intro w hw
    exact mem_fixedSpace.mpr (y_apply_mem_perp hF hp hw)

private theorem aeval_y_mul_X_sub_one_eq_zero (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hab : a ≠ b) :
    aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
      (framePoly t * (X - 1)) = 0 := by
  ext v
  simp only [LinearMap.zero_apply]
  have hc : v ∈ (U a ⊔ U b) ⊔ polarPerp Q (U a ⊔ U b) := by
    rw [(isCompl_U_pair_perp hF).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hc
  have hRu : aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
      (X - 1 : F[X]) u ∈ U a ⊔ U b := by
    rw [aeval_X_sub_one_apply]
    exact sub_mem (y_maps_U_pair hF hp hab hu) hu
  have hRw : aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
      (X - 1 : F[X]) w = 0 := by
    rw [aeval_X_sub_one_apply, y_apply_mem_perp hF hp hw, sub_self]
  rw [map_mul, Module.End.mul_apply, map_add, hRw, add_zero]
  exact framePoly_y_kills_U_pair hF hp hab _ hRu

private theorem primaryFactors_y_subset (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    ∀ k ∈ primaryFactors ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
      V ≃ₗ[F] V).toLinearMap, k = framePoly t ∨ k = X - 1 := by
  intro k hk
  have hmin : minpoly F ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap ∣
      framePoly t * (X - 1) := minpoly.dvd F _
        (aeval_y_mul_X_sub_one_eq_zero (s := s) hF hp hab)
  have hkdvd : k ∣ framePoly t * (X - 1) :=
    (mem_primaryFactors.mp hk).2.2 |>.trans hmin
  by_cases hk1 : k = framePoly t
  · exact Or.inl hk1
  · refine Or.inr ?_
    have hk_irr : Irreducible k := irreducible_of_mem_primaryFactors hk
    have hf_irr : Irreducible (framePoly t) := framePoly_irreducible hp hp2 hpq hF a
    have hcop : IsCoprime k (framePoly t) := by
      rw [hk_irr.coprime_iff_not_dvd]
      intro hd
      exact hk1 (eq_of_monic_of_associated (monic_of_mem_primaryFactors hk) (framePoly_monic t)
        (hk_irr.associated_of_dvd hf_irr hd))
    have hkd : k ∣ (X - 1) := hcop.dvd_of_dvd_mul_left hkdvd
    exact eq_of_monic_of_associated (monic_of_mem_primaryFactors hk) monic_X_sub_one
      (hk_irr.associated_of_dvd irreducible_X_sub_one hkd)

private theorem othersSpace_eq_fixedSpace_of_subset {x : V ≃ₗ[F] V} {h : F[X]}
    (hsub : ∀ k ∈ primaryFactors x.toLinearMap, k = h ∨ k = X - 1) (hh1 : h ≠ X - 1)
    (hself : reciprocalPolynomial h = h) :
    othersSpace x.toLinearMap h = fixedSpace x := by
  rw [fixedSpace_eq_primaryComponent]
  by_cases hmem : (X - 1 : F[X]) ∈ primaryFactors x.toLinearMap
  · refine le_antisymm ?_ ?_
    · refine iSup₂_le fun k hk => ?_
      have h1 : k = X - 1 := (hsub k hk.1).resolve_left hk.2.1
      exact le_of_eq (by rw [h1])
    · refine le_iSup₂_of_le (X - 1) ⟨hmem, Ne.symm hh1, ?_⟩ le_rfl
      rw [hself]; exact Ne.symm hh1
  · have hbot : primaryComponent x.toLinearMap (X - 1) = ⊥ := by
      rw [← fixedSpace_eq_primaryComponent]
      exact fixedSpace_eq_bot_of_not_mem hmem
    rw [hbot, eq_bot_iff]
    refine iSup₂_le fun k hk => ?_
    have h1 : k = X - 1 := (hsub k hk.1).resolve_left hk.2.1
    rw [h1, hbot]

private theorem y_mem (hF : IsCoherentFrame Q p U e E u c t) :
    (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) ∈ E :=
  mul_mem (hF.toIsPlaneFrame.mem a) (cond_mem hF s)

private theorem y_ne_one (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime) (hab : a ≠ b) :
    (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) ≠ 1 := by
  intro h1
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U a) (hF.finrank_eq a)
  have h2 : (e a : V ≃ₗ[F] V) v = v := by
    have h3 : ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) v = v := by
      rw [h1]; rfl
    rwa [y_apply_mem_U_a hF hp hab hv] at h3
  exact hv0 (hF.eq_zero_of_apply_eq a v hv h2)

private theorem orderOf_y (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) : orderOf (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (hF.isElemAbelian.2 _ (y_mem hF)) (y_ne_one hF hp hab)

private theorem othersSpace_y_eq_perp (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    othersSpace ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
      (framePoly t) = polarPerp Q (U a ⊔ U b) := by
  have hord := orderOf_y (s := s) hF hp hab
  have hy : OddOrderIsometry Q p ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
      V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ _ hord
  have hself : reciprocalPolynomial (framePoly t) = framePoly t :=
    hy.reciprocal_eq_of_dvd_card_succ hp hpq
      (framePoly_mem_primaryFactors hp hp2 hpq hF hab s) (framePoly_ne_X_sub_one t)
  rw [othersSpace_eq_fixedSpace_of_subset (primaryFactors_y_subset hp hp2 hpq hF hab)
    (framePoly_ne_X_sub_one t) hself]
  exact fixedSpace_y_eq_perp hF hp hab

theorem isComponentOf_pairBlock (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (hF4 : 4 ≤ Nat.card F) (s : Bool) {X : Set ↥(orthDerived Q)}
    (hyX : (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) ∈ X)
    (hX : X ⊆ Subgroup.closure (insert (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))
      (e '' {j | j ≠ a ∧ j ≠ b}))) :
    CFSG.Assembly.IsComponentOf (pairBlock Q e t a b s) (Subgroup.centralizer X) := by
  have hord : orderOf (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) = p :=
    orderOf_y (s := s) hF hp hab
  have hy : OddOrderIsometry Q p ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
      V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ _ hord
  have hmem := framePoly_mem_primaryFactors hp hp2 hpq hF hab s
  have hne := framePoly_ne_X_sub_one (F := F) t
  have hmul := primaryMultiplicity_pair hp hp2 hpq hF hab s
  have hHq : CFSG.IsQuasisimple
      ↥(specialBlock Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        (framePoly t)) :=
    isQuasisimple_specialBlock_of_multiplicity hp hp2 hpq hy hmem hne hmul
      (Or.inr ⟨Or.inl rfl, hF4⟩)
  have hHle : specialBlock Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
      (framePoly t) ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hHq.1
      ((specialBlock_le_isometryCentralizer (framePoly t)).trans fun _ hg =>
        (Subgroup.mem_inf.mp hg).1)
  have hNq : CFSG.IsQuasisimple ↥((specialBlock Q
      ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
      (framePoly t)).subgroupOf (orthDerived Q)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHle).symm hHq
  change CFSG.Assembly.IsComponentOf ((specialBlock Q
    ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
    (framePoly t)).subgroupOf (orthDerived Q)) (Subgroup.centralizer X)
  have hle : (specialBlock Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
      (framePoly t)).subgroupOf (orthDerived Q) ≤ Subgroup.centralizer X := by
    intro g hg
    have hgS : ((g : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈
        specialBlock Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (framePoly t) := Subgroup.mem_subgroupOf.mp hg
    have hgI : ((g : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ isometryCentralizer Q
        ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) :=
      specialBlock_le_isometryCentralizer (framePoly t) hgS
    have hgS' : ((g : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ supportedBlock Q
        ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t) :=
      specialBlock_le_supportedBlock (framePoly t) hgS
    have hgy : (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) * g =
        g * (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact LinearEquiv.ext fun v => ((mem_isometryCentralizer.mp hgI).2 v).symm
    have hge : ∀ j, j ≠ a → j ≠ b → (e j : ↥(orthDerived Q)) * g = g * e j := by
      intro j hja hjb
      have hfix : ∀ x ∈ U j, ((g : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
        intro x hx
        have hxperp : x ∈ polarPerp Q (U a ⊔ U b) := by
          refine mem_polarPerp_iff.mpr fun y hy => ?_
          obtain ⟨ya, hya, yb, hyb, rfl⟩ := Submodule.mem_sup.mp hy
          rw [QuadraticMap.polar_add_left, hF.perp a j (fun h => hja h.symm) ya hya x hx,
            hF.perp b j (fun h => hjb h.symm) yb hyb x hx, add_zero]
        have hxO : x ∈ othersSpace ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
            V ≃ₗ[F] V).toLinearMap (framePoly t) := by
          rw [othersSpace_y_eq_perp (s := s) hQ hp hp2 hpq hF hab]
          exact hxperp
        exact (mem_supportedBlock.mp hgS').2 x hxO
      have hcomm := commute_of_apply_eq (hF.nondeg j) (orthDerived_le_orthogonalGroup g.2)
        hfix (hF.maps_to j) (hF.apply_of_perp j)
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hcomm.symm
    have h1 : g ∈ Subgroup.centralizer (Subgroup.closure
        (insert (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))
          (e '' {j | j ≠ a ∧ j ≠ b}))) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro w hw
      rcases hw with rfl | hw
      · exact hgy
      · obtain ⟨j, ⟨hja, hjb⟩, rfl⟩ := hw
        exact hge j hja hjb
    rw [Subgroup.mem_centralizer_iff]
    exact fun z hz =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.centralizer_le hX h1) z hz
  have hnormal : ((specialBlock Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
      V ≃ₗ[F] V) (framePoly t)).subgroupOf (orthDerived Q)).subgroupOf
        (Subgroup.centralizer X) |>.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro f n hf hn
    have hfS : ((f : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ specialBlock Q
        ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t) :=
      Subgroup.mem_subgroupOf.mp hf
    have hny : n * (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) =
        (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) * n :=
      (Subgroup.mem_centralizer_iff.mp hn _ hyX).symm
    have hnyc : ((n : ↥(orthDerived Q)) : V ≃ₗ[F] V) *
        ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
        ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) *
          ((n : ↥(orthDerived Q)) : V ≃ₗ[F] V) := by
      have h1 := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hny
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
      exact h1
    have hnI : ((n : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ isometryCentralizer Q
        ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) :=
      mem_isometryCentralizer.mpr ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup n.2),
        fun v => congrArg (fun z : V ≃ₗ[F] V => z v) hnyc⟩
    have hconj := conj_mem_specialBlock (x := ((e a * cond s (e b)⁻¹ (e b) :
      ↥(orthDerived Q)) : V ≃ₗ[F] V)) (h := framePoly t) hnI hfS
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hcoe : ((n * f * n⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
        ((n : ↥(orthDerived Q)) : V ≃ₗ[F] V) * ((f : ↥(orthDerived Q)) : V ≃ₗ[F] V) *
          ((n : ↥(orthDerived Q)) : V ≃ₗ[F] V)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe]
    exact hconj
  refine ⟨hle, CFSG.Assembly.IsSubnormal.step hle hnormal
    (CFSG.Assembly.IsSubnormal.refl _), ?_⟩
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hNq

theorem mem_pairBlock_of_mul_self (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (s : Bool) {g : ↥(orthDerived Q)}
    (hgy : g * (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) =
      (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) * g)
    (hgP : ∀ x ∈ polarPerp Q (U a ⊔ U b), ((g : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x)
    (hg2 : g * g = 1) :
    g ∈ pairBlock Q e t a b s := by
  change g ∈ (specialBlock Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
    V ≃ₗ[F] V) (framePoly t)).subgroupOf (orthDerived Q)
  have hgS : ((g : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ supportedBlock Q
      ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t) := by
    refine mem_supportedBlock.mpr ⟨?_, ?_⟩
    · refine mem_isometryCentralizer.mpr ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup g.2), ?_⟩
      intro v
      have h1 := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hgy
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
      exact congrArg (fun z : V ≃ₗ[F] V => z v) h1
    · intro x hx
      rw [othersSpace_y_eq_perp (s := s) hQ hp hp2 hpq hF hab] at hx
      exact hgP x hx
  refine Subgroup.mem_subgroupOf.mpr (mem_specialBlock.mpr ⟨hgS, ?_⟩)
  haveI : Fact (Irreducible (framePoly t)) := ⟨framePoly_irreducible hp hp2 hpq hF a⟩
  have hd2 : blockDet Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
      (framePoly t) ⟨g, hgS⟩ * blockDet Q
        ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        (framePoly t) ⟨g, hgS⟩ = 1 := by
    have h1 : (⟨g, hgS⟩ : ↥(supportedBlock Q
        ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t))) *
        ⟨g, hgS⟩ = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hg2
    calc blockDet Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (framePoly t) ⟨g, hgS⟩ * blockDet Q
            ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
            (framePoly t) ⟨g, hgS⟩
        = blockDet Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
            (framePoly t) (⟨g, hgS⟩ * ⟨g, hgS⟩) := (map_mul _ _ _).symm
      _ = blockDet Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
            (framePoly t) 1 := by rw [h1]
      _ = 1 := map_one _
  have hchar : CharP (AdjoinRoot (framePoly t)) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AdjoinRoot (framePoly t))).injective 2
  haveI := hchar
  refine CharTwo.sq_injective ?_
  simpa [pow_two] using hd2

theorem dvd_card_pairBlock (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (hF4 : 4 ≤ Nat.card F) (s : Bool) :
    p ∣ Nat.card ↥(pairBlock Q e t a b s) := by
  change p ∣ Nat.card ↥((specialBlock Q
    ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
    (framePoly t)).subgroupOf (orthDerived Q))
  have hord : orderOf (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) = p :=
    orderOf_y (s := s) hF hp hab
  have hy : OddOrderIsometry Q p ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
      V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ _ hord
  have hmem := framePoly_mem_primaryFactors hp hp2 hpq hF hab s
  have hmul := primaryMultiplicity_pair hp hp2 hpq hF hab s
  have hm2 : 2 ≤ primaryMultiplicity
      ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
      (framePoly t) := by rw [hmul]
  have hdvd : p ∣ Nat.card ↥(specialBlock Q
      ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t)) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.orth3_dvd_card_orthSpecialBlock hy hp hp2 hmem
      (framePoly_ne_X_sub_one t) hm2
  have hHq : CFSG.IsQuasisimple ↥(specialBlock Q
      ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t)) :=
    isQuasisimple_specialBlock_of_multiplicity hp hp2 hpq hy hmem
      (framePoly_ne_X_sub_one t) hmul (Or.inr ⟨Or.inl rfl, hF4⟩)
  have hHle : specialBlock Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
      V ≃ₗ[F] V) (framePoly t) ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hHq.1
      ((specialBlock_le_isometryCentralizer (framePoly t)).trans fun _ hg =>
        (Subgroup.mem_inf.mp hg).1)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv]

private theorem aeval_framePoly_apply_of_fixed {f : V ≃ₗ[F] V} {v : V} (hv : f v = v) :
    aeval f.toLinearMap (framePoly t) v = t • v := by
  have hfix : f.toLinearMap v = (1 : F) • v := by
    show f v = (1 : F) • v
    rw [hv, one_smul]
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (μ := (1 : F)) hfix, framePoly_eval_one]

private theorem aeval_symm_framePoly_apply_of {f : V ≃ₗ[F] V} {v : V}
    (hv : f.symm v = f v + t • v) :
    aeval f.symm.toLinearMap (framePoly t) v = 0 := by
  have h1 : f.symm (f.symm v) = v + t • f.symm v := by
    calc f.symm (f.symm v) = f.symm (f v + t • v) := by rw [hv]
      _ = f.symm (f v) + t • f.symm v := by rw [map_add, map_smul]
      _ = v + t • f.symm v := by rw [LinearEquiv.symm_apply_apply]
  rw [aeval_framePoly_apply, h1]
  have h2 : (v + t • f.symm v) + t • f.symm v + v = 0 := by
    rw [show v + t • f.symm v + t • f.symm v + v
      = (v + v) + (t • f.symm v + t • f.symm v) by abel]
    rw [← two_smul F v, ← two_smul F (t • f.symm v), two_smul_eq_zero, two_smul_eq_zero, add_zero]
  exact h2

private theorem inv_eq_pow_of_order (hp : p.Prime) {f : V ≃ₗ[F] V} (hf : f ^ p = 1) :
    f⁻¹ = f ^ (p - 1) := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_one_add_one hp.ne_zero, hf]

private theorem pow_y_maps_U_pair (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) : ∀ n : ℕ, ∀ v ∈ U a ⊔ U b,
      (((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ n) v ∈ U a ⊔ U b := by
  intro n
  induction n with
  | zero => intro v hv; simpa using hv
  | succ n ih =>
    intro v hv
    rw [pow_succ', LinearEquiv.mul_apply]
    exact y_maps_U_pair hF hp hab (ih v hv)

private theorem z_eq_pow (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) :
    (((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V) =
      ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ (p - 1) := by
  have hyp : ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ p = 1 := by
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (pow_orderOf_eq_one (e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)))
    rwa [orderOf_y (s := s) hF hp hab] at h
  exact inv_eq_pow_of_order hp hyp

private theorem z_maps_U_pair (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) {v : V} (hv : v ∈ U a ⊔ U b) :
    ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)) v ∈ U a ⊔ U b := by
  rw [z_eq_pow (s := s) hF hp hab]
  exact pow_y_maps_U_pair (s := s) hF hp hab (p - 1) v hv

private theorem z_apply_mem_perp (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    {v : V} (hv : v ∈ polarPerp Q (U a ⊔ U b)) :
    ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)) v = v := by
  set y' : V ≃ₗ[F] V := ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
    with hy'
  have h1 : y' v = v := y_apply_mem_perp hF hp hv
  have h2 : y'.symm v = v := by
    have h3 := congrArg y'.symm h1
    simpa using h3.symm
  exact h2

private theorem z_apply_eq_add (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) {v : V} (hv : v ∈ U a ⊔ U b) :
    ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)) v =
      ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) v + t • v := by
  set y : V ≃ₗ[F] V := ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) with hy
  set z : V ≃ₗ[F] V := ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V))
    with hz
  have hzv : z v ∈ U a ⊔ U b := z_maps_U_pair (s := s) hF hp hab hv
  have hadd : y (y (z v)) + t • y (z v) + z v = 0 := by
    have h := framePoly_y_kills_U_pair (s := s) hF hp hab (z v) hzv
    rwa [aeval_framePoly_apply] at h
  have h1 : y (z v) = v := by
    rw [hz, hy]
    exact (y).apply_symm_apply v
  rw [h1] at hadd
  have h3 : y v = t • v + z v := by
    have h2 : y v + (t • v + z v) = 0 := by rw [← add_assoc]; exact hadd
    have h4 : (t • v + z v) + (t • v + z v) = 0 := by
      rw [← two_smul F (t • v + z v), two_smul_eq_zero]
    exact add_right_cancel (h2.trans h4.symm)
  have h4 : t • v + (t • v + z v) = z v := by
    rw [← add_assoc, ← two_smul F (t • v), two_smul_eq_zero, zero_add]
  calc z v = t • v + (t • v + z v) := h4.symm
    _ = t • v + y v := by rw [← h3]
    _ = y v + t • v := add_comm _ _

private theorem framePoly_z_kills_U_pair (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) :
    ∀ v ∈ U a ⊔ U b, aeval
      ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)).toLinearMap
      (framePoly t) v = 0 := by
  intro v hv
  have hzv : ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)) v =
      ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) v + t • v :=
    z_apply_eq_add (s := s) hF hp hab hv
  have h2 : aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).symm.toLinearMap
      (framePoly t) v = 0 := by
    refine aeval_symm_framePoly_apply_of (f := ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
      V ≃ₗ[F] V)) ?_
    exact hzv
  exact h2

private theorem framePoly_z_apply_perp (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    {v : V} (hv : v ∈ polarPerp Q (U a ⊔ U b)) :
    aeval ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)).toLinearMap
      (framePoly t) v = t • v := by
  have h1 : ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)) v = v :=
    z_apply_mem_perp hF hp hv
  have h2 : aeval ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V).symm.toLinearMap
      (framePoly t) v = t • v :=
    aeval_framePoly_apply_of_fixed h1
  exact h2

private theorem primaryComponent_z_pair (hp : p.Prime) (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) :
    primaryComponent ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
      V ≃ₗ[F] V)).toLinearMap (framePoly t) = U a ⊔ U b := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hc : x ∈ (U a ⊔ U b) ⊔ polarPerp Q (U a ⊔ U b) := by
      rw [(isCompl_U_pair_perp hF).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hc
    have h1 := framePoly_z_kills_U_pair (s := s) hF hp hab u hu
    have h2 := framePoly_z_apply_perp (s := s) hF hp hw
    have hx' : aeval ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
        V ≃ₗ[F] V)).toLinearMap (framePoly t) (u + w) = 0 := hx
    rw [map_add, h1, h2, zero_add] at hx'
    rcases smul_eq_zero.mp hx' with h3 | h3
    · exact absurd h3 hF.t_ne_zero
    · rw [h3, add_zero]; exact hu
  · exact framePoly_z_kills_U_pair (s := s) hF hp hab

private theorem primaryMultiplicity_z_pair (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    primaryMultiplicity ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
      V ≃ₗ[F] V)).toLinearMap (framePoly t) = 2 := by
  haveI : Fact (Irreducible (framePoly t)) := ⟨framePoly_irreducible hp hp2 hpq hF a⟩
  have hpc : Module.finrank F
      (primaryComponent ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
        V ≃ₗ[F] V)).toLinearMap (framePoly t)) = 4 := by
    rw [primaryComponent_z_pair hp hF hab, ← iSup_pair_eq_sup (a := a) (b := b),
      hF.toIsPlaneSystem.finrank_biSup, Finset.card_pair hab]
  have h := finrank_primaryComponent (x := ((((e a * cond s (e b)⁻¹ (e b) :
    ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)).toLinearMap) (a := framePoly t)
  rw [hpc, framePoly_natDegree] at h
  show Module.finrank (AdjoinRoot (framePoly t))
    (primaryComponent ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
      V ≃ₗ[F] V)).toLinearMap (framePoly t)) = 2
  omega

private theorem framePoly_z_mem_primaryFactors (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    framePoly t ∈ primaryFactors ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
      V ≃ₗ[F] V)).toLinearMap := by
  haveI : Fact (Irreducible (framePoly t)) := ⟨framePoly_irreducible hp hp2 hpq hF a⟩
  refine mem_primaryFactors_of_primaryComponent_ne_bot (Fact.out) (framePoly_monic t) ?_
  rw [primaryComponent_z_pair hp hF hab]
  intro hbot
  have h1 : Module.finrank F (U a) = 0 := by
    rw [le_bot_iff.mp (le_trans le_sup_left (le_of_eq hbot)), finrank_bot]
  have h2 := hF.finrank_eq a
  omega

private theorem orderOf_z (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) :
    orderOf (((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹)) = p := by
  rw [orderOf_inv, orderOf_y (s := s) hF hp hab]

private theorem fixedSpace_z_eq_perp (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hab : a ≠ b) :
    fixedSpace ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)) =
      polarPerp Q (U a ⊔ U b) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    have hvw : ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)) v = v :=
      mem_fixedSpace.mp hv
    have hc : v ∈ (U a ⊔ U b) ⊔ polarPerp Q (U a ⊔ U b) := by
      rw [(isCompl_U_pair_perp hF).sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hc
    have h1 : ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V))
        (u + w) = u + w := hvw
    rw [map_add, z_apply_mem_perp (s := s) hF hp hw] at h1
    have h2 : ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)) u = u :=
      add_right_cancel h1
    have h3 := framePoly_z_kills_U_pair (s := s) hF hp hab u hu
    have h4 : aeval ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
        V ≃ₗ[F] V)).toLinearMap (framePoly t) u = t • u := by
      have hfix : ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
          V ≃ₗ[F] V)).toLinearMap u = (1 : F) • u := by
        show ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)) u =
          (1 : F) • u
        rw [h2, one_smul]
      rw [Module.End.aeval_apply_of_mem_apply_eq_smul (μ := (1 : F)) hfix, framePoly_eval_one]
    rw [h4] at h3
    rcases smul_eq_zero.mp h3 with h5 | h5
    · exact absurd h5 hF.t_ne_zero
    · rw [h5, zero_add]; exact hw
  · intro w hw
    exact mem_fixedSpace.mpr (z_apply_mem_perp (s := s) hF hp hw)

private theorem aeval_z_mul_X_sub_one_eq_zero (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hab : a ≠ b) :
    aeval ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)).toLinearMap
      (framePoly t * (X - 1)) = 0 := by
  ext v
  simp only [LinearMap.zero_apply]
  have hc : v ∈ (U a ⊔ U b) ⊔ polarPerp Q (U a ⊔ U b) := by
    rw [(isCompl_U_pair_perp hF).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hc
  have hRu : aeval ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
      V ≃ₗ[F] V)).toLinearMap (X - 1 : F[X]) u ∈ U a ⊔ U b := by
    rw [aeval_X_sub_one_apply]
    exact sub_mem (z_maps_U_pair (s := s) hF hp hab hu) hu
  have hRw : aeval ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
      V ≃ₗ[F] V)).toLinearMap (X - 1 : F[X]) w = 0 := by
    rw [aeval_X_sub_one_apply, z_apply_mem_perp (s := s) hF hp hw, sub_self]
  rw [map_mul, Module.End.mul_apply, map_add, hRw, add_zero]
  exact framePoly_z_kills_U_pair (s := s) hF hp hab _ hRu

private theorem primaryFactors_z_subset (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    ∀ k ∈ primaryFactors ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
      V ≃ₗ[F] V)).toLinearMap, k = framePoly t ∨ k = X - 1 := by
  intro k hk
  have hmin : minpoly F ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
      V ≃ₗ[F] V)).toLinearMap ∣ framePoly t * (X - 1) :=
    minpoly.dvd F _ (aeval_z_mul_X_sub_one_eq_zero (s := s) hF hp hab)
  have hkdvd : k ∣ framePoly t * (X - 1) :=
    (mem_primaryFactors.mp hk).2.2 |>.trans hmin
  by_cases hk1 : k = framePoly t
  · exact Or.inl hk1
  · refine Or.inr ?_
    have hk_irr : Irreducible k := irreducible_of_mem_primaryFactors hk
    have hf_irr : Irreducible (framePoly t) := framePoly_irreducible hp hp2 hpq hF a
    have hcop : IsCoprime k (framePoly t) := by
      rw [hk_irr.coprime_iff_not_dvd]
      intro hd
      exact hk1 (eq_of_monic_of_associated (monic_of_mem_primaryFactors hk) (framePoly_monic t)
        (hk_irr.associated_of_dvd hf_irr hd))
    have hkd : k ∣ (X - 1) := hcop.dvd_of_dvd_mul_left hkdvd
    exact eq_of_monic_of_associated (monic_of_mem_primaryFactors hk) monic_X_sub_one
      (hk_irr.associated_of_dvd irreducible_X_sub_one hkd)

private theorem othersSpace_z_eq_perp (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    othersSpace ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
      V ≃ₗ[F] V)).toLinearMap (framePoly t) = polarPerp Q (U a ⊔ U b) := by
  have hord := orderOf_z (s := s) hF hp hab
  have hy : OddOrderIsometry Q p ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
      V ≃ₗ[F] V)) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ _ hord
  have hself : reciprocalPolynomial (framePoly t) = framePoly t :=
    hy.reciprocal_eq_of_dvd_card_succ hp hpq
      (framePoly_z_mem_primaryFactors hp hp2 hpq hF hab) (framePoly_ne_X_sub_one t)
  rw [othersSpace_eq_fixedSpace_of_subset (primaryFactors_z_subset hp hp2 hpq hF hab)
    (framePoly_ne_X_sub_one t) hself]
  exact fixedSpace_z_eq_perp hF hp hab

private theorem isometryCentralizer_inv_eq (x : V ≃ₗ[F] V) :
    isometryCentralizer Q x⁻¹ = isometryCentralizer Q x := by
  rw [isometryCentralizer, isometryCentralizer]
  congr 1
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : Commute g x⁻¹ := h
    exact h'.inv_right
  · intro h
    have h' : Commute g x := h
    exact h'.inv_right

private theorem supportedBlock_z_eq (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hF : IsCoherentFrame Q p U e E u c t) (hab : a ≠ b) :
    supportedBlock Q ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V))
        (framePoly t) =
      supportedBlock Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        (framePoly t) := by
  rw [supportedBlock, supportedBlock,
    isometryCentralizer_inv_eq (((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
      V ≃ₗ[F] V)),
    othersSpace_z_eq_perp (s := s) hQ hp hp2 hpq hF hab,
    othersSpace_y_eq_perp (s := s) hQ hp hp2 hpq hF hab]

private theorem specialBlock_eq_commutator_supportedBlock {x : V ≃ₗ[F] V} {h : F[X]}
    (hperf : Group.IsPerfect ↥(specialBlock Q x h)) :
    specialBlock Q x h = ⁅supportedBlock Q x h, supportedBlock Q x h⁆ := by
  have h1 : specialBlock Q x h = ⁅specialBlock Q x h, specialBlock Q x h⁆ :=
    (Subgroup.isPerfect_iff.mp hperf).symm
  refine le_antisymm ?_ (commutator_supportedBlock_le_specialBlock h)
  rw [h1]
  exact Subgroup.commutator_mono (specialBlock_le_supportedBlock h)
    (specialBlock_le_supportedBlock h)

theorem specialBlock_inv_pair (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t)
    (hab : a ≠ b) (hF4 : 4 ≤ Nat.card F) (s : Bool) :
    specialBlock Q ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V))
        (framePoly t) =
      specialBlock Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        (framePoly t) := by
  have hordz := orderOf_z (s := s) hF hp hab
  have hyz : OddOrderIsometry Q p ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) :
      V ≃ₗ[F] V)) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ _ hordz
  have hq_z : CFSG.IsQuasisimple ↥(specialBlock Q
      ((((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q))⁻¹) : V ≃ₗ[F] V)) (framePoly t)) :=
    isQuasisimple_specialBlock_of_multiplicity hp hp2 hpq hyz
      (framePoly_z_mem_primaryFactors hp hp2 hpq hF hab) (framePoly_ne_X_sub_one t)
      (primaryMultiplicity_z_pair hp hp2 hpq hF hab) (Or.inr ⟨Or.inl rfl, hF4⟩)
  have hord := orderOf_y (s := s) hF hp hab
  have hy : OddOrderIsometry Q p ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) :
      V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ _ hord
  have hq_y : CFSG.IsQuasisimple ↥(specialBlock Q
      ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t)) :=
    isQuasisimple_specialBlock_of_multiplicity hp hp2 hpq hy
      (framePoly_mem_primaryFactors hp hp2 hpq hF hab s) (framePoly_ne_X_sub_one t)
      (primaryMultiplicity_pair hp hp2 hpq hF hab s) (Or.inr ⟨Or.inl rfl, hF4⟩)
  rw [specialBlock_eq_commutator_supportedBlock hq_z.1,
    specialBlock_eq_commutator_supportedBlock hq_y.1,
    supportedBlock_z_eq hQ hp hp2 hpq hF hab]

end CFSG.StandardType.OmNsRootGen

end
