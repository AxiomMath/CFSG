module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenPhan
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenComp
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenGenB
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniOmega
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniNorm
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.Holt.Fixed
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.RankThree.PartOne.FOC.CompCommutator
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.LocalAnalysis.GLTheoremA.T173U CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {k : ℕ}
  {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)}
  {u : Fin k → V} {c t : F}

private theorem two_smul_eq_zero_gen (x : V) : (2 : F) • x = 0 := by
  rw [CharTwo.two_eq_zero, zero_smul]

private theorem framePoly_monic (t : F) : (framePoly t).Monic := by
  unfold framePoly
  monicity!

private theorem framePoly_natDegree (t : F) : (framePoly t).natDegree = 2 := by
  unfold framePoly
  compute_degree!

private theorem aeval_framePoly_apply (f : V ≃ₗ[F] V) (t : F) (v : V) :
    aeval f.toLinearMap (framePoly t) v = f (f v) + t • f v + v := by
  have h : aeval f.toLinearMap (framePoly t) =
      f.toLinearMap * f.toLinearMap + t • f.toLinearMap + 1 := by
    simp only [framePoly, map_add, map_mul, map_pow, pow_two, aeval_X, aeval_C, aeval_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [h, LinearMap.add_apply, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rfl

private theorem e_pow_eq_one (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    ((e a : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ p = 1 := by
  have h : (e a) ^ p = 1 := hF.orderOf_eq a ▸ pow_orderOf_eq_one (e a)
  have h2 := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) h
  simpa using h2

private theorem pow_apply_mem_of_maps_to {f : V ≃ₗ[F] V} {W : Submodule F V}
    (hf : ∀ x ∈ W, f x ∈ W) : ∀ n : ℕ, ∀ x ∈ W, (f ^ n) x ∈ W := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih => intro x hx; rw [pow_succ', LinearEquiv.mul_apply]; exact hf _ (ih x hx)

private theorem inv_eq_pow_e (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime) (a : Fin k) :
    ((e a : V ≃ₗ[F] V))⁻¹ = (e a : V ≃ₗ[F] V) ^ (p - 1) := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_one_add_one hp.ne_zero, e_pow_eq_one hF a]

private theorem inv_apply_mem_e (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime) (a : Fin k) :
    ∀ x ∈ U a, ((e a : V ≃ₗ[F] V))⁻¹ x ∈ U a := by
  intro x hx
  rw [inv_eq_pow_e hF hp a]
  exact pow_apply_mem_of_maps_to (hF.maps_to a) (p - 1) x hx

private theorem inv_apply_eq_add_smul {f : V ≃ₗ[F] V} {v : V} {t : F}
    (hrot : f (f v) = t • f v + v) : f.symm v = f v + t • v := by
  have h3 : f v = t • v + f.symm v := by
    have h := congrArg f.symm hrot
    simpa only [LinearEquiv.symm_apply_apply, map_add, map_smul] using h
  have h6 : t • v + (t • v + f.symm v) = f.symm v := by
    rw [← add_assoc, ← two_smul F (t • v), two_smul_eq_zero_gen, zero_add]
  calc f.symm v = t • v + (t • v + f.symm v) := h6.symm
    _ = t • v + f v := by rw [← h3]
    _ = f v + t • v := add_comm _ _

private theorem rot_symm {f : V ≃ₗ[F] V} {v : V} {t : F}
    (hrot : f (f v) = t • f v + v) : f.symm (f.symm v) = t • f.symm v + v := by
  have h1 : f.symm v = f v + t • v := inv_apply_eq_add_smul hrot
  calc f.symm (f.symm v) = f.symm (f v + t • v) := by rw [h1]
    _ = f.symm (f v) + t • f.symm v := by rw [map_add, map_smul]
    _ = v + t • f.symm v := by rw [LinearEquiv.symm_apply_apply]
    _ = t • f.symm v + v := add_comm _ _

private theorem polar_u_inv_e (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    polar Q (u a) (((e a : V ≃ₗ[F] V))⁻¹ (u a)) = t * c := by
  change polar Q (u a) (((e a : V ≃ₗ[F] V)).symm (u a)) = t * c
  rw [inv_apply_eq_add_smul (hF.rot a), QuadraticMap.polar_add_right, hF.polar_eq a,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_self, CharTwo.two_nsmul]
  simp

private theorem linearIndependent_u_apply (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k)
    {f : V ≃ₗ[F] V} (hpol : polar Q (u a) (f (u a)) = t * c) :
    ∀ x y : F, x • u a + y • f (u a) = 0 → x = 0 ∧ y = 0 := by
  have hu0 : u a ≠ 0 := by
    intro h0
    have h1 := hF.quad_eq a
    rw [h0, map_zero] at h1
    exact hF.c_ne_zero h1.symm
  have htc : t * c ≠ 0 := mul_ne_zero hF.t_ne_zero hF.c_ne_zero
  have hpolar0 : polar Q (u a) (u a) = 0 := by
    rw [QuadraticMap.polar_self, CharTwo.two_nsmul]
  intro x y hxy
  by_cases hy : y = 0
  · subst hy
    simp only [zero_smul, add_zero] at hxy
    exact ⟨(smul_eq_zero.mp hxy).resolve_right hu0, rfl⟩
  · exfalso
    have h1 : y • f (u a) = -(x • u a) :=
      eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hxy)
    have hfu : f (u a) = (-(x / y)) • u a := by
      calc f (u a) = y⁻¹ • (y • f (u a)) := by rw [smul_smul, inv_mul_cancel₀ hy, one_smul]
        _ = y⁻¹ • (-(x • u a)) := by rw [h1]
        _ = (-(x / y)) • u a := by
            rw [smul_neg, smul_smul, ← neg_smul, div_eq_mul_inv]
            congr 1
            ring
    have h2 : polar Q (u a) (f (u a)) = (-(x / y)) * polar Q (u a) (u a) := by
      rw [hfu, QuadraticMap.polar_smul_right, smul_eq_mul]
    rw [hpol, hpolar0, mul_zero] at h2
    exact htc h2

private theorem framePoly_aeval_apply_eq_zero_of_rot (hF : IsCoherentFrame Q p U e E u c t)
    (a : Fin k) {f : V ≃ₗ[F] V} (hfU : ∀ x ∈ U a, f x ∈ U a)
    (hrot : f (f (u a)) = t • f (u a) + u a)
    (hpol : polar Q (u a) (f (u a)) = t * c) :
    ∀ x ∈ U a, aeval f.toLinearMap (framePoly t) x = 0 := by
  have hind := linearIndependent_u_apply hF a hpol
  have hli : LinearIndependent F ![u a, f (u a)] := LinearIndependent.pair_iff.2 hind
  have hspan : Submodule.span F {u a, f (u a)} = U a := by
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
    · rintro _ (rfl | rfl)
      · exact hF.mem a
      · exact hfU _ (hF.mem a)
    · have h2 : Module.finrank F (Submodule.span F {u a, f (u a)}) = 2 := by
        rw [show ({u a, f (u a)} : Set V) = Set.range ![u a, f (u a)] by ext; simp [or_comm]]
        simpa using finrank_span_eq_card hli
      rw [h2, hF.finrank_eq a]
  have hv0 : aeval f.toLinearMap (framePoly t) (u a) = 0 := by
    rw [aeval_framePoly_apply, hrot]
    calc t • f (u a) + u a + t • f (u a) + u a
        = (t • f (u a) + t • f (u a)) + (u a + u a) := by abel
      _ = 0 + 0 := by
        rw [← two_smul F (t • f (u a)), ← two_smul F (u a), two_smul_eq_zero_gen,
          two_smul_eq_zero_gen]
      _ = 0 := by rw [add_zero]
  have hfv0 : aeval f.toLinearMap (framePoly t) (f (u a)) = 0 := by
    have hcomm : (aeval f.toLinearMap (framePoly t)) * f.toLinearMap =
        f.toLinearMap * (aeval f.toLinearMap (framePoly t)) := by
      simpa using (commute_aeval (r := f.toLinearMap) (x := f.toLinearMap)
        (Commute.refl _) (framePoly t)).eq.symm
    calc aeval f.toLinearMap (framePoly t) (f (u a))
        = ((aeval f.toLinearMap (framePoly t)) * f.toLinearMap) (u a) := by
          rw [Module.End.mul_apply]; rfl
      _ = (f.toLinearMap * (aeval f.toLinearMap (framePoly t))) (u a) := by rw [hcomm]
      _ = f (aeval f.toLinearMap (framePoly t) (u a)) := by rw [Module.End.mul_apply]; rfl
      _ = 0 := by rw [hv0, map_zero]
  have hker : Submodule.span F {u a, f (u a)} ≤
      LinearMap.ker (aeval f.toLinearMap (framePoly t)) := by
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · exact LinearMap.mem_ker.mpr hv0
    · exact LinearMap.mem_ker.mpr hfv0
  intro x hx
  exact hker (hspan.symm ▸ hx)

private theorem framePoly_irreducible (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    Irreducible (framePoly t) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [framePoly_natDegree]; norm_num
  · intro lam hroot
    have hev : lam ^ 2 + t * lam + 1 = 0 := by
      simpa [framePoly] using hroot
    set f : V ≃ₗ[F] V := (e a : V ≃ₗ[F] V) with hf
    have hrot : f (f (u a)) = t • f (u a) + u a := by rw [hf]; exact hF.rot a
    have htu : f (u a) ∈ U a := by rw [hf]; exact hF.maps_to a (u a) (hF.mem a)
    have hmemv : u a + lam • f (u a) ∈ U a :=
      add_mem (hF.mem a) (Submodule.smul_mem _ _ htu)
    have hv0 : u a + lam • f (u a) ≠ 0 := by
      intro h0
      have h2 : (1 : F) • u a + lam • (e a : V ≃ₗ[F] V) (u a) = 0 := by
        simpa [hf] using h0
      exact one_ne_zero (linearIndependent_u_apply hF a (hF.polar_eq a) 1 lam h2).1
    have hlam2 : lam ^ 2 = t * lam + 1 := by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination hev - (t * lam + 1) * h2
    have heig : f (u a + lam • f (u a)) = lam • (u a + lam • f (u a)) := by
      have huu : f (u a) + lam • (t • f (u a) + u a) =
          lam • u a + (1 + lam * t) • f (u a) := by module
      calc f (u a + lam • f (u a)) = f (u a) + lam • f (f (u a)) := by rw [map_add, map_smul]
        _ = f (u a) + lam • (t • f (u a) + u a) := by rw [hrot]
        _ = lam • u a + (1 + lam * t) • f (u a) := huu
        _ = lam • u a + lam ^ 2 • f (u a) := by
            rw [show (1 : F) + lam * t = lam ^ 2 by rw [hlam2]; ring]
        _ = lam • (u a + lam • f (u a)) := by rw [smul_add, smul_smul, _root_.sq]
    have hiter : ∀ n : ℕ,
        (f ^ n) (u a + lam • f (u a)) = (lam ^ n) • (u a + lam • f (u a)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, heig, smul_smul, pow_succ]
    have hfp : f ^ p = 1 := by
      have h := e_pow_eq_one hF a
      rw [hf]
      simpa using h
    have hlamp : lam ^ p = 1 := by
      have h1 : (lam ^ p) • (u a + lam • f (u a)) = u a + lam • f (u a) := by
        rw [← hiter p, hfp]
        simp
      have h2 : (lam ^ p - 1) • (u a + lam • f (u a)) = 0 := by
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
    have hfix : f (u a + lam • f (u a)) = u a + lam • f (u a) := by
      rw [heig, hlam1, one_smul]
    exact hv0 (hF.eq_zero_of_apply_eq a _ hmemv (by simpa [hf] using hfix))

private def sgnElt (e : Fin k → ↥(orthDerived Q)) (a : Fin k) (s : Bool) : ↥(orthDerived Q) :=
  cond s (e a)⁻¹ (e a)

private theorem sgnElt_false (a : Fin k) : sgnElt e a false = e a := rfl

private theorem sgnElt_true (a : Fin k) : sgnElt e a true = (e a)⁻¹ := rfl

private theorem inv_sgnElt (a : Fin k) (s : Bool) :
    (sgnElt e a s)⁻¹ = sgnElt e a (!s) := by
  cases s <;> simp [sgnElt]

private theorem sgnElt_pow_eq_one (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) (s : Bool) :
    sgnElt e a s ^ p = 1 := by
  cases s
  · simpa [sgnElt] using (hF.orderOf_eq a ▸ pow_orderOf_eq_one (e a))
  · have h : (e a) ^ p = 1 := hF.orderOf_eq a ▸ pow_orderOf_eq_one (e a)
    rw [sgnElt_true, inv_pow, h, inv_one]

private theorem commute_e (hF : IsCoherentFrame Q p U e E u c t) (a b : Fin k) :
    Commute (e a) (e b) := by
  have h := (isMulCommutative_iff.mp hF.isElemAbelian.1)
    (⟨e a, hF.toIsPlaneFrame.mem a⟩ : ↥E) (⟨e b, hF.toIsPlaneFrame.mem b⟩ : ↥E)
  exact Subtype.ext_iff.mp h

private theorem commute_sgnElt (hF : IsCoherentFrame Q p U e E u c t) (a b : Fin k) (s s' : Bool) :
    Commute (sgnElt e a s) (sgnElt e b s') := by
  have h := commute_e hF a b
  cases s <;> cases s'
  · simpa [sgnElt] using h
  · simpa [sgnElt] using h.inv_right
  · simpa [sgnElt] using h.inv_left
  · simpa [sgnElt] using h.inv_left.inv_right

private theorem apply_sgnElt_of_ne (hF : IsCoherentFrame Q p U e E u c t) {a b : Fin k}
    (hab : a ≠ b) (s : Bool) {x : V} (hx : x ∈ U b) :
    ((sgnElt e a s : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
  have hxb : x ∈ polarPerp Q (U a) := mem_polarPerp_iff.mpr fun y hy => by
    rw [QuadraticMap.polar_comm]
    exact hF.perp b a hab.symm x hx y hy
  cases s
  · simpa [sgnElt] using hF.apply_of_perp a x hxb
  · rw [sgnElt_true]
    have hfix : (e a : V ≃ₗ[F] V) x = x := hF.apply_of_perp a x hxb
    simp only [Subgroup.coe_inv]
    change ((e a : V ≃ₗ[F] V)).symm x = x
    rw [LinearEquiv.symm_apply_eq]
    exact hfix.symm

private theorem apply_mem_sgnElt (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime) (a : Fin k)
    (s : Bool) {x : V} (hx : x ∈ U a) :
    ((sgnElt e a s : ↥(orthDerived Q)) : V ≃ₗ[F] V) x ∈ U a := by
  cases s
  · simpa [sgnElt] using hF.maps_to a x hx
  · rw [sgnElt_true]
    simp only [Subgroup.coe_inv]
    rw [inv_eq_pow_e hF hp a]
    exact pow_apply_mem_of_maps_to (hF.maps_to a) (p - 1) x hx

private theorem framePoly_aeval_sgnElt (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (a : Fin k) (s : Bool) :
    ∀ x ∈ U a,
      aeval ((sgnElt e a s : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap (framePoly t) x = 0 := by
  cases s
  · simpa [sgnElt] using
      framePoly_aeval_apply_eq_zero_of_rot hF a (hF.maps_to a) (hF.rot a) (hF.polar_eq a)
  · rw [sgnElt_true]
    simp only [Subgroup.coe_inv]
    exact framePoly_aeval_apply_eq_zero_of_rot hF a (inv_apply_mem_e hF hp a)
      (rot_symm (hF.rot a)) (polar_u_inv_e hF a)

private theorem oddOrderIsometry_of_mem_pow (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) {d : V ≃ₗ[F] V}
    (hd : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hdp : d ^ p = 1) :
    OddOrderIsometry Q p d where
  mem := hd
  pow_eq_one := hdp
  cast_ne_zero := by
    intro h0
    have h1 : ringChar F ∣ p := (ringChar.spec F p).mp h0
    rw [ringChar.eq F 2] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h1).symm
  regular := fun v hv => hQ.1 v fun w => by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hv w

private theorem flip_primary_data (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t)
    (htop : (⨆ j, U j : Submodule F V) = ⊤) (j₀ : Fin k) {d : V ≃ₗ[F] V} {ε : Fin k → Bool}
    (hdO : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hact : ∀ j, ∀ x ∈ U j, d x = ((sgnElt e j (ε j) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x)
    (hperp : ∀ x ∈ polarPerp Q (⨆ j, U j), d x = x) :
    d ^ p = 1 ∧ OddOrderIsometry Q p d ∧
      framePoly t ∈ primaryFactors d.toLinearMap ∧
      (∀ j, U j ≤ primaryComponent d.toLinearMap (framePoly t)) ∧
      (∀ j, ∀ x ∈ U j, d x ∈ U j) := by
  haveI : Nontrivial V := by
    obtain ⟨v, -, hv⟩ := exists_ne_zero_mem_of_finrank_eq_two (U j₀) (hF.finrank_eq j₀)
    exact ⟨⟨v, 0, hv⟩⟩
  have hmem : ∀ j, ∀ x ∈ U j, d x ∈ U j := by
    intro j x hx
    rw [hact j x hx]
    exact apply_mem_sgnElt hF hp j (ε j) hx
  have hiter : ∀ (j : Fin k) (n : ℕ), ∀ y ∈ U j,
      (d ^ n) y = (((sgnElt e j (ε j) : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ n) y := by
    intro j n
    induction n with
    | zero => intro y _; simp
    | succ n ih =>
      intro y hy
      rw [pow_succ', LinearEquiv.mul_apply, pow_succ', LinearEquiv.mul_apply, ih y hy]
      exact hact j _ (pow_apply_mem_of_maps_to (fun x hx => apply_mem_sgnElt hF hp j (ε j) hx)
        n y hy)
  have hpow : ∀ j, ∀ x ∈ U j, (d ^ p) x = x := by
    intro j x hx
    have h1 : (((sgnElt e j (ε j) : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ p) = 1 := by
      rw [← Subgroup.coe_pow, sgnElt_pow_eq_one hF j (ε j)]
      rfl
    rw [hiter j p x hx, h1]
    rfl
  have hpow1 : d ^ p = 1 := by
    refine hF.toIsPlaneFrame.toIsPlaneSystem.eq_one_of_apply_eq (d := d ^ p)
      (fun j x hx => hpow j x hx) ?_
    intro x hx
    have hiterp : ∀ n : ℕ, (d ^ n) x = x := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih]; exact hperp x hx
    exact hiterp p
  have hkill : ∀ j, ∀ x ∈ U j, aeval d.toLinearMap (framePoly t) x = 0 := by
    intro j x hx
    have h1 : d x = ((sgnElt e j (ε j) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x := hact j x hx
    have h2 : d (d x) =
        ((sgnElt e j (ε j) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (((sgnElt e j (ε j) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x) := by
      rw [hact j (d x) (hmem j x hx), h1]
    rw [show aeval d.toLinearMap (framePoly t) x = d (d x) + t • d x + x from
      aeval_framePoly_apply d t x, h2, h1]
    simpa only [aeval_framePoly_apply] using framePoly_aeval_sgnElt hF hp j (ε j) x hx
  have haeval : aeval d.toLinearMap (framePoly t) = 0 := by
    ext v
    have hv : v ∈ (⨆ j, U j : Submodule F V) := by rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction U (motive := fun v => aeval d.toLinearMap (framePoly t) v = 0)
      hv (fun j x hx => hkill j x hx) ?_ ?_
    · simp
    · intro x y hx hy; rw [map_add, hx, hy, add_zero]
  have hminpoly : minpoly F d.toLinearMap = framePoly t :=
    (minpoly.eq_of_irreducible_of_monic (framePoly_irreducible hp hp2 hpq hF j₀) haeval
      (framePoly_monic t)).symm
  refine ⟨hpow1, oddOrderIsometry_of_mem_pow hQ hp hp2 hdO hpow1, ?_, ?_, hmem⟩
  · refine mem_primaryFactors.mpr
      ⟨framePoly_irreducible hp hp2 hpq hF j₀, framePoly_monic t, ?_⟩
    rw [hminpoly]
  · intro j x hx
    exact mem_primaryComponent.mpr (hkill j x hx)

private theorem sgnElt_mem_E (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) (s : Bool) :
    sgnElt e a s ∈ E := by
  cases s
  · simpa [sgnElt] using hF.toIsPlaneFrame.mem a
  · simpa [sgnElt] using inv_mem (hF.toIsPlaneFrame.mem a)

private theorem specialBlock_pair_swap (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t)
    {a b : Fin k} (hab : a ≠ b) (hF4 : 4 ≤ Nat.card F) (s : Bool) :
    specialBlock Q ((e b * cond s (e a)⁻¹ (e a) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        (framePoly t) =
      specialBlock Q ((e a * cond s (e b)⁻¹ (e b) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        (framePoly t) := by
  change specialBlock Q ((e b * sgnElt e a s : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t) =
      specialBlock Q ((e a * sgnElt e b s : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t)
  cases s
  · rw [show (e b * sgnElt e a false : ↥(orthDerived Q)) =
        (e a * sgnElt e b false : ↥(orthDerived Q)) from (commute_e hF b a).eq]
  · have h1 : (e b * sgnElt e a true : ↥(orthDerived Q)) =
        ((e a * sgnElt e b true : ↥(orthDerived Q)))⁻¹ := by
      rw [sgnElt_true, sgnElt_true, mul_inv_rev, inv_inv]
    rw [h1]
    exact specialBlock_inv_pair hQ hp hp2 hpq hF hab hF4 true

private noncomputable def pairIdx {a b : Fin k} (h : a ≠ b) (s : Bool) : OmPlusIdx k :=
  if hab : a < b then (⟨(a, b), hab⟩, s)
  else (⟨(b, a), (lt_or_gt_of_ne h).resolve_left hab⟩, s)

private theorem pairIdx_pair {a b : Fin k} (h : a ≠ b) (s : Bool) :
    ({a, b} : Finset (Fin k)) = {(pairIdx h s).1.1.1, (pairIdx h s).1.1.2} := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [show pairIdx h s = (⟨(a, b), hlt⟩, s) from by unfold pairIdx; rw [dif_pos hlt]]
  · rw [show pairIdx h s = (⟨(b, a), hgt⟩, s) from by
      unfold pairIdx; rw [dif_neg (not_lt.mpr (le_of_lt hgt))]]
    exact (Finset.pair_comm b a).symm

private theorem pairIdx_ne_of_pair_ne {a b : Fin k} (h : a ≠ b) (s : Bool) {x₀ : OmPlusIdx k}
    (hne : ({a, b} : Finset (Fin k)) ≠ {x₀.1.1.1, x₀.1.1.2}) : pairIdx h s ≠ x₀ := by
  intro he
  exact hne (by rw [pairIdx_pair h s, he])

private theorem pairBlock_pairIdx (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF : IsCoherentFrame Q p U e E u c t)
    {a b : Fin k} (hab : a ≠ b) (hF4 : 4 ≤ Nat.card F) (s : Bool) :
    pairBlock Q e t (pairIdx hab s).1.1.1 (pairIdx hab s).1.1.2 (pairIdx hab s).2 =
      pairBlock Q e t a b s := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have h1 : (pairIdx hab s).1.1.1 = a := by
      unfold pairIdx; rw [dif_pos hlt]
    have h2 : (pairIdx hab s).1.1.2 = b := by
      unfold pairIdx; rw [dif_pos hlt]
    have h3 : (pairIdx hab s).2 = s := by
      unfold pairIdx; rw [dif_pos hlt]
    rw [h1, h2, h3]
  · have h1 : (pairIdx hab s).1.1.1 = b := by
      unfold pairIdx; rw [dif_neg (not_lt.mpr (le_of_lt hgt))]
    have h2 : (pairIdx hab s).1.1.2 = a := by
      unfold pairIdx; rw [dif_neg (not_lt.mpr (le_of_lt hgt))]
    have h3 : (pairIdx hab s).2 = s := by
      unfold pairIdx; rw [dif_neg (not_lt.mpr (le_of_lt hgt))]
    rw [h1, h2, h3]
    unfold pairBlock
    rw [specialBlock_pair_swap hQ hp hp2 hpq hF (ne_of_gt hgt) hF4 s]

private theorem specialBlock_sgn_mul_le_iSup (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hF : IsCoherentFrame Q p U e E u c t) {a b : Fin k} (hab : a ≠ b)
    (hF4 : 4 ≤ Nat.card F) (sa sb : Bool) :
    specialBlock Q ((sgnElt e a sa * sgnElt e b sb : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        (framePoly t) ≤
      ⨆ x : OmPlusIdx k,
        specialBlock Q ((e x.1.1.1 * sgnElt e x.1.1.2 x.2 : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (framePoly t) := by
  suffices h : ∃ x : OmPlusIdx k,
      specialBlock Q ((sgnElt e a sa * sgnElt e b sb : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (framePoly t) =
        specialBlock Q ((e x.1.1.1 * sgnElt e x.1.1.2 x.2 : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (framePoly t) by
    obtain ⟨x, hx⟩ := h
    rw [hx]
    exact le_iSup (fun x : OmPlusIdx k =>
      specialBlock Q ((e x.1.1.1 * sgnElt e x.1.1.2 x.2 : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        (framePoly t)) x
  have key : ∀ {i j : Fin k} (hij : i < j) (σ τ : Bool), ∃ s' : Bool,
      specialBlock Q ((sgnElt e i σ * sgnElt e j τ : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (framePoly t) =
        specialBlock Q ((e i * sgnElt e j s' : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t) := by
    intro i j hij σ τ
    cases σ
    · exact ⟨τ, rfl⟩
    · refine ⟨!τ, ?_⟩
      have h1 : (sgnElt e i true * sgnElt e j τ : ↥(orthDerived Q)) =
          ((e i * sgnElt e j (!τ) : ↥(orthDerived Q)))⁻¹ := by
        rw [sgnElt_true, mul_inv_rev, inv_sgnElt, Bool.not_not]
        exact (commute_sgnElt hF i j true τ).eq
      rw [h1]
      exact specialBlock_inv_pair hQ hp hp2 hpq hF (ne_of_lt hij) hF4 (!τ)
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · obtain ⟨s', hs'⟩ := key hlt sa sb
    exact ⟨(⟨(a, b), hlt⟩, s'), hs'⟩
  · obtain ⟨s', hs'⟩ := key hgt sb sa
    refine ⟨(⟨(b, a), hgt⟩, s'), ?_⟩
    rw [show (sgnElt e a sa * sgnElt e b sb : ↥(orthDerived Q)) =
      (sgnElt e b sb * sgnElt e a sa : ↥(orthDerived Q)) from (commute_sgnElt hF a b sa sb).eq]
    exact hs'

private theorem specialBlock_pair_le_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hF : IsCoherentFrame Q p U e E u c t) {a b : Fin k} (hab : a ≠ b)
    (hF4 : 4 ≤ Nat.card F) (s : Bool) :
    specialBlock Q ((e a * sgnElt e b s : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t) ≤
      orthDerived Q := by
  have hmemE : (e a * sgnElt e b s : ↥(orthDerived Q)) ∈ E :=
    mul_mem (hF.toIsPlaneFrame.mem a) (sgnElt_mem_E hF b s)
  have hpow : (e a * sgnElt e b s : ↥(orthDerived Q)) ^ p = 1 := hF.isElemAbelian.2 _ hmemE
  have hy : OddOrderIsometry Q p ((e a * sgnElt e b s : ↥(orthDerived Q)) : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived_pow_eq_one hQ hp hp2 hpow
  have hq : CFSG.IsQuasisimple
      ↥(specialBlock Q ((e a * sgnElt e b s : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t)) :=
    isQuasisimple_specialBlock_of_multiplicity hp hp2 hpq hy
      (framePoly_mem_primaryFactors hp hp2 hpq hF hab s) (framePoly_ne_X_sub_one t)
      (primaryMultiplicity_pair hp hp2 hpq hF hab s) (Or.inr ⟨Or.inl rfl, hF4⟩)
  exact specialBlock_le_orthDerived_of_perfect hq.1
    ((specialBlock_le_isometryCentralizer (framePoly t)).trans
      fun _ hg => (Subgroup.mem_inf.mp hg).1)

private theorem apply_sgnElt_of_mem_polarPerp (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (s : Bool) {x : V} (hx : x ∈ polarPerp Q (U a)) :
    ((sgnElt e a s : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
  cases s
  · simpa [sgnElt] using hF.apply_of_perp a x hx
  · rw [sgnElt_true]
    have hfix : (e a : V ≃ₗ[F] V) x = x := hF.apply_of_perp a x hx
    simp only [Subgroup.coe_inv]
    change ((e a : V ≃ₗ[F] V)).symm x = x
    rw [LinearEquiv.symm_apply_eq]
    exact hfix.symm

private theorem sgnElt_mul_apply_eq_of_acts (hF : IsCoherentFrame Q p U e E u c t) {a b : Fin k}
    (hab : a ≠ b) (sa sb : Bool) {f : V ≃ₗ[F] V}
    (hfa : ∀ x ∈ U a, f x = ((sgnElt e a sa : ↥(orthDerived Q)) : V ≃ₗ[F] V) x)
    (hfb : ∀ x ∈ U b, f x = ((sgnElt e b sb : ↥(orthDerived Q)) : V ≃ₗ[F] V) x)
    (hfbU : ∀ x ∈ U b, f x ∈ U b) :
    ∀ x ∈ U a ⊔ U b,
      ((sgnElt e a sa * sgnElt e b sb : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = f x := by
  intro x hx
  obtain ⟨xa, hxa, xb, hxb, rfl⟩ := Submodule.mem_sup.mp hx
  have h3 : ((sgnElt e b sb : ↥(orthDerived Q)) : V ≃ₗ[F] V) xa = xa :=
    apply_sgnElt_of_ne hF hab.symm sb hxa
  have h5 : ((sgnElt e a sa : ↥(orthDerived Q)) : V ≃ₗ[F] V) (f xb) = f xb :=
    apply_sgnElt_of_ne hF hab sa (hfbU xb hxb)
  have hL : ((sgnElt e a sa * sgnElt e b sb : ↥(orthDerived Q)) : V ≃ₗ[F] V) (xa + xb) =
      ((sgnElt e a sa : ↥(orthDerived Q)) : V ≃ₗ[F] V) xa +
        ((sgnElt e a sa : ↥(orthDerived Q)) : V ≃ₗ[F] V)
          (((sgnElt e b sb : ↥(orthDerived Q)) : V ≃ₗ[F] V) xb) := by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, map_add, h3, map_add]
  rw [hL, ← hfa xa hxa, ← hfb xb hxb, h5]
  exact (map_add f xa xb).symm

private theorem sgnElt_mul_apply_eq_one_of_perp (hF : IsCoherentFrame Q p U e E u c t)
    {a b : Fin k} (hab : a ≠ b) (sa sb : Bool) :
    ∀ x ∈ polarPerp Q (U a ⊔ U b),
      ((sgnElt e a sa * sgnElt e b sb : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
  intro x hx
  have hxa : x ∈ polarPerp Q (U a) := mem_polarPerp_iff.mpr fun y hy =>
    mem_polarPerp_iff.mp hx y (Submodule.mem_sup_left hy)
  have hxb : x ∈ polarPerp Q (U b) := mem_polarPerp_iff.mpr fun y hy =>
    mem_polarPerp_iff.mp hx y (Submodule.mem_sup_right hy)
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, apply_sgnElt_of_mem_polarPerp hF b sb hxb]
  exact apply_sgnElt_of_mem_polarPerp hF a sa hxa

theorem orthDerived_le_iSup_specialBlock_pair_frame (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF4 : 4 ≤ Nat.card F) (hk : 3 ≤ k)
    (hF : IsCoherentFrame Q p U e E u c t) (htop : (⨆ j, U j : Submodule F V) = ⊤) :
    orthDerived Q ≤ ⨆ x : OmPlusIdx k, specialBlock Q
      ((e x.1.1.1 * cond x.2 (e x.1.1.2)⁻¹ (e x.1.1.2) : ↥(orthDerived Q)) : V ≃ₗ[F] V)
      (framePoly t) := by
  classical
  have hdim : Module.finrank F V = 2 * k := by
    have h1 := hF.toIsPlaneFrame.toIsPlaneSystem.finrank_biSup (Finset.univ : Finset (Fin k))
    have h2 : (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) = ⊤ := by rw [← htop]; simp
    rw [h2] at h1
    simpa [Finset.card_univ, Fintype.card_fin] using h1
  have j₀ : Fin k := ⟨0, by omega⟩
  obtain ⟨τ, -, hτrange, -, hτapply⟩ :=
    exists_frameTorus (Q := Q) (p := p) hF.toIsPlaneFrame hp
  set dΩ : ↥(orthDerived Q) := τ (fun _ => Multiplicative.ofAdd (1 : ZMod p)) with hdΩdef
  have hdΩE : dΩ ∈ E := by rw [← hτrange]; exact ⟨_, rfl⟩
  have hdactE : ∀ j, ∀ x ∈ U j,
      ((dΩ : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
        ((sgnElt e j false : ↥(orthDerived Q)) : V ≃ₗ[F] V) x := by
    intro j x hx
    have h := hτapply (fun _ => Multiplicative.ofAdd (1 : ZMod p)) j x hx
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    have hval : (ZMod.val (1 : ZMod p)) = 1 := by
      show (1 : ZMod p).val = 1
      rw [ZMod.val_one]
    simpa [sgnElt, hdΩdef, hval] using h
  have hdperp : ∀ x ∈ polarPerp Q (⨆ j, U j), ((dΩ : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x :=
    fun x hx => hF.toIsPlaneFrame.apply_eq_of_mem_polarPerp_iSup hdΩE hx
  obtain ⟨hdpow, hdodd, hdmem, hdcomp, hdmaps⟩ :=
    flip_primary_data hQ hp hp2 hpq hF htop j₀ (d := ((dΩ : ↥(orthDerived Q)) : V ≃ₗ[F] V))
      (ε := fun _ => false) (orthDerived_le_orthogonalGroup (Q := Q) dΩ.2) hdactE hdperp
  have hT := orthDerived_le_iSup_specialBlock (Q := Q) (U := U) (p := p) (k := k) hQ hk
    hF.toIsPlaneFrame.toIsPlaneSystem htop hp hp2 hpq hdodd hdmaps hdmem
    (framePoly_ne_X_sub_one t) hdcomp
  refine hT.trans (iSup_le fun d' => iSup_le fun hd' => ?_)
  obtain ⟨J, -, hd'O, hd'perp, hd'act⟩ := hd'
  have hactJ : ∀ j, ∀ x ∈ U j, d' x =
      ((sgnElt e j (decide (j ∈ J)) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x := by
    intro j x hx
    have h := hd'act j x hx
    by_cases hj : j ∈ J
    · rw [if_pos hj] at h
      rw [h]
      rw [show sgnElt e j (decide (j ∈ J)) = sgnElt e j true from by
        rw [decide_eq_true_eq.mpr hj]]
      rw [sgnElt_true]
      simp only [Subgroup.coe_inv]
      have hmem : ((e j : V ≃ₗ[F] V))⁻¹ x ∈ U j := apply_mem_sgnElt hF hp j true hx
      have hdx : ((dΩ : ↥(orthDerived Q)) : V ≃ₗ[F] V) (((e j : V ≃ₗ[F] V))⁻¹ x) = x := by
        rw [hdactE j _ hmem, sgnElt_false]
        simp
      change ((dΩ : ↥(orthDerived Q)) : V ≃ₗ[F] V).symm x =
        ((e j : V ≃ₗ[F] V))⁻¹ x
      rw [LinearEquiv.symm_apply_eq]
      exact hdx.symm
    · rw [if_neg hj] at h
      rw [h]
      rw [show sgnElt e j (decide (j ∈ J)) = sgnElt e j false from by
        rw [decide_eq_false_iff_not.mpr hj]]
      rw [sgnElt_false]
      exact hdactE j x hx
  obtain ⟨-, hd'odd, hd'mem, hd'comp, hd'maps⟩ :=
    flip_primary_data hQ hp hp2 hpq hF htop j₀ (d := d') (ε := fun j => decide (j ∈ J))
      hd'O hactJ hd'perp
  have hy : ∀ a b : Fin k, a ≠ b →
      ((sgnElt e a (decide (a ∈ J)) * sgnElt e b (decide (b ∈ J)) : ↥(orthDerived Q)) :
          V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
        (∀ x ∈ U a ⊔ U b,
          ((sgnElt e a (decide (a ∈ J)) * sgnElt e b (decide (b ∈ J)) : ↥(orthDerived Q)) :
            V ≃ₗ[F] V) x = d' x) ∧
        ∀ x ∈ polarPerp Q (U a ⊔ U b),
          ((sgnElt e a (decide (a ∈ J)) * sgnElt e b (decide (b ∈ J)) : ↥(orthDerived Q)) :
            V ≃ₗ[F] V) x = x := by
    intro a b hab
    refine ⟨?_, sgnElt_mul_apply_eq_of_acts hF hab _ _
      (fun x hx => hactJ a x hx) (fun x hx => hactJ b x hx) (hd'maps b),
      sgnElt_mul_apply_eq_one_of_perp hF hab _ _⟩
    exact orthDerived_le_orthogonalGroup (Q := Q)
      (sgnElt e a (decide (a ∈ J)) * sgnElt e b (decide (b ∈ J)) : ↥(orthDerived Q)).2
  have hPhan := specialBlock_le_iSup_specialBlock_pair (Q := Q) (U := U) (p := p)
    hQ hp hp2 hpq hF4 (by omega : 2 ≤ k) hF.toIsPlaneFrame.toIsPlaneSystem htop hd'odd hd'maps
    hd'mem (framePoly_ne_X_sub_one t) hd'comp
    (fun a b => ((sgnElt e a (decide (a ∈ J)) * sgnElt e b (decide (b ∈ J)) :
      ↥(orthDerived Q)) : V ≃ₗ[F] V)) hy
  refine hPhan.trans (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
  exact specialBlock_sgn_mul_le_iSup hQ hp hp2 hpq hF hab hF4 _ _

theorem iSup_pairBlock_ne_eq_top (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF4 : 4 ≤ Nat.card F) (hk : 3 ≤ k)
    (hF : IsCoherentFrame Q p U e E u c t) (htop : (⨆ j, U j : Submodule F V) = ⊤)
    (x₀ : OmPlusIdx k) :
    (⨆ (x : OmPlusIdx k) (_ : x ≠ x₀), pairBlock Q e t x.1.1.1 x.1.1.2 x.2) = ⊤ := by
  classical
  obtain ⟨xij, s⟩ := x₀
  obtain ⟨⟨i, j⟩, hij⟩ := xij
  set H : Subgroup ↥(orthDerived Q) :=
    ⨆ (x : OmPlusIdx k) (_ : x ≠ ((⟨(i, j), hij⟩, s) : OmPlusIdx k)),
      pairBlock Q e t x.1.1.1 x.1.1.2 x.2 with hH
  have hdim : Module.finrank F V = 2 * k := by
    have h1 := hF.toIsPlaneFrame.toIsPlaneSystem.finrank_biSup (Finset.univ : Finset (Fin k))
    have h2 : (⨆ j ∈ (Finset.univ : Finset (Fin k)), U j) = ⊤ := by rw [← htop]; simp
    rw [h2] at h1
    simpa [Finset.card_univ, Fintype.card_fin] using h1
  have hex : ∃ r : Fin k, r ≠ i ∧ r ≠ j := by
    by_contra h
    have h1 : ∀ r : Fin k, r = i ∨ r = j := by
      intro r
      by_cases hri : r = i
      · exact Or.inl hri
      · refine Or.inr (by_contra fun hrj => ?_)
        exact h ⟨r, hri, hrj⟩
    have hsub : (Finset.univ : Finset (Fin k)) ⊆ {i, j} := by
      intro r _
      rcases h1 r with h' | h'
      · simp [h']
      · simp [h']
    have h2 : k ≤ 2 := by
      calc k = Fintype.card (Fin k) := (Fintype.card_fin k).symm
        _ = (Finset.univ : Finset (Fin k)).card := by simp
        _ ≤ ({i, j} : Finset (Fin k)).card := Finset.card_le_card hsub
        _ ≤ 2 := by
            have := Finset.card_insert_le i ({j} : Finset (Fin k))
            simpa using this
    omega
  obtain ⟨r, hci, hcj⟩ := hex
  have hic : i ≠ r := fun h' => hci h'.symm
  have hjc : j ≠ r := fun h' => hcj h'.symm
  have hsw_mem : frameSwap Q e u c t j r ∈ orthDerived Q :=
    frameSwap_mem_orthDerived (a := j) (b := r) hQ hdim hk
  set sw : V ≃ₗ[F] V := frameSwap Q e u c t j r with hsw
  let g : ↥(orthDerived Q) := ⟨sw, hsw_mem⟩
  have hg_coe : ((g : ↥(orthDerived Q)) : V ≃ₗ[F] V) = sw := rfl
  have hsw_inv : sw⁻¹ = sw := by
    rw [inv_eq_iff_mul_eq_one]
    exact frameSwap_mul_self (a := j) (b := r) hF hjc
  have hg2 : g * g = 1 := by
    refine Subtype.ext ?_
    show sw * sw = 1
    exact frameSwap_mul_self (a := j) (b := r) hF hjc
  have hgP : ∀ x ∈ polarPerp Q (U j ⊔ U r), ((g : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x :=
    fun x hx => frameSwap_apply_of_mem_polarPerp (a := j) (b := r) hF hx
  have hleft : sw * (e j : V ≃ₗ[F] V) * sw = (e r : V ≃ₗ[F] V) :=
    frameSwap_conj_left (a := j) (b := r) hF hjc
  have hright : sw * (e r : V ≃ₗ[F] V) * sw = (e j : V ≃ₗ[F] V) :=
    frameSwap_conj_right (a := j) (b := r) hF hjc
  have hgy : g * (e j * cond false (e r)⁻¹ (e r) : ↥(orthDerived Q)) =
      (e j * cond false (e r)⁻¹ (e r) : ↥(orthDerived Q)) * g := by
    have hcond : (cond false (e r)⁻¹ (e r) : ↥(orthDerived Q)) = e r := rfl
    rw [hcond]
    refine Subtype.ext ?_
    show sw * ((e j : V ≃ₗ[F] V) * (e r : V ≃ₗ[F] V)) =
      ((e j : V ≃ₗ[F] V) * (e r : V ≃ₗ[F] V)) * sw
    have hsw2 : sw * sw = 1 := frameSwap_mul_self (a := j) (b := r) hF hjc
    have hleft' : sw * (e j : V ≃ₗ[F] V) * sw⁻¹ = (e r : V ≃ₗ[F] V) := by
      rw [hsw_inv]; exact hleft
    have hright' : sw * (e r : V ≃ₗ[F] V) * sw⁻¹ = (e j : V ≃ₗ[F] V) := by
      rw [hsw_inv]; exact hright
    have hconj2 : sw * ((e j : V ≃ₗ[F] V) * (e r : V ≃ₗ[F] V)) * sw =
        (e j : V ≃ₗ[F] V) * (e r : V ≃ₗ[F] V) := by
      have hconj3 : sw * ((e j : V ≃ₗ[F] V) * (e r : V ≃ₗ[F] V)) * sw⁻¹ =
          (e j : V ≃ₗ[F] V) * (e r : V ≃ₗ[F] V) := by
        have hcomm : (e r : V ≃ₗ[F] V) * (e j : V ≃ₗ[F] V) =
            (e j : V ≃ₗ[F] V) * (e r : V ≃ₗ[F] V) := by
          have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
            (commute_e hF r j).eq
          simpa using h
        rw [← MulAut.conj_apply (g := sw), map_mul, MulAut.conj_apply, MulAut.conj_apply,
          hleft', hright', hcomm]
      rwa [hsw_inv] at hconj3
    calc sw * ((e j : V ≃ₗ[F] V) * (e r : V ≃ₗ[F] V))
        = sw * ((e j : V ≃ₗ[F] V) * (e r : V ≃ₗ[F] V)) * (sw * sw) := by rw [hsw2, mul_one]
      _ = (sw * ((e j : V ≃ₗ[F] V) * (e r : V ≃ₗ[F] V)) * sw) * sw := by group
      _ = ((e j : V ≃ₗ[F] V) * (e r : V ≃ₗ[F] V)) * sw := by rw [hconj2]
  have hg_block : g ∈ pairBlock Q e t j r false :=
    mem_pairBlock_of_mul_self (a := j) (b := r) (s := false) hQ hp hp2 hpq hF hjc hgy hgP hg2
  have hne_jc : ({j, r} : Finset (Fin k)) ≠ {i, j} := by
    intro h'
    have h1 : r ∈ ({i, j} : Finset (Fin k)) := by rw [← h']; simp
    rw [Finset.mem_insert, Finset.mem_singleton] at h1
    exact h1.elim hci hcj
  have hne_ic : ({i, r} : Finset (Fin k)) ≠ {i, j} := by
    intro h'
    have h1 : r ∈ ({i, j} : Finset (Fin k)) := by rw [← h']; simp
    rw [Finset.mem_insert, Finset.mem_singleton] at h1
    exact h1.elim hci hcj
  have hidx_jc : pairIdx hjc false ≠ ((⟨(i, j), hij⟩, s) : OmPlusIdx k) :=
    pairIdx_ne_of_pair_ne hjc false hne_jc
  have hidx_ic : pairIdx hic s ≠ ((⟨(i, j), hij⟩, s) : OmPlusIdx k) :=
    pairIdx_ne_of_pair_ne hic s hne_ic
  have hgH : g ∈ H := by
    have hmem : g ∈ pairBlock Q e t (pairIdx hjc false).1.1.1 (pairIdx hjc false).1.1.2
        (pairIdx hjc false).2 := by
      rwa [pairBlock_pairIdx hQ hp hp2 hpq hF hjc hF4 false]
    exact (le_iSup₂ (f := fun x (_ : x ≠ ((⟨(i, j), hij⟩, s) : OmPlusIdx k)) =>
      pairBlock Q e t x.1.1.1 x.1.1.2 x.2) (pairIdx hjc false) hidx_jc) hmem
  have hB : pairBlock Q e t i r s ≤ H := by
    have hmem : pairBlock Q e t i r s =
        pairBlock Q e t (pairIdx hic s).1.1.1 (pairIdx hic s).1.1.2 (pairIdx hic s).2 :=
      (pairBlock_pairIdx hQ hp hp2 hpq hF hic hF4 s).symm
    rw [hmem]
    exact le_iSup₂ (f := fun x (_ : x ≠ ((⟨(i, j), hij⟩, s) : OmPlusIdx k)) =>
      pairBlock Q e t x.1.1.1 x.1.1.2 x.2) (pairIdx hic s) hidx_ic
  have hconj : (g * (e i * sgnElt e r s) * g⁻¹) = (e i * sgnElt e j s) := by
    refine Subtype.ext ?_
    show sw * ((e i * sgnElt e r s : ↥(orthDerived Q)) : V ≃ₗ[F] V) * sw⁻¹ =
      ((e i * sgnElt e j s : ↥(orthDerived Q)) : V ≃ₗ[F] V)
    simp only [Subgroup.coe_mul]
    have h1 : sw * (e i : V ≃ₗ[F] V) * sw = (e i : V ≃ₗ[F] V) :=
      frameSwap_conj_of_ne (a := j) (b := r) hF hjc (ne_of_lt hij) hic
    have h2 : sw * ((sgnElt e r s : ↥(orthDerived Q)) : V ≃ₗ[F] V) * sw =
        ((sgnElt e j s : ↥(orthDerived Q)) : V ≃ₗ[F] V) := by
      cases s
      · rw [sgnElt_false, sgnElt_false]
        exact hright
      · rw [sgnElt_true, sgnElt_true]
        simp only [Subgroup.coe_inv]
        calc sw * ((e r : V ≃ₗ[F] V))⁻¹ * sw
            = (sw * (e r : V ≃ₗ[F] V) * sw)⁻¹ := by
              rw [mul_inv_rev, mul_inv_rev, hsw_inv]
              group
          _ = ((e j : V ≃ₗ[F] V))⁻¹ := by rw [hright]
    have hstep : (sw * (e i : V ≃ₗ[F] V) * sw) *
        (sw * ((sgnElt e r s : ↥(orthDerived Q)) : V ≃ₗ[F] V) * sw) =
        sw * ((e i : V ≃ₗ[F] V) * ((sgnElt e r s : ↥(orthDerived Q)) : V ≃ₗ[F] V)) * sw := by
      have hsw2 : sw * sw = 1 := frameSwap_mul_self (a := j) (b := r) hF hjc
      calc (sw * (e i : V ≃ₗ[F] V) * sw) *
            (sw * ((sgnElt e r s : ↥(orthDerived Q)) : V ≃ₗ[F] V) * sw)
          = sw * (e i : V ≃ₗ[F] V) * (sw * sw) *
              ((sgnElt e r s : ↥(orthDerived Q)) : V ≃ₗ[F] V) * sw := by group
        _ = sw * (e i : V ≃ₗ[F] V) *
              ((sgnElt e r s : ↥(orthDerived Q)) : V ≃ₗ[F] V) * sw := by rw [hsw2, mul_one]
        _ = sw * ((e i : V ≃ₗ[F] V) *
              ((sgnElt e r s : ↥(orthDerived Q)) : V ≃ₗ[F] V)) * sw := by group
    rw [hsw_inv, ← hstep, h1, h2]
  have hS : specialBlock Q ((e i * sgnElt e j s : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t) =
      (specialBlock Q ((e i * sgnElt e r s : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        (framePoly t)).map (MulAut.conj sw) := by
    rw [← hconj]
    rw [show ((g * (e i * sgnElt e r s) * g⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
      sw * ((e i * sgnElt e r s : ↥(orthDerived Q)) : V ≃ₗ[F] V) * sw⁻¹ from by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]]
    exact specialBlock_conj (orthDerived_le_orthogonalGroup (Q := Q) hsw_mem) (framePoly t)
  have hmain : pairBlock Q e t i j s ≤ H := by
    intro p hp
    have hpS : ((p : V ≃ₗ[F] V)) ∈
        specialBlock Q ((e i * sgnElt e j s : ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t) :=
      Subgroup.mem_subgroupOf.mp hp
    rw [hS] at hpS
    obtain ⟨b₀, hb₀, hb₀eq⟩ := Subgroup.mem_map.mp hpS
    have hb₀eq' : sw * b₀ * sw⁻¹ = (p : V ≃ₗ[F] V) := by
      rw [← hb₀eq]
      rfl
    have hb₀Ω : b₀ ∈ orthDerived Q := by
      have hb₀' : b₀ = sw⁻¹ * (p : V ≃ₗ[F] V) * sw := by
        rw [← hb₀eq']
        group
      rw [hb₀']
      exact mul_mem (mul_mem (inv_mem hsw_mem) p.2) hsw_mem
    have hb : (⟨b₀, hb₀Ω⟩ : ↥(orthDerived Q)) ∈ pairBlock Q e t i r s :=
      Subgroup.mem_subgroupOf.mpr hb₀
    have hpH : p = g * (⟨b₀, hb₀Ω⟩ : ↥(orthDerived Q)) * g⁻¹ := by
      refine Subtype.ext ?_
      show (p : V ≃ₗ[F] V) = sw * b₀ * sw⁻¹
      rw [hb₀eq']
    rw [hpH]
    exact mul_mem (mul_mem hgH (hB hb)) (inv_mem hgH)
  have hle : ∀ x : OmPlusIdx k, pairBlock Q e t x.1.1.1 x.1.1.2 x.2 ≤ H := by
    intro x
    by_cases hx : x = ((⟨(i, j), hij⟩, s) : OmPlusIdx k)
    · rw [hx]
      exact hmain
    · exact (le_iSup₂ (f := fun x (_ : x ≠ ((⟨(i, j), hij⟩, s) : OmPlusIdx k)) =>
        pairBlock Q e t x.1.1.1 x.1.1.2 x.2) x hx)
  have hsup : (⨆ x : OmPlusIdx k, pairBlock Q e t x.1.1.1 x.1.1.2 x.2) ≤ H := iSup_le hle
  have hmap : H.map (orthDerived Q).subtype = orthDerived Q := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨h, -, rfl⟩
      exact h.2
    · refine (orthDerived_le_iSup_specialBlock_pair_frame (k := k) hQ hp hp2 hpq hF4 hk hF
        htop).trans ?_
      refine iSup_le fun x => ?_
      have hxs := specialBlock_pair_le_orthDerived (a := x.1.1.1) (b := x.1.1.2) hQ hp hp2 hpq hF
        (ne_of_lt x.1.2) hF4 x.2
      have h2 : (pairBlock Q e t x.1.1.1 x.1.1.2 x.2).map (orthDerived Q).subtype =
          specialBlock Q ((e x.1.1.1 * cond x.2 (e x.1.1.2)⁻¹ (e x.1.1.2) :
            ↥(orthDerived Q)) : V ≃ₗ[F] V) (framePoly t) := by
        unfold pairBlock
        rw [Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr (by simpa only [sgnElt] using hxs)]
      rw [← h2]
      exact (Subgroup.map_mono (le_iSup (fun x : OmPlusIdx k =>
        pairBlock Q e t x.1.1.1 x.1.1.2 x.2) x)).trans (Subgroup.map_mono hsup)
  refine eq_top_iff.mpr fun p _ => ?_
  have hp : ((p : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ H.map (orthDerived Q).subtype := by
    rw [hmap]; exact p.2
  obtain ⟨h, hh, hph⟩ := Subgroup.mem_map.mp hp
  have hEq : h = p := Subtype.ext hph
  rwa [hEq] at hh

end CFSG.StandardType.OmNsRootGen

end
