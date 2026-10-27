module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentPrim
import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField
import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUCompRoots
import CFSG.LieType.SeitzGeneration.OrthManyTwoPairs
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.SeitzGeneration.OrthExLift
import CFSG.LieType.SeitzGeneration.OrthNonsplitLow
import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual
import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.GroupTheory.WeirSylow

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem exists_coherentFrame {k : ℕ} {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)}
    {E : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e E) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hk : 1 ≤ k) :
    ∃ (e' : Fin k → ↥(orthDerived Q)) (u : Fin k → V) (c t : F),
      IsCoherentFrame Q p U e' E u c t ∧ ∀ j, e' j ∈ Subgroup.zpowers (e j) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hex : ∀ j : Fin k, ∃ h : F[X], h ∈ primaryFactors (e j : V ≃ₗ[F] V).toLinearMap ∧
      U j ≤ primaryComponent (e j : V ≃ₗ[F] V).toLinearMap h := by
    intro j
    obtain ⟨h, hh, hU⟩ := hF.exists_le_primaryComponent hp hp2 hpq (hF.mem j) j
    exact ⟨h, hh, hU⟩
  choose h hmem hU using hex
  have hirr : ∀ j, Irreducible (h j) := fun j => irreducible_of_mem_primaryFactors (hmem j)
  have hmon : ∀ j, (h j).Monic := fun j => monic_of_mem_primaryFactors (hmem j)
  have hne : ∀ j, h j ≠ X - 1 := by
    intro j hj
    obtain ⟨x, hxU, hx0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U j) (hF.finrank_eq j)
    have hxmem : x ∈ fixedSpace (e j : V ≃ₗ[F] V) := by
      rw [fixedSpace_eq_primaryComponent, ← hj]
      exact hU j hxU
    exact hx0 (hF.eq_zero_of_apply_eq j x hxU (mem_fixedSpace.mp hxmem))
  have hpow : ∀ j, (e j : V ≃ₗ[F] V) ^ p = 1 := by
    intro j
    have := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (hF.orderOf_eq j ▸ pow_orderOf_eq_one (e j))
    simpa using this
  have hdvd : ∀ j, h j ∣ (X ^ p - 1 : F[X]) := by
    intro j
    have hmin : minpoly F ((e j : V ≃ₗ[F] V).toLinearMap) ∣ (X ^ p - 1 : F[X]) := by
      refine minpoly.dvd F _ ?_
      rw [map_sub, map_pow, aeval_X, ← toLinearMap_pow, hpow j, map_one]
      exact sub_eq_zero.mpr rfl
    exact ((mem_primaryFactors.mp (hmem j)).2.2).trans hmin
  have hpK : (p : F) ≠ 0 := by
    intro h0
    have h1 := (ringChar.spec F p).mp h0
    have hℓ : (ringChar F).Prime := by rw [ringChar.eq F 2]; exact Nat.prime_two
    have hpl : p ≠ ringChar F := by rw [ringChar.eq F 2]; exact hp2
    rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
    · exact hℓ.one_lt.ne' h2
    · exact hpl h2.symm
  have hcyc : ∀ j, h j ∣ cyclotomic p F := fun j =>
    CoordSU.dvd_cyclotomic_of_dvd hp (hirr j) (hmon j) (by simpa using hdvd j) (hne j)
  have hdeg : ∀ j, (h j).natDegree = 2 := by
    intro j
    haveI : Fact (Irreducible (h j)) := ⟨hirr j⟩
    exact SpNS.natDegree_eq_two hp hp2 hpK (hcyc j) hpq
  have hcoeff0 : ∀ j, (h j).coeff 0 = 1 := by
    intro j
    haveI : Fact (Irreducible (h j)) := ⟨hirr j⟩
    have hnorm := SpNS.norm_root_eq_one hp hp2 hpK (hcyc j) hpq
    have hnorm_eq : Algebra.norm F (AdjoinRoot.root (h j)) = (h j).coeff 0 := by
      have h1 := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (CoordSL.rootPB (h j))
      rw [show (CoordSL.rootPB (h j)).gen = AdjoinRoot.root (h j) by simp [CoordSL.rootPB],
        SpNS.rootPB_dim_eq_two hp hp2 hpK (hcyc j) hpq,
        show minpoly F (AdjoinRoot.root (h j)) = h j by
          rw [AdjoinRoot.minpoly_root (hmon j).ne_zero, (hmon j).leadingCoeff, inv_one,
            C.map_one, mul_one]] at h1
      simpa using h1
    rw [← hnorm_eq, hnorm]
  have hform : ∀ j, h j = framePoly ((h j).coeff 1) := by
    intro j
    have h2 : (h j).coeff 2 = 1 := by
      rw [← hdeg j]
      exact (hmon j).coeff_natDegree
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' (p := h j) (n := 3) (by
      rw [hdeg j]; norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hcoeff0 j, h2, framePoly]
    simp only [map_one, one_mul, mul_one, pow_one, pow_zero]
    ring
  let j0 : Fin k := ⟨0, by omega⟩
  have hexm : ∀ j, ∃ m : ℕ, ¬ p ∣ m ∧ h j ∣ (h j0).comp (X ^ m) := fun j =>
    CFSG.LieType.SeitzGeneration.manyTwo_exists_dvd_comp_X_pow hp (hmon j0) (hmon j)
      (hirr j0) (hirr j) (hdvd j0) (hdvd j) (hne j0) (hne j)
  choose m hmcop hmdiv using hexm
  let e' : Fin k → ↥(orthDerived Q) := fun j => e j ^ m j
  have hcoe : ∀ j, (e' j : V ≃ₗ[F] V) = (e j : V ≃ₗ[F] V) ^ m j := fun j => by
    simp only [e', Subgroup.coe_pow]
  have hrelU : ∀ (j : Fin k) (x : V), x ∈ U j →
      (e' j : V ≃ₗ[F] V) ((e' j : V ≃ₗ[F] V) x) =
        ((h j0).coeff 1) • (e' j : V ≃ₗ[F] V) x + x := by
    intro j x hx
    have hxj : aeval ((e j : V ≃ₗ[F] V) : V →ₗ[F] V) (h j) x = 0 :=
      mem_primaryComponent.mp (hU j hx)
    have hcomp : aeval ((e j : V ≃ₗ[F] V) : V →ₗ[F] V) ((h j0).comp (X ^ m j)) x = 0 := by
      obtain ⟨q, hq⟩ := hmdiv j
      rw [hq, map_mul, Module.End.mul_apply]
      calc ((aeval ((e j : V ≃ₗ[F] V) : V →ₗ[F] V)) (h j))
            (((aeval ((e j : V ≃ₗ[F] V) : V →ₗ[F] V)) q) x)
          = (((aeval ((e j : V ≃ₗ[F] V) : V →ₗ[F] V)) (h j)) *
              ((aeval ((e j : V ≃ₗ[F] V) : V →ₗ[F] V)) q)) x :=
            (Module.End.mul_apply _ _ _).symm
        _ = (((aeval ((e j : V ≃ₗ[F] V) : V →ₗ[F] V)) q) *
              ((aeval ((e j : V ≃ₗ[F] V) : V →ₗ[F] V)) (h j))) x := by
            rw [← map_mul, ← map_mul, mul_comm]
        _ = ((aeval ((e j : V ≃ₗ[F] V) : V →ₗ[F] V)) q)
              (((aeval ((e j : V ≃ₗ[F] V) : V →ₗ[F] V)) (h j)) x) :=
            Module.End.mul_apply _ _ _
        _ = 0 := by rw [hxj, LinearMap.map_zero]
    have hcomp2 : aeval (((e j : V ≃ₗ[F] V) : V →ₗ[F] V) ^ m j) (h j0) x = 0 := by
      rwa [Polynomial.aeval_comp, map_pow, aeval_X] at hcomp
    rw [hform j0] at hcomp2
    have hcoe' : ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) =
        ((e j : V ≃ₗ[F] V) : V →ₗ[F] V) ^ m j := by
      rw [hcoe j]
      exact toLinearMap_pow _ _
    have hcomp3 : aeval ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V)
        (framePoly ((h j0).coeff 1)) x = 0 := by
      rw [hcoe']
      exact hcomp2
    have hpoly : (aeval ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V)
        (framePoly ((h j0).coeff 1)) : Module.End F V) =
        ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) ^ 2 +
          ((h j0).coeff 1) • ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) + 1 := by
      simp [framePoly, map_add, map_mul, map_pow, Algebra.smul_def]
    have h0x : ((((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) ^ 2 +
        ((h j0).coeff 1) • ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) + 1 : Module.End F V)) x = 0 := by
      rw [← hpoly]
      exact hcomp3
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at h0x
    rw [pow_two, Module.End.mul_apply, add_assoc] at h0x
    have hEq : ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) (((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) x) =
        ((h j0).coeff 1) • ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) x + x := by
      have h0' : ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V)
            (((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) x) +
            (((h j0).coeff 1) • ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) x + x) =
          (((h j0).coeff 1) • ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) x + x) +
            (((h j0).coeff 1) • ((e' j : V ≃ₗ[F] V) : V →ₗ[F] V) x + x) := by
        rw [h0x, ← two_smul F, CharTwo.two_eq_zero, zero_smul]
      exact add_right_cancel h0'
    simpa using hEq
  choose v hvU hv0 using fun j =>
    exists_ne_zero_mem_of_finrank_eq_two (U j) (hF.finrank_eq j)
  have hQv : ∀ j, Q (v j) ≠ 0 := by
    intro j h0
    have hplus : IsPlusType (Q.comp (U j).subtype) := by
      refine ⟨Submodule.span F {⟨v j, hvU j⟩}, ?_, ?_⟩
      · rw [finrank_span_singleton (show (⟨v j, hvU j⟩ : U j) ≠ 0 from fun h1 =>
          hv0 j (congrArg Subtype.val h1)), hF.finrank_eq j]
      · rintro y hy
        rw [Submodule.mem_span_singleton] at hy
        obtain ⟨a, rfl⟩ := hy
        change Q (a • v j) = 0
        rw [QuadraticMap.map_smul, h0, smul_zero]
    exact hF.not_isPlusType j hplus
  let c : F := Q (v j0)
  have hc : c ≠ 0 := hQv j0
  have hs : ∀ j, ∃ s : F, s ^ 2 * Q (v j) = c := by
    intro j
    obtain ⟨s, hs⟩ := (isSquare_of_charTwo' (c / Q (v j))).exists_sq
    refine ⟨s, ?_⟩
    rw [← hs]
    exact div_mul_cancel₀ c (hQv j)
  choose s hs using hs
  let u : Fin k → V := fun j => s j • v j
  have huU : ∀ j, u j ∈ U j := fun j => Submodule.smul_mem _ _ (hvU j)
  have hQu : ∀ j, Q (u j) = c := by
    intro j
    rw [show u j = s j • v j from rfl, QuadraticMap.map_smul]
    simpa [pow_two, smul_eq_mul] using hs j
  have ht : (h j0).coeff 1 ≠ 0 := by
    have hpoly : (X ^ 2 - C ((h j0).coeff 1) * X + 1 : F[X]) = framePoly ((h j0).coeff 1) := by
      rw [framePoly, sub_eq_add_neg, CharTwo.neg_eq]
    have hpoly' : (X ^ 2 - C ((h j0).coeff 1) * X + 1 : F[X]) = h j0 :=
      hpoly.trans (hform j0).symm
    refine CFSG.LieType.SeitzGeneration.manyTwo_tau_ne_zero hp hp2 (τ := (h j0).coeff 1) ?_ ?_ ?_ ?_
    · rw [hpoly']
      exact hmon j0
    · rw [hpoly']
      exact hirr j0
    · rw [hpoly']
      exact hdvd j0
    · rw [hpoly']
      exact hne j0
  have hframe : IsPlaneFrame Q p U e' E := by
    refine { hF with
      orderOf_eq := ?_
      apply_of_perp := ?_
      maps_to := ?_
      eq_zero_of_apply_eq := ?_
      closure_eq := ?_ }
    · intro j
      have hpowj : (e j) ^ p = 1 := hF.orderOf_eq j ▸ pow_orderOf_eq_one (e j)
      have hpow' : (e' j) ^ p = 1 := by
        rw [show e' j = e j ^ m j from rfl, ← pow_mul, mul_comm (m j) p, pow_mul, hpowj,
          one_pow]
      have hne' : e' j ≠ 1 := by
        intro h1
        have h1' : (e j) ^ m j = 1 := by rw [← h1]
        have hdvdm : orderOf (e j) ∣ m j := orderOf_dvd_iff_pow_eq_one.2 h1'
        rw [hF.orderOf_eq j] at hdvdm
        exact hmcop j hdvdm
      exact orderOf_eq_prime hpow' hne'
    · intro j x hx
      rw [show (e' j : V ≃ₗ[F] V) = (e j : V ≃ₗ[F] V) ^ m j from hcoe j]
      have hfix : ∀ n : ℕ, ((e j : V ≃ₗ[F] V) ^ n) x = x := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, LinearEquiv.mul_apply, hF.apply_of_perp j x hx, ih]
      exact hfix (m j)
    · intro j x hx
      rw [show (e' j : V ≃ₗ[F] V) = (e j : V ≃ₗ[F] V) ^ m j from hcoe j]
      have hmap : ∀ n : ℕ, ∀ y ∈ U j, ((e j : V ≃ₗ[F] V) ^ n) y ∈ U j := by
        intro n
        induction n with
        | zero => intro y hy; simpa using hy
        | succ n ih =>
          intro y hy
          rw [pow_succ, LinearEquiv.mul_apply]
          exact ih _ (hF.maps_to j y hy)
      exact hmap (m j) x hx
    · intro j x hx hfix
      have hrel := hrelU j x hx
      rw [hfix, hfix] at hrel
      have htx : ((h j0).coeff 1) • x = 0 := by
        have h2 : ((h j0).coeff 1) • x + x = 0 + x := by simpa using hrel.symm
        exact add_right_cancel h2
      exact (smul_eq_zero.mp htx).resolve_left ht
    · apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        exact E.pow_mem (hF.mem j) (m j)
      · rw [← hF.closure_eq, Subgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        have hmem : e j ∈ Subgroup.zpowers (e' j) := by
          have hcop : Nat.Coprime (m j) p := (hp.coprime_iff_not_dvd.2 (hmcop j)).symm
          obtain ⟨n, -, hn⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
          have hgen : (e j) ^ (m j * n) = e j := by
            rw [pow_eq_pow_mod (m j * n) (hF.orderOf_eq j ▸ pow_orderOf_eq_one (e j)), hn,
              pow_one]
          have hgen' : (e' j) ^ n = e j := by
            rw [show e' j = e j ^ m j from rfl, ← pow_mul, hgen]
          refine (Subgroup.mem_zpowers_iff (g := e' j) (h := e j)).2 ?_
          refine ⟨(n : ℤ), ?_⟩
          rw [zpow_natCast]
          exact hgen'
        exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_range_self j)) hmem
  have hpolar : ∀ a, QuadraticMap.polar Q (u a) ((e' a : V ≃ₗ[F] V) (u a)) =
      ((h j0).coeff 1) * c := by
    intro a
    have hmemO : (e' a : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      orthDerived_le_orthogonalGroup (Q := Q) (e' a).2
    have hQw : Q ((e' a : V ≃ₗ[F] V) (u a)) = c := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hmemO, hQu a]
    have hQww : Q ((e' a : V ≃ₗ[F] V) ((e' a : V ≃ₗ[F] V) (u a))) = c := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hmemO, hQw]
    have hrot := hrelU a (u a) (huU a)
    have hQexp : Q (((h j0).coeff 1) • ((e' a : V ≃ₗ[F] V) (u a)) + u a) =
        ((h j0).coeff 1) ^ 2 * c +
          ((h j0).coeff 1) * QuadraticMap.polar Q ((e' a : V ≃ₗ[F] V) (u a)) (u a) + c := by
      rw [QuadraticMap.map_add (⇑Q) _ _, QuadraticMap.map_smul Q ((h j0).coeff 1)
        ((e' a : V ≃ₗ[F] V) (u a)), hQw, hQu a, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_right]
      simp only [smul_eq_mul]
      ring
    have h1 : ((h j0).coeff 1) ^ 2 * c +
        ((h j0).coeff 1) * QuadraticMap.polar Q ((e' a : V ≃ₗ[F] V) (u a)) (u a) + c = c := by
      rw [← hQexp, ← hrot]
      exact hQww
    have h2 : ((h j0).coeff 1) ^ 2 * c +
        ((h j0).coeff 1) *
          QuadraticMap.polar Q ((e' a : V ≃ₗ[F] V) (u a)) (u a) = 0 := by
      have := congrArg (fun z => z + c) h1
      simpa [add_assoc, CharTwo.add_self_eq_zero] using this
    have h3 : ((h j0).coeff 1) *
        (((h j0).coeff 1) * c +
          QuadraticMap.polar Q ((e' a : V ≃ₗ[F] V) (u a)) (u a)) = 0 := by
      simpa [mul_add, mul_assoc, _root_.sq] using h2
    have h4 : ((h j0).coeff 1) * c +
        QuadraticMap.polar Q ((e' a : V ≃ₗ[F] V) (u a)) (u a) = 0 :=
      (mul_eq_zero.mp h3).resolve_left ht
    have h5 : QuadraticMap.polar Q ((e' a : V ≃ₗ[F] V) (u a)) (u a) =
        ((h j0).coeff 1) * c := (CharTwo.add_eq_zero.mp h4).symm
    rw [QuadraticMap.polar_comm]
    exact h5
  refine ⟨e', u, c, (h j0).coeff 1, ?_, ?_⟩
  · exact ⟨hframe, huU, hQu, hc, ht, fun a => hrelU a (u a) (huU a), hpolar⟩
  · intro j
    refine (Subgroup.mem_zpowers_iff (g := e j) (h := e' j)).2 ?_
    refine ⟨(m j : ℤ), ?_⟩
    rw [zpow_natCast]

end CFSG.StandardType.OmNsRootGen

end
