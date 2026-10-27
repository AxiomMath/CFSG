module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.ClassicalInvolution.ModelFacts.CentralLift
public import CFSG.LieType.Steinberg.Classical.SpinPlus
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Steinberg.CentralExt.TorusLift
public import CFSG.LieType.Steinberg.CentralExt.Unipotent
import all CFSG.LieType.Universal.Spin.Structure.TypeD
import CFSG.LieType.Universal.Spin.Structure.Levels
import CFSG.LieType.Universal.Spin.Structure.Entries

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.ClassicalInvolution.ModelFacts

namespace GGRootSpinPlus

variable {n : ℕ} {K : Type} [Field K]

theorem bruhatExtras [Finite K] (hn : 3 ≤ n) :
    BruhatExtras (plusDatum n K hn) (fun k => (torusD K hn k).range) := by
  have hct := SpinPlus.isCTGroupDatum (K := K) hn
  have hext := plusDatum_steinbergExtras (K := K) hn
  obtain ⟨p, _, _⟩ := CFSG.LieType.Steinberg.CentralExt.TorusLift.exists_prime_charP (k := K)
  refine ⟨eq_bot_iff.2 fun x hx => ?_⟩
  obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  have hneg := idBelow_of_mem_iSup (K := K) hn (-1) _ (fun γ hγ => ⟨hγ.1, by
      have : ht (ι := Fin n) γ < 0 := hγ.2
      omega⟩) hxN
  obtain ⟨t, htT, u, hu, htu⟩ := (Set.ext_iff.1 (coe_borel hct) x).1 hxB
  have htu' : t * u = x := htu
  subst htu'
  have hD : (spinMat (quadPlus n K) t).IsDiag := isDiag_of_mem_iSup hn htT
  have hpos := idBelow_of_mem_iSup (K := K) hn 1 _ (fun γ hγ => ⟨hγ.1, by
      have : 0 < ht (ι := Fin n) γ := hγ.2
      omega⟩) hu
  have hdiag : ∀ a, spinMat (quadPlus n K) (t * u) a a = spinMat (quadPlus n K) t a a := by
    intro a
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hpos a a (by simp), Matrix.one_apply_eq, mul_one]
    · intro c _ hca
      rw [hD (Ne.symm hca), zero_mul]
    · simp
  have ht1 : spinMat (quadPlus n K) t = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [← hdiag a]
      exact hneg a a (by simp)
    · rw [hD hab, Matrix.one_apply_ne hab]
  have hxu : spinMat (quadPlus n K) (t * u) = spinMat (quadPlus n K) u := by
    rw [map_mul, ht1, one_mul]
  have hu1 : spinMat (quadPlus n K) u = 1 :=
    eq_one_of_idBelow_one_of_idBelow_neg_one _ hpos (hxu ▸ hneg)
  have hu' : u = 1 := eq_one_of_mem_posPart hn hu hu1
  subst hu'
  rw [mul_one] at hxN ⊢
  rcases eq_one_or_eq_neg_one_of_spinAction_eq_one n K t
    (spinAction_eq_one_of_spinMat_eq_one ht1) with h | h
  · exact Subtype.ext h
  · have hsq : t ^ 2 = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, h, OneMemClass.coe_one]
      simp)
    have hU : IsPGroup p ↥(negUnipotent (plusDatum n K hn)) := by
      refine (isPGroup_iSup_posSet hext
        (fun γ hγ => isPGroup_of_isParametrization (SpinPlus.isParametrization hn) hγ)
        (-htHom)).to_le (iSup₂_le fun γ hγ => le_iSup₂_of_le γ ⟨hγ.1, ?_⟩ le_rfl)
      exact neg_pos.2 hγ.2
    obtain ⟨k, hk⟩ := hU ⟨t, hxN⟩
    have htp : t ^ p ^ k = 1 := congrArg Subtype.val hk
    by_cases hp2 : p = 2
    · subst hp2
      have h20 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
      apply Subtype.ext
      rw [h, Submonoid.coe_one, neg_one_eq_one_of_two_eq_zero _ h20]
    · have hcop : Nat.Coprime (p ^ k) 2 :=
        Nat.Coprime.pow_left k ((Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp2)
      have h1 : orderOf t ∣ Nat.gcd (p ^ k) 2 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one htp) (orderOf_dvd_of_pow_eq_one hsq)
      rw [hcop] at h1
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

theorem ggRootSylowCentral_spinPlus [Finite K] [CharP K 2] (hn : 3 ≤ n) (t : StatedLieTag) :
    GGRootSylowCentral (plusDatum n K hn) t := by
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n K)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (coe_ker_spinMatrix_quadPlus (n := n) (K := K))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ggRootSylowCentral_of_longRoot_reduced (SpinPlus.isCTGroupDatum hn)
    (plusDatum_steinbergExtras hn) (bruhatExtras hn) rfl
    (fun γ hγ => isPGroup_of_isParametrization (SpinPlus.isParametrization hn) hγ)
    (coprime_two_card_iSup_range_units (fun i => torusD K hn i)
      fun i j h hh h' hh' => (plusDatum_steinbergExtras hn).torus_commute i j h hh h' hh')
    (fun γ₀ hγ₀ _ => mul_comm_of_isParametrization (SpinPlus.isParametrization hn) hγ₀)
    fun γ hγ => ggLongRoot_of_symmetric (isIrreducible_cartanD hn)
      (CFSG.ClassicalInvolution.ModelFacts.cartanD_symm n) rfl hγ.1

end GGRootSpinPlus

end CFSG.StandardType
