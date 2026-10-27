module

public import CFSG.LocalAnalysis.StandardType.GGKGWeylRootFacts
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Ad
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedCells
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.LieType.Chevalley.LangRootRankOne

public section

namespace CFSG.StandardType.KGL.TwLayer

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest CFSG.SeitzReduction
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.KGL

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem smul_eq_zero_of_ne {c : ZMod 3} {v : Fin Tag.E6.rank → ZMod 3} (hv : v ≠ 0)
    (h : c • v = 0) : c = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have h2 := congrFun h i
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h2
  exact (mul_eq_zero.mp h2).resolve_right hi

theorem zetaVec_apply_pow_three {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (x : Fin Tag.E6.rank → ZMod 3) (i : Fin Tag.E6.rank) : zetaVec ζ hζ x i ^ 3 = 1 := by
  have h : zetaVec ζ hζ x ^ 3 = 1 := by
    funext i
    simp only [Pi.pow_apply, zetaVec_apply]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow]
    rfl
  exact congrFun h i

section Roots


private theorem iform_E6_self_eq_two {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [hj]
  simp [Tag.symmetrizer, Matrix.one_apply_eq]

private theorem sum_mul_kgExpVec (x y : Fin Tag.E6.rank → ℤ) :
    (∑ j, ((x j : ℤ) : ZMod 3) * (kgExpVec y) j) = ((iform x y : ℤ) : ZMod 3) :=
  rootPair_kgExpVec x y

private theorem adAct_rootReflection_eq {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (y : Fin Tag.E6.rank → ZMod 3) :
    adAct Tag.E6 3 (rootReflection γ) y =
      y - (∑ j, ((γ j : ℤ) : ZMod 3) * y j) • kgExpVec γ :=
  adAct_rootReflection_eq_rootRefl hγ y

theorem adAct_conj_ne {α γ μ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hμ : IsRoot Tag.E6 μ)
    (hμα : iform μ α = 0) (hγα : ((iform γ α : ℤ) : ZMod 3) ≠ 0)
    (hμγ : ((iform μ γ : ℤ) : ZMod 3) ≠ 0) :
    adAct Tag.E6 3 (rootReflection γ * rootReflection μ * (rootReflection γ)⁻¹) (kgExpVec α) ≠
      kgExpVec α := by
  intro h
  have hsq : rootReflection γ * rootReflection γ = (1 : WeylGroup Tag.E6) := by
    have := mul_inv_cancel (rootReflection γ)
    rwa [rootReflection_inv hγ] at this
  have hinv : ∀ y, adAct Tag.E6 3 (rootReflection γ) (adAct Tag.E6 3 (rootReflection γ) y) = y :=
    fun y => by rw [← adAct_mul, hsq, adAct_one]
  rw [rootReflection_inv hγ, adAct_mul, adAct_mul] at h
  set y1 := adAct Tag.E6 3 (rootReflection γ) (kgExpVec α) with hy1
  have h' : adAct Tag.E6 3 (rootReflection μ) y1 = y1 := by
    have h2 := congrArg (adAct Tag.E6 3 (rootReflection γ)) h
    rwa [hinv] at h2
  rw [adAct_rootReflection_eq hμ] at h'
  have hb : (∑ j, ((μ j : ℤ) : ZMod 3) * y1 j) • kgExpVec μ = 0 := sub_eq_self.mp h'
  have hz := smul_eq_zero_of_ne (kgExpVec_ne_zero hμ) hb
  have hsum : (∑ j, ((μ j : ℤ) : ZMod 3) * y1 j) =
      ((iform μ α : ℤ) : ZMod 3) - ((iform γ α : ℤ) : ZMod 3) * ((iform μ γ : ℤ) : ZMod 3) := by
    rw [hy1, adAct_rootReflection_eq hγ]
    have e1 : (∑ j, ((μ j : ℤ) : ZMod 3) *
          (kgExpVec α - (∑ k, ((γ k : ℤ) : ZMod 3) * kgExpVec α k) • kgExpVec γ) j) =
        (∑ j, ((μ j : ℤ) : ZMod 3) * kgExpVec α j) - (∑ k, ((γ k : ℤ) : ZMod 3) * kgExpVec α k) *
          (∑ j, ((μ j : ℤ) : ZMod 3) * kgExpVec γ j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, sum_mul_kgExpVec, sum_mul_kgExpVec, sum_mul_kgExpVec]
  rw [hsum, hμα, Int.cast_zero, zero_sub, neg_eq_zero] at hz
  exact (mul_ne_zero hγα hμγ) hz

private def gamma0 : Fin Tag.E6.rank → ℤ := ![-1, -1, -2, -2, -1, 0]

private theorem isRoot_gamma0 : IsRoot Tag.E6 gamma0 := by
  rw [← mem_rootFinset]
  decide +kernel

theorem exists_root_pair_kgL4 {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (hαβ : iform α β = 0) :
    ∃ γ μ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ IsRoot Tag.E6 μ ∧
      ((iform γ α + iform γ β : ℤ) : ZMod 3) = 0 ∧ ((iform γ α : ℤ) : ZMod 3) ≠ 0 ∧
      iform μ α = 0 ∧ iform μ β = 0 ∧ ((iform μ γ : ℤ) : ZMod 3) ≠ 0 := by
  obtain ⟨w, hwθ, hwα⟩ := exists_weyl_smul_orthPair hα hβ hαβ
  have hμ0 : IsRoot Tag.E6 (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) := IsRoot.basis 2
  have e1 : iform (w • gamma0) α = iform gamma0 (highRoot Tag.E6) := by
    rw [← hwθ, iform_smul]
  have e2 : iform (w • gamma0) β = iform gamma0 (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) := by
    rw [← hwα, iform_smul]
  have e3 : iform (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) α =
      iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (highRoot Tag.E6) := by
    rw [← hwθ, iform_smul]
  have e4 : iform (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) β =
      iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) := by
    rw [← hwα, iform_smul]
  have e5 : iform (w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) (w • gamma0) =
      iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) gamma0 := iform_smul w _ _
  refine ⟨w • gamma0, w • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ), IsRoot.smul isRoot_gamma0 w,
    IsRoot.smul hμ0 w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, e2]
    decide +kernel
  · rw [e1]
    decide +kernel
  · rw [e3]
    decide +kernel
  · rw [e4]
    decide +kernel
  · rw [e5]
    decide +kernel

theorem rootDiagUnit_zetaVec_kgExpVec_add_ne_one {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hαβ : iform α β = 0) :
    rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α + kgExpVec β)) ≠ 1 := by
  have hnum : ¬ ((0 : ZMod 3) = ((2 : ℤ) : ZMod 3) + ((0 : ℤ) : ZMod 3)) := by decide +kernel
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  have h' : zetaVec ζ hζ (kgExpVec α + kgExpVec β) = 1 :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)
  have h0 : zetaVec ζ hζ (0 : Fin Tag.E6.rank → ZMod 3) = 1 := by
    funext i
    simp [zetaVec_apply]
  have hx0 : kgExpVec α + kgExpVec β = 0 := zetaVec_injective hζo hζ (h'.trans h0.symm)
  have hs : (∑ j, ((α j : ℤ) : ZMod 3) * (kgExpVec α + kgExpVec β) j) =
      ((iform α α : ℤ) : ZMod 3) + ((iform α β : ℤ) : ZMod 3) := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [sum_mul_kgExpVec, sum_mul_kgExpVec]
  have hs0 : (∑ j, ((α j : ℤ) : ZMod 3) * (kgExpVec α + kgExpVec β) j) = 0 := by
    rw [hx0]
    simp
  rw [hs0, iform_E6_self_eq_two hα, hαβ] at hs
  exact hnum hs

end Roots

section Monomial

theorem monomial_conj_rootDiagUnit_zetaVec {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    {j : ModGL Tag.E6 L} (hj : j ∈ monomialSubgroup Tag.E6 L) {w : WeylGroup Tag.E6}
    (hjw : MapsRootLines j w) (x : Fin Tag.E6.rank → ZMod 3) :
    j * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * j⁻¹ =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ (adAct Tag.E6 3 w x)) := by
  rw [monomial_conj_rootDiagUnit_weylTuple hj hjw, weylTuple_zetaVec]

theorem rootSL2_WSL_monomial_mapsRootLines {L : Type} [Field L] {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) :
    rootSL2 Tag.E6 L γ WSL ∈ monomialSubgroup Tag.E6 L ∧
      MapsRootLines (rootSL2 Tag.E6 L γ WSL) (rootReflection γ) := by
  have e : rootWeylOne Tag.E6 L γ = rootSL2 Tag.E6 L γ WSL := by
    simp only [rootWeylOne, rootWeylSL2, nSL_one]
  obtain ⟨-, hmono, hmaps⟩ := rootWeylOne_spec (τ := Tag.E6) (K := L) hγ
  rw [e] at hmono hmaps
  exact ⟨hmono, hmaps⟩

theorem rootSL2_WSL_commute_rootDiagUnit_zetaVec {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    {α β γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hSig : ((iform γ α + iform γ β : ℤ) : ZMod 3) = 0) :
    rootSL2 Tag.E6 L γ WSL * rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α + kgExpVec β)) =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α + kgExpVec β)) * rootSL2 Tag.E6 L γ WSL := by
  obtain ⟨hmono, hmaps⟩ := rootSL2_WSL_monomial_mapsRootLines (L := L) hγ
  have h := monomial_conj_rootDiagUnit_zetaVec hζ hmono hmaps (kgExpVec α + kgExpVec β)
  have hfix : adAct Tag.E6 3 (rootReflection γ) (kgExpVec α + kgExpVec β) =
      kgExpVec α + kgExpVec β := by
    rw [adAct_rootReflection_eq hγ]
    have hs : (∑ j, ((γ j : ℤ) : ZMod 3) * (kgExpVec α + kgExpVec β) j) = 0 := by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [sum_mul_kgExpVec, sum_mul_kgExpVec]
      push_cast at hSig
      exact hSig
    rw [hs, zero_smul, sub_zero]
  rw [hfix] at h
  exact mul_inv_eq_iff_eq_mul.1 h

end Monomial

end CFSG.StandardType.KGL.TwLayer

end
