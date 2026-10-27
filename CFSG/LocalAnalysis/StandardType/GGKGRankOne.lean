module

public import CFSG.LocalAnalysis.StandardType.GGKGAdjDefs
public import CFSG.LocalAnalysis.StandardType.GGKGOrthPairs
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZRootTorus
import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedCells

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest CFSG.SeitzReduction
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


private theorem iform_E6_self_eq_two {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [hj]
  simp [Tag.symmetrizer, Matrix.one_apply_eq]

private theorem iform_E6_single_right (x : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    iform x (Pi.single i 1) = (Tag.E6.cartan.mulVec x) i := by
  rw [iform_single_right]
  simp only [Tag.symmetrizer, Matrix.one_apply_eq, one_mul]
  simp [Matrix.mulVec, dotProduct]

private theorem kgExpVec_eq_cast_iform (x : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    kgExpVec x i = ((iform x (Pi.single i 1) : ℤ) : ZMod 3) := by
  simp only [kgExpVec]
  rw [← iform_E6_single_right x i]

private theorem zpow_val_eq_zpow {G : Type} [Group G] {ζ : G} (hζ : ζ ^ 3 = 1) (m : ℤ) :
    ζ ^ ((m : ZMod 3).val) = ζ ^ m := by
  rw [zpow_eq_zpow_emod' (x := ζ) m hζ, ← ZMod.val_intCast (n := 3) m, zpow_natCast]

private theorem zetaVec_kgExpVec_corootPair {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    zetaVec ζ hζ (kgExpVec γ) =
      fun i => ζ ^ (2 * iform γ (Pi.single i 1) / iform γ γ) := by
  funext i
  rw [zetaVec_apply, kgExpVec_eq_cast_iform]
  have hdiv : 2 * iform γ (Pi.single i 1) / iform γ γ = iform γ (Pi.single i 1) := by
    rw [iform_E6_self_eq_two hγ]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [hdiv]
  exact zpow_val_eq_zpow hζ (iform γ (Pi.single i 1))

theorem kgAdjL3ii : KGAdjL3ii := by
  intro K _ _ hchar ζ hζ hζo α β γ hα hβ hαβ hγ hγα hγβ
  obtain ⟨hL, -⟩ := exceptional_Lang_root_rank_one_torus_transport Tag.E6 K hγ
  have hdiag : rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec γ)) = rootTorusSL2 Tag.E6 K γ ζ := by
    rw [zetaVec_kgExpVec_corootPair hζ hγ]
    exact (rootTorusSL2_eq_rootDiagUnit_corootPair hγ ζ).symm
  rw [hdiag]
  have hmem : rootTorusSL2 Tag.E6 K γ ζ ∈ rootRankOneGroup Tag.E6 K γ := ⟨HSL ζ, rfl⟩
  rw [hL] at hmem
  have hS : famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)} =
      {δ | IsRoot Tag.E6 δ ∧ iform δ α = 0 ∧ iform δ β = 0} :=
    famKernel_kgExpVec_pair hζo hζ hα hβ
  have hγS : γ ∈ famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)} := by
    rw [hS]
    exact ⟨hγ, hγα, hγβ⟩
  have hnegS : -γ ∈ famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)} := by
    rw [hS]
    refine ⟨IsRoot.neg hγ, ?_, ?_⟩
    · rw [iform_neg_left, hγα, neg_zero]
    · rw [iform_neg_left, hγβ, neg_zero]
  exact (sup_le (rootSubgroup_le_rootSpan hγS) (rootSubgroup_le_rootSpan hnegS)) hmem

private theorem sum_mul_kgExpVec (x y : Fin Tag.E6.rank → ℤ) :
    (∑ j, ((x j : ℤ) : ZMod 3) * (kgExpVec y) j) = ((iform x y : ℤ) : ZMod 3) := by
  rw [iform_E6_eq x y]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [kgExpVec]

private theorem corootPair_E6_single_eq_kgExpVec {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (i : Fin Tag.E6.rank) :
    ((corootPair γ (Pi.single i 1) : ℤ) : ZMod 3) = kgExpVec γ i := by
  have hmul := corootPair_mul hγ (Pi.single i 1)
  rw [iform_E6_self_eq_two hγ] at hmul
  have hc : corootPair γ (Pi.single i 1) = iform γ (Pi.single i 1) := by
    have h2 : corootPair γ (Pi.single i 1) * 2 = iform γ (Pi.single i 1) * 2 := by
      rw [hmul]; ring
    exact mul_right_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2
  rw [hc, kgExpVec_eq_cast_iform γ i]

private theorem adAct_rootReflection_eq {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (y : Fin Tag.E6.rank → ZMod 3) :
    adAct Tag.E6 3 (rootReflection γ) y =
      y - (∑ j, ((γ j : ℤ) : ZMod 3) * y j) • kgExpVec γ := by
  funext i
  rw [adAct, rootReflection_inv hγ, rootReflection_smul hγ (Pi.single i 1)]
  have hsplit : (∑ j, ((((Pi.single i 1 : Fin Tag.E6.rank → ℤ) -
          corootPair γ (Pi.single i 1) • γ) j : ℤ) : ZMod 3) * y j) =
      (∑ j, (((Pi.single i 1 : Fin Tag.E6.rank → ℤ) j : ℤ) : ZMod 3) * y j) -
        (∑ j, (((corootPair γ (Pi.single i 1) • γ) j : ℤ) : ZMod 3) * y j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.sub_apply, Int.cast_sub, sub_mul]
  have hfirst : (∑ j, (((Pi.single i 1 : Fin Tag.E6.rank → ℤ) j : ℤ) : ZMod 3) * y j) = y i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_apply, hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hsecond : (∑ j, (((corootPair γ (Pi.single i 1) • γ) j : ℤ) : ZMod 3) * y j) =
      ((corootPair γ (Pi.single i 1) : ℤ) : ZMod 3) *
        (∑ j, ((γ j : ℤ) : ZMod 3) * y j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    ring
  rw [hsplit, hfirst, hsecond, corootPair_E6_single_eq_kgExpVec hγ i]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem kgAdjL4 : KGAdjL4 := by
  intro K _ _ hchar ζ hζ hζo α β hα hβ hαβ
  obtain ⟨γ, hγ, hSigγ, hγα⟩ := exists_root_kgL4 hα hβ hαβ
  have hS : famKernel {zetaVec ζ hζ (kgExpVec α + kgExpVec β)} =
      {δ | IsRoot Tag.E6 δ ∧ ((iform δ α + iform δ β : ℤ) : ZMod 3) = 0} :=
    famKernel_kgExpVec_add hζo hζ α β
  have hγS : γ ∈ famKernel {zetaVec ζ hζ (kgExpVec α + kgExpVec β)} := by
    rw [hS]; exact ⟨hγ, hSigγ⟩
  have hnegS : -γ ∈ famKernel {zetaVec ζ hζ (kgExpVec α + kgExpVec β)} := by
    rw [hS]
    refine ⟨IsRoot.neg hγ, ?_⟩
    rw [iform_neg_left, iform_neg_left]
    have : ((-(iform γ α) + -(iform γ β) : ℤ) : ZMod 3) =
        -(((iform γ α + iform γ β : ℤ)) : ZMod 3) := by push_cast; ring
    rw [this, hSigγ, neg_zero]
  have hspec := rootWeylOne_spec (τ := Tag.E6) (K := K) hγ
  obtain ⟨hjroot, hjmono, hjmap⟩ := hspec
  have hle : rootSubgroup Tag.E6 K γ ⊔ rootSubgroup Tag.E6 K (-γ) ≤
      rootSpan Tag.E6 K (famKernel {zetaVec ζ hζ (kgExpVec α + kgExpVec β)}) :=
    sup_le (rootSubgroup_le_rootSpan hγS) (rootSubgroup_le_rootSpan hnegS)
  refine ⟨rootWeylOne Tag.E6 K γ, hle hjroot, ?_, ?_⟩
  · intro x hx
    refine ⟨adAct Tag.E6 3 (rootReflection γ) x, NoOffRest.adAct_mem_hypE6 _ hx, ?_⟩
    rw [monomial_conj_rootDiagUnit_weylTuple hjmono hjmap (zetaVec ζ hζ x), weylTuple_zetaVec]
  · intro hconj
    rw [monomial_conj_rootDiagUnit_weylTuple hjmono hjmap (zetaVec ζ hζ (kgExpVec α)),
      weylTuple_zetaVec] at hconj
    have hkgγ : kgExpVec γ ≠ 0 := by
      intro hzero
      have h0 : (∑ j, ((γ j : ℤ) : ZMod 3) * (kgExpVec γ) j) = 0 := by
        rw [hzero]; simp
      rw [sum_mul_kgExpVec, iform_E6_self_eq_two hγ] at h0
      exact (by decide +kernel : ¬(((2 : ℤ) : ZMod 3) = 0)) h0
    have hsumα : (∑ j, ((γ j : ℤ) : ZMod 3) * (kgExpVec α) j) = ((iform γ α : ℤ) : ZMod 3) :=
      sum_mul_kgExpVec γ α
    have hc : (∑ j, ((γ j : ℤ) : ZMod 3) * (kgExpVec α) j) ≠ 0 := by
      rw [hsumα]; exact hγα
    have heq : adAct Tag.E6 3 (rootReflection γ) (kgExpVec α) = kgExpVec α :=
      zetaVec_injective hζo hζ (rootDiagUnit_injective hconj)
    rw [adAct_rootReflection_eq hγ] at heq
    have hb : (∑ j, ((γ j : ℤ) : ZMod 3) * (kgExpVec α) j) • kgExpVec γ = 0 :=
      sub_eq_self.mp heq
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hkgγ
    have h2 := congrFun hb i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h2
    exact hi ((mul_eq_zero.mp h2).resolve_left hc)

end CFSG.StandardType.KGL

end
