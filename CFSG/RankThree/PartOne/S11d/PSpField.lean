module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.S11d.PSpCyclic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.OddIso CFSG.RankThree.PartOne.KCSpFull
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r p : ℕ} {K : Type} [Field K]

theorem spEnd_fieldSp (σ : K ≃+* K) (g : StatedSp r K) (w : Fin r ⊕ Fin r → K) :
    spEnd (fieldSp r K σ g) (σ ∘ w) = σ ∘ spEnd g w := by
  rw [spEnd_apply, spEnd_apply, coe_fieldSp]
  funext i
  have := RingHom.map_mulVec σ.toRingHom
    ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) w i
  exact this.symm

theorem spEnd_pow_fieldSp {σ : K ≃+* K} {a : StatedSp r K} (ha : fieldSp r K σ a = a) (n : ℕ)
    (w : Fin r ⊕ Fin r → K) : (spEnd a ^ n) (σ ∘ w) = σ ∘ (spEnd a ^ n) w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
    congr 1
    have := spEnd_fieldSp σ a w
    rwa [ha] at this

theorem avg_comp_σ {σ : K ≃+* K} {a : StatedSp r K} (ha : fieldSp r K σ a = a) (p : ℕ)
    (w : Fin r ⊕ Fin r → K) : avg (spEnd a) p (σ ∘ w) = σ ∘ avg (spEnd a) p w := by
  unfold avg
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  funext j
  simp only [Finset.sum_apply, Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := congrFun (spEnd_pow_fieldSp ha i w) j
  simpa using this

theorem fieldSp_spTransvection (σ : K ≃+* K) {v : Fin r ⊕ Fin r → K} (hv : σ ∘ v = v) (t : K)
    (ht : σ t = t) : fieldSp r K σ (spTransvection v t) = spTransvection v t := by
  apply spEnd_injective
  refine LinearMap.ext fun w => ?_
  obtain ⟨w', rfl⟩ : ∃ w', w = σ ∘ w' := ⟨σ.symm ∘ w, by funext i; simp⟩
  rw [spEnd_fieldSp, spEnd_spTransvection, spEnd_spTransvection]
  funext i
  have h1 : σ (v i) = v i := congrFun hv i
  have h2 := spForm_comp_ringEquiv (r := r) (K := K) σ w' v
  rw [hv] at h2
  simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  rw [ht, h1, h2]

theorem exists_rational_pair [Finite K] [CharP K 2] {σ : K ≃+* K} {a : StatedSp r K}
    (hodd : Odd p) (hap : a ^ p = 1) (ha : fieldSp r K σ a = a)
    (hker : LinearMap.ker (spEnd a - 1) ≠ ⊥) :
    ∃ v v' : Fin r ⊕ Fin r → K, v ∈ LinearMap.ker (spEnd a - 1) ∧
      v' ∈ LinearMap.ker (spEnd a - 1) ∧ σ ∘ v = v ∧ σ ∘ v' = v' ∧ spForm r K v v' ≠ 0 := by
  classical
  have hÂp : spEnd a ^ p = 1 := by rw [← spEnd_pow', hap, spEnd_one]
  let b : Fin r ⊕ Fin r → (Fin r ⊕ Fin r → K) := fun i =>
    avg (spEnd a) p (Pi.single i 1)
  have hbker : ∀ i, b i ∈ LinearMap.ker (spEnd a - 1) := fun i => by
    rw [← range_avg hodd hÂp]
    exact ⟨_, rfl⟩
  have hsingle : ∀ i : Fin r ⊕ Fin r, σ ∘ (Pi.single i (1 : K) : Fin r ⊕ Fin r → K) =
      Pi.single i 1 := fun i => by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  have hbσ : ∀ i, σ ∘ b i = b i := fun i => by
    have := avg_comp_σ ha p (Pi.single i 1)
    rw [hsingle i] at this
    exact this.symm
  by_contra hcon
  push Not at hcon
  have hbb : ∀ i j, spForm r K (b i) (b j) = 0 := fun i j =>
    hcon _ _ (hbker i) (hbker j) (hbσ i) (hbσ j)
  have hidem : avg (spEnd a) p * avg (spEnd a) p = avg (spEnd a) p := avg_mul_self hodd hÂp
  have hspan : ∀ u ∈ LinearMap.ker (spEnd a - 1), u = ∑ i, u i • b i := by
    intro u hu
    have hu' : u ∈ LinearMap.range (avg (spEnd a) p) := by rw [range_avg hodd hÂp]; exact hu
    obtain ⟨x, rfl⟩ := hu'
    have hPu : avg (spEnd a) p (avg (spEnd a) p x) = avg (spEnd a) p x := by
      rw [← Module.End.mul_apply, hidem]
    conv_lhs => rw [← hPu, pi_eq_sum_univ (avg (spEnd a) p x)]
    simp only [map_sum, map_smul, b]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  have hzero : ∀ u ∈ LinearMap.ker (spEnd a - 1), ∀ w ∈ LinearMap.ker (spEnd a - 1),
      spForm r K u w = 0 := by
    intro u hu w hw
    calc spForm r K u w = spForm r K (∑ i, u i • b i) (∑ j, w j • b j) := by
          rw [← hspan u hu, ← hspan w hw]
      _ = 0 := by
          simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hbb,
            smul_zero, Finset.sum_const_zero]
  have hBn : ∀ v, (∀ w, spForm r K v w = 0) → v = 0 := fun v hv =>
    (spForm_nondegenerate (r := r) (K := K)).1 v hv
  refine hker ((Submodule.eq_bot_iff _).mpr fun u hu => ?_)
  exact fix_sep hBn (spEnd_isom a) hodd hÂp u hu fun w hw => hzero u hu w hw

end CFSG.RankThree.PartOne
