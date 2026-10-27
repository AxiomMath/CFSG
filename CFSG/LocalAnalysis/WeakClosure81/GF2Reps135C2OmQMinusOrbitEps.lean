module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLat
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFinite
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeylEx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisOrbit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis CFSG.LieType.RootSystem
open CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omq_omMinus_rank_of_eps_orbit {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k V : Type} [Field k]
    [CharP k 2] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hxr : omqnfRealizes (n - 1) x π s) {v : Fin (n - 1) → ℤ}
    (hv : ∀ t : Fin (n - 1), μ t ≠ (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ t →
      omqSignedActZ (omqMinusSimple (n - 1) t).1 (omqMinusSimple (n - 1) t).2 v = v)
    {d : ℕ} {u : Fin d → Fin (n - 1) → ℤ} (hinj : Function.Injective u)
    (horb : ∀ i, OmqFormalInOrbit v (u i))
    (hmove : ∀ i i', u i ≠ omqSignedActZ π s (u i')) :
    d ≤ Module.finrank k
      (LinearMap.range (σ ((SmallO8mCurtis.curtisDatum n hn hirr).nW x) - 1)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D := SmallO8mCurtis.curtisDatum n hn hirr
  let cs := (coxeterMatrix (isFiniteType_cartanB (n - 1))).toCoxeterSystem
  let : MulAction (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group (Fin (n - 1) → ℤ) :=
    MulAction.compHom (Fin (n - 1) → ℤ) (weylAction (isFiniteType_cartanB (n - 1)))
  have hsm : ∀ (w : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group)
      (z : Fin (n - 1) → ℤ), w • z = weylAction (isFiniteType_cartanB (n - 1)) w z := by
    intro w z
    simp [MulAction.compHom_smul_def, Module.End.smul_def]
  let v' : Fin (n - 1) → ℤ := ofStdB (n - 1) v
  let u' : Fin d → Fin (n - 1) → ℤ := fun i => ofStdB (n - 1) (u i)
  have hv' : ∀ t : Fin (n - 1), μ t ≠ D.dScalar χ t → cs.simple t • v' = v' := by
    intro t htne
    rw [hsm]
    apply toStdB_injective (n - 1)
    have h := hv t htne
    by_cases htl : t.val + 1 < n - 1
    · have hr := omqnfRealizes_simple_of_lt htl v'
      rw [hr]
      simp only [omqMinusSimple, dif_pos htl] at h
      rw [toStdB_ofStdB]
      funext b
      have h' := congrFun h b
      simpa [omqSignedActZ] using h'
    · have hr := omqnfRealizes_simple_of_not_lt htl v'
      rw [hr]
      simp only [omqMinusSimple, dif_neg htl] at h
      rw [toStdB_ofStdB]
      funext b
      have h' := congrFun h b
      simpa [omqSignedActZ] using h'
  have hu' : ∀ i, u' i ∈ MulAction.orbit
      (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group v' := by
    intro i
    obtain ⟨π', s', hs', hact⟩ := horb i
    obtain ⟨w, hw⟩ := exists_omqnfRealizes_of_signedPerm π' hs'
    refine MulAction.mem_orbit_iff.mpr ⟨w, ?_⟩
    rw [hsm]
    apply toStdB_injective (n - 1)
    rw [hw v']
    simp only [u']
    rw [toStdB_ofStdB, toStdB_ofStdB, ← hact]
    rfl
  have hinj' : Function.Injective u' := by
    intro i j hij
    apply hinj
    have := congrArg (toStdB (n - 1)) hij
    simpa [u', toStdB_ofStdB] using this
  have hmove' : ∀ i i', u' i ≠ x • u' i' := by
    intro i i' h
    rw [hsm] at h
    apply hmove i i'
    have := congrArg (toStdB (n - 1)) h
    rw [hxr] at this
    simp only [u', toStdB_ofStdB] at this
    exact this
  exact le_finrank_range_sub_one_of_mem_orbit (D := D) hσ ht hv' x u' hu' hinj' hmove'

end CFSG.LocalAnalysis.WeakClosure81
