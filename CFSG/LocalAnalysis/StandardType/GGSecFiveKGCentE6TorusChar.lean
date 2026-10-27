module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyCenter
import CFSG.LieType.Steinberg.CentralExt.MinusculeCentrallyClosed
import CFSG.LocalAnalysis.StandardType.GGRootDetectExcE6

public section

namespace CFSG.StandardType.KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.CentralExt CFSG.ClassicalInvolution.ModelFacts

private theorem adjE6_mul_cartan :
    ∀ m i : Fin Tag.E6.rank,
      ∑ l : Fin Tag.E6.rank, (A2Isogeny.adjE6.getD m []).getD l 0 * Tag.cartan .E6 l i =
        if m = i then 3 else 0 := by
  decide +kernel

theorem ncard_rootChar_le_ncard_torus_E6
    {k : Type} [Field k] [Finite k] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {R : Set (Fin Tag.E6.rank → ℤ)} :
    Set.ncard {b : Fin Tag.E6.rank → kˣ | (∀ i, b i ^ p = 1) ∧ ∀ β ∈ R, rootChar b β = 1} ≤
      Set.ncard {h : ↥(e6Data_valid.minGroup k) | h ∈ ggTorus (e6Datum k) ∧ h ^ p = 1 ∧
        ∀ β ∈ R, ∀ z ∈ (e6Datum k).rootGroup β, Commute h z} := by
  classical
  have : Finite ↥(e6Data_valid.minGroup k) := by
    have : Finite (Module.End k (Fin e6Data.d →₀ k)) := Module.finite_of_finite k
    infer_instance
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  obtain ⟨u, hu⟩ : ∃ u : (Fin Tag.E6.rank → kˣ) → Fin Tag.E6.rank → kˣ, ∀ b l,
      u b l = ∏ m, b m ^ ((s : ℤ) * (A2Isogeny.adjE6.getD m []).getD l 0) :=
    ⟨fun b l => ∏ m, b m ^ ((s : ℤ) * (A2Isogeny.adjE6.getD m []).getD l 0), fun _ _ => rfl⟩
  have key : ∀ b γ, ExceptionalCover.rootChar k γ (u b) = rootChar b γ ^ (3 * s) := by
    intro b γ
    rw [ExceptionalCover.rootChar_apply, rootChar, ← Finset.prod_pow]
    simp only [hu, ← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [← AdjointClosed.zpow_sum_eq_prod, ← zpow_natCast, ← zpow_mul]
    congr 1
    calc ∑ l : Fin Tag.E6.rank,
          (s : ℤ) * (A2Isogeny.adjE6.getD m []).getD l 0 * ExceptionalCover.cartanCoord γ l
        = ∑ i, (s : ℤ) *
            (∑ l : Fin Tag.E6.rank, (A2Isogeny.adjE6.getD m []).getD l 0 * Tag.cartan .E6 l i) *
              γ i := by
          simp only [ExceptionalCover.cartanCoord, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
      _ = γ m * ((3 * s : ℕ) : ℤ) := by
          simp only [adjE6_mul_cartan m, mul_ite, ite_mul, mul_zero, zero_mul,
            Finset.sum_ite_eq, Finset.mem_univ, if_true]
          push_cast
          ring
  have hpow : ∀ b : Fin Tag.E6.rank → kˣ, (∀ i, b i ^ p = 1) → ∀ γ,
      rootChar b γ ^ (3 * s) = rootChar b γ := by
    intro b hb γ
    have h1 : rootChar b γ ^ p = 1 := by
      rw [rootChar, ← Finset.prod_pow]
      exact Finset.prod_eq_one fun i _ => by
        rw [← zpow_natCast, ← zpow_mul, mul_comm _ (p : ℤ), zpow_mul, zpow_natCast, hb i,
          one_zpow]
    rw [← Nat.div_add_mod (3 * s) p, pow_add, pow_mul, h1, one_pow, one_mul, hs, pow_one]
  have hT : ∀ v, MinusculeClosed.minTorus e6Data_valid k v ∈ ggTorus (e6Datum k) := by
    intro v
    induction v using ExceptionalCover.torusVec_induction with
    | h1 => rw [map_one]; exact one_mem _
    | hmul t t' ht ht' => rw [map_mul]; exact mul_mem ht ht'
    | hsingle a t =>
      rw [MinusculeClosed.minTorus_mulSingle]
      exact RootDetectExc.hm_mem_ggTorus e6Data_valid isFiniteType_cartan_E6 k a t
  refine Set.ncard_le_ncard_of_injOn (fun b => MinusculeClosed.minTorus e6Data_valid k (u b))
    ?_ ?_
  · rintro b ⟨hbp, hbR⟩
    refine ⟨hT _, ?_, fun β hβ z hz => ?_⟩
    · have h1 : u b ^ p = 1 := by
        funext l
        rw [Pi.pow_apply, Pi.one_apply, hu, ← Finset.prod_pow]
        exact Finset.prod_eq_one fun m _ => by
          rw [← zpow_natCast, ← zpow_mul, mul_comm _ (p : ℤ), zpow_mul, zpow_natCast, hbp m,
            one_zpow]
      rw [← map_pow, h1, map_one]
    · by_cases hβr : IsRoot .E6 β
      · obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hz
        have h1 := MinusculeClosed.minTorus_conj_xm e6Data_valid k (u b) hβr c
        rw [key, hpow b hbp, hbR β hβ, Units.val_one, one_mul] at h1
        exact mul_inv_eq_iff_eq_mul.1 h1
      ·
        have hz' : z ∈ e6Data_valid.rootGroup k β := hz
        rw [e6Data_valid.rootGroup_eq_bot k hβr, Subgroup.mem_bot] at hz'
        rw [hz']
        exact Commute.one_right _
  · intro b hb b' hb' hbb'
    funext i
    have hi : IsRoot .E6 (Pi.single i 1) := IsRoot.basis i
    have hb1 : ∀ a : Fin Tag.E6.rank → kˣ, rootChar a (Pi.single i 1) = a i := fun a => by
      simpa using rootChar_nsmul_single a i 1
    have h1 := MinusculeClosed.minTorus_conj_xm e6Data_valid k (u b) hi 1
    rw [show MinusculeClosed.minTorus e6Data_valid k (u b) =
      MinusculeClosed.minTorus e6Data_valid k (u b') from hbb',
      MinusculeClosed.minTorus_conj_xm e6Data_valid k (u b') hi 1] at h1
    have h2 := e6Data_valid.xm_injective k hi h1
    rw [key, key, hpow b hb.1, hpow b' hb'.1, hb1, hb1, mul_one, mul_one] at h2
    exact (Units.ext h2).symm

end CFSG.StandardType.KGCentE6

end
