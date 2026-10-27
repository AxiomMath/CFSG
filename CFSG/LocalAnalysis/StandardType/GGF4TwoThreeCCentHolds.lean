module

public import CFSG.LocalAnalysis.StandardType.GGF4TwoThreeCCent
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4ThreeC
import CFSG.Blueprint.ChevalleyRoots
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces

public section

namespace CFSG.StandardType.SmallExc.F4Two

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

theorem parity_of_twelve : ∀ k0 ∈ [0, 1, 2], ∀ k1 ∈ [0, 1, 2], ∀ k2 ∈ [0, 1, 2],
    ∀ k3 ∈ [0, 1, 2], (rts.filter fun γ => kdL k0 k1 k2 k3 γ % 3 = 0).length = 12 →
      (4 + (rts.filter fun γ => ¬ kdL k0 k1 k2 k3 γ % 3 = 1).length) % 2 = 0 ∧
        (rts.filter fun γ => ¬ kdL k0 k1 k2 k3 γ % 3 = 0).length % 2 = 0 := by
  decide +kernel

section Kernel

variable {L : Type} [Field L] [CharP L 2]
  {a : Fin Tag.F4.rank → Lˣ} {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ}

open scoped Classical in
theorem ncard_kernel_eq_card_filter (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hak : ∀ i, a i = ω ^ k i) :
    {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0}.ncard =
      ((rootFinset Tag.F4).filter fun α => rootChar a α = 1).card := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  congr 1
  ext γ
  simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_rootFinset, rootChar_eq_one_iff hω3 hω1 hak]

end Kernel

section Trace

variable {L : Type} [Field L]
  [CharP L 2] {a : Fin Tag.F4.rank → Lˣ} {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ}

theorem trace_rootDiagUnit_eq_zero_of_card_eq_twelve (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hak : ∀ i, a i = ω ^ k i) (hk3 : ∀ i, k i < 3)
    (hcard : {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0}.ncard = 12) :
    LinearMap.trace L (RootModule Tag.F4 L)
      ((rootDiagUnit Tag.F4 a : ModGL Tag.F4 L) : Module.End L (RootModule Tag.F4 L)) = 0 := by
  have hm : ∀ n : ℕ, n < 3 → n ∈ [0, 1, 2] := fun n hn => by simp; omega
  rw [ncard_roots_filter (fun γ : V4 => kdot k γ % 3 = 0)] at hcard
  have hpar := parity_of_twelve (k (idx 0)) (hm _ (hk3 _)) (k (idx 1)) (hm _ (hk3 _))
    (k (idx 2)) (hm _ (hk3 _)) (k (idx 3)) (hm _ (hk3 _)) hcard
  have h1 : (4 + (rts.filter fun l => decide (¬ kdot k (vec4 l) % 3 = 1)).length) % 2 = 0 :=
    hpar.1
  have h0 : (rts.filter fun l => decide (¬ kdot k (vec4 l) % 3 = 0)).length % 2 = 0 := hpar.2
  have e1 : (((4 + (rts.filter fun l => decide (¬ kdot k (vec4 l) % 3 = 1)).length : ℕ)) : L)
      = 0 := (CharP.cast_eq_zero_iff L 2 _).2 (Nat.dvd_of_mod_eq_zero h1)
  have e0 : (((rts.filter fun l => decide (¬ kdot k (vec4 l) % 3 = 0)).length : ℕ) : L) = 0 :=
    (CharP.cast_eq_zero_iff L 2 _).2 (Nat.dvd_of_mod_eq_zero h0)
  rw [trace_rootDiagUnit_omega hω3 hω1 hak, ncard_roots_filter, ncard_roots_filter, e1, e0,
    zero_mul, add_zero]

end Trace

section Main


theorem ggF4TwoThreeCCentInput_holds :
    CFSG.LieType.SeitzGeneration.ExcHighThree.GGF4TwoThreeCCentInput := by
  unfold CFSG.LieType.SeitzGeneration.ExcHighThree.GGF4TwoThreeCCentInput
  intro K _ _ _ hK e c a he3 he1 _hc hda hcard
  classical
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  have he3' : (e : ModGL Tag.F4 K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, he3, Subgroup.coe_one]
  have hB : (baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K)) ^ 3 = 1 := by
    rw [← map_pow, he3', map_one]
  have hd3 : rootDiagUnit Tag.F4 a ^ 3 = 1 := by
    have h := conj_pow (a := c⁻¹)
      (b := baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K)) (i := 3)
    rw [inv_inv] at h
    rw [hda, h, hB, mul_one, inv_mul_cancel]
  have hap : ∀ i, a i ^ 3 = 1 := by
    have h : rootDiagUnit Tag.F4 (a ^ 3) = rootDiagUnit Tag.F4 1 := by
      rw [← rootDiagUnit_pow, hd3, rootDiagUnit_one]
    intro i
    simpa using congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) i
  obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ := exists_omega_param hap
  have hker : {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0}.ncard = 12 := by
    rw [ncard_kernel_eq_card_filter hω3 hω1 hak]
    exact hcard
  have htrL := trace_rootDiagUnit_eq_zero_of_card_eq_twelve hω3 hω1 hak hk3 hker
  have htrK : LinearMap.trace K (RootModule Tag.F4 K)
      ((e : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K)) = 0 := by
    have h := ChevQ.E8NonToral.trace_conj c⁻¹
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K))
    rw [inv_inv] at h
    rw [hda, h, CFSG.RankThree.Chevalley.trace_baseChangeGL] at htrL
    exact (map_eq_zero _).1 htrL
  exact isSolvable_centralizer_of_trace_eq_zero hK hord htrK

end Main

end CFSG.StandardType.SmallExc.F4Two
