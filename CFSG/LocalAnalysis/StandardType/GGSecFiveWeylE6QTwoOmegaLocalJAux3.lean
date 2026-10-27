module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalJAux2

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open
open Polynomial Module
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCPrimary

variable {K : Type} [Field K] [Finite K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.blockDet_self_eq (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hsupp : x ∈ supportedBlock Q x h) :
    blockDet Q x h ⟨x, hsupp⟩ =
      (AdjoinRoot.root h) ^ primaryMultiplicity x.toLinearMap h := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  rw [blockDet_apply]
  have hfun : ((blockGL Q x h ⟨x, hsupp⟩ : BlockGL x h) :
      Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) =
      (AdjoinRoot.root h) • 1 := by
    ext v
    change x (v : V) = ↑((AdjoinRoot.root h) • v)
    rw [coe_root_smul_primaryComponent]
    rfl
  rw [hfun, LinearMap.det_smul, map_one, mul_one]

theorem exists_pow_of_commute_of_finrank_two (hK : Nat.card K = 2)
    {y b : V ≃ₗ[K] V} (hy : y ^ 3 = 1) (hb : Commute b y)
    {U : Submodule K V} (hyU : ∀ u ∈ U, y u ∈ U) (hbU : ∀ u ∈ U, b u ∈ U)
    (hy2 : ∀ u ∈ U, y (y u) = y u + u)
    (hdim : finrank K U = 2) :
    ∃ j : ℕ, ∀ u ∈ U, b u = (y ^ j) u := by
  classical
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  have h2K : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have hadd2 : ∀ z : V, z + z = 0 := by
    intro z
    calc z + z = (2 : K) • z := (two_smul K z).symm
      _ = 0 := by rw [h2K, zero_smul]
  have hK2 : ∀ a : K, a = 0 ∨ a = 1 := by
    intro a
    obtain ⟨c, hcne, hcall⟩ := (Nat.card_eq_two_iff' (1 : K)).mp hK
    by_cases ha : a = 1
    · exact Or.inr ha
    · have hac : a = c := hcall a ha
      have hc0 : c = 0 := by
        by_contra hc0
        exact hc0 (hcall 0 (by norm_num)).symm
      exact Or.inl (hac.trans hc0)
  obtain ⟨v, hvU, hv0⟩ : ∃ v ∈ U, v ≠ 0 := by
    by_contra h
    push Not at h
    have : U = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Submodule.mem_bot]
      exact h u hu
    rw [this, finrank_bot] at hdim
    omega
  have hyvU : y v ∈ U := hyU v hvU
  have hli : LinearIndependent K ![v, y v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hv0, rfl⟩
    · exfalso
      have h1 : y v = (-(s / t)) • v := by
        have h2 : t • y v = -(s • v) := by
          rw [eq_neg_iff_add_eq_zero]
          rwa [add_comm] at hst
        calc y v = t⁻¹ • (t • y v) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = t⁻¹ • (-(s • v)) := by rw [h2]
          _ = (-(s / t)) • v := by
            rw [smul_neg, smul_smul, neg_smul, div_eq_mul_inv]
            congr 1
            ring_nf
      set c : K := -(s / t) with hc
      have hy2' : y (y v) = y v + v := hy2 v hvU
      have hcc : c • v = y v := h1.symm
      have hc2 : c ^ 2 • v = y (y v) := by
        calc c ^ 2 • v = c • (c • v) := by rw [sq, smul_smul]
          _ = c • y v := by rw [hcc]
          _ = y (c • v) := by rw [map_smul]
          _ = y (y v) := by rw [hcc]
      have h3 : (c ^ 2 + c + 1) • v = 0 := by
        rw [add_smul, add_smul, one_smul, hc2, hcc, hy2']
        calc y v + v + y v + v = (y v + y v) + (v + v) := by abel
          _ = 0 := by rw [hadd2, hadd2, add_zero]
      have h4 : c ^ 2 + c + 1 ≠ 0 := by
        rcases hK2 c with hc0' | hc1'
        · rw [hc0']; norm_num
        · rw [hc1']
          have h3K : (3 : K) = 1 := by
            calc (3 : K) = 1 + 2 := by norm_num
              _ = 1 + 0 := by rw [h2K]
              _ = 1 := by rw [add_zero]
          have h1 : (1 : K) ^ 2 + 1 + 1 = 3 := by norm_num
          rw [h1, h3K]
          exact one_ne_zero
      exact h4 (smul_eq_zero.mp h3 |>.resolve_right hv0)
  have hli2 : finrank K (Submodule.span K (Set.range ![v, y v])) = 2 := by
    rw [finrank_span_eq_card hli]
    simp
  have hspan_le : Submodule.span K (Set.range ![v, y v]) ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hvU
    · exact hyvU
  have hspan : U = Submodule.span K (Set.range ![v, y v]) := by
    exact (Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hli2, hdim])).symm
  have hspan_pair : U = Submodule.span K {v, y v} := by
    simpa [Set.pair_comm] using hspan
  have hbv : b v ∈ Submodule.span K (Set.range ![v, y v]) := by
    rw [← hspan]
    exact hbU v hvU
  have hbv_pair : b v ∈ Submodule.span K {v, y v} := by
    simpa [Set.pair_comm] using hbv
  rw [Submodule.mem_span_pair] at hbv_pair
  obtain ⟨a, c, hac⟩ := hbv_pair
  have hbv' : b v = a • v + c • (y v) := hac.symm
  have hbcases : b v = v ∨ b v = y v ∨ b v = v + y v := by
    have hb0 : b v ≠ 0 := by
      intro h0
      have hb0' : b v = b 0 := by rw [h0, map_zero]
      exact hv0 (b.injective hb0')
    rcases hK2 a with ha | ha <;> rcases hK2 c with hc | hc
    · exfalso
      apply hb0
      rw [hbv', ha, hc]
      simp
    · right; left
      rw [hbv', ha, hc]
      simp
    · left
      rw [hbv', ha, hc]
      simp
    · right; right
      rw [hbv', ha, hc]
      module
  have hby : b (y v) = y (b v) := by
    have h := congrArg (fun e : V ≃ₗ[K] V => e v) hb.eq
    simpa [LinearEquiv.mul_apply] using h
  have hyv_ne_v : y v ≠ v := by
    intro he
    have hpair := (LinearIndependent.pair_iff).mp hli
    have h2 : (1 : K) • v + (1 : K) • y v = 0 := by
      rw [one_smul, one_smul, he, hadd2]
    exact one_ne_zero (hpair 1 1 h2).2
  rcases hbcases with h | h | h
  · refine ⟨0, ?_⟩
    intro u hu
    rw [hspan_pair, Submodule.mem_span_pair] at hu
    obtain ⟨α, β, hαβ⟩ := hu
    have hbu : b u = α • b v + β • b (y v) := by rw [← hαβ, map_add, map_smul, map_smul]
    have hbyv : b (y v) = y v := by rw [hby, h]
    rw [pow_zero]
    calc b u = α • v + β • y v := by rw [hbu, h, hbyv]
      _ = u := by rw [hαβ]
  · refine ⟨1, ?_⟩
    intro u hu
    rw [hspan_pair, Submodule.mem_span_pair] at hu
    obtain ⟨α, β, hαβ⟩ := hu
    have hbu : b u = α • b v + β • b (y v) := by rw [← hαβ, map_add, map_smul, map_smul]
    rw [pow_one]
    calc b u = α • y v + β • (y v + v) := by rw [hbu, h, hby, h, hy2 v hvU]
      _ = y u := by rw [← hαβ, map_add, map_smul, map_smul, hy2 v hvU]
  · refine ⟨2, ?_⟩
    intro u hu
    rw [hspan_pair, Submodule.mem_span_pair] at hu
    obtain ⟨α, β, hαβ⟩ := hu
    have hbu : b u = α • b v + β • b (y v) := by rw [← hαβ, map_add, map_smul, map_smul]
    have hbvy : b (y v) = v := by
      calc b (y v) = y (b v) := hby
        _ = y (v + y v) := by rw [h]
        _ = y v + y (y v) := by rw [map_add]
        _ = y v + (y v + v) := by rw [hy2 v hvU]
        _ = v := by rw [← add_assoc, hadd2, zero_add]
    have hyvy : y (y v) = y v + v := hy2 v hvU
    have hy3v : y (y (y v)) = v := by
      have h3 := congrArg (fun e : V ≃ₗ[K] V => e v) hy
      simpa [pow_succ, pow_two, LinearEquiv.mul_apply] using h3
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_add, pow_one]
    calc b u = α • v + α • y v + β • v := by rw [hbu, h, hbvy]; module
      _ = y (y u) := by
        rw [← hαβ, map_add, map_smul, map_smul, map_add, map_smul, map_smul, hy3v, hyvy]
        module

end CFSG.StandardType.E6QTwo

end
