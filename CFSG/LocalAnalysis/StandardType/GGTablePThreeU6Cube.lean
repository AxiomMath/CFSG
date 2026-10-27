module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeEigen
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeNe
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeComp
import CFSG.Assembly.GL83StatedBridge
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthSUFin
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UnitaryTwoLocalProj
import CFSG.LieType.Multipliers.U62Sylow
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.Quasithin.EmptyFaithful.S146zYFacts
import CFSG.Quasithin.EmptyFaithful.S146zYRes
import CFSG.Quasithin.H13.NQCoreP134Main

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

private theorem exists_cubeRoot {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) :
    ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso
      rw [h] at hK
      have h0 : Nat.card K = 0 := by simpa using hK
      have hpos : 0 < Nat.card K := Nat.card_pos
      omega
    · exact h
  have hcard : Nat.card Kˣ = q ^ 2 - 1 := by rw [Nat.card_units K, hK]
  have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    have h : q ^ 2 - 1 = q ^ 2 - 1 ^ 2 := by norm_num
    rw [h, Nat.sq_sub_sq]
  have h3dvd : 3 ∣ Nat.card Kˣ := by
    rw [hcard, hfac]
    exact dvd_mul_of_dvd_left hq3 (q - 1)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3dvd
  refine ⟨(u : K), ?_⟩
  have hu3 : (u : K) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu] at h
    exact congrArg (fun v : Kˣ => (v : K)) h
  have hu1 : (u : K) ≠ 1 := by
    intro h
    have hu_one : u = 1 := Units.ext h
    rw [hu_one, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hfac2 : ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) = 0 := by
    have h1 : ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) = (u : K) ^ 3 - 1 := by ring
    rw [h1, hu3]; ring
  rcases mul_eq_zero.mp hfac2 with h | h
  · exact absurd (sub_eq_zero.mp h) hu1
  · exact h

private theorem cubeRoot_mem {K : Type} [Field K] [CharP K 2] {ω μ : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hμ : μ ^ 3 = 1) :
    μ = 1 ∨ μ = ω ∨ μ = ω ^ 2 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hfac : (μ - 1) * (μ - ω) * (μ - ω ^ 2) = 0 := by
    have h1 : (μ - 1) * (μ - ω) * (μ - ω ^ 2) =
        (μ ^ 3 - 1) + (ω ^ 2 + ω + 1) * (μ - μ ^ 2) + (ω ^ 3 - 1) * (μ - 1) := by ring
    rw [h1, hμ, hω, hω3]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h1 | h2
    · left; exact sub_eq_zero.mp h1
    · right; left; exact sub_eq_zero.mp h2
  · right; right; exact sub_eq_zero.mp h

private theorem cubeRoot_distinct {K : Type} [Field K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 ∧ ω ^ 2 ≠ 1 ∧ ω ^ 2 ≠ ω := by
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h] at hω
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h3c : (3 : K) = 1 := by
      rw [show (3 : K) = 2 + 1 by norm_num, h2]; ring
    have h30 : (3 : K) = 0 := by norm_num at hω ⊢; exact hω
    rw [h3c] at h30
    exact one_ne_zero h30
  have h21 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω * 1 := by ring
      _ = ω * ω ^ 2 := by rw [h]
      _ = ω ^ 3 := by ring
      _ = 1 := h3
  have h2ω : ω ^ 2 ≠ ω := by
    intro h
    apply hω1
    have h3eq : ω ^ 3 = ω := by
      calc ω ^ 3 = ω ^ 2 * ω := by ring
        _ = ω * ω := by rw [h]
        _ = ω ^ 2 := by ring
        _ = ω := h
    calc ω = ω ^ 3 := h3eq.symm
      _ = 1 := h3
  exact ⟨hω1, h21, h2ω⟩

private theorem cube_block_dim_eq_two {K F : Type} [Field K] [Finite K] [CharP K 2]
    [Field F] [Finite F] {q k : ℕ} (hK : Nat.card K = q ^ 2)
    (hk2 : 2 ≤ k) (hkq : (k, q) ≠ (3, 2))
    (hLR : Nonempty (LargeEvenProj (LargeEvenSUGroup (Fin k) K q) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 2) F))) :
    k = 2 := by
  by_contra hkne
  have hk3 : 3 ≤ k := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hpow : Nat.card K = 2 ^ Module.finrank (ZMod 2) K :=
    (FiniteField.pow_finrank_eq_natCard 2 K).symm
  have hq_dvd : q ∣ 2 ^ Module.finrank (ZMod 2) K := by
    rw [← hpow, hK]
    exact ⟨q, by ring⟩
  obtain ⟨f, _, hqf⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hq_dvd
  have hK' : Nat.card K = (2 ^ f) ^ 2 := by rw [← hqf]; exact hK
  have hne : (k, 2 ^ f) ≠ (3, 2) := by
    intro h
    exact hkq (by rw [hqf]; exact h)
  rw [hqf] at hLR
  obtain ⟨eLR⟩ := hLR
  change CFSG.Open.StatedProj (LargeEvenSUGroup (Fin k) K (2 ^ f)) ≃*
    CFSG.Open.StatedProj (LargeEvenSLGroup (Fin 2) F) at eLR
  have eSU : CFSG.Open.StatedProj (LargeEvenSUGroup (Fin k) K (2 ^ f)) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU k (2 ^ f) K) :=
    QuotientGroup.equivQuotientSubgroupOfOfEq (A' := CFSG.Open.StatedScalars (Fin k) K)
      (A := LargeEvenSUGroup (Fin k) K (2 ^ f))
      (B' := CFSG.Open.StatedScalars (Fin k) K)
      (B := CFSG.Open.StatedSU k (2 ^ f) K) rfl
      (largeEvenSUGroup_eq_statedSU k (2 ^ f))
  have eSL : CFSG.Open.StatedProj (LargeEvenSLGroup (Fin 2) F) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F) :=
    QuotientGroup.equivQuotientSubgroupOfOfEq (A' := CFSG.Open.StatedScalars (Fin 2) F)
      (A := LargeEvenSLGroup (Fin 2) F)
      (B' := CFSG.Open.StatedScalars (Fin 2) F)
      (B := CFSG.Open.StatedSL 2 F) rfl
      (largeEvenSLGroup_eq_statedSL 2)
  have eS : CFSG.Open.StatedProj (CFSG.Open.StatedSU k (2 ^ f) K) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F) :=
    eSU.symm.trans (eLR.trans eSL)
  have hSU := CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) (f := f) hK' k
  have hcenter := CFSG.LocalAnalysis.GLTheoremA.center_statedSU_eq_scalars
    (F := K) (f := f) (d := k) hK' hk3
  refine CFSG.HardMathSupport.Dickson.Sec6.I1431.excOth_suid_no_psl2
    (F := K) (p := 2) (f := f) (F' := F) hK' hk3 hne ?_
  rw [hSU]
  exact (QuotientGroup.quotientMulEquivOfEq hcenter).trans eS

theorem uni6_cube_impossible {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1)
    {d : GL (Fin 6) K} (hd : IsHermIsometry q (d : Matrix (Fin 6) (Fin 6) K)) (hd3 : d ^ 3 = 1)
    (hdn : ∀ c : K, (d : Matrix (Fin 6) (Fin 6) K) ≠ c • (1 : Matrix (Fin 6) (Fin 6) K))
    {δ' : MulAut (PSUg 6 K q)} (hδ : IsConjBy d δ')
    {J' : Subgroup (PSUg 6 K q)} (hJc : IsComponentOf J' (ggAutFixedSubgroup δ'))
    (huniq : ∀ Q : Subgroup (PSUg 6 K q), IsComponentOf Q (ggAutFixedSubgroup δ') → Q = J')
    {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F)
    (hA1 : Nonempty (J' ⧸ Subgroup.center J' ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) F))) : False := by
  obtain ⟨ω, hω⟩ := exists_cubeRoot hK hq3
  obtain ⟨_, hsumω⟩ := uni_cube_eigen hK hq3 hd hd3
  obtain ⟨μ₀, hμ0, hQS0, hJ'iff⟩ :=
    uni_cube_component_block hK hq3 (by norm_num) hd hd3 hδ hJc
  obtain ⟨Q, hQcomp, _, hQequiv⟩ :=
    uni_cube_block_component hK hq3 (by norm_num) hd hd3 hδ hμ0 hQS0
  have hQJ : Q = J' := huniq Q hQcomp
  have hQequiv' : Nonempty (J' ⧸ Subgroup.center J' ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin (Module.finrank K (cubeEigen d μ₀))) K q)) := by
    rw [hQJ] at hQequiv
    exact hQequiv
  have hLR : Nonempty (LargeEvenProj
        (LargeEvenSUGroup (Fin (Module.finrank K (cubeEigen d μ₀))) K q) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 2) F)) := by
    obtain ⟨e1⟩ := hQequiv'
    obtain ⟨e2⟩ := hA1
    exact ⟨e1.symm.trans e2⟩
  have hk2 : 2 ≤ Module.finrank K (cubeEigen d μ₀) := by
    rcases hQS0 with h | h
    · exact h.1
    · omega
  have hkq : (Module.finrank K (cubeEigen d μ₀), q) ≠ (3, 2) := by
    intro h
    have h1 : Module.finrank K (cubeEigen d μ₀) = 3 := congrArg Prod.fst h
    have h2 : q = 2 := congrArg Prod.snd h
    rcases hQS0 with ⟨_, hq4⟩ | hk4
    · omega
    · omega
  have hkμ2 : Module.finrank K (cubeEigen d μ₀) = 2 :=
    cube_block_dim_eq_two hK hk2 hkq hLR
  have hq4 : 4 ≤ q := by
    rcases hQS0 with h | h
    · exact h.2
    · omega
  have hbound : ∀ ν : K, ν ^ 3 = 1 → ν ≠ μ₀ →
      Module.finrank K (cubeEigen d ν) ≤ 1 := by
    intro ν hν hνne
    by_contra hcon
    have hle : 2 ≤ Module.finrank K (cubeEigen d ν) := by omega
    obtain ⟨Qν, hQνcomp, hQνiff, _⟩ :=
      uni_cube_block_component hK hq3 (by norm_num) hd hd3 hδ hν (Or.inl ⟨hle, hq4⟩)
    have hQνJ : Qν = J' := huniq Qν hQνcomp
    have hP4 := uni_cube_blocks_ne hK hq3 (by norm_num) hd hd3 hμ0 hν (Ne.symm hνne) hk2 hle
    apply hP4
    intro x
    rw [← hQνiff x, hQνJ, hJ'iff x]
  have hmem : μ₀ = 1 ∨ μ₀ = ω ∨ μ₀ = ω ^ 2 := cubeRoot_mem hω hμ0
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω23 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  have hdist := cubeRoot_distinct hω
  have hsum := hsumω ω hω
  rcases hmem with h | h | h
  · rw [h] at hkμ2
    have h1 : Module.finrank K (cubeEigen d ω) ≤ 1 := hbound ω hω3 (by rw [h]; exact hdist.1)
    have h2 : Module.finrank K (cubeEigen d (ω ^ 2)) ≤ 1 :=
      hbound (ω ^ 2) hω23 (by rw [h]; exact hdist.2.1)
    omega
  · rw [h] at hkμ2
    have h1 : Module.finrank K (cubeEigen d 1) ≤ 1 :=
      hbound 1 (one_pow 3) (by rw [h]; exact Ne.symm hdist.1)
    have h2 : Module.finrank K (cubeEigen d (ω ^ 2)) ≤ 1 :=
      hbound (ω ^ 2) hω23 (by rw [h]; exact hdist.2.2)
    omega
  · rw [h] at hkμ2
    have h1 : Module.finrank K (cubeEigen d 1) ≤ 1 :=
      hbound 1 (one_pow 3) (by rw [h]; exact Ne.symm hdist.2.1)
    have h2 : Module.finrank K (cubeEigen d ω) ≤ 1 :=
      hbound ω hω3 (by rw [h]; exact Ne.symm hdist.2.2)
    omega


end CFSG.StandardType.TablePThreeKG

end