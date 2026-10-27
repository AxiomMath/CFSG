module

public import CFSG.LocalAnalysis.UniquenessCase.Frob4PFixedPoint
public import CFSG.LocalAnalysis.UniquenessCase.Frob4PComplement
public import CFSG.LocalAnalysis.UniquenessCase.Frob4PSylow
public import CFSG.LocalAnalysis.UniquenessCase.Frob4PBridge
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Fpf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G]

theorem frob4Prime_holds (hK : FrobKFacts) (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) : Frob4Prime (UC6.dataOfSetup4 hS hU S) := by
  classical
  intro p P P₀ hH h5 hab hcl d hdL hdp
  by_contra hdc
  have hpσ : p ∈ uniqueFourSigma S.M := hH.mem_sig2.1
  haveI : Fact p.Prime := ⟨hpσ.1.1⟩
  have hp2 : p ≠ 2 := by omega
  have hM : Group.IsSolvable S.M :=
    UC6S846.solvable_of_sigmaTwo4 hU S.maxLocal hpσ hH.mem_sig2.2
  have hdN : d ∈ normalizer (P₀ : Set G) :=
    frob4P_centralizer_layer_le_normalizer hS hU S hH h5 hab hcl hdL
  have hdM : d ∈ S.M := uc22p22qzb_centralizer_layer_le hS hU S hH h5 hab hcl hdL
  have hcl' := hcl
  obtain ⟨hP₀P, hcard, -, -, -, -, hfrob, -⟩ := hcl'
  obtain ⟨P', x, rfl, rfl, hl⟩ := frob4P_frobLocal hS hU S hH h5 hab hcl
  have hG := frob4P_frobGlobal hS hU
  have hdc' : d ∉ centralizer ({x} : Set G) := by
    rwa [← centralizer_zpowers_eq]
  have hdL' : d ∈ centralizer ((layerOf x : Subgroup G) : Set G) := hdL
  have hSyl := frob4P_isSylowOf_centralizer hG hl hM hdL' hdN hdc'
  have hd1 : d ≠ 1 := fun h => by
    rw [h, orderOf_one] at hdp
    exact Nat.not_prime_one hdp
  have hbot : pCoreOf 2 S.M ⊓ centralizer ({d} : Set G) = ⊥ :=
    fr_cT_eq_bot hK hG hl hd1 hdL' (Or.inl hSyl)
  obtain ⟨hT1, -, -, -, -, -, -, hfpf⟩ := hfrob
  have hTp : IsPGroup 2 (pCoreOf 2 S.M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S.M
  have hMT : S.M ≤ normalizer (pCoreOf 2 S.M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 S.M
  have hP₀M : zpowers x ≤ S.M := hP₀P.trans hH.sylow.le
  obtain ⟨t, htT, ht1, htd⟩ := frob4P_exists_fixed_of_frobenius (p := p) (r := orderOf d)
    (Fact.out : p.Prime) hp2 hdp hTp hT1 hcard (fun y hy => hMT (hP₀M hy))
    (fun y hy hy1 t ht hty => hfpf y (Subgroup.mem_sup_right hy) hy1 t ht hty) rfl (hMT hdM) hdN
    (by rwa [← centralizer_zpowers_eq] at hdc')
  have hmem : t ∈ pCoreOf 2 S.M ⊓ centralizer ({d} : Set G) :=
    mem_inf.2 ⟨htT, by rw [mem_centralizer_singleton_iff]; exact htd⟩
  rw [hbot, mem_bot] at hmem
  exact ht1 hmem

end CFSG.LocalAnalysis.UniquenessCase.UC22
