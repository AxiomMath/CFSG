module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUModel
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUEven
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.Assembly

theorem qTwoLMPrimeA_marking {X : Type} [Group X] {m : ℕ} (hm : 5 ≤ m)
    (hL : LieModel X .PSU m 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ 1) ^ 2 ∧
      Nonempty (X ≃* StatedProj (StatedSU m (2 ^ 1) K)) := by
  rcases hL with ⟨-, -, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact hc
  all_goals omega

theorem qTwoLMPrimeA_center_scalars {m : ℕ} (hm : 5 ≤ m) (h3 : ¬ 3 ∣ m) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Subgroup.center (StatedSU m (2 ^ 1) K) = ⊥ ∧
      (StatedScalars (Fin m) K).subgroupOf (StatedSU m (2 ^ 1) K) = ⊥ := by
  have hcop : Nat.Coprime m (2 ^ 1 + 1) := by
    rw [show (2 : ℕ) ^ 1 + 1 = 3 by norm_num, Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have hZU : Subgroup.center (StatedSU m (2 ^ 1) K) = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSU_eq_bot_of_coprime hK le_rfl (by omega)
      hcop
  refine ⟨hZU, eq_bot_iff.2 fun u hu => ?_⟩
  have hcen : (u : GL (Fin m) K) ∈ Subgroup.center (GL (Fin m) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact Subgroup.mem_subgroupOf.1 hu
  have hc : u ∈ Subgroup.center (StatedSU m (2 ^ 1) K) := by
    rw [Subgroup.mem_center_iff]
    intro v
    exact Subtype.ext (Subgroup.mem_center_iff.1 hcen (v : GL (Fin m) K))
  rwa [hZU] at hc

theorem qTwoLMPrimeA_centerPrime {m : ℕ} (hm : 5 ≤ m) (h3 : ¬ 3 ∣ m)
    (hMul : PSUTrivialMultiplier m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) :
    GGCenterPrime 3 (LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ 1))) := by
  intro L' _ _ ψ hψ hker hperf
  obtain ⟨hZU, hscal⟩ := qTwoLMPrimeA_center_scalars hm h3 hK
  let eR : LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ 1)) ≃* StatedSU m (2 ^ 1) K :=
    (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ 1))) = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have h1 : eR z ∈ Subgroup.center (StatedSU m (2 ^ 1) K) := by
      rw [Subgroup.mem_center_iff]
      intro v
      obtain ⟨w, rfl⟩ := eR.surjective v
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
    rw [hZU, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (eR.injective (h1.trans (map_one eR).symm))
  have hZker : Subgroup.center L' = ψ.ker := by
    refine le_antisymm (fun z hz => ?_) hker
    have h1 : ψ z ∈ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ 1))) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz l]
    rw [hZR, Subgroup.mem_bot] at h1
    exact h1
  have hLM : LieModel (L' ⧸ Subgroup.center L') .PSU m 2 1 := by
    refine Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by omega, fun h => ?_⟩, K, inferInstance,
      inferInstance, hK, ⟨(QuotientGroup.quotientMulEquivOfEq hZker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩⟩
    have := congrArg Prod.fst h
    simp only at this
    omega
  rw [hMul L' hperf hLM]
  norm_num

theorem qTwoLMSkel_prime_ker {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (_hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (_hMul : PSUTrivialMultiplier m) :
    ∀ b : ↥Bs, ggGamma L hN b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := by
  intro b
  have hS : LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLx hl)
  have hBsE : IsElemAbelian 3 Bs := hBs.2.1
  have hxBs : x ∈ Bs := hBs.1 hxB
  rw [ggGamma_eq_one_iff L hN b]
  constructor
  · intro hb
    have hSp : IsPGroup 3 ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
      fun g => ⟨1, Subtype.ext (by simpa using hBsE.2 g g.2.1)⟩
    have hcyc : IsCyclic ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
      hS.2.2.2.2 _ inf_le_right hSp
    have hcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
      obtain ⟨g, hg⟩ :=
        IsCyclic.exists_ofOrder_eq_natCard (α := ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
      have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hBsE.2 g g.2.1)
      rw [← hg]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)
    have hx3 : orderOf x = 3 :=
      orderOf_eq_prime (hBsE.2 x hxBs) hx1
    have hxS : Subgroup.zpowers x ≤ Bs ⊓ Subgroup.centralizer (L : Set G) :=
      Subgroup.zpowers_le.2 ⟨hxBs, hxC⟩
    have hSeq : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
      (Subgroup.eq_of_le_of_card_ge hxS (by rw [Nat.card_zpowers, hx3]; exact hcard)).symm
    have hbS : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨b.2, hb⟩
    rwa [hSeq] at hbS
  · intro hb
    exact Subgroup.zpowers_le.2 hxC hb

theorem qTwoLMSkel_prime_model {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {m : ℕ} (hG : GGThmIHyp 3 B x L) (_hBs : GGBstar 3 B Bs)
    (_hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 5 ≤ m) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (hMul : PSUTrivialMultiplier m) :
    Nonempty (QTwoUnitaryModel m L) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := qTwoLMPrimeA_marking hm hL
  have hS : LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
  have hperf : commutator ↥L = ⊤ := hS.2.2.2.1.2.2.1
  have hZ : Subgroup.center L = ⊥ := Subgroup.card_eq_one.1 (hMul L hperf hL)
  exact ⟨{ R := LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ 1))
           centerBot := hZ
           perfect := hperf
           theta := e
           centerPrime := qTwoLMPrimeA_centerPrime hm h3 hMul hK
           torusPerm := UModel.ggTorusPermEltSC_unitary hK le_rfl (by omega) Nat.prime_three
             (by norm_num) (by norm_num) h3 }⟩

theorem qTwoLMSkel_prime_rank
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G}
    {x : G} {m : ℕ} (hcfg : GGConfig 3 B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 5 ≤ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) :
    3 ^ 3 ≤ Nat.card (ggGamma L hN).range ∧ GGTorusSelfCent 3 (ggGamma L hN).range := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := qTwoLMPrimeA_marking hm hL
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hperf : commutator ↥L = ⊤ := hS.2.2.2.1.2.2.1
  have hlift := ggTorusLift_unitary (K := K) (n := 1) (d := m) (p := 3) hK le_rfl (by omega)
    (fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega) Nat.prime_three (by norm_num)
  exact ⟨(card_range_ggGamma_bstar_ge hcfg hperf e hN hlift).2,
    ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2⟩

end CFSG.StandardType.QTwo
