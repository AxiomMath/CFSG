module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelStatement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairStabilizerInvolution
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullRegularComplement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem orderOf_conj_eq (h x : G) : orderOf (h⁻¹ * x * h) = orderOf x := by
  simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj h⁻¹).orderOf_eq x

omit [Finite G] in
theorem normal_subgroupOf_of_le {H L Q : Subgroup G} (hLH : L ≤ H)
    (hQ : (Q.subgroupOf H).Normal) : (Q.subgroupOf L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have := hQ.conj_mem ⟨n, hLH n.2⟩ hn ⟨g, hLH g.2⟩
  exact this

structure FinalHyps (H : Subgroup G) (z : G) (beta : rightCosetSpace H) (t : G) : Prop where
  failure : MinimalInvolutionPointLocalFailure H z
  comm : ProperStrongEmbeddingCommutingImages G
  smallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
    2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F
  beta_ne : beta ≠ rightCosetMk H 1
  flip : t ∈ rightPairFlipFiber H z beta
  proper : minimalLocalFailureProperPairHull H z beta t < ⊤
  kernel : LinearChain.LinearPointKernelConclusion H z beta t
  excl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 → UnitaryFixedModelExcludedConclusion H z u
  root : RootCentralizerTwoCoreConclusion H z beta t
  inv : RootCentralizerInvolutionsConclusion H z beta t

namespace FinalHyps

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t : G}

theorem point_data (d : FinalHyps H z beta t) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    Q ≤ H ∧ (Q.subgroupOf H).Normal ∧ IsElemAbelian 2 Q ∧ 4 ≤ Nat.card Q ∧
      (∃ e : ℕ, Nat.card Q = 2 ^ e) ∧ B ≤ H ∧ X ≤ B ∧ X ≤ K ∧ IsCyclic X ∧
      Nat.card X = Nat.card Q - 1 ∧
      ∀ x ∈ X, x ≠ 1 → {ω : rightCosetSpace H | rightCosetTranslate H ω x = ω} =
        {rightCosetMk H 1, beta} := by
  intro B X K Q
  obtain ⟨hQ, hQe, hQ4, -, hXB, -, hXcyc, hXcard, -, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses d.failure d.comm d.smallerR1 d.beta_ne
      d.flip d.proper
  obtain ⟨-, -, -, -, -, -, -, -, -, hXK, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator d.failure d.comm d.smallerR1 d.beta_ne d.flip
      d.proper
  obtain ⟨-, -, -, -, -, hfix, -⟩ :=
    CyclicSemiregular.minimalLocalFailure_proper_pair_cyclic_semiregularity d.failure d.comm
      d.smallerR1 d.beta_ne d.flip d.proper
  exact ⟨minimalLocalFailurePairActionPointHull_le_point H d.failure.local_datum.distinguished_mem,
    minimalLocalFailurePairActionPointHull_normal_in_point H
      d.failure.local_datum.distinguished_mem, hQ, hQ4, hQe, pairPointStabilizer_le_point H beta,
    hXB, hXK, hXcyc, hXcard, hfix⟩

theorem core_data (d : FinalHyps H z beta t) :
    let B := pairPointStabilizer H beta
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    let M := TwoCoreGrowth.pointTwoCoreImage H
    let J := Subgroup.centralizer (K : Set G)
    J = B ⊓ Subgroup.centralizer (Q : Set G) ∧ M = H ⊓ Subgroup.centralizer (Q : Set G) ∧
      J ≤ B ∧ J ≤ M ∧ M ⊓ B = J ∧ Q ≤ M ∧ Q ⊓ J = ⊥ ∧ J ≤ Subgroup.centralizer (Q : Set G) ∧
      Subgroup.normalizer (K : Set G) ⊓ H = Q ⊔ B ∧ Q ⊓ B = ⊥ ∧
      B.relIndex H = Nat.card Q ^ 3 := by
  intro B K Q M J
  obtain ⟨-, -, hBidx, hNK, hQB, hJeq, -, hQJ, hJQ, -, -, -, hQM, -, -, -, -⟩ := d.kernel
  have hM : TwoCoreGrowth.pointTwoCoreImage H =
      H ⊓ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) := d.root.symm
  have hBH : pairPointStabilizer H beta ≤ H := pairPointStabilizer_le_point H beta
  have hJB : Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) ≤
      pairPointStabilizer H beta := hJeq ▸ inf_le_left
  have hJM : Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) ≤
      TwoCoreGrowth.pointTwoCoreImage H := by
    rw [hM, hJeq]
    exact inf_le_inf_right _ hBH
  have hMB : TwoCoreGrowth.pointTwoCoreImage H ⊓ pairPointStabilizer H beta =
      Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) := by
    rw [hM, hJeq, inf_right_comm, inf_eq_right.mpr hBH, inf_comm]
  exact ⟨hJeq, hM, hJB, hJM, hMB, hQM, hQJ, hJQ, hNK, hQB, hBidx⟩

theorem J_data (d : FinalHyps H z beta t) :
    let J := Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)
    IsPGroup 2 J ∧ IsElemAbelian 2 J ∧ J ≠ ⊥ ∧ ∀ j ∈ J, j ≠ 1 → orderOf j = 2 := by
  intro J
  obtain ⟨⟨k, _, _, hk, ⟨ψ⟩⟩, -, -, -, -, -, -, -, -, -, ⟨f, hf⟩, hBinv, -⟩ := d.kernel
  obtain ⟨-, -, -, hJM, -⟩ := d.core_data
  obtain ⟨-, -, -, -, ⟨e, hQe⟩, -⟩ := d.point_data
  have hJ2 : IsPGroup 2 J := (TwoCoreGrowth.pointTwoCoreImage_isPGroup H).to_le hJM
  have hEA : IsElemAbelian 2 J := isElemAbelian_of_injective_psl2 (hk.trans hQe) hJ2 ψ f hf
  have hord : ∀ j ∈ J, j ≠ 1 → orderOf j = 2 := fun j hj hj1 =>
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    orderOf_eq_prime_iff.mpr ⟨hEA.2 j hj, hj1⟩
  refine ⟨hJ2, hEA, ?_, hord⟩
  obtain ⟨u, huB, hu⟩ := proper_pair_stabilizer_exists_involution d.failure d.comm d.beta_ne
    d.flip d.proper
  intro hbot
  have huJ : u ∈ J := hBinv u huB hu
  rw [hbot, Subgroup.mem_bot] at huJ
  rw [huJ, orderOf_one] at hu
  exact absurd hu (by norm_num)

theorem localHull_J
    (d : FinalHyps H z beta t) {j : G}
    (hj : j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hj1 : j ≠ 1) :
    j ∈ pairPointStabilizer H beta ∧ orderOf j = 2 ∧
      Subgroup.closure (involutionPointClass z ∩
        (Subgroup.centralizer ({j} : Set G) : Set G)) =
          minimalLocalFailureProperPairHull H z beta t := by
  obtain ⟨-, -, hJB, -⟩ := d.core_data
  obtain ⟨-, -, -, hord⟩ := d.J_data
  have hjB := hJB hj
  have hj2 := hord j hj hj1
  exact ⟨hjB, hj2, (proper_pair_hull_regular_complement_of_conclusions d.failure d.comm
    d.smallerR1 d.beta_ne d.flip d.proper d.excl hjB hj2).1⟩

theorem point_centralizer_J
    (d : FinalHyps H z beta t) {j : G}
    (hj : j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hj1 : j ≠ 1) :
    H ⊓ Subgroup.centralizer ({j} : Set G) = minimalLocalFailurePairActionPointHull H z ⊔
      (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({j} : Set G)) := by
  obtain ⟨hQH, hQn, -, -, -, hBH, -⟩ := d.point_data
  obtain ⟨-, -, -, -, -, -, -, hJQ, hNK, -⟩ := d.core_data
  obtain ⟨-, -, hLj⟩ := d.localHull_J hj hj1
  have hQj : minimalLocalFailurePairActionPointHull H z ≤ Subgroup.centralizer ({j} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hJQ hj) y hy
  apply le_antisymm
  · intro y ⟨hyH, hyj⟩
    have hyN : y ∈ Subgroup.normalizer (minimalLocalFailureProperPairHull H z beta t : Set G) ⊓
        H := ⟨centralizer_le_normalizer_of_localHull_eq hLj hyj, hyH⟩
    rw [hNK] at hyN
    obtain ⟨c, hc, b, hb, rfl⟩ := exists_mul_of_mem_sup hQH hQn hBH hyN
    have hbj : b ∈ Subgroup.centralizer ({j} : Set G) := by
      have : b = c⁻¹ * (c * b) := by group
      rw [this]
      exact mul_mem (inv_mem (hQj hc)) hyj
    exact mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right ⟨hb, hbj⟩)
  · exact sup_le (le_inf hQH hQj) (inf_le_inf_right _ hBH)

theorem two_core_centralizer_J
    (d : FinalHyps H z beta t) {j : G}
    (hj : j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hj1 : j ≠ 1) :
    TwoCoreGrowth.pointTwoCoreImage H ⊓ Subgroup.centralizer ({j} : Set G) =
      minimalLocalFailurePairActionPointHull H z ⊔
        Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) := by
  obtain ⟨hQH, hQn, -, -, -, hBH, -⟩ := d.point_data
  obtain ⟨-, hM, -, hJM, hMB, hQM, -, hJQ, -⟩ := d.core_data
  obtain ⟨-, hEA, -⟩ := d.J_data
  have hPC := d.point_centralizer_J hj hj1
  apply le_antisymm
  · intro y ⟨hyM, hyj⟩
    have hyH : y ∈ H := TwoCoreGrowth.pointTwoCoreImage_le H hyM
    have hy : y ∈ minimalLocalFailurePairActionPointHull H z ⊔
        (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({j} : Set G)) :=
      hPC ▸ ⟨hyH, hyj⟩
    obtain ⟨c, hc, b, hb, rfl⟩ := exists_mul_of_mem_sup hQH hQn (inf_le_left.trans hBH) hy
    have hbM : b ∈ TwoCoreGrowth.pointTwoCoreImage H := by
      have : b = c⁻¹ * (c * b) := by group
      rw [this]
      exact mul_mem (inv_mem (hQM hc)) hyM
    have hbJ : b ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) :=
      hMB ▸ ⟨hbM, hb.1⟩
    exact mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hbJ)
  · refine le_inf (sup_le hQM hJM) (sup_le ?_ ?_)
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hJQ hj) y hy
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (isMulCommutative_iff.mp hEA.1 ⟨y, hy⟩ ⟨j, hj⟩)

theorem two_core_centralizer_X (d : FinalHyps H z beta t) {x : G}
    (hx : x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) (hx1 : x ≠ 1) :
    TwoCoreGrowth.pointTwoCoreImage H ⊓ Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, hXK, -, -, hfix⟩ := d.point_data
  obtain ⟨-, -, -, hJM, hMB, -⟩ := d.core_data
  apply le_antisymm
  · intro m ⟨hmM, hmx⟩
    have hmH : m ∈ H := TwoCoreGrowth.pointTwoCoreImage_le H hmM
    have hfixm : rightCosetTranslate H (rightCosetTranslate H beta m) x =
        rightCosetTranslate H beta m := by
      rw [rightCosetTranslate_mul, Subgroup.mem_centralizer_singleton_iff.mp hmx,
        ← rightCosetTranslate_mul, show rightCosetTranslate H beta x = beta from ?_]
      have hmem : beta ∈ {ω : rightCosetSpace H | rightCosetTranslate H ω x = ω} := by
        rw [hfix x hx hx1]
        exact Or.inr rfl
      exact hmem
    have hmem : rightCosetTranslate H beta m ∈
        {ω : rightCosetSpace H | rightCosetTranslate H ω x = ω} := hfixm
    rw [hfix x hx hx1] at hmem
    have hβm : rightCosetTranslate H beta m = beta := by
      rcases hmem with hα | hβ
      · exfalso
        apply d.beta_ne
        have hinv : rightCosetTranslate H (rightCosetMk H 1) m⁻¹ = rightCosetMk H 1 := by
          rw [← mem_rightCosetStabilizer_iff, rightCosetStabilizer_base]
          exact H.inv_mem hmH
        rw [← hinv, ← hα, rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
      · exact hβ
    have hmB : m ∈ pairPointStabilizer H beta := by
      refine ⟨?_, (mem_rightCosetStabilizer_iff H beta m).mpr hβm⟩
      rw [rightCosetStabilizer_base]
      exact hmH
    exact hMB ▸ ⟨hmM, hmB⟩
  · refine le_inf hJM ?_
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hj x (hXK hx)).symm

theorem conj_mem_J_iff
    (d : FinalHyps H z beta t) {j : G}
    (hj : j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hj1 : j ≠ 1) {g : G} (hg : g ∈ H) :
    g⁻¹ * j * g ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) ↔
      g ∈ minimalLocalFailurePairActionPointHull H z ⊔ pairPointStabilizer H beta := by
  obtain ⟨hQH, hQn, -, -, -, hBH, -⟩ := d.point_data
  obtain ⟨hJeq, -, -, -, -, -, -, hJQ, hNK, -⟩ := d.core_data
  obtain ⟨-, -, hLj⟩ := d.localHull_J hj hj1
  constructor
  · intro hk
    have hk1 : g⁻¹ * j * g ≠ 1 := by
      intro h1
      apply hj1
      have : j = g * (g⁻¹ * j * g) * g⁻¹ := by group
      rw [this, h1, mul_one, mul_inv_cancel]
    obtain ⟨-, -, hLk⟩ := d.localHull_J hk hk1
    have hgN := mem_normalizer_of_localHull_eq hLj hLk rfl
    have : g ∈ Subgroup.normalizer (minimalLocalFailureProperPairHull H z beta t : Set G) ⊓ H :=
      ⟨hgN, hg⟩
    rwa [hNK] at this
  · intro hgQB
    obtain ⟨c, hc, b, hb, rfl⟩ := exists_mul_of_mem_sup hQH hQn hBH hgQB
    have hcj : c⁻¹ * j * c = j := by
      rw [mul_assoc, ← (Subgroup.mem_centralizer_iff.mp (hJQ hj) c hc), inv_mul_cancel_left]
    have heq : (c * b)⁻¹ * j * (c * b) = b⁻¹ * (c⁻¹ * j * c) * b := by group
    rw [heq, hcj]
    rw [hJeq] at hj ⊢
    refine ⟨?_, ?_⟩
    · exact (pairPointStabilizer H beta).mul_mem
        ((pairPointStabilizer H beta).mul_mem (inv_mem hb) hj.1) hb
    · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have hy' : b * y * b⁻¹ ∈ minimalLocalFailurePairActionPointHull H z := by
        have := hQn.conj_mem ⟨y, hQH hy⟩ hy ⟨b, hBH hb⟩
        exact this
      have hcomm := Subgroup.mem_centralizer_iff.mp hj.2 _ hy'
      calc y * (b⁻¹ * j * b) = b⁻¹ * ((b * y * b⁻¹) * j) * b := by group
        _ = b⁻¹ * (j * (b * y * b⁻¹)) * b := by rw [hcomm]
        _ = b⁻¹ * j * b * y := by group

theorem conjugacyWithin_J_iff
    (d : FinalHyps H z beta t) {j k : G}
    (hj : j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hj1 : j ≠ 1)
    (hk : k ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)) :
    k ∈ conjugacyWithin H j ↔ k ∈ conjugacyWithin (pairPointStabilizer H beta) j := by
  obtain ⟨hQH, hQn, -, -, -, hBH, -⟩ := d.point_data
  obtain ⟨-, -, -, -, -, -, -, hJQ, -⟩ := d.core_data
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    have hgQB := (d.conj_mem_J_iff hj hj1 hg).mp hk
    obtain ⟨c, hc, b, hb, rfl⟩ := exists_mul_of_mem_sup hQH hQn hBH hgQB
    refine ⟨⟨b, hb⟩, ?_⟩
    have hcj : c⁻¹ * j * c = j := by
      rw [mul_assoc, ← (Subgroup.mem_centralizer_iff.mp (hJQ hj) c hc), inv_mul_cancel_left]
    change b⁻¹ * j * b = (c * b)⁻¹ * j * (c * b)
    rw [show (c * b)⁻¹ * j * (c * b) = b⁻¹ * (c⁻¹ * j * c) * b by group, hcj]
  · rintro ⟨⟨b, hb⟩, rfl⟩
    exact ⟨⟨b, hBH hb⟩, rfl⟩

end FinalHyps

end CFSG.ShultStronglyClosedTI.FinalChain
