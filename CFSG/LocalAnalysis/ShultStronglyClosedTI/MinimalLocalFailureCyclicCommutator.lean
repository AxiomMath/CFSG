module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicModel

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CyclicPair

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem proper_pair_stabilizer_eq_point_intersection
    {H : Subgroup G} {z : G} {beta : rightCosetSpace H}
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    pairPointStabilizer H beta = H ⊓ rightConjugate H t := by
  have hbetaeq : beta = rightCosetMk H t := by
    simpa only [rightCosetTranslate_mk, one_mul] using ht.2.symm
  rw [pairPointStabilizer, rightCosetStabilizer_base, hbetaeq, rightCosetStabilizer_mk]

theorem proper_pair_commutator_cyclic_and_odd
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    X ≤ pairOddCore H beta ∧ X ≤ minimalLocalFailureProperPairHull H z beta t ∧
      IsCyclic X ∧ Odd (Nat.card X) := by
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  let K := minimalLocalFailureProperPairHull H z beta t
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hXeq : X = Subgroup.closure (pairInvertedSet H beta t) :=
    pair_commutator_eq_closure_inverted_set h.local_datum S hzS hzcenter hbeta ht
  have hXI : X ≤ pairOddCore H beta :=
    (pair_commutator_le_odd_core h.local_datum S hzS hzcenter hbeta ht).1
  have hXK : X ≤ K := by
    intro x hx
    exact Subgroup.subset_closure (Or.inr hx)
  obtain ⟨_, _, _, T, hTset, hTcyclic, _⟩ :=
    proper_pair_full_inversion_torus h hcomm hsmallerR1 hbeta ht hproper
  have hXT : X ≤ T := by
    rw [hXeq]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rw [hTset]
    refine ⟨?_, hx.2, hXK ?_⟩
    · rw [← proper_pair_stabilizer_eq_point_intersection ht]
      exact (pairOddCore_le H beta t).1 hx.1
    · rw [hXeq]
      exact Subgroup.subset_closure hx
  let : IsCyclic T := hTcyclic
  exact ⟨hXI, hXK, Subgroup.isCyclic_of_le hXT,
    (pairOddCore_odd H beta).of_dvd_nat (Subgroup.card_dvd_of_le hXI)⟩

theorem proper_pair_commutator_exact_inversion_set
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    IsMulCommutative X ∧ (∀ x : G, x ∈ X → rightConjugateElem x t = x⁻¹) ∧
      (X : Set G) = {x : G | x ∈ pairOddCore H beta ∧ rightConjugateElem x t = x⁻¹} := by
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  obtain ⟨hXI, _, hXcyclic, _⟩ :=
    proper_pair_commutator_cyclic_and_odd h hcomm hsmallerR1 hbeta ht hproper
  let : IsCyclic X := hXcyclic
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hXeq : X = Subgroup.closure (pairInvertedSet H beta t) :=
    pair_commutator_eq_closure_inverted_set h.local_datum S hzS hzcenter hbeta ht
  have hcommX : ∀ a b : G, a ∈ X → b ∈ X → a * b = b * a := by
    intro a b ha hb
    exact congrArg (fun x : X => (x : G))
      ((isMulCommutative_iff.mp (inferInstance : IsMulCommutative X))
        (⟨a, ha⟩ : X) (⟨b, hb⟩ : X))
  have hinv : ∀ x : G, x ∈ X → rightConjugateElem x t = x⁻¹ := by
    intro x hx
    rw [hXeq] at hx
    refine Subgroup.closure_induction
      (p := fun x _ => rightConjugateElem x t = x⁻¹) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact hy.2
    · simp [rightConjugateElem]
    · intro a b ha hb hai hbi
      have hab : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
        apply hcommX
        · exact X.inv_mem (hXeq.symm ▸ ha)
        · exact X.inv_mem (hXeq.symm ▸ hb)
      have hmul : rightConjugateElem (a * b) t =
          rightConjugateElem a t * rightConjugateElem b t := by
        unfold rightConjugateElem
        group
      rw [hmul, hai, hbi, mul_inv_rev, hab]
    · intro a _ hai
      have hinverse : rightConjugateElem a⁻¹ t = (rightConjugateElem a t)⁻¹ := by
        unfold rightConjugateElem
        group
      rw [hinverse, hai]
  refine ⟨inferInstance, hinv, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨hXI hx, hinv x hx⟩
  · intro x hx
    exact (show x ∈ X from hXeq.symm ▸ Subgroup.subset_closure hx)

theorem proper_pair_commutator_card
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    Nat.card (rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) =
      Nat.card (conjugacyWithin H z) := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hset := (proper_pair_commutator_exact_inversion_set
    h hcomm hsmallerR1 hbeta ht hproper).2.2
  have hcard := Nat.card_congr (Set.equivOfEq hset)
  exact hcard.trans (pair_inverted_set_card h.local_datum S hzS hzcenter hbeta ht)

theorem proper_pair_commutator_inf_odd_core_eq_bot
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ⊓
      minimalLocalFailureProperPairOddCore H z beta t = ⊥ := by
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  have hcentral := (proper_pair_full_odd_core_central h hcomm hbeta ht hproper).2
  have hinv := (proper_pair_commutator_exact_inversion_set
    h hcomm hsmallerR1 hbeta ht hproper).2.1
  have hodd := (proper_pair_commutator_cyclic_and_odd
    h hcomm hsmallerR1 hbeta ht hproper).2.2.2
  apply le_antisymm _ bot_le
  intro x hx
  have htx : t * x = x * t :=
    (Subgroup.mem_centralizer_iff.mp (hcentral hx.2)) t
      (minimalLocalFailureProperPair_flip_mem H z beta t)
  have hfix : rightConjugateElem x t = x := by
    unfold rightConjugateElem
    calc
      t⁻¹ * x * t = t⁻¹ * (x * t) := mul_assoc _ _ _
      _ = t⁻¹ * (t * x) := by rw [htx]
      _ = x := inv_mul_cancel_left t x
  have hself : x = x⁻¹ := hfix.symm.trans (hinv x hx.1)
  have hsquare : x ^ 2 = 1 := by
    rw [pow_two]
    calc
      x * x = x⁻¹ * x := congrArg (fun y : G => y * x) hself
      _ = 1 := inv_mul_cancel x
  have horder : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsquare
  have hoddorder : Odd (orderOf x) := hodd.of_dvd_nat (X.orderOf_dvd_natCard hx.1)
  have hone : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp horder with heq | heq
    · exact heq
    · rw [heq] at hoddorder
      exact (by norm_num at hoddorder)
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)

end CFSG.ShultStronglyClosedTI.CyclicPair
