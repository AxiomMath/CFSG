module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralSectionHomocyclic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
@[expose] def omegaCenterPreimage (Q M : Subgroup G) (hQM : ∀ m ∈ M, ∀ y ∈ Q, m * y = y * m) :
    Subgroup G where
  carrier := {a | a ∈ M ∧ (∀ m ∈ M, a * m * a⁻¹ * m⁻¹ ∈ Q) ∧ a ^ 2 ∈ Q}
  one_mem' := by
    refine ⟨M.one_mem, fun m _ => ?_, ?_⟩
    · rw [one_mul, inv_one, mul_one, mul_inv_cancel]
      exact Q.one_mem
    · rw [one_pow]
      exact Q.one_mem
  mul_mem' := by
    rintro a b ⟨haM, ha, ha2⟩ ⟨hbM, hb, hb2⟩
    refine ⟨M.mul_mem haM hbM, fun m hm => ?_, ?_⟩
    · have hcb := hb m hm
      have key : a * (b * m * b⁻¹ * m⁻¹) * a⁻¹ = b * m * b⁻¹ * m⁻¹ := by
        rw [hQM a haM _ hcb, mul_inv_cancel_right]
      have : a * b * m * (a * b)⁻¹ * m⁻¹ =
          (a * (b * m * b⁻¹ * m⁻¹) * a⁻¹) * (a * m * a⁻¹ * m⁻¹) := by group
      rw [this, key]
      exact Q.mul_mem hcb (ha m hm)
    · have hc := ha b hbM
      have hba : b * a = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by group
      have hca : a * (a * b * a⁻¹ * b⁻¹)⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ * a :=
        hQM a haM _ (Q.inv_mem hc)
      have : (a * b) ^ 2 = (a * b * a⁻¹ * b⁻¹)⁻¹ * a ^ 2 * b ^ 2 := by
        calc (a * b) ^ 2 = a * (b * a) * b := by rw [sq]; group
          _ = a * ((a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b)) * b := by rw [← hba]
          _ = (a * (a * b * a⁻¹ * b⁻¹)⁻¹) * a * b * b := by group
          _ = ((a * b * a⁻¹ * b⁻¹)⁻¹ * a) * a * b * b := by rw [hca]
          _ = (a * b * a⁻¹ * b⁻¹)⁻¹ * a ^ 2 * b ^ 2 := by rw [sq, sq]; group
      rw [this]
      exact Q.mul_mem (Q.mul_mem (Q.inv_mem hc) ha2) hb2
  inv_mem' := by
    rintro a ⟨haM, ha, ha2⟩
    refine ⟨M.inv_mem haM, fun m hm => ?_, ?_⟩
    · have hc := ha m hm
      have hca : a⁻¹ * (a * m * a⁻¹ * m⁻¹)⁻¹ = (a * m * a⁻¹ * m⁻¹)⁻¹ * a⁻¹ :=
        hQM a⁻¹ (M.inv_mem haM) _ (Q.inv_mem hc)
      have : a⁻¹ * m * a⁻¹⁻¹ * m⁻¹ = (a⁻¹ * (a * m * a⁻¹ * m⁻¹)⁻¹) * a := by group
      rw [this, hca, inv_mul_cancel_right]
      exact Q.inv_mem hc
    · rw [inv_pow]
      exact Q.inv_mem ha2

omit [Finite G] in
theorem mem_omegaCenterPreimage {Q M : Subgroup G} {hQM : ∀ m ∈ M, ∀ y ∈ Q, m * y = y * m}
    {a : G} : a ∈ omegaCenterPreimage Q M hQM ↔
      a ∈ M ∧ (∀ m ∈ M, a * m * a⁻¹ * m⁻¹ ∈ Q) ∧ a ^ 2 ∈ Q :=
  Iff.rfl

omit [Finite G] in
theorem omegaCenterPreimage_spec [Finite G] {H Q M : Subgroup G}
    (hQM : ∀ m ∈ M, ∀ y ∈ Q, m * y = y * m) (hQH : Q ≤ H) (hQn : (Q.subgroupOf H).Normal)
    (hQ2 : ∀ y ∈ Q, y ^ 2 = 1) (hQleM : Q < M) (hMH : M ≤ H) (hMn : (M.subgroupOf H).Normal)
    (hM2 : IsPGroup 2 M) :
    omegaCenterPreimage Q M hQM ≤ H ∧ ((omegaCenterPreimage Q M hQM).subgroupOf H).Normal ∧
      Q < omegaCenterPreimage Q M hQM ∧ omegaCenterPreimage Q M hQM ≤ M := by
  have hNM : omegaCenterPreimage Q M hQM ≤ M := fun a ha => (mem_omegaCenterPreimage.mp ha).1
  have hconjM : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M := fun h hh m hm =>
    hMn.conj_mem ⟨m, hMH hm⟩ hm ⟨h, hh⟩
  have hconjQ : ∀ h ∈ H, ∀ y ∈ Q, h * y * h⁻¹ ∈ Q := fun h hh y hy =>
    hQn.conj_mem ⟨y, hQH hy⟩ hy ⟨h, hh⟩
  have hQN : Q ≤ omegaCenterPreimage Q M hQM := by
    intro y hy
    refine mem_omegaCenterPreimage.mpr ⟨hQleM.le hy, fun m hm => ?_, by
      rw [hQ2 y hy]; exact Q.one_mem⟩
    rw [← hQM m hm y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact Q.one_mem
  refine ⟨hNM.trans hMH, ⟨fun a ha h => ?_⟩, lt_of_le_of_ne hQN fun hQN' => ?_, hNM⟩
  · rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨haM, hac, ha2⟩ := mem_omegaCenterPreimage.mp ha
    refine mem_omegaCenterPreimage.mpr ⟨hconjM h h.2 a haM, fun m hm => ?_, ?_⟩
    · have hm' : (h : G)⁻¹ * m * h ∈ M := by
        have := hconjM (h : G)⁻¹ (H.inv_mem h.2) m hm
        rwa [inv_inv] at this
      have := hconjQ h h.2 _ (hac _ hm')
      have heq : (h : G) * a * (h : G)⁻¹ * m * ((h : G) * a * (h : G)⁻¹)⁻¹ * m⁻¹ =
          (h : G) * ((a : G) * ((h : G)⁻¹ * m * h) * (a : G)⁻¹ * ((h : G)⁻¹ * m * h)⁻¹) *
            (h : G)⁻¹ := by
        group
      change (h : G) * a * (h : G)⁻¹ * m * ((h : G) * a * (h : G)⁻¹)⁻¹ * m⁻¹ ∈ Q
      rw [heq]
      exact this
    · change ((h : G) * a * (h : G)⁻¹) ^ 2 ∈ Q
      have : ((h : G) * a * (h : G)⁻¹) ^ 2 = (h : G) * a ^ 2 * (h : G)⁻¹ := by
        rw [sq, sq]; group
      rw [this]
      exact hconjQ h h.2 _ ha2
  ·
    have hQZ : Q.subgroupOf M ≤ Subgroup.center M := by
      intro y hy
      rw [Subgroup.mem_center_iff]
      intro m
      exact Subtype.ext (hQM m m.2 y hy)
    have : (Q.subgroupOf M).Normal := Subgroup.normal_of_le_center hQZ
    have hne : Q.subgroupOf M ≠ ⊤ := by
      rw [Ne, Subgroup.subgroupOf_eq_top]
      exact hQleM.not_ge
    have : Nontrivial (M ⧸ Q.subgroupOf M) := QuotientGroup.nontrivial_iff.mpr hne
    have hp : IsPGroup 2 (M ⧸ Q.subgroupOf M) := hM2.to_quotient _
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Nontrivial (Subgroup.center (M ⧸ Q.subgroupOf M)) := hp.center_nontrivial
    have hZp : IsPGroup 2 (Subgroup.center (M ⧸ Q.subgroupOf M)) := hp.to_subgroup _
    obtain ⟨n, hn, hcard⟩ := hZp.nontrivial_iff_card.mp inferInstance
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2
      (show 2 ∣ Nat.card (Subgroup.center (M ⧸ Q.subgroupOf M)) by
        rw [hcard]; exact dvd_pow_self 2 (by omega))
    obtain ⟨a₁, ha₁⟩ := QuotientGroup.mk_surjective (w : M ⧸ Q.subgroupOf M)
    have hw2 : orderOf (w : M ⧸ Q.subgroupOf M) = 2 := (Subgroup.orderOf_coe w).trans hw
    have ha₁N : (a₁ : G) ∈ omegaCenterPreimage Q M hQM := by
      refine mem_omegaCenterPreimage.mpr ⟨a₁.2, fun m hm => ?_, ?_⟩
      · have hcen := Subgroup.mem_center_iff.mp w.2 (QuotientGroup.mk ⟨m, hm⟩)
        have : (QuotientGroup.mk (a₁ * ⟨m, hm⟩ * a₁⁻¹ * (⟨m, hm⟩ : M)⁻¹) :
            M ⧸ Q.subgroupOf M) = 1 := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
            QuotientGroup.mk_inv, QuotientGroup.mk_inv, ha₁, ← hcen]
          group
        have h5 := (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) _).mp this
        exact h5
      · have : (QuotientGroup.mk (a₁ ^ 2) : M ⧸ Q.subgroupOf M) = 1 := by
          rw [QuotientGroup.mk_pow, ha₁, ← hw2, pow_orderOf_eq_one]
        have h5 := (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) _).mp this
        exact h5
    have ha₁Q : (a₁ : G) ∉ Q := by
      intro hQ'
      have : (QuotientGroup.mk a₁ : M ⧸ Q.subgroupOf M) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hQ'
      rw [ha₁] at this
      rw [this, orderOf_one] at hw2
      exact absurd hw2 (by norm_num)
    exact ha₁Q (hQN'.symm ▸ ha₁N)

namespace FinalHyps

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t : G}

theorem exists_minimal_central_section (d : FinalHyps H z beta t) :
    ∃ A : Subgroup G, IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A := by
  classical
  obtain ⟨hQH, hQn, hQ, -⟩ := d.point_data
  obtain ⟨-, hM, -, hJM, -, hQM', hQJ, -⟩ := d.core_data
  obtain ⟨-, -, hJne, -⟩ := d.J_data
  have hQM : ∀ m ∈ TwoCoreGrowth.pointTwoCoreImage H,
      ∀ y ∈ minimalLocalFailurePairActionPointHull H z, m * y = y * m := by
    intro m hm y hy
    have hmC : m ∈ H ⊓ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) :=
      hM ▸ hm
    exact (Subgroup.mem_centralizer_iff.mp hmC.2 y hy).symm
  have hQltM : minimalLocalFailurePairActionPointHull H z < TwoCoreGrowth.pointTwoCoreImage H := by
    refine lt_of_le_of_ne hQM' fun hQeq => ?_
    obtain ⟨j, hj1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hJne
    have : (j : G) ∈ minimalLocalFailurePairActionPointHull H z ⊓ Subgroup.centralizer
        (minimalLocalFailureProperPairHull H z beta t : Set G) := ⟨hQeq ▸ hJM j.2, j.2⟩
    rw [hQJ, Subgroup.mem_bot] at this
    exact hj1 (Subtype.ext this)
  obtain ⟨h1, h2, h3, h4⟩ := omegaCenterPreimage_spec hQM hQH hQn hQ.2 hQltM
    (TwoCoreGrowth.pointTwoCoreImage_le H) (TwoCoreGrowth.pointTwoCoreImage_normal H)
    (TwoCoreGrowth.pointTwoCoreImage_isPGroup H)
  let P : Subgroup G → Prop := fun N => N ≤ H ∧ (N.subgroupOf H).Normal ∧
    minimalLocalFailurePairActionPointHull H z < N ∧ N ≤ TwoCoreGrowth.pointTwoCoreImage H ∧
    (∀ a ∈ N, ∀ m ∈ TwoCoreGrowth.pointTwoCoreImage H,
      a * m * a⁻¹ * m⁻¹ ∈ minimalLocalFailurePairActionPointHull H z) ∧
    ∀ a ∈ N, a ^ 2 ∈ minimalLocalFailurePairActionPointHull H z
  have hex : ∃ n, ∃ N, P N ∧ Nat.card N = n :=
    ⟨_, _, ⟨h1, h2, h3, h4, fun a ha => (mem_omegaCenterPreimage.mp ha).2.1,
      fun a ha => (mem_omegaCenterPreimage.mp ha).2.2⟩, rfl⟩
  obtain ⟨A, hPA, hAcard⟩ := Nat.find_spec hex
  obtain ⟨hAH, hAn, hQA, hAM, hcomm, hsq⟩ := hPA
  refine ⟨A, hAH, hAn, hQA, hAM, fun N hNH hNn hQN hNA => ?_, hcomm, hsq⟩
  by_cases hNQ : N = minimalLocalFailurePairActionPointHull H z
  · exact Or.inl hNQ
  · right
    have hPN : P N := ⟨hNH, hNn, lt_of_le_of_ne hQN (Ne.symm hNQ), hNA.trans hAM,
      fun a ha => hcomm a (hNA ha), fun a ha => hsq a (hNA ha)⟩
    have hle : Nat.find hex ≤ Nat.card N := Nat.find_min' hex ⟨N, hPN, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hNA (hAcard ▸ hle)

end FinalHyps

theorem central_section_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hroot : RootCentralizerTwoCoreConclusion H z beta t)
    (hinv : RootCentralizerInvolutionsConclusion H z beta t) :
    CentralSectionConclusion H z beta t := by
  have d : FinalHyps H z beta t :=
    ⟨h, hcomm, hsmallerR1, hbeta, ht, hproper, hker, hexcl, hroot, hinv⟩
  refine ⟨d.exists_minimal_central_section, fun A hA => ?_⟩
  exact ⟨d.section_inf_J hA, (d.section_index hA).2, d.section_homocyclic hA,
    d.section_involutions hA,
    fun x hx hx1 => ⟨d.section_centralizer_X_eq_bot hA hx hx1,
      fun a ha hfix => d.section_quotient_fixed hA hx hx1 ha hfix⟩,
    fun j hj hj1 => d.section_commutator_iso hA hj hj1, (d.section_square_hom hA).1⟩

end CFSG.ShultStronglyClosedTI.FinalChain
