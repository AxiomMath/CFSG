module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroup
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiScalarAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiScalarFitting

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ShultStronglyClosedTI.ProperPairModel CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ker_conjToAut (Q N : Subgroup G) (hN : N ≤ Subgroup.normalizer (Q : Set G)) :
    (conjToAut Q N hN).ker = (Subgroup.centralizer (Q : Set G)).subgroupOf N := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hn y hy
    have h := congrArg (fun α : MulAut Q => ((α ⟨y, hy⟩ : Q) : G)) hn
    simp only [conjToAut_apply_coe, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  · intro hn
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [conjToAut_apply_coe, MulAut.one_apply, ← hn y y.2, mul_inv_cancel_right]

theorem not_dvd_suzuki_norm_of_dvd_sub_one {q p : ℕ} (hp : p.Prime) (hq : 1 ≤ q)
    (hpq : p ∣ q - 1) : ¬ p ∣ q ^ 2 - q + 1 := by
  intro h
  have h1 : q ^ 2 - q + 1 = q * (q - 1) + 1 := by
    rcases q with _ | q
    · omega
    · simp only [Nat.add_sub_cancel]
      ring_nf
      omega
  rw [h1] at h
  have h2 : p ∣ q * (q - 1) := Dvd.dvd.mul_left hpq q
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h2).mp h))

theorem fittingSubgroup_point_image_eq_of_exclusion
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* suzukiGroup m k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hHN : H ≤ Subgroup.normalizer (minimalLocalFailurePairActionPointHull H z : Set G)) :
    CFSG.fittingSubgroup (conjToAut (minimalLocalFailurePairActionPointHull H z) H hHN).range =
      ((rightInvolutionCommutatorSubgroup t (pairOddCore H beta)).subgroupOf H).map
        (conjToAut (minimalLocalFailurePairActionPointHull H z) H hHN).rangeRestrict := by
  set B := pairPointStabilizer H beta with hBdef
  set X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta) with hXdef
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set ρ := conjToAut Q H hHN with hρ
  obtain ⟨m, k, _, _, hk, hm, hQcard, hKB, ψ, -, hψB, -, hQK, hQZ, T, hTM, -, -, -, hBT, -, -,
    hTU, -, -, -, -, e, he⟩ := proper_pair_suzuki_structure h hcomm hsmallerR1 hbeta ht hproper hSz
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, hCodd, -⟩, -⟩ :=
    minimalLocalFailure_suzuki_point_group_action_odd_of_conclusions h hcomm hsmallerR1 hbeta ht
      hproper hBinv hSz hexcl
  obtain ⟨-, -, hQ4, hQclass, hXB, -, -, hXcard, -, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, hHB⟩ :=
    pair_stabilizer_relIndex_eq_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv hSz hexcl
  have hXC := torus_inf_centralizer_eq_bot h hcomm hsmallerR1 hbeta ht hproper
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hXH : X ≤ H := hXB.trans hBH
  have hTK : T ≤ minimalLocalFailureProperPairHull H z beta t := fun x hx => (hTM hx).2
  have hq4 : 4 ≤ Nat.card Q := hQ4
  obtain ⟨sc, hsci, hsc⟩ := exists_scalar_hom e
  have hXcard' : Nat.card X = Nat.card k - 1 := by rw [hXcard, hk, hQcard]
  have hXbar : (X.subgroupOf H).map ρ = sc.range :=
    map_conj_torus_eq_range hk ψ hψB hKB e he hXH hHN hXC hXcard' sc hsci hsc
  have hTbot : T ≤ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := fun x _ =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  have hBsemi : ∀ b : H, (b : G) ∈ B → ρ b ∈ coordSemilinearGroup e := by
    intro b hb
    obtain ⟨c, σ, hcσ⟩ := exists_semilinear_conj hm hk ψ hTK hQK hTU hQZ hTbot (inf_bot_eq T) e he
      (g := b) (by rw [sup_bot_eq]; exact hBT hb) (hHN b.2)
    exact ⟨c, σ, fun b' => Subtype.ext (by rw [conjToAut_apply_coe]; exact hcσ b')⟩
  set π := ρ.rangeRestrict with hπ
  have hπcoe : ∀ g : H, ((π g : ρ.range) : MulAut Q) = ρ g := fun g => rfl
  have hπsurj : Function.Surjective π := ρ.rangeRestrict_surjective
  set Bt := (B.subgroupOf H).map π with hBt
  set Xt := (X.subgroupOf H).map π with hXt
  have hmemXt : ∀ a : ρ.range, a ∈ Xt ↔ (a : MulAut Q) ∈ sc.range := by
    intro a
    rw [← hXbar]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxa⟩
      exact ⟨x, hx, Subtype.ext hxa⟩
  have hXtBt : Xt ≤ Bt := Subgroup.map_mono fun x hx => hXB hx
  let j : Bt →* MulAut Q := ρ.range.subtype.comp Bt.subtype
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hFB : CFSG.fittingSubgroup Bt = sc.range.comap j := by
    refine fittingSubgroup_eq_comap_scalar e hk j hj sc hsci hsc (fun a => ?_) (fun c => ?_)
    · obtain ⟨b, hb, hba⟩ := a.2
      change ((a : ρ.range) : MulAut Q) ∈ _
      rw [← hba, hπcoe]
      exact hBsemi b hb
    · have hc : sc c ∈ (X.subgroupOf H).map ρ := hXbar ▸ ⟨c, rfl⟩
      obtain ⟨x, hx, hxc⟩ := hc
      exact ⟨⟨π x, hXtBt ⟨x, hx, rfl⟩⟩, hxc⟩
  have htrans : ∀ y₀ y : Q, y₀ ≠ 1 → y ≠ 1 → ∃ a ∈ ρ.range, a y₀ = y := by
    intro y₀ y hy₀ hy
    have hy₀' : (y₀ : G) ∈ conjugacyWithin H z := by
      rw [← hQclass]
      exact ⟨y₀.2, fun h1 => hy₀ (Subtype.ext h1)⟩
    have hy' : (y : G) ∈ conjugacyWithin H z := by
      rw [← hQclass]
      exact ⟨y.2, fun h1 => hy (Subtype.ext h1)⟩
    obtain ⟨h₀, hh₀⟩ := hy₀'
    obtain ⟨h₁, hh₁⟩ := hy'
    refine ⟨ρ (h₁⁻¹ * h₀), ⟨_, rfl⟩, Subtype.ext ?_⟩
    rw [conjToAut_apply_coe, ← hh₀, ← hh₁]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hBtidx : Bt.index ∣ Nat.card Q ^ 3 * (Nat.card Q ^ 2 - Nat.card Q + 1) := by
    rw [← hHB]
    exact Subgroup.index_map_dvd _ hπsurj
  have hFle : CFSG.fittingSubgroup ρ.range ≤ Bt := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hpq : (p : ℕ) ∣ Nat.card Q - 1
    · refine pCore_le_of_not_dvd_index fun hp => ?_
      have hp' := hp.trans hBtidx
      have hpp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.1.2
      rcases (Nat.Prime.dvd_mul hpp).mp hp' with h1 | h1
      · have h2 : (p : ℕ) ∣ 2 := by
          rw [hQcard] at h1
          exact hpp.dvd_of_dvd_pow (hpp.dvd_of_dvd_pow h1)
        have h3 : (p : ℕ) = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2
        rw [h3, hQcard] at hpq
        have : 2 ∣ 2 ^ (2 * m + 1) := dvd_pow_self 2 (by omega)
        have : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
        omega
      · exact not_dvd_suzuki_norm_of_dvd_sub_one hpp (by omega) hpq h1
    · rw [pCore_eq_bot_of_transitive htrans hpq]
      exact bot_le
  have hFX : CFSG.fittingSubgroup ρ.range ≤ Xt := by
    intro a ha
    have h1 : (⟨a, hFle ha⟩ : Bt) ∈ CFSG.fittingSubgroup Bt :=
      fittingSubgroup_subgroupOf_le Bt hFle ha
    rw [hFB] at h1
    exact (hmemXt a).mpr h1
  have hsolv : Group.IsSolvable ρ.range := by
    refine CFSG.FeitThompson.isSolvable_of_odd_natCard _ ?_
    rw [← Subgroup.index_ker, ker_conjToAut]
    have hsub : (Subgroup.centralizer (Q : Set G)).subgroupOf H =
        (H ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf H := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
    rw [hsub]
    exact hCodd
  refine le_antisymm hFX fun a ha => ?_
  refine CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
    (Subgroup.mem_centralizer_iff.mpr fun f hf => ?_)
  obtain ⟨c, hc⟩ := (hmemXt a).mp ha
  obtain ⟨d, hd⟩ := (hmemXt f).mp (hFX hf)
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc, ← hd, ← map_mul, ← map_mul, mul_comm]

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
