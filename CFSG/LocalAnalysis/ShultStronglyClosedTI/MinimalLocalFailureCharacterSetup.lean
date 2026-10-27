module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootTwoCoreStatement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearHullOvergroups
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCharacterSetupTorus
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCharacterSetupQuotient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCharacterSetupNormal
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelStatement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.CharacterSetup

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel

section Transport

variable {G : Type*} [Group G]

theorem index_map_mk'_eq_relIndex {C Q J : Subgroup G} [(Q.subgroupOf C).Normal]
    (hQC : Q ≤ C) (hJC : J ≤ C) :
    ((J.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C))).index =
      (Q ⊔ J).relIndex C := by
  rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
    Subgroup.comap_map_eq, QuotientGroup.ker_mk', ← Subgroup.subgroupOf_sup hJC hQC, sup_comm]
  rfl

theorem quotient_involutions_conjugate {C Q J : Subgroup G} [(Q.subgroupOf C).Normal]
    (hJC : J ≤ C) (hQJ : Q ⊓ J = ⊥) (u : C)
    (hconj : ∀ v ∈ J, orderOf v = 2 → ∃ g ∈ J, g * (u : G) * g⁻¹ = v) :
    ∀ v ∈ (J.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C)), orderOf v = 2 →
      ∃ g ∈ (J.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C)),
        g * QuotientGroup.mk' (Q.subgroupOf C) u * g⁻¹ = v := by
  rintro _ ⟨⟨b, hbC⟩, hbJ, rfl⟩ hv
  have hbJ' : b ∈ J := hbJ
  rw [orderOf_mk'_of_mem hQJ (b := ⟨b, hbC⟩) hbJ'] at hv
  obtain ⟨g, hg, hgb⟩ := hconj b hbJ' hv
  refine ⟨QuotientGroup.mk' (Q.subgroupOf C) ⟨g, hJC hg⟩, ⟨⟨g, hJC hg⟩, hg, rfl⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hgb

theorem quotient_odd_invariant_eq_bot {C Q J : Subgroup G} [(Q.subgroupOf C).Normal]
    (hJC : J ≤ C) (hQJ : Q ⊓ J = ⊥)
    (hodd : ∀ N : Subgroup G, N ≤ J → (∀ g ∈ J, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      Odd (Nat.card N) → N = ⊥) :
    ∀ M : Subgroup (↥C ⧸ Q.subgroupOf C),
      M ≤ (J.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C)) →
      (∀ g ∈ (J.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C)), ∀ m ∈ M,
        g * m * g⁻¹ ∈ M) → Odd (Nat.card M) → M = ⊥ := by
  intro M hMJ hMinv hModd
  set π := QuotientGroup.mk' (Q.subgroupOf C)
  let M' : Subgroup G := (M.comap π).map C.subtype ⊓ J
  have hM'J : M' ≤ J := inf_le_right
  have hmap : (M'.subgroupOf C).map π = M := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨⟨y, hy, hyx⟩, -⟩, rfl⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro x hx
      obtain ⟨⟨b, hbC⟩, hbJ, rfl⟩ := hMJ hx
      exact ⟨⟨b, hbC⟩, ⟨⟨⟨b, hbC⟩, hx, rfl⟩, hbJ⟩, rfl⟩
  have hM'inv : ∀ g ∈ J, ∀ n ∈ M', g * n * g⁻¹ ∈ M' := by
    rintro g hg _ ⟨⟨y, hy, rfl⟩, hnJ⟩
    refine ⟨⟨⟨g, hJC hg⟩ * y * ⟨g, hJC hg⟩⁻¹, ?_, rfl⟩,
      J.mul_mem (J.mul_mem hg hnJ) (J.inv_mem hg)⟩
    change π (⟨g, hJC hg⟩ * y * ⟨g, hJC hg⟩⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    exact hMinv _ ⟨⟨g, hJC hg⟩, hg, rfl⟩ _ hy
  have hM'odd : Odd (Nat.card M') := by
    rwa [← card_map_mk'_of_le hJC hQJ hM'J, hmap]
  rw [← hmap, hodd M' hM'J hM'inv hM'odd, Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem relIndex_eq_two_of_sup_zpowers {W J : Subgroup G} {u : G} (hu : u * u = 1)
    (hinv : ∀ w ∈ W, u⁻¹ * w * u = w⁻¹) (huW : u ∉ W)
    (hJ : W ⊔ Subgroup.zpowers u = J) : W.relIndex J = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨u, hJ ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers u), fun b hb => ?_⟩
  rw [← hJ] at hb
  rcases mem_or_mem_mul_of_mem_sup_zpowers hu hinv hb with hbW | ⟨w, hw, rfl⟩
  · refine Or.inr ⟨hbW, fun hbu => huW ?_⟩
    have h := W.mul_mem (W.inv_mem hbW) hbu
    rwa [inv_mul_cancel_left] at h
  · refine Or.inl ⟨?_, fun hwu => huW ?_⟩
    · rw [mul_assoc, hu, mul_one]
      exact hw
    · have h := W.mul_mem (W.inv_mem hw) hwu
      rwa [inv_mul_cancel_left] at h

end Transport

theorem minimalLocalFailure_root_centralizer_quotient_character_setup_of_conclusions
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t)
    (hodd : LinearChain.RootCentralizerOddCoreFreeConclusion H z)
    (htriv : LinearChain.TrivialPairTwoCoreConclusion H z beta t) :
    LinearChain.RootQuotientCharacterSetupConclusion H z beta t := by
  unfold LinearChain.RootQuotientCharacterSetupConclusion
  intro K Q J C hJ2
  obtain ⟨-, -, hQn, hE2⟩ := htriv hJ2
  have hodd' : ∃ _ : (Q.subgroupOf C).Normal, CFSG.oddCore (↥C ⧸ Q.subgroupOf C) = ⊥ := hodd
  obtain ⟨_, hEodd⟩ := hodd'
  obtain ⟨⟨k, _, _, hkq, ⟨ψ⟩⟩, -, -, -, -, hJB, hNC, hQJ, hJQ, hidx, ⟨f, hf⟩, -, hQM, hQZ,
    -⟩ := hker
  have hJB' : J = pairPointStabilizer H beta ⊓ Subgroup.centralizer (Q : Set G) := hJB
  have hNC' : Subgroup.normalizer (K : Set G) ⊓ C = Q ⊔ J := hNC
  have hQJ' : Q ⊓ J = ⊥ := hQJ
  have hJQ' : J ≤ Subgroup.centralizer (Q : Set G) := hJQ
  have hidx' : (Q ⊔ J).relIndex C ∣ Nat.card Q ^ 2 := hidx
  have hQM' : Q ≤ TwoCoreGrowth.pointTwoCoreImage H := hQM
  have hQZ' : Q ≤ Subgroup.centralizer (TwoCoreGrowth.pointTwoCoreImage H : Set G) := hQZ
  have hJC : J ≤ C := fun x hx => by
    rw [hJB'] at hx
    exact ⟨pairPointStabilizer_le_point H beta hx.1, hx.2⟩
  have hQC : Q ≤ C := fun x hx =>
    ⟨TwoCoreGrowth.pointTwoCoreImage_le H (hQM' hx), Subgroup.mem_centralizer_iff.mpr
      fun y hy => Subgroup.mem_centralizer_iff.mp (hQZ' hx) y (hQM' hy)⟩
  have hQ2 : IsPGroup 2 Q := (TwoCoreGrowth.pointTwoCoreImage_isPGroup H).to_le hQM'
  obtain ⟨-, hq4, -, hover⟩ :=
    minimalLocalFailure_linear_hull_proper_overgroups_normalize_of_conclusions h hcomm
      hsmallerR1 hbeta ht hproper hlin hexcl
  have hq4' : 4 ≤ Nat.card Q := hq4
  obtain ⟨hsimple, a₀, b₀, hab₀⟩ := minimalLocalFailure_nonabelian_simple h
  obtain ⟨e, he⟩ := hQ2.exists_card_eq
  have he2 : 2 ≤ e := by
    by_contra hlt
    have : 2 ^ e < 2 ^ 2 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hk : Nat.card k = 2 ^ e := hkq.trans he
  have := hQn
  obtain ⟨a, -, ha⟩ : ∃ a ≤ e * 2,
      ((J.subgroupOf C).map (QuotientGroup.mk' (Q.subgroupOf C))).index = 2 ^ a := by
    rw [index_map_mk'_eq_relIndex hQC hJC]
    refine (Nat.dvd_prime_pow Nat.prime_two).mp ?_
    rw [pow_mul, ← he]
    exact hidx'
  refine ⟨hQn, hE2, hEodd, fun u huJ hu2 => ?_⟩
  have heven : Even (Nat.card J) := by
    have h1 := orderOf_dvd_natCard (⟨(u : G), huJ⟩ : J)
    rw [Subgroup.orderOf_mk, hu2] at h1
    exact even_iff_two_dvd.mpr h1
  let φ : J →* PSL2MatrixGroup k := ψ.toMonoidHom.comp f
  have hφ : Function.Injective φ := ψ.injective.comp hf
  obtain ⟨hconjJ, htorusJ, hfourJ⟩ := embedded_two_core_free_torus e he2 hk J φ hφ heven hJ2
  obtain ⟨W, hWJ, hWne, hWcyc, hWodd, hWinv, huW, hWform, hWtwo⟩ := htorusJ (u : G) huJ hu2
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => by
    let _ := IsCyclic.commGroup (α := W)
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : W) ⟨b, hb⟩)
  have h3 : 3 ≤ Nat.card W := by
    have h1 := W.one_lt_card_iff_ne_bot.mpr hWne
    obtain ⟨m, hm⟩ := hWodd
    omega
  have hWN : ∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ →
      J ⊓ Subgroup.centralizer (W₀ : Set G) = W ∧
      J ⊓ Subgroup.normalizer (W₀ : Set G) = W ⊔ Subgroup.zpowers (u : G) ∧
      C ⊓ Subgroup.normalizer (W₀ : Set G) ≤ Q ⊔ J := by
    intro W₀ hW₀ hW₀ne
    obtain ⟨hC₀, hN₀⟩ := hWform W₀ hW₀ hW₀ne
    refine ⟨hC₀, hN₀, ?_⟩
    have hW₀K : W₀ ≤ Subgroup.centralizer (K : Set G) := hW₀.trans hWJ
    have hKN : K ≤ Subgroup.normalizer (W₀ : Set G) :=
      (Subgroup.le_centralizer_iff.mp hW₀K).trans (Subgroup.centralizer_le_normalizer _)
    have hNtop : Subgroup.normalizer (W₀ : Set G) < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => ?_
      have : W₀.Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases hsimple.eq_bot_or_eq_top_of_normal W₀ with hbot | htop'
      · exact hW₀ne hbot
      · have ha₀ : a₀ ∈ W₀ := by rw [htop']; exact Subgroup.mem_top a₀
        have hb₀ : b₀ ∈ W₀ := by rw [htop']; exact Subgroup.mem_top b₀
        exact hab₀ (hWcomm a₀ (hW₀ ha₀) b₀ (hW₀ hb₀))
    calc C ⊓ Subgroup.normalizer (W₀ : Set G) ≤ C ⊓ Subgroup.normalizer (K : Set G) :=
          inf_le_inf_left C (hover _ hKN hNtop).2
      _ = Q ⊔ J := by rw [inf_comm]; exact hNC'
  refine ⟨W, hWJ, hWcyc, hWodd, h3, ?_⟩
  intro π Wbar
  obtain ⟨hWbarcyc, hWbarcard, hubar2, hubarW, hubarinv⟩ :=
    quotient_torus_basic hJC hQJ' hWJ u huJ hu2 huW hWinv
  have hCN := quotient_torus_centralizer_normalizer hJC hJQ' hQJ' hQ2 hWJ hWodd hWcomm u hu2
    hWinv hWN
  refine ⟨hWbarcyc, hWbarcard, hubar2, hubarW, hubarinv, hCN, fun N hNn hN => ?_⟩
  have hπu : π u * π u = 1 := by
    have h1 := pow_orderOf_eq_one (π u)
    rwa [hubar2, pow_two] at h1
  let S : Sylow 2 J := default
  obtain ⟨m, hm⟩ := S.isPGroup'.exists_card_eq
  have hm1 : m ≠ 0 := by
    rintro rfl
    apply S.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven)
    exact Subgroup.card_eq_one.mp (by rw [hm, pow_zero])
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  ·
    have hS : Nat.card S = 2 := by rw [hm, show m = 1 by omega, pow_one]
    have hu1 : (u : G) * u = 1 := by
      have h1 := pow_orderOf_eq_one (u : G)
      rwa [hu2, pow_two] at h1
    have huinv : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_right hu1
    have hinv' : ∀ w ∈ W, (u : G)⁻¹ * w * u = w⁻¹ := fun w hw => by
      rw [huinv]
      nth_rw 2 [← huinv]
      exact hWinv w hw
    have hJcard : Nat.card J = 2 * Nat.card W := by
      have h1 := Subgroup.relIndex_mul_card W J
      rw [inf_of_le_left hWJ, relIndex_eq_two_of_sup_zpowers hu1 hinv' huW (hWtwo S hS)] at h1
      exact h1.symm
    have hWbaridx : Wbar.index = 2 ^ (a + 1) := by
      have h1 := Wbar.card_mul_index
      have h2 := ((J.subgroupOf C).map π).card_mul_index
      rw [card_map_mk'_of_le hJC hQJ' le_rfl, ha, hJcard, ← h1, hWbarcard] at h2
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := W))
      rw [← h2, pow_succ]
      ring
    have hWbarcomm : ∀ x ∈ Wbar, ∀ y ∈ Wbar, x * y = y * x := fun x hx y hy => by
      let _ := IsCyclic.commGroup (α := Wbar)
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Wbar) ⟨y, hy⟩)
    exact mem_normal_of_odd_hall_torus hWbaridx hE2 hEodd hWbarcomm (hWbarcard ▸ hWodd) hπu
      hubarinv (fun P hP hPne => (hCN P hP hPne).2.le) N hN
  ·
    have hS : 4 ≤ Nat.card S := by
      rw [hm]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    exact mem_normal_of_involution_conjugacy ha hE2
      (quotient_involutions_conjugate hJC hQJ' u fun v hv hv2 => hconjJ (u : G) huJ v hv hu2 hv2)
      (quotient_odd_invariant_eq_bot hJC hQJ' (hfourJ S hS)) N hN

end CFSG.ShultStronglyClosedTI.LinearChain.CharacterSetup
