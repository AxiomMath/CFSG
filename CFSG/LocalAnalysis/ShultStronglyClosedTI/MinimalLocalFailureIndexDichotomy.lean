module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainCountBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureIndexDichotomyBasic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open scoped Pointwise

namespace IndexDichotomy

variable {G : Type} [Group G]

theorem conjSet_conjSet (S : Set G) (g h : G) :
    conjSet (conjSet S g) h = conjSet S (g * h) := by
  simp only [conjSet, Set.image_image]
  congr 1
  funext x
  group

theorem conjSet_one (S : Set G) : conjSet S 1 = S := by
  simp [conjSet]

theorem le_normalizer_of_le_of_normal {H A S : Subgroup G} (hAH : A ≤ H)
    (hAn : (A.subgroupOf H).Normal) (hSH : S ≤ H) : S ≤ Subgroup.normalizer (A : Set G) :=
  hSH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hAn)

theorem inf_sup_le_sup_inf {A B M : Subgroup G} (hAM : A ≤ M)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) : M ⊓ (A ⊔ B) ≤ A ⊔ (M ⊓ B) := by
  intro x hx
  obtain ⟨hxM, hxAB⟩ := Subgroup.mem_inf.mp hx
  have hxAB' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hBA]
    exact hxAB
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hxAB'
  have hbM : b ∈ M := by
    have h := M.mul_mem (M.inv_mem (hAM ha)) hxM
    rwa [inv_mul_cancel_left] at h
  exact Subgroup.mul_mem_sup ha ⟨hbM, hb⟩

theorem card_sup_eq_mul {A J : Subgroup G} (hJA : J ≤ Subgroup.normalizer (A : Set G))
    (hAJ : A ⊓ J = ⊥) : Nat.card (A ⊔ J : Subgroup G) = Nat.card A * Nat.card J := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_eq_of_bijective
    (fun p : A × J => (⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : (A ⊔ J : Subgroup G)))
    ⟨?_, ?_⟩
  · rintro ⟨a, j⟩ ⟨a', j'⟩ h
    have h' : (a : G) * j = a' * j' := congrArg Subtype.val h
    have hmem : (a' : G)⁻¹ * a ∈ A ⊓ J := by
      refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
      have heq : (a' : G)⁻¹ * a = j' * (j : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
      rw [heq]
      exact J.mul_mem j'.2 (J.inv_mem j.2)
    rw [hAJ, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    rw [hmem] at h'
    exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext (mul_left_cancel h'))
  · rintro ⟨x, hx⟩
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A J hJA] at hx
    obtain ⟨a, ha, j, hj, rfl⟩ := Set.mem_mul.mp hx
    exact ⟨(⟨a, ha⟩, ⟨j, hj⟩), rfl⟩

theorem conj_mem_of_fixes_conjugates {H Q A B M J : Subgroup G} {u : G}
    (hN : {h : G | h ∈ H ∧ conjSet (involutionCoset Q u) h = involutionCoset Q u} =
      ((A ⊔ B : Subgroup G) : Set G))
    (hfix : ∀ g ∈ A ⊔ J, ∀ D ∈ cosetConjugates H Q u, conjSet D g = D)
    (hMH : M ≤ H) (hMn : (M.subgroupOf H).Normal) (hAM : A ≤ M) (hJM : J ≤ M)
    (hMB : M ⊓ B = J) (hBA : B ≤ Subgroup.normalizer (A : Set G)) {h : G} (hh : h ∈ H)
    {r : G} (hr : r ∈ A ⊔ J) : h⁻¹ * r * h ∈ A ⊔ J := by
  have hD : conjSet (involutionCoset Q u) h⁻¹ ∈ cosetConjugates H Q u :=
    ⟨h⁻¹, H.inv_mem hh, rfl⟩
  have h1 := hfix r hr _ hD
  rw [conjSet_conjSet] at h1
  have hrM : r ∈ M := sup_le hAM hJM hr
  have hcM : h⁻¹ * r * h ∈ M := by
    have := (Subgroup.normal_subgroupOf_iff hMH).mp hMn r h⁻¹ hrM (H.inv_mem hh)
    rwa [inv_inv] at this
  have hstab : h⁻¹ * r * h ∈
      {g : G | g ∈ H ∧ conjSet (involutionCoset Q u) g = involutionCoset Q u} := by
    refine ⟨hMH hcM, ?_⟩
    rw [← conjSet_conjSet, h1, conjSet_conjSet, inv_mul_cancel, conjSet_one]
  rw [hN] at hstab
  have := inf_sup_le_sup_inf hAM hBA ⟨hcM, hstab⟩
  rwa [hMB] at this

theorem exists_conj_eq_of_eq_sup {H Q M B : Subgroup G} {u : G} (hHMB : H = M ⊔ B)
    (hBM : B ≤ Subgroup.normalizer (M : Set G))
    (hBfix : ∀ b ∈ B, conjSet (involutionCoset Q u) b = involutionCoset Q u)
    {D D' : Set G} (hD : D ∈ cosetConjugates H Q u) (hD' : D' ∈ cosetConjugates H Q u) :
    ∃ m ∈ M, conjSet D m = D' := by
  have key : ∀ h ∈ H, ∃ m ∈ M,
      conjSet (involutionCoset Q u) h = conjSet (involutionCoset Q u) m := by
    intro h hh
    rw [hHMB, sup_comm, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right B M hBM] at hh
    obtain ⟨b, hb, m, hm, rfl⟩ := Set.mem_mul.mp hh
    exact ⟨m, hm, by rw [← conjSet_conjSet, hBfix b hb]⟩
  obtain ⟨h₁, hh₁, rfl⟩ := hD
  obtain ⟨h₂, hh₂, rfl⟩ := hD'
  obtain ⟨m₁, hm₁, e₁⟩ := key h₁ hh₁
  obtain ⟨m₂, hm₂, e₂⟩ := key h₂ hh₂
  refine ⟨m₁⁻¹ * m₂, M.mul_mem (M.inv_mem hm₁) hm₂, ?_⟩
  rw [e₁, e₂, conjSet_conjSet, mul_inv_cancel_left]

theorem eq_sup_of_relIndex_eq [Finite G] {H M B : Subgroup G} (hMH : M ≤ H) (hBH : B ≤ H)
    (hidx : B.relIndex M = B.relIndex H) : H = M ⊔ B := by
  have hne : B.relIndex (M ⊔ B) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : B.relIndex M ≤ B.relIndex (M ⊔ B) :=
    Subgroup.relIndex_le_of_le_right le_sup_left hne
  have h2 := Subgroup.relIndex_mul_relIndex B (M ⊔ B) H le_sup_right (sup_le hMH hBH)
  have hx : (M ⊔ B).relIndex H ≤ 1 := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.pos_of_ne_zero hne)
    rw [mul_one, h2, ← hidx]
    exact h1
  have hx1 : (M ⊔ B).relIndex H = 1 :=
    le_antisymm hx (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hx1) (sup_le hMH hBH)

end IndexDichotomy

theorem index_dichotomy_of_conclusions
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
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
    (hinv : RootCentralizerInvolutionsConclusion H z beta t)
    (h2 : CentralSectionConclusion H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A)
    (h3 : FourSectionConclusion H z beta t A) :
    IndexDichotomyConclusion H z beta t A := by
  have d : FinalHyps H z beta t :=
    ⟨h, hcomm, hsmallerR1, hbeta, ht, hproper, hker, hexcl, hroot, hinv⟩
  obtain ⟨-, -, -, hq4, ⟨e, hqe⟩, hBH, hXB, -, -, hXcard, -⟩ := d.point_data
  obtain ⟨-, -, -, hJM, hMB, -, -, -, -, -, hBidx⟩ := d.core_data
  obtain ⟨-, h2A⟩ := h2
  obtain ⟨hAJ, hAcard, -⟩ := h2A A hA
  obtain ⟨hAH, hAn, -, hAM, -⟩ := hA
  obtain ⟨u, hu2, hJu, -, -, -, -, -, -, -, hNΔ, -, -, -, hfixθ⟩ := h3
  unfold IndexDichotomyConclusion
  intro B X K Q q M J
  have hq4 : 4 ≤ q := hq4
  have hqe : q = 2 ^ e := hqe
  have hBH : B ≤ H := hBH
  have hXB : X ≤ B := hXB
  have hXcard : Nat.card X = q - 1 := hXcard
  have hJM : J ≤ M := hJM
  have hMB : M ⊓ B = J := hMB
  have hBidx : B.relIndex H = q ^ 3 := hBidx
  have hAJ : A ⊓ J = ⊥ := hAJ
  have hAcard : Nat.card A = q ^ 2 := hAcard
  have hAM : A ≤ M := hAM
  have hJu : (J : Set G) = {1, u} := hJu
  have hNΔ : {g : G | g ∈ H ∧ conjSet (involutionCoset Q u) g = involutionCoset Q u} =
      ((A ⊔ B : Subgroup G) : Set G) := hNΔ
  have hfixθ : ∀ g ∈ A ⊔ J, ∀ D ∈ cosetConjugates H Q u, conjSet D g = D := hfixθ
  have hCX : ∀ x ∈ X, x ≠ 1 → ∀ g ∈ M, g * x = x * g → g ∈ A ⊔ J := by
    intro x hx hx1 g hg hgx
    have hgx' : g ∈ M ⊓ Subgroup.centralizer ({x} : Set G) :=
      ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgx⟩
    exact Subgroup.mem_sup_right ((d.two_core_centralizer_X hx hx1).le hgx')
  have hMH : M ≤ H := TwoCoreGrowth.pointTwoCoreImage_le H
  have hMn : (M.subgroupOf H).Normal := TwoCoreGrowth.pointTwoCoreImage_normal H
  have hM2 : IsPGroup 2 M := TwoCoreGrowth.pointTwoCoreImage_isPGroup H
  have hMn' : ∀ g ∈ H, ∀ m ∈ M, g * m * g⁻¹ ∈ M := fun g hg m hm =>
    (Subgroup.normal_subgroupOf_iff hMH).mp hMn m g hm hg
  have hXH : X ≤ H := hXB.trans hBH
  have hJH : J ≤ H := hJM.trans hMH
  have hBA : B ≤ Subgroup.normalizer (A : Set G) :=
    IndexDichotomy.le_normalizer_of_le_of_normal hAH hAn hBH
  have hJA : J ≤ Subgroup.normalizer (A : Set G) :=
    IndexDichotomy.le_normalizer_of_le_of_normal hAH hAn hJH
  have hBM : B ≤ Subgroup.normalizer (M : Set G) :=
    IndexDichotomy.le_normalizer_of_le_of_normal hMH hMn hBH
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hJcard : Nat.card J = 2 := by
    change Nat.card (J : Set G) = 2
    rw [hJu, Nat.card_coe_set_eq, Set.ncard_pair hu1.symm]
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hqe
    omega
  have hXodd : Odd (Nat.card X) := by
    rw [hXcard, hqe]
    obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0
    refine ⟨2 ^ e' - 1, ?_⟩
    have := Nat.one_le_two_pow (n := e')
    rw [pow_succ]
    omega
  have hRM : A ⊔ J ≤ M := sup_le hAM hJM
  have hRH : A ⊔ J ≤ H := hRM.trans hMH
  have hR2 : IsPGroup 2 (A ⊔ J : Subgroup G) := hM2.to_le hRM
  have hRcard : Nat.card (A ⊔ J : Subgroup G) = 2 * q ^ 2 := by
    rw [IndexDichotomy.card_sup_eq_mul hJA hAJ, hAcard, hJcard, mul_comm]
  have hRn : ∀ g ∈ H, ∀ r ∈ A ⊔ J, g * r * g⁻¹ ∈ A ⊔ J := by
    intro g hg r hr
    have := IndexDichotomy.conj_mem_of_fixes_conjugates hNΔ hfixθ hMH hMn hAM hJM hMB hBA
      (H.inv_mem hg) hr
    rwa [inv_inv] at this
  have hJidx : J.relIndex M = B.relIndex M := by
    rw [← hMB, inf_comm, Subgroup.inf_relIndex_right]
  have hMcard : Nat.card M = 2 * B.relIndex M := by
    have h1 := Subgroup.relIndex_mul_card J M
    rw [inf_eq_left.mpr hJM, hJcard, hJidx] at h1
    omega
  have hBMle : B.relIndex M ≤ q ^ 3 := by
    rw [← hBidx]
    exact Subgroup.relIndex_le_of_le_right hMH Subgroup.index_ne_zero_of_finite
  have hRidx : (A ⊔ J).relIndex M * (2 * q ^ 2) = Nat.card M := by
    have h1 := Subgroup.relIndex_mul_card (A ⊔ J) M
    rwa [inf_eq_left.mpr hRM, hRcard] at h1
  have hRle : (A ⊔ J).relIndex M ≤ q := by
    refine Nat.le_of_mul_le_mul_right ?_ (by positivity : 0 < 2 * q ^ 2)
    rw [hRidx, hMcard]
    calc 2 * B.relIndex M ≤ 2 * q ^ 3 := by omega
      _ = q * (2 * q ^ 2) := by ring
  have hXq : Nat.card X + 1 = q := by omega
  have hdich : (A ⊔ J).relIndex M = 1 ∨ (A ⊔ J).relIndex M = q := by
    by_cases hMR : M ≤ A ⊔ J
    · exact Or.inl (Subgroup.relIndex_eq_one.mpr hMR)
    · right
      obtain ⟨m, hmM, hmR⟩ := IsConcreteLE.not_le_iff_exists.mp hMR
      have := (IndexDichotomy.card_add_one_le_relIndex_of_not_mem hRM hMn' hR2 hRn hXH hXodd
        hCX hmM hmR).1
      omega
  refine ⟨hdich, fun hq => ?_⟩
  have hMcard' : Nat.card M = 2 * q ^ 3 := by
    rw [← hRidx, hq]
    ring
  have hHMB : H = M ⊔ B := IndexDichotomy.eq_sup_of_relIndex_eq hMH hBH (by omega)
  have hBfix : ∀ b ∈ B, conjSet (involutionCoset Q u) b = involutionCoset Q u := by
    intro b hb
    have hb' : b ∈ ((A ⊔ B : Subgroup G) : Set G) := Subgroup.mem_sup_right hb
    rw [← hNΔ] at hb'
    exact hb'.2
  have hreg : ∀ m ∈ M, m ∉ A ⊔ J → ∀ m' ∈ M, m' ∉ A ⊔ J →
      ∃ x ∈ X, m'⁻¹ * (x * m * x⁻¹) ∈ A ⊔ J := fun m hm hmR =>
    (IndexDichotomy.card_add_one_le_relIndex_of_not_mem hRM hMn' hR2 hRn hXH hXodd hCX hm
      hmR).2 (by omega)
  have hsq : ∀ m ∈ M, m ^ 2 ∈ A ⊔ J := by
    have hRnM : ((A ⊔ J).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff hRM).mpr fun r g hr hg => hRn g (hMH hg) r hr
    have h2dvd : 2 ∣ Nat.card (↥M ⧸ (A ⊔ J).subgroupOf M) := by
      change 2 ∣ (A ⊔ J).relIndex M
      rw [hq, hqe]
      exact dvd_pow_self 2 he0
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    obtain ⟨⟨m₀, hm₀⟩, rfl⟩ := QuotientGroup.mk_surjective c
    have hm₀R : m₀ ∉ A ⊔ J := by
      intro hmem
      have h1 : (QuotientGroup.mk ⟨m₀, hm₀⟩ : ↥M ⧸ (A ⊔ J).subgroupOf M) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hmem
      rw [h1, orderOf_one] at hc
      exact absurd hc (by norm_num)
    have hm₀sq : m₀ ^ 2 ∈ A ⊔ J := by
      have h1 := pow_orderOf_eq_one (QuotientGroup.mk ⟨m₀, hm₀⟩ : ↥M ⧸ (A ⊔ J).subgroupOf M)
      rw [hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
      exact h1
    intro m hm
    by_cases hmR : m ∈ A ⊔ J
    · exact pow_mem hmR 2
    obtain ⟨x, hx, hxm⟩ := hreg m₀ hm₀ hm₀R m hm hmR
    have hy : x * m₀ ^ 2 * x⁻¹ ∈ A ⊔ J := hRn x (hXH hx) _ hm₀sq
    have hyH : x * m₀ * x⁻¹ ∈ H := hMH (hMn' x (hXH hx) m₀ hm₀)
    have h1 := hRn (x * m₀ * x⁻¹)⁻¹ (H.inv_mem hyH) _ (inv_mem hxm)
    convert (A ⊔ J).mul_mem ((A ⊔ J).mul_mem hy h1) (inv_mem hxm) using 1
    simp only [sq]
    group
  have hcomm' : ∀ m ∈ M, ∀ m' ∈ M, m * m' * m⁻¹ * m'⁻¹ ∈ A ⊔ J := by
    intro m hm m' hm'
    have h1 := hsq (m * m') (M.mul_mem hm hm')
    have h2 := hRn m'⁻¹ (H.inv_mem (hMH hm')) _ (inv_mem (hsq m hm))
    have h3 := inv_mem (hsq m' hm')
    convert (A ⊔ J).mul_mem ((A ⊔ J).mul_mem h1 h2) h3 using 1
    simp only [sq]
    group
  refine ⟨hMcard', hHMB, ?_, ?_, hsq, hcomm', ?_⟩
  · intro u' hu' hu'1 D hD D' hD'
    have hu'u : u' = u := by
      have hmem : u' ∈ (J : Set G) := hu'
      rw [hJu] at hmem
      rcases hmem with h1 | h1
      · exact absurd h1 hu'1
      · exact h1
    rw [hu'u] at hD hD'
    exact IndexDichotomy.exists_conj_eq_of_eq_sup hHMB hBM hBfix hD hD'
  · exact (Subgroup.normal_subgroupOf_iff hRH).mpr fun r g hr hg => hRn g hg r hr
  · intro m hm hmR m' hm' hm'R
    obtain ⟨x, hx, hxm⟩ := hreg m hm hmR m' hm' hm'R
    refine ⟨⟨x, hx⟩, hxm, fun y hy => Subtype.ext ?_⟩
    refine (IndexDichotomy.eq_of_conj_mem_coset hRM hR2 hRn hXH hXodd hCX hm hmR hx y.2
      ?_).symm
    convert (A ⊔ J).mul_mem (inv_mem hxm) hy using 1
    group

end CFSG.ShultStronglyClosedTI.FinalChain
