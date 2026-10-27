module

public import CFSG.RankThree.GF2n.Smith81.InspKSpCard
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmCent
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCountOmega

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp.KFact

open Subgroup CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank QuadraticMap Module
  CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot CFSG.StandardType.RCSTOm
  CFSG.StandardType.KGOm CFSG.StandardType.RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open scoped MatrixGroups

theorem card_comap_eq_of_le_range {U G : Type*} [Group U] [Group G] {σ : U →* G}
    (hσ : Function.Injective σ) {L : Subgroup G} (hL : L ≤ σ.range) :
    Nat.card (L.comap σ) = Nat.card L :=
  Nat.card_congr (((L.comap σ).equivMapOfInjective σ hσ).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hL))).toEquiv

theorem card_dvd_of_decomp {U : Type} [Group U] [Finite U] {x : U} {R L₁ L₂ : Subgroup U}
    (hC : Subgroup.centralizer ({x} : Set U) = R ⊔ (L₁ ⊔ L₂))
    (hn : L₁ ⊔ L₂ ≤ normalizer (R : Set U)) (hd : Disjoint R (L₁ ⊔ L₂))
    (hd12 : Disjoint L₁ L₂) (h12 : L₁ ≤ centralizer (L₂ : Set U)) (hR2 : IsPGroup 2 R)
    {N N₁ N₂ r r₁ r₂ : ℕ} (hr : Odd r) (hr₁ : Odd r₁) (hr₂ : Odd r₂)
    (hU : Nat.card U = 2 ^ N * r) (h₁ : Nat.card L₁ = 2 ^ N₁ * r₁)
    (h₂ : Nat.card L₂ = 2 ^ N₂ * r₂) :
    Nat.card (Subgroup.centralizer ({x} : Set U)) ∣
      2 ^ (N - N₁ - N₂) * Nat.card L₁ * Nat.card L₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h21 : L₂ ≤ normalizer (L₁ : Set U) :=
    (Subgroup.le_centralizer_iff.mp h12).trans (centralizer_le_normalizer L₁)
  have hL12 : Nat.card (L₁ ⊔ L₂ : Subgroup U) = Nat.card L₁ * Nat.card L₂ :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer L₁ L₂ h21 hd12
  have hCR : Nat.card (Subgroup.centralizer ({x} : Set U)) =
      Nat.card R * (Nat.card L₁ * Nat.card L₂) := by
    rw [hC, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer R (L₁ ⊔ L₂) hn hd,
      hL12]
  obtain ⟨a, ha⟩ := hR2.exists_card_eq
  have hdvd : Nat.card (Subgroup.centralizer ({x} : Set U)) ∣ Nat.card U :=
    Subgroup.card_subgroup_dvd_card _
  rw [hCR, ha, h₁, h₂, hU] at hdvd
  have hle : a + N₁ + N₂ ≤ N := by
    have h1 : 2 ^ (a + N₁ + N₂) ∣ 2 ^ N * r := by
      refine Dvd.dvd.trans ?_ hdvd
      refine ⟨r₁ * r₂, ?_⟩
      rw [pow_add, pow_add]
      ring
    have hcop : Nat.Coprime (2 ^ (a + N₁ + N₂)) r :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hr)
    have h2 : 2 ^ (a + N₁ + N₂) ∣ 2 ^ N := hcop.dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  rw [hCR, ha]
  have h2a : 2 ^ a ∣ 2 ^ (N - N₁ - N₂) := pow_dvd_pow 2 (by omega)
  calc 2 ^ a * (Nat.card L₁ * Nat.card L₂) ∣ 2 ^ (N - N₁ - N₂) * (Nat.card L₁ * Nat.card L₂) :=
        mul_dvd_mul h2a dvd_rfl
    _ = 2 ^ (N - N₁ - N₂) * Nat.card L₁ * Nat.card L₂ := by ring


theorem card_centralizer_dvd_of_frame {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {P₁ P₂ : HypPair Q} (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    (h₁₂ : P₁.Orth P₂)
    (hΩ : omegaGroup (Q.restrict (wSub P₁ P₂))
      (CFSG.StandardType.RCSTOm.nondegenerate_restrict_wSub hQ h₁₂) ≤
      orthDerived (Q.restrict (wSub P₁ P₂)))
    (hWq : CFSG.IsQuasisimple (orthDerived (Q.restrict (wSub P₁ P₂))))
    (hWZ : Subgroup.center (orthDerived (Q.restrict (wSub P₁ P₂))) = ⊥)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U} (hx : σ x = eichler Q P₁.e P₂.e)
    {f N N₂ r r₂ : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : Odd r) (hr₂ : Odd r₂)
    (hU : Nat.card U = 2 ^ N * r)
    (hL₂ : Nat.card (orthDerived (Q.restrict (wSub P₁ P₂))) = 2 ^ N₂ * r₂) :
    Nat.card (Subgroup.centralizer ({x} : Set U)) ∣
      2 ^ (N - f - N₂) * Nat.card SL(2, K) *
        Nat.card (orthDerived (Q.restrict (wSub P₁ P₂))) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite U := Finite.of_injective σ hσ
  have hEich : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  obtain ⟨hC, hn, hd, -⟩ := centralizer_decomp_frame hQ hEΩ hOE h₁₂ hΩ hWq hWZ hσ hσE hx
  have hRE : rootRadical Q P₁ P₂ ≤ σ.range := hσE ▸ rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) P₁ P₂ ≤ σ.range :=
    hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q P₁ P₂ ≤ σ.range := hσE ▸ fun g hg => (mem_omFix.mp hg).1
  have hR2 : IsPGroup 2 ((rootRadical Q P₁ P₂).comap σ) :=
    IsPGroup.comap_of_injective isPGroup_rootRadical σ hσ
  have hd12 : Disjoint ((leviFix (elementaryGroup Q) P₁ P₂).comap σ) ((omFix Q P₁ P₂).comap σ) := by
    rw [Subgroup.disjoint_def]
    intro y hy hy'
    apply hσ
    rw [map_one]
    exact Subgroup.disjoint_def.mp (disjoint_leviFix_omFix h₁₂) (Subgroup.mem_comap.mp hy)
      (Subgroup.mem_comap.mp hy')
  have h12 : (leviFix (elementaryGroup Q) P₁ P₂).comap σ ≤
      Subgroup.centralizer (((omFix Q P₁ P₂).comap σ) : Set U) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro h hh
    apply hσ
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp (leviFix_le_centralizer_omFix h₁₂ hg) (σ h) hh
  have hc1 : Nat.card ((leviFix (elementaryGroup Q) P₁ P₂).comap σ) = Nat.card SL(2, K) :=
    (card_comap_eq_of_le_range hσ hL₁E).trans
      (Nat.card_congr (leviFixEquiv P₁ P₂ h₁₂ hEich).toEquiv)
  have hc2 : Nat.card ((omFix Q P₁ P₂).comap σ) =
      Nat.card (orthDerived (Q.restrict (wSub P₁ P₂))) :=
    (card_comap_eq_of_le_range hσ hL₂E).trans
      (Nat.card_congr (omFixEquiv h₁₂ hQ hEΩ hOE
        (CFSG.StandardType.RCSTOm.nondegenerate_restrict_wSub hQ h₁₂) hΩ).toEquiv)
  have hSL : Nat.card SL(2, K) = 2 ^ f * (2 ^ (2 * f) - 1) := by
    rw [CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hK, ← pow_mul, mul_comm f 2]
  have hodd : Odd (2 ^ (2 * f) - 1) := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [show 2 * (g + 1) = (2 * g + 1) + 1 from by ring, pow_succ]
    exact ⟨2 ^ (2 * g + 1) - 1, by have := Nat.one_le_two_pow (n := 2 * g + 1); omega⟩
  have key := card_dvd_of_decomp (U := U) (x := x) (R := (rootRadical Q P₁ P₂).comap σ)
    (L₁ := (leviFix (elementaryGroup Q) P₁ P₂).comap σ) (L₂ := (omFix Q P₁ P₂).comap σ)
    hC hn hd hd12 h12 hR2 (N := N) (N₁ := f) (N₂ := N₂) hr hodd hr₂ hU
    (by rw [hc1, hSL]) (by rw [hc2, hL₂])
  rwa [hc1, hc2] at key


theorem card_centralizer_dvd_of_hypFrame_five {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {N : ℕ}
    (F : HypFrame Q N) (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    {i j k l m : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hjk : j ≠ k)
    (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) (s t : Bool) {c : K}
    (hc : c ≠ 0) {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U}
    (hx : σ x = eichler Q (F.vec j t) (c • F.vec i s))
    {f N' N₂ r r₂ M : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : Odd r) (hr₂ : Odd r₂)
    (hU : Nat.card U = 2 ^ N' * r) (hM : M = 2 ^ N₂ * r₂)
    (hL₂ : omegaGroup (Q.restrict (wSub (framePair F j t) (smulPair (framePair F i s) hc)))
        (CFSG.StandardType.RCSTOm.nondegenerate_restrict_wSub hQ (orth₁₂ F hij s t hc)) ≤
        orthDerived (Q.restrict (wSub (framePair F j t) (smulPair (framePair F i s) hc))) →
      Nat.card (orthDerived (Q.restrict (wSub (framePair F j t)
        (smulPair (framePair F i s) hc)))) = M) :
    Nat.card (Subgroup.centralizer ({x} : Set U)) ∣
      2 ^ (N' - f - N₂) * Nat.card SL(2, K) * M := by
  have h₁₂ := orth₁₂ F hij s t hc
  have hR := CFSG.StandardType.RCSTOm.nondegenerate_restrict_wSub hQ h₁₂
  have hT := exists_totallySingular_wSub F hik hil him hjk hjl hjm hkl hkm hlm s t hc
  have hΩ := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT
  have hcard := hL₂ hΩ
  have h := card_centralizer_dvd_of_frame hQ hEΩ hOE h₁₂ hΩ
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT)
    (center_orthDerived_eq_bot' hR hT (exists_restrict_ne_zero F hik hjk hc)) hσ hσE hx hf hK hr
    hr₂ hU (hcard.trans hM)
  rwa [hcard] at h


theorem card_SL2_eq_ordBC {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : Nat.card SL(2, K) = CFSG.Open.ordBC 1 (2 ^ f) := by
  rw [← card_statedSp_eq_ordBC hf hK 1]
  exact Nat.card_congr (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).toEquiv

theorem exists_ordD_eq {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    ∃ r, Odd r ∧ CFSG.Open.ordD n (2 ^ f) = 2 ^ (f * (n * (n - 1))) * r :=
  (CFSG.Timmesfeld.Orders.profile_ordD hn hf).two

theorem exists_ordTwistedD_eq {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    ∃ r, Odd r ∧ CFSG.Open.ordTwistedD n (2 ^ f) = 2 ^ (f * (n * (n - 1))) * r :=
  (CFSG.Timmesfeld.Orders.profile_ordTwistedD hn hf).two


theorem card_orthDerived_plus {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {R : QuadraticForm K W} {m f : ℕ} (hm : 4 ≤ m)
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K W = 2 * m) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType R) :
    Nat.card (orthDerived R) = CFSG.Open.ordD m (2 ^ f) := by
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hR hdim hplus
  have hL := CFSG.RankThree.PartOne.lieModel_of_orthDerived_plus hm hf hK e (MulEquiv.refl _)
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two
    (hL.statedClassicalModel (by decide))).2.2.2.1 rfl


theorem card_orthDerived_minus {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {R : QuadraticForm K W} {m f : ℕ} (hm : 4 ≤ m)
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K W = 2 * m) (hnp : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType R) :
    Nat.card (orthDerived R) = CFSG.Open.ordTwistedD m (2 ^ f) := by
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus R hR (by omega) hdim with
    he | ⟨b, c, hirr, he⟩
  · obtain ⟨e⟩ := he
    exact absurd (CFSG.GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv e.symm
      (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K m)) hnp
  · obtain ⟨e⟩ := he
    have hL := CFSG.RankThree.PartOne.lieModel_of_orthDerived_minus hm hf hK hirr e
      (MulEquiv.refl _)
    exact (CFSG.Timmesfeld.card_statedClassicalModel_two
      (hL.statedClassicalModel (by decide))).2.2.2.2 rfl


theorem card_orthDerived_plus_of_le {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {R : QuadraticForm K W} {m f : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ f) (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K W = 2 * m) (hΩ : omegaGroup R hR ≤ orthDerived R)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType R) :
    Nat.card (orthDerived R) = CFSG.Open.ordD m (2 ^ f) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [CFSG.StandardType.card_orthDerived_eq_ordD R hR hdim hΩ hplus, hK]

theorem card_orthDerived_minus_of_le {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {R : QuadraticForm K W} {m f : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ f) (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K W = 2 * m) (hΩ : omegaGroup R hR ≤ orthDerived R)
    (hnp : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType R) :
    Nat.card (orthDerived R) = CFSG.Open.ordTwistedD m (2 ^ f) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [CFSG.StandardType.card_orthDerived_eq_ordTwistedD R hR hdim hΩ hnp, hK]

theorem exponent_centralizer_eq {f n : ℕ} (hn : 3 ≤ n) :
    f * (n * (n - 1)) - f - f * ((n - 2) * (n - 2 - 1)) = f * (4 * n - 7) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : m + 3 - 1 = m + 2 := by omega
  have h2 : m + 3 - 2 = m + 1 := by omega
  have h3 : m + 1 - 1 = m := by omega
  have h4 : 4 * (m + 3) - 7 = 4 * m + 5 := by omega
  rw [h1, h2, h3, h4]
  have h5 : f * ((m + 3) * (m + 2)) = f * ((m + 1) * m) + f * (4 * m + 5) + f := by ring
  omega

@[expose] noncomputable def stdLongRootPlus (K : Type) [Field K] {n : ℕ} (hn : 3 ≤ n) :
    spinGroup (quadPlus n K) :=
  (plusFrame n K hn).longRoot (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (by simp) true true
    (Multiplicative.ofAdd 1)

theorem card_centralizer_longRoot_plus_dvd {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hU : Nat.card (spinGroup (quadPlus n K)) = CFSG.Open.ordD n (2 ^ f)) :
    Nat.card (Subgroup.centralizer ({stdLongRootPlus K (by omega : 3 ≤ n)} :
        Set (spinGroup (quadPlus n K)))) ∣
      (2 ^ f) ^ (4 * n - 7) * CFSG.Open.ordBC 1 (2 ^ f) * CFSG.Open.ordD (n - 2) (2 ^ f) := by
  have hn3 : 3 ≤ n := by omega
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp
  have hOE : orthDerived (quadPlus n K) ≤ elementaryGroup (quadPlus n K) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadPlus hn3]
  obtain ⟨r, hr, hUr⟩ := exists_ordD_eq (n := n) (by omega) hf
  obtain ⟨r₂, hr₂, hL₂r⟩ := exists_ordD_eq (n := n - 2) (by omega) hf
  have hdimV : finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hplus := isPlusType_restrict_wSub_of_hypFrame (plusFrame n K hn3) hdimV h12 true true
    (one_ne_zero (α := K))
  have h₁₂ := orth₁₂ (plusFrame n K hn3) h12 true true (one_ne_zero (α := K))
  have hR := CFSG.StandardType.RCSTOm.nondegenerate_restrict_wSub
    (nondegenerate_polarBilin_quadPlus n K) h₁₂
  have hdimW : finrank K (wSub (framePair (plusFrame n K hn3) ⟨2, by omega⟩ true)
      (smulPair (framePair (plusFrame n K hn3) ⟨1, by omega⟩ true) (one_ne_zero (α := K)))) =
      2 * (n - 2) := by
    have := finrank_wSub_add_four (Q := quadPlus n K) h₁₂
    omega
  have key := card_centralizer_dvd_of_hypFrame_five (plusFrame n K hn3)
    (nondegenerate_polarBilin_quadPlus n K)
    (CFSG.StandardType.RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn3) hOE
    (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (k := ⟨3, by omega⟩) (l := ⟨4, by omega⟩)
    (m := ⟨0, by omega⟩) h12 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) true true (one_ne_zero (α := K))
    CFSG.StandardType.RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus hn3)
    (CFSG.StandardType.RootCentOmega.spinAction_longRoot_eq_eichler _ h12 true true 1) hf hK hr
    hr₂ (hU.trans hUr) hL₂r
    (fun hΩ => card_orthDerived_plus_of_le (by omega) hK hR hdimW hΩ hplus)
  rw [card_SL2_eq_ordBC hf hK] at key
  refine key.trans ?_
  rw [exponent_centralizer_eq hn3, pow_mul]

@[expose] noncomputable def stdLongRootMinus (K : Type) [Field K] {n : ℕ} (hn : 4 ≤ n) (b c : K) :
    spinGroup (quadMinus n K b c) :=
  (minusFrame n b c).longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp) true true
    (Multiplicative.ofAdd 1)

theorem card_centralizer_longRoot_minus_dvd {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n)
    (hU : Nat.card (spinGroup (quadMinus n K b c)) = CFSG.Open.ordTwistedD n (2 ^ f)) :
    Nat.card (Subgroup.centralizer ({stdLongRootMinus K (by omega : 4 ≤ n) b c} :
        Set (spinGroup (quadMinus n K b c)))) ∣
      (2 ^ f) ^ (4 * n - 7) * CFSG.Open.ordBC 1 (2 ^ f) *
        CFSG.Open.ordTwistedD (n - 2) (2 ^ f) := by
  have hn4 : 4 ≤ n := by omega
  set F := (minusFrame n b c).toHypFrame with hF
  have h01 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨1, by omega⟩ := by simp
  have ha : (1 : K) ≠ 0 := one_ne_zero
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have hEΩ := CFSG.StandardType.RootCentOmega.elementaryGroup_quadMinus_le_omegaGroup hirr hn4
  have hOE : orthDerived (quadMinus n K b c) ≤ elementaryGroup (quadMinus n K b c) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadMinus hn4 hirr]
  obtain ⟨r, hr, hUr⟩ := exists_ordTwistedD_eq (n := n) (by omega) hf
  obtain ⟨r₂, hr₂, hL₂r⟩ := exists_ordTwistedD_eq (n := n - 2) (by omega) hf
  have h₁₂ : (framePair F ⟨1, by omega⟩ true).Orth
      (smulPair (framePair F ⟨0, by omega⟩ true) ha) := orth₁₂ F h01 true true ha
  have hR := CFSG.StandardType.RCSTOm.nondegenerate_restrict_wSub hQ h₁₂
  have hdimW : finrank K (wSub (framePair F ⟨1, by omega⟩ true)
      (smulPair (framePair F ⟨0, by omega⟩ true) ha)) = 2 * (n - 2) := by
    have h := finrank_wSub_add_four (Q := quadMinus n K b c) h₁₂
    rw [finrank_quadMinus (by omega)] at h
    omega
  have hts : ∀ U : Submodule K (wSub (framePair F ⟨1, by omega⟩ true)
      (smulPair (framePair F ⟨0, by omega⟩ true) ha)), finrank K U = n - 2 →
      ∃ u ∈ U, (quadMinus n K b c).restrict (wSub (framePair F ⟨1, by omega⟩ true)
        (smulPair (framePair F ⟨0, by omega⟩ true) ha)) u ≠ 0 :=
    fun U hU => exists_restrict_ne_zero_minus (by omega) hirr h₁₂ U hU
  have hneg : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType ((quadMinus n K b c).restrict
      (wSub (framePair F ⟨1, by omega⟩ true) (smulPair (framePair F ⟨0, by omega⟩ true) ha))) :=
    CFSG.StandardType.not_isPlusType_of_forall_ne_zero (d := n - 2) hdimW hts
  have hx := CFSG.StandardType.RootCentOmega.spinAction_longRoot_eq_eichler F h01 true true 1
  have key : Nat.card (Subgroup.centralizer ({stdLongRootMinus K hn4 b c} :
      Set (spinGroup (quadMinus n K b c)))) ∣
      2 ^ (f * (n * (n - 1)) - f - f * ((n - 2) * (n - 2 - 1))) * Nat.card SL(2, K) *
        CFSG.Open.ordTwistedD (n - 2) (2 ^ f) := by
    rcases (show n = 5 ∨ 6 ≤ n by omega) with hn5 | hn6
    · have hdim6 : finrank K (wSub (framePair F ⟨1, by omega⟩ true)
          (smulPair (framePair F ⟨0, by omega⟩ true) ha)) = 6 := by omega
      have hts3 : ∀ U : Submodule K (wSub (framePair F ⟨1, by omega⟩ true)
          (smulPair (framePair F ⟨0, by omega⟩ true) ha)), finrank K U = 3 →
          ∃ u ∈ U, (quadMinus n K b c).restrict (wSub (framePair F ⟨1, by omega⟩ true)
            (smulPair (framePair F ⟨0, by omega⟩ true) ha)) u ≠ 0 :=
        fun U hU => hts U (by omega)
      have hΩ := omegaGroup_le_orthDerived_of_six hR hdim6 hts3
      obtain ⟨hWq, hWZ⟩ := isQuasisimple_orthDerived_of_six hR hdim6 hts3
      have hcard := card_orthDerived_minus_of_le (by omega) hK hR hdimW hΩ hneg
      have h := card_centralizer_dvd_of_frame hQ hEΩ hOE h₁₂ hΩ hWq hWZ
        (CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirr)
        (range_spinAction_quadMinus hn4 hirr) hx hf hK hr hr₂ (hU.trans hUr)
        (hcard.trans hL₂r)
      rwa [hcard] at h
    · exact card_centralizer_dvd_of_hypFrame_five F hQ hEΩ hOE
        (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (k := ⟨2, by omega⟩) (l := ⟨3, by omega⟩)
        (m := ⟨4, by omega⟩) h01 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) true true ha
        (CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirr)
        (range_spinAction_quadMinus hn4 hirr) hx hf hK hr hr₂ (hU.trans hUr) hL₂r
        (fun hΩ => card_orthDerived_minus_of_le (by omega) hK hR hdimW hΩ hneg)
  rw [card_SL2_eq_ordBC hf hK] at key
  refine key.trans ?_
  rw [exponent_centralizer_eq (by omega : 3 ≤ n), pow_mul]

theorem card_spinGroup_quadPlus {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hn : 4 ≤ n) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    Nat.card (spinGroup (quadPlus n K)) = CFSG.Open.ordD n (2 ^ f) := by
  have hn3 : 3 ≤ n := by omega
  have hOE : orthDerived (quadPlus n K) = elementaryGroup (quadPlus n K) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadPlus hn3]
  have hdim : finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  rw [← card_orthDerived_plus (m := n) hn hf hK (nondegenerate_polarBilin_quadPlus n K) hdim
    (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K n), hOE, ← range_spinAction_quadPlus hn3]
  exact Nat.card_congr (MonoidHom.ofInjective
    CFSG.StandardType.RootCentOmega.spinAction_quadPlus_injective).toEquiv

theorem card_spinGroup_quadMinus {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    Nat.card (spinGroup (quadMinus n K b c)) = CFSG.Open.ordTwistedD n (2 ^ f) := by
  have hOE : orthDerived (quadMinus n K b c) = elementaryGroup (quadMinus n K b c) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadMinus hn hirr]
  rw [← card_orthDerived_minus (m := n) hn hf hK
    (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
    (CFSG.StandardType.RCSTOm.finrank_quadMinus (by omega))
    (CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by omega) hirr), hOE,
    ← range_spinAction_quadMinus hn hirr]
  exact Nat.card_congr (MonoidHom.ofInjective
    (CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirr)).toEquiv

theorem card_centralizer_conj_mulEquiv {P Y : Type*} [Group P] [Group Y] (e : P ≃* Y) (g x : P) :
    Nat.card (Subgroup.centralizer ({e (g * x * g⁻¹)} : Set Y)) =
      Nat.card (Subgroup.centralizer ({x} : Set P)) := by
  have hconj : g * x * g⁻¹ = (MulAut.conj g) x := rfl
  rw [card_centralizer_mulEquiv e, hconj, card_centralizer_mulEquiv (MulAut.conj g) x]

end CFSG.RankThree.GF2n.Smith81.Insp.KFact
