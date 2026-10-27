module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofKMd
public import CFSG.RankThree.PartTwo.Sec17.Item17Res10ProofKMd
public import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofLd
public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofONPoint
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped Pointwise commutatorElement

theorem step1711KMdNT_noinv
    (hOut : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → omegaA A = {Subgroup.zpowers c} →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ b ∈ A, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
    ∀ d : G, d ∈ A → d ≠ 1 → IsThreeCentralIn L d → Subgroup.zpowers b = Subgroup.zpowers d →
    ∀ X : Subgroup G,
      delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
      ∀ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 b → 𝒳.Nonempty → X = sSup 𝒳 →
      (∃ K ∈ 𝒳, ¬ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K) →
      (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) →
      CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
      ¬ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) →
      ¬ (c ∈ Subgroup.normalizer (X : Set G) ∧
          ⁅X, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X) →
        X ≤ (X ⊓ Subgroup.normalizer (Y₀ : Set G)) ⊔ inSubgroup (aschbacherSolvableCore 3) X)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h134 : Item134) :   ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ b ∈ A, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
    ∀ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb ∈ lA A b' →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → Subgroup.zpowers b = Subgroup.zpowers d →
    ∀ X : Subgroup G,
      delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
      (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 b ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) →
      (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) →
      CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
      ¬ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) →
      ¬ (c ∈ Subgroup.normalizer (X : Set G) ∧
          ⁅X, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X) →
        X ≤ (X ⊓ Subgroup.normalizer (Y₀ : Set G)) ⊔ inSubgroup (aschbacherSolvableCore 3) X := by
  intro G _ _ A c L Y₀ hs b hb hb1 hbΩ b' d Lb hb'Ω hLb hJ hdA hd1 hdc hbd X hDX h𝒳
    htypes hO2 hDM hNT
  have hΩ : omegaA A = {Subgroup.zpowers c} :=
    Proof17Res10.omegaA_eq_of_j2 hs (h1514 G A c L Y₀ hs) (hMeets G A c L Y₀ hs) hb'Ω hLb hJ
  have hb'c : Subgroup.zpowers b' = Subgroup.zpowers c := by
    have h := hb'Ω
    rw [hΩ] at h
    exact h
  have hLbc : Lb ∈ lA A c := lA_eq_of_zpowers_eq hb'c ▸ hLb
  have hLbL : Lb = L :=
    (hs.toSec14Std.chosen136.2 c hs.toSec13Data.zpowers_mem_omegaA L hs.toSec13Data.mem_lA).2
      Lb hLbc.1 (Proof17Res7.three_dvd_card_of_j2 hJ)
  rw [hLbL] at hJ hdc
  obtain ⟨𝒳, h𝒳s, h𝒳n, hX⟩ := h𝒳
  by_cases hall :
      ∀ K ∈ 𝒳, inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K
  · exfalso
    apply hNT
    have h𝒳d : 𝒳 ⊆ thetaComponentsAt 3 d :=
      Item148PtRes.thetaComponentsAt_eq_of_zpowers_eq hbd ▸ h𝒳s
    rw [hX]
    exact Proof17Res7.trivial_of_forall_le h134 Sec4.Sporadic.rank3II_4_15 hs hΩ hJ hdA hd1 hdc
      h𝒳d h𝒳n hall
  · push Not at hall
    exact hOut G A c L Y₀ hs hΩ hJ b hb hb1 hbΩ d hdA hd1 hdc hbd X hDX 𝒳 h𝒳s h𝒳n hX hall
      htypes hO2 hDM hNT

theorem step1711KMdOut_noinv (hLd : Claim143LdThree) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ → omegaA A = {Subgroup.zpowers c} →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ b ∈ A, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
      ∀ d : G, d ∈ A → d ≠ 1 → IsThreeCentralIn L d → Subgroup.zpowers b = Subgroup.zpowers d →
      ∀ X : Subgroup G,
        delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
          pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
            pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
        ∀ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 b → 𝒳.Nonempty → X = sSup 𝒳 →
        (∃ K ∈ 𝒳, ¬ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K) →
        (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON ∨
          Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
          IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) →
        CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
        ¬ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤
          Subgroup.normalizer (Y₀ : Set G) →
        ¬ (c ∈ Subgroup.normalizer (X : Set G) ∧
            ⁅X, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X) →
          X ≤ (X ⊓ Subgroup.normalizer (Y₀ : Set G)) ⊔
            inSubgroup (aschbacherSolvableCore 3) X := by
  intro G _ _ A c L Y₀ hs hΩ hJ b hb hb1 hbΩ d hdA hd1 hdc hbd X hDX 𝒳 h𝒳s h𝒳n hX hK
    htypes hO2 hDM hNT
  exfalso
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK𝒳, hLK⟩ := hK
  have hCbd : Subgroup.centralizer ({b} : Set G) = Subgroup.centralizer ({d} : Set G) :=
    centralizer_singleton_eq_of_zpowers_eq hbd
  have hKd : K ∈ thetaComponentsAt 3 d :=
    Item148PtRes.thetaComponentsAt_eq_of_zpowers_eq hbd ▸ h𝒳s hK𝒳
  have hKX : K ≤ X := hX ▸ le_sSup hK𝒳
  have hXΔ : X ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) := hDX ▸ le_sup_right
  have hKΔ : K ≤ delta A (lB A) (Subgroup.centralizer ({d} : Set G)) := by
    rw [← hCbd]
    exact hKX.trans hXΔ
  rcases hLd G A c L Y₀ hs hΩ hJ d hdA hd1 hdc K hKd hKΔ with hKO | hLK'
  ·
    have hXC : X ≤ Subgroup.centralizer ({b} : Set G) := hX ▸ sSup_le fun K' hK' =>
      le_centralizer_of_mem_thetaComponentsAt (h𝒳s hK')
    set O := pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) with hO
    have hXN : X ≤ Subgroup.normalizer (O : Set G) :=
      hXC.trans (le_normalizer_pPrimeCoreOf 3 _)
    have hON : (O.subgroupOf X).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using (Subgroup.mem_normalizer_iff.mp (hXN g.2) n).mp hn⟩
    have hO3 : ¬ 3 ∣ Nat.card (O.subgroupOf X) := fun h =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
        (h.trans (Proof17Res8.card_subgroupOf_dvd O X))
    have hOθ := Proof17Res8.le_theta_of_normal_of_types htypes (O.subgroupOf X) hO3
    have hKO' : K ≤ O := by rw [hO, ← hCbd] at *; exact hKO
    have hKθ : K.subgroupOf X ≤ aschbacherSolvableCore 3 ↥X := fun k hk =>
      hOθ (Subgroup.mem_subgroupOf.mpr (hKO' (Subgroup.mem_subgroupOf.mp hk)))
    have hθs : Group.IsSolvable (aschbacherSolvableCore 3 ↥X) :=
      (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).1
    have hKs' : Group.IsSolvable (K.subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKθ)
    have hKs : Group.IsSolvable K :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hKX).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKX).symm.injective
    have hKbot : K = ⊥ := CFSG.RankThree.GroupTheory.eq_bot_of_isPerfect_of_isSolvable
      (Sec6.isPerfect_of_mem_thetaComponentsAt hKd) hKs
    apply Sec6.theta_ne_of_mem_thetaComponentsAt hKd
    rw [hKbot]
    exact le_bot_iff.mp (Subgroup.map_subtype_le _)
  · exact hLK hLK'

theorem step1711KMd_noinv (hNT :   ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ b ∈ A, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
    ∀ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb ∈ lA A b' →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → Subgroup.zpowers b = Subgroup.zpowers d →
    ∀ X : Subgroup G,
      delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
      (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 b ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) →
      (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) →
      CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
      ¬ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) →
      ¬ (c ∈ Subgroup.normalizer (X : Set G) ∧
          ⁅X, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X) →
        X ≤ (X ⊓ Subgroup.normalizer (Y₀ : Set G)) ⊔ inSubgroup (aschbacherSolvableCore 3) X) :   ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ b ∈ A, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
    ∀ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb ∈ lA A b' →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → Subgroup.zpowers b = Subgroup.zpowers d →
    ∀ X : Subgroup G,
      delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
      (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 b ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) →
      (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) →
      CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
      ¬ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) →
        X ≤ (X ⊓ Subgroup.normalizer (Y₀ : Set G)) ⊔ inSubgroup (aschbacherSolvableCore 3) X := by
  intro G _ _ A c L Y₀ hs b hb hb1 hbΩ b' d Lb hb'Ω hLb hJ hdA hd1 hdc hbd X hDX h𝒳 htypes
    hO2 hDM
  by_cases hT : c ∈ Subgroup.normalizer (X : Set G) ∧
      ⁅X, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X
  · refine (Proof17Res6.le_centralizer_sup_theta
      (HeadProof.pow_three_of_std hs hs.toSec13Data.mem_A) hT.1 hT.2).trans ?_
    exact sup_le_sup_right (inf_le_inf_left _ (HeadProof.centralizer_c_le_M hs)) _
  · exact hNT G A c L Y₀ hs b hb hb1 hbΩ b' d Lb hb'Ω hLb hJ hdA hd1 hdc hbd X hDX h𝒳 htypes
      hO2 hDM hT
theorem step1711KMdNoInv_holds
    (hbal : Step143Balance) (h48 : Sec4.Item4_8)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h134 : Item134) :   ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ b ∈ A, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
    ∀ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb ∈ lA A b' →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → Subgroup.zpowers b = Subgroup.zpowers d →
    ∀ X : Subgroup G,
      delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
      (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 b ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) →
      (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) →
      CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
      ¬ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) →
        X ≤ (X ⊓ Subgroup.normalizer (Y₀ : Set G)) ⊔ inSubgroup (aschbacherSolvableCore 3) X :=
  step1711KMd_noinv (step1711KMdNT_noinv (step1711KMdOut_noinv (claim143LdThree_of hbal h48))
    h1514 hMeets h134)

end CFSG.RankThree.PartTwo.Sec17
