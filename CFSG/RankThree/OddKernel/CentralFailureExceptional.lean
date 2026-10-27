module

public import CFSG.RankThree.OddKernel.CentralFailureAlternating
public import CFSG.RankThree.OddKernel.SporadicKernelRestrictionB
public import CFSG.RankThree.Chevalley.SmallReeCentralExtension
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.TitsCover

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank CFSG.LocalCores CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (localRank)

variable {p : ℕ}

theorem coprime_six_of_isPGroup {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hp : p.Prime) (hp3 : 3 < p) (hH : IsPGroup p H) : Nat.Coprime (Nat.card H) 6 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  rw [hk]
  refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_)
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem component_exclusions_of_kernel_restriction {K : Type} [Group K] [Finite K]
    (hp : p.Prime) (hp3 : 3 < p) (hK : IsQuasisimple K) (hZ : center K ≠ ⊥)
    (hZp : IsPGroup p (center K))
    (htwelve : ∀ s ∈ ({.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru} :
        Set TauCeti.SporadicName), NativeSporadic.IsSporadic (K ⧸ center K) s →
          (QuotientGroup.mk' (center K)).ker = ⊥) :
    (∀ (t : StatedLieTag) (ℓ d : ℕ), ¬ ReeTitsModel (K ⧸ center K) t ℓ d) ∧
      (∀ ℓ d : ℕ, ¬ SuzukiModel (K ⧸ center K) ℓ d) ∧
      (∀ d : ℕ, ¬ ChevalleyExceptionalModel (K ⧸ center K) .G2 2 d ∧
        ¬ ChevalleyExceptionalModel (K ⧸ center K) .trialityD4 2 d) ∧
      ∀ s ∈ ({.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru} :
        Set TauCeti.SporadicName), ¬ NativeSporadic.IsSporadic (K ⧸ center K) s := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect K := hK.1
  have hker : (QuotientGroup.mk' (center K)).ker = center K := QuotientGroup.ker_mk' _
  have hπ : Function.Surjective (QuotientGroup.mk' (center K)) := QuotientGroup.mk'_surjective _
  have hodd : Odd (Nat.card (center K)) := by
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two (by omega)).pow
  have hcop : Nat.Coprime (Nat.card (center K)) 6 := coprime_six_of_isPGroup hp hp3 hZp
  have hcover : ∀ {T : Type} [Group T], (K ⧸ center K ≃* T) →
      (∀ π' : K →* T, Function.Surjective π' → π'.ker ≤ center K → Odd (Nat.card π'.ker) →
        π'.ker = ⊥) → False := by
    intro T _ e htriv
    have h := htriv _ (e.surjective.comp hπ) (center_eq_ker_of_mulEquiv e).le
      ((center_eq_ker_of_mulEquiv e).symm ▸ hodd)
    rw [center_eq_ker_of_mulEquiv e] at h
    exact hZ h
  refine ⟨fun t ℓ d hM => ?_, fun ℓ d hM => ?_, fun d => ⟨fun hM => ?_, fun hM => ?_⟩,
    fun s hs hS => hZ (hker ▸ htwelve s hs hS)⟩
  ·
    have ht : t ∈ reeTitsTags := by
      obtain ⟨-, a, -, hm⟩ := hM
      cases t <;> first | exact (hm : False).elim | simp [reeTitsTags]
    simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have h := CFSG.RankThree.Chevalley.small_Ree_model_central_kernel_trivial _ ℓ d hM
        (QuotientGroup.mk' (center K)) hπ hker.le (by rw [hker]; exact hcop)
      exact hZ (hker ▸ h)
    · obtain ⟨F, _, _, _, a, ha, hF, ⟨e⟩⟩ := exists_mulEquiv_reeFixed_of_model hM
      exact hcover e fun π' h1 h2 h3 =>
        LargeRee.large_ree_perfect_odd_cover_trivial_of_suzuki LargeRee.suzukiBlockInputs ha hF
          π' h1 h2 h3
    · obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_titsGroup_of_model hM
      exact hcover e fun π' h1 h2 h3 => Tits_perfect_odd_cover_trivial hF π' h1 h2 h3
  ·
    obtain ⟨a, ha, ⟨e⟩⟩ :=
      CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hM
    exact hcover e fun π' h1 h2 h3 => suzuki_perfect_odd_cover_trivial a (by omega) π' h1 h2 h3
  ·
    exact hcover (MulEquiv.refl _) fun π' h1 h2 h3 =>
      g2_even_perfect_odd_cover_trivial hM π' h1 h2 h3
  ·
    exact hcover (MulEquiv.refl _) fun π' h1 h2 h3 =>
      triality_even_perfect_odd_cover_trivial hM π' h1 h2 h3

theorem component_alternatives_of_kernel_restriction {K : Type} [Group K] [Finite K]
    (hp : p.Prime) (hp3 : 3 < p) (hK : IsQuasisimple K) (hZ : center K ≠ ⊥)
    (hZp : IsPGroup p (center K))
    (hrep : ExceptionalRep (K ⧸ center K) ∨ NativeSporadic.SporadicRep (K ⧸ center K))
    (hspor : (∀ s ∈ ({.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru} :
        Set TauCeti.SporadicName), NativeSporadic.IsSporadic (K ⧸ center K) s →
          (QuotientGroup.mk' (center K)).ker = ⊥) ∧
      (∀ s ∈ ({.Co1, .Fi24Prime, .Th, .B} : Set TauCeti.SporadicName),
        NativeSporadic.IsSporadic (K ⧸ center K) s → ∀ r : ℕ, r.Prime →
          r ∣ Nat.card (QuotientGroup.mk' (center K)).ker → r = 5 ∨ r = 7) ∧
      (∀ s ∈ ({.Co2, .Co3, .Fi22, .Fi23, .McL, .Suz, .HN, .Ly} : Set TauCeti.SporadicName),
        NativeSporadic.IsSporadic (K ⧸ center K) s → ∀ r : ℕ, r.Prime →
          r ∣ Nat.card (QuotientGroup.mk' (center K)).ker → r = 5) ∧
      (NativeSporadic.IsSporadic (K ⧸ center K) .ONan → ∀ r : ℕ, r.Prime →
        r ∣ Nat.card (QuotientGroup.mk' (center K)).ker → r = 7)) :
    (∃ τ ∈ chevalleyExceptionalTags, ∃ ℓ d : ℕ, ℓ.Prime ∧ 1 ≤ d ∧
        ChevalleyExceptionalModel (K ⧸ center K) τ ℓ d ∧ (τ = .G2 ∨ τ = .trialityD4 → Odd ℓ)) ∨
      ((∃ s ∈ ({.Co1, .Fi24Prime, .Th, .B} : Set TauCeti.SporadicName),
          NativeSporadic.IsSporadic (K ⧸ center K) s ∧ (p = 5 ∨ p = 7)) ∨
        (∃ s ∈ ({.Co2, .Co3, .Fi22, .Fi23, .McL, .Suz, .HN, .Ly} : Set TauCeti.SporadicName),
          NativeSporadic.IsSporadic (K ⧸ center K) s ∧ p = 5) ∨
        (NativeSporadic.IsSporadic (K ⧸ center K) .ONan ∧ p = 7)) ∨
      NativeSporadic.IsSporadic (K ⧸ center K) .M := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hRT, hSz, hGT, h12⟩ :=
    component_exclusions_of_kernel_restriction hp hp3 hK hZ hZp hspor.1
  have hker : (QuotientGroup.mk' (center K)).ker = center K := QuotientGroup.ker_mk' _
  have hpZ : p ∣ Nat.card (QuotientGroup.mk' (center K)).ker := by
    rw [hker]
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd (Subgroup.card_eq_one.mp hk) hZ
    · rw [hk]
      exact dvd_pow_self p k.succ_ne_zero
  rcases hrep with (⟨t, ℓ, d, ht, hM⟩ | ⟨t, ℓ, d, -, hM⟩ | ⟨ℓ, d, hM⟩) | ⟨s, ⟨e⟩⟩
  ·
    refine .inl ⟨t, ht, ℓ, d, hM.1.1, hM.1.2.1, hM, fun hτ => hM.1.1.odd_of_ne_two fun h2 => ?_⟩
    subst h2
    rcases hτ with rfl | rfl
    · exact (hGT d).1 hM
    · exact (hGT d).2 hM
  · exact (hRT t ℓ d hM).elim
  · exact (hSz ℓ d hM).elim
  ·
    obtain ⟨-, h2, h3, h4⟩ := hspor
    have hS : NativeSporadic.IsSporadic (K ⧸ center K) s := ⟨e⟩
    have hcases : s ∈ ({.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru} :
          Set TauCeti.SporadicName) ∨ s ∈ ({.Co1, .Fi24Prime, .Th, .B} : Set TauCeti.SporadicName) ∨
        s ∈ ({.Co2, .Co3, .Fi22, .Fi23, .McL, .Suz, .HN, .Ly} : Set TauCeti.SporadicName) ∨
        s = .ONan ∨ s = .M := by
      cases s <;> simp
    rcases hcases with hs | hs | hs | rfl | rfl
    · exact (h12 s hs hS).elim
    · exact .inr (.inl (.inl ⟨s, hs, hS, h2 s hs hS p hp hpZ⟩))
    · exact .inr (.inl (.inr (.inl ⟨s, hs, hS, h3 s hs hS p hp hpZ⟩)))
    · exact .inr (.inl (.inr (.inr ⟨hS, h4 hS p hp hpZ⟩)))
    · exact .inr (.inr hS)

theorem original_central_failure_excludes_Ree_Suzuki_and_twelve_sporadic_components {G : Type}
    [Group G] [Finite G] (hK : IsKGroupCat G) (he : CFSG.twoLocalOddRank G ≤ 3)
    (hr : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (H : Subgroup G) (N₀ : Subgroup H)
    [N₀.Normal] (hS : CFSG.layer (H ⧸ N₀) = ⊤) (hp : p.Prime) (hp3 : 3 < p)
    (hfail : 2 < localRank p (H ⧸ N₀) ∨ (pRank p G ≤ 3 ∧ pRank p G < pRank p (H ⧸ N₀)))
    (X : Subgroup H) (hXS : X.map (QuotientGroup.mk' N₀) = ⊤)
    (hXmin : ∀ U : Subgroup H, U.map (QuotientGroup.mk' N₀) = ⊤ → Nat.card X ≤ Nat.card U) :
    let ρX : X →* H ⧸ N₀ := (QuotientGroup.mk' N₀).comp X.subtype
    let C₀ : Subgroup X := (center (H ⧸ N₀)).comap ρX
    let D₀ : Subgroup X := sylowPrimeComplement p C₀
    ∃ _ : D₀.Normal, ∃ _ : (D₀.map ρX).Normal, ∃ _ : (C₀.map (QuotientGroup.mk' D₀)).Normal,
    ∃ f : X ⧸ D₀ →* (H ⧸ N₀) ⧸ D₀.map ρX,
      (∀ x : X, f (QuotientGroup.mk x) = QuotientGroup.mk (ρX x)) ∧ Function.Surjective f ∧
      f.ker = (N₀.subgroupOf X ⊔ D₀).map (QuotientGroup.mk' D₀) ∧ f.ker ≠ ⊥ ∧
      f.ker ≤ C₀.map (QuotientGroup.mk' D₀) ∧
      C₀.map (QuotientGroup.mk' D₀) = center (X ⧸ D₀) ∧ CFSG.layer (X ⧸ D₀) = ⊤ ∧
      (∀ K : Subgroup (X ⧸ D₀), CFSG.IsComponent K →
        ((∃ τ ∈ chevalleyExceptionalTags, ∃ ℓ d : ℕ, ℓ.Prime ∧ 1 ≤ d ∧
            ChevalleyExceptionalModel (K ⧸ center K) τ ℓ d ∧
            (τ = .G2 ∨ τ = .trialityD4 → Odd ℓ)) ∨
          ((∃ s ∈ ({.Co1, .Fi24Prime, .Th, .B} : Set TauCeti.SporadicName),
              NativeSporadic.IsSporadic (K ⧸ center K) s ∧ (p = 5 ∨ p = 7)) ∨
            (∃ s ∈ ({.Co2, .Co3, .Fi22, .Fi23, .McL, .Suz, .HN, .Ly} :
                Set TauCeti.SporadicName),
              NativeSporadic.IsSporadic (K ⧸ center K) s ∧ p = 5) ∨
            (NativeSporadic.IsSporadic (K ⧸ center K) .ONan ∧ p = 7)) ∨
          NativeSporadic.IsSporadic (K ⧸ center K) .M) ∧
        (∀ (t : StatedLieTag) (ℓ d : ℕ), ¬ ReeTitsModel (K ⧸ center K) t ℓ d) ∧
        (∀ ℓ d : ℕ, ¬ SuzukiModel (K ⧸ center K) ℓ d) ∧
        (∀ d : ℕ, ¬ ChevalleyExceptionalModel (K ⧸ center K) .G2 2 d ∧
          ¬ ChevalleyExceptionalModel (K ⧸ center K) .trialityD4 2 d) ∧
        ∀ s ∈ ({.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru} :
          Set TauCeti.SporadicName), ¬ NativeSporadic.IsSporadic (K ⧸ center K) s) ∧
      ((CFSG.IsQuasisimple (X ⧸ D₀) ∧ Nat.card (ComponentIndex (X ⧸ D₀)) = 1) ∨
        (Nat.card (ComponentIndex (X ⧸ D₀)) = 2 ∧
          ∃ K₁ K₂ : Subgroup (X ⧸ D₀), CFSG.IsComponent K₁ ∧ CFSG.IsComponent K₂ ∧ K₁ ≠ K₂ ∧
            (∀ K : Subgroup (X ⧸ D₀), CFSG.IsComponent K → K = K₁ ∨ K = K₂) ∧
            IsCyclic (center (X ⧸ D₀)) ∧ center K₁ ≠ ⊥ ∧ IsCyclic (center K₁) ∧
            center K₂ ≠ ⊥ ∧ IsCyclic (center K₂) ∧
            K₁ ⊓ K₂ = (center K₁).map K₁.subtype ⊓ (center K₂).map K₂.subtype ∧
            K₁ ⊓ K₂ ≠ ⊥ ∧ pRank p K₁ = 2 ∧ pRank p K₂ = 2 ∧ localRank p K₁ = 1 ∧
            localRank p K₂ = 1 ∧ K₁ ⊔ K₂ = ⊤ ∧
            center (X ⧸ D₀) = (center K₁).map K₁.subtype ⊔ (center K₂).map K₂.subtype ∧
            ∃ μ : K₁ × K₂ →* X ⧸ D₀, (∀ x : K₁ × K₂, μ x = (x.1 : X ⧸ D₀) * x.2) ∧
              Function.Surjective μ ∧
              ∀ x : K₁ × K₂, μ x = 1 ↔
                ∃ z ∈ K₁ ⊓ K₂, (x.1 : X ⧸ D₀) = z ∧ (x.2 : X ⧸ D₀) = z⁻¹)) := by
  intro ρX C₀ D₀
  obtain ⟨hDn, hZ₀n, hPn, f, hf, hfs, hfker, hA, -, hAP, hPZ, hEY, hmod, hcomp⟩ :=
    original_central_failure_components hK he hr H N₀ hS hp hp3 hfail X hXS hXmin
  obtain ⟨_i₁, _i₂, _i₃, -, -, -, -, -, -, -, -, hAlt, -⟩ :=
    original_central_failure_excludes_alternating_components hK he hr H N₀ hS hp hp3 hfail X
      hXS hXmin
  refine ⟨hDn, hZ₀n, hPn, f, hf, hfs, hfker, hA, hAP, hPZ, hEY, fun K hKc => ?_, hmod⟩
  obtain ⟨hZ, hZp, -⟩ := hcomp K hKc
  have : Group.IsPerfect K := hKc.1.1
  have hker : (QuotientGroup.mk' (center K)).ker = center K := QuotientGroup.ker_mk' _
  obtain ⟨h1, h2, h3, h4, -⟩ := twenty_five_sporadic_central_prime_to_six_kernel_restriction
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _) hker.le
    (by rw [hker]; exact coprime_six_of_isPGroup hp hp3 hZp)
  exact ⟨component_alternatives_of_kernel_restriction hp hp3 hKc.1 hZ hZp (hAlt K hKc).2
    ⟨h1, h2, h3, h4⟩, component_exclusions_of_kernel_restriction hp hp3 hKc.1 hZ hZp h1⟩

end CFSG.RankThree.OddKernel
