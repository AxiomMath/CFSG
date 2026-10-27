module

public import CFSG.RankThree.PartOne.D4RC.RxFrame

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Abstract

theorem rcl_card_ker_ge {G : Type*} [Group G] {L : Type*} [Field L] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) (χ : G →* Lˣ) (hχ : ∀ g, χ g ^ p = 1) :
    p ≤ Nat.card χ.ker := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hle : χ.range ≤ rootsOfUnity p L := by
    rintro _ ⟨g, rfl⟩
    exact (mem_rootsOfUnity ..).2 (hχ g)
  have h1 : Nat.card χ.range ≤ p := (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity L p)
  have h2 := Subgroup.card_ker_mul_card_range χ
  rw [hG] at h2
  by_contra hlt
  have hlt' := Nat.lt_of_not_ge hlt
  nlinarith

theorem rcl_lines_abstract {G R J L : Type*} [Group G] [Finite G] [Field L] [Nontrivial J]
    {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) (hGp : ∀ g : G, g ^ p = 1)
    (χ : R → G →* Lˣ) (Rt : R → Prop) (S : J → Set R)
    (hS : ∀ j, ∀ α ∈ S j, Rt α) (hSne : ∀ j, (S j).Nonempty)
    (hSd : ∀ j j', j ≠ j' → Disjoint (S j) (S j')) (Kk : G → Set R)
    (hK : ∀ g α, α ∈ Kk g ↔ Rt α ∧ χ α g = 1)
    (hT : ∀ g, g ≠ 1 → Kk g = ∅ ∨ ∃ j, Kk g = S j) :
    ∃ x : J → G, (∀ j, x j ≠ 1 ∧ Kk (x j) = S j) ∧
      (∀ j j', x j' ∈ Subgroup.zpowers (x j) → j' = j) ∧
      (∀ j g, Kk g = S j → g ∈ Subgroup.zpowers (x j)) ∧
      (∀ g, g ≠ 1 → (∃ j, g ∈ Subgroup.zpowers (x j)) ∨ Kk g = ∅) := by
  classical
  choose a ha using hSne
  have hχ : ∀ α g, χ α g ^ p = 1 := fun α g => by rw [← map_pow, hGp, map_one]
  have hA : ∀ α, p ≤ Nat.card (χ α).ker := fun α => rcl_card_ker_ge hp hG (χ α) (hχ α)
  have hex : ∀ j, ∃ x : G, x ≠ 1 ∧ x ∈ (χ (a j)).ker ∧ Kk x = S j := by
    intro j
    obtain hbot | ⟨x, hxk, hx1⟩ := Subgroup.bot_or_exists_ne_one (χ (a j)).ker
    · exfalso
      have h := hA (a j)
      rw [hbot, Subgroup.card_bot] at h
      have := hp.two_le
      omega
    · refine ⟨x, hx1, hxk, ?_⟩
      have hmem : a j ∈ Kk x := (hK _ _).2 ⟨hS j _ (ha j), hxk⟩
      rcases hT x hx1 with h | ⟨j', h⟩
      · rw [h] at hmem
        exact absurd hmem (Set.notMem_empty _)
      · rw [h] at hmem ⊢
        by_cases hjj : j' = j
        · rw [hjj]
        · exact absurd (ha j) (Set.disjoint_left.1 (hSd j' j hjj) hmem)
  choose x hx1 hxk hxK using hex
  have hzp : ∀ j, Subgroup.zpowers (x j) = (χ (a j)).ker := by
    intro j
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (x j) = p := orderOf_eq_prime (hGp (x j)) (hx1 j)
    have hcard1 : Nat.card (Subgroup.zpowers (x j)) = p := by rw [Nat.card_zpowers, hord]
    have hle : Subgroup.zpowers (x j) ≤ (χ (a j)).ker := Subgroup.zpowers_le.2 (hxk j)
    have hne_top : (χ (a j)).ker ≠ ⊤ := by
      intro htop
      obtain ⟨j', hj'⟩ := exists_ne j
      have hmem : x j' ∈ (χ (a j)).ker := by rw [htop]; exact Subgroup.mem_top _
      have h2 : a j ∈ Kk (x j') := (hK _ _).2 ⟨hS j _ (ha j), hmem⟩
      rw [hxK j'] at h2
      exact Set.disjoint_left.1 (hSd j' j hj') h2 (ha j)
    have hdvd : Nat.card (χ (a j)).ker ∣ p ^ 2 := hG ▸ Subgroup.card_subgroup_dvd_card _
    have hle2 : Nat.card (χ (a j)).ker ≤ p := by
      obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      have h3 := hA (a j)
      have h4 := hp.two_le
      interval_cases k
      · rw [pow_zero] at hkeq
        omega
      · rw [pow_one] at hkeq
        omega
      · exact absurd (Subgroup.eq_top_of_card_eq _ (by rw [hkeq, hG])) hne_top
    exact Subgroup.eq_of_le_of_card_ge hle (hcard1.symm ▸ hle2)
  have hiii : ∀ j g, Kk g = S j → g ∈ Subgroup.zpowers (x j) := by
    intro j g hg
    rw [hzp j]
    have : a j ∈ Kk g := by rw [hg]; exact ha j
    exact ((hK _ _).1 this).2
  refine ⟨x, fun j => ⟨hx1 j, hxK j⟩, ?_, hiii, ?_⟩
  · intro j j' hmem
    have hsub : S j ⊆ S j' := by
      intro α hα
      have h1 : α ∈ Kk (x j) := by rw [hxK j]; exact hα
      have h2 := (hK _ _).1 h1
      have h3 : x j' ∈ (χ α).ker := (Subgroup.zpowers_le.2 h2.2) hmem
      rw [← hxK j']
      exact (hK _ _).2 ⟨h2.1, h3⟩
    by_contra hne
    exact Set.disjoint_left.1 (hSd j j' (Ne.symm hne)) (ha j) (hsub (ha j))
  · intro g hg
    rcases hT g hg with h | ⟨j, h⟩
    · exact Or.inr h
    · exact Or.inl ⟨j, hiii j g h⟩

end Abstract

section Lines

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem rcl_char_data_of_conj (F : RclFrame ℓ f K σ ε p L) (E : Subgroup 𝒞[K, σ])
    (c : 𝒞[K, σ]) (hc : ∀ y ∈ E, F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    ∃ β : E →* (Fin TwistTag.D4.tag.rank → Lˣ),
      (∀ y : E, rootDiagUnit TwistTag.D4.tag (β y) =
        F.g0⁻¹ * triEmb K σ L (c * (y : 𝒞[K, σ]) * c⁻¹) * F.g0) ∧
      (∀ y : E, rootDiagUnit TwistTag.D4.tag (β y) ∈
        twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) ∧
      (∀ y : E, β y ∈ fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f)) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hT := twistedTorus_D4_eq_map_of_weylImage (iterateFrobenius L ℓ f) F.hn F.w F.hnw
    (d4T36M ε) F.hw
  have hex : ∀ y : E, ∃ b ∈ fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f),
      rootDiagUnit TwistTag.D4.tag b =
        F.g0⁻¹ * triEmb K σ L (c * (y : 𝒞[K, σ]) * c⁻¹) * F.g0 := fun y => by
    have h := hc y y.2
    rw [hT] at h
    obtain ⟨b, hb, hbb⟩ := h
    exact ⟨b, hb, hbb⟩
  choose β hβfix hβ using hex
  have hmul : ∀ y y' : E, β (y * y') = β y * β y' := fun y y' => by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    have e1 : c * ((y * y' : E) : 𝒞[K, σ]) * c⁻¹ =
        (c * (y : 𝒞[K, σ]) * c⁻¹) * (c * (y' : 𝒞[K, σ]) * c⁻¹) := by
      rw [Subgroup.coe_mul]
      group
    rw [rootDiagUnit_mul, hβ (y * y'), hβ y, hβ y', e1, map_mul]
    group
  refine ⟨MonoidHom.mk' β hmul, hβ, fun y => ?_, hβfix⟩
  have h := hc y y.2
  rw [← hβ y] at h
  exact h

theorem rcl_special_lines_of_conj (F : RclFrame ℓ f K σ ε p L) (E : Subgroup 𝒞[K, σ])
    (hEp : ∀ y ∈ E, y ^ p = 1) (hEc : Nat.card E = p ^ 2) (c : 𝒞[K, σ])
    (hc : ∀ y ∈ E, F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    ∃ x : Fin 4 → 𝒞[K, σ],
      (∀ j, x j ∈ E ∧ x j ≠ 1) ∧
      (∀ j, ∃ sp : RclSpecial F (x j) j, sp.c = c) ∧
      (∀ j j', Subgroup.zpowers (x j) = Subgroup.zpowers (x j') → j = j') ∧
      (∀ j (y : 𝒞[K, σ]) (sp : RclSpecial F y j), y ∈ E → sp.c = c →
        y ∈ Subgroup.zpowers (x j)) ∧
      (∀ y ∈ E, y ≠ 1 → (∃ j, y ∈ Subgroup.zpowers (x j)) ∨
        ∃ b : Fin TwistTag.D4.tag.rank → Lˣ,
          rootDiagUnit TwistTag.D4.tag b = F.g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * F.g0 ∧
          rootCharKernel b = ∅) := by
  classical
  have hp := F.hp
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; exact pow_ne_zero 2 hp.ne_zero)
  have hEp' : ∀ y : E, y ^ p = 1 := fun y =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hEp y y.2)
  obtain ⟨β, hβ, hβT, hβfix⟩ := rcl_char_data_of_conj F E c hc
  have hβ1 : ∀ y : E, y ≠ 1 → β y ≠ 1 := by
    intro y hy h1
    apply hy
    have h2 : F.g0⁻¹ * triEmb K σ L (c * (y : 𝒞[K, σ]) * c⁻¹) * F.g0 = 1 := by
      rw [← hβ y, h1, rootDiagUnit_one]
    have h3 : triEmb K σ L (c * (y : 𝒞[K, σ]) * c⁻¹) = 1 := by
      have := congrArg (fun z => F.g0 * z * F.g0⁻¹) h2
      simpa [mul_assoc] using this
    have h4 : c * (y : 𝒞[K, σ]) * c⁻¹ = 1 := triEmb_injective (h3.trans (map_one _).symm)
    exact Subtype.ext (conj_eq_one_iff.1 h4)
  obtain ⟨χ, hχ⟩ : ∃ χ : (Fin TwistTag.D4.tag.rank → ℤ) → (E →* Lˣ),
      ∀ u g, χ u g = rootChar (β g) u :=
    ⟨fun u => MonoidHom.mk' (fun g => rootChar (β g) u) (fun a b => by
      rw [map_mul]; exact CTTorus.rootChar_mul _ _ _), fun _ _ => rfl⟩
  have hT : ∀ g : E, g ≠ 1 → rootCharKernel (β g) = ∅ ∨
      ∃ j : Fin 4, rootCharKernel (β g) = d4Sigma j :=
    fun g hg => d4T36_rootCharKernel_cases F.hε (hβfix g) (hβ1 g hg)
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ := rcl_lines_abstract (G := E)
    (R := Fin TwistTag.D4.tag.rank → ℤ) (J := Fin 4) hp hEc hEp' χ
    (fun α => IsRoot TwistTag.D4.tag α) (fun j => d4Sigma j)
    (fun j α hα => isRoot_of_mem_d4Sigma hα)
    (fun j => ⟨trialityU j, mem_trialitySigma.2 List.mem_cons_self⟩)
    (fun j j' h => pairwise_disjoint_trialitySigma h) (fun g => rootCharKernel (β g))
    (fun g α => by rw [hχ]; exact Iff.rfl) hT
  have hzp : ∀ (j : Fin 4) (g : E), g ∈ Subgroup.zpowers (x j) →
      (g : 𝒞[K, σ]) ∈ Subgroup.zpowers ((x j : E) : 𝒞[K, σ]) := by
    intro j g hg
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact Subgroup.mem_zpowers_iff.2 ⟨a, by rw [Subgroup.coe_zpow]⟩
  have hzp' : ∀ j j' : Fin 4, ((x j' : E) : 𝒞[K, σ]) ∈ Subgroup.zpowers ((x j : E) : 𝒞[K, σ]) →
      x j' ∈ Subgroup.zpowers (x j) := by
    intro j j' h
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨a, Subtype.ext (by rw [Subgroup.coe_zpow]; exact ha)⟩
  refine ⟨fun j => (x j : 𝒞[K, σ]),
    fun j => ⟨(x j).2, fun h => (hx1 j).1 (Subtype.ext h)⟩, ?_, ?_, ?_, ?_⟩
  · intro j
    have hne : ((x j : E) : 𝒞[K, σ]) ≠ 1 := fun h => (hx1 j).1 (Subtype.ext h)
    have hord : orderOf ((x j : E) : 𝒞[K, σ]) = p := orderOf_eq_prime (hEp _ (x j).2) hne
    exact ⟨⟨c, β (x j), hord, hβ (x j), hβT (x j), (hx1 j).2⟩, rfl⟩
  · intro j j' h
    have h1 : ((x j' : E) : 𝒞[K, σ]) ∈ Subgroup.zpowers ((x j : E) : 𝒞[K, σ]) := by
      rw [h]
      exact Subgroup.mem_zpowers _
    exact (hx2 j j' (hzp' j j' h1)).symm
  · intro j y sp hy hc
    have hb : sp.b = β ⟨y, hy⟩ := by
      apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
      rw [sp.hb, hβ ⟨y, hy⟩, hc]
    have hk : rootCharKernel (β ⟨y, hy⟩) = d4Sigma j := by
      rw [← hb]
      exact sp.hker
    exact hzp j ⟨y, hy⟩ (hx3 j ⟨y, hy⟩ hk)
  · intro y hy hne
    rcases hx4 ⟨y, hy⟩ (fun h => hne (congrArg Subtype.val h)) with ⟨j, hj⟩ | hempty
    · exact Or.inl ⟨j, hzp j _ hj⟩
    · exact Or.inr ⟨β ⟨y, hy⟩, hβ ⟨y, hy⟩, hempty⟩

end Lines

end CFSG.RankThree.PartOne.D4RC
