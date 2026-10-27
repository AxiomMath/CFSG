module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcCore

public section

namespace CFSG.StandardType

namespace GGOppRadExc

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical

variable {τ : Tag} {K : Type} [Field K]

theorem oppRadicalRoots_eq_neg (J : Set (Fin τ.rank)) :
    oppRadicalRoots τ J = -parabolicRadicalRoots τ J :=
  Set.ext fun _ => Iff.rfl

theorem ncard_oppRadicalRoots (J : Set (Fin τ.rank)) :
    (oppRadicalRoots τ J).ncard = (parabolicRadicalRoots τ J).ncard := by
  rw [oppRadicalRoots_eq_neg, Set.ncard_neg]

variable {w₀ : WeylGroup τ} {δ : Fin τ.rank → Fin τ.rank}

theorem longest_image_oppRadicalRoots_subset (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (h₀ : ReversesSigns w₀) (J : Set (Fin τ.rank)) :
    (fun α => w₀ • α) '' oppRadicalRoots τ J ⊆ parabolicRadicalRoots τ (δ '' J) := by
  rintro _ ⟨α, hα, rfl⟩
  show w₀ • α ∈ parabolicRadicalRoots τ (δ '' J)
  have hα' : -α ∈ parabolicRadicalRoots τ J := hα
  have hr : IsRoot τ α := isRoot_of_mem_oppRadicalRoots hα
  refine mem_parabolicRadicalRoots_of_degree (IsRoot.smul hr w₀) ?_ ?_
  · have h1 := h₀ (-α) hα'.1.1 hα'.1.2
    rw [smul_neg, height_neg] at h1
    omega
  · rw [parabolicDegree_longest hinj hδ J α]
    have := one_le_parabolicDegree_of_mem hα'
    rw [parabolicDegree_neg] at this
    omega

theorem longest_image_oppRadicalRoots (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) (hsq : w₀ * w₀ = 1)
    (h₀ : ReversesSigns w₀) (J : Set (Fin τ.rank)) :
    (fun α => w₀ • α) '' oppRadicalRoots τ J = parabolicRadicalRoots τ (δ '' J) :=
  Set.Subset.antisymm (longest_image_oppRadicalRoots_subset hinj hδ h₀ J)
    (parabolicRadicalRoots_subset_longest hinj hδ hsq h₀ J)

theorem ncard_parabolicRadicalRoots_longest (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) (hsq : w₀ * w₀ = 1)
    (h₀ : ReversesSigns w₀) (J : Set (Fin τ.rank)) :
    (parabolicRadicalRoots τ (δ '' J)).ncard = (parabolicRadicalRoots τ J).ncard := by
  rw [← longest_image_oppRadicalRoots hinj hδ hsq h₀ J,
    Set.ncard_image_of_injective _ (MulAction.injective w₀), ncard_oppRadicalRoots]

theorem oppRadical_eq_map_conj (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) (hsq : w₀ * w₀ = 1)
    (h₀ : ReversesSigns w₀) (J : Set (Fin τ.rank)) :
    oppRadical τ K J = (parabolicRadical τ K (δ '' J)).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) K w₀)⁻¹).toMonoidHom := by
  refine le_antisymm ?_ (map_conj_longest_parabolicRadical_le hinj hδ hsq h₀ J)
  set n := canonicalRep (coxeterSystem τ) K w₀
  have hmap : (oppRadical τ K J).map (MulAut.conj n).toMonoidHom =
      parabolicRadical τ K (δ '' J) := by
    rw [oppRadical, (canonical_weyl_root_transport τ K).1 w₀ (oppRadicalRoots τ J)
      fun α hα => isRoot_of_mem_oppRadicalRoots hα, longest_image_oppRadicalRoots hinj hδ hsq h₀ J]
    rfl
  rw [← hmap, ← GGTwoSig.map_conj_mul, inv_mul_cancel, GGTwoSig.map_conj_one]

theorem card_oppRadical [Finite K] (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) (hsq : w₀ * w₀ = 1)
    (h₀ : ReversesSigns w₀) (J : Set (Fin τ.rank)) :
    Nat.card (oppRadical τ K J) = Nat.card (parabolicRadical τ K J) := by
  rw [oppRadical_eq_map_conj hinj hδ hsq h₀ J,
    Subgroup.card_map_of_injective (MulAut.conj _).injective, card_parabolicRadical,
    card_parabolicRadical, ncard_parabolicRadicalRoots_longest hinj hδ hsq h₀ J]

theorem parabolicLevi_le_normalizer_oppRadical (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) (hsq : w₀ * w₀ = 1)
    (h₀ : ReversesSigns w₀) (J : Set (Fin τ.rank)) :
    parabolicLevi τ K J ≤ Subgroup.normalizer (oppRadical τ K J : Set (ModGL τ K)) := by
  rw [oppRadical_eq_map_conj hinj hδ hsq h₀ J]
  exact fun m hm => mem_normalizer_map_conj_inv (((parabolicLevi_le_parabolicSubgroup (δ '' J)).trans
    (parabolicSubgroup_le_normalizer_parabolicRadical (δ '' J)))
    (map_conj_parabolicLevi_le hδ J (Subgroup.mem_map_of_mem _ hm)))

theorem oppRadical_mem_oppositePRadicals_prime [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) (hsq : w₀ * w₀ = 1)
    (h₀ : ReversesSigns w₀) (J : Set (Fin τ.rank)) :
    oppRadical τ K J ∈ CFSG.GroupTheory.oppositePRadicals r (adjointGroup τ K)
      (parabolicRadical τ K J) := by
  refine ⟨?_, card_oppRadical hinj hδ hsq h₀ J, ?_⟩
  · rw [oppRadical_eq_map_conj hinj hδ hsq h₀ J]
    refine (isRadicalPGroup_parabolicRadical_prime r (δ '' J)).map_mulAut
      (MulAut.conj (canonicalRep (coxeterSystem τ) K w₀)⁻¹) ?_
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
    exact Subgroup.le_normalizer (inv_mem (canonicalRep_mem_adjointGroup _ K w₀))
  · rw [adjointGroup_inf_normalizer_parabolicRadical, inf_comm]
    exact parabolicSubgroup_inf_oppRadical J

theorem parabolicRadical_sup_oppRadical [IsSimpleGroup (adjointGroup τ K)]
    (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) (hsq : w₀ * w₀ = 1)
    (h₀ : ReversesSigns w₀) {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
    parabolicRadical τ K J ⊔ oppRadical τ K J = adjointGroup τ K := by
  set C := adjointGroup τ K with hCdef
  set Q := parabolicRadical τ K J with hQdef
  set Q' := oppRadical τ K J with hQ'def
  have hQ1 : Q ≠ ⊥ := parabolicRadical_ne_bot hJ
  have hQC : Q ≤ C := rootSpan_le_adjointGroup K _
  have hQ'C : Q' ≤ C := rootSpan_le_adjointGroup K _
  have hMQ : parabolicLevi τ K J ≤ Subgroup.normalizer (Q : Set (ModGL τ K)) :=
    (parabolicLevi_le_parabolicSubgroup J).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical J)
  have hMQ' := parabolicLevi_le_normalizer_oppRadical (K := K) hinj hδ hsq h₀ J
  have hgen : C ≤ Q ⊔ Q' ⊔ parabolicLevi τ K J := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, hg | hg⟩
    · have hg' : g = xUnit τ K i c := Units.ext (hg.trans (coe_xUnit i c).symm)
      rw [hg']
      by_cases hi : i ∈ J
      · exact Subgroup.mem_sup_right (xUnit_mem_parabolicLevi hi c)
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (xUnit_mem_parabolicRadical hi c))
    · have hg' : g = yUnit τ K i c := Units.ext (hg.trans (coe_yUnit i c).symm)
      rw [hg']
      by_cases hi : i ∈ J
      · exact Subgroup.mem_sup_right (yUnit_mem_parabolicLevi hi c)
      · refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
        rw [← pinnedX_neg_single]
        refine pinnedX_mem_rootSpan ?_ c
        show -(-Pi.single i 1) ∈ parabolicRadicalRoots τ J
        rw [neg_neg]
        exact mem_parabolicRadicalRoots_iff.2 ⟨isRoot_single τ i,
          by rw [height_single]; exact one_pos, i, hi, by simp⟩
  have hXC : Q ⊔ Q' ≤ C := sup_le hQC hQ'C
  refine le_antisymm hXC ?_
  have hN : C ≤ Subgroup.normalizer ((Q ⊔ Q' : Subgroup (ModGL τ K)) : Set (ModGL τ K)) :=
    hgen.trans (sup_le Subgroup.le_normalizer fun m hm =>
      mem_normalizer_sup_of_mem (hMQ hm) (hMQ' hm))
  have : ((Q ⊔ Q').subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q ⊔ Q').subgroupOf C) with h | h
  · exfalso
    apply hQ1
    have hdis := Subgroup.subgroupOf_eq_bot.1 h
    exact eq_bot_iff.2 fun q hq => (Subgroup.disjoint_def.1 hdis)
      (Subgroup.mem_sup_left hq) (hQC hq) ▸ Subgroup.mem_bot.2 rfl
  · exact Subgroup.subgroupOf_eq_top.1 h

theorem exists_eq_map_conj_oppRadical_prime [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) (hsq : w₀ * w₀ = 1)
    (h₀ : ReversesSigns w₀) {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ)
    {V : Subgroup (ModGL τ K)}
    (hV : V ∈ CFSG.GroupTheory.oppositePRadicals r (adjointGroup τ K)
      (parabolicRadical τ K J)) :
    ∃ u ∈ parabolicRadical τ K J, V = (oppRadical τ K J).map (MulAut.conj u).toMonoidHom := by
  have := finite_modGL (τ := τ) (K := K)
  obtain ⟨hVrad, hVcard, hVinf⟩ := hV
  rw [adjointGroup_inf_normalizer_parabolicRadical] at hVinf
  have hQ1 : parabolicRadical τ K J ≠ ⊥ := parabolicRadical_ne_bot hJ
  have hVne : V ≠ ⊥ := by
    rintro rfl
    apply hQ1
    apply Subgroup.eq_bot_of_card_eq
    rw [← hVcard, Subgroup.card_bot]
  obtain ⟨g, hg, K', rfl⟩ := exists_eq_map_conj_parabolicRadical_prime r hVne hVrad
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcardR : (parabolicRadicalRoots τ K').ncard = (parabolicRadicalRoots τ J).ncard := by
    have h := hVcard
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_parabolicRadical,
      card_parabolicRadical] at h
    exact Nat.pow_right_injective hq h
  have hRJ0 : (parabolicRadicalRoots τ J).ncard ≠ 0 := by
    intro h0
    apply hQ1
    apply Subgroup.eq_bot_of_card_eq
    rw [card_parabolicRadical, h0, pow_zero]
  have hg' : g ∈ (adjointGroup τ K : Set (ModGL τ K)) := hg
  rw [adjointGroup_eq_iUnion_bruhatCell, Set.mem_iUnion] at hg'
  obtain ⟨w, hw⟩ := hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.mp hw
  set n := canonicalRep (coxeterSystem τ) K w with hn
  set S := (fun α => w • α) '' parabolicRadicalRoots τ K' with hS
  have hb'N : b' ∈ Subgroup.normalizer (parabolicRadical τ K K' : Set (ModGL τ K)) :=
    parabolicSubgroup_le_normalizer_parabolicRadical K' (borelGroup_le_parabolicSubgroup K' hb')
  have hVeq : (parabolicRadical τ K K').map (MulAut.conj (b * n * b')).toMonoidHom =
      (rootSpan τ K S).map (MulAut.conj b).toMonoidHom := by
    rw [GGTwoSig.map_conj_mul, GGTwoSig.map_conj_mul, GGTwoSig.map_conj_eq hb'N, parabolicRadical,
      (canonical_weyl_root_transport τ K).1 w _ (fun α hα => hα.1.1)]
  rw [hVeq] at hVinf ⊢
  have hbP : b ∈ parabolicSubgroup τ K J := borelGroup_le_parabolicSubgroup J hb
  have hSsub : S ⊆ oppRadicalRoots τ J := by
    rintro _ ⟨α, hα, rfl⟩
    by_contra hβ
    have hr : IsRoot τ (w • α) := IsRoot.smul hα.1.1 w
    have hle : rootSubgroup τ K (w • α) ≤ parabolicSubgroup τ K J := by
      rcases IsRoot.height_pos_or_neg hr with hpos | hneg
      · exact (rootSubgroup_le_posUnipotent hr hpos).trans (posUnipotent_le_parabolicSubgroup J)
      · refine rootSubgroup_le_parabolicSubgroup_of_neg ?_
        have hmem : -(w • α) ∈ {β | IsRoot τ β ∧ 0 < height β} :=
          ⟨IsRoot.neg hr, by rw [height_neg]; omega⟩
        by_contra hnot
        exact hβ ⟨hmem, hnot⟩
    have h1 : pinnedX τ K (w • α) 1 ∈ rootSpan τ K S :=
      pinnedX_mem_rootSpan (show w • α ∈ S from ⟨α, hα, rfl⟩) 1
    have h2 : b * pinnedX τ K (w • α) 1 * b⁻¹ ∈
        (rootSpan τ K S).map (MulAut.conj b).toMonoidHom ⊓ parabolicSubgroup τ K J :=
      Subgroup.mem_inf.mpr ⟨⟨_, h1, rfl⟩, mul_mem (mul_mem hbP
        (hle (Subgroup.subset_closure ⟨1, rfl⟩))) (inv_mem hbP)⟩
    rw [hVinf, Subgroup.mem_bot] at h2
    have h3 : pinnedX τ K (w • α) 1 = 1 := by
      have := congrArg (fun x => b⁻¹ * x * b) h2
      simpa [mul_assoc] using this
    exact one_ne_zero (pinnedX_injective τ K _ (h3.trans (pinnedX_zero τ K _).symm))
  have hSeq : S = oppRadicalRoots τ J := by
    refine Set.eq_of_subset_of_ncard_le hSsub ?_ ?_
    · rw [ncard_oppRadicalRoots, hS, Set.ncard_image_of_injective _ (MulAction.injective w),
        hcardR]
    · refine Set.finite_of_ncard_ne_zero ?_
      rwa [ncard_oppRadicalRoots]
  rw [hSeq, ← oppRadical]
  have hbB : b ∈ (borelGroup τ K : Set (ModGL τ K)) := hb
  rw [borelGroup_eq_mul_parabolic J] at hbB
  obtain ⟨u, hu, t, ht, rfl⟩ := Set.mem_mul.mp hbB
  obtain ⟨h, hh, v, hv, rfl⟩ := Set.mem_mul.mp ht
  have htM : h * v ∈ parabolicLevi τ K J :=
    mul_mem (torusGroup_le_parabolicLevi J hh) (parabolicLeviUnipotent_le_parabolicLevi J hv)
  refine ⟨u, hu, ?_⟩
  rw [GGTwoSig.map_conj_mul, GGTwoSig.map_conj_eq
    (parabolicLevi_le_normalizer_oppRadical hinj hδ hsq h₀ J htM)]

theorem hasGoodOppositePRadicals_parabolicRadical_prime [Finite K] (r : ℕ) [Fact r.Prime]
    [CharP K r] [IsSimpleGroup (adjointGroup τ K)]
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) :
    CFSG.GroupTheory.HasGoodOppositePRadicals r (adjointGroup τ K) (parabolicRadical τ K J) := by
  obtain ⟨w₀, δ, hinj, hδ, hsq, h₀⟩ := exists_longest τ
  exact ⟨oppRadical τ K J, oppRadical_mem_oppositePRadicals_prime r hinj hδ hsq h₀ J,
    parabolicRadical_sup_oppRadical hinj hδ hsq h₀ hJ,
    fun V hV => exists_eq_map_conj_oppRadical_prime r hinj hδ hsq h₀ hJ hV⟩

theorem hasGoodOppositePRadicals_adjointGroup_prime [Finite K] (r : ℕ) [Fact r.Prime]
    [CharP K r] [IsSimpleGroup (adjointGroup τ K)]
    {R : Subgroup (ModGL τ K)} (hR : R ≠ ⊥)
    (hRad : CFSG.GroupTheory.IsRadicalPGroup r (adjointGroup τ K) R) :
    CFSG.GroupTheory.HasGoodOppositePRadicals r (adjointGroup τ K) R := by
  obtain ⟨g, hg, J, rfl⟩ := exists_eq_map_conj_parabolicRadical_prime r hR hRad
  have hJ : J ≠ Set.univ := by
    rintro rfl
    apply hR
    rw [parabolicRadical_univ, Subgroup.map_bot]
  exact (hasGoodOppositePRadicals_parabolicRadical_prime r hJ).map_conj
    (Subgroup.le_normalizer hg)

theorem ggOppRadGood_adjointGroup [Finite K] [CharP K 2] [IsSimpleGroup (adjointGroup τ K)]
    {R : Subgroup (ModGL τ K)} (hR : R ≠ ⊥) (hRad : GGRadicalTwo (adjointGroup τ K) R) :
    GGOppRadGood (adjointGroup τ K) R := by
  have hRad' : CFSG.GroupTheory.IsRadicalPGroup 2 (adjointGroup τ K) R := by
    simpa [CFSG.GroupTheory.IsRadicalPGroup, GGRadicalTwo] using hRad
  have h := hasGoodOppositePRadicals_adjointGroup_prime (τ := τ) (K := K) 2 hR hRad'
  simpa [CFSG.GroupTheory.HasGoodOppositePRadicals, GGOppRadGood,
    CFSG.GroupTheory.oppositePRadicals, ggOppositeRadicals,
    CFSG.GroupTheory.IsRadicalPGroup, GGRadicalTwo] using h

end GGOppRadExc

end CFSG.StandardType
