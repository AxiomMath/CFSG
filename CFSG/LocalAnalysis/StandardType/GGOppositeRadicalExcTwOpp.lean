module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcTwCore

public section

namespace CFSG.StandardType

namespace GGOppRadExc

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.EvenOddRadical

section Ambient

variable {τ : Tag} {K : Type} [Field K] {w₀ : WeylGroup τ} {δ : Fin τ.rank → Fin τ.rank}

theorem oppRadical_eq_map_conj' (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) (hsq : w₀ * w₀ = 1)
    (h₀ : ReversesSigns w₀) (J : Set (Fin τ.rank)) :
    oppRadical τ K J = (parabolicRadical τ K (δ '' J)).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) K w₀)).toMonoidHom := by
  have hS : (fun α => w₀ • α) '' parabolicRadicalRoots τ (δ '' J) = oppRadicalRoots τ J := by
    rw [← longest_image_oppRadicalRoots hinj hδ hsq h₀ J, Set.image_image]
    simp only [smul_smul, hsq, one_smul, Set.image_id']
  rw [parabolicRadical, (canonical_weyl_root_transport τ K).1 w₀ _ (fun α hα => hα.1.1), hS]
  rfl

end Ambient

theorem longest_sq_and_reversesSigns {τ : Tag} {w₀ : WeylGroup τ}
    (hmax : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀) :
    w₀ * w₀ = 1 ∧ ReversesSigns w₀ := by
  obtain ⟨w₁, -, huniq, -, hsq, -⟩ := weyl_longest_element τ
  obtain rfl : w₀ = w₁ := huniq w₀ hmax
  exact ⟨by rw [← pow_two]; exact hsq, reversesSigns_of_forall_length_le hmax⟩

theorem diagramOrbit_subset_of_mem_of_stable
    (t : TwistTag) {T : Set (Fin t.tag.rank → ℤ)}
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ T)
    (hTρ : ∀ β ∈ T, permLattice t.perm β ∈ T) :
    (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)) ⊆ T := by
  have hpow : ∀ k : ℕ, permLattice (t.perm ^ k) α ∈ T := by
    intro k
    induction k with
    | zero => exact hα
    | succ k ih =>
      rw [pow_succ']
      exact hTρ _ ih
  intro β hβ
  rw [Finset.mem_coe, TwistTag.diagramOrbit, Finset.mem_image] at hβ
  obtain ⟨k, -, rfl⟩ := hβ
  exact hpow k

theorem exists_ne_one_twistHom_fixed_of_stable_rootSet
    (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)
    {T : Set (Fin t.tag.rank → ℤ)}
    (hT : T.Nonempty) (hTr : ∀ α ∈ T, IsRoot t.tag α)
    (hTρ : ∀ α ∈ T, permLattice t.perm α ∈ T) :
    ∃ u ∈ rootSpan t.tag K T,
      u ≠ 1 ∧ twistHom t K σ u = u := by
  obtain ⟨α, hα⟩ := hT
  obtain ⟨w, hw, a, ha⟩ := t.exists_diagramOrbit_eq (hTr α hα)
  set v := orbitConjEquiv t σ a hw (Multiplicative.ofAdd (1 : orbitField t K σ a)) with hv
  have hsub : ((fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊆ T := by
    intro β hβ
    apply diagramOrbit_subset_of_mem_of_stable t hα hTρ
    rw [ha, Finset.coe_image]
    exact hβ
  obtain ⟨hvS, hvΓ⟩ := Subgroup.mem_inf.1 v.2
  refine ⟨v, (biSup_mono hsub : rootSpan t.tag K _ ≤ rootSpan t.tag K T) hvS, fun h1 => ?_,
    ((mem_twistedFixedGroup_iff_twistHom (t := t) (K := K) (σ := σ)).1 hvΓ).2⟩
  have h2 : v = 1 := Subtype.ext h1
  rw [hv, MulEquiv.map_eq_one_iff] at h2
  exact one_ne_zero (congrArg Multiplicative.toAdd h2)

theorem eq_empty_of_rootSpan_le_of_stable (t : TwistTag) {K : Type} [Field K] (σ : K ≃+* K)
    {J : Set (Fin t.foldedTag.rank)}
    {S T : Set (Fin t.tag.rank → ℤ)} {b : ModGL t.tag K}
    (hb : b ∈ graphFixedParabolic t K σ.toRingHom J)
    (hV : (rootSpan t.tag K S ⊓ twistedFixedGroup t K σ.toRingHom).map
      (MulAut.conj b).toMonoidHom ⊓ graphFixedParabolic t K σ.toRingHom J = ⊥)
    (hTS : T ⊆ S) (hTr : ∀ α ∈ T, IsRoot t.tag α)
    (hTρ : ∀ α ∈ T, permLattice t.perm α ∈ T)
    (hTP : rootSpan t.tag K T ≤ parabolicSubgroup t.tag K (t.orbitUnion J))
    (hTU : rootSpan t.tag K T ≤ posUnipotent t.tag K ∨
      rootSpan t.tag K T ≤ negUnipotent t.tag K) :
    T = ∅ := by
  by_contra hne
  obtain ⟨w, hwX, hw1, hwF⟩ := exists_ne_one_twistHom_fixed_of_stable_rootSet t σ.toRingHom
    (Set.nonempty_iff_ne_empty.mpr hne) hTr hTρ
  have hwC : w ∈ adjointGroup t.tag K := rootSpan_le_adjointGroup K _ hwX
  have hwΓ : w ∈ twistedFixedGroup t K σ.toRingHom :=
    (mem_twistedFixedGroup_iff_twistHom (t := t) (K := K) (σ := σ.toRingHom)).2 ⟨hwC, hwF⟩
  have hwC₀ : w ∈ graphFixedRootGroup t K σ.toRingHom := by
    rcases hTU with h | h
    · exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨h hwX, hwΓ⟩)
    · exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨h hwX, hwΓ⟩)
  have hwP : w ∈ graphFixedParabolic t K σ.toRingHom J := by
    obtain ⟨-, hPC, -⟩ := diagram_fixed_parabolic_intersection t K σ J
    rw [← hPC]
    exact Subgroup.mem_inf.mpr ⟨hTP hwX, hwC₀⟩
  have hwS : w ∈ rootSpan t.tag K S ⊓ twistedFixedGroup t K σ.toRingHom :=
    Subgroup.mem_inf.mpr ⟨(biSup_mono hTS : rootSpan t.tag K T ≤ rootSpan t.tag K S) hwX, hwΓ⟩
  have h2 : b * w * b⁻¹ ∈ (rootSpan t.tag K S ⊓
      twistedFixedGroup t K σ.toRingHom).map (MulAut.conj b).toMonoidHom ⊓
        graphFixedParabolic t K σ.toRingHom J :=
    Subgroup.mem_inf.mpr ⟨⟨w, hwS, rfl⟩, mul_mem (mul_mem hb hwP) (inv_mem hb)⟩
  rw [hV, Subgroup.mem_bot] at h2
  apply hw1
  have := congrArg (fun x => b⁻¹ * x * b) h2
  simpa [mul_assoc] using this

variable {K : Type} [Field K] {t : TwistTag} {w₀ : WeylGroup t.tag}
  {δ : Fin t.tag.rank → Fin t.tag.rank}

@[expose] noncomputable def graphFixedOppRadicalFor (t : TwistTag) (σ : K ≃+* K)
    (J : Set (Fin t.foldedTag.rank)) : Subgroup (ModGL t.tag K) :=
  oppRadical t.tag K (t.orbitUnion J) ⊓ twistedFixedGroup t K σ.toRingHom

theorem canonicalRep_longest_mem_graphFixedRootGroup (σ : K ≃+* K)
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀) :
    canonicalRep (coxeterSystem t.tag) K w₀ ∈ graphFixedRootGroup t K σ.toRingHom ∧
      canonicalRep (coxeterSystem t.tag) K w₀ ∈ twistedFixedGroup t K σ.toRingHom := by
  have h := canonicalRep_mem_graphFixedRootGroup (K := K) (σ := σ.toRingHom)
    (mem_relWeylTwist_of_forall_length_le hmax)
  exact ⟨h, graphFixedRootGroup_le _ _ _ h⟩

theorem graphFixedOppRadicalFor_eq_map_conj_inv (σ : K ≃+* K)
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (hδδ : ∀ i, δ (δ i) = i)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (δ i) 1)
    {J : Set (Fin t.foldedTag.rank)}
    (hδJ : δ '' t.orbitUnion J = t.orbitUnion J) :
    graphFixedOppRadicalFor t σ J = (graphFixedParabolicRadical t K σ.toRingHom J).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)⁻¹).toMonoidHom := by
  obtain ⟨hsq, h₀⟩ := longest_sq_and_reversesSigns hmax
  have hinj : Function.Injective δ := Function.Involutive.injective hδδ
  obtain ⟨-, hnΓ⟩ := canonicalRep_longest_mem_graphFixedRootGroup σ hmax
  have h1 : (parabolicRadical t.tag K (t.orbitUnion J)).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)⁻¹).toMonoidHom =
      oppRadical t.tag K (t.orbitUnion J) := by
    rw [oppRadical_eq_map_conj hinj hδ hsq h₀, hδJ]
  rw [graphFixedParabolicRadical, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, h1,
    GGTwoSig.map_conj_eq (Subgroup.le_normalizer (inv_mem hnΓ))]
  rfl

theorem graphFixedOppRadicalFor_eq_map_conj (σ : K ≃+* K)
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (hδδ : ∀ i, δ (δ i) = i)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (δ i) 1)
    {J : Set (Fin t.foldedTag.rank)}
    (hδJ : δ '' t.orbitUnion J = t.orbitUnion J) :
    graphFixedOppRadicalFor t σ J = (graphFixedParabolicRadical t K σ.toRingHom J).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
  obtain ⟨hsq, h₀⟩ := longest_sq_and_reversesSigns hmax
  have hinj : Function.Injective δ := Function.Involutive.injective hδδ
  obtain ⟨-, hnΓ⟩ := canonicalRep_longest_mem_graphFixedRootGroup σ hmax
  have h1 : (parabolicRadical t.tag K (t.orbitUnion J)).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      oppRadical t.tag K (t.orbitUnion J) := by
    rw [oppRadical_eq_map_conj' hinj hδ hsq h₀, hδJ]
  rw [graphFixedParabolicRadical, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, h1,
    GGTwoSig.map_conj_eq (Subgroup.le_normalizer hnΓ)]
  rfl

theorem isRadicalPGroup_graphFixedOppRadicalFor [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r]
    (σ : K ≃+* K)
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (hδδ : ∀ i, δ (δ i) = i)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (δ i) 1)
    {J : Set (Fin t.foldedTag.rank)}
    (hδJ : δ '' t.orbitUnion J = t.orbitUnion J) :
    CFSG.GroupTheory.IsRadicalPGroup r (graphFixedRootGroup t K σ.toRingHom)
        (graphFixedOppRadicalFor t σ J) ∧
      Nat.card (graphFixedOppRadicalFor t σ J) =
        Nat.card (graphFixedParabolicRadical t K σ.toRingHom J) := by
  obtain ⟨hnC, -⟩ := canonicalRep_longest_mem_graphFixedRootGroup σ hmax
  rw [graphFixedOppRadicalFor_eq_map_conj_inv σ hmax hδδ hδ hδJ]
  exact ⟨(isRadicalPGroup_graphFixedParabolicRadical_prime r σ J).map_mulAut
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)⁻¹)
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (inv_mem hnC))),
    Subgroup.card_map_of_injective (MulAut.conj _).injective⟩

theorem graphFixedParabolicLevi_le_normalizer_graphFixedOppRadicalFor (σ : K ≃+* K)
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (hδδ : ∀ i, δ (δ i) = i)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin t.foldedTag.rank)) :
    graphFixedParabolicLevi t K σ.toRingHom J ≤
      Subgroup.normalizer (graphFixedOppRadicalFor t σ J : Set (ModGL t.tag K)) := by
  obtain ⟨hsq, h₀⟩ := longest_sq_and_reversesSigns hmax
  have hinj : Function.Injective δ := Function.Involutive.injective hδδ
  intro m hm
  obtain ⟨hmM, hmC⟩ := Subgroup.mem_inf.mp hm
  exact mem_normalizer_inf
    (parabolicLevi_le_normalizer_oppRadical hinj hδ hsq h₀ _ hmM)
    (Subgroup.le_normalizer (graphFixedRootGroup_le _ _ _ hmC))

theorem graphFixedOppRadicalFor_mem_oppositePRadicals [Finite K] (r : ℕ) [Fact r.Prime]
    [CharP K r] (σ : K ≃+* K)
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (hδδ : ∀ i, δ (δ i) = i)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (δ i) 1)
    {J : Set (Fin t.foldedTag.rank)}
    (hδJ : δ '' t.orbitUnion J = t.orbitUnion J) :
    graphFixedOppRadicalFor t σ J ∈ CFSG.GroupTheory.oppositePRadicals r
      (graphFixedRootGroup t K σ.toRingHom) (graphFixedParabolicRadical t K σ.toRingHom J) := by
  obtain ⟨hrad, hcard⟩ := isRadicalPGroup_graphFixedOppRadicalFor r σ hmax hδδ hδ hδJ
  refine ⟨hrad, hcard, ?_⟩
  rw [diagram_fixed_parabolic_root_radical_normalizers]
  obtain ⟨-, hPC, -⟩ := diagram_fixed_parabolic_intersection t K σ J
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hxV, hxP⟩ := Subgroup.mem_inf.mp hx
  have hxPA : x ∈ parabolicSubgroup t.tag K (t.orbitUnion J) := by
    rw [← hPC] at hxP
    exact (Subgroup.mem_inf.mp hxP).1
  have h1 : x ∈ parabolicSubgroup t.tag K (t.orbitUnion J) ⊓
      oppRadical t.tag K (t.orbitUnion J) :=
    Subgroup.mem_inf.mpr ⟨hxPA, (Subgroup.mem_inf.mp hxV).1⟩
  rwa [parabolicSubgroup_inf_oppRadical] at h1

theorem graphFixedParabolicRadical_sup_graphFixedOppRadicalFor (σ : K ≃+* K)
    [IsSimpleGroup (graphFixedRootGroup t K σ.toRingHom)]
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (hδδ : ∀ i, δ (δ i) = i)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (δ i) 1)
    {J : Set (Fin t.foldedTag.rank)}
    (hδJ : δ '' t.orbitUnion J = t.orbitUnion J) (hJ : J ≠ Set.univ) :
    graphFixedParabolicRadical t K σ.toRingHom J ⊔ graphFixedOppRadicalFor t σ J =
      graphFixedRootGroup t K σ.toRingHom := by
  obtain ⟨hnC, -⟩ := canonicalRep_longest_mem_graphFixedRootGroup σ hmax
  set C := graphFixedRootGroup t K σ.toRingHom with hC
  set n := canonicalRep (coxeterSystem t.tag) K w₀ with hn
  set Q := graphFixedParabolicRadical t K σ.toRingHom J with hQdef
  set Q' := graphFixedOppRadicalFor t σ J with hQ'def
  set L := graphFixedParabolicLevi t K σ.toRingHom J with hLdef
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLP, -, -, -, -, -, -, hne⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
  have hQ1 : Q ≠ ⊥ := hne hJ
  have hQC : Q ≤ C := hQP.trans (graphFixedParabolic_le _ _ _ J)
  have hQ'eq : Q' = Q.map (MulAut.conj n).toMonoidHom :=
    graphFixedOppRadicalFor_eq_map_conj σ hmax hδδ hδ hδJ
  have hQ'C : Q' ≤ C := by
    rw [hQ'eq]
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem hnC (hQC hq)) (inv_mem hnC)
  have hPQ : graphFixedParabolic t K σ.toRingHom J ≤
      Subgroup.normalizer (Q : Set (ModGL t.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm
  have hLQ : L ≤ Subgroup.normalizer (Q : Set (ModGL t.tag K)) := hLP.trans hPQ
  have hLQ' : L ≤ Subgroup.normalizer (Q' : Set (ModGL t.tag K)) :=
    graphFixedParabolicLevi_le_normalizer_graphFixedOppRadicalFor σ hmax hδδ hδ J
  have hLn : L.map (MulAut.conj n).toMonoidHom ≤ L :=
    map_conj_graphFixedParabolicLevi_le hnC (by
      have := map_conj_parabolicLevi_le (k := K) hδ (t.orbitUnion J)
      rwa [hδJ] at this)
  have hgen : C ≤ Q ⊔ Q' ⊔ L := by
    refine sup_le ((graphFixedPosUnipotent_le_sup σ J).trans
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)) ?_
    rw [← map_conj_graphFixedPosUnipotent hmax]
    refine (Subgroup.map_mono (graphFixedPosUnipotent_le_sup σ J)).trans ?_
    rw [Subgroup.map_sup, ← hQ'eq]
    exact sup_le (le_sup_right.trans le_sup_left) (hLn.trans le_sup_right)
  have hXC : Q ⊔ Q' ≤ C := sup_le hQC hQ'C
  refine le_antisymm hXC ?_
  have hN : C ≤ Subgroup.normalizer ((Q ⊔ Q' : Subgroup (ModGL t.tag K)) :
      Set (ModGL t.tag K)) :=
    hgen.trans (sup_le Subgroup.le_normalizer fun m hm =>
      mem_normalizer_sup_of_mem (hLQ hm) (hLQ' hm))
  have : ((Q ⊔ Q').subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q ⊔ Q').subgroupOf C) with h | h
  · exfalso
    apply hQ1
    have hdis := Subgroup.subgroupOf_eq_bot.1 h
    exact eq_bot_iff.2 fun q hq => (Subgroup.disjoint_def.1 hdis)
      (Subgroup.mem_sup_left hq) (hQC hq) ▸ Subgroup.mem_bot.2 rfl
  · exact Subgroup.subgroupOf_eq_top.1 h

theorem exists_eq_map_conj_graphFixedOppRadicalFor [Finite K] (r : ℕ) [Fact r.Prime]
    [CharP K r] (σ : K ≃+* K) (hσ : σ ^ t.order = 1)
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (hδδ : ∀ i, δ (δ i) = i)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (δ i) 1)
    {J : Set (Fin t.foldedTag.rank)}
    (hδJ : δ '' t.orbitUnion J = t.orbitUnion J) (hJ : J ≠ Set.univ)
    {V : Subgroup (ModGL t.tag K)}
    (hV : V ∈ CFSG.GroupTheory.oppositePRadicals r (graphFixedRootGroup t K σ.toRingHom)
      (graphFixedParabolicRadical t K σ.toRingHom J)) :
    ∃ u ∈ graphFixedParabolicRadical t K σ.toRingHom J,
      V = (graphFixedOppRadicalFor t σ J).map (MulAut.conj u).toMonoidHom := by
  have := finite_modGL (τ := t.tag) (K := K)
  obtain ⟨hVrad, hVcard, hVinf⟩ := hV
  rw [diagram_fixed_parabolic_root_radical_normalizers] at hVinf
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hB, -, hHV, -, -, hne⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
  have hQ1 := hne hJ
  have hVne : V ≠ ⊥ := by
    rintro rfl
    apply hQ1
    apply Subgroup.eq_bot_of_card_eq
    rw [← hVcard, Subgroup.card_bot]
  obtain ⟨g, hg, K', rfl⟩ :=
    exists_eq_map_conj_graphFixedParabolicRadical_prime r σ hσ hVne hVrad
  have hg' : g ∈ (graphFixedRootGroup t K σ.toRingHom : Set (ModGL t.tag K)) := hg
  rw [graphFixedRootGroup_eq_iUnion σ.surjective, Set.mem_iUnion] at hg'
  obtain ⟨w, hw⟩ := hg'
  obtain ⟨y, hy, b', hb', rfl⟩ := Set.mem_mul.mp hw
  obtain ⟨b, hb, n', hn', rfl⟩ := Set.mem_mul.mp hy
  rw [Set.mem_singleton_iff] at hn'
  subst hn'
  set n := canonicalRep (coxeterSystem t.tag) K (w : WeylGroup t.tag) with hn
  have hnC : n ∈ graphFixedRootGroup t K σ.toRingHom :=
    canonicalRep_mem_graphFixedRootGroup w.2
  have hnΓ : n ∈ twistedFixedGroup t K σ.toRingHom := graphFixedRootGroup_le _ _ _ hnC
  set S := (fun α => (w : WeylGroup t.tag) • α) ''
    parabolicRadicalRoots t.tag (t.orbitUnion K') with hS
  obtain ⟨-, -, -, -, -, -, -, -, hQP', hQnorm', -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ K'
  have hb'N : b' ∈ Subgroup.normalizer
      (graphFixedParabolicRadical t K σ.toRingHom K' : Set (ModGL t.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP').1 hQnorm'
      ((le_sup_left : graphFixedRootBorel t K σ.toRingHom ≤
        graphFixedParabolic t K σ.toRingHom K') hb')
  have hVeq : (graphFixedParabolicRadical t K σ.toRingHom K').map
      (MulAut.conj (b * n * b')).toMonoidHom =
      (rootSpan t.tag K S ⊓ twistedFixedGroup t K σ.toRingHom).map
        (MulAut.conj b).toMonoidHom := by
    rw [GGTwoSig.map_conj_mul, GGTwoSig.map_conj_mul, GGTwoSig.map_conj_eq hb'N,
      graphFixedParabolicRadical, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
      GGTwoSig.map_conj_eq (Subgroup.le_normalizer hnΓ), parabolicRadical,
      (canonical_weyl_root_transport t.tag K).1 _ _ (fun α hα => hα.1.1)]
  rw [hVeq] at hVinf hVcard ⊢
  have hbP : b ∈ graphFixedParabolic t K σ.toRingHom J :=
    (le_sup_left : graphFixedRootBorel t K σ.toRingHom ≤
      graphFixedParabolic t K σ.toRingHom J) hb
  have hwρ := (mem_relWeylTwist_iff_smul t).1 w.2
  have hSr : ∀ α ∈ S, IsRoot t.tag α := by
    rintro _ ⟨α, hα, rfl⟩
    exact IsRoot.smul hα.1.1 _
  have hSρ : ∀ α ∈ S, permLattice t.perm α ∈ S := by
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨permLattice t.perm α, permLattice_mem_parabolicRadicalRoots hα, hwρ α⟩
  set A := t.orbitUnion J with hA
  set Tp := {α | α ∈ S ∧ 0 < height α} with hTp
  set Tn := {α | α ∈ S ∧ height α < 0 ∧ -α ∈ parabolicPosRoots t.tag A} with hTn
  have hTp0 : Tp = ∅ := eq_empty_of_rootSpan_le_of_stable t σ hbP hVinf (fun _ h => h.1)
    (fun _ h => hSr _ h.1) (fun α h => ⟨hSρ α h.1, by rw [height_permLattice]; exact h.2⟩)
    ((rootSpan_le_posUnipotent fun α h => ⟨hSr α h.1, h.2⟩).trans
      (posUnipotent_le_parabolicSubgroup A))
    (Or.inl (rootSpan_le_posUnipotent fun α h => ⟨hSr α h.1, h.2⟩))
  have hTn0 : Tn = ∅ := eq_empty_of_rootSpan_le_of_stable t σ hbP hVinf (fun _ h => h.1)
    (fun _ h => hSr _ h.1)
    (fun α h => ⟨hSρ α h.1, by rw [height_permLattice]; exact h.2.1, by
      have := permLattice_mem_parabolicPosRoots h.2.2
      exact this⟩)
    (iSup₂_le fun α h => rootSubgroup_le_parabolicSubgroup_of_neg h.2.2)
    (Or.inr (rootSpan_le_negUnipotent fun α h => ⟨hSr α h.1, h.2.1⟩))
  have hSsub : S ⊆ oppRadicalRoots t.tag A := by
    intro β hβS
    by_contra hβ
    have hr : IsRoot t.tag β := hSr β hβS
    rcases IsRoot.height_pos_or_neg hr with hpos | hneg
    · have hmem : β ∈ Tp := ⟨hβS, hpos⟩
      rw [hTp0] at hmem
      exact hmem
    · have hmem' : -β ∈ parabolicPosRoots t.tag A := by
        by_contra hnot
        exact hβ ⟨⟨IsRoot.neg hr, by rw [height_neg]; omega⟩, hnot⟩
      have hmem : β ∈ Tn := ⟨hβS, hneg, hmem'⟩
      rw [hTn0] at hmem
      exact hmem
  have hle : rootSpan t.tag K S ⊓ twistedFixedGroup t K σ.toRingHom ≤
      graphFixedOppRadicalFor t σ J :=
    inf_le_inf_right _ (biSup_mono hSsub)
  have hcard : Nat.card (graphFixedOppRadicalFor t σ J) ≤
      Nat.card (rootSpan t.tag K S ⊓ twistedFixedGroup t K σ.toRingHom :
        Subgroup (ModGL t.tag K)) := by
    rw [(isRadicalPGroup_graphFixedOppRadicalFor r σ hmax hδδ hδ hδJ).2, ← hVcard,
      Subgroup.card_map_of_injective (MulAut.conj b).injective]
  rw [Subgroup.eq_of_le_of_card_ge hle hcard]
  have hbB : b ∈ (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) := hb
  rw [hB] at hbB
  obtain ⟨u, hu, m, hm, rfl⟩ := Set.mem_mul.mp hbB
  refine ⟨u, hu, ?_⟩
  rw [GGTwoSig.map_conj_mul, GGTwoSig.map_conj_eq
    (graphFixedParabolicLevi_le_normalizer_graphFixedOppRadicalFor σ hmax hδδ hδ J (hHV hm))]

theorem hasGoodOppositePRadicals_graphFixedParabolicRadical [Finite K] (r : ℕ) [Fact r.Prime]
    [CharP K r] (σ : K ≃+* K) (hσ : σ ^ t.order = 1)
    [IsSimpleGroup (graphFixedRootGroup t K σ.toRingHom)]
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (hδδ : ∀ i, δ (δ i) = i)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (δ i) 1)
    {J : Set (Fin t.foldedTag.rank)}
    (hδJ : δ '' t.orbitUnion J = t.orbitUnion J) (hJ : J ≠ Set.univ) :
    CFSG.GroupTheory.HasGoodOppositePRadicals r (graphFixedRootGroup t K σ.toRingHom)
      (graphFixedParabolicRadical t K σ.toRingHom J) :=
  ⟨graphFixedOppRadicalFor t σ J,
    graphFixedOppRadicalFor_mem_oppositePRadicals r σ hmax hδδ hδ hδJ,
    graphFixedParabolicRadical_sup_graphFixedOppRadicalFor σ hmax hδδ hδ hδJ hJ,
    fun _ hV => exists_eq_map_conj_graphFixedOppRadicalFor r σ hσ hmax hδδ hδ hδJ hJ hV⟩

theorem hasGoodOppositePRadicals_graphFixedRootGroup_of_longest [Finite K] (r : ℕ)
    [Fact r.Prime] [CharP K r] (σ : K ≃+* K) (hσ : σ ^ t.order = 1)
    [IsSimpleGroup (graphFixedRootGroup t K σ.toRingHom)]
    (hmax : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
    (hδδ : ∀ i, δ (δ i) = i)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single (δ i) 1)
    (hδorb : ∀ J : Set (Fin t.foldedTag.rank), δ '' t.orbitUnion J = t.orbitUnion J)
    {R : Subgroup (ModGL t.tag K)} (hR : R ≠ ⊥)
    (hRad : CFSG.GroupTheory.IsRadicalPGroup r (graphFixedRootGroup t K σ.toRingHom) R) :
    CFSG.GroupTheory.HasGoodOppositePRadicals r (graphFixedRootGroup t K σ.toRingHom) R := by
  obtain ⟨g, hg, J, rfl⟩ := exists_eq_map_conj_graphFixedParabolicRadical_prime r σ hσ hR hRad
  have hJ : J ≠ Set.univ := by
    rintro rfl
    apply hR
    rw [graphFixedParabolicRadical_univ, Subgroup.map_bot]
  exact (hasGoodOppositePRadicals_graphFixedParabolicRadical r σ hσ hmax hδδ hδ
    (hδorb J) hJ).map_conj (Subgroup.le_normalizer hg)

section TwistedE6

variable {K : Type} [Field K]

variable {w₀ : WeylGroup TwistTag.E6.tag} {δ : Fin TwistTag.E6.tag.rank → Fin TwistTag.E6.tag.rank}

theorem ggOppRadGood_graphFixedRootGroup [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1)
    [IsSimpleGroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)]
    (hmax : ∀ w, (coxeterSystem TwistTag.E6.tag).length w ≤
      (coxeterSystem TwistTag.E6.tag).length w₀) (hδδ : ∀ i, δ (δ i) = i)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = -Pi.single (δ i) 1)
    (hδorb : ∀ J : Set (Fin TwistTag.E6.foldedTag.rank),
      δ '' TwistTag.E6.orbitUnion J = TwistTag.E6.orbitUnion J)
    {R : Subgroup (ModGL TwistTag.E6.tag K)} (hR : R ≠ ⊥)
    (hRad : GGRadicalTwo (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) R) :
    GGOppRadGood (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRad' : CFSG.GroupTheory.IsRadicalPGroup 2
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) R := by
    simpa only [CFSG.GroupTheory.IsRadicalPGroup, GGRadicalTwo] using hRad
  have h := hasGoodOppositePRadicals_graphFixedRootGroup_of_longest (t := TwistTag.E6)
    (w₀ := w₀) (δ := δ) 2 σ hσ hmax hδδ hδ hδorb hR hRad'
  simpa only [CFSG.GroupTheory.HasGoodOppositePRadicals, GGOppRadGood,
    CFSG.GroupTheory.oppositePRadicals, ggOppositeRadicals,
    CFSG.GroupTheory.IsRadicalPGroup, GGRadicalTwo] using h

end TwistedE6

end GGOppRadExc

end CFSG.StandardType
