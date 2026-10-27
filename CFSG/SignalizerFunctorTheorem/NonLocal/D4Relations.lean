module

public import CFSG.LieType.Chevalley.EvenTrialityTraceCommutators

public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

section Pairs

variable {K : Type} [Field K]

theorem commute_of_d4CommB_nc {α β : Fin TwistTag.D4.tag.rank → ℤ} (h : d4CommB α β = true)
    (s t : K) : Commute (pinnedX TwistTag.D4.tag K α s) (pinnedX TwistTag.D4.tag K β t) := by
  simp only [d4CommB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hα, hβ⟩, hne⟩, hne'⟩, hn⟩ := h
  have hn' : ¬IsRoot TwistTag.D4.tag (α + β) := fun hr => by
    rw [← d4IsRootB_iff, hn] at hr
    exact Bool.false_ne_true hr
  exact (simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl) (d4IsRootB_iff.1 hα)
    (d4IsRootB_iff.1 hβ) hne hne').2 hn' K _ (mem_rootSubgroup.2 ⟨s, rfl⟩) _
    (mem_rootSubgroup.2 ⟨t, rfl⟩)

theorem commutator_of_d4SumB_nc [CharP K 2] {α β γ : Fin TwistTag.D4.tag.rank → ℤ}
    (h : d4SumB α β γ = true) (s t : K) :
    ⁅pinnedX TwistTag.D4.tag K α s, pinnedX TwistTag.D4.tag K β t⁆ =
      pinnedX TwistTag.D4.tag K γ (s * t) := by
  simp only [d4SumB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hα, hβ⟩, hne⟩, hne'⟩, hsum⟩, hγ⟩ := h
  subst hsum
  obtain ⟨hε, hf⟩ := (simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl)
    (d4IsRootB_iff.1 hα) (d4IsRootB_iff.1 hβ) hne hne').1 (d4IsRootB_iff.1 hγ)
  rw [hf K s t]
  congr 1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rcases hε with h | h
  · rw [h]
    simp
  · rw [h]
    push_cast
    linear_combination (-(s * t)) * h2

end Pairs

section OrbitProducts

variable {K : Type} [Field K] [CharP K 2]

theorem commutator_trialityOrbitProd_nc
    {α β γ : Fin TwistTag.D4.tag.rank → ℤ} (σ : K →+* K)
    (hs : d4SumB α β γ = true ∧
      d4SumB (permLattice TwistTag.D4.perm α) (permLattice TwistTag.D4.perm β) γ = true ∧
      d4SumB (permLattice (TwistTag.D4.perm ^ 2) α) (permLattice (TwistTag.D4.perm ^ 2) β) γ = true)
    (hc : d4CommB α (permLattice TwistTag.D4.perm β) = true ∧
      d4CommB α (permLattice (TwistTag.D4.perm ^ 2) β) = true ∧
      d4CommB (permLattice TwistTag.D4.perm α) β = true ∧
      d4CommB (permLattice TwistTag.D4.perm α) (permLattice (TwistTag.D4.perm ^ 2) β) = true ∧
      d4CommB (permLattice (TwistTag.D4.perm ^ 2) α) β = true ∧
      d4CommB (permLattice (TwistTag.D4.perm ^ 2) α) (permLattice TwistTag.D4.perm β) = true)
    (hz : d4CommB α γ = true ∧ d4CommB (permLattice TwistTag.D4.perm α) γ = true ∧
      d4CommB (permLattice (TwistTag.D4.perm ^ 2) α) γ = true ∧ d4CommB β γ = true ∧
      d4CommB (permLattice TwistTag.D4.perm β) γ = true ∧
      d4CommB (permLattice (TwistTag.D4.perm ^ 2) β) γ = true)
    (s t : K) :
    ⁅(trialityOrbitProd K σ α s : ModGL TwistTag.D4.tag K),
        (trialityOrbitProd K σ β t : ModGL TwistTag.D4.tag K)⁆ =
      pinnedX TwistTag.D4.tag K γ (s * t + σ s * σ t + σ (σ s) * σ (σ t)) := by
  obtain ⟨hs0, hs1, hs2⟩ := hs
  obtain ⟨hc01, hc02, hc10, hc12, hc20, hc21⟩ := hc
  obtain ⟨hz0, hz1, hz2, hw0, hw1, hw2⟩ := hz
  set zs := [pinnedX TwistTag.D4.tag K α s,
    pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm α) (σ s),
    pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) α) (σ (σ s))]
  set ws := [pinnedX TwistTag.D4.tag K β t,
    pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm β) (σ t),
    pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) β) (σ (σ t))]
  have ez : (trialityOrbitProd K σ α s : ModGL TwistTag.D4.tag K) = zs.prod := by
    simp only [coe_trialityOrbitProd, zs, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have ew : (trialityOrbitProd K σ β t : ModGL TwistTag.D4.tag K) = ws.prod := by
    simp only [coe_trialityOrbitProd, ws, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hZc : ∀ (δ : Fin TwistTag.D4.tag.rank → ℤ), d4CommB δ γ = true → ∀ a : K,
      ∀ c ∈ rootSubgroup TwistTag.D4.tag K γ, Commute (pinnedX TwistTag.D4.tag K δ a) c := by
    intro δ hδ a c hcm
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hcm
    exact commute_of_d4CommB_nc hδ a d
  have h1 : ∀ {x y : ModGL TwistTag.D4.tag K}, Commute x y → ⁅x, y⁆ = 1 := fun h =>
    commutatorElement_eq_one_iff_mul_comm.2 h
  have key := commutator_list_prod_of_central (commute_rootSubgroup γ) zs ws
    (by
      intro z hz c hcm
      simp only [zs, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact hZc _ hz0 _ c hcm
      · exact hZc _ hz1 _ c hcm
      · exact hZc _ hz2 _ c hcm)
    (by
      intro w hw c hcm
      simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hZc _ hw0 _ c hcm
      · exact hZc _ hw1 _ c hcm
      · exact hZc _ hw2 _ c hcm)
    (by
      intro z hz w hw
      simp only [zs, ws, List.mem_cons, List.not_mem_nil, or_false] at hz hw
      rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
      · rw [commutator_of_d4SumB_nc hs0]
        exact mem_rootSubgroup.2 ⟨_, rfl⟩
      · rw [h1 (commute_of_d4CommB_nc hc01 _ _)]
        exact Subgroup.one_mem _
      · rw [h1 (commute_of_d4CommB_nc hc02 _ _)]
        exact Subgroup.one_mem _
      · rw [h1 (commute_of_d4CommB_nc hc10 _ _)]
        exact Subgroup.one_mem _
      · rw [commutator_of_d4SumB_nc hs1]
        exact mem_rootSubgroup.2 ⟨_, rfl⟩
      · rw [h1 (commute_of_d4CommB_nc hc12 _ _)]
        exact Subgroup.one_mem _
      · rw [h1 (commute_of_d4CommB_nc hc20 _ _)]
        exact Subgroup.one_mem _
      · rw [h1 (commute_of_d4CommB_nc hc21 _ _)]
        exact Subgroup.one_mem _
      · rw [commutator_of_d4SumB_nc hs2]
        exact mem_rootSubgroup.2 ⟨_, rfl⟩)
  rw [ez, ew, key.2]
  simp only [zs, ws, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    commutator_of_d4SumB_nc hs0, commutator_of_d4SumB_nc hs1, commutator_of_d4SumB_nc hs2,
    h1 (commute_of_d4CommB_nc hc01 _ _), h1 (commute_of_d4CommB_nc hc02 _ _),
    h1 (commute_of_d4CommB_nc hc10 _ _), h1 (commute_of_d4CommB_nc hc12 _ _),
    h1 (commute_of_d4CommB_nc hc20 _ _), h1 (commute_of_d4CommB_nc hc21 _ _), one_mul]
  rw [← pinnedX_add, ← pinnedX_add, add_assoc]


end OrbitProducts

section Main

variable {K : Type} [Field K] [CharP K 2]

theorem commutator_trialityOrbitProd_of_check_nc
    {α β γ : Fin TwistTag.D4.tag.rank → ℤ}
    (h : trialityPairCheck α β γ = true) (σ : K →+* K) (s t : K) :
    ⁅(trialityOrbitProd K σ α s : ModGL TwistTag.D4.tag K),
        (trialityOrbitProd K σ β t : ModGL TwistTag.D4.tag K)⁆ =
      pinnedX TwistTag.D4.tag K γ (s * t + σ s * σ t + σ (σ s) * σ (σ t)) := by
  simp only [trialityPairCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs0, hs1⟩, hs2⟩, hc01⟩, hc02⟩, hc10⟩, hc12⟩, hc20⟩, hc21⟩, hz0⟩, hz1⟩,
    hz2⟩, hw0⟩, hw1⟩, hw2⟩ := h
  exact commutator_trialityOrbitProd_nc σ ⟨hs0, hs1, hs2⟩ ⟨hc01, hc02, hc10, hc12, hc20, hc21⟩
    ⟨hz0, hz1, hz2, hw0, hw1, hw2⟩ s t


omit [CharP K 2] in
theorem commute_trialityOrbit_nc
    {p : Fin 6 × Fin 6} (hp : p ∈ trialityCommPairs)
    {g g' : ModGL TwistTag.D4.tag K}
    (hg : g ∈ rootSpan TwistTag.D4.tag K (trialityOrbit p.1 : Set (Fin TwistTag.D4.tag.rank → ℤ)))
    (hg' : g' ∈ rootSpan TwistTag.D4.tag K
      (trialityOrbit p.2 : Set (Fin TwistTag.D4.tag.rank → ℤ))) : Commute g g' :=
  commute_of_mem_rootSpan (fun α hα β hβ s t =>
    commute_of_d4CommB_nc (trialityOrbit_comm p hp α hα β hβ) s t) hg hg'


theorem even_triality_trace_commutators_nc
    (K : Type) [Field K] [CharP K 2] (σ : K →+* K)
    (hσ : σ ^ 3 = 1) :
    (∀ s t : K, ⁅trialityX₁ K σ s, trialityX₄ K σ t⁆ =
      trialityX₅ K σ (trialityTrace K σ hσ (s * t))) ∧
    (∀ s t : K, ⁅trialityX₃ K σ s, trialityX₄ K σ t⁆ =
      trialityX₆ K σ (trialityTrace K σ hσ (s * t))) ∧
    (∀ b e : trialityFixedField K σ, ⁅trialityX₂ K σ b, trialityX₅ K σ e⁆ =
      trialityX₆ K σ (b * e)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₁ K σ a) (trialityX₅ K σ b)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₁ K σ a) (trialityX₆ K σ b)) ∧
    (∀ (a : trialityFixedField K σ) (b : K), Commute (trialityX₂ K σ a) (trialityX₃ K σ b)) ∧
    (∀ (a : trialityFixedField K σ) (b : K), Commute (trialityX₂ K σ a) (trialityX₄ K σ b)) ∧
    (∀ a b : trialityFixedField K σ, Commute (trialityX₂ K σ a) (trialityX₆ K σ b)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₃ K σ a) (trialityX₅ K σ b)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₃ K σ a) (trialityX₆ K σ b)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₄ K σ a) (trialityX₅ K σ b)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₄ K σ a) (trialityX₆ K σ b)) ∧
    (∀ a b : trialityFixedField K σ, Commute (trialityX₅ K σ a) (trialityX₆ K σ b)) ∧
    (∀ s t : K, trialityTraceForm K σ hσ s t = trialityTrace K σ hσ (s * t)) ∧
    (trialityTraceForm K σ hσ).Nondegenerate := by
  have hT : ∀ s t : K, s * t + σ s * σ t + σ (σ s) * σ (σ t) =
      (trialityTrace K σ hσ (s * t) : K) := fun s t => by
    rw [coe_trialityTrace, map_mul, map_mul]
  have hcomm : ∀ {p : Fin 6 × Fin 6}, p ∈ trialityCommPairs →
      ∀ {x y : adjointGroup TwistTag.D4.tag K},
        (x : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K
          (trialityOrbit p.1 : Set (Fin TwistTag.D4.tag.rank → ℤ)) →
        (y : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K
          (trialityOrbit p.2 : Set (Fin TwistTag.D4.tag.rank → ℤ)) → Commute x y :=
    fun hp _ _ hx hy => Subtype.ext (commute_trialityOrbit_nc hp hx hy)
  have m1 : ∀ a : K, (trialityX₁ K σ a : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K
      (trialityOrbit 0 : Set (Fin TwistTag.D4.tag.rank → ℤ)) := trialityOrbitProd_mem_rootSpan σ
  have m3 : ∀ a : K, (trialityX₃ K σ a : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K
      (trialityOrbit 2 : Set (Fin TwistTag.D4.tag.rank → ℤ)) := trialityOrbitProd_mem_rootSpan σ
  have m4 : ∀ a : K, (trialityX₄ K σ a : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K
      (trialityOrbit 3 : Set (Fin TwistTag.D4.tag.rank → ℤ)) := trialityOrbitProd_mem_rootSpan σ
  have m2 : ∀ a : trialityFixedField K σ, (trialityX₂ K σ a : ModGL TwistTag.D4.tag K) ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit 1 : Set (Fin TwistTag.D4.tag.rank → ℤ)) :=
    fun a => pinnedX_mem_rootSpan_trialityOrbit 1 _
  have m5 : ∀ a : trialityFixedField K σ, (trialityX₅ K σ a : ModGL TwistTag.D4.tag K) ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit 4 : Set (Fin TwistTag.D4.tag.rank → ℤ)) :=
    fun a => pinnedX_mem_rootSpan_trialityOrbit 4 _
  have m6 : ∀ a : trialityFixedField K σ, (trialityX₆ K σ a : ModGL TwistTag.D4.tag K) ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit 5 : Set (Fin TwistTag.D4.tag.rank → ℤ)) :=
    fun a => pinnedX_mem_rootSpan_trialityOrbit 5 _
  refine ⟨fun s t => Subtype.ext ?_, fun s t => Subtype.ext ?_, fun b e => Subtype.ext ?_,
    fun a b => hcomm (p := (0, 4)) (by decide) (m1 a) (m5 b),
    fun a b => hcomm (p := (0, 5)) (by decide) (m1 a) (m6 b),
    fun a b => hcomm (p := (1, 2)) (by decide) (m2 a) (m3 b),
    fun a b => hcomm (p := (1, 3)) (by decide) (m2 a) (m4 b),
    fun a b => hcomm (p := (1, 5)) (by decide) (m2 a) (m6 b),
    fun a b => hcomm (p := (2, 4)) (by decide) (m3 a) (m5 b),
    fun a b => hcomm (p := (2, 5)) (by decide) (m3 a) (m6 b),
    fun a b => hcomm (p := (3, 4)) (by decide) (m4 a) (m5 b),
    fun a b => hcomm (p := (3, 5)) (by decide) (m4 a) (m6 b),
    fun a b => hcomm (p := (4, 5)) (by decide) (m5 a) (m6 b),
    trialityTraceForm_apply K σ hσ, trialityTraceForm_nondegenerate K σ hσ⟩
  · rw [coe_commutatorElement_adjoint]
    exact (commutator_trialityOrbitProd_of_check_nc trialityPairCheck_14 σ s t).trans
      (congrArg _ (hT s t))
  · rw [coe_commutatorElement_adjoint]
    exact (commutator_trialityOrbitProd_of_check_nc trialityPairCheck_34 σ s t).trans
      (congrArg _ (hT s t))
  · rw [coe_commutatorElement_adjoint]
    exact commutator_of_d4SumB_nc triality_sum_25 (b : K) (e : K)


end Main

end CFSG.SignalizerFunctorTheorem.NonLocal
