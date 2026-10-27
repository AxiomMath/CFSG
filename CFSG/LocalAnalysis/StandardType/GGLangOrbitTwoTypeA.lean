module

public import CFSG.LocalAnalysis.StandardType.GGLangOrbitTwo
public import CFSG.LocalAnalysis.StandardType.GGLangOrbitTwoE6Checks
public import CFSG.LocalAnalysis.StandardType.GGLangSixRoot

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem orbitTwo_perm_eq_one_F4 (π : Equiv.Perm (Fin Tag.F4.rank))
    (h : ∀ i j, Tag.F4.cartan (π i) (π j) = Tag.F4.cartan i j) : π = 1 := by
  have key : ∀ π : Equiv.Perm (Fin Tag.F4.rank),
      (∀ i j, tagCartanEntry .F4 (π i) (π j) = tagCartanEntry .F4 i j) → π = 1 := by
    decide +kernel
  exact key π h

private theorem e6A1_compRank_pair (α : Fin Tag.E6.rank → ℤ) (hα : α ≠ 0) :
    compRank ({α, -α} : Set (Fin Tag.E6.rank → ℤ)) = 1 := by
  classical
  have hne : (fun i : Fin Tag.E6.rank => (α i : ℚ)) ≠ 0 := by
    intro h
    apply hα
    funext i
    have := congrFun h i
    simpa using this
  have himg : (fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) ''
      ({α, -α} : Set (Fin Tag.E6.rank → ℤ)) =
      ({(fun i : Fin Tag.E6.rank => (α i : ℚ)),
        -(fun i : Fin Tag.E6.rank => (α i : ℚ))} : Set (Fin Tag.E6.rank → ℚ)) := by
    ext x
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      rcases hγ with rfl | rfl
      · exact Or.inl rfl
      · right
        funext i
        simp
    · rintro (hx | hx)
      · exact ⟨α, Or.inl rfl, hx.symm⟩
      · refine ⟨-α, Or.inr rfl, ?_⟩
        rw [hx]
        funext i
        simp
  have hspan : Submodule.span ℚ
      ({(fun i : Fin Tag.E6.rank => (α i : ℚ)),
        -(fun i : Fin Tag.E6.rank => (α i : ℚ))} : Set (Fin Tag.E6.rank → ℚ)) =
      Submodule.span ℚ ({(fun i : Fin Tag.E6.rank => (α i : ℚ))} : Set _) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.subset_span (Set.mem_singleton _)
      · exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton _))
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Submodule.subset_span (Set.mem_insert _ _)
  rw [compRank, himg, hspan]
  exact finrank_span_singleton hne

private theorem e6_component_A1_case
    {C : Set (Fin Tag.E6.rank → ℤ)} (hC : IsRootComponent C) (hne : C.Nonempty)
    (hno : ∀ x ∈ C, ∀ y ∈ C, iform x y ≠ -1) : compRank C = 1 ∧ C.ncard = 2 := by
  classical
  obtain ⟨α, hαC⟩ := hne
  have hαroot : IsRoot Tag.E6 α := hC.isRoot α hαC
  have hself : iform α α = 2 := e6_iform_self_check α (mem_rootFinset.2 hαroot)
  have hα0 : α ≠ 0 := by
    intro h
    have h0 : iform α α = 0 := by rw [h]; simp [iform]
    rw [hself] at h0
    omega
  have hαne : α ≠ -α := by
    intro h
    have h1 : iform α (-α) = -iform α α := by
      rw [← neg_one_smul ℤ α, iform_smul_right]
      ring
    have h2 : iform α α = iform α (-α) := congrArg (fun x => iform α x) h
    rw [h1, hself] at h2
    omega
  have hSC : ({α, -α} : Set (Fin Tag.E6.rank → ℤ)) ⊆ C := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hαC
    · exact hC.neg_mem α hαC
  have horth : ∀ x ∈ ({α, -α} : Set (Fin Tag.E6.rank → ℤ)), ∀ β ∈ C,
      β ∉ ({α, -α} : Set (Fin Tag.E6.rank → ℤ)) → iform x β = 0 := by
    intro x hx β hβC hβS
    have hβroot : IsRoot Tag.E6 β := hC.isRoot β hβC
    have htri := e6_iform_trichotomy_check α (mem_rootFinset.2 hαroot) β
      (mem_rootFinset.2 hβroot)
    have hβneα : β ≠ α := fun h => hβS (Or.inl h)
    have hβne_negα : β ≠ -α := fun h => hβS (Or.inr h)
    have hαβ : iform α β = 0 := by
      rcases htri ⟨hβneα, hβne_negα⟩ with h0 | h1 | hm1
      · exact h0
      · exfalso
        have hnegβ : -β ∈ C := hC.neg_mem β hβC
        have hneg : iform α (-β) = -1 := by
          rw [← neg_one_smul ℤ β, iform_smul_right, h1]
          ring
        exact absurd hneg (hno α hαC (-β) hnegβ)
      · exact absurd hm1 (hno α hαC β hβC)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hαβ
    · rw [← neg_one_smul ℤ α, iform_smul_left, hαβ]
      ring
  have hS_eq_C : ({α, -α} : Set (Fin Tag.E6.rank → ℤ)) = C := by
    rcases hC.irreducible ({α, -α} : Set (Fin Tag.E6.rank → ℤ)) hSC horth with h | h
    · exfalso
      have hmem : α ∈ ({α, -α} : Set (Fin Tag.E6.rank → ℤ)) :=
        Set.mem_insert α ({-α} : Set (Fin Tag.E6.rank → ℤ))
      rw [h] at hmem
      exact hmem
    · exact h
  have hncard : C.ncard = 2 := by
    rw [← hS_eq_C]
    exact Set.ncard_pair hαne
  refine ⟨?_, hncard⟩
  rw [← hS_eq_C]
  exact e6A1_compRank_pair α hα0

private def e6A2_coeffA : Fin 6 → ℤ := ![1, 0, 1, -1, 0, -1]

private def e6A2_coeffB : Fin 6 → ℤ := ![0, 1, 1, 0, -1, -1]

private def e6A2_g (α β : Fin Tag.E6.rank → ℤ) : Fin 6 → (Fin Tag.E6.rank → ℤ) :=
  fun i => e6A2_coeffA i • α + e6A2_coeffB i • β

private theorem e6A2_iform_alpha_combo
    {α β : Fin Tag.E6.rank → ℤ} (hαα : iform α α = 2) (hαβ : iform α β = -1) (a b : ℤ) :
    iform α (a • α + b • β) = 2 * a - b := by
  rw [iform_add_right, iform_smul_right, iform_smul_right, hαα, hαβ]
  ring

private theorem e6A2_iform_beta_combo
    {α β : Fin Tag.E6.rank → ℤ} (hββ : iform β β = 2) (hαβ : iform α β = -1) (a b : ℤ) :
    iform β (a • α + b • β) = -a + 2 * b := by
  rw [iform_add_right, iform_smul_right, iform_smul_right, iform_comm β α, hαβ, hββ]
  ring

private theorem e6A2_pair_eq_coeff
    {α β : Fin Tag.E6.rank → ℤ} (hαα : iform α α = 2) (hββ : iform β β = 2)
    (hαβ : iform α β = -1) (a b c d : ℤ)
    (h : (iform α (a • α + b • β), iform β (a • α + b • β)) =
      (iform α (c • α + d • β), iform β (c • α + d • β))) : a = c ∧ b = d := by
  have h1 : 2 * a - b = 2 * c - d := by
    have := congrArg Prod.fst h
    rw [e6A2_iform_alpha_combo hαα hαβ a b, e6A2_iform_alpha_combo hαα hαβ c d] at this
    exact this
  have h2 : -a + 2 * b = -c + 2 * d := by
    have := congrArg Prod.snd h
    rw [e6A2_iform_beta_combo hββ hαβ a b, e6A2_iform_beta_combo hββ hαβ c d] at this
    exact this
  omega

private theorem e6A2_g_injective
    {α β : Fin Tag.E6.rank → ℤ} (hαα : iform α α = 2) (hββ : iform β β = 2)
    (hαβ : iform α β = -1) : Function.Injective (e6A2_g α β) := by
  intro i j hij
  have hp : (iform α (e6A2_g α β i), iform β (e6A2_g α β i)) =
      (iform α (e6A2_g α β j), iform β (e6A2_g α β j)) := by
    rw [hij]
  have hpair : (iform α (e6A2_coeffA i • α + e6A2_coeffB i • β),
        iform β (e6A2_coeffA i • α + e6A2_coeffB i • β)) =
      (iform α (e6A2_coeffA j • α + e6A2_coeffB j • β),
        iform β (e6A2_coeffA j • α + e6A2_coeffB j • β)) := by
    simpa only [e6A2_g] using hp
  obtain ⟨ha, hb⟩ := e6A2_pair_eq_coeff hαα hββ hαβ (e6A2_coeffA i) (e6A2_coeffB i)
    (e6A2_coeffA j) (e6A2_coeffB j) hpair
  fin_cases i <;> fin_cases j <;> simp [e6A2_coeffA, e6A2_coeffB] at ha hb ⊢ <;> omega

private theorem e6_component_A2_case
    {C : Set (Fin Tag.E6.rank → ℤ)} (hC : IsRootComponent C)
    (horth : ∀ α ∈ C, ∀ β ∈ C, iform α (latPerm excDiagramSigmaE6 β) = 0)
    (hex : ∃ x ∈ C, ∃ y ∈ C, iform x y = -1) : compRank C = 2 ∧ C.ncard = 6 := by
  classical
  obtain ⟨α, hαC, β, hβC, hαβ⟩ := hex
  have hαR : α ∈ rootFinset Tag.E6 := mem_rootFinset.2 (hC.isRoot α hαC)
  have hβR : β ∈ rootFinset Tag.E6 := mem_rootFinset.2 (hC.isRoot β hβC)
  have hαα : iform α α = 2 := e6_iform_self_check α hαR
  have hββ : iform β β = 2 := e6_iform_self_check β hβR
  have hne_neg : α ≠ -β := by
    intro h
    have h2 : iform α β = -2 := by
      rw [h, ← neg_one_smul ℤ β, iform_smul_left, hββ]
      ring
    omega
  have hαβroot : IsRoot Tag.E6 (α + β) :=
    isRoot_add_of_iform_neg (hC.isRoot α hαC) (hC.isRoot β hβC) hne_neg (by omega)
  have hαβC : α + β ∈ C := hC.add_mem α hαC β hβC hαβroot
  let T : Set (Fin Tag.E6.rank → ℤ) := Set.range (e6A2_g α β)
  have hg0 : e6A2_g α β 0 = α := by simp [e6A2_g, e6A2_coeffA, e6A2_coeffB]
  have hg1 : e6A2_g α β 1 = β := by simp [e6A2_g, e6A2_coeffA, e6A2_coeffB]
  have hg2 : e6A2_g α β 2 = α + β := by simp [e6A2_g, e6A2_coeffA, e6A2_coeffB]
  have hg3 : e6A2_g α β 3 = -α := by simp [e6A2_g, e6A2_coeffA, e6A2_coeffB]
  have hg4 : e6A2_g α β 4 = -β := by simp [e6A2_g, e6A2_coeffA, e6A2_coeffB]
  have hg5 : e6A2_g α β 5 = -(α + β) := by
    simp [e6A2_g, e6A2_coeffA, e6A2_coeffB] <;> abel
  have hαT : α ∈ T := ⟨0, hg0⟩
  have hβT : β ∈ T := ⟨1, hg1⟩
  have hαβT : α + β ∈ T := ⟨2, hg2⟩
  have hnegαT : -α ∈ T := ⟨3, hg3⟩
  have hnegβT : -β ∈ T := ⟨4, hg4⟩
  have hnegαβT : -(α + β) ∈ T := ⟨5, hg5⟩
  have hTC : T ⊆ C := by
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa [hg0] using hαC
    · simpa [hg1] using hβC
    · simpa [hg2] using hαβC
    · simpa [hg3] using hC.neg_mem α hαC
    · simpa [hg4] using hC.neg_mem β hβC
    · simpa [hg5] using hC.neg_mem (α + β) hαβC
  have hTne : T ≠ ∅ := by
    intro h
    have : α ∈ (∅ : Set (Fin Tag.E6.rank → ℤ)) := h ▸ hαT
    exact this
  have hclosed : ∀ x ∈ T, ∀ y ∈ C, y ∉ T → iform x y = 0 := by
    intro x hxT y hyC hyT
    obtain ⟨i, rfl⟩ := hxT
    have hyR : y ∈ rootFinset Tag.E6 := mem_rootFinset.2 (hC.isRoot y hyC)
    have hnotα : y ≠ α := fun h => hyT (by rw [h]; exact hαT)
    have hnotβ : y ≠ β := fun h => hyT (by rw [h]; exact hβT)
    have hnotαβ : y ≠ α + β := fun h => hyT (by rw [h]; exact hαβT)
    have hnotnegα : y ≠ -α := fun h => hyT (by rw [h]; exact hnegαT)
    have hnotnegβ : y ≠ -β := fun h => hyT (by rw [h]; exact hnegβT)
    have hnotnegαβ : y ≠ -(α + β) := fun h => hyT (by rw [h]; exact hnegαβT)
    obtain ⟨hαy, hβy⟩ := e6_sigmaOrth_A2_closed_check α hαR β hβR
      ⟨hαβ, horth α hαC α hαC, horth α hαC β hβC,
        horth β hβC α hαC, horth β hβC β hβC⟩ y hyR
      ⟨hnotα, hnotβ, hnotαβ, hnotnegα, hnotnegβ, hnotnegαβ,
        horth α hαC y hyC, horth β hβC y hyC,
        horth y hyC α hαC, horth y hyC β hβC, horth y hyC y hyC⟩
    have hpos : iform (α + β) y = 0 := by rw [iform_add_left, hαy, hβy, add_zero]
    have hnegαy : iform (-α) y = 0 := by
      rw [← neg_one_smul ℤ α, iform_smul_left, hαy, mul_zero]
    have hnegβy : iform (-β) y = 0 := by
      rw [← neg_one_smul ℤ β, iform_smul_left, hβy, mul_zero]
    have hnegαβy : iform (-(α + β)) y = 0 := by
      rw [← neg_one_smul ℤ (α + β), iform_smul_left, iform_add_left, hαy, hβy, add_zero,
        mul_zero]
    fin_cases i
    · simpa [hg0] using hαy
    · simpa [hg1] using hβy
    · simpa [hg2] using hpos
    · simpa [hg3] using hnegαy
    · simpa [hg4] using hnegβy
    · simpa [hg5] using hnegαβy
  have hTinj : Function.Injective (e6A2_g α β) := e6A2_g_injective hαα hββ hαβ
  have hTncard : T.ncard = 6 := by
    change (Set.range (e6A2_g α β)).ncard = 6
    rw [Set.ncard_range_of_injective hTinj]
    simp
  rcases hC.irreducible T hTC hclosed with hTempty | hTCeq
  · exact absurd hTempty hTne
  · have h6 : C.ncard = 6 := by rw [← hTCeq]; exact hTncard
    exact ⟨compRank_eq_two_of_ncard_eq_six hC h6, h6⟩

theorem e6_rootComponent_orthogonal_sigma
    {C : Set (Fin Tag.E6.rank → ℤ)} (hC : IsRootComponent C) (hne : C.Nonempty)
    (horth : ∀ α ∈ C, ∀ β ∈ C, iform α (latPerm excDiagramSigmaE6 β) = 0) :
    (compRank C = 1 ∧ C.ncard = 2) ∨ (compRank C = 2 ∧ C.ncard = 6) := by
  by_cases hex : ∃ x ∈ C, ∃ y ∈ C, iform x y = -1
  · exact Or.inr (e6_component_A2_case hC horth hex)
  · push Not at hex
    exact Or.inl (e6_component_A1_case hC hne hex)

theorem langOrbitTwo_data
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (π : Equiv.Perm (Fin τ.rank))
    (hπ : ∀ j k, τ.cartan (π j) (π k) = τ.cartan j k) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hne : rationalRoots S.ρ (rootCharHom a) i ≠ componentRoots (rootCharHom a) i) :
    τ = .E6 ∧ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ∧
      ((compRank (componentRoots (rootCharHom a) i) = 1 ∧
          (componentRoots (rootCharHom a) i).ncard = 2) ∨
        (compRank (componentRoots (rootCharHom a) i) = 2 ∧
          (componentRoots (rootCharHom a) i).ncard = 6)) := by
  classical
  have hρρ : ∀ γ, IsRoot τ γ → S.ρ (S.ρ γ) = γ := fun γ hγ =>
    rho_rho_eq_of_latPerm S hτ π hπ hε hρ hγ
  have hC := isRootComponent_componentRoots (χ := rootCharHom a) i
  obtain ⟨-, -, hmin⟩ := outer_componentOrbitLength_spec S hT i
  rcases langOrbit_cases_of_rho_rho S hρρ hT i with ⟨-, h1⟩ | ⟨hlen, j, -, himg, -, hperp⟩
  · exact absurd h1 hne
  ·
    have hπ1 : π ≠ 1 := by
      intro hπ1
      refine hmin 1 one_pos (by omega) ?_
      rw [Function.iterate_one]
      have hρ1 : ∀ γ ∈ componentRoots (rootCharHom a) i,
          S.ρ γ ∈ componentRoots (rootCharHom a) i := by
        intro γ hγ
        have hlat1 : latPerm (1 : Equiv.Perm (Fin τ.rank)) γ = γ := rfl
        rw [hρ γ hγ.1.1, hπ1, hlat1]
        rcases hε with rfl | rfl
        · simpa using hγ
        · simpa using hC.neg_mem γ hγ
      ext δ
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        exact hρ1 γ hγ
      · intro hδ
        exact ⟨S.ρ δ, hρ1 δ hδ, hρρ δ hδ.1.1⟩
    have hE6 : τ = .E6 := by
      rcases hτ with rfl | h | rfl | rfl
      · exact absurd (orbitTwo_perm_eq_one_F4 π hπ) hπ1
      · exact h
      · exact absurd (perm_eq_one_of_cartan_E7 π hπ) hπ1
      · exact absurd (perm_eq_one_of_cartan_E8 π hπ) hπ1
    subst hE6
    have hπσ : π = excDiagramSigmaE6 := by
      rcases perm_eq_one_or_eq_sigma_of_cartan_E6 π hπ with h | h
      · exact absurd h hπ1
      · exact h
    subst hπσ
    refine ⟨rfl, hlen, ?_⟩
    have hne' : (componentRoots (rootCharHom a) i).Nonempty := by
      obtain ⟨b, hb⟩ := Quotient.exists_rep i
      exact ⟨b.1, b.2, hb⟩
    refine e6_rootComponent_orthogonal_sigma hC hne' ?_
    intro α hα γ hγ
    have h1 : S.ρ γ ∈ componentRoots (rootCharHom a) j := by
      rw [← himg]
      exact ⟨γ, hγ, rfl⟩
    have h2 := hperp α hα (S.ρ γ) h1
    rw [hρ γ hγ.1.1, iform_smul_right] at h2
    rcases hε with rfl | rfl <;> simpa using h2

end CFSG.StandardType.LangRat
