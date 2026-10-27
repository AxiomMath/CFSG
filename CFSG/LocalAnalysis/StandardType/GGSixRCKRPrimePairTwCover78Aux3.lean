module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux1

public section

namespace CFSG.StandardType.RCKRP

variable {CoeffField : Type} [Field CoeffField] [IsAlgClosed CoeffField] [CharP CoeffField 2]
attribute [local instance] ZMod.algebra


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T CFSG.LieType.Steinberg.TwistedE6
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

omit [CharP CoeffField 2] in
theorem rckTw78_hρ
    {τ : Tag} [M27Ok τ] [E6Sub τ] {p₀ : ℕ} (S : LangSetup τ CoeffField p₀)
    {a : Fin τ.rank → CoeffFieldˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) :
    ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  have hτ : M27Ok τ := ‹M27Ok τ›
  have h6 : 6 ≤ τ.rank := by rcases hτ.isE7E8 with rfl | rfl <;> decide
  rcases hτ.isE7E8 with rfl | rfl
  · refine S.rho_mem_componentRootsT hT i v hΨ (N := 0) (fun s hs => ?_)
      ⟨({Pi.single 0 1} : Finset (Fin Tag.E7.rank → ℤ)), fun α hα => ?_, by simp⟩
    · have := card_le_of_orth_e6 h6 [] (fun l hl h => absurd h (orth_e6_E7 l hl)) s hs
      simpa using this
    · rw [Finset.mem_singleton.1 hα]
      exact single_mem_parabolicRoots_e6 _ (by decide)
  · refine S.rho_mem_componentRootsT hT i v hΨ (N := 6) (fun s hs => ?_)
      ⟨({Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1,
        Pi.single 5 1, Pi.single 0 1 + Pi.single 2 1} : Finset (Fin Tag.E8.rank → ℤ)),
        fun α hα => ?_, by decide⟩
    · exact (card_le_of_orth_e6 h6 _ orth_e6_E8 s hs).trans (by decide)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hα
      rcases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · refine ⟨isRoot_iff_mem_artifactRoots.2 (by decide), fun j hj => ?_⟩
        have key : ∀ j : Fin 8, ¬ (j.val ≤ 5) →
            ((Pi.single 0 1 + Pi.single 2 1 : Fin 8 → ℤ)) j = 0 := by decide
        exact key j hj

omit [CharP CoeffField 2] in
theorem rckTw78_hπρ
    {τ : Tag} [M27Ok τ] [E6Sub τ] {p₀ : ℕ} (S : LangSetup τ CoeffField p₀)
    {a : Fin τ.rank → CoeffFieldˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) CoeffField w)
    (nv nw : ModGL τ CoeffField) (hnv : nv = canonicalRep (coxeterSystem τ) CoeffField v)
    (hnw : nw = canonicalRep (coxeterSystem τ) CoeffField w)
    (hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup τ CoeffField)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) :
    ∃ (u : WeylGroup τ), u ∈ parabolicWeylGroup τ (e6Set τ) ∧
      ∀ (j : Fin τ.rank) (hj : j ∈ e6Set τ),
        weylQuotientHom τ CoeffField ⟨nv⁻¹ * nw * nv, hn'M⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
          u • (Pi.single (rhoτ τ j) 1 : Fin τ.rank → ℤ) := by
  classical
  have hτ : M27Ok τ := ‹M27Ok τ›
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    rcases hτ.isE7E8 with rfl | rfl
    · exact twistTag_tag_ne_E7
    · exact twistTag_tag_ne_E8
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ' : Ψ = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := hΨ
  have hnvM : nv ∈ monomialSubgroup τ CoeffField := by
    rw [hnv]; exact canonicalRep_mem_monomialSubgroup CoeffField v
  have hnwM : nw ∈ monomialSubgroup τ CoeffField := by
    rw [hnw]; exact canonicalRep_mem_monomialSubgroup CoeffField w
  have hmapv : MapsRootLines nv v := by rw [hnv]; exact mapsRootLines_canonicalRep v
  have hmapw : MapsRootLines nw w := by rw [hnw]; exact mapsRootLines_canonicalRep w
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := by
    intro γ hγ
    rw [← S.rho_eq_smul hτ' hn hγ.1.1]
    exact hρ γ hγ
  have hπ : weylQuotientHom τ CoeffField ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup τ CoeffField) =
        (⟨nv, hnvM⟩ : monomialSubgroup τ CoeffField)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq hmapv, weylQuotientHom_eq hmapw]
  have hmaps : ∀ α ∈ parabolicRoots τ (e6Nodes τ),
      weylQuotientHom τ CoeffField ⟨nv⁻¹ * nw * nv, hn'M⟩ • α ∈ parabolicRoots τ (e6Nodes τ) := by
    intro α hα
    rw [hπ]
    have h1 : w • (v • α) ∈ (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := by
      rw [← hΨ']
      exact hw _ (by rw [hΨ']; exact ⟨α, hα, rfl⟩)
    obtain ⟨β, hβ, hβe⟩ := h1
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  have hwJ : MapsJ τ (e6Set τ) (weylQuotientHom τ CoeffField ⟨nv⁻¹ * nw * nv, hn'M⟩) := by
    intro α hα
    have := hmaps α (by rwa [e6Nodes_eq_e6Set])
    rwa [e6Nodes_eq_e6Set] at this
  obtain ⟨u, hu, π, hπ12, hact⟩ := exists_action hwJ
  rcases hπ12 with h1 | h1
  · exfalso
    apply hout
    subst h1
    set g : WeylGroup τ := v * u * v⁻¹ with hg
    have hgcl : g ∈ Subgroup.closure
        {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} := by
      have hu2 : u ∈ parabolicWeylGroup τ (e6Nodes τ) := by
        rw [e6Nodes_eq_e6Set]
        exact hu
      exact conj_parabolicWeyl_mem_closure v hΨ' hu2
    have hact1 : ∀ γ ∈ Ψ, S.ρ γ = g • γ := by
      intro γ hγ
      have hγ' := hγ
      rw [hΨ'] at hγ'
      obtain ⟨α, hα, rfl⟩ := hγ'
      have hαJ : ∀ k, k ∉ e6Set τ → α k = 0 := by
        intro k hk
        exact hα.2 k (by rwa [e6Nodes_eq_e6Set])
      have hwα : (v⁻¹ * w * v) • α = u • α := by
        have hα_eq : α = ∑ j ∈ (Finset.univ.filter fun j => j ∈ e6Set τ),
            α j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
          funext k
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          by_cases hk : k ∈ e6Set τ
          · rw [Finset.sum_eq_single k]
            · simp
            · intro b hb hbk
              simp [Pi.single_apply, Ne.symm hbk]
            · intro hk'
              exact absurd (by simpa using hk) hk'
          · rw [hαJ k hk, Finset.sum_eq_zero]
            intro b hb
            have hbk : k ≠ b := fun h => hk (h ▸ (Finset.mem_filter.1 hb).2)
            simp [Pi.single_apply, hbk]
        rw [hα_eq, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjJ : j ∈ e6Set τ := (Finset.mem_filter.1 hj).2
        rw [smul_comm (v⁻¹ * w * v) (α j) _, smul_comm u (α j) _, ← hπ, hact j hjJ]
        rfl
      have hρw : S.ρ (v • α) = w • (v • α) :=
        S.rho_eq_smul hτ' hn (IsRoot.smul hα.1 v)
      have : w • (v • α) = v • ((v⁻¹ * w * v) • α) := by
        rw [mul_smul, mul_smul, smul_inv_smul]
      show S.ρ (v • α) = g • (v • α)
      rw [hρw, this, hwα, hg, mul_smul, mul_smul, inv_smul_smul]
    have hsts : ∀ γ ∈ Ψ, g • γ ∈ Ψ := fun γ hγ => by
      rw [← hact1 γ hγ]
      exact hρ γ hγ
    refine ⟨g ^ componentOrbitLength S.ρ Ψ, Subgroup.pow_mem _ hgcl _, ?_⟩
    have key : ∀ n : ℕ, ∀ γ ∈ Ψ, (S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ = (g ^ n) • γ ∧
        (g ^ n) • γ ∈ Ψ := by
      intro n
      induction n with
      | zero => exact fun γ hγ => ⟨by simp, by simpa using hγ⟩
      | succ n ih =>
        intro γ hγ
        obtain ⟨h1, h2⟩ := ih γ hγ
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_succ_apply', h1, hact1 _ h2, ← mul_smul, ← pow_succ']
        · rw [pow_succ', mul_smul]
          exact hsts _ h2
    exact fun γ hγ => (key _ γ hγ).1
  · subst h1
    exact ⟨u, hu, hact⟩

end CFSG.StandardType.RCKRP

end
