module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoRatLabelDStrict
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.RankThree.PartOne.KE6 CFSG.LocalAnalysis.GLTheoremA.K155X

private theorem twE6_triality_layer_model
    {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    {a b c : Fin Tag.E6.rank} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 4)
    (hb : b.val = 1 ∨ b.val = 2 ∨ b.val = 4)
    (hc : c.val = 1 ∨ c.val = 2 ∨ c.val = 4)
    {n : ModGL Tag.E6 L} (hn : n ∈ monomialSubgroup Tag.E6 L)
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    (hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨n, hn⟩ • permLattice e6Graph α =
        u • permLattice (List.formPerm [a, b, c]) α) :
    LieModel (↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) ⧸
      Subgroup.center ↥(rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (n * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) .trialityD4 0 ℓ f := by
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E6 a b c ha hb hc hab hbc hac
  have hact' : ∀ j ∈ d4Set Tag.E6, weylQuotientHom Tag.E6 L ⟨n, hn⟩ •
      permLattice e6Graph (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
        u • (Pi.single (List.formPerm [a, b, c] j) 1 : Fin Tag.E6.rank → ℤ) :=
    fun j hj => by
      have := hact _ (single_mem_parabolicRoots hj)
      rw [permLattice_single (List.formPerm [a, b, c])] at this
      exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun i hi => hπ i hi)
    (fun i hi => hπ' i hi) hu hact'
  have hd4 : d4Nodes Tag.E6 = d4Set Tag.E6 := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcyc with h1 | h2
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 1 :=
      ⟨Or.inl rfl, h1, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact CFSG.StandardType.TablePThreeKG.lieModel_model_layer_triality hf hstd hh hlang rfl
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 2 :=
      ⟨Or.inr rfl, h2, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact CFSG.StandardType.TablePThreeKG.lieModel_model_layer_triality hf hstd hh hlang rfl

private theorem twE6_pi_sq
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]))
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6))
    {w₀ : WeylGroup Tag.E6} {πJ : Equiv.Perm (Fin Tag.E6.rank)}
    (hleaf : IsD4LeafPerm πJ)
    (hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α)
    (hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α) :
    πJ * πJ ≠ 1 := by
  intro hππ
  apply hnin2
  have hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) :=
    fun α hα => l154td4_theta_mem S i v hΨ hρ hα
  have huJ := mapsJ_of_mem_parabolicWeylGroup hu
  have hπJpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice πJ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have h1 := hθmem α hα
    rw [hθ' α hα] at h1
    have h2 := (mapsJ_of_mem_parabolicWeylGroup (inv_mem hu)) _ h1
    rwa [inv_smul_smul] at h2
  have hδu : e6WeylTwist u ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
    have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map e6WeylTwist.toMonoidHom ≤
        parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨e6Graph j, ((e6Graph_on_d4 j).1 hj).2.2, ?_⟩
      exact (e6WeylTwist_simple j).symm
    exact hle ⟨u, hu, rfl⟩
  have hconj : w₀ * e6WeylTwist u * w₀⁻¹ ∈ parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
    have hle : (parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6)).map (MulAut.conj w₀).toMonoidHom ≤
        parabolicWeylGroup Tag.E6 (d4Nodes Tag.E6) := by
      rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have hinv : ∀ x : Fin Tag.E6.rank, e6Graph.symm x = e6Graph x := by
        intro x
        have hfun : ∀ y, e6Graph (e6Graph y) = y := by
          intro y
          have h := congr_fun (congrArg (fun f : Equiv.Perm (Fin Tag.E6.rank) => (f : _ → _))
            e6Graph_mul_self) y
          simpa [Equiv.Perm.mul_apply] using h
        apply e6Graph.injective
        rw [Equiv.apply_symm_apply, hfun]
      have hk' : e6Graph.symm k ∈ d4Nodes Tag.E6 := by
        rw [hinv k]
        exact ((e6Graph_on_d4 k).1 hk).2.2
      have hsingle := hlin (Pi.single (e6Graph.symm k) 1)
        (single_mem_parabolicRoots hk')
      rw [permLattice_single e6Graph, Equiv.apply_symm_apply, permLattice_single πJ] at hsingle
      refine Subgroup.subset_closure ⟨πJ (e6Graph.symm k), hleaf.mem_d4Set hk', ?_⟩
      change simple Tag.E6 (πJ (e6Graph.symm k)) = w₀ * simple Tag.E6 k * w₀⁻¹
      rw [← rootReflection_single (πJ (e6Graph.symm k)),
        ← rootReflection_eq_conj (j := k) hsingle]
    exact hle ⟨e6WeylTwist u, hδu, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ x, x = u * (w₀ * e6WeylTwist u * w₀⁻¹) := ⟨_, rfl⟩
  refine ⟨v * u₂ * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v (hu₂ ▸ mul_mem hu hconj), ?_⟩
  rintro γ hγ
  obtain ⟨α, hα, rfl⟩ :=
    (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
  have hpx : ∀ x ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), permLattice πJ (u • x) =
      (w₀ * e6WeylTwist u * w₀⁻¹) • permLattice πJ x := by
    intro x hx
    rw [← hlin _ (huJ x hx), ← hlin x hx, ← e6WeylTwist_smul u x, mul_smul, mul_smul,
      inv_smul_smul]
  set β := u • permLattice πJ α with hβ
  have hβJ : β ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    rw [hβ, ← hθ' α hα]
    exact hθmem α hα
  have e1 : S.ρ (v • α) = v • β := by
    rw [hβ, ← hθ' α hα, smul_inv_smul]
  have e2 : S.ρ (v • β) = v • (u • permLattice πJ β) := by
    rw [← hθ' β hβJ, smul_inv_smul]
  have e3 : permLattice πJ (permLattice πJ α) = α := by
    rw [← permLattice_mul, hππ]
    rfl
  calc (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] (v • α) = S.ρ (S.ρ (v • α)) := rfl
    _ = v • (u • permLattice πJ β) := by rw [e1, e2]
    _ = v • (u₂ • α) := by
        rw [hβ, hpx _ (hπJpar α hα), e3, hu₂,
          mul_smul u (w₀ * e6WeylTwist u * w₀⁻¹) α]
    _ = (v * u₂ * v⁻¹) • v • α := by simp only [mul_smul, inv_smul_smul]

theorem lieModel_rationalComponent_of_d4_twE6_triality
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E6 L p)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (hnin2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2])) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .trialityD4 0
        (ringChar L) f := by
  classical
  obtain ⟨w, hn, hρw⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.d4t2out_rho_eq S hS
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  obtain ⟨u, hu, w₀, hw₀, πJ, hleaf, hlin, hθ'⟩ := l154r4_tw_action S hρw i v hΨ hρ
  have hπ1 : πJ ≠ 1 := l154r4_tw_pi_ne_one S i v hΨ hnin hu hθ'
  have hπ2 : πJ * πJ ≠ 1 :=
    twE6_pi_sq S i v hΨ hρ hnin2 hu hleaf hlin hθ'
  obtain ⟨n', hn', hact, g, heq⟩ := l154r4_tw_layer_eq S hFr' hΦ' hn i v hΨ hw₀ hlin
  have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
      (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
  have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
      (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
      (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
  set Q := rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
    twistedFixedPoints (n' * e6Diagram L)
      (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) with hQ
  have hqsQ : CFSG.IsQuasisimple ↥Q := by
    rcases hleaf.eq_cycle hπ1 hπ2 with hc | hc
    · rw [hc] at hact
      exact (twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn' hu hact).2
    · rw [hc] at hact
      exact (twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn' hu hact).2
  have hmodelQ : LieModel (↥Q ⧸ Subgroup.center ↥Q) .trialityD4 0 ℓ f := by
    rcases hleaf.eq_cycle hπ1 hπ2 with hc | hc
    · rw [hc] at hact
      exact twE6_triality_layer_model hf h12 h24 h14 hv1 hv2 hv4 hn' hu hact
    · rw [hc] at hact
      exact twE6_triality_layer_model hf h14 h24.symm h12 hv1 hv4 hv2 hn' hu hact
  have e : Q ≃* Q.map (MulAut.conj g).toMonoidHom :=
    Q.equivMapOfInjective _ (MulAut.conj g).injective
  have hqs : CFSG.IsQuasisimple
      ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [heq]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqsQ
  refine ⟨f, by rw [ringChar.eq L ℓ, hq], ?_⟩
  rw [rationalComponent_eq_of_layer S i hρ hqs, heq, ringChar.eq L ℓ]
  exact CFSG.StandardType.TablePThreeKG.lieModel_triD4_map_conj (MulAut.conj g) hmodelQ


end CFSG.StandardType.TableCRes

end
