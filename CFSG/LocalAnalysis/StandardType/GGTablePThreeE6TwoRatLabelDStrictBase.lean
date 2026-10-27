module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoRatLabelDLeafPerm
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
public import CFSG.RankThree.PartOne.KD4T.Emb
public import CFSG.RankThree.PartOne.KD4T.Inj
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.RankThree.PartOne.KE6.E6LAct
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.StandardParabolic
public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4B
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4D4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section E6TwoRatLabelD

open CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.GLTheoremA.K155X CFSG.RankThree.PartOne.KD4L
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley
  CFSG.RankThree.E6 CFSG.Timmesfeld.LevisSpin CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Tau
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.Yardstones.Md0ec50421ce4

theorem e6TwoRatLabelD_strict_tauDatum
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
    (hf : 1 ≤ f) :
    CFSG.Blueprint.LieModel
      (↥(tauDatum L ℓ f hf).orbitGroup ⧸
        Subgroup.center ↥(tauDatum L ℓ f hf).orbitGroup)
      .POmegaMinus 4 ℓ f := by
  classical
  have h1S : (1 : Fin Tag.E6.rank) ∈ d4Support := by
    change (1 : Fin Tag.E6.rank) ≠ 0 ∧ (1 : Fin Tag.E6.rank) ≠ 5
    decide
  have h2S : (2 : Fin Tag.E6.rank) ∈ d4Support := by
    change (2 : Fin Tag.E6.rank) ≠ 0 ∧ (2 : Fin Tag.E6.rank) ≠ 5
    decide
  have h3S : (3 : Fin Tag.E6.rank) ∈ d4Support := by
    change (3 : Fin Tag.E6.rank) ≠ 0 ∧ (3 : Fin Tag.E6.rank) ≠ 5
    decide
  have h4S : (4 : Fin Tag.E6.rank) ∈ d4Support := by
    change (4 : Fin Tag.E6.rank) ≠ 0 ∧ (4 : Fin Tag.E6.rank) ≠ 5
    decide
  refine lieModel_orbitGroup_of_datum_four (τ := Tag.E6) (Or.inr (Or.inl rfl))
    (tauDatum L ℓ f hf) (m := 4) le_rfl (CompsPTwoDChainO.twoDChainRecog_all hf le_rfl) bTau
    bTau_root bTau_injective iform_bTau (l154r4_tau_simpleRoots hf) ?_ ?_ ?_ ?_
  · intro j hj
    fin_cases j
    · exact (theta_single_tau hf h1S).trans (by rw [gam_one]; rfl)
    · exact (theta_single_tau hf h3S).trans (by rw [gam_three]; rfl)
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
  · exact (theta_single_tau hf h2S).trans (by rw [gam_two]; rfl)
  · exact (theta_single_tau hf h4S).trans (by rw [gam_four]; rfl)
  · intro j k hjk
    fin_cases j <;> fin_cases k <;>
      first
      | (exfalso; revert hjk; decide)
      | exact exists_frame_E6 (by decide)

theorem e6TwoRatLabelD_strict_fixE6_dN
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
    (hf : 1 ≤ f) :
    CFSG.Blueprint.LieModel
      (↥(fixE6 (ℓ := ℓ) f (dN L)) ⧸
        Subgroup.center ↥(fixE6 (ℓ := ℓ) f (dN L)))
      .POmegaMinus 4 ℓ f := by
  rw [fixE6_dN hf]
  exact e6TwoRatLabelD_strict_tauDatum (L := L) (ℓ := ℓ) hf


@[expose] def e6TwoRatLabelD_StrictModel (ℓ f : ℕ) (X : Type) [Group X] : Prop :=
  CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .POmegaMinus 4 ℓ f

@[expose] def e6TwoRatLabelD_StrictSwapLayer (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ i j : Fin τ.rank, i ≠ j → i.val ∈ ({1, 2, 4} : Set ℕ) → j.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      e6TwoRatLabelD_StrictModel ℓ f ↥P

theorem e6TwoRatLabelD_strict_model_mulEquiv {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) {ℓ f : ℕ} (h : e6TwoRatLabelD_StrictModel ℓ f X) :
    e6TwoRatLabelD_StrictModel ℓ f Y := by
  let e' : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
    QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (Subgroup.map_center_eq e)
  exact h.of_mulEquiv e'

theorem e6TwoRatLabelD_strict_model_map_conj {G : Type} [Group G] {ℓ f : ℕ}
    {R : Subgroup G} (φ : G ≃* G) (h : e6TwoRatLabelD_StrictModel ℓ f ↥R) :
    e6TwoRatLabelD_StrictModel ℓ f ↥(R.map φ.toMonoidHom) := by
  exact e6TwoRatLabelD_strict_model_mulEquiv
    (R.equivMapOfInjective φ.toMonoidHom φ.injective) h

theorem e6TwoRatLabelD_strict_exists_fix_swap13
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
    (hf : 1 ≤ f) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 1 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      e6TwoRatLabelD_StrictModel ℓ f ↥(fixE6 (ℓ := ℓ) f n₂) := by
  exact ⟨dN L, acts_dN, E6Fix_dN hf, e6TwoRatLabelD_strict_fixE6_dN (L := L) (ℓ := ℓ) hf⟩

theorem e6TwoRatLabelD_strict_exists_fix_swap03
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
    (hf : 1 ≤ f) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      e6TwoRatLabelD_StrictModel ℓ f ↥(fixE6 (ℓ := ℓ) f n₂) := by
  refine ⟨d4TrialityRep L * dN L * (d4TrialityRep L)⁻¹, ?_, ?_, ?_⟩
  · have h := Acts.conj (acts_d4TrialityRep (L := L)) (acts_dN (L := L))
    rwa [rho_conj_swap] at h
  · exact E6Fix.conj map_conj_d4TrialityRep frob_d4TrialityRep (E6Fix_dN hf)
  · rw [fixE6_conj map_conj_d4TrialityRep frob_d4TrialityRep]
    exact e6TwoRatLabelD_strict_model_map_conj _
      (e6TwoRatLabelD_strict_fixE6_dN (L := L) (ℓ := ℓ) hf)

theorem e6TwoRatLabelD_strict_exists_fix_swap01
    {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
    (hf : 1 ≤ f) :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 1) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      e6TwoRatLabelD_StrictModel ℓ f ↥(fixE6 (ℓ := ℓ) f n₂) := by
  have hR := map_conj_mul (L := L) map_conj_d4TrialityRep map_conj_d4TrialityRep
  have hF : Units.map (entrywiseHom (iterateFrobenius L ℓ f))
      (d4TrialityRep L * d4TrialityRep L) = d4TrialityRep L * d4TrialityRep L := by
    rw [map_mul, frob_d4TrialityRep]
  refine ⟨(d4TrialityRep L * d4TrialityRep L) * dN L *
    (d4TrialityRep L * d4TrialityRep L)⁻¹, ?_, ?_, ?_⟩
  · have h := Acts.conj ((acts_d4TrialityRep (L := L)).mul (acts_d4TrialityRep (L := L)))
      (acts_dN (L := L))
    rwa [rho_sq_conj_swap] at h
  · exact E6Fix.conj hR hF (E6Fix_dN hf)
  · rw [fixE6_conj hR hF]
    exact e6TwoRatLabelD_strict_model_map_conj _
      (e6TwoRatLabelD_strict_fixE6_dN (L := L) (ℓ := ℓ) hf)

theorem e6TwoRatLabelD_strict_model_layer_swap
    {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ]
    {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)} {σ : Equiv.Perm (Fin Tag.D4.rank)}
    {n₂ : ModGL Tag.E6 L} (hstd : StdSwap n₁ π σ) (h₂ : Acts n₂ σ)
    (hRL : e6TwoRatLabelD_StrictModel ℓ f ↥(fixE6 (ℓ := ℓ) f n₂)) {n h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    e6TwoRatLabelD_StrictModel ℓ f ↥P := by
  obtain ⟨eP⟩ := nonempty_equiv_stdLayer hh hlang hP
  exact e6TwoRatLabelD_strict_model_mulEquiv
    (eP.trans (hstd.layerEquiv (ℓ := ℓ) (f := f) h₂)).symm hRL

theorem e6TwoRatLabelD_strict_swapLayer_generic
    {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    (σ : Equiv.Perm (Fin Tag.D4.rank))
    (hE : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ σ ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      e6TwoRatLabelD_StrictModel ℓ f ↥(fixE6 (ℓ := ℓ) f n₂))
    (π : Equiv.Perm (Fin τ.rank)) (hπσ : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (σ k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    e6TwoRatLabelD_StrictModel ℓ f ↥P := by
  obtain ⟨n₂, h₂, -, hRL⟩ := hE
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdSwap n₁ π σ := ⟨hπ, hπ', hπσ, hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact e6TwoRatLabelD_strict_model_layer_swap hstd h₂ hRL hh hlang hP

theorem e6TwoRatLabelD_strict_rootSpan_inf_model_d4_of_layer
    {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {π : Equiv.Perm (Fin τ.rank)}
    (hlayer : ∀ (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f → S.D.q = ℓ ^ f →
      ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α) →
      e6TwoRatLabelD_StrictModel ℓ f ↥(rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ∧ e6TwoRatLabelD_StrictModel (ringChar L) f
      ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hring : ringChar L = ℓ := ringChar.eq L ℓ
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  refine ⟨f, by rw [hring, hq], ?_⟩
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ (d4Nodes τ), IsRoot τ α := fun α hα => hα.1
  rw [l154r4_rootSpan_inf_model_eq S hFr' hΦ hn,
    rootSpan_inf_twistedFixedPoints_smul _ v nw hroots, hring]
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hn'C : nv⁻¹ * nw * nv ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem (canonicalRep_mem_adjointGroup _ L v))
      (canonicalRep_mem_adjointGroup _ L w)) (canonicalRep_mem_adjointGroup _ L v)
  have hπ : weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup τ L) =
        (⟨nv, hnvM⟩ : monomialSubgroup τ L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  have hP := hlayer ℓ f hf hq (nv⁻¹ * nw * nv) hn'M hn'C
    ⟨u, hu, fun α hα => by rw [hπ]; exact hact α hα⟩
  exact e6TwoRatLabelD_strict_model_map_conj (MulAut.conj nv) hP

theorem e6TwoRatLabelD_strict_rootSpan_inf_model_d4_swap
    {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (hL : ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
      ∀ i j : Fin τ.rank, i ≠ j → i.val ∈ ({1, 2, 4} : Set ℕ) → j.val ∈ ({1, 2, 4} : Set ℕ) →
      ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
        (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
          weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) →
        ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
        e6TwoRatLabelD_StrictModel ℓ f ↥P)
    (S : LangSetup τ L p)
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (v : WeylGroup τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Nodes τ)) {i j : Fin τ.rank}
    (hij : i ≠ j) (hi : i.val ∈ ({1, 2, 4} : Set ℕ)) (hj : j.val ∈ ({1, 2, 4} : Set ℕ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice (Equiv.swap i j) α) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ∧ e6TwoRatLabelD_StrictModel (ringChar L) f
      ↥(rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model) := by
  exact e6TwoRatLabelD_strict_rootSpan_inf_model_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf _ n hn hC hex => hL L ℓ f hf i j hij hi hj n hn hC hex _ rfl) hact

end E6TwoRatLabelD

end CFSG.StandardType.TablePThreeKG

end
