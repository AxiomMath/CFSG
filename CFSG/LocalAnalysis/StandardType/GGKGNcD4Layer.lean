module

public import CFSG.LocalAnalysis.StandardType.GGKGNotCDefs
import CFSG.LocalAnalysis.StandardType.GGKGNcD4Cubic

public section

namespace CFSG.StandardType.KG

open CFSG.LocalAnalysis.GLTheoremA.CanonTriL
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4L CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)

open scoped Matrix MatrixGroups

theorem d4TrialityLayerKGNotC_of_leafCycle
    {τ : CFSG.Blueprint.Chevalley.Tag}
    [CFSG.RankThree.PartOne.KD4T.E6Sub τ]
    (hleaf : ∀ (a b c : Fin τ.rank),
      (↑a : ℕ) = 1 ∨ (↑a : ℕ) = 2 ∨ (↑a : ℕ) = 4 →
        (↑b : ℕ) = 1 ∨ (↑b : ℕ) = 2 ∨ (↑b : ℕ) = 4 →
          (↑c : ℕ) = 1 ∨ (↑c : ℕ) = 2 ∨ (↑c : ℕ) = 4 →
            a ≠ b →
              b ≠ c →
                a ≠ c →
                  ((∀ (k : Fin CFSG.Blueprint.Chevalley.Tag.D4.rank),
                        ([a, b, c].formPerm : Fin τ.rank → Fin τ.rank) (CFSG.RankThree.PartOne.KD4T.d4Id k) =
                          CFSG.RankThree.PartOne.KD4T.d4Id (CFSG.RankThree.PartOne.KD4L.rhoE 1 k)) ∨
                      ∀ (k : Fin CFSG.Blueprint.Chevalley.Tag.D4.rank),
                        ([a, b, c].formPerm : Fin τ.rank → Fin τ.rank) (CFSG.RankThree.PartOne.KD4T.d4Id k) =
                          CFSG.RankThree.PartOne.KD4T.d4Id (CFSG.RankThree.PartOne.KD4L.rhoE 2 k)) ∧
                    (∀ (i : Fin τ.rank),
                        1 ≤ (↑i : ℕ) ∧ (↑i : ℕ) ≤ 4 →
                          1 ≤ (↑(([a, b, c].formPerm : Fin τ.rank → Fin τ.rank) i) : ℕ) ∧
                            (↑(([a, b, c].formPerm : Fin τ.rank → Fin τ.rank) i) : ℕ) ≤ 4) ∧
                      ∀ (i : Fin τ.rank),
                        1 ≤ (↑i : ℕ) ∧ (↑i : ℕ) ≤ 4 →
                          1 ≤ (↑((Equiv.symm [a, b, c].formPerm : Fin τ.rank → Fin τ.rank) i) : ℕ) ∧
                            (↑((Equiv.symm [a, b, c].formPerm : Fin τ.rank → Fin τ.rank) i) : ℕ) ≤ 4) :
    CFSG.StandardType.KG.D4TrialityLayerKGNotC τ := by
  intro L _ _ ℓ f _ _ hf a b c hab hbc hac ha hb hc n hn _ hact P hP
  have ha' : a.val = 1 ∨ a.val = 2 ∨ a.val = 4 := by simpa using ha
  have hb' : b.val = 1 ∨ b.val = 2 ∨ b.val = 4 := by simpa using hb
  have hc' : c.val = 1 ∨ c.val = 2 ∨ c.val = 4 := by simpa using hc
  obtain ⟨hcyc, hπ, hπ'⟩ := hleaf a b c ha' hb' hc' hab hbc hac
  rcases hcyc with h1 | h2
  · exact trialityLayerKGNotC_generic hf (List.formPerm [a, b, c]) 1 (Or.inl rfl) h1
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP
  · exact trialityLayerKGNotC_generic hf (List.formPerm [a, b, c]) 2 (Or.inr rfl) h2
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP

theorem d4SwapLayerKGNotC_of_leafSwap
    {τ : CFSG.Blueprint.Chevalley.Tag}
    [CFSG.RankThree.PartOne.KD4T.E6Sub τ]
    (hleaf : ∀ (i j : Fin τ.rank),
      (↑i : ℕ) = 1 ∨ (↑i : ℕ) = 2 ∨ (↑i : ℕ) = 4 →
        (↑j : ℕ) = 1 ∨ (↑j : ℕ) = 2 ∨ (↑j : ℕ) = 4 →
          i ≠ j →
            ((∀ (k : Fin CFSG.Blueprint.Chevalley.Tag.D4.rank),
                  (Equiv.swap i j : Fin τ.rank → Fin τ.rank) (CFSG.RankThree.PartOne.KD4T.d4Id k) =
                    CFSG.RankThree.PartOne.KD4T.d4Id
                      ((Equiv.swap 1 3 :
                          Fin CFSG.Blueprint.Chevalley.Tag.D4.rank → Fin CFSG.Blueprint.Chevalley.Tag.D4.rank)
                        k)) ∨
                (∀ (k : Fin CFSG.Blueprint.Chevalley.Tag.D4.rank),
                    (Equiv.swap i j : Fin τ.rank → Fin τ.rank) (CFSG.RankThree.PartOne.KD4T.d4Id k) =
                      CFSG.RankThree.PartOne.KD4T.d4Id
                        ((Equiv.swap 0 3 :
                            Fin CFSG.Blueprint.Chevalley.Tag.D4.rank → Fin CFSG.Blueprint.Chevalley.Tag.D4.rank)
                          k)) ∨
                  ∀ (k : Fin CFSG.Blueprint.Chevalley.Tag.D4.rank),
                    (Equiv.swap i j : Fin τ.rank → Fin τ.rank) (CFSG.RankThree.PartOne.KD4T.d4Id k) =
                      CFSG.RankThree.PartOne.KD4T.d4Id
                        ((Equiv.swap 0 1 :
                            Fin CFSG.Blueprint.Chevalley.Tag.D4.rank → Fin CFSG.Blueprint.Chevalley.Tag.D4.rank)
                          k)) ∧
              (∀ (x : Fin τ.rank),
                  1 ≤ (↑x : ℕ) ∧ (↑x : ℕ) ≤ 4 →
                    1 ≤ (↑((Equiv.swap i j : Fin τ.rank → Fin τ.rank) x) : ℕ) ∧
                      (↑((Equiv.swap i j : Fin τ.rank → Fin τ.rank) x) : ℕ) ≤ 4) ∧
                ∀ (x : Fin τ.rank),
                  1 ≤ (↑x : ℕ) ∧ (↑x : ℕ) ≤ 4 →
                    1 ≤ (↑((Equiv.symm (Equiv.swap i j) : Fin τ.rank → Fin τ.rank) x) : ℕ) ∧
                      (↑((Equiv.symm (Equiv.swap i j) : Fin τ.rank → Fin τ.rank) x) : ℕ) ≤ 4) :
    CFSG.StandardType.KG.D4SwapLayerKGNotC τ := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn _ hact P hP
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := hleaf i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact swapLayerKGNotC_generic hf (Equiv.swap 1 3) (exists_fix_swap13_kgNotC hf)
      (Equiv.swap i j) h1 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerKGNotC_generic hf (Equiv.swap 0 3) (exists_fix_swap03_kgNotC hf)
      (Equiv.swap i j) h2 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact swapLayerKGNotC_generic hf (Equiv.swap 0 1) (exists_fix_swap01_kgNotC hf)
      (Equiv.swap i j) h3 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP

theorem d4SwapLayerKGNotC_E6 :
    CFSG.StandardType.KG.D4SwapLayerKGNotC CFSG.Blueprint.Chevalley.Tag.E6 :=
  d4SwapLayerKGNotC_of_leafSwap leafSwap_E6

theorem d4SwapLayerKGNotC_E7 :
    CFSG.StandardType.KG.D4SwapLayerKGNotC CFSG.Blueprint.Chevalley.Tag.E7 :=
  d4SwapLayerKGNotC_of_leafSwap leafSwap_E7

theorem d4SwapLayerKGNotC_E8 :
    CFSG.StandardType.KG.D4SwapLayerKGNotC CFSG.Blueprint.Chevalley.Tag.E8 :=
  d4SwapLayerKGNotC_of_leafSwap leafSwap_E8

theorem d4TrialityLayerKGNotC_E6
     :
    CFSG.StandardType.KG.D4TrialityLayerKGNotC CFSG.Blueprint.Chevalley.Tag.E6 :=
  d4TrialityLayerKGNotC_of_leafCycle leafCycle_E6

theorem d4TrialityLayerKGNotC_E7
     :
    CFSG.StandardType.KG.D4TrialityLayerKGNotC CFSG.Blueprint.Chevalley.Tag.E7 :=
  d4TrialityLayerKGNotC_of_leafCycle leafCycle_E7

theorem d4TrialityLayerKGNotC_E8
     :
    CFSG.StandardType.KG.D4TrialityLayerKGNotC CFSG.Blueprint.Chevalley.Tag.E8 :=
  d4TrialityLayerKGNotC_of_leafCycle leafCycle_E8

theorem rootSpan_inf_model_kgNotC_d4_of_layer
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p)
    {Fr : L →+* L}
    (hFr : ∀ (c : L), (Fr : L → L) c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (CFSG.Blueprint.Chevalley.entrywiseHom Fr))
    {w : CFSG.LieType.Chevalley.WeylGroup τ}
    (hn : S.D.n = CFSG.LieType.Chevalley.canonicalRep (CFSG.LieType.Chevalley.coxeterSystem τ) L w)
    (v : CFSG.LieType.Chevalley.WeylGroup τ)
    {u : CFSG.LieType.Chevalley.WeylGroup τ}
    (hu : u ∈ CFSG.LieType.Chevalley.parabolicWeylGroup τ (CFSG.RankThree.PartOne.KE.d4Nodes τ))
    {π : Equiv.Perm (Fin τ.rank)}
    (hlayer : ∀ (ℓ f : ℕ) [inst : Fact (Nat.Prime ℓ)] [inst_1 : CharP L ℓ],
      1 ≤ f →
        S.D.q = ℓ ^ f →
          ∀ (n : CFSG.Blueprint.Chevalley.ModGL τ L)
            (hn :
              Membership.mem (γ := Subgroup (Module.End L (CFSG.Blueprint.Chevalley.RootModule τ L))ˣ)
                (CFSG.LieType.Chevalley.monomialSubgroup τ L) n),
            Membership.mem (γ := Subgroup (CFSG.Blueprint.Chevalley.ModGL τ L)) (CFSG.Blueprint.Chevalley.adjointGroup τ L)
                n →
              (∃ u ∈ CFSG.LieType.Chevalley.parabolicWeylGroup τ (CFSG.RankThree.PartOne.KE.d4Nodes τ),
                  ∀ α ∈ CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ),
                    HSMul.hSMul (α := CFSG.LieType.Chevalley.WeylGroup τ)
                        ((CFSG.LieType.Chevalley.weylQuotientHom τ L :
                              ↥(CFSG.LieType.Chevalley.monomialSubgroup τ L) → CFSG.LieType.Chevalley.WeylGroup τ)
                            (⟨n, hn⟩ : ↥(CFSG.LieType.Chevalley.monomialSubgroup τ L)) :
                          CFSG.LieType.Chevalley.WeylGroup τ)
                        α =
                      u • CFSG.Blueprint.Chevalley.permLattice π α) →
                CFSG.StandardType.KG.KGNotCLieType ℓ
                  ↥(CFSG.Blueprint.Chevalley.rootSpan τ L
                        (CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ)) ⊓
                      CFSG.RankThree.PartOne.KE.twistedFixedPoints n
                        (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom (iterateFrobenius L ℓ f)))))
    (hact : ∀ α ∈ CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ),
      (v⁻¹ * w * v) • α = u • CFSG.Blueprint.Chevalley.permLattice π α) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.Blueprint.Chevalley.rootSpan τ L
            ((fun (α : Fin τ.rank → ℤ) => v • α) ''
              CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ)) ⊓
          S.D.model) := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hring : ringChar L = ℓ := ringChar.eq L ℓ
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ (d4Nodes τ), IsRoot τ α := fun α hα => hα.1
  have hmodel : rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓ S.D.model =
      rootSpan τ L ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints nw (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ, hFr'] at hxF'
      exact hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ, hFr']
      exact hxF
  rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v nw hroots, hring]
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
  exact KGNotCLieType.map_conj (MulAut.conj nv) hP

theorem rootSpan_inf_model_kgNotC_d4_swap
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p : ℕ}
    {Fr : L →+* L}
    (hL : CFSG.StandardType.KG.D4SwapLayerKGNotC τ)
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p)
    (hFr : ∀ (c : L), (Fr : L → L) c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (CFSG.Blueprint.Chevalley.entrywiseHom Fr))
    {w : CFSG.LieType.Chevalley.WeylGroup τ}
    (hn : S.D.n = CFSG.LieType.Chevalley.canonicalRep (CFSG.LieType.Chevalley.coxeterSystem τ) L w)
    (v : CFSG.LieType.Chevalley.WeylGroup τ)
    {u : CFSG.LieType.Chevalley.WeylGroup τ}
    (hu : u ∈ CFSG.LieType.Chevalley.parabolicWeylGroup τ (CFSG.RankThree.PartOne.KE.d4Nodes τ))
    {i : Fin τ.rank}
    {j : Fin τ.rank}
    (hij : i ≠ j)
    (hi : Membership.mem (γ := Set ℕ) {1, 2, 4} (↑i : ℕ))
    (hj : Membership.mem (γ := Set ℕ) {1, 2, 4} (↑j : ℕ))
    (hact : ∀ α ∈ CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ),
      (v⁻¹ * w * v) • α = u • CFSG.Blueprint.Chevalley.permLattice (Equiv.swap i j) α) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.Blueprint.Chevalley.rootSpan τ L
            ((fun (α : Fin τ.rank → ℤ) => v • α) ''
              CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ)) ⊓
          S.D.model) :=
  rootSpan_inf_model_kgNotC_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf _ n hn hC hex => hL L ℓ f hf i j hij hi hj n hn hC hex _ rfl) hact

theorem rootSpan_inf_model_kgNotC_d4
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p : ℕ}
    {Fr : L →+* L}
    (hL : CFSG.StandardType.KG.D4TrialityLayerKGNotC τ)
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p)
    (hFr : ∀ (c : L), (Fr : L → L) c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (CFSG.Blueprint.Chevalley.entrywiseHom Fr))
    {w : CFSG.LieType.Chevalley.WeylGroup τ}
    (hn : S.D.n = CFSG.LieType.Chevalley.canonicalRep (CFSG.LieType.Chevalley.coxeterSystem τ) L w)
    (v : CFSG.LieType.Chevalley.WeylGroup τ)
    {u : CFSG.LieType.Chevalley.WeylGroup τ}
    (hu : u ∈ CFSG.LieType.Chevalley.parabolicWeylGroup τ (CFSG.RankThree.PartOne.KE.d4Nodes τ))
    {a : Fin τ.rank}
    {b : Fin τ.rank}
    {c : Fin τ.rank}
    (hab : a ≠ b)
    (hbc : b ≠ c)
    (hac : a ≠ c)
    (ha : Membership.mem (γ := Set ℕ) {1, 2, 4} (↑a : ℕ))
    (hb : Membership.mem (γ := Set ℕ) {1, 2, 4} (↑b : ℕ))
    (hc : Membership.mem (γ := Set ℕ) {1, 2, 4} (↑c : ℕ))
    (hact : ∀ α ∈ CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ),
      (v⁻¹ * w * v) • α = u • CFSG.Blueprint.Chevalley.permLattice [a, b, c].formPerm α) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.Blueprint.Chevalley.rootSpan τ L
            ((fun (α : Fin τ.rank → ℤ) => v • α) ''
              CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ)) ⊓
          S.D.model) :=
  rootSpan_inf_model_kgNotC_d4_of_layer S hFr hΦ hn v hu
    (fun ℓ f _ _ hf _ n hn hC hex => hL L ℓ f hf a b c hab hbc hac ha hb hc n hn hC hex _ rfl)
    hact

theorem kgNotC_rationalComponent_of_d4_outer
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p : ℕ}
    [CFSG.RankThree.PartOne.KD4T.E6Sub τ]
    (hsearch : CFSG.HardMathSupport.Timmesfeld.LangTorus.D4BaseSearch τ)
    (hL3 : CFSG.RankThree.PartOne.KE.D4TrialityLayer τ)
    (hL2 : CFSG.HardMathSupport.Timmesfeld.CrossChar.D4SwapLayer τ)
    (hR3 : CFSG.StandardType.KG.D4TrialityLayerKGNotC τ)
    (hR2 : CFSG.StandardType.KG.D4SwapLayerKGNotC τ)
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p)
    {Fr : L →+* L}
    (hFr : ∀ (c : L), (Fr : L → L) c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (CFSG.Blueprint.Chevalley.entrywiseHom Fr))
    {w : CFSG.LieType.Chevalley.WeylGroup τ}
    (hn : S.D.n = CFSG.LieType.Chevalley.canonicalRep (CFSG.LieType.Chevalley.coxeterSystem τ) L w)
    (hρw : ∀ (γ : Fin τ.rank → ℤ), CFSG.Blueprint.Chevalley.IsRoot τ γ → (S.ρ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) γ = w • γ)
    {a : Fin τ.rank → Lˣ}
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := τ) (M := Lˣ) (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (v : CFSG.LieType.Chevalley.WeylGroup τ)
    (hΨ : CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i =
      (fun (α : Fin τ.rank → ℤ) => v • α) '' CFSG.LieType.Chevalley.parabolicRoots τ (CFSG.RankThree.PartOne.KE.d4Nodes τ))
    (hρ : ∀ γ ∈ CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i,
      Membership.mem (α := Fin τ.rank → ℤ)
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) γ : Fin τ.rank → ℤ))
    (h1 : ¬CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
        (⇑S.ρ :
            (Fin τ.rank → ℤ) →
              Fin τ.rank →
                ℤ)^[CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
            (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)]) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ, Function.iterate_one] at h1
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Nodes τ), w₀ • α = permLattice π α := fun α hα => by
    have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
    rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) ∧
      KGNotCLieType (ringChar L) ↥(rootSpan τ L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact).2,
        rootSpan_inf_model_kgNotC_d4_swap hR2 S hFr hΦ hn v hu h12 hv1 hv2 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact).2,
        rootSpan_inf_model_kgNotC_d4_swap hR2 S hFr hΦ hn v hu h14 hv1 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact).2,
        rootSpan_inf_model_kgNotC_d4_swap hR2 S hFr hΦ hn v hu h24 hv2 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
        hact).2, rootSpan_inf_model_kgNotC_d4 hR3 S hFr hΦ hn v hu h12 h24
          h14 hv1 hv2 hv4 hact⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
        hact).2, rootSpan_inf_model_kgNotC_d4 hR3 S hFr hΦ hn v hu h14
          h24.symm h12 hv1 hv4 hv2 hact⟩
  rw [rationalComponent_eq_of_layer S i hρ hlayer.1]
  exact hlayer.2

end CFSG.StandardType.KG
