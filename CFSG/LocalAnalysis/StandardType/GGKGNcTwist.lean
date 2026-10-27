module

public import CFSG.LocalAnalysis.StandardType.GGKGNotCDefs
import CFSG.LocalAnalysis.StandardType.GGKGNcD4Cubic

public section

namespace CFSG.StandardType.KG

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open scoped Matrix MatrixGroups

theorem twisted_swap_layer_kgNotC
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {ℓ : ℕ}
    {f : ℕ}
    [Fact (Nat.Prime ℓ)]
    [CharP L ℓ]
    (hf : 1 ≤ f)
    {i : Fin CFSG.Blueprint.Chevalley.TwistTag.E6.tag.rank}
    {j : Fin CFSG.Blueprint.Chevalley.TwistTag.E6.tag.rank}
    (hij : i ≠ j)
    (hi : (↑i : ℕ) = 1 ∨ (↑i : ℕ) = 2 ∨ (↑i : ℕ) = 4)
    (hj : (↑j : ℕ) = 1 ∨ (↑j : ℕ) = 2 ∨ (↑j : ℕ) = 4)
    {n : CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.TwistTag.E6.tag L}
    (hn : Membership.mem (γ :=
      Subgroup (Module.End L (CFSG.Blueprint.Chevalley.RootModule
        CFSG.Blueprint.Chevalley.TwistTag.E6.tag L))ˣ)
      (CFSG.LieType.Chevalley.monomialSubgroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag L) n)
    {u : CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag}
    (hu : Membership.mem (γ := Subgroup (CFSG.LieType.Chevalley.WeylGroup
      CFSG.Blueprint.Chevalley.TwistTag.E6.tag))
      (CFSG.LieType.Chevalley.parabolicWeylGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag
        (CFSG.RankThree.PartOne.KE.d4Nodes CFSG.Blueprint.Chevalley.TwistTag.E6.tag))
      u)
    (hact : ∀ (α : Fin CFSG.Blueprint.Chevalley.TwistTag.E6.tag.rank → ℤ),
      Membership.mem (γ := Set (Fin CFSG.Blueprint.Chevalley.TwistTag.E6.tag.rank → ℤ))
          (CFSG.LieType.Chevalley.parabolicRoots CFSG.Blueprint.Chevalley.TwistTag.E6.tag
            (CFSG.RankThree.PartOne.KE.d4Nodes CFSG.Blueprint.Chevalley.TwistTag.E6.tag))
          α →
        HSMul.hSMul (α := CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag)
            ((CFSG.LieType.Chevalley.weylQuotientHom CFSG.Blueprint.Chevalley.TwistTag.E6.tag L :
                  ↥(CFSG.LieType.Chevalley.monomialSubgroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag
                    L) →
                    CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag)
                (⟨n, hn⟩ : ↥(CFSG.LieType.Chevalley.monomialSubgroup
                  CFSG.Blueprint.Chevalley.TwistTag.E6.tag L)) :
              CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag)
            (CFSG.Blueprint.Chevalley.permLattice CFSG.Blueprint.Chevalley.TwistTag.E6.perm α) =
          u • CFSG.Blueprint.Chevalley.permLattice (Equiv.swap i j) α) :
    CFSG.StandardType.KG.KGNotCLieType ℓ
      ↥(CFSG.Blueprint.Chevalley.rootSpan CFSG.Blueprint.Chevalley.TwistTag.E6.tag L
            (CFSG.LieType.Chevalley.parabolicRoots CFSG.Blueprint.Chevalley.TwistTag.E6.tag
              (CFSG.RankThree.PartOne.KE.d4Nodes CFSG.Blueprint.Chevalley.TwistTag.E6.tag)) ⊓
          CFSG.RankThree.PartOne.KE.twistedFixedPoints
            (n * CFSG.Blueprint.Chevalley.diagramMap CFSG.Blueprint.Chevalley.TwistTag.E6 L)
            (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcases, hπ, hπ'⟩ := leafSwap_E6 i j hi hj hij
  have hact' : ∀ k ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (Equiv.swap i j k) 1 : Fin TwistTag.E6.tag.rank → ℤ) := fun k hk => by
    have := hact _ (single_mem_parabolicRoots hk)
    rw [permLattice_single (Equiv.swap i j)] at this
    exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun x hx => hπ x hx)
    (fun x hx => hπ' x hx) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcases with h1 | h2 | h3
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap13_kgNotC (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 1 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h1, hgen⟩
    exact kgNotC_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap03_kgNotC (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 3) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h2, hgen⟩
    exact kgNotC_layer_swap hstd h₂ hRL hh hlang rfl
  · obtain ⟨n₂, h₂, -, hRL⟩ := exists_fix_swap01_kgNotC (L := L) (ℓ := ℓ) hf
    have hstd : StdSwap n₁ (Equiv.swap i j) (Equiv.swap 0 1) :=
      ⟨fun x hx => hπ x hx, fun x hx => hπ' x hx, h3, hgen⟩
    exact kgNotC_layer_swap hstd h₂ hRL hh hlang rfl

theorem twisted_triality_layer_kgNotC
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {ℓ : ℕ}
    {f : ℕ}
    [Fact (Nat.Prime ℓ)]
    [CharP L ℓ]
    (hf : 1 ≤ f)
    {a : Fin CFSG.Blueprint.Chevalley.TwistTag.E6.tag.rank}
    {b : Fin CFSG.Blueprint.Chevalley.TwistTag.E6.tag.rank}
    {c : Fin CFSG.Blueprint.Chevalley.TwistTag.E6.tag.rank}
    (hab : a ≠ b)
    (hbc : b ≠ c)
    (hac : a ≠ c)
    (ha : (↑a : ℕ) = 1 ∨ (↑a : ℕ) = 2 ∨ (↑a : ℕ) = 4)
    (hb : (↑b : ℕ) = 1 ∨ (↑b : ℕ) = 2 ∨ (↑b : ℕ) = 4)
    (hc : (↑c : ℕ) = 1 ∨ (↑c : ℕ) = 2 ∨ (↑c : ℕ) = 4)
    {n : CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.TwistTag.E6.tag L}
    (hn : Membership.mem (γ :=
      Subgroup (Module.End L (CFSG.Blueprint.Chevalley.RootModule
        CFSG.Blueprint.Chevalley.TwistTag.E6.tag L))ˣ)
      (CFSG.LieType.Chevalley.monomialSubgroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag L) n)
    {u : CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag}
    (hu : Membership.mem (γ := Subgroup (CFSG.LieType.Chevalley.WeylGroup
      CFSG.Blueprint.Chevalley.TwistTag.E6.tag))
      (CFSG.LieType.Chevalley.parabolicWeylGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag
        (CFSG.RankThree.PartOne.KE.d4Nodes CFSG.Blueprint.Chevalley.TwistTag.E6.tag))
      u)
    (hact : ∀ (α : Fin CFSG.Blueprint.Chevalley.TwistTag.E6.tag.rank → ℤ),
      Membership.mem (γ := Set (Fin CFSG.Blueprint.Chevalley.TwistTag.E6.tag.rank → ℤ))
          (CFSG.LieType.Chevalley.parabolicRoots CFSG.Blueprint.Chevalley.TwistTag.E6.tag
            (CFSG.RankThree.PartOne.KE.d4Nodes CFSG.Blueprint.Chevalley.TwistTag.E6.tag))
          α →
        HSMul.hSMul (α := CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag)
            ((CFSG.LieType.Chevalley.weylQuotientHom CFSG.Blueprint.Chevalley.TwistTag.E6.tag L :
                  ↥(CFSG.LieType.Chevalley.monomialSubgroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag
                    L) →
                    CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag)
                (⟨n, hn⟩ : ↥(CFSG.LieType.Chevalley.monomialSubgroup
                  CFSG.Blueprint.Chevalley.TwistTag.E6.tag L)) :
              CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.TwistTag.E6.tag)
            (CFSG.Blueprint.Chevalley.permLattice CFSG.Blueprint.Chevalley.TwistTag.E6.perm α) =
          u • CFSG.Blueprint.Chevalley.permLattice [a, b, c].formPerm α) :
    CFSG.StandardType.KG.KGNotCLieType ℓ
      ↥(CFSG.Blueprint.Chevalley.rootSpan CFSG.Blueprint.Chevalley.TwistTag.E6.tag L
            (CFSG.LieType.Chevalley.parabolicRoots CFSG.Blueprint.Chevalley.TwistTag.E6.tag
              (CFSG.RankThree.PartOne.KE.d4Nodes CFSG.Blueprint.Chevalley.TwistTag.E6.tag)) ⊓
          CFSG.RankThree.PartOne.KE.twistedFixedPoints
            (n * CFSG.Blueprint.Chevalley.diagramMap CFSG.Blueprint.Chevalley.TwistTag.E6 L)
            (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨hcyc, hπ, hπ'⟩ := leafCycle_E6 a b c ha hb hc hab hbc hac
  have hact' : ∀ j ∈ d4Set TwistTag.E6.tag, weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ •
      permLattice TwistTag.E6.perm (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        u • (Pi.single (List.formPerm [a, b, c] j) 1 : Fin TwistTag.E6.tag.rank → ℤ) :=
    fun j hj => by
      have := hact _ (single_mem_parabolicRoots hj)
      rw [permLattice_single (List.formPerm [a, b, c])] at this
      exact this
  obtain ⟨n₁, h, hh, hgen, hlang⟩ := exists_conj_twistedFixed_twist hf hn (fun i hi => hπ i hi)
    (fun i hi => hπ' i hi) hu hact'
  have hd4 : d4Nodes TwistTag.E6.tag = d4Set TwistTag.E6.tag := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  rcases hcyc with h1 | h2
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 1 :=
      ⟨Or.inl rfl, h1, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact kgNotC_layer_triality hf hstd hh hlang rfl
  · have hstd : StdTwist n₁ (List.formPerm [a, b, c]) 2 :=
      ⟨Or.inr rfl, h2, fun i hi => hπ i hi, fun i hi => hπ' i hi, hgen⟩
    exact kgNotC_layer_triality hf hstd hh hlang rfl

theorem kgNotC_rationalComponent_of_d4_twE6_of_layer
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup CFSG.Blueprint.Chevalley.Tag.E6 L p)
    (hS : ∃ (t : CFSG.Blueprint.Chevalley.TwistTag) (h : t.tag = CFSG.Blueprint.Chevalley.Tag.E6)
      (Fr : L →+* L),
      (∀ (c : L), (Fr : L → L) c = c ^ S.D.q) ∧
        ∀ (g : CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.E6 L),
          (S.D.Φ :
                CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.E6 L →
                  CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.E6 L)
              g =
            HMul.hMul (α := CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.E6 L) (β :=
                (Module.End L (CFSG.Blueprint.Chevalley.RootModule CFSG.Blueprint.Chevalley.Tag.E6
                  L))ˣ)
                (CFSG.HardMathSupport.Timmesfeld.LangTorus.diagramAt CFSG.Blueprint.Chevalley.Tag.E6
                  L t h)
                ((Units.map (CFSG.Blueprint.Chevalley.entrywiseHom Fr) :
                      (Module.End L (CFSG.Blueprint.Chevalley.RootModule
                        CFSG.Blueprint.Chevalley.Tag.E6 L))ˣ →
                        (Module.End L (CFSG.Blueprint.Chevalley.RootModule
                          CFSG.Blueprint.Chevalley.Tag.E6 L))ˣ)
                    g :
                  (Module.End L (CFSG.Blueprint.Chevalley.RootModule CFSG.Blueprint.Chevalley.Tag.E6
                    L))ˣ) *
              (CFSG.HardMathSupport.Timmesfeld.LangTorus.diagramAt CFSG.Blueprint.Chevalley.Tag.E6 L
                t h)⁻¹)
    {a : Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → Lˣ}
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := CFSG.Blueprint.Chevalley.Tag.E6) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (v : CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.Tag.E6)
    (hΨ : CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i =
      (fun (α : Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ) => v • α) ''
        CFSG.LieType.Chevalley.parabolicRoots CFSG.Blueprint.Chevalley.Tag.E6
          (CFSG.RankThree.PartOne.KE.d4Nodes CFSG.Blueprint.Chevalley.Tag.E6))
    (hρ : ∀ γ ∈ CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a)
      i,
      Membership.mem (α := Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ)
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
        ((S.ρ : (Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ) → Fin
          CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ) γ :
          Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ))
    (hnin : ¬CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
        (⇑S.ρ : (Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ) → Fin
          CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ))
    (hlay : ∀ (ℓ f : ℕ) [inst : Fact (Nat.Prime ℓ)] [inst_1 : CharP L ℓ],
      1 ≤ f →
        S.D.q = ℓ ^ f →
          ∀ (n : CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.E6 L)
            (hn :
              Membership.mem (γ :=
                Subgroup (Module.End L (CFSG.Blueprint.Chevalley.RootModule
                  CFSG.Blueprint.Chevalley.Tag.E6 L))ˣ)
                (CFSG.LieType.Chevalley.monomialSubgroup CFSG.Blueprint.Chevalley.Tag.E6 L) n),
            ∀
              u ∈
                CFSG.LieType.Chevalley.parabolicWeylGroup CFSG.Blueprint.Chevalley.Tag.E6
                  (CFSG.RankThree.PartOne.KE.d4Nodes CFSG.Blueprint.Chevalley.Tag.E6),
              ∀ (π : Equiv.Perm (Fin CFSG.Blueprint.Chevalley.Tag.E6.rank)),
                CFSG.HardMathSupport.Timmesfeld.LangTorus.IsD4LeafPerm π →
                  π ≠ 1 →
                    (¬CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
                            (CFSG.LieType.Chevalley.componentRoots
                              (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
                            (⇑S.ρ :
                                (Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ) →
                                  Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → ℤ)^[2] →
                        π * π ≠ 1) →
                      (∀
                          α ∈
                            CFSG.LieType.Chevalley.parabolicRoots CFSG.Blueprint.Chevalley.Tag.E6
                              (CFSG.RankThree.PartOne.KE.d4Nodes CFSG.Blueprint.Chevalley.Tag.E6),
                          HSMul.hSMul (α := CFSG.LieType.Chevalley.WeylGroup
                            CFSG.Blueprint.Chevalley.Tag.E6)
                              ((CFSG.LieType.Chevalley.weylQuotientHom
                                CFSG.Blueprint.Chevalley.Tag.E6 L :
                                    ↥(CFSG.LieType.Chevalley.monomialSubgroup
                                      CFSG.Blueprint.Chevalley.Tag.E6 L) →
                                      CFSG.LieType.Chevalley.WeylGroup
                                        CFSG.Blueprint.Chevalley.Tag.E6)
                                  (⟨n, hn⟩ : ↥(CFSG.LieType.Chevalley.monomialSubgroup
                                    CFSG.Blueprint.Chevalley.Tag.E6 L)) :
                                CFSG.LieType.Chevalley.WeylGroup CFSG.Blueprint.Chevalley.Tag.E6)
                              (CFSG.Blueprint.Chevalley.permLattice
                                CFSG.HardMathSupport.Timmesfeld.LangTorus.e6Graph α) =
                            u • CFSG.Blueprint.Chevalley.permLattice π α) →
                        CFSG.IsQuasisimple
                            ↥(CFSG.Blueprint.Chevalley.rootSpan CFSG.Blueprint.Chevalley.Tag.E6 L
                                  (CFSG.LieType.Chevalley.parabolicRoots
                                    CFSG.Blueprint.Chevalley.Tag.E6
                                    (CFSG.RankThree.PartOne.KE.d4Nodes
                                      CFSG.Blueprint.Chevalley.Tag.E6)) ⊓
                                CFSG.RankThree.PartOne.KE.twistedFixedPoints
                                  (n * CFSG.HardMathSupport.Timmesfeld.LangTorus.e6Diagram L)
                                  (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom
                                    (iterateFrobenius L ℓ f)))) ∧
                          CFSG.StandardType.KG.KGNotCLieType ℓ
                            ↥(CFSG.Blueprint.Chevalley.rootSpan CFSG.Blueprint.Chevalley.Tag.E6 L
                                  (CFSG.LieType.Chevalley.parabolicRoots
                                    CFSG.Blueprint.Chevalley.Tag.E6
                                    (CFSG.RankThree.PartOne.KE.d4Nodes
                                      CFSG.Blueprint.Chevalley.Tag.E6)) ⊓
                                CFSG.RankThree.PartOne.KE.twistedFixedPoints
                                  (n * CFSG.HardMathSupport.Timmesfeld.LangTorus.e6Diagram L)
                                  (Units.map (CFSG.Blueprint.Chevalley.entrywiseHom
                                    (iterateFrobenius L ℓ f))))) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ
        (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  classical
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  have hq0 : 0 < S.D.q := by
    rw [hq]
    exact pow_pos hℓ.pos f
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
    intro γ hγ
    have hst : S.D.step = twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
        Fr := by
      ext1 g
      change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
        (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
      rw [hΦ', hn]
    have h2 := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
        rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2
    have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
      IsRoot.smul (hγ.permLattice e6Graph_cartan) w
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3
  have hσσ : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x :=
    fun x => by
      rw [← permLattice_mul, e6Graph_mul_self]
      rfl
  have hσpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    refine ⟨hα.1.permLattice e6Graph_cartan, fun k hk => ?_⟩
    exact hα.2 _ ((e6Graph_on_d4 k).2 hk).1
  set w' : WeylGroup Tag.E6 := v⁻¹ * w * e6WeylTwist v with hw'
  have hθ : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = w' • permLattice e6Graph α := by
    intro α hα
    rw [hρw _ ((isRoot_smul_iff v).2 hα.1), ← e6WeylTwist_smul v α, hw', mul_smul, mul_smul]
  have hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have hmemΨ : v • α ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨α, hα, rfl⟩
    have h2 := hρ _ hmemΨ
    rw [hΨ] at h2
    obtain ⟨β, hβ, hβe⟩ := h2
    rw [← hβe, inv_smul_smul]
    exact hβ
  have hmaps : MapsJ Tag.E6 (d4Set Tag.E6) w' := by
    intro α hα
    have h1 := hθ (permLattice e6Graph α) (hσpar α hα)
    rw [hσσ] at h1
    rw [← h1]
    exact hθmem _ (hσpar α hα)
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  set πJ : Equiv.Perm (Fin Tag.E6.rank) := π' * Equiv.swap (e6Idx 2) (e6Idx 4) with hπJ
  have hπJleaf : IsD4LeafPerm πJ := isD4LeafPerm_mul_swap hπ'
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α := by
    intro α hα
    have h1 := smul_eq_of_simple (w := w₀) (u := 1) (π := π') (J := d4Set Tag.E6)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) (hσpar α hα).2
    rw [one_smul] at h1
    rw [h1, hπJ, permLattice_mul]
    congr 1
    funext k
    simp only [permLattice, Function.comp]
    by_cases hk : 1 ≤ k.val ∧ k.val ≤ 4
    · rw [((e6Graph_on_d4 k).1 hk).2.1]
    · rw [hα.2 _ ((e6Graph_on_d4 k).2 hk).1, hα.2 _ ((e6Graph_on_d4 k).2 hk).2]
  have hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
    intro α hα
    rw [hθ α hα, hw₀, mul_smul, hlin α hα]
  have huJ := mapsJ_of_mem_parabolicWeylGroup hu
  have hπJpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      permLattice πJ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
    intro α hα
    have h1 := hθmem α hα
    rw [hθ' α hα] at h1
    have h2 := (mapsJ_of_mem_parabolicWeylGroup (inv_mem hu)) _ h1
    rwa [inv_smul_smul] at h2
  have hπ1 : πJ ≠ 1 := by
    intro h1
    apply hnin
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ :=
      (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    have h := hθ' α hα
    rw [h1] at h
    calc S.ρ (v • α) = v • (v⁻¹ • S.ρ (v • α)) := (smul_inv_smul v _).symm
      _ = v • (u • α) := by rw [h]; rfl
      _ = (v * u * v⁻¹) • v • α := by rw [mul_smul, mul_smul, inv_smul_smul]
  have hπ2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) → πJ * πJ ≠ 1 := by
    intro hnin2 h2
    apply hnin2
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
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨π' j, hπ'.mem_d4Set hj, ?_⟩
        change simple Tag.E6 (π' j) = w₀ * simple Tag.E6 j * w₀⁻¹
        rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
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
      rw [← permLattice_mul, h2]
      rfl
    calc (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] (v • α) = S.ρ (S.ρ (v • α)) := rfl
      _ = v • (u • permLattice πJ β) := by rw [e1, e2]
      _ = v • (u₂ • α) := by
          rw [hβ, hpx _ (hπJpar α hα), e3, hu₂, mul_smul u (w₀ * e6WeylTwist u * w₀⁻¹) α]
      _ = (v * u₂ * v⁻¹) • v • α := by simp only [mul_smul, inv_smul_smul]
  have hroots : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6), IsRoot Tag.E6 α := fun α hα => hα.1
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  set nδ := canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist v) with hnδ
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hnδM := canonicalRep_mem_monomialSubgroup L (e6WeylTwist v)
  have hn'M : nv⁻¹ * nw * nδ ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnδM
  have hπn' : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ = w' := by
    have e : (⟨nv⁻¹ * nw * nδ, hn'M⟩ : monomialSubgroup Tag.E6 L) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nδ, hnδM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w),
      weylQuotientHom_eq (mapsRootLines_canonicalRep (e6WeylTwist v))]
  have hnPv : nv⁻¹ * (nw * e6Diagram L) * nv = (nv⁻¹ * nw * nδ) * e6Diagram L := by
    have h := e6Diagram_conj_canonicalRep Fr v
    calc nv⁻¹ * (nw * e6Diagram L) * nv =
        nv⁻¹ * nw * (e6Diagram L * nv * (e6Diagram L)⁻¹) * e6Diagram L := by group
      _ = (nv⁻¹ * nw * nδ) * e6Diagram L := by rw [h]
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6),
      weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ • permLattice e6Graph α =
        u • permLattice πJ α := by
    intro α hα
    rw [hπn', hw₀, mul_smul, hlin α hα]
  have hlayer := hlay ℓ f hf hq _ hn'M u hu πJ hπJleaf hπ1 hπ2 hact
  have hmodel : rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
        twistedFixedPoints (nw * e6Diagram L)
          (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hΨ]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ', hFr'] at hxF'
      change (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
        (nw * e6Diagram L)⁻¹ = x
      calc (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (nw * e6Diagram L)⁻¹ = nw * (e6Diagram L *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (e6Diagram L)⁻¹) * nw⁻¹ := by
            group
        _ = x := hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      have hxF' : (nw * e6Diagram L) * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
          (nw * e6Diagram L)⁻¹ = x := hxF
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ', hFr']
      calc nw * (e6Diagram L * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x *
            (e6Diagram L)⁻¹) * nw⁻¹ = (nw * e6Diagram L) *
              Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (nw * e6Diagram L)⁻¹ := by
            group
        _ = x := hxF'
  have hqs : CFSG.IsQuasisimple
        ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) ∧
      KGNotCLieType ℓ ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [hmodel, rootSpan_inf_twistedFixedPoints_smul _ v (nw * e6Diagram L) hroots, ← hnv, hnPv]
    set Q := rootSpan Tag.E6 L (parabolicRoots Tag.E6 (d4Nodes Tag.E6)) ⊓
      twistedFixedPoints ((nv⁻¹ * nw * nδ) * e6Diagram L)
        (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
    have e : Q ≃* Q.map (MulAut.conj nv).toMonoidHom :=
      Q.equivMapOfInjective _ (MulAut.conj nv).injective
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hlayer.1,
      KGNotCLieType.map_conj (MulAut.conj nv) hlayer.2⟩
  rw [rationalComponent_eq_of_layer S i hρ hqs.1, ringChar.eq L ℓ]
  exact hqs.2

end CFSG.StandardType.KG
