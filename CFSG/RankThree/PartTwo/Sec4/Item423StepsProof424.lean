module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofInnerBack
public import CFSG.RankThree.PartTwo.Sec4.Item47WStatement
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

section Statements

@[expose] def Item4_24M : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G,
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    partTwoE G = partTwoF G →
    ∀ L ∈ thetaComponents 3 G, ∀ a : G, orderOf a = 3 → a ∈ Subgroup.center G →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers a : Set G) →
    ∀ c ∈ A, c ∉ Subgroup.zpowers a →
    ∀ K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)),
      ((∃ n : ℕ, 1 ≤ n ∧
          Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 2 (GaloisField 2 n))) ∨
        (∃ (p n : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ n ∧
          Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 2 (GaloisField p n))) ∨
        ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi (K ⧸ aschbacherSolvableCore 3 K) 2 n) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) →
        (KFacts.InducesStdKind L c .field ∧ Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))) ∨
        (((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
              Nonempty (thetaImage (L ⊔ A) ≃* Multiplicative (ZMod 3) ×
                (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
            ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
              Nonempty (thetaImage (L ⊔ A) ≃* Multiplicative (ZMod 3) ×
                (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
          Nonempty (autIn L A ≃* DihedralGroup 6)) ∨
        ((Sec8.IsZ3LThreePi (thetaImage (L ⊔ A)) ∨ Sec8.IsZ3PGLThreePi (thetaImage (L ⊔ A))) ∧
          Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))) ∨
        ((Nonempty (thetaImage (L ⊔ A) ≃*
              Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M24) ∨
            Nonempty (thetaImage (L ⊔ A) ≃*
              Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.He)) ∧
          Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 3 (GaloisField 2 1)) ∧
          Nonempty (autIn L A ≃* DihedralGroup 6))

end Statements

@[expose] def Census424Full (X : Type) [Group X] [Finite X] : Prop :=
  ∀ (D : Subgroup X) (c d : X) (K : Subgroup X), InnerConfig424 X D c d K →
    (((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
          Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
        ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
          Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
      Nonempty (autIn (⊤ : Subgroup X) D ≃* DihedralGroup 6)) ∨
    ((Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.He)) ∧
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 3 (GaloisField 2 1)) ∧
      Nonempty (autIn (⊤ : Subgroup X) D ≃* DihedralGroup 6))

@[expose] def K424InnerFull : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46 X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census424Full X

@[expose] def Item424Full.prodCongrRightMul {M N N' : Type*} [Mul M] [Mul N] [Mul N']
    (e : N ≃* N') : M × N ≃* M × N' :=
  { (Equiv.refl M).prodCongr e.toEquiv with
    map_mul' := fun x y => Prod.ext rfl (map_mul e x.2 y.2) }

namespace Config424

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {a c : G} {K : Subgroup G}

theorem conclusionFull (h45 : Item4_5) (h46 : Item4_6) (h47 : Item4_7W) (hF : K424FieldCent)
    (hD4 : K424TrialityOuter) (hCov : K424CoverCent) (hSL : K424SLThree)
    (hIn : K424InnerFull) (h : Config424 G A L a c K) :
    (KFacts.InducesStdKind L c .field ∧ Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))) ∨
      (((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
            Nonempty (thetaImage (L ⊔ A) ≃* Multiplicative (ZMod 3) ×
              (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
          ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
            Nonempty (thetaImage (L ⊔ A) ≃* Multiplicative (ZMod 3) ×
              (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
        Nonempty (autIn L A ≃* DihedralGroup 6)) ∨
      ((Sec8.IsZ3LThreePi (thetaImage (L ⊔ A)) ∨ Sec8.IsZ3PGLThreePi (thetaImage (L ⊔ A))) ∧
        Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))) ∨
      ((Nonempty (thetaImage (L ⊔ A) ≃*
            Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M24) ∨
          Nonempty (thetaImage (L ⊔ A) ≃*
            Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.He)) ∧
        Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 3 (GaloisField 2 1)) ∧
        Nonempty (autIn L A ≃* DihedralGroup 6)) := by
  have hAN := h.le_normalizer h45
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hAN h.c_mem
  have hc3 : c ^ 3 = 1 := h.pow_three c h.c_mem
  have h3 : 3 ∣ Nat.card (Subgroup.center G) := by
    rw [← h.orderOf_a]
    exact Subgroup.orderOf_dvd_natCard _ h.a_mem_center
  have hL46 : IsList46 (L ⧸ aschbacherSolvableCore 3 L) :=
    h46 G h.sectionFourHyp h3 L h.mem_thetaComponents
  by_cases hout : InducesOuterTheta c L
  ·
    rcases h47 G h.sectionFourHyp h3 L h.mem_thetaComponents c h.orderOf_c hout with
      ⟨-, -, -, -, -, -, hkind⟩ | ⟨p, e, hp, -, he, -, hSL', hdiag⟩ | ⟨-, hkind⟩ |
      ⟨n, hn, hSL', hdiag⟩ | ⟨n, -, hD⟩
    · exact Or.inl ⟨hkind, h.autIn_field h45 hF hkind⟩
    · have hany : IsSLThreePiAny (L ⧸ aschbacherSolvableCore 3 L) := by
        rcases hSL' with h1 | h1
        · exact Or.inl ⟨_, h1⟩
        · exact Or.inr ⟨p, e, hp, he, h1⟩
      obtain ⟨hS3, hT⟩ := hSL G A L a c K h hany (Or.inr hdiag)
      exact Or.inr (Or.inr (Or.inl ⟨hT, hS3⟩))
    · exact Or.inl ⟨hkind, h.autIn_field h45 hF hkind⟩
    · have hany : IsSLThreePiAny (L ⧸ aschbacherSolvableCore 3 L) := by
        rcases hSL' with h1 | h1
        · exact Or.inl ⟨_, h1⟩
        · exact Or.inr ⟨2, n, ⟨Nat.prime_two⟩, hn, h1⟩
      obtain ⟨hS3, hT⟩ := hSL G A L a c K h hany (Or.inr hdiag)
      exact Or.inr (Or.inr (Or.inl ⟨hT, hS3⟩))
    · exact absurd h.isType424 (hD4 G L K c n hD hout hc3 h.mem_thetaComponentsIn)
  ·
    by_cases hany : IsSLThreePiAny (L ⧸ aschbacherSolvableCore 3 L)
    · obtain ⟨hS3, hT⟩ := hSL G A L a c K h hany (Or.inl hout)
      exact Or.inr (Or.inr (Or.inl ⟨hT, hS3⟩))
    by_cases hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥
    · obtain ⟨c₀, d, i, hci, hdK, -, hc₀A, hc₀L, hc₀1, hdc₀, hAL, h9, hA⟩ :=
        h.inner_structure h45 hZ hout
      have hdAK : d ∈ A ⊓ K := by rw [hdK]; exact Subgroup.mem_zpowers d
      have hdL : d ∈ L := h.K_le_L hdAK.2
      have hcfg := h.innerConfig hci hdK hc₀A hc₀L hc₀1 hdc₀ hAL h9 hA hdL
      obtain ⟨eA⟩ := h.nonempty_autIn_equiv hA ⟨hc₀A, hc₀L⟩ ⟨hdAK.1, hdL⟩
      obtain ⟨eT⟩ := h.nonempty_thetaImage_equiv hZ hA ⟨hc₀A, hc₀L⟩ ⟨hdAK.1, hdL⟩
      obtain ⟨-, ⟨eK⟩⟩ := h.imageModTheta_K_facts hci hc₀L (h.pow_three c₀ hc₀A)
      rcases hIn _ hL46 h.isQuasisimple_L hZ hany _ _ _ _ hcfg with
        ⟨hX, ⟨eD⟩⟩ | ⟨hX, ⟨eKb⟩, ⟨eD⟩⟩
      · refine Or.inr (Or.inl ⟨?_, ⟨eA.trans eD⟩⟩)
        rcases hX with ⟨q, hq, ⟨e⟩⟩ | ⟨q, hq, ⟨e⟩⟩
        · exact Or.inl ⟨q, hq, ⟨eT.trans (Item424Full.prodCongrRightMul e)⟩⟩
        · exact Or.inr ⟨q, hq, ⟨eT.trans (Item424Full.prodCongrRightMul e)⟩⟩
      · refine Or.inr (Or.inr (Or.inr ⟨?_, ⟨eK.symm.trans eKb⟩, ⟨eA.trans eD⟩⟩))
        rcases hX with he | he
        · obtain ⟨e⟩ := he
          exact Or.inl ⟨eT.trans (Item424Full.prodCongrRightMul e)⟩
        · obtain ⟨e⟩ := he
          exact Or.inr ⟨eT.trans (Item424Full.prodCongrRightMul e)⟩
    · exfalso
      have hcT : c ∉ thetaQuotCentralizer L := by
        intro hcT
        have hmem : c ∈ A ⊓ thetaQuotCentralizer L := ⟨h.c_mem, hcT⟩
        rw [h.inf_thetaQuotCentralizer hAN] at hmem
        exact h.c_not_mem hmem
      exact hCov G L K c hL46 h.isQuasisimple_L hZ (fun h' => hany (Or.inl h')) hcN hc3 hout hcT
        h.mem_thetaComponentsIn h.isType424

end Config424

section Main

theorem item4_24M_of (h45 : Item4_5) (h46 : Item4_6) (h47 : Item4_7W) (hF : K424FieldCent)
    (hD4 : K424TrialityOuter) (hCov : K424CoverCent) (hSL : K424SLThree)
    (hIn : K424InnerFull) : Item4_24M :=
  fun _ _ _ hG _ hAmax hA27 _ _ hL _ ha3 haZ hCA _ hcA hca _ hK hKT hN =>
    Config424.conclusionFull h45 h46 h47 hF hD4 hCov hSL hIn
      ⟨hG, hAmax, hA27, hL, ha3, haZ, hCA, hcA, hca, hK, hKT, hN⟩

end Main

end CFSG.RankThree.PartTwo.Sec4
