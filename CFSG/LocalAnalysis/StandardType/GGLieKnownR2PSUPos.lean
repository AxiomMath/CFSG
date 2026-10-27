module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUForms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUCores
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSUBounds
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLPos
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUModel
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.LeviAssembly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpModel
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadicalSmall
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympTypes
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.C31Steps
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.GoldschmidtS146RArith2
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.EmptyFaithful.R3c20A
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S151YC
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.SBc5Aut
public import CFSG.Quasithin.EmptyFaithful.SzN17Abs
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31Blk
public import CFSG.Quasithin.Vol2.KGFactC31HSCases
public import CFSG.Quasithin.Vol2.KGFactC31HSMod
public import CFSG.Quasithin.Vol2.KGFactC31Hat
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

namespace CFSG.StandardType.LieKnownR2.PSU

private theorem l10sdsu_subsingleton_SU {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}
    (hm : m ≤ 1) : Subsingleton (Unitary.SU σ m) := by
  have hm0 : m = 0 ∨ m = 1 := by omega
  rcases hm0 with rfl | rfl
  · haveI : Subsingleton (Matrix (Fin 0) (Fin 0) F) :=
      ⟨fun _ _ => funext fun i => Fin.elim0 i⟩
    haveI : Subsingleton (GL (Fin 0) F) :=
      ⟨fun A B => Units.ext (Subsingleton.elim (A : Matrix (Fin 0) (Fin 0) F)
        (B : Matrix (Fin 0) (Fin 0) F))⟩
    exact ⟨fun A B => Subtype.ext (Subsingleton.elim A.1 B.1)⟩
  · refine ⟨fun A B => ?_⟩
    apply CFSG.LieType.Universal.Unitary.SUExtras.mat_injective
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    rw [hi, hj]
    have hA : (A.1 : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
      have h := A.2.1
      rwa [Matrix.det_fin_one] at h
    have hB : (B.1 : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
      have h := B.2.1
      rwa [Matrix.det_fin_one] at h
    simp only [CFSG.LieType.Universal.Unitary.SUExtras.mat_apply]
    rw [hA, hB]

@[expose] def GGSixPSUPosExplicit :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSU n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X),
    CFSG.StandardType.ClassicalPosition.GGSixPosHyp .PSU n f ψ p G₀ B₁ D J L x →
  ∃ (R Rm : Subgroup X),
        R ≤ J ∧ Rm ≤ J ∧ 1 ≤ f ∧
        ((∃ (mJ : ℕ) (βJ : Fin (ggU .PSU mJ f).D.rank → ℤ), mJ < n ∧
            βJ ∈ (ggU .PSU mJ f).D.roots ∧ GGLongRoot (ggU .PSU mJ f).D βJ ∧
            GGRootVia (ggU .PSU mJ f) J R βJ ∧
            (∃ β : Fin (ggU .PSU n f).D.rank → ℤ, β ∈ (ggU .PSU n f).D.roots ∧
              GGLongRoot (ggU .PSU n f).D β ∧ ∃ u : (ggU .PSU n f).K,
                R = ggRootSub (ggU .PSU n f).D ψ β u ∧ Rm = ggRootSub (ggU .PSU n f).D ψ (-β) u) ∧
            ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
              CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
              Odd (Nat.card (Subgroup.center ↥K)) →
              ∃ (mK : ℕ) (βK : Fin (ggU .PSU mK f).D.rank → ℤ), mJ < mK ∧
                βK ∈ (ggU .PSU mK f).D.roots ∧ GGLongRoot (ggU .PSU mK f).D βK ∧
                GGRootVia (ggU .PSU mK f) K R βK) ∨
          (∃ (kJ : ℕ) (φJ : (ggU .PSL (kJ + 1) (2 * f)).K →* X)
              (βJ : Fin (ggU .PSL (kJ + 1) (2 * f)).D.rank → ℤ), 2 * (kJ + 1) ≤ n ∧
            βJ ∈ (ggU .PSL (kJ + 1) (2 * f)).D.roots ∧
            φJ.range = J ∧ φJ.ker ≤ Subgroup.center (ggU .PSL (kJ + 1) (2 * f)).K ∧
            (∃ u : (ggU .PSL (kJ + 1) (2 * f)).K,
              R = ggRootSub (ggU .PSL (kJ + 1) (2 * f)).D φJ βJ u) ∧
            (∀ b ∈ B₁, ∃ s : GL (Fin (kJ + 1)) (GaloisField 2 (2 * f)),
              IsGLLift Matrix.SpecialLinearGroup.toGL φJ s b) ∧
            p ∣ 2 ^ f - 1 ∧
            (∃ β : Fin (ggU .PSU n f).D.rank → ℤ, β ∈ (ggU .PSU n f).D.roots ∧
              2 • β ∉ (ggU .PSU n f).D.roots ∧ ∃ u : (ggU .PSU n f).K,
                R = ggRootSub (ggU .PSU n f).D ψ β u ∧ Rm = ggRootSub (ggU .PSU n f).D ψ (-β) u) ∧
            ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
              CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
              Odd (Nat.card (Subgroup.center ↥K)) →
              (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) (2 * f)).D.rank → ℤ), kJ < kK ∧
                βK ∈ (ggU .PSL (kK + 1) (2 * f)).D.roots ∧
                GGRootVia (ggU .PSL (kK + 1) (2 * f)) K R βK) ∨
              (∃ (mK : ℕ) (βK : Fin (ggU .PSU mK f).D.rank → ℤ), 2 * (kJ + 1) ≤ mK ∧
                βK ∈ (ggU .PSU mK f).D.roots ∧
                (GGLongRoot (ggU .PSU mK f).D βK ∨ 2 • βK ∉ (ggU .PSU mK f).D.roots) ∧
                GGRootVia (ggU .PSU mK f) K R βK)))

theorem jDim_selfDual_psu
    {m f : ℕ} {X : Type} [Group X] (φ : (ggU .PSU m f).K →* X)
    (hns : ¬ Group.IsSolvable ↥φ.range) : 2 ≤ m ∧ (m ≤ 3 → 2 ≤ f) := by
  have hsmall : ∀ {m f : ℕ}, (m ≤ 1 ∨ (m ≤ 3 ∧ f ≤ 1)) →
      Group.IsSolvable (ggU .PSU m f).K := by
    intro m f h
    by_cases hf0 : f = 0
    · subst hf0
      have h0 : (ggU .PSU m 0).K = Matrix.SpecialLinearGroup (Fin 1) (ZMod 2) := by
        simp only [ggU, lieUniversal]
        rw [dif_neg (show ¬ 1 ≤ 0 by omega)]
        rfl
      haveI : Subsingleton (ggU .PSU m 0).K := by
        rw [h0]
        exact CFSG.StandardType.subsingleton_specialLinear_of_card_le_one (Q := ZMod 2) (by simp)
      infer_instance
    · have hf : 1 ≤ f := by omega
      have hK : (ggU .PSU m f).K =
          Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m := by
        simp only [ggU, lieUniversal, hf, ↓reduceDIte]
      rcases h with hm | ⟨hm3, hf1⟩
      · haveI : Subsingleton (ggU .PSU m f).K := by
          rw [hK]
          exact l10sdsu_subsingleton_SU hm
        infer_instance
      · have hf_eq : f = 1 := by omega
        subst hf_eq
        interval_cases m
        · haveI : Subsingleton (ggU .PSU 0 1).K := by
            rw [hK]
            exact l10sdsu_subsingleton_SU (by omega : 0 ≤ 1)
          infer_instance
        · haveI : Subsingleton (ggU .PSU 1 1).K := by
            rw [hK]
            exact l10sdsu_subsingleton_SU (by omega : 1 ≤ 1)
          infer_instance
        · exact CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.su_two_solvable
            (F := GaloisField 2 (2 * 1)) (f := 1)
            (by rw [GaloisField.card 2 (2 * 1) (by norm_num)]; norm_num) rfl
        · exact CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.su_three_solvable
            (F := GaloisField 2 (2 * 1)) (f := 1)
            (by rw [GaloisField.card 2 (2 * 1) (by norm_num)]; norm_num) rfl
  constructor
  · by_contra hm
    haveI : Group.IsSolvable (ggU .PSU m f).K := hsmall (m := m) (f := f) (Or.inl (by omega))
    exact hns (Group.isSolvable_of_surjective φ.rangeRestrict_surjective)
  · intro hm3
    by_contra hf2
    haveI : Group.IsSolvable (ggU .PSU m f).K := hsmall (m := m) (f := f) (Or.inr ⟨hm3, by omega⟩)
    exact hns (Group.isSolvable_of_surjective φ.rangeRestrict_surjective)

theorem ggSixLieKnownPos_PSU_of_explicit
    (hpos : GGSixPSUPosExplicit) : GGSixLieKnownPos .PSU := by
  intro X _ _ n f ψ p G₀ B₁ D J L x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hadm : StatedLieAdmissible .PSU n 2 f := h3.admissible
  have hn : 3 ≤ n := hadm.2.2.1
  have hnf : ¬ (n = 3 ∧ f = 1) := by
    rintro ⟨rfl, rfl⟩
    exact hadm.2.2.2 (by norm_num)
  have hH : CFSG.StandardType.ClassicalPosition.GGSixPosHyp .PSU n f ψ p G₀ B₁ D J L x :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
  have hJns : ¬ Group.IsSolvable ↥J := by
    haveI : Group.IsPerfect ↥J := Group.isPerfect_def.mpr h15.2.2.1
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := h15.2.2.2
    haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
    exact Group.IsPerfect.not_isSolvable ↥J
  obtain ⟨R, Rm, hRJ, hRmJ, hf, hcase⟩ := hpos X n f ψ p G₀ B₁ D J L x hH
  rcases hcase with
    ⟨mJ, βJ, hmJlt, hβJ, hlongJ, hviaJ, ⟨β, hβ, hlongβ, u, hRu, hRmu⟩, hnbr⟩ |
    ⟨kJ, φJ, βJ, hkn, hβJ, hφJ, hφJker, hviaJ, hlift, hpq, hG0, hnbr⟩
  · obtain ⟨φ, hφr, -, -, -⟩ := hviaJ
    have hJns' : ¬ Group.IsSolvable ↥φ.range := by rw [hφr]; exact hJns
    have hmJ := jDim_selfDual_psu φ hJns'
    refine ⟨R, Rm, hRJ, hRmJ, ⟨β, hβ, Or.inl hlongβ, u, hRu, hRmu⟩, ?_, ?_⟩
    · intro e he hne K hKG hKcomp hJK hKJ hodd
      obtain ⟨mK, βK, hlt, hβK, hlongK, hviaK⟩ := hnbr e he hne K hKG hKcomp hJK hKJ hodd
      obtain ⟨φK, hφKr, hφKker, uK, hRK⟩ := hviaK
      have hmK3 : 3 ≤ mK := by omega
      have hmKf : ¬ (mK = 3 ∧ f = 1) := by
        rintro ⟨rfl, rfl⟩
        have := hmJ.2 (by omega : mJ ≤ 3)
        omega
      refine ⟨?_, ?_⟩
      · have hmain := ggRootInnerAt_ggU_psu (n := mK) hmK3 hmKf φK hφKker hβK
          (Or.inl hlongK) uK
        rw [hφKr, ← hRK] at hmain
        exact hmain
      · have hmain := ggRootNoCentralAt_ggU_psu (n := mK) hmK3 hmKf φK hφKker hβK
          (Or.inl hlongK) uK
        rw [hφKr, ← hRK] at hmain
        exact hmain
    · intro Y hY hYnorG hYnorR hcomm
      rw [← h1] at hYnorG hcomm ⊢
      exact itemThree_ggU_psu hn hnf ψ h2 hβ (Or.inl hlongβ) u hRu Y hY hYnorG hYnorR hcomm
  · have hJns' : ¬ Group.IsSolvable ↥φJ.range := by rw [hφJ]; exact hJns
    have h13' : B₁ ≤ Subgroup.normalizer (φJ.range : Set X) := by rwa [hφJ]
    have h14' : B₁ ⊓ Subgroup.centralizer (φJ.range : Set X) = D := by
      rw [hφJ]
      exact h14
    have hk : 2 ≤ kJ := jDim_dualPair_psu φJ hφJker hJns' h5 h6 h9 h13' h14' h10 h12 hlift
    have hf2 : 2 ≤ f := by
      by_contra hlt
      push Not at hlt
      have hf1 : f = 1 := by omega
      subst hf1
      have hpq1 : p ∣ 1 := by simpa using hpq
      have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hpq1
      have hp2 := h5.two_le
      omega
    refine ⟨R, Rm, hRJ, hRmJ, ggRootPosG0_dualPair_psu ψ hpq hG0, ?_, ?_⟩
    · intro e he hne K hKG hKcomp hJK hKJ hodd
      rcases hnbr e he hne K hKG hKcomp hJK hKJ hodd with
        ⟨kK, βK, hlt, hβK, hviaK⟩ | ⟨mK, βK, hle, hβK, hor, hviaK⟩
      · obtain ⟨φK, hφKr, hφKker, uK, hRK⟩ := hviaK
        have hmain := PSL.itemTwo_ggU_psl (f := 2 * f) (k := kK)
          (Or.inr (Or.inl ⟨by omega, by omega⟩)) φK hφKker hβK uK hRK
        simpa [hφKr] using hmain
      · obtain ⟨φK, hφKr, hφKker, uK, hRK⟩ := hviaK
        have hmK3 : 3 ≤ mK := by omega
        have hmKf : ¬ (mK = 3 ∧ f = 1) := by omega
        have hposK : GGLongRoot (ggU .PSU mK f).D βK ∨
            (6 ≤ mK ∧ 2 ≤ f ∧ 2 • βK ∉ (ggU .PSU mK f).D.roots) :=
          hor.imp_right (fun h => ⟨by omega, hf2, h⟩)
        refine ⟨?_, ?_⟩
        · have hmain := ggRootInnerAt_ggU_psu (n := mK) hmK3 hmKf φK hφKker hβK hposK uK
          rw [hφKr, ← hRK] at hmain
          exact hmain
        · have hmain := ggRootNoCentralAt_ggU_psu (n := mK) hmK3 hmKf φK hφKker hβK hposK uK
          rw [hφKr, ← hRK] at hmain
          exact hmain
    · intro Y hY hYnorG hYnorR hcomm
      obtain ⟨β, hβ, h2β, u, hRu, -⟩ := hG0
      rw [← h1] at hYnorG hcomm ⊢
      exact itemThree_ggU_psu hn hnf ψ h2 hβ (Or.inr ⟨by omega, hf2, h2β⟩) u hRu
        Y hY hYnorG hYnorR hcomm

theorem ggSixLieKnown_PSU_of_explicit
    (hpos : GGSixPSUPosExplicit) : GGSixLieKnown .PSU :=
  ggSixLieKnown_of_pos_PSU (ggSixLieKnownPos_PSU_of_explicit hpos)

end CFSG.StandardType.LieKnownR2.PSU
