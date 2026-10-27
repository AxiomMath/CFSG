module

public import CFSG.LocalAnalysis.StandardType.GGTorusLangCoordinates
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusE7
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusLarge
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNonsLang
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LocalAnalysis.StandardType.GGRealKGExcNegJ

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_e7_scalar_frame_of_langFrame
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E7 K))
    (hE : CFSG.Assembly.IsElemAbelian p E)
    (hSC : ∀ g : adjointGroup .E7 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E)
    (hLang : Irred937.LangFrameData .E7 p K E) :
    ∃ (F : ExcFrame .E7 K p E) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K)
      (n : Fin Tag.E7.rank → adjointGroup .E7 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧
      (∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x) ∧
      (∀ u : Fin Tag.E7.rank → ℤ, F.w • u = -u) ∧
      orderOf ζ = p ∧ Function.Injective ι ∧ ι.range = E ∧
      (∀ s : Fin Tag.E7.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            (ι (Multiplicative.ofAdd s) : ModGL .E7 K) =
          F.D.g0 * ExcFrames.frameDiag ζ hζ s * F.D.g0⁻¹) ∧
      (∀ k, baseChangeGL (algebraMap K (AlgebraicClosure K)) (n k : ModGL .E7 K) =
        F.D.g0 * canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) (simple .E7 k) * F.D.g0⁻¹) ∧
      (∀ k s, n k * ι (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (simple .E7 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .E7 K)),
        ∃ v : WeylGroup .E7, ∀ s,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct .E7 p v s))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨F, Fr, ζ, hζ, ι, -, hplus, hFr, hΦ, hζo, hι, hrange, hcent, hbase⟩ :=
    excFrame_of_langFrameData_with_coordinates (Or.inl rfl) hp2 hq hE hSC hLang
  have hwneg := ggRealKGNeg_smul_eq_neg (Or.inl rfl) (hplus hq)
  have hrat : ∀ X : Subgroup (ModGL .E7 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .E7 (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    fun X hfin hXC hXF => by
      let : Finite X := hfin
      exact finite_fixed_le_map_adjointGroup_E7 Fr hFr X hXC hXF
  have hlang : Units.map (entrywiseHom Fr) F.D.g0 =
      F.D.g0 * canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) F.w := by
    rw [← hΦ, ← F.n_eq]
    exact F.D.lang
  obtain ⟨n, hn, hact⟩ := exists_simpleRealization_of_frame_with_baseChange hFr hrat
    F.D.g0_mem hlang hcent hbase
  refine ⟨F, Fr, ζ, hζ, ι, n, hFr, hΦ, hwneg, hζo, hι, hrange, hbase, hn, hact,
    (fun g hg => exists_weyl_of_mem_normalizer_of_frame F.D.g0_mem hι hrange hbase hg)⟩

theorem exists_e7_scalar_frame
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E7 K))
    (hE : CFSG.Assembly.IsElemAbelian p E) (hcard : p ^ 6 ≤ Nat.card E)
    (hSC : ∀ g : adjointGroup .E7 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∃ (F : ExcFrame .E7 K p E) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι : Multiplicative (Fin Tag.E7.rank → ZMod p) →* adjointGroup .E7 K)
      (n : Fin Tag.E7.rank → adjointGroup .E7 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧
      (∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x) ∧
      (∀ u : Fin Tag.E7.rank → ℤ, F.w • u = -u) ∧
      orderOf ζ = p ∧ Function.Injective ι ∧ ι.range = E ∧
      (∀ s : Fin Tag.E7.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            (ι (Multiplicative.ofAdd s) : ModGL .E7 K) =
          F.D.g0 * ExcFrames.frameDiag ζ hζ s * F.D.g0⁻¹) ∧
      (∀ k, baseChangeGL (algebraMap K (AlgebraicClosure K)) (n k : ModGL .E7 K) =
        F.D.g0 * canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) (simple .E7 k) * F.D.g0⁻¹) ∧
      (∀ k s, n k * ι (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E7 p (simple .E7 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .E7 K)),
        ∃ v : WeylGroup .E7, ∀ s,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct .E7 p v s))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  exact exists_e7_scalar_frame_of_langFrame hp hp2 hq E hE hSC
    (exists_langFrame_of_sc_odd (Or.inl rfl) hp2 K hq E hE hcard
      (fun g hg hp => hSC g (fun x hx => (Subgroup.mem_centralizer_iff.mp hg x hx).symm) hp))


theorem e7_scalar_centralizer_le_coordinates {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (adjointGroup .E7 K)} (F : ExcFrame .E7 K p E)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x)
    (hq : p ∣ Nat.card K + 1) (hlong : ExcIsLongest .E7 F.w)
    (hw : ∀ u : Fin Tag.E7.rank → ℤ, F.w • u = -u) :
    Subgroup.centralizer (E : Set (adjointGroup .E7 K)) ≤
      (ScalarLangTorus.coordHom F.D Fr hFr hΦ F.n_eq hw
        (fun X hfin hXC hXF => by
          let : Finite X := hfin
          exact finite_fixed_le_map_adjointGroup_E7 Fr hFr X hXC hXF)).range := by
  intro g hg
  apply (ScalarLangTorus.mem_range_coordHom_iff F.D Fr hFr hΦ F.n_eq hw _ g).mpr
  exact (ggKGExc_centralizer_eq (Or.inr (Or.inl rfl)) hp
    (by have := hp.two_le; omega) (by simp) F (Or.inr ⟨hq, hlong⟩) g).mp hg

theorem e7_scalar_mem_iff_coordinates {p : ℕ} {E : Subgroup (adjointGroup .E7 K)}
    (F : ExcFrame .E7 K p E)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x)
    (hw : ∀ u : Fin Tag.E7.rank → ℤ, F.w • u = -u) (g : adjointGroup .E7 K) :
    g ∈ E ↔ g ^ p = 1 ∧
      g ∈ (ScalarLangTorus.coordHom F.D Fr hFr hΦ F.n_eq hw
        (fun X hfin hXC hXF => by
          let : Finite X := hfin
          exact finite_fixed_le_map_adjointGroup_E7 Fr hFr X hXC hXF)).range := by
  rw [F.mem_iff, ScalarLangTorus.mem_range_coordHom_iff]

end CFSG.StandardType
