module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusLangCoordinates
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusLarge
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNonsLang
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LocalAnalysis.StandardType.GGRealKGExcNegJ
public import CFSG.RankThree.PartOne.KE.E8RootCharacterTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public noncomputable section

namespace CFSG.StandardType.E8ScalarTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def coordHom (D : LangDatum .E8 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .E8} (hn : D.n = canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.E8.rank → ℤ, w • u = -u) :
    (Fin Tag.E8.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) →*
      adjointGroup .E8 K := by
  exact ScalarLangTorus.coordHom D Fr hFr hΦ hn hw (fun X hfin hXC hXF => by
      let : Finite X := hfin
      exact Subgroup.relIndex_eq_one.mp (Nat.dvd_one.mp
        (finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K)
          (L := AlgebraicClosure K) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1))

omit [CharP K 2] in
theorem coordHom_injective (D : LangDatum .E8 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .E8} (hn : D.n = canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.E8.rank → ℤ, w • u = -u) :
    Function.Injective (coordHom D Fr hFr hΦ hn hw) := by
  exact ScalarLangTorus.coordHom_injective D Fr hFr hΦ hn hw
    (fun X hfin hXC hXF => by
      let : Finite X := hfin
      exact Subgroup.relIndex_eq_one.mp (Nat.dvd_one.mp
        (finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K)
          (L := AlgebraicClosure K) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1))

omit [CharP K 2] in
theorem mem_range_coordHom_iff (D : LangDatum .E8 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .E8} (hn : D.n = canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.E8.rank → ℤ, w • u = -u) (y : adjointGroup .E8 K) :
    y ∈ (coordHom D Fr hFr hΦ hn hw).range ↔
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E8 K) * D.g0 ∈
        D.torus := by
  exact ScalarLangTorus.mem_range_coordHom_iff D Fr hFr hΦ hn hw
    (fun X hfin hXC hXF => by
      let : Finite X := hfin
      exact Subgroup.relIndex_eq_one.mp (Nat.dvd_one.mp
        (finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K)
          (L := AlgebraicClosure K) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1)) y

theorem exists_frame_of_langFrameData
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E8 K))
    (hE : CFSG.Assembly.IsElemAbelian p E)
    (hSC : ∀ g : adjointGroup .E8 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E)
    (hLang : Irred937.LangFrameData .E8 p K E) :
    ∃ (F : ExcFrame .E8 K p E) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι : Multiplicative (Fin Tag.E8.rank → ZMod p) →* adjointGroup .E8 K)
      (n : Fin Tag.E8.rank → adjointGroup .E8 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧
      (∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x) ∧
      (∀ u : Fin Tag.E8.rank → ℤ, F.w • u = -u) ∧
      orderOf ζ = p ∧ Function.Injective ι ∧ ι.range = E ∧
      (∀ s : Fin Tag.E8.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            (ι (Multiplicative.ofAdd s) : ModGL .E8 K) =
          F.D.g0 * ExcFrames.frameDiag ζ hζ s * F.D.g0⁻¹) ∧
      (∀ k, baseChangeGL (algebraMap K (AlgebraicClosure K)) (n k : ModGL .E8 K) =
        F.D.g0 * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) (simple .E8 k) * F.D.g0⁻¹) ∧
      (∀ k s, n k * ι (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .E8 K)),
        ∃ v : WeylGroup .E8, ∀ s,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 p v s))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨F, Fr, ζ, hζ, ι, -, hplus, hFr, hΦ, hζo, hι, hrange, hcent, hbase⟩ :=
    excFrame_of_langFrameData_with_coordinates (Or.inr rfl) hp2 hq hE hSC hLang
  have hwneg := ggRealKGNeg_smul_eq_neg (Or.inr (Or.inl rfl)) (hplus hq)
  have hrat : ∀ X : Subgroup (ModGL .E8 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .E8 (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup .E8 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    fun X _ hXC hXF => Subgroup.relIndex_eq_one.mp (Nat.dvd_one.mp
      (finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K)
        (L := AlgebraicClosure K) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1)
  have hlang : Units.map (entrywiseHom Fr) F.D.g0 =
      F.D.g0 * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) F.w := by
    rw [← hΦ, ← F.n_eq]
    exact F.D.lang
  obtain ⟨n, hn, hact⟩ := exists_simpleRealization_of_frame_with_baseChange hFr hrat
    F.D.g0_mem hlang hcent hbase
  refine ⟨F, Fr, ζ, hζ, ι, n, hFr, hΦ, hwneg, hζo, hι, hrange, hbase, hn, hact,
    (fun g hg => exists_weyl_of_mem_normalizer_of_frame F.D.g0_mem hι hrange hbase hg)⟩

theorem exists_frame_of_selfCentralizing
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E8 K))
    (hE : CFSG.Assembly.IsElemAbelian p E) (hcard : p ^ 7 ≤ Nat.card E)
    (hSC : ∀ g : adjointGroup .E8 K, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∃ (F : ExcFrame .E8 K p E) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι : Multiplicative (Fin Tag.E8.rank → ZMod p) →* adjointGroup .E8 K)
      (n : Fin Tag.E8.rank → adjointGroup .E8 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧
      (∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x) ∧
      (∀ u : Fin Tag.E8.rank → ℤ, F.w • u = -u) ∧
      orderOf ζ = p ∧ Function.Injective ι ∧ ι.range = E ∧
      (∀ s : Fin Tag.E8.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            (ι (Multiplicative.ofAdd s) : ModGL .E8 K) =
          F.D.g0 * ExcFrames.frameDiag ζ hζ s * F.D.g0⁻¹) ∧
      (∀ k, baseChangeGL (algebraMap K (AlgebraicClosure K)) (n k : ModGL .E8 K) =
        F.D.g0 * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) (simple .E8 k) * F.D.g0⁻¹) ∧
      (∀ k s, n k * ι (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 p (simple .E8 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .E8 K)),
        ∃ v : WeylGroup .E8, ∀ s,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 p v s))) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  exact exists_frame_of_langFrameData hp hp2 hq E hE hSC
    (exists_langFrame_of_sc_odd (Or.inr rfl) hp2 K hq E hE hcard
      (fun g hg hp => hSC g (fun x hx => (Subgroup.mem_centralizer_iff.mp hg x hx).symm) hp))

theorem exists_frame_of_selfCentralizing_three
    (hq : 3 ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E8 K))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hcard : 3 ^ 7 ≤ Nat.card E)
    (hSC : ∀ g : adjointGroup .E8 K, (∀ x ∈ E, g * x = x * g) → g ^ 3 = 1 → g ∈ E) :
    ∃ (F : ExcFrame .E8 K 3 E) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1)
      (ι : Multiplicative (Fin Tag.E8.rank → ZMod 3) →* adjointGroup .E8 K)
      (n : Fin Tag.E8.rank → adjointGroup .E8 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧
      (∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x) ∧
      (∀ u : Fin Tag.E8.rank → ℤ, F.w • u = -u) ∧
      orderOf ζ = 3 ∧ Function.Injective ι ∧ ι.range = E ∧
      (∀ s : Fin Tag.E8.rank → ZMod 3,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            (ι (Multiplicative.ofAdd s) : ModGL .E8 K) =
          F.D.g0 * ExcFrames.frameDiag ζ hζ s * F.D.g0⁻¹) ∧
      (∀ k, baseChangeGL (algebraMap K (AlgebraicClosure K)) (n k : ModGL .E8 K) =
        F.D.g0 * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) (simple .E8 k) * F.D.g0⁻¹) ∧
      (∀ k s, n k * ι (Multiplicative.ofAdd s) * (n k)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 3 (simple .E8 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .E8 K)),
        ∃ v : WeylGroup .E8, ∀ s,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct .E8 3 v s))) := by
  exact exists_frame_of_selfCentralizing Nat.prime_three (by norm_num) hq E hE hcard hSC

theorem centralizer_le_range {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (adjointGroup .E8 K)} (F : ExcFrame .E8 K p E)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x)
    (hq : p ∣ Nat.card K + 1) (hlong : ExcIsLongest .E8 F.w)
    (hw : ∀ u : Fin Tag.E8.rank → ℤ, F.w • u = -u) :
    Subgroup.centralizer (E : Set (adjointGroup .E8 K)) ≤
      (coordHom F.D Fr hFr hΦ F.n_eq hw).range := by
  intro g hg
  apply (mem_range_coordHom_iff F.D Fr hFr hΦ F.n_eq hw g).mpr
  exact (ggKGExc_centralizer_eq (Or.inr (Or.inr (Or.inl rfl))) hp
    (by have := hp.two_le; omega) (by simp) F (Or.inr ⟨hq, hlong⟩) g).mp hg

omit [CharP K 2] in
theorem mem_primeSubgroup_iff {p : ℕ} {E : Subgroup (adjointGroup .E8 K)} (F : ExcFrame .E8 K p E)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, F.D.Φ x = Units.map (entrywiseHom Fr) x)
    (hw : ∀ u : Fin Tag.E8.rank → ℤ, F.w • u = -u) (g : adjointGroup .E8 K) :
    g ∈ E ↔ g ^ p = 1 ∧ g ∈ (coordHom F.D Fr hFr hΦ F.n_eq hw).range := by
  rw [F.mem_iff, mem_range_coordHom_iff]

@[expose] def corootTupleHom (k : Fin Tag.E8.rank) :
    rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) →*
      (Fin Tag.E8.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) where
  toFun := fun z j => z ^ Tag.E8.cartan k j
  map_one' := by ext j; simp
  map_mul' := fun z u => by ext j; simp [mul_zpow]

@[expose] def corootHom (D : LangDatum .E8 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .E8} (hn : D.n = canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.E8.rank → ℤ, w • u = -u) (k : Fin Tag.E8.rank) :
    rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) →* adjointGroup .E8 K :=
  (coordHom D Fr hFr hΦ hn hw).comp (corootTupleHom k)

omit [CharP K 2] in
theorem simple_conj_coordHom (D : LangDatum .E8 (AlgebraicClosure K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ x, D.Φ x = Units.map (entrywiseHom Fr) x)
    {w : WeylGroup .E8} (hn : D.n = canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w)
    (hw : ∀ u : Fin Tag.E8.rank → ℤ, w • u = -u) (k : Fin Tag.E8.rank)
    (n : adjointGroup .E8 K)
    (hnb : baseChangeGL (algebraMap K (AlgebraicClosure K)) (n : ModGL .E8 K) =
      D.g0 * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) (simple .E8 k) * D.g0⁻¹)
    (a : Fin Tag.E8.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    n * coordHom D Fr hFr hΦ hn hw a * n⁻¹ =
      coordHom D Fr hFr hΦ hn hw a * (corootHom D Fr hFr hΦ hn hw k (a k))⁻¹ := by
  exact ScalarLangTorus.simple_conj_coordHom D Fr hFr hΦ hn hw
    (fun X hfin hXC hXF => by
      let : Finite X := hfin
      exact Subgroup.relIndex_eq_one.mp (Nat.dvd_one.mp
        (finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K)
          (L := AlgebraicClosure K) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1)) k n hnb a

theorem exists_rootValue_equiv :
    Nonempty (rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) ≃*
      Multiplicative (ZMod (Nat.card K + 1))) :=
  ScalarLangTorus.exists_rootValue_equiv

end CFSG.StandardType.E8ScalarTorus
