module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4Frame
public import CFSG.LocalAnalysis.StandardType.GGTorusF4Scalar
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusFrame
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcCent

public noncomputable section

namespace CFSG.StandardType.F4NonsplitFrame

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus

open scoped Matrix


theorem exists_nonsplit_frame_data_of_langFrame
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp3 : 3 ≤ p) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hpq : p ∣ Nat.card K + 1)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ p = 1 → x ∈ E)
    (hLF : ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (g0 : ModGL .F4 (AlgebraicClosure K)) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .F4 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧ g0 ∈ adjointGroup .F4 (AlgebraicClosure K) ∧
      Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) f4Neg ∧
      orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = E ∧
      ∀ s : Fin Tag.F4.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((ι₀ (Multiplicative.ofAdd s) : adjointGroup .F4 K) : ModGL .F4 K) =
          g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (g0 : ModGL .F4 (AlgebraicClosure K)) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (D : LangDatum .F4 (AlgebraicClosure K))
      (φ : (Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) →*
        adjointGroup .F4 K)
      (n : Fin Tag.F4.rank → adjointGroup .F4 K)
      (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .F4 K)
      (hFr : ∀ c, Fr c = c ^ Nat.card K)
      (hg0C : g0 ∈ adjointGroup .F4 (AlgebraicClosure K))
      (hg0 : Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) f4Neg)
      (hΦ : ∀ x : ModGL .F4 (AlgebraicClosure K),
        D.Φ x = Units.map (entrywiseHom Fr) x)
      (hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) f4Neg)
      (hw : ∀ u : Fin Tag.F4.rank → ℤ, f4Neg • u = -u)
      (_hζo : orderOf ζ = p)
      (_hι : Function.Injective ι₀)
      (_hrange : ι₀.range = E)
      (_hbase : ∀ s : Fin Tag.F4.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((ι₀ (Multiplicative.ofAdd s) : adjointGroup .F4 K) : ModGL .F4 K) =
          g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹),
      D = LangDatum.ofFrobenius Fr (Nat.card K) hFr f4Neg hg0C hg0 ∧
      (∀ a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K),
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            (φ a : ModGL .F4 K) =
          g0 * rootDiagUnit .F4 (fun i => (a i : (AlgebraicClosure K)ˣ)) * g0⁻¹) ∧
      Function.Injective φ ∧
      (∀ y : adjointGroup .F4 K,
        y ∈ φ.range ↔
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .F4 K) * g0
            ∈ D.torus) ∧
      (∀ k, baseChangeGL (algebraMap K (AlgebraicClosure K)) (n k : ModGL .F4 K) =
        g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) (simple .F4 k) * g0⁻¹) ∧
      (∀ (k : Fin Tag.F4.rank) (s : Fin Tag.F4.rank → ZMod p),
        n k * ι₀ (Multiplicative.ofAdd s) * (n k)⁻¹ =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple .F4 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .F4 K)),
        ∃ u : WeylGroup .F4, ∀ s : Fin Tag.F4.rank → ZMod p,
          g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p u s))) ∧
      (∀ g : adjointGroup .F4 K, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range) ∧
      (Subgroup.centralizer (E : Set (adjointGroup .F4 K)) ≤ φ.range) ∧
      (∀ (k : Fin Tag.F4.rank)
        (a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)),
        n k * φ a * (n k)⁻¹ =
          φ a * (F4ScalarTorus.corootHom D Fr hFr hΦ hn hw k (a k))⁻¹)
    := by
  classical
  obtain ⟨Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hζo, hι, hrange, hbase⟩ := hLF
  let D : LangDatum .F4 (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr f4Neg hg0C hg0
  have hD : D = LangDatum.ofFrobenius Fr (Nat.card K) hFr f4Neg hg0C hg0 := rfl
  have hΦ : ∀ x : ModGL .F4 (AlgebraicClosure K),
      D.Φ x = Units.map (entrywiseHom Fr) x := fun x => rfl
  have hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) f4Neg := rfl
  have hw : ∀ u : Fin Tag.F4.rank → ℤ, f4Neg • u = -u := f4Neg_smul
  let φ : (Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) →*
      adjointGroup .F4 K := F4ScalarTorus.coordHom D Fr hFr hΦ hn hw
  have hφbase : ∀ a : Fin Tag.F4.rank →
      rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K),
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (φ a : ModGL .F4 K) =
        g0 * rootDiagUnit .F4 (fun i => (a i : (AlgebraicClosure K)ˣ)) * g0⁻¹ :=
    fun a => F4ScalarTorus.baseChange_coordHom D Fr hFr hΦ hn hw a
  have hφinj : Function.Injective φ :=
    F4ScalarTorus.coordHom_injective D Fr hFr hΦ hn hw
  have hφrange : ∀ y : adjointGroup .F4 K,
      y ∈ φ.range ↔
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .F4 K) * g0 ∈
          D.torus :=
    fun y => F4ScalarTorus.mem_range_coordHom_iff D Fr hFr hΦ hn hw y
  have hrat : ∀ X : Subgroup (ModGL .F4 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .F4 (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup .F4 K).map
          (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
    intro X _ hXC hXF x hx
    exact CFSG.LieType.Chevalley.mem_map_adjointGroup_F4_of_frobenius_fixed
      Fr hFr (hXC hx) (hXF x hx)
  obtain ⟨n, hnbase, hact⟩ :=
    exists_simpleRealization_of_frame_with_baseChange (τ := .F4) (p := p) (w := f4Neg)
      hFr hrat hg0C hg0 (fun v => f4Neg_comm v) hbase
  have hframeT : ∀ s : Fin Tag.F4.rank → ZMod p,
      ExcFrames.frameDiag ζ hζ s ∈ D.torus := by
    intro s
    let a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ :=
      TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .F4 p s)
    have hfd : ExcFrames.frameDiag ζ hζ s = rootDiagUnit .F4 a := rfl
    have hpow : a ^ p = 1 := by
      apply (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
        (τ := .F4) (K := AlgebraicClosure K))
      rw [← rootDiagUnit_pow]
      simpa [a, ExcFrames.frameDiag, rootDiagUnit_one] using
        ExcFrames.frameDiag_pow (τ := .F4) ζ hζ s
    have hpow_i : ∀ i, (a i) ^ p = 1 := fun i => by simpa using congrFun hpow i
    have hroot : ∀ i, a i ^ (Nat.card K + 1) = 1 := by
      intro i
      obtain ⟨c, hc⟩ := hpq
      rw [hc, pow_mul, hpow_i i, one_pow]
    rw [hfd]
    exact (F4ScalarTorus.mem_torus_iff_of_neg D Fr hFr hΦ hn hw).2 ⟨a, rfl, hroot⟩
  have hEsub : E ≤ φ.range := by
    intro e he
    rw [← hrange] at he
    obtain ⟨t, rfl⟩ := he
    let s : Fin Tag.F4.rank → ZMod p := Multiplicative.toAdd t
    have ht : t = Multiplicative.ofAdd s := rfl
    rw [ht]
    apply (hφrange _).2
    rw [hbase s]
    have hconj : g0⁻¹ * (g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) * g0 =
        ExcFrames.frameDiag ζ hζ s := by group
    rw [hconj]
    exact hframeT s
  have hφcomm : ∀ a b : φ.range, a * b = b * a := by
    rintro ⟨a, ⟨x, rfl⟩⟩ ⟨b, ⟨y, rfl⟩⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, mul_comm]
  have hEiff : ∀ g : adjointGroup .F4 K, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range := by
    intro g
    constructor
    · intro hg
      exact ⟨hE.2 g hg, hEsub hg⟩
    · rintro ⟨hgpow, hgφ⟩
      have hcomm : ∀ e ∈ E, g * e = e * g := by
        intro e he
        exact congrArg Subtype.val (hφcomm ⟨g, hgφ⟩ ⟨e, hEsub he⟩)
      have hcomm' : ∀ h ∈ E, h * g = g * h := by
        intro h hh
        exact (hcomm h hh).symm
      exact hSC g (Subgroup.mem_centralizer_iff.2 hcomm') hgpow
  have hEiffT : ∀ x : adjointGroup .F4 K,
      x ∈ E ↔ x ^ p = 1 ∧ g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL .F4 K) * g0 ∈ D.torus := by
    intro x
    rw [hEiff x]
    constructor
    · rintro ⟨hp, hφ⟩
      exact ⟨hp, (hφrange x).1 hφ⟩
    · rintro ⟨hp, ht⟩
      exact ⟨hp, (hφrange x).2 ht⟩
  let F : ExcFrame .F4 K p E :=
    { D := D
      w := f4Neg
      q_eq := rfl
      frob := ⟨Fr, hFr, hΦ⟩
      n_eq := rfl
      mem_iff := hEiffT }
  have hlong : ExcIsLongest .F4 f4Neg := by
    intro α _ hpos i
    rw [f4Neg_smul]
    exact neg_nonpos.mpr (hpos i)
  have hcent_eq := ggKGExc_centralizer_eq (τ := .F4)
    (Or.inr (Or.inr (Or.inr rfl))) (Fact.out : p.Prime) hp3
    (by intro h; cases h) F (Or.inr ⟨hpq, hlong⟩)
  refine ⟨Fr, g0, ζ, hζ, D, φ, n, ι₀, hFr, hg0C, hg0, hΦ, hn, hw, hζo, hι, hrange, hbase,
    hD, hφbase, hφinj, hφrange, hnbase, hact, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact exists_weyl_of_mem_normalizer_of_frame hg0C hι hrange hbase hg
  · exact hEiff
  · intro x hx
    exact (hφrange x).2 ((hcent_eq x).1 hx)
  · intro k a
    exact F4ScalarTorus.simple_conj_coordHom D Fr hFr hΦ hn hw k (n k) (hnbase k) a

theorem exists_nonsplit_frame_data
    {p : ℕ} [Fact p.Prime] [NeZero p] (hp5 : 5 ≤ p) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hpq : p ∣ Nat.card K + 1)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ p = 1 → x ∈ E) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (g0 : ModGL .F4 (AlgebraicClosure K)) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (D : LangDatum .F4 (AlgebraicClosure K))
      (φ : (Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) →*
        adjointGroup .F4 K)
      (n : Fin Tag.F4.rank → adjointGroup .F4 K)
      (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .F4 K)
      (hFr : ∀ c, Fr c = c ^ Nat.card K)
      (hg0C : g0 ∈ adjointGroup .F4 (AlgebraicClosure K))
      (hg0 : Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) f4Neg)
      (hΦ : ∀ x : ModGL .F4 (AlgebraicClosure K),
        D.Φ x = Units.map (entrywiseHom Fr) x)
      (hn : D.n = canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) f4Neg)
      (hw : ∀ u : Fin Tag.F4.rank → ℤ, f4Neg • u = -u)
      (_hζo : orderOf ζ = p)
      (_hι : Function.Injective ι₀)
      (_hrange : ι₀.range = E)
      (_hbase : ∀ s : Fin Tag.F4.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((ι₀ (Multiplicative.ofAdd s) : adjointGroup .F4 K) : ModGL .F4 K) =
          g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹),
      D = LangDatum.ofFrobenius Fr (Nat.card K) hFr f4Neg hg0C hg0 ∧
      (∀ a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K),
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            (φ a : ModGL .F4 K) =
          g0 * rootDiagUnit .F4 (fun i => (a i : (AlgebraicClosure K)ˣ)) * g0⁻¹) ∧
      Function.Injective φ ∧
      (∀ y : adjointGroup .F4 K,
        y ∈ φ.range ↔
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .F4 K) * g0
            ∈ D.torus) ∧
      (∀ k, baseChangeGL (algebraMap K (AlgebraicClosure K)) (n k : ModGL .F4 K) =
        g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) (simple .F4 k) * g0⁻¹) ∧
      (∀ (k : Fin Tag.F4.rank) (s : Fin Tag.F4.rank → ZMod p),
        n k * ι₀ (Multiplicative.ofAdd s) * (n k)⁻¹ =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple .F4 k) s))) ∧
      (∀ g ∈ Subgroup.normalizer (E : Set (adjointGroup .F4 K)),
        ∃ u : WeylGroup .F4, ∀ s : Fin Tag.F4.rank → ZMod p,
          g * ι₀ (Multiplicative.ofAdd s) * g⁻¹ =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 p u s))) ∧
      (∀ g : adjointGroup .F4 K, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range) ∧
      (Subgroup.centralizer (E : Set (adjointGroup .F4 K)) ≤ φ.range) ∧
      (∀ (k : Fin Tag.F4.rank)
        (a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)),
        n k * φ a * (n k)⁻¹ =
          φ a * (F4ScalarTorus.corootHom D Fr hFr hΦ hn hw k (a k))⁻¹)
    :=
  exists_nonsplit_frame_data_of_langFrame (by omega) hpq hE hSC
    (exists_langFrame_F4_of_sc (p := p) hp5 hpq hE hSC)

end CFSG.StandardType.F4NonsplitFrame
