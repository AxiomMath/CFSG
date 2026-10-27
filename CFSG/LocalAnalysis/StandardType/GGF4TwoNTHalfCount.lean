module

public import CFSG.LocalAnalysis.StandardType.GGF4TwoNTHalfMaxFixed
public import CFSG.LocalAnalysis.StandardType.GGF4TwoThreeCCent
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBLang
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThreeProved
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8b
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.LieType.SeitzGeneration.UnitaryNonabLift
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.RankThree.PartOne.KE.E8FourA1Family
public import CFSG.RankThree.PartOne.KLR.SL2Gen
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartTwo.KFacts.AutPSUDet
public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithNF
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz434
public import CFSG.RankThree.PartTwo.Sec19.Step199Proof
public import CFSG.RankThree.PartTwo.Sec4.Census.Open43

public section

namespace CFSG.StandardType.HalfMaxF4

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree TableB CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBF4TwoTB

section Count


private theorem exists_rational_of_fixed_F4 {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {y : ModGL .F4 L} (hy : y ∈ adjointGroup .F4 L)
    (hyF : Units.map (entrywiseHom Fr) y = y) :
    ∃ c : adjointGroup .F4 K, baseChangeGL (algebraMap K L) (c : ModGL .F4 K) = y := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_descent hy
  obtain ⟨E, hEf, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) S
  obtain ⟨y', hy', hyy⟩ := hS E hSE
  rw [← hyy] at hyF ⊢
  haveI : Finite E := hEf
  obtain ⟨σE, -, hJ, hfix⟩ := exists_subfieldFrobenius_data (τ := .F4) Fr hFr E hKE
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : CharP E 2 := RingHom.charP E.subtype E.subtype_injective 2
  have hring : ringChar E = 2 := ringChar.eq E 2
  have hyΓ : y' ∈ fixedFieldImage .F4 σE := by
    rw [← entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (τ := .F4)
      (Or.inr (Or.inl rfl)) hring σE]
    exact hfix y' hy' hyF
  have hmem : baseChangeGL E.subtype y' ∈
      (fixedFieldImage .F4 σE).map (baseChangeGL E.subtype) :=
    Subgroup.mem_map_of_mem (baseChangeGL E.subtype) hyΓ
  rw [hJ] at hmem
  obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 hmem
  exact ⟨⟨a, ha⟩, hay⟩

private theorem natCard_eq_torsion_F4 {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (E : Subgroup (adjointGroup .F4 K)) (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ p = 1 → x ∈ E)
    (w : WeylGroup .F4) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (g0 : ModGL .F4 L)
    (hg0C : g0 ∈ adjointGroup .F4 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem .F4) L w)
    (hEin : ∀ x ∈ E, baseChangeGL (algebraMap K L) ((x : adjointGroup .F4 K) : ModGL .F4 K) ∈
      (twistedTorus (canonicalRep (coxeterSystem .F4) L w) Fr).map (MulAut.conj g0).toMonoidHom) :
    Nat.card E = Nat.card {x : ModGL .F4 L //
      x ∈ twistedTorus (canonicalRep (coxeterSystem .F4) L w) Fr ∧ x ^ p = 1} := by
  classical
  have hι_inj : ∀ a b : ModGL .F4 K, baseChangeGL (algebraMap K L) a =
      baseChangeGL (algebraMap K L) b → a = b := fun a b h => baseChangeGL_injective _ h
  have hT : ∀ x : E, ∃ t ∈ twistedTorus (canonicalRep (coxeterSystem .F4) L w) Fr,
      g0 * t * g0⁻¹ = baseChangeGL (algebraMap K L) ((x : adjointGroup .F4 K) : ModGL .F4 K) :=
    fun x => Subgroup.mem_map.1 (hEin x x.2)
  have hmem : ∀ x : E, g0⁻¹ * baseChangeGL (algebraMap K L)
      ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0 ∈
      twistedTorus (canonicalRep (coxeterSystem .F4) L w) Fr := by
    intro x
    obtain ⟨t, ht, htx⟩ := hT x
    rw [← htx]
    have : g0⁻¹ * (g0 * t * g0⁻¹) * g0 = t := by group
    rw [this]
    exact ht
  have hpow : ∀ x : E, (g0⁻¹ * baseChangeGL (algebraMap K L)
      ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0) ^ p = 1 := by
    intro x
    have h1 : ((x : adjointGroup .F4 K) : ModGL .F4 K) ^ p = 1 :=
      congrArg Subtype.val (hE.2 x x.2)
    have := conj_pow (a := g0⁻¹) (b := baseChangeGL (algebraMap K L)
      ((x : adjointGroup .F4 K) : ModGL .F4 K)) (i := p)
    rw [inv_inv] at this
    rw [this, ← map_pow, h1, map_one]
    group
  let f : E → {x : ModGL .F4 L //
      x ∈ twistedTorus (canonicalRep (coxeterSystem .F4) L w) Fr ∧ x ^ p = 1} :=
    fun x => ⟨_, hmem x, hpow x⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : g0⁻¹ * baseChangeGL (algebraMap K L) ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0 =
        g0⁻¹ * baseChangeGL (algebraMap K L) ((y : adjointGroup .F4 K) : ModGL .F4 K) * g0 :=
      congrArg Subtype.val hxy
    have h2 : baseChangeGL (algebraMap K L) ((x : adjointGroup .F4 K) : ModGL .F4 K) =
        baseChangeGL (algebraMap K L) ((y : adjointGroup .F4 K) : ModGL .F4 K) := by
      have := mul_left_cancel (mul_right_cancel h1)
      exact this
    exact Subtype.ext (Subtype.ext (hι_inj _ _ h2))
  have hsurj : Function.Surjective f := by
    rintro ⟨t, ht, htp⟩
    have htC : t ∈ adjointGroup .F4 L := twistedTorusOf_le_adjointGroup _ _ ht
    have hyC : g0 * t * g0⁻¹ ∈ adjointGroup .F4 L := mul_mem (mul_mem hg0C htC) (inv_mem hg0C)
    have hyp : (g0 * t * g0⁻¹) ^ p = 1 := by
      rw [conj_pow, htp]
      group
    have hyΦ : Units.map (entrywiseHom Fr) (g0 * t * g0⁻¹) = g0 * t * g0⁻¹ := by
      have ht2 : canonicalRep (coxeterSystem .F4) L w * Units.map (entrywiseHom Fr) t *
          (canonicalRep (coxeterSystem .F4) L w)⁻¹ = t := (mem_twistedTorus.1 ht).2
      rw [map_mul, map_mul, map_inv, hg0]
      calc g0 * canonicalRep (coxeterSystem .F4) L w * Units.map (entrywiseHom Fr) t *
            (g0 * canonicalRep (coxeterSystem .F4) L w)⁻¹
          = g0 * (canonicalRep (coxeterSystem .F4) L w * Units.map (entrywiseHom Fr) t *
              (canonicalRep (coxeterSystem .F4) L w)⁻¹) * g0⁻¹ := by group
        _ = g0 * t * g0⁻¹ := by rw [ht2]
    obtain ⟨c, hc⟩ := exists_rational_of_fixed_F4 Fr hFr hyC hyΦ
    have hcE : c ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨s, hs, hsx⟩ := hT ⟨x, hx⟩
      have hts : s * t = t * s := by
        have := (ExcFramesHalf.isMulCommutative_twistedTorus (L := L) w Fr).is_comm.comm
          ⟨s, hs⟩ ⟨t, ht⟩
        exact congrArg Subtype.val this
      have h3 : baseChangeGL (algebraMap K L) (x : ModGL .F4 K) *
          baseChangeGL (algebraMap K L) (c : ModGL .F4 K) =
          baseChangeGL (algebraMap K L) (c : ModGL .F4 K) *
            baseChangeGL (algebraMap K L) (x : ModGL .F4 K) := by
        rw [hc, ← hsx]
        calc g0 * s * g0⁻¹ * (g0 * t * g0⁻¹) = g0 * (s * t) * g0⁻¹ := by group
          _ = g0 * (t * s) * g0⁻¹ := by rw [hts]
          _ = g0 * t * g0⁻¹ * (g0 * s * g0⁻¹) := by group
      have h4 : (x : ModGL .F4 K) * (c : ModGL .F4 K) =
          (c : ModGL .F4 K) * (x : ModGL .F4 K) := by
        apply hι_inj
        rw [map_mul, map_mul]
        exact h3
      exact Subtype.ext h4
    have hcp : c ^ p = 1 := by
      apply Subtype.ext
      apply hι_inj
      rw [Subgroup.coe_pow, map_pow, hc, hyp, Subgroup.coe_one, map_one]
    have hcEmem : c ∈ E := hSC c hcE hcp
    refine ⟨⟨c, hcEmem⟩, Subtype.ext ?_⟩
    change g0⁻¹ * baseChangeGL (algebraMap K L) ((c : adjointGroup .F4 K) : ModGL .F4 K) * g0 = t
    rw [hc]
    group
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

private theorem false_of_fixed_root_F4 {K L : Type} [Field K] [Finite K]
    [CharP K 2] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .F4 K))
    (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ p = 1 → x ∈ E)
    (w : WeylGroup .F4) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (g0 : ModGL .F4 L)
    (hg0C : g0 ∈ adjointGroup .F4 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem .F4) L w)
    (hEin : ∀ x ∈ E, baseChangeGL (algebraMap K L) ((x : adjointGroup .F4 K) : ModGL .F4 K) ∈
      (twistedTorus (canonicalRep (coxeterSystem .F4) L w) Fr).map (MulAut.conj g0).toMonoidHom)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot .F4 β) (hwβ : w • β = β) : False := by
  classical
  have : Fintype K := Fintype.ofFinite K
  haveI hCharL : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hFrι : ∀ c : K, Fr (algebraMap K L c) = algebraMap K L c := by
    intro c
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card]
    exact congrArg (algebraMap K L) (FiniteField.pow_card c)
  obtain ⟨b, hb⟩ := ExcFramesHalf.exists_sl2_orderOf_prime hp hpq
  have hbp : b ^ p = 1 := hb ▸ pow_orderOf_eq_one b
  have hbLp : Matrix.SpecialLinearGroup.map (algebraMap K L) b ^ p = 1 := by
    rw [← map_pow, hbp, map_one]
  have hmapFr : Matrix.SpecialLinearGroup.map Fr
      (Matrix.SpecialLinearGroup.map (algebraMap K L) b) =
      Matrix.SpecialLinearGroup.map (algebraMap K L) b := by
    apply Subtype.ext
    ext i j
    simp [hFrι]
  have hyC : rootSL2 .F4 L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b) ∈
      adjointGroup .F4 L := (exceptional_Lang_root_rank_one_data .F4 L β).2.2.2.2.1 _
  have hyp : rootSL2 .F4 L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b) ^ p = 1 := by
    rw [← map_pow, hbLp, map_one]
  have hyΦ : Units.map (entrywiseHom Fr)
      (rootSL2 .F4 L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b)) =
      rootSL2 .F4 L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b) := by
    rw [entrywise_rootSL2_of_field, hmapFr]
  have hn := ExcFramesHalf.canonicalRep_conj_rootSL2_of_fixed w hβ hwβ
    (Matrix.SpecialLinearGroup.map (algebraMap K L) b)
  generalize hy : rootSL2 .F4 L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b) = y
    at hyC hyp hyΦ hn
  have hy2C : g0 * y * g0⁻¹ ∈ adjointGroup .F4 L := mul_mem (mul_mem hg0C hyC) (inv_mem hg0C)
  have hy2p : (g0 * y * g0⁻¹) ^ p = 1 := by
    rw [conj_pow, hyp]
    group
  have hy2Φ : Units.map (entrywiseHom Fr) (g0 * y * g0⁻¹) = g0 * y * g0⁻¹ := by
    rw [map_mul, map_mul, map_inv, hg0, hyΦ]
    calc g0 * canonicalRep (coxeterSystem .F4) L w * y *
          (g0 * canonicalRep (coxeterSystem .F4) L w)⁻¹
        = g0 * (canonicalRep (coxeterSystem .F4) L w * y *
            (canonicalRep (coxeterSystem .F4) L w)⁻¹) * g0⁻¹ := by group
      _ = g0 * y * g0⁻¹ := by rw [hn]
  obtain ⟨c, hc⟩ := exists_rational_of_fixed_F4 Fr hFr hy2C hy2Φ
  have hι_inj : ∀ a b : ModGL .F4 K, baseChangeGL (algebraMap K L) a =
      baseChangeGL (algebraMap K L) b → a = b := fun a b h => baseChangeGL_injective _ h
  have hcE : c ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.1 (hEin x hx)
    have htx' : g0 * t * g0⁻¹ = baseChangeGL (algebraMap K L) (x : ModGL .F4 K) := htx
    have htp : t ^ p = 1 := by
      have h1 : (g0 * t * g0⁻¹) ^ p = 1 := by
        rw [htx', ← map_pow]
        have : ((x : ModGL .F4 K)) ^ p = 1 := congrArg Subtype.val (hE.2 x hx)
        rw [this, map_one]
      rw [conj_pow] at h1
      calc t ^ p = g0⁻¹ * (g0 * t ^ p * g0⁻¹) * g0 := by group
        _ = 1 := by rw [h1]; group
    have hcomm := ExcFramesHalf.commute_rootSL2_of_mem_twistedTorus (q := Nat.card K) hFr hp hp2
      hpq hβ hwβ ht htp (Matrix.SpecialLinearGroup.map (algebraMap K L) b)
    rw [hy] at hcomm
    have h3 : baseChangeGL (algebraMap K L) (x : ModGL .F4 K) *
        baseChangeGL (algebraMap K L) (c : ModGL .F4 K) =
        baseChangeGL (algebraMap K L) (c : ModGL .F4 K) *
          baseChangeGL (algebraMap K L) (x : ModGL .F4 K) := by
      rw [hc, ← htx']
      calc g0 * t * g0⁻¹ * (g0 * y * g0⁻¹) = g0 * (t * y) * g0⁻¹ := by group
        _ = g0 * (y * t) * g0⁻¹ := by rw [hcomm]
        _ = g0 * y * g0⁻¹ * (g0 * t * g0⁻¹) := by group
    have h4 : (x : ModGL .F4 K) * (c : ModGL .F4 K) =
        (c : ModGL .F4 K) * (x : ModGL .F4 K) := by
      apply hι_inj
      rw [map_mul, map_mul]
      exact h3
    exact Subtype.ext h4
  have hcp : c ^ p = 1 := by
    apply Subtype.ext
    apply hι_inj
    rw [Subgroup.coe_pow, map_pow, hc, hy2p, Subgroup.coe_one, map_one]
  have hcEmem : c ∈ E := hSC c hcE hcp
  obtain ⟨t', ht', htc⟩ := Subgroup.mem_map.1 (hEin c hcEmem)
  have htc' : g0 * t' * g0⁻¹ = baseChangeGL (algebraMap K L) (c : ModGL .F4 K) := htc
  rw [hc] at htc'
  have hty : t' = y := by
    calc t' = g0⁻¹ * (g0 * t' * g0⁻¹) * g0 := by group
      _ = g0⁻¹ * (g0 * y * g0⁻¹) * g0 := by rw [htc']
      _ = y := by group
  rw [hty] at ht'
  have hcommA : ∀ A : SL2 L,
      rootSL2 .F4 L β (Matrix.SpecialLinearGroup.map (algebraMap K L) b * A) =
        rootSL2 .F4 L β (A * Matrix.SpecialLinearGroup.map (algebraMap K L) b) := by
    intro A
    have := ExcFramesHalf.commute_rootSL2_of_mem_twistedTorus (q := Nat.card K) hFr hp hp2
      hpq hβ hwβ ht' hyp A
    rw [← hy] at this
    rw [map_mul, map_mul]
    exact this
  have hbL1 : Matrix.SpecialLinearGroup.map (algebraMap K L) b = 1 := by
    refine ExcFramesHalf.eq_one_of_commute_uSL_vSL_charTwo ?_ ?_
    · exact (rootSL2_injective_of_field β (hcommA (uSL 1)))
    · exact (rootSL2_injective_of_field β (hcommA (vSL 1)))
  have hb1 : b = 1 := by
    apply ExcFramesHalf.map_specialLinearGroup_injective (algebraMap K L)
    rw [hbL1, map_one]
  rw [hb1, orderOf_one] at hb
  exact hp.one_lt.ne hb

theorem card_ge_of_toral_F4 (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (E : Subgroup (adjointGroup .F4 K)) (hE : IsElemAbelian 3 E)
    (htor : ∃ g ∈ adjointGroup .F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g ∈ torusGroup .F4 (AlgebraicClosure K))
    (hcard : 3 ^ 3 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ 3 = 1 → x ∈ E) :
    3 ^ 4 ≤ Nat.card E := by
  classical
  have hpq : 3 ∣ Nat.card K + 1 := by norm_num [hK]
  have hpK : ¬ 3 ∣ Nat.card K := by norm_num [hK]
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hEin⟩ :=
    ExcFramesHalf.exists_langTorus_of_toral (p := 3) Nat.prime_three K hpK E hE htor
  have hcount := natCard_eq_torsion_F4 (p := 3) Nat.prime_three (by norm_num) E hE hSC w Fr hFr
    g0 hg0C hg0 hEin
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hcard2 := ExcFramesHalf.natCard_twistedTorus_pTorsion (L := AlgebraicClosure K)
    (τ := .F4) (ℓ := 2) Nat.prime_two Fr hFr (p := 3) Nat.prime_three (by norm_num) w
  have hq : ((Nat.card K : ℕ) : ZMod 3) = -1 := by
    have h0 : ((Nat.card K + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  rw [hq] at hcard2
  have hE' := hcount.trans hcard2
  by_contra hlt
  push Not at hlt
  obtain ⟨β, hβ, hwβ⟩ := halfMaxFixedRoot_F4_three w (hE' ▸ hcard) (hE' ▸ hlt)
  exact false_of_fixed_root_F4 (p := 3) Nat.prime_three (by norm_num) hpq E hE hSC w Fr hFr
    g0 hg0C hg0 hEin hβ hwβ

theorem isEmpty_langPlaneData_of_selfCentralizing (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ 3 = 1 → x ∈ E) :
    IsEmpty (LangPlaneData .F4 K E) := by
  refine ⟨fun D => ?_⟩
  let E' : Subgroup (adjointGroup .F4 K) := E.map (MulAut.conj D.c).toMonoidHom
  have hE' : IsElemAbelian 3 E' := TableB.isElemAbelian_map hE _
  have hcard' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj D.c).injective
  have hSC' : ∀ x ∈ Subgroup.centralizer (E' : Set (adjointGroup .F4 K)), x ^ 3 = 1 → x ∈ E' := by
    intro x hx hx3
    have huc : D.c⁻¹ * x * D.c ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he' : D.c * e * D.c⁻¹ ∈ E' :=
        Subgroup.mem_map_of_mem (MulAut.conj D.c).toMonoidHom he
      have hcomm := (Subgroup.mem_centralizer_iff.1 hx) (D.c * e * D.c⁻¹) he'
      calc e * (D.c⁻¹ * x * D.c)
          = D.c⁻¹ * ((D.c * e * D.c⁻¹) * x) * D.c := by group
        _ = D.c⁻¹ * (x * (D.c * e * D.c⁻¹)) * D.c := by rw [hcomm]
        _ = (D.c⁻¹ * x * D.c) * e := by group
    have hu3 : (D.c⁻¹ * x * D.c) ^ 3 = 1 := by
      have := conj_pow (a := D.c⁻¹) (b := x) (i := 3)
      rw [inv_inv] at this
      rw [this, hx3]
      group
    have huE : D.c⁻¹ * x * D.c ∈ E := hSC _ huc hu3
    have hxmem : D.c * (D.c⁻¹ * x * D.c) * D.c⁻¹ ∈ E' :=
      Subgroup.mem_map_of_mem (MulAut.conj D.c).toMonoidHom huE
    convert hxmem using 1
    group
  have htor : ∃ g ∈ adjointGroup .F4 (AlgebraicClosure K), ∀ x ∈ E',
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g ∈
        torusGroup .F4 (AlgebraicClosure K) := by
    refine ⟨D.g0, D.hg0C, ?_⟩
    intro x' hx'
    obtain ⟨x, hx, hxdef⟩ := Subgroup.mem_map.1 hx'
    obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.1 (D.hc x hx)
    have htx' : D.g0 * t * D.g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((D.c * x * D.c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) := htx
    have hconj : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x' : adjointGroup .F4 K) : ModGL .F4 K) * D.g0 = t := by
      rw [← hxdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← htx']
      group
    rw [hconj]
    exact (mem_twistedTorusOf.1 ht).1
  have hcard3 : 3 ^ 3 ≤ Nat.card E' := by
    rw [hcard']
    exact le_of_eq hcard.symm
  have h34 := card_ge_of_toral_F4 K hK E' hE' htor hcard3 hSC'
  rw [hcard'.trans hcard] at h34
  exact absurd h34 (by norm_num)

end Count

end CFSG.StandardType.HalfMaxF4
