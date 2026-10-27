module

public import CFSG.LocalAnalysis.StandardType.GGF4TwoNTHalfCount

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG.Assembly CFSG.LieType.SeitzGeneration.ExcHighThree TableB CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.StandardType.TableBF4TwoTB

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem f4gen_exists_rational_of_fixed
    {K L : Type} [Field K] [Finite K] [CharP K 2]
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

private theorem f4gen_natCard_eq_torsion
    {K L : Type} [Field K] [Finite K] [CharP K 2]
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
    obtain ⟨c, hc⟩ := f4gen_exists_rational_of_fixed Fr hFr hyC hyΦ
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

private theorem f4gen_false_of_fixed_root
    {K L : Type} [Field K] [Finite K]
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
  obtain ⟨c, hc⟩ := f4gen_exists_rational_of_fixed Fr hFr hy2C hy2Φ
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

theorem f4_exists_rational_of_fixed
    {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {y : ModGL .F4 L} (hy : y ∈ adjointGroup .F4 L)
    (hyF : Units.map (entrywiseHom Fr) y = y) :
    ∃ c : adjointGroup .F4 K, baseChangeGL (algebraMap K L) (c : ModGL .F4 K) = y := by
  exact f4gen_exists_rational_of_fixed Fr hFr hy hyF

theorem f4_natCard_eq_torsion
    {K L : Type} [Field K] [Finite K] [CharP K 2]
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
  exact f4gen_natCard_eq_torsion hp hp2 E hE hSC w Fr hFr g0 hg0C hg0 hEin

theorem card_ge_of_toral_F4_gen
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : 3 ∣ Nat.card K + 1) (E : Subgroup (adjointGroup Tag.F4 K)) (hE : IsElemAbelian 3 E)
    (htor : ∃ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g ∈ torusGroup Tag.F4 (AlgebraicClosure K))
    (hcard : 3 ^ 3 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup Tag.F4 K)), x ^ 3 = 1 → x ∈ E) :
    3 ^ 4 ≤ Nat.card E := by
  classical
  have hpK : ¬ 3 ∣ Nat.card K := by
    intro h
    have h0 : ((Nat.card K : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    have h1 : ((Nat.card K + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h1
    rw [h0] at h1
    norm_num at h1
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hEin⟩ :=
    ExcFramesHalf.exists_langTorus_of_toral (p := 3) Nat.prime_three K hpK E hE htor
  have hcount := f4gen_natCard_eq_torsion (p := 3) Nat.prime_three (by norm_num) E hE hSC w Fr hFr
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
  obtain ⟨β, hβ, hwβ⟩ :=
    CFSG.StandardType.HalfMaxF4.halfMaxFixedRoot_F4_three w (hE' ▸ hcard) (hE' ▸ hlt)
  exact f4gen_false_of_fixed_root (p := 3) Nat.prime_three (by norm_num) hpq E hE hSC w Fr hFr
    g0 hg0C hg0 hEin hβ hwβ

end Irred937

end CFSG.StandardType

end
