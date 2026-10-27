module

public import CFSG.LocalAnalysis.StandardType.GGTorusE6RelativeLang
public import CFSG.LocalAnalysis.StandardType.GGTorusE6RelativeWeyl
public import CFSG.LocalAnalysis.StandardType.GGTorusE6Relative
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeLang
public import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplitTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenRoot
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.RankThree.PartOne.KE.CTLang

public noncomputable section

namespace CFSG.StandardType.E6RelativeLangWeyl

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.CentralCover

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {p : ℕ} {E : Subgroup (adjointGroup .E6 K)}
variable (F : ExcFrame .E6 K p E)

theorem F_w_eq_e6W0 (hlong : ExcIsLongest .E6 F.w) :
    F.w = CFSG.RankThree.Lattice.e6W0 := by
  have hgg : F.w = ggKGEp_w0 .E6 := ggKGEp_eq_w0_of_longest hlong
  have hrev : ReversesSigns (CFSG.RankThree.Lattice.e6W0 : WeylGroup TwistTag.E6.tag) := by
    intro α hα hpos
    let α' : Fin Tag.E6.rank → ℤ := fun i =>
      α (Fin.cast (by rfl : Tag.E6.rank = TwistTag.E6.tag.rank) i)
    have hαeq : α' = α := by
      funext i
      exact congrArg α (Fin.ext rfl)
    have h := CFSG.RankThree.Lattice.e6W0_smul α'
    rw [hαeq] at h
    rw [h, height_neg]
    change -height (permLattice TwistTag.E6.perm α) < 0
    have hh : height (permLattice TwistTag.E6.perm α) = height α :=
      CFSG.HardMathSupport.Malle.E27Lie.ExcCross.height_permLattice6 α
    linarith
  exact hgg.trans (ReversesSigns.eq (ggKGEp_w0_reversesSigns_E6) hrev)

theorem orbitReflection_mem_relWeyl (a : Fin Tag.F4.rank) :
    TwistTag.E6.orbitReflection a ∈ relWeylTwist TwistTag.E6 :=
  TwistTag.E6.orbitReflection_mem a

theorem exists_nativeRep (hlong : ExcIsLongest .E6 F.w)
    (v : WeylGroup Tag.E6) (hv : v ∈ relWeylTwist TwistTag.E6)
    (hv2 : v * v = 1) :
    ∃ n : adjointGroup .E6 K,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (n : ModGL .E6 K) =
        F.D.g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v *
          F.D.g0⁻¹ := by
  classical
  let L := AlgebraicClosure K
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  haveI : CharP L 2 := charP_of_injective_algebraMap
    (algebraMap K L).injective 2
  have hFr_bij : Function.Bijective Fr :=
    frobenius_bijective (k := K) (L := L) Fr hFr
  set σ : L ≃+* L := RingEquiv.ofBijective Fr hFr_bij with hσdef
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hmul : ∀ a b : WeylGroup Tag.E6,
      canonicalRep (coxeterSystem Tag.E6) L (a * b) =
        canonicalRep (coxeterSystem Tag.E6) L a *
          canonicalRep (coxeterSystem Tag.E6) L b :=
    fun a b => CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo
      (τ := Tag.E6) (R := L) a b
  have hFr_canon : ∀ w : WeylGroup Tag.E6,
      Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem Tag.E6) L w) =
        canonicalRep (coxeterSystem Tag.E6) L w :=
    fun w => by
      simpa only [hσ] using entrywise_canonicalRep (τ := Tag.E6) σ w
  have hinv : ∀ a : WeylGroup Tag.E6,
      canonicalRep (coxeterSystem Tag.E6) L a⁻¹ =
        (canonicalRep (coxeterSystem Tag.E6) L a)⁻¹ := by
    intro a
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hmul, inv_mul_cancel, canonicalRep_one]
  have hg0 : Units.map (entrywiseHom Fr) F.D.g0 =
      F.D.g0 * canonicalRep (coxeterSystem Tag.E6) L F.w := by
    rw [← hΦ, F.D.lang, F.n_eq]
  have hcent : v * F.w = F.w * v := by
    have hvcent : v ∈ Subgroup.centralizer
        ({CFSG.RankThree.Lattice.e6W0} : Set (WeylGroup Tag.E6)) := by
      rw [CFSG.StandardType.ExcFrames.E6QPlusThree.centralizer_e6W0]
      exact hv
    have h := (Subgroup.mem_centralizer_singleton_iff.mp hvcent)
    rw [F_w_eq_e6W0 F hlong]
    exact h
  let y : ModGL .E6 L :=
    F.D.g0 * canonicalRep (coxeterSystem Tag.E6) L v * F.D.g0⁻¹
  have hyC : y ∈ adjointGroup .E6 L :=
    mul_mem (mul_mem F.D.g0_mem (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) L v))
      (inv_mem F.D.g0_mem)
  have hyFix : Units.map (entrywiseHom Fr) y = y := by
    have hwv : (F.w * v) * F.w⁻¹ = v := by rw [← hcent]; group
    have hkey : canonicalRep (coxeterSystem Tag.E6) L F.w *
        canonicalRep (coxeterSystem Tag.E6) L v *
        (canonicalRep (coxeterSystem Tag.E6) L F.w)⁻¹ =
        canonicalRep (coxeterSystem Tag.E6) L v := by
      rw [← hinv, ← hmul, ← hmul, hwv]
    calc Units.map (entrywiseHom Fr) y
        = (F.D.g0 * canonicalRep (coxeterSystem Tag.E6) L F.w) *
            canonicalRep (coxeterSystem Tag.E6) L v *
            (F.D.g0 * canonicalRep (coxeterSystem Tag.E6) L F.w)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hg0, hFr_canon v]
      _ = y := by
        rw [show (F.D.g0 * canonicalRep (coxeterSystem Tag.E6) L F.w) *
              canonicalRep (coxeterSystem Tag.E6) L v *
              (F.D.g0 * canonicalRep (coxeterSystem Tag.E6) L F.w)⁻¹ =
            F.D.g0 * (canonicalRep (coxeterSystem Tag.E6) L F.w *
              canonicalRep (coxeterSystem Tag.E6) L v *
              (canonicalRep (coxeterSystem Tag.E6) L F.w)⁻¹) * F.D.g0⁻¹ by group,
          hkey]
  have hy2 : y ^ 2 = 1 := by
    have hnv : canonicalRep (coxeterSystem Tag.E6) L v *
        canonicalRep (coxeterSystem Tag.E6) L v = 1 := by
      rw [← hmul v v, hv2, canonicalRep_one]
    change (F.D.g0 * canonicalRep (coxeterSystem Tag.E6) L v * F.D.g0⁻¹) ^ 2 = 1
    rw [conj_pow, pow_two, hnv, mul_one, mul_inv_cancel]
  let X : Subgroup (ModGL .E6 L) := Subgroup.zpowers y
  have hXfin : Finite X := by
    apply finite_zpowers.2
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, hy2⟩
  haveI : Finite X := hXfin
  have hXC : X ≤ adjointGroup .E6 L := Subgroup.zpowers_le.2 hyC
  have hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [map_zpow, hyFix]
  letI : Fintype K := Fintype.ofFinite K
  have hEven : Even (Nat.card K) := by
    rw [Nat.even_iff, Nat.card_eq_fintype_card]
    exact FiniteField.even_card_of_char_two (ringChar.eq K 2)
  have hOdd : Odd (Nat.card K - 1) := by
    rw [Nat.odd_iff]
    rcases hEven with ⟨k, hk⟩
    have h2 : 2 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  have hcop : Nat.Coprime 2 (Nat.card K - 1) :=
    Nat.coprime_two_left.mpr hOdd
  have hmX : Nat.card X ∣ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hy2
  have hXle : X ≤ (adjointGroup .E6 K).map
      (baseChangeGL (algebraMap K L)) :=
    finite_fixed_subgroup_rational_card_dvd (τ := .E6) 3 (Or.inl ⟨rfl, rfl⟩)
      Fr hFr X hXC hXF (m := 2) hcop hmX
  obtain ⟨n, hnmem, hnbase⟩ := hXle (Subgroup.mem_zpowers y)
  exact ⟨⟨n, hnmem⟩, hnbase⟩

noncomputable def nNative (hlong : ExcIsLongest .E6 F.w) (a : Fin Tag.F4.rank) :
    adjointGroup .E6 K :=
  Classical.choose (exists_nativeRep F hlong (TwistTag.E6.orbitReflection a)
    (orbitReflection_mem_relWeyl a) (by
      let a' : Fin TwistTag.E6.foldedTag.rank := Fin.cast (by rfl) a
      have h : TwistTag.E6.orbitReflection a' *
          TwistTag.E6.orbitReflection a' = 1 :=
        TwistTag.E6.orbitReflection_mul_self a'
      have ha : a' = a := Fin.ext rfl
      exact (show (TwistTag.E6.orbitReflection a * TwistTag.E6.orbitReflection a :
        WeylGroup Tag.E6) = 1 from by simpa [ha] using h)))

theorem nNative_spec (hlong : ExcIsLongest .E6 F.w) (a : Fin Tag.F4.rank) :
    baseChangeGL (algebraMap K (AlgebraicClosure K))
        (nNative F hlong a : ModGL .E6 K) =
      F.D.g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        (TwistTag.E6.orbitReflection a) * F.D.g0⁻¹ :=
  Classical.choose_spec (exists_nativeRep F hlong (TwistTag.E6.orbitReflection a)
    (orbitReflection_mem_relWeyl a) (by
      let a' : Fin TwistTag.E6.foldedTag.rank := Fin.cast (by rfl) a
      have h : TwistTag.E6.orbitReflection a' *
          TwistTag.E6.orbitReflection a' = 1 :=
        TwistTag.E6.orbitReflection_mul_self a'
      have ha : a' = a := Fin.ext rfl
      exact (show (TwistTag.E6.orbitReflection a * TwistTag.E6.orbitReflection a :
        WeylGroup Tag.E6) = 1 from by simpa [ha] using h)))

def pCoord (s : Fin Tag.F4.rank → ZMod p) : Fin Tag.F4.rank → ZMod p :=
  fun k => ∑ i, ((Tag.F4.cartan (f4FoldedIndex k) i : ℤ) : ZMod p) * s i

theorem twE6SplitTheta_apply_local {p : ℕ} [NeZero p]
    (s : Fin Tag.F4.rank → ZMod p) (i : Fin Tag.E6.rank) :
    ExcFrames.twE6SplitTheta p s i = s (f4FoldedIndex (e6IndexToF4 i)) := by
  show ((TwistTag.foldMap TwistTag.E6 (TableBExc.liftMod .F4 p s) i : ℤ) : ZMod p) = _
  have h := TwistTag.foldMap_apply_apply TwistTag.E6 (TableBExc.liftMod .F4 p s) i
  rw [h]
  change (((s (TwistTag.E6.orbitIndex i)).val : ℤ) : ZMod p) = _
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  congr 1
  fin_cases i <;> rfl

def pTupleFn (hp : p.Prime) (ζ : (AlgebraicClosure K)ˣ)
    (hζ : ζ ^ p = 1) (hpq : p ∣ Nat.card K + 1)
    (s : Fin Tag.F4.rank → ZMod p) :
    Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  refine fun k => ⟨TableBExc.E6Three.zetaVec ζ hζ (pCoord (p := p) s) k, ?_⟩
  apply (mem_rootsOfUnity _ _).mpr
  rw [TableBExc.E6Three.zetaVec_apply]
  obtain ⟨d, hd⟩ := hpq
  calc
    (ζ ^ (pCoord (p := p) s k).val) ^ (Nat.card K + 1) =
        (ζ ^ (Nat.card K + 1)) ^ (pCoord (p := p) s k).val := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ac_rfl
    _ = ((ζ ^ p) ^ d) ^ (pCoord (p := p) s k).val := by
      rw [hd, pow_mul]
    _ = 1 := by rw [hζ, one_pow, one_pow]

theorem pTupleFn_one (hp : p.Prime) (ζ : (AlgebraicClosure K)ˣ)
    (hζ : ζ ^ p = 1) (hpq : p ∣ Nat.card K + 1) :
    pTupleFn (K := K) (p := p) hp ζ hζ hpq 0 = 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  funext k
  apply Subtype.ext
  change TableBExc.E6Three.zetaVec ζ hζ (pCoord (p := p) 0) k = 1
  rw [TableBExc.E6Three.zetaVec_apply]
  simp [pCoord]

theorem pTupleFn_mul (hp : p.Prime) (ζ : (AlgebraicClosure K)ˣ)
    (hζ : ζ ^ p = 1) (hpq : p ∣ Nat.card K + 1)
    (s t : Fin Tag.F4.rank → ZMod p) :
    pTupleFn (K := K) (p := p) hp ζ hζ hpq (s + t) =
      pTupleFn (K := K) (p := p) hp ζ hζ hpq s *
        pTupleFn (K := K) (p := p) hp ζ hζ hpq t := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  funext k
  apply Subtype.ext
  change TableBExc.E6Three.zetaVec ζ hζ (pCoord (p := p) (s + t)) k =
    TableBExc.E6Three.zetaVec ζ hζ (pCoord (p := p) s) k *
      TableBExc.E6Three.zetaVec ζ hζ (pCoord (p := p) t) k
  have hsum : pCoord (p := p) (s + t) = pCoord (p := p) s + pCoord (p := p) t := by
    funext j
    simp only [pCoord, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hsum, ExcFrames.zetaVec_add]
  rfl

theorem pTupleFn_pow (hp : p.Prime) (ζ : (AlgebraicClosure K)ˣ)
    (hζ : ζ ^ p = 1) (hpq : p ∣ Nat.card K + 1)
    (s : Fin Tag.F4.rank → ZMod p) :
    pTupleFn (K := K) (p := p) hp ζ hζ hpq s ^ p = 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  funext k
  apply Subtype.ext
  change (ζ ^ (pCoord (p := p) s k).val) ^ p = 1
  rw [← pow_mul, Nat.mul_comm _ p, pow_mul, hζ, one_pow]

@[expose] def pFrame (hp : p.Prime) (ζ : (AlgebraicClosure K)ˣ)
    (_hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hpq : p ∣ Nat.card K + 1)
    (hlong : ExcIsLongest .E6 F.w) :
    Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .E6 K where
  toFun s := E6RelativeLang.phi F hlong (pTupleFn hp ζ hζ hpq s.toAdd)
  map_one' := by
    change E6RelativeLang.phi F hlong (pTupleFn hp ζ hζ hpq 0) = 1
    rw [pTupleFn_one]
    exact map_one (E6RelativeLang.phi F hlong)
  map_mul' s t := by
    change E6RelativeLang.phi F hlong (pTupleFn hp ζ hζ hpq (s.toAdd + t.toAdd)) = _
    rw [pTupleFn_mul]
    exact map_mul (E6RelativeLang.phi F hlong) _ _

@[simp] theorem pFrame_apply (hp : p.Prime) (ζ : (AlgebraicClosure K)ˣ)
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hpq : p ∣ Nat.card K + 1)
    (hlong : ExcIsLongest .E6 F.w) (s : Fin Tag.F4.rank → ZMod p) :
    pFrame F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd s) =
      E6RelativeLang.phi F hlong (pTupleFn hp ζ hζ hpq s) := rfl

theorem pFrame_mem (hp : p.Prime) (ζ : (AlgebraicClosure K)ˣ)
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hpq : p ∣ Nat.card K + 1)
    (hlong : ExcIsLongest .E6 F.w) (s : Multiplicative (Fin Tag.F4.rank → ZMod p)) :
    pFrame F hp ζ hζo hζ hpq hlong s ∈ E := by
  rw [E6RelativeLang.mem_E_iff_pow_p_mem_phi_range F hlong hpq]
  change (E6RelativeLang.phi F hlong (pTupleFn hp ζ hζ hpq s.toAdd)) ^ p = 1 ∧ _
  refine ⟨?_, ⟨_, rfl⟩⟩
  exact (map_pow (E6RelativeLang.phi F hlong) _ p).symm.trans
    ((congrArg (E6RelativeLang.phi F hlong) (pTupleFn_pow hp ζ hζ hpq s.toAdd)).trans
      (map_one (E6RelativeLang.phi F hlong)))

theorem frameDiag_twE6SplitTheta_eq_pTuple (hp : p.Prime) [NeZero p]
    (ζ : (AlgebraicClosure K)ˣ) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hpq : p ∣ Nat.card K + 1) (s : Fin Tag.F4.rank → ZMod p) :
    ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p s) =
      rootDiagUnit .E6 (E6RelativeLang.coordTuple (pTupleFn hp ζ hζ hpq s)) := by
  have hfc : ExcFrames.frameCoord Tag.E6 p (ExcFrames.twE6SplitTheta p s) =
      ExcFrames.twE6SplitTheta p (fun a => ∑ b, ((Tag.F4.cartan a b : ℤ) : ZMod p) * s b) := by
    exact CFSG.StandardType.TwE6SplitRootGen.frameCoord_twE6SplitTheta s
  change rootDiagUnit .E6
      (TableBExc.E6Three.zetaVec ζ hζ
        (ExcFrames.frameCoord Tag.E6 p (ExcFrames.twE6SplitTheta p s))) = _
  rw [hfc]
  congr 1
  funext i
  change ζ ^ ((ExcFrames.twE6SplitTheta p
    (fun a => ∑ b, ((Tag.F4.cartan a b : ℤ) : ZMod p) * s b)) i).val =
    ζ ^ (pCoord (p := p) s (e6IndexToF4 i)).val
  rw [twE6SplitTheta_apply_local]
  rfl

theorem pFrame_baseChange (hp : p.Prime) [NeZero p] (ζ : (AlgebraicClosure K)ˣ)
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hpq : p ∣ Nat.card K + 1)
    (hlong : ExcIsLongest .E6 F.w) (s : Multiplicative (Fin Tag.F4.rank → ZMod p)) :
    baseChangeGL (algebraMap K (AlgebraicClosure K))
        (pFrame F hp ζ hζo hζ hpq hlong s : ModGL .E6 K) =
      F.D.g0 * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p s.toAdd) * F.D.g0⁻¹ := by
  change baseChangeGL (algebraMap K (AlgebraicClosure K))
    (E6RelativeLang.phi F hlong (pTupleFn hp ζ hζ hpq s.toAdd) : ModGL .E6 K) = _
  exact (E6RelativeLang.phi_apply_baseChange F hlong (pTupleFn hp ζ hζ hpq s)).trans
    (congrArg (fun x : ModGL .E6 (AlgebraicClosure K) => F.D.g0 * x * F.D.g0⁻¹)
      (frameDiag_twE6SplitTheta_eq_pTuple hp ζ hζo hζ hpq s.toAdd).symm)

theorem pFrame_injective (hp : p.Prime) (hp5 : 5 ≤ p) (ζ : (AlgebraicClosure K)ˣ)
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hpq : p ∣ Nat.card K + 1)
    (hlong : ExcIsLongest .E6 F.w) :
    Function.Injective (pFrame F hp ζ hζo hζ hpq hlong) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro s t hst
  have hst' : pFrame F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd s.toAdd) =
      pFrame F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd t.toAdd) := by
    simpa using hst
  have hbase := congrArg (fun x : adjointGroup .E6 K =>
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K)) hst'
  have hbase' := (pFrame_baseChange F hp ζ hζo hζ hpq hlong s).symm.trans
    (hbase.trans (pFrame_baseChange F hp ζ hζo hζ hpq hlong t))
  have hfd : ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
      (ExcFrames.twE6SplitTheta p s.toAdd) =
      ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p t.toAdd) :=
    mul_left_cancel (mul_right_cancel hbase')
  have hdet : IsUnit ((TwistTag.E6.tag.symmetrizedCartan.det : ℤ) : ZMod p) := by
    have hsymm : TwistTag.E6.tag.symmetrizedCartan = TwistTag.E6.tag.cartan := by
      rw [Tag.symmetrizedCartan]
      exact one_mul _
    have h3 : TwistTag.E6.tag.cartan.det = 3 := det_cartan_E6
    rw [hsymm, h3, isUnit_iff_ne_zero, Ne, show ((3 : ℤ) : ZMod p) = ((3 : ℕ) : ZMod p) by simp,
      ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  exact Multiplicative.toAdd.injective (ExcFrames.twE6SplitTheta_injective
    (ExcFrames.frameDiag_injective (τ := Tag.E6) hζo hζ hdet hfd))

theorem pFrame_range (hp : p.Prime) (hp5 : 5 ≤ p) (ζ : (AlgebraicClosure K)ˣ)
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hpq : p ∣ Nat.card K + 1)
    (hlong : ExcIsLongest .E6 F.w) :
    (pFrame F hp ζ hζo hζ hpq hlong).range = E := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    exact pFrame_mem F hp ζ hζo hζ hpq hlong s
  · intro x hx
    rw [E6RelativeLang.mem_E_iff_pow_p_mem_phi_range F hlong hpq] at hx
    obtain ⟨hxp, ha⟩ := hx
    obtain ⟨a, rfl⟩ := ha
    have hap : a ^ p = 1 := by
      apply E6RelativeLang.phi_injective F hlong
      rw [map_pow, hxp, map_one]
    have hcp : ∀ i, E6RelativeLang.coordTuple a i ^ p = 1 := by
      intro i
      have h := congrArg (fun f => ((f (e6IndexToF4 i) :
          rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ)) hap
      exact h
    have h05 : E6RelativeLang.coordTuple a ⟨0, by decide⟩ =
        E6RelativeLang.coordTuple a ⟨5, by decide⟩ := rfl
    have h24 : E6RelativeLang.coordTuple a ⟨2, by decide⟩ =
        E6RelativeLang.coordTuple a ⟨4, by decide⟩ := rfl
    obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_twE6SplitTheta_eq
      (K := AlgebraicClosure K) (p := p) hp5 hζo hζ hcp h05 h24
    refine ⟨Multiplicative.ofAdd s, ?_⟩
    change E6RelativeLang.phi F hlong (pTupleFn hp ζ hζ hpq s) = E6RelativeLang.phi F hlong a
    apply congrArg (E6RelativeLang.phi F hlong)
    have hct : E6RelativeLang.coordTuple
        (pTupleFn (K := K) (p := p) hp ζ hζ hpq s) =
        E6RelativeLang.coordTuple a := by
      apply rootDiagUnit_injective
      exact (frameDiag_twE6SplitTheta_eq_pTuple hp ζ hζo hζ hpq s).symm.trans hs
    have htuple : pTupleFn (K := K) (p := p) hp ζ hζ hpq s = a :=
      E6RelativeLang.coordMap_injective hct
    rw [htuple]

theorem nNative_frameConj (hp : p.Prime) (hp5 : 5 ≤ p)
    (ζ : (AlgebraicClosure K)ˣ) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hpq : p ∣ Nat.card K + 1) (hlong : ExcIsLongest .E6 F.w)
    (a : Fin Tag.F4.rank) (s : Fin Tag.F4.rank → ZMod p) :
    nNative F hlong a * pFrame F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd s) *
        (nNative F hlong a)⁻¹ =
      pFrame F hp ζ hζo hζ hpq hlong
        (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 p (simple Tag.F4 a) s)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv,
    nNative_spec F hlong a, pFrame_baseChange F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd s),
    pFrame_baseChange F hp ζ hζo hζ hpq hlong
      (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 p (simple Tag.F4 a) s))]
  have hfold : foldedWeylEquiv TwistTag.E6
      ⟨TwistTag.E6.orbitReflection a, TwistTag.E6.orbitReflection_mem a⟩ =
      simple Tag.F4 a := foldedWeylEquiv_orbitReflection TwistTag.E6 a
  have hact : TableBExc.torusAct Tag.E6 p (TwistTag.E6.orbitReflection a)
      (ExcFrames.twE6SplitTheta p s) =
      ExcFrames.twE6SplitTheta p (TableBExc.torusAct Tag.F4 p (simple Tag.F4 a) s) := by
    have h := ExcFrames.torusAct_twE6SplitTheta
      ⟨TwistTag.E6.orbitReflection a, TwistTag.E6.orbitReflection_mem a⟩ s
    have h' : TableBExc.torusAct Tag.E6 p (TwistTag.E6.orbitReflection a)
        (ExcFrames.twE6SplitTheta p s) =
        ExcFrames.twE6SplitTheta p (TableBExc.torusAct Tag.F4 p
          (foldedWeylEquiv TwistTag.E6
            ⟨TwistTag.E6.orbitReflection a, TwistTag.E6.orbitReflection_mem a⟩) s) := h
    rw [hfold] at h'
    exact h' 
  have hcanon : canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        (TwistTag.E6.orbitReflection a) *
      ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p s) *
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        (TwistTag.E6.orbitReflection a))⁻¹ =
      ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p (TableBExc.torusAct Tag.F4 p (simple Tag.F4 a) s)) :=
    (ExcFrames.canonicalRep_conj_frameDiag (τ := Tag.E6) ζ hζ
      (TwistTag.E6.orbitReflection a) (ExcFrames.twE6SplitTheta p s)).trans
        (congrArg (ExcFrames.frameDiag (τ := Tag.E6) ζ hζ) hact)
  calc
    (F.D.g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        (TwistTag.E6.orbitReflection a) * F.D.g0⁻¹) *
      (F.D.g0 * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p s) * F.D.g0⁻¹) *
      (F.D.g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        (TwistTag.E6.orbitReflection a) * F.D.g0⁻¹)⁻¹ =
      F.D.g0 * (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        (TwistTag.E6.orbitReflection a) *
        ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
          (ExcFrames.twE6SplitTheta p s) *
        (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
          (TwistTag.E6.orbitReflection a))⁻¹) * F.D.g0⁻¹ := by group
    _ = F.D.g0 * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p
          (TableBExc.torusAct Tag.F4 p (simple Tag.F4 a) s)) * F.D.g0⁻¹ := by
      rw [hcanon]

theorem nNative_phiConj (hlong : ExcIsLongest .E6 F.w) (j : Fin Tag.F4.rank)
    (a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)) :
    nNative F hlong (f4FoldedIndex j) * E6RelativeLang.phi F hlong a *
        (nNative F hlong (f4FoldedIndex j))⁻¹ =
      E6RelativeLang.phi F hlong a *
        (E6RelativeLang.phi F hlong
          (corTuple CartanMatrix.F₄.transpose j (a j)))⁻¹ :=
  E6RelativeLang.conj_phi_of_baseChange_orbitReflection F hlong j
    (nNative_spec F hlong (f4FoldedIndex j)) a

theorem normalizer_frame_action (hp : p.Prime) (hp5 : 5 ≤ p)
    (ζ : (AlgebraicClosure K)ˣ) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hpq : p ∣ Nat.card K + 1) (hlong : ExcIsLongest .E6 F.w)
    (g : adjointGroup .E6 K)
    (hg : g ∈ Subgroup.normalizer (E : Set (adjointGroup .E6 K))) :
    ∃ u : WeylGroup Tag.F4, ∀ s : Fin Tag.F4.rank → ZMod p,
      g * pFrame F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd s) * g⁻¹ =
        pFrame F hp ζ hζo hζ hpq hlong
          (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 p u s)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨v, hvcent, hconj⟩ := ggKGExc_normalizer_weyl (hτ := Or.inl rfl)
    hp (by omega) (fun _ => hp5) F (Or.inr ⟨hpq, hlong⟩) hg
  have hvrel : v ∈ relWeylTwist TwistTag.E6 := by
    rw [← ExcFrames.E6QPlusThree.centralizer_e6W0, ← F_w_eq_e6W0 F hlong]
    exact hvcent
  let u : WeylGroup Tag.F4 := foldedWeylEquiv TwistTag.E6 ⟨v, hvrel⟩
  refine ⟨u, fun s => ?_⟩
  let es := pFrame F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd s)
  have hes : es ∈ E := pFrame_mem F hp ζ hζo hζ hpq hlong _
  have hc := hconj es hes
  have hback : baseChangeGL (algebraMap K (AlgebraicClosure K))
      (g * es * g⁻¹ : ModGL .E6 K) =
      F.D.g0 * (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v *
        (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (es : ModGL .E6 K) * F.D.g0) *
        (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v)⁻¹) * F.D.g0⁻¹ := by
    calc
      _ = F.D.g0 * (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (g * es * g⁻¹ : ModGL .E6 K) * F.D.g0) * F.D.g0⁻¹ := by group
      _ = _ := congrArg (fun z => F.D.g0 * z * F.D.g0⁻¹) hc
  have hbase : baseChangeGL (algebraMap K (AlgebraicClosure K))
      (es : ModGL .E6 K) = F.D.g0 * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
      (ExcFrames.twE6SplitTheta p s) * F.D.g0⁻¹ :=
    pFrame_baseChange F hp ζ hζo hζ hpq hlong (Multiplicative.ofAdd s)
  have htor : TableBExc.torusAct Tag.E6 p v (ExcFrames.twE6SplitTheta p s) =
      ExcFrames.twE6SplitTheta p (TableBExc.torusAct Tag.F4 p u s) :=
    ExcFrames.torusAct_twE6SplitTheta ⟨v, hvrel⟩ s
  have hcanon : canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v *
      ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p s) *
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v)⁻¹ =
      ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
        (ExcFrames.twE6SplitTheta p (TableBExc.torusAct Tag.F4 p u s)) :=
    (ExcFrames.canonicalRep_conj_frameDiag (τ := Tag.E6) ζ hζ v
      (ExcFrames.twE6SplitTheta p s)).trans
        (congrArg (ExcFrames.frameDiag (τ := Tag.E6) ζ hζ) htor)
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  calc
    _ = F.D.g0 * (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v *
      (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (es : ModGL .E6 K) * F.D.g0) *
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v)⁻¹) * F.D.g0⁻¹ := hback
    _ = F.D.g0 * (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v *
      ExcFrames.frameDiag (τ := Tag.E6) ζ hζ (ExcFrames.twE6SplitTheta p s) *
      (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v)⁻¹) * F.D.g0⁻¹ := by
        rw [hbase]
        group
    _ = F.D.g0 * ExcFrames.frameDiag (τ := Tag.E6) ζ hζ
      (ExcFrames.twE6SplitTheta p (TableBExc.torusAct Tag.F4 p u s)) * F.D.g0⁻¹ := by rw [hcanon]
    _ = _ := (pFrame_baseChange F hp ζ hζo hζ hpq hlong
      (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 p u s))).symm

theorem exists_markedWeyl_qplusLang (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) (hlong : ExcIsLongest .E6 F.w) :
    ∃ (n : Fin Tag.F4.rank → adjointGroup .E6 K) (ζ : (AlgebraicClosure K)ˣ),
      orderOf ζ = p ∧ ζ ^ p = 1 ∧
      (∀ (j : Fin Tag.F4.rank)
        (a : Fin Tag.F4.rank → rootsOfUnity (Nat.card K + 1) (AlgebraicClosure K)),
        n j * E6RelativeLang.phi F hlong a * (n j)⁻¹ =
          E6RelativeLang.phi F hlong a *
            (E6RelativeLang.phi F hlong
              (corTuple CartanMatrix.F₄.transpose j (a j)))⁻¹) ∧
      ∃ hnN : ∀ j, n j ∈ Subgroup.normalizer (E : Set (adjointGroup .E6 K)),
        ∃ eW : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer
            (⊤ : Subgroup ↥(adjointGroup .E6 K)) E),
          ∀ j : Fin Tag.F4.rank,
            (eW (CoxeterMatrix.F₄.simple j) : MulAut ↥E) =
              ggConjAut E (hnN j) := by
  classical
  let L := AlgebraicClosure K
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨ζ, hζprim⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := L) (ℓ := 2) (by norm_num) hp (by omega)
  have hζo : orderOf ζ = p := hζprim.eq_orderOf.symm
  have hζ : ζ ^ p = 1 := hζprim.pow_eq_one
  let n : Fin Tag.F4.rank → adjointGroup .E6 K := fun j =>
    nNative F hlong (f4FoldedIndex j)
  have hphi : ∀ (j : Fin Tag.F4.rank) (a : Fin Tag.F4.rank →
      rootsOfUnity (Nat.card K + 1) L),
      n j * E6RelativeLang.phi F hlong a * (n j)⁻¹ =
        E6RelativeLang.phi F hlong a *
          (E6RelativeLang.phi F hlong
            (corTuple CartanMatrix.F₄.transpose j (a j)))⁻¹ := fun j a =>
    nNative_phiConj F hlong j a
  obtain ⟨hnW, -, e, he⟩ := exists_markedWeyl_ggAutomizer (τ := Tag.F4)
    (p := p) (hp.odd_of_ne_two (by omega)) (E := E)
    (pFrame F hp ζ hζo hζ hpq hlong)
    (pFrame_injective F hp hp5 ζ hζo hζ hpq hlong)
    (pFrame_range F hp hp5 ζ hζo hζ hpq hlong)
    (fun j => nNative F hlong j)
    (fun j s => nNative_frameConj F hp hp5 ζ hζo hζ hpq hlong j s)
    (fun g hg => normalizer_frame_action F hp hp5 ζ hζo hζ hpq hlong g hg)
  let eW : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer
      (⊤ : Subgroup ↥(adjointGroup .E6 K)) E) :=
    ggF4Row_coxeterGroupEquiv.trans (E6RelativeWeyl.revWeyl.trans e)
  refine ⟨n, ζ, hζo, hζ, hphi, fun j => hnW (f4FoldedIndex j), eW, ?_⟩
  intro j
  change (e (E6RelativeWeyl.revWeyl
    (ggF4Row_coxeterGroupEquiv (CoxeterMatrix.F₄.simple j))) : MulAut ↥E) = _
  rw [ggF4Row_coxeterGroupEquiv_simple, E6RelativeWeyl.revWeyl_simple,
    E6RelativeWeyl.f4RevTag_eq_f4FoldedIndex]
  exact he (f4FoldedIndex j)

end CFSG.StandardType.E6RelativeLangWeyl
