module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBWeyl
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTw
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.LieType.Chevalley.FoldedWeylData
public import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBIrred
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.DefChar

section WeylRealize


private theorem perm_E6_symm : TwistTag.E6.perm.symm = TwistTag.E6.perm :=
  Equiv.ext fun i => by fin_cases i <;> rfl

private theorem permLattice_E6_invol (x : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm x) = x := by
  have h := permLattice_symm_permLattice TwistTag.E6.perm x
  rwa [perm_E6_symm] at h

private theorem twE6PhiTwoWeyl_smul_neg' (x : Fin TwistTag.E6.tag.rank → ℤ) :
    twE6PhiTwoWeyl • x = -permLattice TwistTag.E6.perm x := by
  have htomat : toMat TwistTag.E6.tag.rank twE6TwoMat =
      (-1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [twE6PhiTwoWeyl_smul, htomat, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem twE6PhiTwoWeyl_conj_weylTwist (v : WeylGroup TwistTag.E6.tag) :
    twE6PhiTwoWeyl * weylTwist TwistTag.E6 v * twE6PhiTwoWeyl⁻¹ = v := by
  have hinv : ∀ y : Fin TwistTag.E6.tag.rank → ℤ,
      twE6PhiTwoWeyl⁻¹ • y = -permLattice TwistTag.E6.perm y := by
    intro y
    rw [inv_smul_eq_iff, twE6PhiTwoWeyl_smul_neg', permLattice_neg, permLattice_E6_invol, neg_neg]
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, hinv, weylTwist_smul, twE6PhiTwoWeyl_smul_neg', perm_E6_symm,
    permLattice_neg, permLattice_E6_invol, smul_neg, neg_neg, permLattice_E6_invol]

theorem twistHom_conj_canonicalRep_twE6 {L : Type} [Field L] [CharP L 2] (Fr : L →+* L)
    {g₀ : ModGL TwistTag.E6.tag L}
    (hg₀ : twistHom TwistTag.E6 L Fr g₀ =
      g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6PhiTwoWeyl)
    (v : WeylGroup TwistTag.E6.tag) :
    twistHom TwistTag.E6 L Fr (g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L v * g₀⁻¹) =
      g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L v * g₀⁻¹ := by
  have hmul : ∀ a b : WeylGroup TwistTag.E6.tag,
      canonicalRep (coxeterSystem TwistTag.E6.tag) L (a * b) =
        canonicalRep (coxeterSystem TwistTag.E6.tag) L a *
          canonicalRep (coxeterSystem TwistTag.E6.tag) L b :=
    fun a b => RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo a b
  have hinv : ∀ a : WeylGroup TwistTag.E6.tag,
      canonicalRep (coxeterSystem TwistTag.E6.tag) L a⁻¹ =
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_left (by rw [← hmul, inv_mul_cancel, canonicalRep_one])
  have key : canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6PhiTwoWeyl *
      canonicalRep (coxeterSystem TwistTag.E6.tag) L (weylTwist TwistTag.E6 v) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6PhiTwoWeyl)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L v := by
    rw [← hinv, ← hmul, ← hmul, twE6PhiTwoWeyl_conj_weylTwist]
  rw [map_mul, map_mul, map_inv, hg₀, twistHom_canonicalRep, mul_inv_rev, ← key]
  group

theorem torusAct_simple (τ : Tag) {p : ℕ} [NeZero p] (i : Fin τ.rank) (x : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p (simple τ i) x =
      x - (∑ j, ((τ.cartan i j : ℤ) : ZMod p) * x j) • Pi.single i 1 := by
  funext k
  simp only [TableBExc.torusAct, simple_smul, reflect, TableBExc.redMod, TableBExc.liftMod,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp only [ZMod.natCast_zmod_val, ZMod.cast_id', id_eq]
  congr 2
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem torusAct_simple_E6 {p : ℕ} [NeZero p] (i : Fin 6) (s : Fin 6 → ZMod p) :
    TableBExc.torusAct Tag.E6 p (simple Tag.E6 i) s = TwE6TB.reflE6 p i s := by
  refine (torusAct_simple Tag.E6 i s).trans ?_
  show (s - (∑ j : Fin 6, ((Tag.E6.cartan i j : ℤ) : ZMod p) * s j) •
      (Pi.single i 1 : Fin 6 → ZMod p) : Fin 6 → ZMod p) = _
  rw [TwE6TB.reflE6]
  congr 2
  unfold TwE6TB.pairE6
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  congr 2
  fin_cases i <;> fin_cases j <;> rfl

theorem exists_langFrame_weyl {f p : ℕ} (hf : 1 ≤ f) [NeZero p]
    (K : Type) [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L 2] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    {ζ : Lˣ} (hζ : ζ ^ p = 1) {g₀ : ModGL TwistTag.E6.tag L}
    (hg₀C : g₀ ∈ adjointGroup TwistTag.E6.tag L)
    (hg₀ : twistHom TwistTag.E6 L Fr g₀ =
      g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6PhiTwoWeyl)
    (ι₀ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hbase : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      baseChangeGL (algebraMap K L) ((ι₀ (Multiplicative.ofAdd s) : _) : ModGL TwistTag.E6.tag K) =
        g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹) :
    ∃ m : WeylGroup TwistTag.E6.tag →* ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (∀ v, baseChangeGL (algebraMap K L) ((m v : _) : ModGL TwistTag.E6.tag K) =
        g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L v * g₀⁻¹) ∧
      ∀ v (s : Fin TwistTag.E6.tag.rank → ZMod p), m v * ι₀ (Multiplicative.ofAdd s) * (m v)⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct TwistTag.E6.tag p v s)) := by
  classical
  obtain ⟨hfinR, -, hder, ⟨k, hk⟩, -, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
      (ℓ := 2) (f := f) Nat.prime_two hf K hK σ hσ L Fr hFr
  set R' : Subgroup (ModGL TwistTag.E6.tag L) := twistedFixedGroup TwistTag.E6 L Fr with hR'
  set C' : Subgroup (ModGL TwistTag.E6.tag L) :=
    (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K L)) with hC'
  haveI : Finite R' := hfinR
  have hnormal : (C'.subgroupOf R').Normal := by
    have e : C'.subgroupOf R' = ⁅(⊤ : Subgroup R'), ⊤⁆ := by
      have h1 : ⁅R', R'⁆ = Subgroup.map R'.subtype ⁅(⊤ : Subgroup R'), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R'.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  let nHom : WeylGroup TwistTag.E6.tag →* ModGL TwistTag.E6.tag L :=
    MonoidHom.mk' (canonicalRep (coxeterSystem TwistTag.E6.tag) L)
      fun a b => RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo a b
  let X : WeylGroup TwistTag.E6.tag →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g₀).toMonoidHom.comp nHom
  have hX : ∀ v, X v = g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L v * g₀⁻¹ :=
    fun v => rfl
  have hXR : ∀ v, X v ∈ R' := by
    intro v
    rw [hX, mem_twistedFixedGroup_iff_twistHom]
    exact ⟨mul_mem (mul_mem hg₀C (canonicalRep_mem_adjointGroup _ L v)) (inv_mem hg₀C),
      twistHom_conj_canonicalRep_twE6 Fr hg₀ v⟩
  let Y : WeylGroup TwistTag.E6.tag →* R' := X.codRestrict R' hXR
  let H : Subgroup (WeylGroup TwistTag.E6.tag) := (C'.subgroupOf R').comap Y
  have hsimple : ∀ i, (coxeterSystem TwistTag.E6.tag).simple i ∈ H := by
    intro i
    have hy2 : (Y ((coxeterSystem TwistTag.E6.tag).simple i)) ^ 2 = 1 := by
      rw [← map_pow, sq, CoxeterSystem.simple_mul_simple_self, map_one]
    have hpow := Subgroup.pow_index_mem (C'.subgroupOf R') (Y ((coxeterSystem TwistTag.E6.tag).simple i))
    rw [hk] at hpow
    obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    rw [hj, pow_succ, pow_mul, hy2, one_pow, one_mul] at hpow
    exact hpow
  have htop : H = ⊤ := by
    rw [eq_top_iff, ← (coxeterSystem TwistTag.E6.tag).subgroup_closure_range_simple,
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hsimple i
  have hXC : ∀ v, X v ∈ C' := by
    intro v
    have hv : v ∈ H := htop ▸ Subgroup.mem_top v
    exact hv
  have hι : Function.Injective (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K L)) :=
    baseChangeGL_injective _
  let e := (graphFixedRootGroup TwistTag.E6 K σ).equivMapOfInjective
    (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K L)) hι
  let m : WeylGroup TwistTag.E6.tag →* ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    e.symm.toMonoidHom.comp (X.codRestrict C' hXC)
  have hm : ∀ v, baseChangeGL (algebraMap K L) ((m v : _) : ModGL TwistTag.E6.tag K) =
      g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L v * g₀⁻¹ := by
    intro v
    have h := congrArg Subtype.val (e.apply_symm_apply (X.codRestrict C' hXC v))
    rw [Subgroup.coe_equivMapOfInjective_apply] at h
    exact h
  refine ⟨m, hm, fun v s => ?_⟩
  apply Subtype.ext
  apply hι
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hm, hbase]
  calc g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L v * g₀⁻¹ *
        (g₀ * frameDiag (τ := TwistTag.E6.tag) ζ hζ s * g₀⁻¹) *
        (g₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L v * g₀⁻¹)⁻¹ =
      g₀ * (canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        frameDiag (τ := TwistTag.E6.tag) ζ hζ s *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) * g₀⁻¹ := by group
    _ = _ := by rw [canonicalRep_conj_frameDiag]

end WeylRealize

end ExcFrames

end CFSG.StandardType
