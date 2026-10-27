module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeCentralizer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7Model
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame
public import CFSG.RankThree.Chevalley.SteinbergBTTrialitySplitPrimePlane
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate1952

public section

namespace CFSG.StandardType.OrdPToralLang

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.Open (IsElemAbelian)
open CFSG.RankThree.Chevalley (SteinbergBT.TrialityPlane.canonicalRep_conj_rootDiagUnit_of_neg)

theorem ggOrdPToralMax_of_conj_mem {C : Type*} [Group C] {p : ℕ} {V : Subgroup C}
    (hV : IsElemAbelian p V) (hconj : ∀ s : C, s ^ p = 1 → ∃ u : C, u * s * u⁻¹ ∈ V)
    (hmax : ∀ A : Subgroup C, IsElemAbelian p A → Nat.card A ≤ Nat.card V) :
    GGOrdPToralMax C p := by
  intro s hs
  obtain ⟨u, hu⟩ := hconj s hs
  refine ⟨V.map (MulAut.conj u⁻¹).toMonoidHom, OrdPInnerExc.isElemAbelian_map _ hV,
    ⟨_, hu, ?_⟩, fun A hA => ?_⟩
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective]
    exact hmax A hA

section Torsion

@[expose] noncomputable def torsionTorus (τ : Tag) (L : Type) [Field L] (p : ℕ) :
    Subgroup (ModGL τ L) :=
  ((rootDiagUnitHom τ L).comp (MonoidHom.compLeft (rootsOfUnity p L).subtype (Fin τ.rank))).range

theorem mem_torsionTorus_iff {τ : Tag} {L : Type} [Field L] {p : ℕ} {g : ModGL τ L} :
    g ∈ torsionTorus τ L p ↔ ∃ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) ∧ rootDiagUnit τ a = g := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨fun i => (b i : Lˣ), fun i => (mem_rootsOfUnity p (b i : Lˣ)).1 (b i).2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun i => ⟨a i, (mem_rootsOfUnity p (a i)).2 (ha i)⟩, rfl⟩

theorem isElemAbelian_torsionTorus {τ : Tag} {L : Type} [Field L] {p : ℕ} :
    IsElemAbelian p (torsionTorus τ L p) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨b, hb⟩ := x.2
    obtain ⟨c, hc⟩ := y.2
    apply Subtype.ext
    change (x : ModGL τ L) * y = y * x
    rw [← hb, ← hc, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨b, rfl⟩ := hx
    rw [← map_pow]
    have : b ^ p = 1 := funext fun i => Subtype.ext ((mem_rootsOfUnity p (b i : Lˣ)).1 (b i).2)
    rw [this, map_one]

theorem card_torsionTorus {τ : Tag}
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0) :
    Nat.card (torsionTorus τ L p) = p ^ τ.rank := by
  classical
  have hinj : Function.Injective
      ((rootDiagUnitHom τ L).comp (MonoidHom.compLeft (rootsOfUnity p L).subtype (Fin τ.rank))) :=
    fun b c h => funext fun i => Subtype.ext
      (congrFun (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective (τ := τ) h) i)
  have : NeZero (p : L) := ⟨hpL⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  have hcard : Nat.card (rootsOfUnity p L) = p := hζ.card_rootsOfUnity
  rw [torsionTorus, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun, hcard,
    Nat.card_eq_fintype_card, Fintype.card_fin]

end Torsion

section Frobenius

theorem entrywise_pow_rootDiagUnit
    {τ : Tag} {L : Type} [Field L] [CharP L 2] (e : ℕ)
    (a : Fin τ.rank → Lˣ) :
    Units.map (entrywiseHom (iterateFrobenius L 2 e)) (rootDiagUnit τ a) =
      rootDiagUnit τ a ^ (2 ^ e) := by
  change baseChangeGL (iterateFrobenius L 2 e) (rootDiagUnit τ a) = _
  rw [baseChangeGL_rootDiagUnit]
  have h : (fun i => Units.map (iterateFrobenius L 2 e).toMonoidHom (a i)) = a ^ (2 ^ e) := by
    funext i
    apply Units.ext
    change iterateFrobenius L 2 e (a i : L) = ((a ^ (2 ^ e)) i : L)
    rw [iterateFrobenius_def, Pi.pow_apply, Units.val_pow_eq_pow_val]
  rw [h]
  exact map_pow (rootDiagUnitHom τ L) a _

theorem frob_rootDiagUnit_eq
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {e p : ℕ}
    (hpe : p ∣ 2 ^ e - 1) {a : Fin τ.rank → Lˣ}
    (ha : ∀ i, a i ^ p = 1) :
    Units.map (entrywiseHom (iterateFrobenius L 2 e)) (rootDiagUnit τ a) = rootDiagUnit τ a := by
  rw [entrywise_pow_rootDiagUnit]
  obtain ⟨k, hk⟩ := hpe
  have hdp : rootDiagUnit τ a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall ha
  have h2 : 2 ^ e = p * k + 1 := by
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  rw [h2, pow_succ, pow_mul, hdp, one_pow, one_mul]

theorem twFrob_neg_rootDiagUnit_eq
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {w₀ : WeylGroup τ}
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {e p : ℕ} (hpe : p ∣ 2 ^ e + 1)
    {a : Fin τ.rank → Lˣ} (ha : ∀ i, a i ^ p = 1) :
    canonicalRep (coxeterSystem τ) L w₀ *
        Units.map (entrywiseHom (iterateFrobenius L 2 e)) (rootDiagUnit τ a) *
      (canonicalRep (coxeterSystem τ) L w₀)⁻¹ = rootDiagUnit τ a := by
  rw [entrywise_pow_rootDiagUnit, ← conj_pow,
    SteinbergBT.TrialityPlane.canonicalRep_conj_rootDiagUnit_of_neg hw₀, inv_pow]
  obtain ⟨k, hk⟩ := hpe
  have hdp : rootDiagUnit τ a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall ha
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ, hk, pow_mul, hdp, one_pow]

end Frobenius

section Fusion

theorem exists_conj_mem_torsionTorus
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hmon : MonomialToralAt τ p)
    {n : ModGL τ L} (hn : n ∈ adjointGroup τ L) {e : ℕ}
    (hfix : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) →
      frobTwistGL τ L 2 e n (rootDiagUnit τ a) = rootDiagUnit τ a)
    (hLang : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → ∀ c ∈ toralCentralizer τ L a,
      ∃ z ∈ toralCentralizer τ L a, z⁻¹ * frobTwistGL τ L 2 e n z = c)
    {s : ModGL τ L} (hs : s ∈ twModel n (iterateFrobenius L 2 e)) (hsp : s ^ p = 1) :
    ∃ u ∈ twModel n (iterateFrobenius L 2 e), u * s * u⁻¹ ∈ torsionTorus τ L p := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := frobTwistGL τ L 2 e n with hF
  have hFG : ∀ g ∈ adjointGroup τ L, F g ∈ adjointGroup τ L := fun g hg =>
    mul_mem (mul_mem hn (entrywiseFrobGL_mem 2 e hg)) (inv_mem hn)
  have hsG : s ∈ adjointGroup τ L := hs.1
  have hFs : F s = s := hs.2
  obtain ⟨g, hgG, hgT⟩ := exists_conj_torusGroup_of_pow_eq_one hp hmon (ℓ := 2) (Ne.symm hp2)
    halg hsG hsp
  obtain ⟨t, ht⟩ : ∃ t, t = g⁻¹ * s * g := ⟨_, rfl⟩
  rw [← ht] at hgT
  obtain ⟨a, ha⟩ := torusGroup_le_range_rootDiagUnitHom hgT
  have hta : t = rootDiagUnit τ a := ha.symm
  have htp : t ^ p = 1 := by
    rw [ht, show g⁻¹ * s * g = g⁻¹ * s * g⁻¹⁻¹ by rw [inv_inv], conj_pow, hsp, mul_one,
      mul_inv_cancel]
  have hap : ∀ i, a i ^ p = 1 := by
    have h1 : rootDiagUnitHom τ L (a ^ p) = rootDiagUnitHom τ L 1 := by
      rw [map_pow, map_one]
      change (rootDiagUnit τ a) ^ p = 1
      rw [← hta, htp]
    have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective (τ := τ) (K := L) h1
    intro i
    simpa using congrFun h2 i
  have hFt : F t = t := by rw [hta]; exact hfix a hap
  have hsg : s = g * t * g⁻¹ := by rw [ht]; group
  have h1 : F g * t * (F g)⁻¹ = g * t * g⁻¹ := by
    have := congrArg F hsg
    rw [map_mul, map_mul, map_inv, hFt, hFs] at this
    exact this.symm.trans hsg
  have hcc : g⁻¹ * F g ∈ toralCentralizer τ L a := by
    rw [mem_toralCentralizer]
    refine ⟨mul_mem (inv_mem hgG) (hFG g hgG), ?_⟩
    have h2 : (g⁻¹ * F g) * t = t * (g⁻¹ * F g) := by
      calc (g⁻¹ * F g) * t = g⁻¹ * (F g * t * (F g)⁻¹) * g * (g⁻¹ * F g) := by group
        _ = g⁻¹ * (g * t * g⁻¹) * g * (g⁻¹ * F g) := by rw [h1]
        _ = t * (g⁻¹ * F g) := by group
    rw [← hta]
    calc t * (g⁻¹ * F g) * t⁻¹ = (g⁻¹ * F g) * t * t⁻¹ := by rw [h2]
      _ = g⁻¹ * F g := by group
  obtain ⟨z, hz, hzc⟩ := hLang a hap _ hcc
  obtain ⟨hzG, hzt⟩ := mem_toralCentralizer.1 hz
  obtain ⟨u, hu⟩ : ∃ u, u = g * z⁻¹ := ⟨_, rfl⟩
  have hFu : F u = u := by
    have hFz : F z = z * (g⁻¹ * F g) := by rw [← hzc]; group
    rw [hu, map_mul, map_inv, hFz]
    group
  have huG : u ∈ adjointGroup τ L := hu ▸ mul_mem hgG (inv_mem hzG)
  have hut : u * t * u⁻¹ = s := by
    have hzt' : z * t = t * z := by
      have h3 : t * z * t⁻¹ = z := by rw [hta]; exact hzt
      calc z * t = (t * z * t⁻¹) * t := by rw [h3]
        _ = t * z := by group
    rw [hsg, hu]
    calc g * z⁻¹ * t * (g * z⁻¹)⁻¹ = g * (z⁻¹ * (t * z)) * g⁻¹ := by group
      _ = g * (z⁻¹ * (z * t)) * g⁻¹ := by rw [hzt']
      _ = g * t * g⁻¹ := by group
  have huW : u ∈ twModel n (iterateFrobenius L 2 e) := ⟨huG, hFu⟩
  refine ⟨u⁻¹, inv_mem huW, ?_⟩
  have : u⁻¹ * s * u⁻¹⁻¹ = t := by rw [← hut]; group
  rw [this]
  exact mem_torsionTorus_iff.2 ⟨a, hap, hta.symm⟩

end Fusion

section Model

noncomputable def twModelEquivOfDescent
    {τ : Tag} (K : Type) [Field K]
    (L : Type) [Field L] [Algebra K L] {Fr : L →+* L}
    (hD : adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
      (adjointGroup τ K).map (baseChangeGL (algebraMap K L)))
    {n g0 : ModGL τ L} (hg0C : g0 ∈ adjointGroup τ L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * n) :
    adjointGroup τ K ≃* twModel n Fr :=
  ((adjointGroup τ K).equivMapOfInjective _ (baseChangeGL_injective _)).trans
    ((MulEquiv.subgroupCongr ((map_conj_twModel hg0C hg0).trans hD)).symm.trans
      ((MulAut.conj g0).subgroupMap _).symm)

end Model

section Assembly

theorem ggOrdPToralMax_adjointGroup_of_lang
    {τ : Tag} (K : Type) [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hmon : MonomialToralAt τ p)
    {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (htor : ∀ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ a ∈ adjointGroup τ (AlgebraicClosure K))
    (hW : ∀ a : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ p = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    (hD : ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) →
      adjointGroup τ (AlgebraicClosure K) ⊓
          (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
        (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1)
    (hmax : ∀ A : Subgroup (adjointGroup τ K), IsElemAbelian p A → Nat.card A ≤ p ^ τ.rank) :
    GGOrdPToralMax (adjointGroup τ K) p := by
  classical
  set L := AlgebraicClosure K with hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hfK⟩ := FiniteField.card K 2
  have hKf : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hfK]
  have halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L :=
    isAlgebraic_zmod_algebraicClosure_of_finite K 2
  have hpL : (p : L) ≠ 0 := by
    intro h0
    have h2p : (2 : ℕ) ∣ p := (CharP.cast_eq_zero_iff L 2 p).1 h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2p).symm
  set Fr : L →+* L := iterateFrobenius L 2 f with hFr
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hFr, iterateFrobenius_def, hKf]
  have hn : ∃ n ∈ adjointGroup τ L, ∃ g0 ∈ adjointGroup τ L,
      Units.map (entrywiseHom Fr) g0 = g0 * n ∧ ∃ s : ℕ, ¬ p ∣ s ∧
      (∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) →
        n * rootDiagUnit τ a * n⁻¹ = rootDiagUnit τ a ^ s ∧
          frobTwistGL τ L 2 f n (rootDiagUnit τ a) = rootDiagUnit τ a) := by
    rcases hpq with h1 | h1
    · refine ⟨1, one_mem _, 1, one_mem _, by rw [map_one, mul_one], 1, hp.one_lt.ne' ∘
        (Nat.dvd_one.1 ·), fun a ha => ⟨by group, ?_⟩⟩
      rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
      exact frob_rootDiagUnit_eq (by rwa [hKf] at h1) ha
    · obtain ⟨Fr', hFr', g0, hg0C, hg0⟩ := exists_lang_data τ K w₀
      have hFF : Fr' = Fr := RingHom.ext fun c => by rw [hFr', hFrK]
      rw [hFF] at hg0
      refine ⟨canonicalRep (coxeterSystem τ) L w₀, canonicalRep_mem_adjointGroup _ L _, g0, hg0C,
        hg0, p - 1, fun h => ?_, fun a ha => ⟨?_, ?_⟩⟩
      · have h2p := hp.two_le
        have := Nat.le_of_dvd (by omega) h
        omega
      · rw [SteinbergBT.TrialityPlane.canonicalRep_conj_rootDiagUnit_of_neg hw₀]
        have hdp : rootDiagUnit τ a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall ha
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hdp]
      · rw [frobTwistGL_apply]
        exact twFrob_neg_rootDiagUnit_eq hw₀ (by rwa [hKf] at h1) ha
  obtain ⟨n, hnC, g0, hg0C, hg0, s, hs, hns⟩ := hn
  let e : adjointGroup τ K ≃* twModel n Fr :=
    twModelEquivOfDescent K L (hD Fr hFrK) hg0C hg0
  have hTW : torsionTorus τ L p ≤ twModel n Fr := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_torsionTorus_iff.1 hx
    exact ⟨htor a, (hns a ha).2⟩
  refine OrdPInnerExc.ggOrdPToralMax_of_mulEquiv e ?_
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  refine ggOrdPToralMax_of_conj_mem (V := (torsionTorus τ L p).subgroupOf (twModel n Fr))
    ?_ (fun x hx => ?_) (fun A hA => ?_)
  · have hcomm : ∀ x y : ModGL τ L, x ∈ torsionTorus τ L p → y ∈ torsionTorus τ L p →
        x * y = y * x := by
      intro x y hx hy
      obtain ⟨a, -, rfl⟩ := mem_torsionTorus_iff.1 hx
      obtain ⟨b, -, rfl⟩ := mem_torsionTorus_iff.1 hy
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hcomm _ _ x.2 y.2))⟩⟩, fun x hx => ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact isElemAbelian_torsionTorus.2 _ hx
  · obtain ⟨u, hu, hux⟩ := exists_conj_mem_torsionTorus halg hp hp2 hmon hnC
      (fun a ha => (hns a ha).2)
      (fun a ha => toral_centralizer_Lang_of_prime 2 hp (Ne.symm hp2) a ha (hW a ha) f hf1 hnC
        hs (hns a ha).1) x.2 (by rw [← Subgroup.coe_pow, hx, Subgroup.coe_one])
    exact ⟨⟨u, hu⟩, hux⟩
  · have hcard : Nat.card ((torsionTorus τ L p).subgroupOf (twModel n Fr)) = p ^ τ.rank := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTW).toEquiv]
      exact card_torsionTorus hp hpL
    rw [hcard, ← Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective]
    exact hmax _ (OrdPInnerExc.isElemAbelian_map _ hA)

end Assembly

end CFSG.StandardType.OrdPToralLang

end
