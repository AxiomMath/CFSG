module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Rank
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.PartOne.K133H.F4Weyl
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.CTLangData
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 F4Weyl

namespace F4AutWeyl

private theorem F4_root_exists_not_three_dvd
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) : ∃ i, ¬ (3 : ℤ) ∣ α i := by
  have h : ∀ β ∈ f4RootList, ∃ j : Fin Tag.F4.rank, β j % 3 ≠ 0 := by decide
  obtain ⟨j, hj⟩ := h α (isRoot_iff_mem_f4RootList.1 hα)
  exact ⟨j, fun hd => hj (Int.emod_eq_zero_of_dvd hd)⟩

theorem F4_exists_rootChar_mulSingle_ne_one_of_ne_two
    {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : kˣ} (hζ : orderOf ζ = p)
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) :
    ∃ i, rootChar (Pi.mulSingle i ζ) α ≠ 1 := by
  rcases eq_or_ne p 3 with rfl | hp3
  · obtain ⟨i, hi⟩ := F4_root_exists_not_three_dvd hα
    refine ⟨i, fun h1 => hi ?_⟩
    rw [rootChar_mulSingle_eq_zpow, ← orderOf_dvd_iff_zpow_eq_one, hζ] at h1
    exact_mod_cast h1
  · have h5 := five_le_of_prime_of_three_lt hp (by have := hp.two_le; omega)
    exact F4_exists_rootChar_mulSingle_ne_one (by omega) hζ hα

theorem F4_adjointGroup_inf_centralizer_torusPow_of_ne_two
    {k : Type} [Field k] [Finite k] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpk : p ∣ Nat.card kˣ) :
    adjointGroup .F4 k ⊓
        Subgroup.centralizer {h : ModGL .F4 k | h ∈ torusGroup .F4 k ∧ h ^ p = 1} =
      torusGroup .F4 k := by
  have : Fact p.Prime := ⟨hp⟩
  have hTcomm := (triangular_borel_structure.{0, 0} .F4 k).1
  refine le_antisymm (fun z hz => ?_) (le_inf torusGroup_le_adjointGroup_F4 fun h hh =>
    Subgroup.mem_centralizer_iff.2 fun x hx => hTcomm _ hx.1 _ hh)
  obtain ⟨hzC, hzV⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpk
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hbV : ∀ i, rootDiagUnit .F4 (Pi.mulSingle i ζ) ∈
      {h : ModGL .F4 k | h ∈ torusGroup .F4 k ∧ h ^ p = 1} := fun i =>
    ⟨F4_rootDiagUnit_mem_torusGroup _, by
      rw [rootDiagUnit_pow, ← Pi.mulSingle_pow, hζp, Pi.mulSingle_one, rootDiagUnit_one]⟩
  have hX : ∀ i, z ∈ toralCentralizer .F4 k (Pi.mulSingle i ζ) := fun i =>
    mem_toralCentralizer.2 ⟨hzC, by
      rw [Subgroup.mem_centralizer_iff.1 hzV _ (hbV i), mul_inv_cancel_right]⟩
  have hB := Chevalley_toral_centralizer_Bruhat_factors .F4 k (Pi.mulSingle ⟨0, by decide⟩ ζ)
  obtain ⟨w, -, h, hh, u, hu, v, hv, hz1⟩ := hB.1 z (hX _)
  have hwall : ∀ i, w ∈ rootCharStabilizer (Pi.mulSingle i ζ) := by
    intro i
    obtain ⟨w', hw', h', hh', u', hu', v', hv', hz2⟩ :=
      (Chevalley_toral_centralizer_Bruhat_factors .F4 k (Pi.mulSingle i ζ)).1 z (hX i)
    obtain ⟨hww, -, -, -⟩ := hB.2.1 w w' h h' u u' v v' hh hh'
      (rootSpan_le_posUnipotent (fun α hα => hα.2) hu)
      (rootSpan_le_posUnipotent (fun α hα => hα.2) hu')
      (rootSpan_mono Set.inter_subset_right hv) (rootSpan_mono Set.inter_subset_right hv')
      (hz1.symm.trans hz2)
    rw [hww]
    exact hw'
  have hw1 : w = 1 := F4_eq_one_of_smul_modEq (p := p) hp2 fun v i => by
    have := natCast_mul_smul_apply_eq_of_rootChar (m := 1) hζ (fun v => by
      rw [pow_one]
      exact hwall i v) v
    rwa [Nat.cast_one, one_mul] at this
  subst hw1
  have hbot : rootSpan .F4 k (∅ : Set (Fin Tag.F4.rank → ℤ)) = ⊥ := by simp [rootSpan]
  rw [inversionSet_one, Set.inter_empty, hbot, Subgroup.mem_bot] at hv
  subst hv
  rw [canonicalRep_one, mul_one, mul_one] at hz1
  have hu1 : u = 1 := by
    refine eq_one_of_mem_posUnipotent_of_conj_rootDiagUnit_eq
      (rootSpan_le_posUnipotent (fun α hα => hα.2) hu)
      (A := Set.range fun i => Pi.mulSingle i ζ) (fun α hα _ => ?_) ?_
    · obtain ⟨i, hi⟩ := F4_exists_rootChar_mulSingle_ne_one_of_ne_two hp hp2 hζ hα
      exact ⟨_, ⟨i, rfl⟩, hi⟩
    · rintro _ ⟨i, rfl⟩
      have hd := (mem_toralCentralizer.1 (hX i)).2
      rw [hz1] at hd
      exact conj_eq_self_of_commute_of_conj_mul_eq (hTcomm _ (hbV i).1 _ hh) hd
  rw [hz1, hu1, mul_one]
  exact hh

theorem mem_normalizer_torusPow_iff
    {M : Type} [Field M] {p : ℕ} {g : adjointGroup .F4 M} :
    g ∈ Subgroup.normalizer (TableBF4.torusPow M p : Set (adjointGroup .F4 M)) ↔
      (g : ModGL .F4 M) ∈
        Subgroup.normalizer {h : ModGL .F4 M | h ∈ torusGroup .F4 M ∧ h ^ p = 1} := by
  have hmem : ∀ x : adjointGroup .F4 M, x ∈ TableBF4.torusPow M p ↔
      (x : ModGL .F4 M) ∈ {h : ModGL .F4 M | h ∈ torusGroup .F4 M ∧ h ^ p = 1} := by
    intro x
    rw [TableBF4.mem_torusPow]
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Subtype.ext ?_⟩
    · rw [← Subgroup.coe_pow, h, OneMemClass.coe_one]
    · rw [Subgroup.coe_pow, h, OneMemClass.coe_one]
  have hC : ∀ h : ModGL .F4 M, h ∈ {h : ModGL .F4 M | h ∈ torusGroup .F4 M ∧ h ^ p = 1} →
      h ∈ adjointGroup .F4 M := fun h hh => torusGroup_le_adjointGroup_F4 hh.1
  constructor
  · intro hg
    refine Subgroup.mem_set_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.1 hg ⟨h, hC h hh⟩).1 ((hmem _).2 hh)
      exact (hmem _).1 h1
    · have hgh : g.1 * h * g.1⁻¹ ∈ adjointGroup .F4 M := hC _ hh
      have hhC : h ∈ adjointGroup .F4 M := by
        have := mul_mem (mul_mem (inv_mem g.2) hgh) g.2
        rwa [show g.1⁻¹ * (g.1 * h * g.1⁻¹) * g.1 = h by group] at this
      exact (hmem ⟨h, hhC⟩).1 ((Subgroup.mem_normalizer_iff.1 hg ⟨h, hhC⟩).2 ((hmem _).2 hh))
  · intro hg
    refine Subgroup.mem_normalizer_iff.2 fun x => ?_
    rw [hmem, hmem]
    exact Subgroup.mem_set_normalizer_iff.1 hg (x : ModGL .F4 M)

theorem canonicalRep_mem_normalizer_torusPow_F4
    (M : Type) [Field M] (p : ℕ) (w : WeylGroup .F4) :
    (⟨canonicalRep (coxeterSystem .F4) M w, canonicalRep_mem_adjointGroup _ M w⟩ :
        adjointGroup .F4 M) ∈
      Subgroup.normalizer (TableBF4.torusPow M p : Set (adjointGroup .F4 M)) :=
  mem_normalizer_torusPow_iff.2
    (mem_normalizer_torusPow_of_mem_normalizer (canonicalRep_mem_normalizer (R := M) w))

theorem exists_eq_mul_canonicalRep_of_mem_normalizer_torusPow
    {M : Type} [Field M] [Finite M] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : p ∣ Nat.card M - 1) {g : adjointGroup .F4 M}
    (hg : g ∈ Subgroup.normalizer (TableBF4.torusPow M p : Set (adjointGroup .F4 M))) :
    ∃ t ∈ torusGroup .F4 M, ∃ w : WeylGroup .F4,
      (g : ModGL .F4 M) = t * canonicalRep (coxeterSystem .F4) M w := by
  have hCV := F4_adjointGroup_inf_centralizer_torusPow_of_ne_two (k := M) hp hp2
    (by rw [Nat.card_units]; exact hpM)
  exact exists_eq_mul_canonicalRep_of_mem_normalizer (fun x hx => hx.1) hCV
    (Subgroup.mem_inf.2 ⟨g.2, mem_normalizer_torusPow_iff.1 hg⟩)

@[expose] noncomputable def weylTorusAut
    (M : Type) [Field M] [CharP M 2] (p : ℕ) :
    WeylGroup .F4 →* MulAut ↥(TableBF4.torusPow M p) where
  toFun w := ggConjAut _ (canonicalRep_mem_normalizer_torusPow_F4 M p w)
  map_one' := MulEquiv.ext fun v => Subtype.ext (Subtype.ext (by
    simp only [ggConjAut_apply, Subgroup.coe_mul, Subgroup.coe_inv, canonicalRep_one, one_mul,
      inv_one, mul_one, MulAut.one_apply]))
  map_mul' w w' := MulEquiv.ext fun v => Subtype.ext (Subtype.ext (by
    simp only [MulAut.mul_apply, ggConjAut_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      EvenF4QPlus.canonicalRep_mul_of_charTwo]
    group))

theorem coe_weylTorusAut_apply
    {M : Type} [Field M] [CharP M 2] {p : ℕ} (w : WeylGroup .F4)
    (v : ↥(TableBF4.torusPow M p)) :
    (((weylTorusAut M p w v : ↥(TableBF4.torusPow M p)) : adjointGroup .F4 M) :
        ModGL .F4 M) =
      canonicalRep (coxeterSystem .F4) M w * ((v : adjointGroup .F4 M) : ModGL .F4 M) *
        (canonicalRep (coxeterSystem .F4) M w)⁻¹ :=
  rfl

private theorem mem_torusPow_rootDiagUnit
    {M : Type} [Field M] {p : ℕ} {ζ : Mˣ} (hζ : orderOf ζ = p)
    (x : Fin Tag.F4.rank → ZMod p) :
    (⟨rootDiagUnit .F4 fun i => ζ ^ (x i).val,
        torusGroup_le_adjointGroup_F4 (F4_rootDiagUnit_pow_val_mem hζ x).1⟩ :
        adjointGroup .F4 M) ∈ TableBF4.torusPow M p :=
  ⟨(F4_rootDiagUnit_pow_val_mem hζ x).1, Subtype.ext (by
    rw [Subgroup.coe_pow, (F4_rootDiagUnit_pow_val_mem hζ x).2, OneMemClass.coe_one])⟩

private noncomputable def torusPowCoordEquiv
    {M : Type} [Field M] {p : ℕ} [NeZero p] {ζ : Mˣ}
    (hζ : orderOf ζ = p) : (Fin Tag.F4.rank → ZMod p) ≃ ↥(TableBF4.torusPow M p) :=
  Equiv.ofBijective (fun x => ⟨_, mem_torusPow_rootDiagUnit hζ x⟩)
    ⟨fun x y hxy => (F4_bijOn_rootDiagUnit_pow_val hζ).injOn (Set.mem_univ x) (Set.mem_univ y)
        (congrArg (fun v : ↥(TableBF4.torusPow M p) => ((v : adjointGroup .F4 M) :
          ModGL .F4 M)) hxy),
      fun v => by
        obtain ⟨x, -, hx⟩ := (F4_bijOn_rootDiagUnit_pow_val hζ).surjOn
          (show ((v : adjointGroup .F4 M) : ModGL .F4 M) ∈
            {h : ModGL .F4 M | h ∈ torusGroup .F4 M ∧ h ^ p = 1} from
            ⟨v.2.1, by rw [← Subgroup.coe_pow, v.2.2, OneMemClass.coe_one]⟩)
        exact ⟨x, Subtype.ext (Subtype.ext hx)⟩⟩

private theorem coe_torusPowCoordEquiv
    {M : Type} [Field M] {p : ℕ} [NeZero p] {ζ : Mˣ} (hζ : orderOf ζ = p)
    (x : Fin Tag.F4.rank → ZMod p) :
    (((torusPowCoordEquiv hζ x : ↥(TableBF4.torusPow M p)) : adjointGroup .F4 M) : ModGL .F4 M) =
      rootDiagUnit .F4 fun i => ζ ^ (x i).val :=
  rfl

private theorem card_eval_eq_zero_mul {p : ℕ} (i : Fin Tag.F4.rank) :
    Nat.card {x : Fin Tag.F4.rank → ZMod p // x i = 0} * p = p ^ 4 := by
  set f : (Fin Tag.F4.rank → ZMod p) →+ ZMod p := Pi.evalAddMonoidHom (fun _ => ZMod p) i
  have hf : Function.Surjective f := fun a => ⟨Pi.single i a, by simp [f]⟩
  have h1 := AddSubgroup.card_mul_index f.ker
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf, AddSubgroup.card_top,
    Nat.card_zmod, Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h1
  have h2 : Nat.card ↥f.ker = Nat.card {x : Fin Tag.F4.rank → ZMod p // x i = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [f])
  rw [← h2]
  exact h1

theorem weylTorusAut_injective
    {M : Type} [Field M] [Finite M] [CharP M 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : p ∣ Nat.card M - 1) : Function.Injective (weylTorusAut M p) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [injective_iff_map_eq_one]
  intro w hw
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p
    (show p ∣ Nat.card Mˣ by rw [Nat.card_units]; exact hpM)
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hwall : ∀ i, w ∈ rootCharStabilizer (Pi.mulSingle i ζ) := by
    intro i
    have hdT : rootDiagUnit .F4 (Pi.mulSingle i ζ) ∈ torusGroup .F4 M :=
      F4_rootDiagUnit_mem_torusGroup _
    have hdp : rootDiagUnit .F4 (Pi.mulSingle i ζ) ^ p = 1 := by
      rw [rootDiagUnit_pow, ← Pi.mulSingle_pow, hζp, Pi.mulSingle_one, rootDiagUnit_one]
    let v : ↥(TableBF4.torusPow M p) := ⟨⟨_, torusGroup_le_adjointGroup_F4 hdT⟩, hdT,
      Subtype.ext (by rw [Subgroup.coe_pow, hdp, OneMemClass.coe_one])⟩
    have h1 : weylTorusAut M p w v = v := by rw [hw, MulAut.one_apply]
    have h2 := congrArg (fun x : ↥(TableBF4.torusPow M p) =>
      ((x : adjointGroup .F4 M) : ModGL .F4 M)) h1
    simp only [coe_weylTorusAut_apply] at h2
    exact (rootDiagUnit_eq_conj_canonicalRep_iff _ _ w).1 h2.symm
  exact F4_eq_one_of_smul_modEq (p := p) hp2 fun v i => by
    have := natCast_mul_smul_apply_eq_of_rootChar (m := 1) hζ (fun v => by
      rw [pow_one]
      exact hwall i v) v
    rwa [Nat.cast_one, one_mul] at this

private theorem charVal_simple_smul_iff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (x : Fin Tag.F4.rank → ZMod p) (i : Fin Tag.F4.rank) :
    (∀ u : Fin Tag.F4.rank → ℤ, charVal x (simple .F4 i • u) = charVal x u) ↔ x i = 0 := by
  have key : ∀ u : Fin Tag.F4.rank → ℤ, charVal x (simple .F4 i • u) =
      charVal x u - ((∑ j, Tag.F4.cartan i j * u j : ℤ) : ZMod p) * x i := by
    intro u
    rw [simple_smul, reflect, charVal_sub', charVal_smul, charVal_single]
  constructor
  · intro h
    have h1 := h (Pi.single i 1)
    rw [key, sub_eq_self] at h1
    have hii : (∑ j, Tag.F4.cartan i j * (Pi.single i (1 : ℤ) : Fin Tag.F4.rank → ℤ) j) = 2 := by
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp only [Pi.single_eq_same, mul_one]
      fin_cases i <;> decide
    rw [hii, Int.cast_ofNat] at h1
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)
    exact (mul_eq_zero.1 h1).resolve_left h2
  · intro h u
    rw [key, h]
    simp

theorem isReflection_weylTorusAut_simple
    {M : Type} [Field M] [Finite M] [CharP M 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : p ∣ Nat.card M - 1) (i : Fin Tag.F4.rank) :
    GGIsReflection p (weylTorusAut M p (simple .F4 i)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p
    (show p ∣ Nat.card Mˣ by rw [Nat.card_units]; exact hpM)
  refine ⟨by rw [← map_pow, CoxeterSystem.simple_sq, map_one], ?_⟩
  have hfix : ∀ x, x i = 0 ↔ weylTorusAut M p (simple .F4 i) (torusPowCoordEquiv hζ x) =
      torusPowCoordEquiv hζ x := by
    intro x
    rw [← charVal_simple_smul_iff hp2 x i]
    constructor
    · intro h
      refine Subtype.ext (Subtype.ext ?_)
      rw [coe_weylTorusAut_apply, coe_torusPowCoordEquiv]
      refine ((rootDiagUnit_eq_conj_canonicalRep_iff _ _ _).2 fun u => ?_).symm
      rw [rootChar_pow_val_eq hζ, rootChar_pow_val_eq hζ, h u]
    · intro h u
      have h2 := congrArg (fun v : ↥(TableBF4.torusPow M p) =>
        ((v : adjointGroup .F4 M) : ModGL .F4 M)) h
      simp only [coe_weylTorusAut_apply, coe_torusPowCoordEquiv] at h2
      have h3 := (rootDiagUnit_eq_conj_canonicalRep_iff _ _ _).1 h2.symm u
      rw [rootChar_pow_val_eq hζ, rootChar_pow_val_eq hζ] at h3
      exact eq_of_pow_val_eq_pow_val hζ h3
  have hcard : Nat.card {v : ↥(TableBF4.torusPow M p) //
      weylTorusAut M p (simple .F4 i) v = v} =
      Nat.card {x : Fin Tag.F4.rank → ZMod p // x i = 0} :=
    (Nat.card_congr ((torusPowCoordEquiv hζ).subtypeEquiv hfix)).symm
  rw [hcard, TableBF4.card_torusPow hp hpM]
  exact card_eval_eq_zero_mul i

theorem weylTorusAut_f4Neg_apply
    {M : Type} [Field M] [CharP M 2] {p : ℕ} (v : ↥(TableBF4.torusPow M p)) :
    weylTorusAut M p CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg v = v⁻¹ := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_weylTorusAut_apply]
  have h := mul_canonicalRep_conj_eq_inv_of_smul_eq_neg (one_mem (torusGroup .F4 M))
    CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul v.2.1
  rw [one_mul] at h
  rw [h]
  rfl

theorem ggConjAut_eq_weylTorusAut
    {M : Type} [Field M] [CharP M 2] {p : ℕ} {g : adjointGroup .F4 M}
    (hg : g ∈ Subgroup.normalizer (TableBF4.torusPow M p : Set (adjointGroup .F4 M)))
    {t : ModGL .F4 M} (ht : t ∈ torusGroup .F4 M) {w : WeylGroup .F4}
    (hgt : (g : ModGL .F4 M) = t * canonicalRep (coxeterSystem .F4) M w) :
    ggConjAut _ hg = weylTorusAut M p w := by
  have hTcomm := (triangular_borel_structure.{0, 0} .F4 M).1
  refine MulEquiv.ext fun v => Subtype.ext (Subtype.ext ?_)
  rw [coe_weylTorusAut_apply]
  change (g : ModGL .F4 M) * ((v : adjointGroup .F4 M) : ModGL .F4 M) * (g : ModGL .F4 M)⁻¹ = _
  set n := canonicalRep (coxeterSystem .F4) M w
  have hy : n * ((v : adjointGroup .F4 M) : ModGL .F4 M) * n⁻¹ ∈ torusGroup .F4 M :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := M) w) _).1 v.2.1
  rw [hgt]
  calc t * n * ((v : adjointGroup .F4 M) : ModGL .F4 M) * (t * n)⁻¹ =
        t * (n * ((v : adjointGroup .F4 M) : ModGL .F4 M) * n⁻¹) * t⁻¹ := by group
    _ = n * ((v : adjointGroup .F4 M) : ModGL .F4 M) * n⁻¹ := by
      rw [hTcomm _ ht _ hy]
      group

theorem ggAutomizer_torusPow_eq_range
    {M : Type} [Field M] [Finite M] [CharP M 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : p ∣ Nat.card M - 1) {H : Subgroup (adjointGroup .F4 M)}
    (hW : ∀ w : WeylGroup .F4, ∃ h ∈ H, ∃ t ∈ torusGroup .F4 M,
      (h : ModGL .F4 M) = t * canonicalRep (coxeterSystem .F4) M w) :
    ggAutomizer H (TableBF4.torusPow M p) = (weylTorusAut M p).range := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨g, -, hg, hφg⟩ := mem_ggAutomizer_iff.1 hφ
    obtain ⟨t, ht, w, hgt⟩ := exists_eq_mul_canonicalRep_of_mem_normalizer_torusPow hp hp2 hpM hg
    refine ⟨w, ?_⟩
    rw [← ggConjAut_eq_weylTorusAut hg ht hgt]
    exact MulEquiv.ext fun b => Subtype.ext (hφg b).symm
  · rintro _ ⟨w, rfl⟩
    obtain ⟨h, hhH, t, ht, hht⟩ := hW w
    have hh : h ∈ Subgroup.normalizer (TableBF4.torusPow M p : Set (adjointGroup .F4 M)) := by
      refine mem_normalizer_torusPow_iff.2 ?_
      rw [hht]
      exact mem_normalizer_torusPow_of_mem_normalizer
        (mul_mem (Subgroup.le_normalizer ht) (canonicalRep_mem_normalizer (R := M) w))
    rw [← ggConjAut_eq_weylTorusAut hh ht hht]
    exact ggConjAut_mem_ggAutomizer hhH hh

theorem ggAutomizer_torusPow_F4
    {M : Type} [Field M] [Finite M] [CharP M 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpM : p ∣ Nat.card M - 1) {H : Subgroup (adjointGroup .F4 M)}
    (hW : ∀ w : WeylGroup .F4, ∃ h ∈ H, ∃ t ∈ torusGroup .F4 M,
      (h : ModGL .F4 M) = t * canonicalRep (coxeterSystem .F4) M w) :
    2 ^ 4 * Nat.factorial 4 ≤ Nat.card (ggAutomizer H (TableBF4.torusPow M p)) ∧
      GGReflGenerated p (ggAutomizer H (TableBF4.torusPow M p)) ∧
      ∀ e : ↥(TableBF4.torusPow M p),
        (∀ φ ∈ ggAutomizer H (TableBF4.torusPow M p), φ e = e) → e = 1 := by
  rw [ggAutomizer_torusPow_eq_range hp hp2 hpM hW]
  refine ⟨?_, ?_, fun e he => ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective (weylTorusAut_injective hp hp2 hpM)).toEquiv,
      CFSG.RankThree.PartOne.K133H.card_weylGroup_F4]
    decide
  · have hrange : (weylTorusAut M p).range =
        Subgroup.closure (weylTorusAut M p '' Set.range (simple .F4)) := by
      rw [MonoidHom.range_eq_map, ← (coxeterSystem .F4).subgroup_closure_range_simple,
        MonoidHom.map_closure]
    refine le_antisymm (fun φ hφ => ?_) ((Subgroup.closure_le _).2 fun φ hφ => hφ.1)
    rw [hrange] at hφ
    refine Subgroup.closure_mono ?_ hφ
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨simple .F4 i, rfl⟩, isReflection_weylTorusAut_simple hp hp2 hpM i⟩
  · have h1 := he _ ⟨CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg, rfl⟩
    rw [weylTorusAut_f4Neg_apply] at h1
    have h2 : e ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [← h1]
      exact mul_inv_cancel e
    have hp1 : e ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, e.2.2, OneMemClass.coe_one])
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    rw [← orderOf_eq_one_iff, ← Nat.dvd_one, ← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hp1)

end F4AutWeyl

end CFSG.StandardType
