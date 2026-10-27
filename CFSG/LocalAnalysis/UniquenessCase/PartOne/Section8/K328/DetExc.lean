module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetDefs
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
import CFSG.RankThree.PartTwo.Sec19.SimsC198Ree
import CFSG.Quasithin.H13.NQBlockLargeRee
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcCent
import CFSG.RankThree.PartTwo.Sec12.Hering129KRes
import CFSG.RankThree.PartTwo.Sec12.Hering129LG2
import CFSG.RankThree.PartTwo.Sec19.SimsC198G2
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriCentHolds
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U2
import CFSG.LocalAnalysis.GLTheoremA.CatA.K148InnerOrd
import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2U
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetOddTools
import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeIso
import CFSG.CGT.PushingUpLit.CGT6M.FiveDataPSL
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.LieType.Ree.Duality
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)

open CFSG.Blueprint.Chevalley

private theorem k328dg2c_card_of_isSLThreePiAt {X : Type} [Group X] {q : ℕ}
    (h : CFSG.RankThree.PartTwo.Sec4.IsSLThreePiAt X q) :
    Nat.card X = k328det_sl3eps q := by
  obtain ⟨K, hKf, hKfin, h1 | h1⟩ := h
  · obtain ⟨hcard, hq1, ⟨e⟩⟩ := h1
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, hcard]
    simp only [k328det_sl3eps, hq1, if_true]
    ring
  · obtain ⟨hcard, hq2, ⟨e⟩⟩ := h1
    rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hcard]
    have hq1 : q % 3 ≠ 1 := by omega
    rw [k328det_sl3eps, if_neg hq1]
    ring

private theorem k328dg2c_perfect_le_commutator {G : Type*} [Group G] {N C : Subgroup G}
    (hN : Group.IsPerfect N) (hNC : N ≤ C) : N ≤ ⁅C, C⁆ := by
  have h := congrArg (Subgroup.map N.subtype) hN.commutator_eq_top
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact fun x hx => Subgroup.commutator_mono hNC hNC (by rw [h]; exact hx)

private theorem k328dg2c_map_centralizer_singleton {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (z : A) :
    (Subgroup.centralizer ({z} : Set A)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set B) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    show e x * e z = e z * e x
    rw [← e.map_mul, ← e.map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hy

private theorem k328dg2c_adjoint_card
    (r : TauCeti.PrimePower) {K : Type} [Field K] [Finite K]
    (hr : Nat.card K = r.card) (hchar : ringChar K ≠ 3) (h4 : 4 ≤ Nat.card K)
    {z : adjointGroup .G2 K} (hz : orderOf z = 3)
    {X : Subgroup (adjointGroup .G2 K)} (hzX : z ∈ X)
    (hXC : X ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)))
    (hsub : (X.subgroupOf (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)))).IsSubnormal)
    (hq : CFSG.Open.IsQuasisimple ↥X) :
    Nat.card X = k328det_sl3eps (Nat.card K) := by
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz; omega
  have hTLM := CFSG.RankThree.PartTwo.Sec12.Hering129L.g2_threeLocalModel r hr hchar h4
  obtain ⟨g, hg⟩ := hTLM.conj z hz
  set w : adjointGroup .G2 K := g * z * g⁻¹ with hw
  set X' : Subgroup (adjointGroup .G2 K) := X.map (MulAut.conj g).toMonoidHom with hX'
  let eX : ↥X ≃* ↥X' :=
    X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hw3 : w ^ 3 = 1 := by
    rw [hw, show g * z * g⁻¹ = MulAut.conj g z from rfl, ← map_pow, hz3, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    apply hz1
    have h' : MulAut.conj g z = MulAut.conj g 1 := by rw [hw] at h; simpa using h
    simpa using (MulAut.conj g).injective h'
  have hz'X' : w ∈ X' := by
    rw [hw, hX']
    exact ⟨z, hzX, rfl⟩
  have hX'C : X' ≤ Subgroup.centralizer ({w} : Set (adjointGroup .G2 K)) := by
    rw [hX', hw]
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨x, hxX, rfl⟩ := hy
    have hx : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (hXC hxX)
    calc (g * x * g⁻¹) * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
      _ = g * (z * x) * g⁻¹ := by rw [hx]
      _ = (g * z * g⁻¹) * (g * x * g⁻¹) := by group
  have hsub' :
      (X'.subgroupOf (Subgroup.centralizer ({w} : Set (adjointGroup .G2 K)))).IsSubnormal := by
    rw [hX', hw]
    have hmapC := k328dg2c_map_centralizer_singleton (MulAut.conj g) z
    have h := isSubnormal_subgroupOf_map' (MulAut.conj g) hXC hsub
    rwa [hmapC] at h
  have hperf' : Group.IsPerfect ↥X' := by
    rw [hX']
    have hPerfX : Group.IsPerfect ↥X := ⟨hq.1⟩
    exact Group.IsPerfect.ofSurjective
      (f := (X.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toMonoidHom)
      (X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).surjective
  have hX'ne : X' ≠ ⊥ := by
    intro hbot
    rw [hbot] at hz'X'
    exact hw1 (Subgroup.mem_bot.mp hz'X')
  rcases hg with hS | hM
  · obtain ⟨-, hSL⟩ :=
      CFSG.RankThree.PartTwo.Sec12.Hering129L.g2_centralizer_threeA hchar h4 hS hw3 hw1
    have hqC : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({w} : Set (adjointGroup .G2 K))) :=
      CFSG.RankThree.PartTwo.Sec12.Hering129KRes.isQuasisimple_of_isSLThreePiAt hSL (by omega)
    have hX'eq : X' = Subgroup.centralizer ({w} : Set (adjointGroup .G2 K)) :=
      CFSG.RankThree.PartTwo.Sec19.SimsC198.G2.eq_of_isPerfect_of_isSubnormal_of_isQuasisimple
        hqC hX'C hperf' hsub' hX'ne
    calc Nat.card X = Nat.card X' := Nat.card_congr eX.toEquiv
      _ = Nat.card (Subgroup.centralizer ({w} : Set (adjointGroup .G2 K))) := by rw [hX'eq]
      _ = k328det_sl3eps (Nat.card K) := k328dg2c_card_of_isSLThreePiAt hSL
  · exfalso
    have hcomm :=
      (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ThreeBCent_holds K hchar h4 w hM hw3 hw1).1
    have hX'S : X' ≤ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 K := by
      refine (k328dg2c_perfect_le_commutator hperf' hX'C).trans ?_
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact hcomm a ha b hb
    exact hw1 (hTLM.inter w (hX'S hz'X') hM hw3)

theorem k328det_excThreeCompG2 :
    ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .G2 0 p f → p ≠ 3 → ∀ z : S,
      orderOf z = 3 → ∀ X : Subgroup S, z ∈ X → X ≤ Subgroup.centralizer ({z} : Set S) →
        (X.subgroupOf (Subgroup.centralizer ({z} : Set S))).IsSubnormal →
        CFSG.Open.IsQuasisimple ↥X → Nat.card X = k328det_sl3eps (p ^ f) := by
  intro S _ _ p f hLie hp3 z hz X hzX hXC hsub hq
  have hadm : CFSG.Open.StatedLieAdmissible .G2 0 p f := hLie.admissible
  have h3le : 3 ≤ p ^ f := hadm.2.2.2
  have hf1 : 1 ≤ f := hadm.2.1
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel S .G2 p f :=
    hLie.chevalleyExceptionalModel (by decide)
  have hmodel : CFSG.Blueprint.UntwistedChevalleyModel S .G2 (p ^ f) := hce.2
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hmodel
  let hKfld : Field K := hKf
  let hKfin' : Finite K := hKfin
  have hCharP : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hadm.1 hf1 hKcard
  have hchar : ringChar K ≠ 3 := by rw [ringChar.eq K p]; exact hp3
  have hpow_ne : p ^ f ≠ 3 := by
    intro h
    have hdvd : p ∣ 3 := by
      rw [← h]; exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hf1)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hadm.1 Nat.prime_three).1 hdvd)
  have h4 : 4 ≤ Nat.card K := by rw [hKcard]; omega
  set r : TauCeti.PrimePower := ⟨p, f, hadm.1, by omega⟩ with hrdef
  have hr : Nat.card K = r.card := by rw [hKcard, hrdef, TauCeti.PrimePower.card_def]
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz; omega
  set z' : adjointGroup .G2 K := e z with hz'def
  set X' : Subgroup (adjointGroup .G2 K) := X.map e.toMonoidHom with hX'def
  let eX : ↥X ≃* ↥X' := X.equivMapOfInjective e.toMonoidHom e.injective
  have hz'3 : z' ^ 3 = 1 := by rw [hz'def, ← map_pow, hz3, map_one]
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    apply e.injective
    rw [← hz'def, h, map_one]
  have hz' : orderOf z' = 3 := orderOf_eq_prime hz'3 hz'1
  have hzX' : z' ∈ X' := by rw [hz'def, hX'def]; exact ⟨z, hzX, rfl⟩
  have hXC' : X' ≤ Subgroup.centralizer ({z'} : Set (adjointGroup .G2 K)) := by
    rw [hX'def, hz'def]
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨x, hxX, rfl⟩ := hy
    have hx : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (hXC hxX)
    show e x * e z = e z * e x
    rw [← e.map_mul, ← e.map_mul, hx]
  have hsub' :
      (X'.subgroupOf (Subgroup.centralizer ({z'} : Set (adjointGroup .G2 K)))).IsSubnormal := by
    rw [hX'def, hz'def]
    have hmapC := k328dg2c_map_centralizer_singleton e z
    have h := isSubnormal_subgroupOf_map' e hXC hsub
    rwa [hmapC] at h
  have hq' : CFSG.Open.IsQuasisimple ↥X' := by
    rw [hX'def]
    exact isQuasisimple_of_mulEquiv' (X.equivMapOfInjective e.toMonoidHom e.injective) hq
  have hcore := k328dg2c_adjoint_card r hr hchar h4 hz' hzX' hXC' hsub' hq'
  calc Nat.card X = Nat.card X' := Nat.card_congr eX.toEquiv
    _ = k328det_sl3eps (Nat.card K) := hcore
    _ = k328det_sl3eps (p ^ f) := by rw [hKcard]

private theorem k328df4c_map_centralizer {S T : Type*} [Group S] [Group T] (e : S ≃* T) (z : S) :
    (Subgroup.centralizer ({z} : Set S)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set T) := by
  refine le_antisymm ?_ ?_
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      Subgroup.map_centralizer_le_centralizer_image ({z} : Set S) e.toMonoidHom
  · intro x hx
    rw [Subgroup.mem_map]
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hx

private theorem k328df4c_open_of_isQuasisimple {Q : Type*} [Group Q]
    (h : CFSG.IsQuasisimple Q) : CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem k328df4c_perfect_of_quasisimple {G : Type*} [Group G] {J : Subgroup G}
    (hJ : CFSG.Open.IsQuasisimple ↥J) : ⁅J, J⁆ = J := by
  have hmap : (⊤ : Subgroup ↥J).map J.subtype = J := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : Subgroup.map J.subtype ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ = J := by
    rw [← _root_.commutator_def, hJ.1, hmap]
  rwa [Subgroup.map_commutator, hmap] at h1

private theorem k328df4c_ne_bot_of_quasisimple {G : Type*} [Group G] {J : Subgroup G}
    (hJ : CFSG.Open.IsQuasisimple ↥J) : J ≠ ⊥ := by
  intro hbot
  have hnt : Nontrivial ↥J := by
    obtain ⟨x, y, hxy⟩ := hJ.2.exists_pair_ne
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨a, b, fun hab => hxy (by rw [hab])⟩
  have hsub : Subsingleton ↥J := by rw [hbot]; exact inferInstance
  obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
  exact hab (hsub.elim a b)

theorem k328det_f4ThreeComp :
    ∀ (S : Type) [Group S] [Finite S] (f : ℕ), LieModel S .twistedF4 0 2 f → ∀ z : S,
      orderOf z = 3 → ∀ X : Subgroup S, z ∈ X → X ≤ Subgroup.centralizer ({z} : Set S) →
        (X.subgroupOf (Subgroup.centralizer ({z} : Set S))).IsSubnormal →
        CFSG.Open.IsQuasisimple ↥X → Nat.card X = k328det_su3 (2 ^ f) := by
  intro S _ _ f hLM z hz X hzX hXle hXsub hXq
  have ht : CFSG.Open.StatedLieTag.twistedF4 ∈ CFSG.Blueprint.reeTitsTags := by decide
  have hRT : CFSG.Blueprint.ReeTitsModel S CFSG.Open.StatedLieTag.twistedF4 2 f :=
    (hLM.reeTitsModel ht).2
  have hadm : CFSG.Open.StatedLieAdmissible CFSG.Open.StatedLieTag.twistedF4 0 2 f :=
    hLM.admissible
  obtain ⟨a, hf, -⟩ := hRT.2
  have hf3 : 3 ≤ f := by
    obtain ⟨-, -, -, h3⟩ := hadm.2.2
    exact h3
  have ha : 1 ≤ a := by omega
  have hRT' : CFSG.Blueprint.ReeTitsModel S CFSG.Open.StatedLieTag.twistedF4 2 (2 * a + 1) :=
    hf ▸ hRT
  obtain ⟨K, hKf, hKfin, hKchar, hKcard, ⟨e⟩⟩ :=
    CFSG.Quasithin.H13.NQBlock.exists_mulEquiv_reeGamma_of_reeTitsModel ha hRT'
  have hy : orderOf (e z) = 3 := by
    simp [hz]
  have hSq : CFSG.Open.IsQuasisimple
      ↥(Subgroup.centralizer ({e z} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))) :=
    k328df4c_open_of_isQuasisimple
      (CFSG.RankThree.PartTwo.Sec19.SimsC198.reeGamma_isQuasisimple_centralizer ha hKcard (e z) hy)
  have hsubOpen : CFSG.Open.IsSubnormal X (Subgroup.centralizer ({z} : Set S)) :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hXle).2 hXsub
  have hsubMap : CFSG.Open.IsSubnormal (X.map e.toMonoidHom)
      ((Subgroup.centralizer ({z} : Set S)).map e.toMonoidHom) :=
    CFSG.Open.IsSubnormal.map e.toMonoidHom hsubOpen
  have hsub' : CFSG.Open.IsSubnormal (X.map e.toMonoidHom)
      (Subgroup.centralizer ({e z} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))) := by
    rwa [k328df4c_map_centralizer e z] at hsubMap
  let eX : ↥X ≃* ↥(X.map e.toMonoidHom) := X.equivMapOfInjective e.toMonoidHom e.injective
  have hX'q : CFSG.Open.IsQuasisimple ↥(X.map e.toMonoidHom) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eX.symm hXq
  have hJeq : X.map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a)) :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.l154_eq_of_subnormal_quasisimple hsub' hSq
      (k328df4c_perfect_of_quasisimple hX'q) (k328df4c_ne_bot_of_quasisimple hX'q)
  have hcardC : Nat.card
      (Subgroup.centralizer ({e z} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))) =
      (2 ^ (2 * a + 1)) ^ 3 * ((2 ^ (2 * a + 1)) ^ 2 - 1) *
        ((2 ^ (2 * a + 1)) ^ 3 + 1) :=
    CFSG.RankThree.PartTwo.Sec19.SimsC198.reeGamma_card_centralizer hKcard (e z) hy
  calc Nat.card X
      = Nat.card (X.map e.toMonoidHom) := Nat.card_congr eX.toEquiv
    _ = Nat.card (Subgroup.centralizer
          ({e z} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a))) := by rw [hJeq]
    _ = (2 ^ (2 * a + 1)) ^ 3 * ((2 ^ (2 * a + 1)) ^ 2 - 1) *
          ((2 ^ (2 * a + 1)) ^ 3 + 1) := hcardC
    _ = k328det_su3 (2 ^ f) := by
          rw [hf, k328det_su3]
          ring

private theorem k328dd4c_center_map_bot {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  have h1 : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := Subgroup.map_center_eq e
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

private theorem k328dd4c_center_d4ShortSL2
    {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) :
    Subgroup.center
      (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) = ⊥ := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
  exact k328dd4c_center_map_bot e.symm
    (CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof.center_sl2_eq_bot)

private theorem k328dd4c_model_comp
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {z : CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4
      K σ.toRingHom} (hz : orderOf z = 3)
    {X : Subgroup (CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4
      K σ.toRingHom)} (hzX : z ∈ X)
    (hXC : X ≤ Subgroup.centralizer ({z} : Set (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom)))
    (hsub : (X.subgroupOf (Subgroup.centralizer ({z} : Set (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom)))).IsSubnormal)
    (hqs : CFSG.Open.IsQuasisimple ↥X) :
    Nat.card X = k328det_sl3eps (2 ^ f) := by
  have hZ3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hz; norm_num at hz
  have hK3 : Nat.card K = 2 ^ (f * 3) := by rw [hK, ← pow_mul]
  have hcharK : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have halgchar : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hSub : CFSG.Assembly.IsSubnormal X
      (Subgroup.centralizer ({z} : Set (CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom))) :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hXC).2 hsub
  have hComp : CFSG.Assembly.IsComponentOf X
      (Subgroup.centralizer ({z} : Set (CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom))) :=
    ⟨hXC, hSub, hqs⟩
  have h3 : ¬ 3 ∣ 2 ^ f := by
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at this
  obtain ⟨g, hg | hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeConj_holds
    K (2 ^ f) σ hK hσ h3 z hZ3 hz1
  ·
    set g' : MulAut (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) := MulAut.conj g with hg'def
    set Y : Subgroup (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) := X.map g'.toMonoidHom with hYdef
    have hYcomp : CFSG.Assembly.IsComponentOf Y (Subgroup.centralizer ({g' z} : Set
        (CFSG.LieType.Chevalley.graphFixedRootGroup
          CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom))) := by
      have h := CFSG.LocalAnalysis.GLTheoremA.tcent_isComponentOf_map g' hComp
      rw [CFSG.LocalAnalysis.GLTheoremA.tcent_map_centralizer g' z] at h
      rwa [hYdef]
    have hYcard : Nat.card Y = Nat.card X := by
      rw [hYdef, Subgroup.card_map_of_injective g'.injective]
    have hgz : g' z = g * z * g⁻¹ := by rw [hg'def, MulAut.conj_apply]
    have hy : g' z ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := by
      rw [hgz]; exact hg
    have hy3 : (g' z) ^ 3 = 1 := by rw [← map_pow, hZ3, map_one]
    have hy1 : g' z ≠ 1 := by
      intro h1
      apply hz1
      have h2 := congrArg g'.symm h1
      rw [MulEquiv.symm_apply_apply, map_one] at h2
      exact h2
    by_cases hev : f % 2 = 0
    ·
      obtain ⟨c, R, hcR, hRC, hcomm, hRq, F, hFfield, hFfin, hFcard, ⟨eR⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model Nat.prime_two hf
          (by norm_num) (CFSG.LocalAnalysis.GLTheoremA.K148Inner.two_pow_mod_three_of_even hev)
          hK hσ hy hy3 hy1
      set c' : MulAut (CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) := MulAut.conj c with hc'def
      have hc'eq : c' (g' z) = c * (g' z) * c⁻¹ := by rw [hc'def, MulAut.conj_apply]
      have hZcomp : CFSG.Assembly.IsComponentOf (Y.map c'.toMonoidHom)
          (Subgroup.centralizer ({c' (g' z)} : Set
            (CFSG.LieType.Chevalley.graphFixedRootGroup
              CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom))) := by
        have h := CFSG.LocalAnalysis.GLTheoremA.tcent_isComponentOf_map c' hYcomp
        rw [CFSG.LocalAnalysis.GLTheoremA.tcent_map_centralizer c' (g' z)] at h
        exact h
      have hZR : Y.map c'.toMonoidHom = R := by
        refine CFSG.LocalAnalysis.GLTheoremA.tcent_component_eq hZcomp ?_ ?_ hRq
        · rw [hc'eq]; exact hRC
        · intro a ha b hb
          rw [hc'eq] at ha hb
          exact hcomm a ha b hb
      have hcard : Nat.card X = Nat.card R := by
        rw [← hYcard, ← Subgroup.card_map_of_injective (K := Y) (f := c'.toMonoidHom) c'.injective, hZR]
      rw [hcard, Nat.card_congr eR.toEquiv,
        CFSG.LocalAnalysis.GLTheoremA.K148Inner.natCard_SL3 F, hFcard, k328det_sl3eps,
        if_pos (CFSG.LocalAnalysis.GLTheoremA.K148Inner.two_pow_mod_three_of_even hev)]
    ·
      have hodd : f % 2 = 1 := by omega
      by_cases hf1 : f = 1
      ·
        obtain ⟨c, R, hcR, hRC, hcomm, U, hU, ⟨eR⟩⟩ :=
          CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model_unitary_two Nat.prime_two
            hf (by norm_num) (by rw [hf1]; norm_num) hK hσ hy hy3 hy1
        set c' : MulAut (CFSG.LieType.Chevalley.graphFixedRootGroup
          CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) := MulAut.conj c with hc'def
        have hc'eq : c' (g' z) = c * (g' z) * c⁻¹ := by rw [hc'def, MulAut.conj_apply]
        have hZcomp : CFSG.Assembly.IsComponentOf (Y.map c'.toMonoidHom)
            (Subgroup.centralizer ({c' (g' z)} : Set
              (CFSG.LieType.Chevalley.graphFixedRootGroup
                CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom))) := by
          have h := CFSG.LocalAnalysis.GLTheoremA.tcent_isComponentOf_map c' hYcomp
          rw [CFSG.LocalAnalysis.GLTheoremA.tcent_map_centralizer c' (g' z)] at h
          exact h
        have hqsZ : CFSG.Open.IsQuasisimple ↥(Y.map c'.toMonoidHom) := by
          have e : ↥X ≃* ↥(Y.map c'.toMonoidHom) :=
            (X.equivMapOfInjective g'.toMonoidHom g'.injective).trans
              (Y.equivMapOfInjective c'.toMonoidHom c'.injective)
          exact (CFSG.Open.IsQuasisimple.congr e).1 hqs
        have hc'gz1 : c' (g' z) ≠ 1 := by
          intro h1
          apply hy1
          have h2 := congrArg c'.symm h1
          rw [MulEquiv.symm_apply_apply, map_one] at h2
          exact h2
        have hnt : Nontrivial ↥(Y.map c'.toMonoidHom) :=
          ⟨⟨c' (g' z), Subgroup.mem_map_of_mem c'.toMonoidHom
              (by rw [hgz]; exact Subgroup.mem_map_of_mem g'.toMonoidHom hzX)⟩,
            1, fun h => hc'gz1 (Subtype.ext_iff.mp h)⟩
        have hZle : Y.map c'.toMonoidHom ≤ R := by
          have hperf : ⁅Y.map c'.toMonoidHom, Y.map c'.toMonoidHom⁆ =
              Y.map c'.toMonoidHom := by
            have h1 : (commutator ↥(Y.map c'.toMonoidHom)).map
                (Y.map c'.toMonoidHom).subtype =
                ⁅Y.map c'.toMonoidHom, Y.map c'.toMonoidHom⁆ := by
              rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
                Subgroup.range_subtype]
            rw [← h1, hqsZ.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
          rw [← hperf]
          refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
          rw [commutatorElement_def]
          exact hcomm a (hc'eq ▸ hZcomp.1 ha) b (hc'eq ▸ hZcomp.1 hb)
        have hUcard := CFSG.RankThree.PartTwo.Sec4.E27.card_subgroup_unitarySet
          (ℓ := 2) (f := f) hf U hU
        have hRcard : Nat.card R = 216 := by
          rw [Nat.card_congr eR.toEquiv, hUcard, hf1]
          norm_num
        have hftR : Fintype ↥R := Fintype.ofFinite _
        have hsolR : Group.IsSolvable ↥R :=
          CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
            (a := 3) (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
            (by rw [← Nat.card_eq_fintype_card, hRcard]; norm_num)
        have hsolRi : Group.IsSolvable ↥R := hsolR
        have hsolZ : Group.IsSolvable ↥(Y.map c'.toMonoidHom) :=
          Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hZle)
        have hperfZ : Group.IsPerfect ↥(Y.map c'.toMonoidHom) := ⟨hqsZ.1⟩
        exact (Group.IsPerfect.not_isSolvable ↥(Y.map c'.toMonoidHom) hsolZ).elim
      ·
        have hf3 : 3 ≤ f := by omega
        have h2f : 2 < 2 ^ f := by
          calc 2 = 2 ^ 1 := by norm_num
            _ < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
        obtain ⟨c, R, hcR, hRC, hcomm, hRq, U, hU, ⟨eR⟩⟩ :=
          CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model_unitary Nat.prime_two hf
            (by norm_num) (CFSG.LocalAnalysis.GLTheoremA.K148Inner.two_pow_mod_three_of_odd hodd)
            h2f hK hσ hy hy3 hy1
        set c' : MulAut (CFSG.LieType.Chevalley.graphFixedRootGroup
          CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) := MulAut.conj c with hc'def
        have hc'eq : c' (g' z) = c * (g' z) * c⁻¹ := by rw [hc'def, MulAut.conj_apply]
        have hZcomp : CFSG.Assembly.IsComponentOf (Y.map c'.toMonoidHom)
            (Subgroup.centralizer ({c' (g' z)} : Set
              (CFSG.LieType.Chevalley.graphFixedRootGroup
                CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom))) := by
          have h := CFSG.LocalAnalysis.GLTheoremA.tcent_isComponentOf_map c' hYcomp
          rw [CFSG.LocalAnalysis.GLTheoremA.tcent_map_centralizer c' (g' z)] at h
          exact h
        have hZR : Y.map c'.toMonoidHom = R := by
          refine CFSG.LocalAnalysis.GLTheoremA.tcent_component_eq hZcomp ?_ ?_ hRq
          · rw [hc'eq]; exact hRC
          · intro a ha b hb
            rw [hc'eq] at ha hb
            exact hcomm a ha b hb
        have hcard : Nat.card X = Nat.card R := by
          rw [← hYcard, ← Subgroup.card_map_of_injective (K := Y) (f := c'.toMonoidHom) c'.injective, hZR]
        rw [hcard, Nat.card_congr eR.toEquiv,
          CFSG.RankThree.PartTwo.Sec4.E27.card_subgroup_unitarySet (ℓ := 2) (f := f) hf U hU,
          k328det_sl3eps,
          if_neg (by
            rw [CFSG.LocalAnalysis.GLTheoremA.K148Inner.two_pow_mod_three_of_odd hodd]
            norm_num)]
        ring_nf
  ·
    set g' : MulAut (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) := MulAut.conj g with hg'def
    set Y : Subgroup (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) := X.map g'.toMonoidHom with hYdef
    have hYcomp : CFSG.Assembly.IsComponentOf Y (Subgroup.centralizer ({g' z} : Set
        (CFSG.LieType.Chevalley.graphFixedRootGroup
          CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom))) := by
      have h := CFSG.LocalAnalysis.GLTheoremA.tcent_isComponentOf_map g' hComp
      rw [CFSG.LocalAnalysis.GLTheoremA.tcent_map_centralizer g' z] at h
      rwa [hYdef]
    have hgz : g' z = g * z * g⁻¹ := by rw [hg'def, MulAut.conj_apply]
    have hyC : g' z ∈ Subgroup.centralizer
        ((CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
          Subgroup (CFSG.LieType.Chevalley.graphFixedRootGroup
            CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom)) :
          Set (CFSG.LieType.Chevalley.graphFixedRootGroup
            CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom)) := by
      rw [hgz]; exact hg
    have hy3 : (g' z) ^ 3 = 1 := by rw [← map_pow, hZ3, map_one]
    have hy1 : g' z ≠ 1 := by
      intro h1
      apply hz1
      have h2 := congrArg g'.symm h1
      rw [MulEquiv.symm_apply_apply, map_one] at h2
      exact h2
    obtain ⟨hcomm, -⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeBCent_holds
      K (2 ^ f) σ hK hσ h3 (g' z) hyC hy3 hy1
    have hSC : CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom ≤
        Subgroup.centralizer ({g' z} : Set (CFSG.LieType.Chevalley.graphFixedRootGroup
          CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom)) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hyC s hs
    have hσ3 : σ ^ 3 = 1 := by
      refine RingEquiv.ext fun c => ?_
      have := CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq hK hσ c
      simpa [pow_succ] using this
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left
            (by
              calc 2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf) 3
    have hSq : CFSG.IsQuasisimple
        ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) :=
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.isQuasisimple_d4ShortSL2 hσ3 hK4
    have hYeqS : Y = CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :=
      CFSG.LocalAnalysis.GLTheoremA.tcent_component_eq hYcomp hSC hcomm hSq
    have hyY : g' z ∈ Y := by
      rw [hgz, hYdef]
      exact Subgroup.mem_map_of_mem g'.toMonoidHom hzX
    have hzy : (⟨g' z, hYeqS ▸ hyY⟩ :
        ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)) ∈
        Subgroup.center ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (hYcomp.1 (hYeqS.symm ▸ y.2))
    have hSZ := k328dd4c_center_d4ShortSL2 hσ3
    rw [hSZ, Subgroup.mem_bot] at hzy
    exact (hy1 (Subtype.ext_iff.mp hzy)).elim

private theorem k328dd4c_transport
    {S : Type} [Group S] [Finite S] {f : ℕ} (h : LieModel S .trialityD4 0 2 f)
    {z : S} (hz : orderOf z = 3) {X : Subgroup S} (hzX : z ∈ X)
    (hXC : X ≤ Subgroup.centralizer ({z} : Set S))
    (hsub : (X.subgroupOf (Subgroup.centralizer ({z} : Set S))).IsSubnormal)
    (hqs : CFSG.Open.IsQuasisimple ↥X) :
    Nat.card X = k328det_sl3eps (2 ^ f) := by
  have hf : 1 ≤ f := h.admissible.2.1
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 2 f :=
    h.chevalleyExceptionalModel (by decide)
  have htw : CFSG.Blueprint.TwistedChevalleyModel S .D4 (2 ^ f) := hce.2
  obtain ⟨K, hKfld, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card
      CFSG.Blueprint.Chevalley.TwistTag.D4 Nat.prime_two hf htw
  have hz' : orderOf (e z) = 3 := by rw [MulEquiv.orderOf_eq, hz]
  have hzX' : e z ∈ X.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom hzX
  have hXC' : X.map e.toMonoidHom ≤
      Subgroup.centralizer ({e z} : Set (CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom)) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.tcent_map_centralizer e z]
    exact Subgroup.map_mono hXC
  have hsub' : ((X.map e.toMonoidHom).subgroupOf (Subgroup.centralizer ({e z} : Set
      (CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4
        K σ.toRingHom)))).IsSubnormal := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.tcent_map_centralizer e z]
    exact isSubnormal_subgroupOf_map' e hXC hsub
  have hqs' : CFSG.Open.IsQuasisimple ↥(X.map e.toMonoidHom) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (X.equivMapOfInjective e.toMonoidHom e.injective).symm hqs
  have hcard : Nat.card (X.map e.toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective e.injective
  rw [← hcard]
  exact k328dd4c_model_comp hf K hKcard hσ hz' hzX' hXC' hsub' hqs'

theorem k328det_triD4TwoComp :
    ∀ (S : Type) [Group S] [Finite S] (f : ℕ), LieModel S .trialityD4 0 2 f → ∀ z : S,
      orderOf z = 3 → ∀ X : Subgroup S, z ∈ X → X ≤ Subgroup.centralizer ({z} : Set S) →
        (X.subgroupOf (Subgroup.centralizer ({z} : Set S))).IsSubnormal →
        CFSG.Open.IsQuasisimple ↥X → Nat.card X = k328det_sl3eps (2 ^ f) := by
  intro S _ _ f h z hz X hzX hXC hsub hqs
  exact k328dd4c_transport h hz hzX hXC hsub hqs

section
open Matrix Polynomial CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.HardMathSupport.Dickson.Bal207.D4Graph

private theorem k328dd4o_lift_center {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (U : Subgroup (GL ι K)) (X : Subgroup (StatedProj U))
    (hXq : CFSG.Open.IsQuasisimple ↥X) :
    ∃ (Y : Subgroup U) (ψ : Y →* ↥X),
      ⁅Y, Y⁆ = Y ∧ Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center Y ∧
        (Subgroup.center Y).map ψ = Subgroup.center ↥X := by
  let N : Subgroup U := (StatedScalars ι K).subgroupOf U
  let T := StatedProj U
  let π : U →* T := QuotientGroup.mk' N
  let Xp : Subgroup U := X.comap π
  have hXp : Xp.map π = X :=
    (Subgroup.map_comap_eq_self_of_surjective (f := π) (QuotientGroup.mk'_surjective N)) X
  let Y : Subgroup U := CFSG.Quasithin.perfectCore Xp
  have hYperf : ⁅Y, Y⁆ = Y := CFSG.Quasithin.perfectCore_perfect Xp
  have hXcomm : ⁅X, X⁆ = X :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hXq.1)
  have hYmap : Y.map π = X := by
    rw [show Y = CFSG.Quasithin.perfectCore Xp from rfl, CFSG.Quasithin.map_perfectCore,
      hXp, CFSG.Quasithin.perfectCore_eq_self_of_perfect hXcomm]
  let πY : Y →* T := π.comp Y.subtype
  have hrange : πY.range ≤ X := by
    rw [show πY.range = Y.map π by ext x; simp [πY], hYmap]
  let ψ : Y →* ↥X := πY.codRestrict X (fun x => by
    rw [← hYmap]
    exact Subgroup.mem_map_of_mem π x.2)
  have hψ : Function.Surjective ψ := by
    intro x
    have hx : (x : T) ∈ Y.map π := by rw [hYmap]; exact x.2
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    refine ⟨⟨y, hy⟩, ?_⟩
    exact Subtype.ext hxy
  have hker : ψ.ker ≤ Subgroup.center Y := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    have hy1 : ψ y = 1 := hy
    have hπy : π (y : U) = 1 := by
      have := congrArg (fun w : ↥X => (w : T)) hy1
      simpa [ψ, πY] using this
    have hyN : (y : U) ∈ N := by
      rw [← QuotientGroup.ker_mk' N]
      exact MonoidHom.mem_ker.mpr hπy
    have hcen : (y : U) ∈ Subgroup.center U :=
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center U hyN
    have hcomm := Subgroup.mem_center_iff.mp hcen (z : U)
    exact Subtype.ext hcomm
  refine ⟨Y, ψ, hYperf, hψ, hker, ?_⟩
  have hYcommtop : commutator ↥Y = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hYperf)
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_center_of_surjective
    hYcommtop ψ hψ hker

private theorem k328dd4o_three_dvd_pow_six (p f : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    3 ∣ p ^ (6 * f) - 1 := by
  have hp3mod : p % 3 = 1 ∨ p % 3 = 2 := by
    have h := Nat.mod_lt p (by norm_num : 0 < 3)
    have hne : p % 3 ≠ 0 := by
      intro h0
      have hdvd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h0
      rcases hp.eq_one_or_self_of_dvd 3 hdvd with h1 | h1
      · omega
      · exact hp3 h1.symm
    omega
  have hp2 : 1 ≡ p ^ 2 [MOD 3] := by
    rw [Nat.ModEq]
    rcases hp3mod with h | h <;> rw [pow_two, Nat.mul_mod, h]
  have hpow : 1 ≡ p ^ (6 * f) [MOD 3] := by
    have h1 : p ^ (6 * f) = (p ^ 2) ^ (3 * f) := by rw [← pow_mul]; ring_nf
    rw [h1]
    simpa using hp2.pow (3 * f)
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.one_le)).mp hpow

private theorem k328dd4o_finite_ext {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (f0 : K →+* E),
      Function.Injective f0 ∧ (∃ ω : E, ω ^ 3 = 1 ∧ ω ≠ 1) ∧ ringChar E ≠ 2 := by
  have _ : Fact p.Prime := ⟨hp⟩
  have hcardK : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hcardE : Nat.card (GaloisField p (6 * f)) = p ^ (6 * f) :=
    GaloisField.card p (6 * f) (by omega)
  have _ : Finite (GaloisField p (6 * f)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardE]; exact (pow_pos hp.pos _).ne')
  have hcharK : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hcardK
  have hcharE : CharP (GaloisField p (6 * f)) p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hcardE
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  let _ : Algebra (ZMod p) (GaloisField p (6 * f)) := ZMod.algebra (GaloisField p (6 * f)) p
  have hfrK : Module.finrank (ZMod p) K = 3 * f := by
    have := FiniteField.pow_finrank_eq_natCard p K
    rw [hcardK] at this
    exact Nat.pow_right_injective hp.one_lt this
  have hfrE : Module.finrank (ZMod p) (GaloisField p (6 * f)) = 6 * f := by
    have := FiniteField.pow_finrank_eq_natCard p (GaloisField p (6 * f))
    rw [hcardE] at this
    exact Nat.pow_right_injective hp.one_lt this
  obtain ⟨f0⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p) (K := K)
    (L := GaloisField p (6 * f)) (by rw [hfrK, hfrE]; exact ⟨2, by ring⟩)
  have h3 : 3 ∣ Nat.card (GaloisField p (6 * f)) - 1 := by
    rw [hcardE]; exact k328dd4o_three_dvd_pow_six p f hp hp3
  obtain ⟨ω, hω1, hω3⟩ := CFSG.CGT.PushingUpLit.CGT6M.exists_cube_root_of_unity
    (GaloisField p (6 * f)) h3
  refine ⟨GaloisField p (6 * f), inferInstance, inferInstance, f0.toRingHom,
    f0.toRingHom.injective, ⟨ω, hω3, hω1⟩, ?_⟩
  rw [ringChar.eq (GaloisField p (6 * f)) p]
  exact hp2

private theorem k328dd4o_eigenspace_singular {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {A : GL (Fin d) K} (hA : A ∈ matrixIsometries Q)
    {μ : K} (hμ : μ ^ 2 ≠ 1) {v : Fin d → K}
    (hv : Matrix.toLin' (A : Matrix (Fin d) (Fin d) K) v = μ • v) : Q v = 0 := by
  have hml : Matrix.toLin' (A : Matrix (Fin d) (Fin d) K) v = matrixLinearEquiv A v := by
    rw [matrixLinearEquiv_apply]; rfl
  have h1 : Q (matrixLinearEquiv A v) = Q v := (mem_matrixIsometries_iff Q A).mp hA v
  rw [← hml, hv, QuadraticMap.map_smul] at h1
  have h2 : μ ^ 2 * Q v = Q v := by simpa [pow_two, smul_eq_mul] using h1
  have h3 : (1 - μ ^ 2) * Q v = 0 := by rw [sub_mul, one_mul, h2, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hμ))

private theorem k328dd4o_eigenspace_finrank_le {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {A : GL (Fin d) K} (hA : A ∈ matrixIsometries Q) {μ : K} (hμ : μ ^ 2 ≠ 1) :
    2 * Module.finrank K (Module.End.eigenspace
      (Matrix.toLin' (A : Matrix (Fin d) (Fin d) K)) μ) ≤ d := by
  have h1 := CFSG.Blueprint.EvenSource.two_mul_finrank_le_of_singular hQ
    (W := Module.End.eigenspace (Matrix.toLin' (A : Matrix (Fin d) (Fin d) K)) μ)
    (fun v hv => k328dd4o_eigenspace_singular hA hμ (Module.End.mem_eigenspace_iff.mp hv))
  have h2 : Module.finrank K (Fin d → K) = d := by simp
  omega

private theorem k328dd4o_test_poly {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1)
    (hT3 : T ^ 3 = 1) :
    (T - 1) * (T - ω • 1) * (T - ω ^ 2 • 1) = 0 := by
  have h1 : (1 : K) + ω + ω ^ 2 = 0 := by linear_combination hω
  have hfac : (Polynomial.X - Polynomial.C (1 : K)) * (Polynomial.X - Polynomial.C ω) *
      (Polynomial.X - Polynomial.C (ω ^ 2)) = Polynomial.X ^ 3 - Polynomial.C (1 : K) := by
    rw [map_one]
    ring_nf
    have hA : (1 : K[X]) + Polynomial.C ω + Polynomial.C (ω ^ 2) = 0 := by
      simpa [map_add, map_one] using congrArg (Polynomial.C : K →+* K[X]) h1
    have hB : Polynomial.C ω * Polynomial.C (ω ^ 2) = 1 := by
      have h2 : ω * ω ^ 2 = 1 := by linear_combination hω3
      simpa [map_mul, map_one] using congrArg (Polynomial.C : K →+* K[X]) h2
    linear_combination (Polynomial.X - Polynomial.X ^ 2) * hA + (Polynomial.X - 1) * hB
  let aevalT : K[X] →ₐ[K] Module.End K V :=
    @Polynomial.aeval K (Module.End K V) _ _ (Module.End.instAlgebra K K V) T
  have h := congrArg aevalT hfac
  simpa only [aevalT, Polynomial.aeval_X, Polynomial.aeval_C, map_neg, map_add, map_sub, map_mul,
    map_pow, map_one, ← Algebra.algebraMap_eq_smul_one, hT3, sub_eq_add_neg, add_neg_cancel] using h

private theorem k328dd4o_eigenvalue_exists {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1) (hT3 : T ^ 3 = 1) (hTne : T ≠ 1) :
    T.eigenspace ω ≠ ⊥ ∨ T.eigenspace (ω ^ 2) ≠ ⊥ := by
  by_contra h
  rw [not_or] at h
  have hωe : T.eigenspace ω = ⊥ := by simpa using h.1
  have hω2e : T.eigenspace (ω ^ 2) = ⊥ := by simpa using h.2
  have hker1 : (T - ω • (1 : Module.End K V)).ker = ⊥ := by
    rw [← Module.End.eigenspace_def]
    exact hωe
  have hker2 : (T - ω ^ 2 • (1 : Module.End K V)).ker = ⊥ := by
    rw [← Module.End.eigenspace_def]
    exact hω2e
  have hinj1 : Function.Injective (T - ω • (1 : Module.End K V)) := by simpa using LinearMap.ker_eq_bot.mp hker1
  have hinj2 : Function.Injective (T - ω ^ 2 • (1 : Module.End K V)) := by simpa using LinearMap.ker_eq_bot.mp hker2
  have hsurj1 : Function.Surjective (T - ω • (1 : Module.End K V)) :=
    LinearMap.injective_iff_surjective.mp hinj1
  have hsurj2 : Function.Surjective (T - ω ^ 2 • (1 : Module.End K V)) :=
    LinearMap.injective_iff_surjective.mp hinj2
  have hfac := k328dd4o_test_poly T hω hω3 hT3
  let g : Module.End K V := (T - ω • (1 : Module.End K V)) * (T - ω ^ 2 • (1 : Module.End K V))
  have hsurjG : Function.Surjective g := by
    rw [show g = (T - ω • (1 : Module.End K V)).comp (T - ω ^ 2 • (1 : Module.End K V)) by
      simp [g, Module.End.mul_eq_comp]]
    exact hsurj1.comp hsurj2
  have hzero : (T - 1) * g = 0 := by
    rw [show (T - 1) * g = (T - 1) * (T - ω • (1 : Module.End K V)) * (T - ω ^ 2 • (1 : Module.End K V)) by
      simp [g, mul_assoc]]
    exact hfac
  have hTsub : T - 1 = 0 := by
    ext v
    obtain ⟨u, hu⟩ := hsurjG v
    have h1 : ((T - 1) * g) u = 0 := by rw [hzero]; rfl
    rw [Module.End.mul_eq_comp, LinearMap.comp_apply, hu] at h1
    exact h1
  exact hTne (sub_eq_zero.mp hTsub)

private theorem k328dd4o_embed {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hLie : LieModel S .trialityD4 0 p f) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E)
      (φ : S →* StatedProj (StatedOmega (StatedQuadPlus 4 E))) (ω : E),
      Function.Injective φ ∧ ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ringChar E ≠ 2 := by
  have hadm : CFSG.Open.StatedLieAdmissible .trialityD4 0 p f := hLie.admissible
  obtain ⟨hp, hf, -⟩ := hadm
  have _ : Fact p.Prime := ⟨hp⟩
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 p f :=
    hLie.chevalleyExceptionalModel (by decide)
  have htw : CFSG.Blueprint.TwistedChevalleyModel S .D4 (p ^ f) := hce.2
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e1⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  let _ : Field K := hKf
  let _ : Finite K := hKfin
  obtain ⟨E, hEf, hEfin, f0, hf0inj, ⟨ω, hω3, hω1⟩, hE2⟩ :=
    k328dd4o_finite_ext hp hp2 hp3 hf hKcard
  let _ : Field E := hEf
  let _ : Finite E := hEfin
  let U : Subgroup (GL (Fin 4 ⊕ Fin 4) E) := StatedOmega (StatedQuadPlus 4 E)
  have hmap : (adjointGroup Tag.D4 K).map (baseChangeGL (τ := Tag.D4) f0) ≤
      adjointGroup Tag.D4 E := by
    rw [map_baseChangeGL_adjointGroup]
    refine Subgroup.closure_mono ?_
    rintro g ⟨i, c, rfl | rfl⟩
    · exact ⟨i, f0 c, Or.inl rfl⟩
    · exact ⟨i, f0 c, Or.inr rfl⟩
  let ψ0 : graphFixedRootGroup .D4 K σ.toRingHom →* adjointGroup Tag.D4 E :=
    ((baseChangeGL (τ := Tag.D4) f0).comp
      (graphFixedRootGroup .D4 K σ.toRingHom).subtype).codRestrict
        (adjointGroup Tag.D4 E)
        (fun g => hmap (Subgroup.mem_map_of_mem _
          (((graphFixedRootGroup_le .D4 K σ.toRingHom).trans inf_le_left) g.2)))
  have hψ0inj : Function.Injective ψ0 := by
    intro a b hab
    have h1 : baseChangeGL (τ := Tag.D4) f0 (a : ModGL (TwistTag.D4).tag K) =
        baseChangeGL (τ := Tag.D4) f0 (b : ModGL (TwistTag.D4).tag K) :=
      Subtype.ext_iff.mp hab
    exact Subtype.ext (baseChangeGL_injective (τ := Tag.D4) f0 h1)
  let ψ1 : graphFixedRootGroup .D4 K σ.toRingHom →*
      StatedProj (StatedOmega (StatedQuadPlus 4 E)) :=
    (isoAdj E).symm.toMonoidHom.comp ψ0
  have hψ1inj : Function.Injective ψ1 := (isoAdj E).symm.injective.comp hψ0inj
  let φ : S →* StatedProj (StatedOmega (StatedQuadPlus 4 E)) := ψ1.comp e1.toMonoidHom
  have hφinj : Function.Injective φ := hψ1inj.comp e1.injective
  exact ⟨E, hEf, hEfin, φ, ω, hφinj, hω3, hω1, hE2⟩

private theorem k328dd4o_nondegenerate_coordinateQuadPlus (n : ℕ) (K : Type) [Field K] :
    (QuadraticMap.polarBilin (coordinateQuadPlus n K)).Nondegenerate :=
  CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_of_isometryEquiv
    (reindexQuadraticIsometry (plusIndexEquiv n) (quadPlus n K))
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K)

theorem k328det_triD4OddExcluded :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p ≠ 2 → p ≠ 3 →
      LieModel S .trialityD4 0 p f → ¬ K328DetPosIn S := by
  intro S _ _ hS p f hp2 hp3 hLie hPos
  obtain ⟨E, hEf, hEfin, φ, ω, hφinj, hω3, hω1, hE2⟩ :=
    k328dd4o_embed hp2 hp3 hLie
  let _ : Field E := hEf
  let _ : Finite E := hEfin
  let U : Subgroup (GL (Fin 4 ⊕ Fin 4) E) := StatedOmega (StatedQuadPlus 4 E)
  obtain ⟨Z, X, hpos, hXne⟩ := hPos
  let X' : Subgroup (StatedProj U) := X.map φ
  let eX : ↥X ≃* ↥X' := X.equivMapOfInjective φ hφinj
  have hX'q : CFSG.Open.IsQuasisimple ↥X' :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eX.symm hpos.2.2.2.2.1
  have hX'center : Nat.card (Subgroup.center ↥X') = 3 := by
    have hmapc := Subgroup.map_center_eq eX
    rw [← hmapc, Subgroup.card_map_of_injective eX.injective]
    exact hpos.2.2.2.2.2.1
  obtain ⟨Y, ψ, hYperf, hψsurj, hψker, hψcenter⟩ := k328dd4o_lift_center U X' hX'q
  have _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card (Subgroup.center Y) := by
    rw [← hX'center, ← hψcenter]
    exact Subgroup.card_map_dvd (H := Subgroup.center Y) ψ
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Y) 3 hdvd
  let zY : Y := (z : Y)
  have hzYord : orderOf zY = 3 := by rw [Subgroup.orderOf_coe]; exact hzord
  let W : Type := ↥X' ⧸ Subgroup.center ↥X'
  have hWlie : LieModel W .PSL 3 2 2 ∨ LieModel W .PSU 3 2 3 := by
    let eW : (↥X ⧸ Subgroup.center ↥X) ≃* W :=
      QuotientGroup.congr _ _ eX (Subgroup.map_center_eq eX)
    rcases hpos.2.2.2.2.2.2 with h | h
    · exact Or.inl (LieModel.of_mulEquiv eW h)
    · exact Or.inr (LieModel.of_mulEquiv eW h)
  let φY : Y →* W := (QuotientGroup.mk' (Subgroup.center ↥X')).comp ψ
  have hφYsurj : Function.Surjective φY := (QuotientGroup.mk'_surjective _).comp hψsurj
  have hφYker : φY.ker ≤ Subgroup.center Y := by
    intro y hy
    have hy' : ψ y ∈ Subgroup.center ↥X' := (QuotientGroup.eq_one_iff (ψ y)).mp hy
    have hy'' : ψ y ∈ (Subgroup.center Y).map ψ := by rw [hψcenter]; exact hy'
    obtain ⟨z0, hz0, hz0eq⟩ := hy''
    have hmem : y * z0⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hz0eq]; simp
    have hcen : y * z0⁻¹ ∈ Subgroup.center Y := hψker hmem
    have heq : y = (y * z0⁻¹) * z0 := by group
    rw [heq]
    exact Subgroup.mul_mem _ hcen hz0
  have hUdet : U ≤ (GeneralLinearGroup.det : GL (Fin 4 ⊕ Fin 4) E →* Eˣ).ker := by
    unfold U
    rw [StatedOmega]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hdetreindex : ∀ A : GL (Fin 4 ⊕ Fin 4) E,
      Matrix.det ((reindexMatrixEquiv (plusIndexEquiv 4) A : GL (Fin 8) E) :
        Matrix (Fin 8) (Fin 8) E) = Matrix.det (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) E) := by
    intro A
    rw [reindexMatrixEquiv_val]
    exact Matrix.det_reindex_self (plusIndexEquiv 4) A.val
  let eGL : Y →* GL (Fin 8) E :=
    (reindexMatrixEquiv (plusIndexEquiv 4)).toMonoidHom.comp (U.subtype.comp Y.subtype)
  have heGLmem : ∀ y : Y, eGL y ∈ (GeneralLinearGroup.det : GL (Fin 8) E →* Eˣ).ker := by
    intro y
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp only [eGL, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
    rw [hdetreindex]
    simpa using congrArg Units.val (MonoidHom.mem_ker.mp (hUdet ((y : U).2)))
  let ρ : Y →* Matrix.SpecialLinearGroup (Fin 8) E :=
    (Matrix.SpecialLinearGroup.toGLKerEquiv).symm.toMonoidHom.comp (eGL.codRestrict _ heGLmem)
  have hρinj : Function.Injective ρ := by
    intro a b hab
    have h1 : (eGL.codRestrict _ heGLmem) a = (eGL.codRestrict _ heGLmem) b := by
      have := congrArg (fun x => (Matrix.SpecialLinearGroup.toGLKerEquiv x :
        (GeneralLinearGroup.det : GL (Fin 8) E →* Eˣ).ker)) hab
      simpa [ρ] using this
    have h2 : eGL a = eGL b := Subtype.ext_iff.mp h1
    exact Subtype.ext (Subtype.ext ((reindexMatrixEquiv (plusIndexEquiv 4)).injective h2))
  let Ysl : Subgroup (Matrix.SpecialLinearGroup (Fin 8) E) := ρ.range
  have hrinj : Function.Injective ρ.rangeRestrict := fun a b h => hρinj (Subtype.ext_iff.mp h)
  let eYsl : Y ≃* Ysl := MulEquiv.ofBijective ρ.rangeRestrict ⟨hrinj, ρ.rangeRestrict_surjective⟩
  let zsl : Ysl := ⟨ρ zY, ⟨zY, rfl⟩⟩
  have hzsl_eq : zsl = eYsl zY := rfl
  have hYslperf : ⁅Ysl, Ysl⁆ = Ysl := by
    have h2 : commutator ↥Y = ⊤ :=
      Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hYperf)
    rw [commutator_def] at h2
    have h1 : (⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆).map ρ = ⁅Ysl, Ysl⁆ := by
      rw [Subgroup.map_commutator]
      congr 1 <;> exact Subgroup.map_top ρ
    rw [← h1, h2, Subgroup.map_top]
  have hzsl_center : zsl ∈ Subgroup.center Ysl := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp w.2
    have hw : w = ⟨ρ y, ⟨y, rfl⟩⟩ := Subtype.ext hy.symm
    rw [hw]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hz : y * zY = zY * y := Subgroup.mem_center_iff.mp z.2 y
    exact (map_mul ρ y zY).symm.trans ((congrArg ρ hz).trans (map_mul ρ zY y))
  have hzsl_ord : orderOf zsl = 3 := by
    rw [hzsl_eq]
    exact (MulEquiv.orderOf_eq eYsl zY).trans hzYord
  have hzsl_ordSL : orderOf (zsl : Matrix.SpecialLinearGroup (Fin 8) E) = 3 := by
    rw [Subgroup.orderOf_coe]; exact hzsl_ord
  have hzsl_ne_one : zsl ≠ 1 := by
    intro h
    have h1 : ρ zY = 1 := Subtype.ext_iff.mp h
    have h2 : zY = 1 := hρinj (by rw [h1, map_one])
    rw [h2, orderOf_one] at hzYord
    norm_num at hzYord
  have hzsl_mem : ((zsl : Ysl) : GL (Fin 8) E) ∈ matrixIsometries (coordinateQuadPlus 4 E) := by
    have h1 : ((zsl : Ysl) : GL (Fin 8) E) = eGL zY := by
      change ((ρ zY : Matrix.SpecialLinearGroup (Fin 8) E) : GL (Fin 8) E) = eGL zY
      ext i j
      rfl
    rw [h1]
    have h2 : eGL zY ∈ matrixDerived (coordinateQuadPlus 4 E) := by
      have h3 : eGL zY = reindexMatrixEquiv (plusIndexEquiv 4)
          ((zY : U) : GL (Fin 4 ⊕ Fin 4) E) := rfl
      rw [h3]
      let eR : U ≃* matrixDerived (coordinateQuadPlus 4 E) :=
        statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 E) (coe_quadPlus 4 E)
      rw [← statedDerivedReindexEquiv_val (plusIndexEquiv 4) (quadPlus 4 E)
        (coe_quadPlus 4 E) (zY : U)]
      exact (eR (zY : U)).2
    exact (matrixDerived_le_isometries _) h2
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      have h' : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
      rw [h', hω3, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)
  have hωsq : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω * ω ^ 2 := by rw [h]; ring
      _ = ω ^ 3 := by ring
      _ = 1 := hω3
  have hω2sq : (ω ^ 2) ^ 2 ≠ 1 := by
    intro h
    apply hω1
    have h' : ω ^ 4 = 1 := by
      rw [← pow_mul] at h
      simpa using h
    have h4 : ω ^ 4 = ω := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hω3, one_mul, pow_one]
    have h5 : ω = 1 := by rw [← h4]; exact h'
    exact h5
  let zslGL : GL (Fin 8) E := ((zsl : Ysl) : GL (Fin 8) E)
  let T : Module.End E (Fin 8 → E) := Matrix.toLin' (zslGL : Matrix (Fin 8) (Fin 8) E)
  have hzsl3 : zsl ^ 3 = 1 := by rw [← hzsl_ord]; exact pow_orderOf_eq_one zsl
  have hzslMat3 : ((zslGL : Matrix (Fin 8) (Fin 8) E)) ^ 3 = 1 := by
    have h := congrArg (fun x : Ysl =>
      (((x : Matrix.SpecialLinearGroup (Fin 8) E) : GL (Fin 8) E) : Matrix (Fin 8) (Fin 8) E)) hzsl3
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one, zslGL] using h
  have hT3 : T ^ 3 = 1 := by
    dsimp [T]
    rw [← Matrix.toLin'_pow, hzslMat3, Matrix.toLin'_one]
    rfl
  have hTne : T ≠ 1 := by
    intro h
    apply hzsl_ne_one
    have h1 : (zslGL : Matrix (Fin 8) (Fin 8) E) = 1 := by
      have := congrArg LinearMap.toMatrix' h
      simpa [T, LinearMap.toMatrix'_toLin'] using this
    exact Subtype.ext (Subtype.ext h1)
  have hnd : (QuadraticMap.polarBilin (coordinateQuadPlus 4 E)).Nondegenerate :=
    k328dd4o_nondegenerate_coordinateQuadPlus 4 E
  have hzsl_central : ∀ y ∈ Ysl, Commute (zsl : Matrix.SpecialLinearGroup (Fin 8) E) y :=
    fun y hy => (Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hzsl_center ⟨y, hy⟩)).symm
  let φYsl : Ysl →* W := φY.comp eYsl.symm.toMonoidHom
  have hφYslsurj : Function.Surjective φYsl := hφYsurj.comp eYsl.symm.surjective
  have hφYslker : φYsl.ker ≤ Subgroup.center Ysl := by
    intro y hy
    have hy' : eYsl.symm y ∈ φY.ker := hy
    have hy'' : eYsl.symm y ∈ Subgroup.center Y := hφYker hy'
    have h1 : y = eYsl (eYsl.symm y) := (eYsl.apply_symm_apply y).symm
    rw [h1, ← Subgroup.map_center_eq eYsl]
    exact Subgroup.mem_map_of_mem _ hy''
  rcases k328dd4o_eigenvalue_exists T hω hω3 hT3 hTne with hEig | hEig
  · have hdim := k328dd4o_eigenspace_finrank_le hnd hzsl_mem (A := zslGL) hωsq
    have hdim4 : Module.finrank E (Module.End.eigenspace
        (Matrix.toLin' (zslGL : Matrix (Fin 8) (Fin 8) E)) ω) ≤ 4 := by
      exact Nat.le_of_mul_le_mul_left (by simpa [mul_comm] using hdim) (by norm_num)
    exact (k328det_oddEigenblock E hE2 8 Ysl hYslperf (zsl : Matrix.SpecialLinearGroup (Fin 8) E)
      zsl.2 hzsl_central hzsl_ordSL ω hω1 hEig hdim4 W φYsl hφYslsurj hφYslker) hWlie
  · have hdim := k328dd4o_eigenspace_finrank_le hnd hzsl_mem (A := zslGL) hω2sq
    have hdim4 : Module.finrank E (Module.End.eigenspace
        (Matrix.toLin' (zslGL : Matrix (Fin 8) (Fin 8) E)) (ω ^ 2)) ≤ 4 := by
      exact Nat.le_of_mul_le_mul_left (by simpa [mul_comm] using hdim) (by norm_num)
    exact (k328det_oddEigenblock E hE2 8 Ysl hYslperf (zsl : Matrix.SpecialLinearGroup (Fin 8) E)
      zsl.2 hzsl_central hzsl_ordSL (ω ^ 2) hωsq hEig hdim4 W φYsl hφYslsurj hφYslker) hWlie
end

private theorem k328dx3_g2_notPos {S : Type} [Group S] [Finite S] {f : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible .G2 0 3 f)
    (hcard : Nat.card S = CFSG.EvenSmallLie.CatalogOrders.lieOrd .G2 0 (3 ^ f))
    (h3f : 3 * f ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S))
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3) : ¬ K328DetPosIn S := by
  have hf : 1 ≤ f := hadm.2.1
  have hf1 : f = 1 := by omega
  subst hf1
  refine k328det_not_posIn_of_card ?_ ?_ <;> rw [hcard] <;> decide +kernel

private theorem k328dx3_triD4_notPos {S : Type} [Group S] [Finite S]
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S))
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3) : ¬ K328DetPosIn S := by
  exfalso
  omega

theorem k328det_excCharThree :
    ∀ (S : Type) [Group S] [Finite S] (f : ℕ),
      (LieModel S .G2 0 3 f ∨ LieModel S .trialityD4 0 3 f) →
        CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3 → ¬ K328DetPosIn S := by
  intro S _ _ f hL hrank
  rcases hL with hG2 | hD4
  · have hadm : CFSG.Open.StatedLieAdmissible .G2 0 3 f := hG2.admissible
    have hCE : CFSG.Blueprint.ChevalleyExceptionalModel S .G2 3 f :=
      hG2.chevalleyExceptionalModel (by decide)
    have hcard : Nat.card S = CFSG.EvenSmallLie.CatalogOrders.lieOrd .G2 0 (3 ^ f) :=
      CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional hCE
    obtain ⟨-, hU⟩ := hCE
    have h3prime : Fact (Nat.Prime 3) := ⟨hadm.1⟩
    have h3f : 3 * f ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
      CFSG.SectionRank.three_mul_le_pRank_of_G2Model hU
    exact k328dx3_g2_notPos hadm hcard h3f hrank
  · have hadm : CFSG.Open.StatedLieAdmissible .trialityD4 0 3 f := hD4.admissible
    have hCE : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 3 f :=
      hD4.chevalleyExceptionalModel (by decide)
    obtain ⟨-, hT⟩ := hCE
    have hf : 1 ≤ f := hadm.2.1
    have h3prime : Fact (Nat.Prime 3) := ⟨hadm.1⟩
    have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
      CFSG.SectionRank.four_le_pRank_of_trialityD4Model hf hT
    exact k328dx3_triD4_notPos h4 hrank

private theorem k328dg2_sl3eps_eq (q : ℕ) (hq : 3 ≤ q)
    (h : k328det_sl3eps q = 60480 ∨ k328det_sl3eps q = 16547328) :
    q = 4 ∨ q = 8 := by
  have hq8 : q ≤ 8 := by
    by_contra hle
    have hq9 : 9 ≤ q := by omega
    have hbase : q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) ≤ k328det_sl3eps q := by
      rw [k328det_sl3eps]
      split_ifs with h3
      · exact le_rfl
      · exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (by omega : q ^ 3 - 1 ≤ q ^ 3 + 1))
    have hmono : 9 ^ 3 * (9 ^ 3 - 1) * (9 ^ 2 - 1) ≤
        q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hq9 3)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq9 3) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq9 2) 1)
    have hbig : 16547328 < k328det_sl3eps q := by
      have : (42456960 : ℕ) ≤ k328det_sl3eps q := le_trans hmono hbase
      omega
    rcases h with h | h <;> omega
  interval_cases q
  · exfalso; revert h; norm_num [k328det_sl3eps]
  · left; rfl
  · exfalso; revert h; norm_num [k328det_sl3eps]
  · exfalso; revert h; norm_num [k328det_sl3eps]
  · exfalso; revert h; norm_num [k328det_sl3eps]
  · right; rfl

private theorem k328dg2_pow_eq (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (h : p ^ f = 4 ∨ p ^ f = 8) : p = 2 ∧ (f = 2 ∨ f = 3) := by
  have hp2 : p = 2 := by
    have h24 : p ^ f = 2 ^ 2 ∨ p ^ f = 2 ^ 3 := by
      rcases h with h | h
      · left; rw [h]; norm_num
      · right; rw [h]; norm_num
    have hp2dvd : p ∣ 2 := by
      rcases h24 with h4 | h8
      · exact hp.dvd_of_dvd_pow (h4 ▸ dvd_pow_self p (by omega))
      · exact hp.dvd_of_dvd_pow (h8 ▸ dvd_pow_self p (by omega))
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2dvd
  subst hp2
  have hf23 : f = 2 ∨ f = 3 := by
    have hf3 : f ≤ 3 := by
      by_contra hle
      have h4 : 4 ≤ f := by omega
      have h16 : 16 ≤ 2 ^ f := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h4
      rcases h with h | h <;> rw [h] at h16 <;> norm_num at h16
    interval_cases f
    · exfalso; revert h; norm_num
    · left; rfl
    · right; rfl
  exact ⟨rfl, hf23⟩

private theorem k328dg2_exists_generator {S : Type} [Group S] [Finite S] {Z : Subgroup S}
    (hZ : Nat.card Z = 3) :
    ∃ z : S, z ∈ Z ∧ orderOf z = 3 ∧ Subgroup.zpowers z = Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZ])
  refine ⟨(z : S), z.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hzord
  · apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem z.2)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hzord, hZ]

theorem k328det_famG2 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3 →
      ∀ p f : ℕ, LieModel S .G2 0 p f → K328DetPosIn S →
        LieModel S .G2 0 2 2 ∨ LieModel S .G2 0 2 3 := by
  intro S _ _ hS hrank p f hLie hpos
  by_cases hp3 : p = 3
  · subst hp3
    exact (k328det_excCharThree S f (Or.inl hLie) hrank hpos).elim
  · have hadm : CFSG.Open.StatedLieAdmissible .G2 0 p f := hLie.admissible
    have hpprime : p.Prime := hadm.1
    have hf1 : 1 ≤ f := hadm.2.1
    have h3le : 3 ≤ p ^ f := hadm.2.2.2
    obtain ⟨Z, X, hpZ, -⟩ := hpos
    obtain ⟨z, hzZ, hzord, hZzp⟩ := k328dg2_exists_generator hpZ.1
    have hCeq : Subgroup.centralizer (Z : Set S) = Subgroup.centralizer ({z} : Set S) := by
      rw [← hZzp, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hXC : X ≤ Subgroup.centralizer ({z} : Set S) := by
      rw [← hCeq]; exact hpZ.2.2.1
    have hsub : (X.subgroupOf (Subgroup.centralizer ({z} : Set S))).IsSubnormal := by
      rw [← hCeq]; exact hpZ.2.2.2.1
    have hcardX : Nat.card X = k328det_sl3eps (p ^ f) :=
      k328det_excThreeCompG2 S p f hLie hp3 z hzord X (hpZ.2.1 hzZ) hXC hsub
        hpZ.2.2.2.2.1
    have hq : p ^ f = 4 ∨ p ^ f = 8 := by
      rcases k328det_posCard S Z X hpZ with h1 | h1
      · exact k328dg2_sl3eps_eq (p ^ f) h3le (Or.inl (by rw [← hcardX, h1]))
      · exact k328dg2_sl3eps_eq (p ^ f) h3le (Or.inr (by rw [← hcardX, h1]))
    obtain ⟨hp2, hf23⟩ := k328dg2_pow_eq p f hpprime hf1 hq
    rcases hf23 with hf2 | hf3
    · rw [hp2, hf2] at hLie; exact Or.inl hLie
    · rw [hp2, hf3] at hLie; exact Or.inr hLie

private theorem k328dd4_sl3eps_ge_cube {q : ℕ} (hq : 2 ≤ q) :
    q ^ 3 ≤ k328det_sl3eps q := by
  rw [k328det_sl3eps]
  have hq3 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hq2 : 4 ≤ q ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h1 : 1 ≤ q ^ 3 - 1 := by omega
  have h2 : 1 ≤ q ^ 2 - 1 := by omega
  split_ifs with h
  · calc q ^ 3 = q ^ 3 * 1 * 1 := by ring
      _ ≤ q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left (q ^ 3) h1) h2
  · calc q ^ 3 = q ^ 3 * 1 * 1 := by ring
      _ ≤ q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left (q ^ 3) (by omega : 1 ≤ q ^ 3 + 1)) h2

private theorem k328dd4_sl3eps_two_pow {f : ℕ} (hf : 1 ≤ f)
    (h : k328det_sl3eps (2 ^ f) = 60480 ∨ k328det_sl3eps (2 ^ f) = 16547328) :
    f = 2 ∨ f = 3 := by
  have hcube : (2 ^ f) ^ 3 ≤ k328det_sl3eps (2 ^ f) :=
    k328dd4_sl3eps_ge_cube (q := 2 ^ f) (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
  rw [← pow_mul] at hcube
  have hle : 2 ^ (3 * f) ≤ 16547328 := by
    rw [Nat.mul_comm 3 f]
    rcases h with h | h
    · rw [h] at hcube; exact hcube.trans (by norm_num)
    · rw [h] at hcube; exact hcube
  have hf7 : f ≤ 7 := by
    have hlt : 2 ^ (3 * f) < 2 ^ 24 := by
      calc 2 ^ (3 * f) ≤ 16547328 := hle
        _ < 2 ^ 24 := by norm_num
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  interval_cases f <;> norm_num [k328det_sl3eps] at *

theorem k328det_famTriD4 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3 →
      ∀ p f : ℕ, LieModel S .trialityD4 0 p f → K328DetPosIn S →
        LieModel S .trialityD4 0 2 2 ∨ LieModel S .trialityD4 0 2 3 := by
  intro S _ _ hS hrank p f hLie hPos
  have hadm : CFSG.Open.StatedLieAdmissible .trialityD4 0 p f := hLie.admissible
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  rcases hp.eq_two_or_odd with hp2 | hpodd
  · subst hp2
    rcases hPos with ⟨Z, X, hpPos, -⟩
    have hZcard : Nat.card Z = 3 := hpPos.1
    have hZX : Z ≤ X := hpPos.2.1
    have hXC : X ≤ Subgroup.centralizer (Z : Set S) := hpPos.2.2.1
    have hsub : (X.subgroupOf (Subgroup.centralizer (Z : Set S))).IsSubnormal := hpPos.2.2.2.1
    have hqs : CFSG.Open.IsQuasisimple ↥X := hpPos.2.2.2.2.1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZcard])
    have hzS : orderOf (z : S) = 3 := by rw [Subgroup.orderOf_coe]; exact hz
    have hzZ : (z : S) ∈ Z := z.2
    have hzX : (z : S) ∈ X := hZX hzZ
    have hle : Subgroup.zpowers (z : S) ≤ Z := Subgroup.zpowers_le_of_mem hzZ
    have hcard : Nat.card Z ≤ Nat.card (Subgroup.zpowers (z : S)) := by
      rw [Nat.card_zpowers, hzS, hZcard]
    have hZeq : Z = Subgroup.zpowers (z : S) := (Subgroup.eq_of_le_of_card_ge hle hcard).symm
    have hcent : Subgroup.centralizer (Z : Set S) = Subgroup.centralizer ({(z : S)} : Set S) := by
      refine le_antisymm (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzZ)) ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : w ∈ Subgroup.zpowers (z : S) := hZeq ▸ hw
      rw [Subgroup.mem_zpowers_iff] at hw'
      obtain ⟨n, rfl⟩ := hw'
      have hc : Commute y (z : S) := Subgroup.mem_centralizer_singleton_iff.mp hy
      exact (Commute.zpow_right hc n).eq.symm
    rw [hcent] at hXC hsub
    have hcardX : Nat.card X = k328det_sl3eps (2 ^ f) :=
      k328det_triD4TwoComp S f hLie (z : S) hzS X hzX hXC hsub hqs
    have harith : f = 2 ∨ f = 3 := by
      refine k328dd4_sl3eps_two_pow hf ?_
      rcases k328det_posCard S Z X hpPos with h | h
      · exact Or.inl (hcardX.symm.trans h)
      · exact Or.inr (hcardX.symm.trans h)
    rcases harith with rfl | rfl
    · exact Or.inl hLie
    · exact Or.inr hLie
  · have hp2' : p ≠ 2 := by
      intro h; rw [h] at hpodd; norm_num at hpodd
    by_cases hp3 : p = 3
    · subst hp3
      exact (k328det_excCharThree S f (Or.inr hLie) hrank hPos).elim
    · exact (k328det_triD4OddExcluded S hS p f hp2' hp3 hLie hPos).elim

private theorem k328df4_su3_ge_six (q : ℕ) (hq : 2 ≤ q) :
    q ^ 6 ≤ k328det_su3 q := by
  rw [k328det_su3]
  have h1 : q ^ 3 ≤ q ^ 3 + 1 := Nat.le_succ _
  have h2 : 1 ≤ q ^ 2 - 1 := by
    have h4 : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    norm_num at h4
    omega
  calc q ^ 6 = q ^ 3 * q ^ 3 * 1 := by ring
    _ ≤ q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left (q ^ 3) h1) h2

private theorem k328df4_pos_generator {S : Type} [Group S] [Finite S]
    {Z X : Subgroup S} (hp : Pos S Z X) :
    ∃ z : S, orderOf z = 3 ∧ z ∈ X ∧
      X ≤ Subgroup.centralizer ({z} : Set S) ∧
      (X.subgroupOf (Subgroup.centralizer ({z} : Set S))).IsSubnormal := by
  obtain ⟨hZcard, hZX, hXC, hXsub, -, -, -⟩ := hp
  have h3prime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZcard])
  set zS : S := (z : S) with hzSdef
  have hzS : orderOf zS = 3 := by rw [hzSdef, Subgroup.orderOf_coe, hz]
  have hzZ : zS ∈ Z := by rw [hzSdef]; exact z.2
  have hZgen : Z = Subgroup.zpowers zS := by
    have htop : Subgroup.zpowers (z : ↥Z) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hz, hZcard]
    have hmap := MonoidHom.map_zpowers Z.subtype (z : ↥Z)
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    exact hmap
  have hCeq : Subgroup.centralizer (Z : Set S) =
      Subgroup.centralizer ({zS} : Set S) := by
    rw [hZgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  refine ⟨zS, hzS, hZX hzZ, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hXC hx) zS hzZ).symm
  · rwa [← hCeq]

theorem k328det_famTwF4 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ f : ℕ,
      LieModel S .twistedF4 0 2 f → K328DetPosIn S → LieModel S .twistedF4 0 2 3 := by
  intro S _ _ _ f hLM hpos
  obtain ⟨Z, X, hp, -⟩ := hpos
  obtain ⟨z, hz, hzX, hXC, hXsub⟩ := k328df4_pos_generator hp
  have hXq : CFSG.Open.IsQuasisimple ↥X := hp.2.2.2.2.1
  have hcardX : Nat.card X = k328det_su3 (2 ^ f) :=
    k328det_f4ThreeComp S f hLM z hz X hzX hXC hXsub hXq
  have hN : Nat.card X ≤ 16547328 := by
    rcases k328det_posCard S Z X hp with h | h
    · omega
    · omega
  have hadm : CFSG.Open.StatedLieAdmissible .twistedF4 0 2 f := hLM.admissible
  have hf3 : 3 ≤ f := by
    obtain ⟨-, -, -, h3⟩ := hadm.2.2
    exact h3
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := pow_le_pow_right' (by norm_num : 1 ≤ 2) (by omega : 1 ≤ f)
  have hsu3 : (2 ^ f) ^ 6 ≤ k328det_su3 (2 ^ f) := k328df4_su3_ge_six (2 ^ f) hq2
  have hpow : (2 ^ f) ^ 6 ≤ 16547328 := by
    calc (2 ^ f) ^ 6 ≤ k328det_su3 (2 ^ f) := hsu3
      _ = Nat.card X := hcardX.symm
      _ ≤ 16547328 := hN
  have hlt : 2 ^ (f * 6) < 2 ^ 24 := by
    calc 2 ^ (f * 6) = (2 ^ f) ^ 6 := pow_mul 2 f 6
      _ ≤ 16547328 := hpow
      _ < 2 ^ 24 := by norm_num
  have hf_le : f ≤ 3 := by
    by_contra h
    have h4 : 24 ≤ f * 6 := by omega
    have hge : 2 ^ 24 ≤ 2 ^ (f * 6) :=
      pow_le_pow_right' (by norm_num : 1 ≤ 2) h4
    omega
  have hf : f = 3 := le_antisymm hf_le hf3
  simpa [hf] using hLM

theorem k328det_titsCard :
    ∀ (S : Type) [Group S] [Finite S], LieModel S .Tits 0 2 1 → Nat.card S = 17971200 := by
  intro S _ _ h
  have hT : CFSG.Open.StatedLieTag.Tits ∈ CFSG.Blueprint.reeTitsTags := by decide
  obtain ⟨-, hR⟩ := h.reeTitsModel hT
  rw [CFSG.SeitzReduction.F4Pilot.EvenExc.card_of_reeTitsModel_tits hR]
  norm_num [CFSG.Open.ordTits]

theorem k328det_tits_excluded
    {S : Type} [Group S] [Finite S] (h : LieModel S .Tits 0 2 1) :
    ¬ K328DetPosIn S :=
  k328det_not_posIn_of_card (by rw [k328det_titsCard S h]; norm_num)
    (by rw [k328det_titsCard S h]; norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
