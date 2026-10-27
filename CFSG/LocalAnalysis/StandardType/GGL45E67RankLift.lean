module

public import CFSG.LocalAnalysis.StandardType.GGL45TorusHDefs
public import CFSG.LocalAnalysis.StandardType.GGL45E67Config
public import CFSG.LocalAnalysis.StandardType.GGL45NtGroupLemmas
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdLayerP
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.CentralLift
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

namespace CentralLift

open CFSG CFSG.Assembly
open scoped commutatorElement

theorem commutator_pow_three_eq_one_of_central {G : Type} [Group G] {a b : G}
    (ha : a ^ 2 ∈ Subgroup.center G) (hb : b ^ 2 ∈ Subgroup.center G)
    (hab : (a * b) ^ 3 ∈ Subgroup.center G) : ⁅a, b⁆ ^ 3 = 1 := by
  let z1 : G := a ^ 2
  let z2 : G := b ^ 2
  let z3 : G := (a * b) ^ 3
  have hz1 : z1 ∈ Subgroup.center G := ha
  have hz2 : z2 ∈ Subgroup.center G := hb
  have hz3 : z3 ∈ Subgroup.center G := hab
  have hz1inv : z1⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hz1
  have hz2inv : z2⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hz2
  have hainv : a⁻¹ = z1⁻¹ * a := by
    show a⁻¹ = (a ^ 2)⁻¹ * a
    group
  have hbinv : b⁻¹ = z2⁻¹ * b := by
    show b⁻¹ = (b ^ 2)⁻¹ * b
    group
  have hc : ⁅a, b⁆ = (a * b) ^ 2 * z1⁻¹ * z2⁻¹ := by
    rw [commutatorElement_def, hainv, hbinv]
    rw [show z1⁻¹ * a = a * z1⁻¹ from (Subgroup.mem_center_iff.mp hz1inv a).symm,
      show z2⁻¹ * b = b * z2⁻¹ from (Subgroup.mem_center_iff.mp hz2inv b).symm]
    rw [show a * b * (a * z1⁻¹) * (b * z2⁻¹) = a * b * a * (z1⁻¹ * b) * z2⁻¹ by group]
    rw [show z1⁻¹ * b = b * z1⁻¹ from (Subgroup.mem_center_iff.mp hz1inv b).symm]
    rw [show a * b * a * (b * z1⁻¹) * z2⁻¹ = (a * b) ^ 2 * z1⁻¹ * z2⁻¹ by
      rw [pow_two]
      group]
  have hleft : a * (a * b) * a⁻¹ = b * a := by
    rw [show a * (a * b) * a⁻¹ = a ^ 2 * b * a⁻¹ by
      rw [pow_two]
      group]
    rw [show a ^ 2 * b = b * a ^ 2 from (Subgroup.mem_center_iff.mp ha b).symm]
    rw [show b * a ^ 2 * a⁻¹ = b * (a ^ 2 * a⁻¹) by group]
    rw [show a ^ 2 * a⁻¹ = a by
      rw [pow_two]
      group]
  have hright : (a * b)⁻¹ * z1 * z2 = b * a := by
    have hb' : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
    rw [hb', hbinv, hainv]
    rw [show z2⁻¹ * b = b * z2⁻¹ from (Subgroup.mem_center_iff.mp hz2inv b).symm,
      show z1⁻¹ * a = a * z1⁻¹ from (Subgroup.mem_center_iff.mp hz1inv a).symm]
    rw [show b * z2⁻¹ * (a * z1⁻¹) = b * (z2⁻¹ * a) * z1⁻¹ by group]
    rw [show z2⁻¹ * a = a * z2⁻¹ from (Subgroup.mem_center_iff.mp hz2inv a).symm]
    rw [show b * (a * z2⁻¹) * z1⁻¹ = (b * a) * (z2⁻¹ * z1⁻¹) by group]
    rw [show (b * a) * (z2⁻¹ * z1⁻¹) * z1 * z2 = b * a by group]
  have hconj : a * (a * b) * a⁻¹ = (a * b)⁻¹ * z1 * z2 := hleft.trans hright.symm
  have hconjpow : a * (a * b) ^ 3 * a⁻¹ = z3 := by
    rw [show a * (a * b) ^ 3 * a⁻¹ = a * z3 * a⁻¹ from rfl]
    rw [(Subgroup.mem_center_iff.mp hz3 a)]
    group
  have hz3eq : z3 = z3⁻¹ * (z1 * z2) ^ 3 := by
    conv_lhs => rw [← hconjpow]
    rw [show a * (a * b) ^ 3 * a⁻¹ = (a * (a * b) * a⁻¹) ^ 3 by
      rw [show a * (a * b) ^ 3 * a⁻¹ = (MulAut.conj a) ((a * b) ^ 3) by
        rw [MulAut.conj_apply]]
      rw [map_pow, MulAut.conj_apply]]
    rw [hconj]
    rw [show (a * b)⁻¹ * z1 * z2 = (a * b)⁻¹ * (z1 * z2) by group]
    have hc1 : Commute (a * b)⁻¹ z1 := Subgroup.mem_center_iff.mp hz1 ((a * b)⁻¹)
    have hc2 : Commute (a * b)⁻¹ z2 := Subgroup.mem_center_iff.mp hz2 ((a * b)⁻¹)
    rw [(hc1.mul_right hc2).mul_pow]
    rw [show ((a * b)⁻¹) ^ 3 = z3⁻¹ by
      rw [show z3 = (a * b) ^ 3 from rfl]
      exact inv_pow (a * b) 3]
  have hz3sq : z3 ^ 2 = (z1 * z2) ^ 3 := by
    have h := congrArg (fun x => z3 * x) hz3eq
    simpa only [pow_two, mul_assoc, mul_inv_cancel_left, one_mul] using h
  have hz12 : Commute z1 z2 := (Subgroup.mem_center_iff.mp hz1 z2).symm
  have hz12inv : Commute z1⁻¹ z2⁻¹ := (Subgroup.mem_center_iff.mp hz1inv z2⁻¹).symm
  have hc3 : ⁅a, b⁆ ^ 3 = z3 ^ 2 * (z1⁻¹ * z2⁻¹) ^ 3 := by
    rw [hc]
    have hq1 : Commute ((a * b) ^ 2) z1⁻¹ := Subgroup.mem_center_iff.mp hz1inv ((a * b) ^ 2)
    have hq2 : Commute ((a * b) ^ 2) z2⁻¹ := Subgroup.mem_center_iff.mp hz2inv ((a * b) ^ 2)
    rw [show (a * b) ^ 2 * z1⁻¹ * z2⁻¹ = ((a * b) ^ 2) * (z1⁻¹ * z2⁻¹) by group]
    rw [(hq1.mul_right hq2).mul_pow]
    rw [show (((a * b) ^ 2)) ^ 3 = z3 ^ 2 by
      rw [show z3 = (a * b) ^ 3 from rfl]
      group]
  rw [hc3, hz3sq, hz12.mul_pow, hz12inv.mul_pow]
  rw [show z1 ^ 3 * z2 ^ 3 = z2 ^ 3 * z1 ^ 3 from (hz12.pow_pow 3 3).eq]
  group


theorem exists_sylow_two_comap {K R : Type} [Group K] [Finite K] [Group R]
    (π : K →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    {Q : Subgroup R} (hQ2 : IsPGroup 2 Q) (hQne : Q ≠ ⊥) :
    ∃ Q' : Subgroup K, IsPGroup 2 Q' ∧ Q' ≠ ⊥ ∧ Q' ≤ Q.comap π ∧
      ∀ T : Subgroup K, T ≤ Q.comap π → IsPGroup 2 T → T ≤ Q' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup K := Q.comap π
  have hPfin : Finite ↥P :=
    Finite.of_injective (fun x : ↥P => (x : K)) (fun x y h => Subtype.ext h)
  have hQfin : Finite ↥Q :=
    Finite.of_surjective (π.subgroupComap Q)
      (MonoidHom.subgroupComap_surjective π Q hπ)
  have : Group.IsNilpotent ↥Q := IsPGroup.isNilpotent hQ2
  have hPnil : Group.IsNilpotent ↥P :=
    Subgroup.isNilpotent_of_ker_le_center (π.subgroupComap Q)
      (CFSG.LieType.CentralExt.ker_subgroupComap_le_center hker Q)
  let S : Sylow 2 ↥P := Classical.choice Sylow.nonempty
  have huniq : Unique (Sylow 2 ↥P) := Sylow.unique_of_normal S inferInstance
  refine ⟨(S : Subgroup ↥P).map P.subtype, S.isPGroup'.map P.subtype, ?_, ?_, ?_⟩
  ·
    set T : Sylow 2 ↥Q := S.mapSurjective (MonoidHom.subgroupComap_surjective π Q hπ) with hT
    have htop : (T : Subgroup ↥Q) = ⊤ := by
      have hmax := T.is_maximal' (Q := ⊤) (hQ2.to_subgroup ⊤) le_top
      exact hmax.symm
    have hcomp : π.comp P.subtype = Q.subtype.comp (π.subgroupComap Q) := by
      ext x
      rfl
    have hmap : ((S : Subgroup ↥P).map P.subtype).map π = Q := by
      calc ((S : Subgroup ↥P).map P.subtype).map π
          = (S : Subgroup ↥P).map (π.comp P.subtype) := by rw [Subgroup.map_map]
        _ = (S : Subgroup ↥P).map (Q.subtype.comp (π.subgroupComap Q)) := by rw [hcomp]
        _ = ((S : Subgroup ↥P).map (π.subgroupComap Q)).map Q.subtype := by rw [Subgroup.map_map]
        _ = ((T : Subgroup ↥Q)).map Q.subtype := by
              rw [hT, Sylow.coe_mapSurjective]
        _ = (⊤ : Subgroup ↥Q).map Q.subtype := by rw [htop]
        _ = Q := by rw [Subgroup.map_top, Subgroup.range_subtype]
    intro hbot
    apply hQne
    rw [← hmap, hbot, Subgroup.map_bot]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  ·
    intro T hTP hT2
    have hTsub : IsPGroup 2 (T.subgroupOf P) :=
      hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTP).symm
    obtain ⟨T', hT'⟩ := hTsub.exists_le_sylow
    have hT'eq : T' = S := (huniq.uniq T').trans (huniq.uniq S).symm
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hTP hx⟩, ?_, rfl⟩
    have : (⟨x, hTP hx⟩ : ↥P) ∈ T.subgroupOf P := hx
    rw [hT'eq] at hT'
    exact hT' this

private lemma lift_commutator_pi {K R : Type} [Group K] [Group R] (π : K →* R) {r : ℕ}
    {a b : Fin r → R} (ha2 : ∀ i, a i ^ 2 = 1) (hb2 : ∀ i, b i ^ 2 = 1)
    {ahat bhat : Fin r → K} (hahat : ∀ i, π (ahat i) = a i)
    (hbhat : ∀ i, π (bhat i) = b i) :
    ∀ i, π (⁅ahat i, bhat i⁆) = (a i * b i) ^ 2 := by
  intro i
  have hmap : π (⁅ahat i, bhat i⁆) = ⁅a i, b i⁆ := by
    simp only [commutatorElement_def, map_mul, map_inv, hahat i, hbhat i]
  have hainv : (a i)⁻¹ = a i := by
    have h := ha2 i
    rw [pow_two] at h
    exact inv_eq_of_mul_eq_one_left h
  have hbinv : (b i)⁻¹ = b i := by
    have h := hb2 i
    rw [pow_two] at h
    exact inv_eq_of_mul_eq_one_left h
  rw [hmap, commutatorElement_def, hainv, hbinv, pow_two, mul_assoc]

private lemma lift_commutator_cube {K R : Type} [Group K] [Group R] (π : K →* R)
    (hker : π.ker = Subgroup.center K) {r : ℕ} {a b : Fin r → R}
    (ha2 : ∀ i, a i ^ 2 = 1) (hb2 : ∀ i, b i ^ 2 = 1)
    (hab3 : ∀ i, orderOf (a i * b i) = 3)
    {ahat bhat : Fin r → K} (hahat : ∀ i, π (ahat i) = a i)
    (hbhat : ∀ i, π (bhat i) = b i) :
    ∀ i, ⁅ahat i, bhat i⁆ ^ 3 = 1 := by
  intro i
  refine commutator_pow_three_eq_one_of_central ?_ ?_ ?_
  · rw [← hker, MonoidHom.mem_ker]
    simp only [map_pow, hahat i, ha2 i]
  · rw [← hker, MonoidHom.mem_ker]
    simp only [map_pow, hbhat i, hb2 i]
  · rw [← hker, MonoidHom.mem_ker]
    simp only [map_pow, map_mul, hahat i, hbhat i]
    rw [← orderOf_dvd_iff_pow_eq_one, hab3 i]

private lemma lift_commutator_commute {K R : Type} [Group K] [Group R] (π : K →* R)
    (hker : π.ker = Subgroup.center K) {r : ℕ} {a b : Fin r → R}
    (hcomm : ∀ i j, j < i → Commute (a i * b i) (a j) ∧ Commute (a i * b i) (b j))
    {ahat bhat : Fin r → K} {c : Fin r → K} (hahat : ∀ i, π (ahat i) = a i)
    (hbhat : ∀ i, π (bhat i) = b i) (hc_def : ∀ i, c i = ⁅ahat i, bhat i⁆)
    (hc_pi : ∀ i, π (c i) = (a i * b i) ^ 2) :
    ∀ i j, j < i → Commute (c i) (c j) := by
  intro i j hji
  have ha0 : c i * ahat j * (c i)⁻¹ * (ahat j)⁻¹ ∈ Subgroup.center K := by
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hc_pi i, hahat j]
    have hcij : Commute ((a i * b i) ^ 2) (a j) := (hcomm i j hji).1.pow_left 2
    rw [hcij.eq]
    group
  have hb0 : c i * bhat j * (c i)⁻¹ * (bhat j)⁻¹ ∈ Subgroup.center K := by
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hc_pi i, hbhat j]
    have hcij : Commute ((a i * b i) ^ 2) (b j) := (hcomm i j hji).2.pow_left 2
    rw [hcij.eq]
    group
  have ha : ⁅ahat j, c i⁆ ∈ Subgroup.center K := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center K).inv_mem ha0
  have hb : ⁅bhat j, c i⁆ ∈ Subgroup.center K := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center K).inv_mem hb0
  have hcommc :=
    CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad.commutator_commutator_eq_one_of_commutators_mem_center
      ha hb
  rw [commutatorElement_eq_one_iff_commute] at hcommc
  have h : Commute (c i) ⁅ahat j, bhat j⁆ := hcommc.symm
  simpa only [hc_def j] using h

private lemma lift_commutator_fixed {K R : Type} [Group K] [Group R] (π : K →* R)
    (hker : π.ker = Subgroup.center K) {ψ : MulAut K} {f : MulAut R} {r : ℕ}
    (hind : ∀ k : K, f (π k) = π (ψ k)) {a b : Fin r → R}
    (hfa : ∀ i, f (a i) = a i) (hfb : ∀ i, f (b i) = b i)
    {ahat bhat : Fin r → K} (hahat : ∀ i, π (ahat i) = a i)
    (hbhat : ∀ i, π (bhat i) = b i) :
    ∀ i, ψ (⁅ahat i, bhat i⁆) = ⁅ahat i, bhat i⁆ := by
  intro i
  have hpsi_ahat : π (ψ (ahat i)) = a i := by
    rw [← hind, hahat i, hfa i]
  have hpsi_bhat : π (ψ (bhat i)) = b i := by
    rw [← hind, hbhat i, hfb i]
  have hz : (ahat i)⁻¹ * ψ (ahat i) ∈ Subgroup.center K := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hahat i, hpsi_ahat, inv_mul_cancel]
  have hw : (bhat i)⁻¹ * ψ (bhat i) ∈ Subgroup.center K := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hbhat i, hpsi_bhat, inv_mul_cancel]
  have hmap : ψ (⁅ahat i, bhat i⁆) = ⁅ψ (ahat i), ψ (bhat i)⁆ := by
    simp only [commutatorElement_def, map_mul, map_inv]
  have h2 : ψ (ahat i) = ahat i * ((ahat i)⁻¹ * ψ (ahat i)) := by group
  have h3 : ψ (bhat i) = bhat i * ((bhat i)⁻¹ * ψ (bhat i)) := by group
  rw [hmap, h2, h3, CFSG.SectionRank.commutatorElement_mul_mem_center (ahat i) (bhat i) hz hw]

private lemma closure_lift_psi_fixed {K : Type} [Group K] {ψ : MulAut K} {r : ℕ}
    {c : Fin r → K} (hcψ : ∀ i, ψ (c i) = c i) :
    ∀ x ∈ Subgroup.closure (Set.range c), ψ x = x := by
  intro x hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    exact hcψ i
  · rw [map_one]
  · intro x y _ _ ihx ihy
    rw [map_mul, ihx, ihy]
  · intro x _ ihx
    rw [map_inv, ihx]

private lemma commute_all_of_lt {K : Type} [Group K] {r : ℕ} {c : Fin r → K}
    (hc_comm : ∀ i j, j < i → Commute (c i) (c j)) :
    ∀ i j, Commute (c i) (c j) := by
  intro i j
  rcases lt_trichotomy j i with h | h | h
  · exact hc_comm i j h
  · subst h
    exact Commute.refl _
  · exact (hc_comm j i h).symm

private lemma closure_lift_isElemAbelian {K : Type} [Group K] {r : ℕ} {c : Fin r → K}
    (hc3 : ∀ i, c i ^ 3 = 1) (hc_comm : ∀ i j, j < i → Commute (c i) (c j)) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.closure (Set.range c)) := by
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact (commute_all_of_lt hc_comm i j).eq
  · rintro x ⟨i, rfl⟩
    exact hc3 i

private lemma closure_lift_card_le {K : Type} [Group K] {r : ℕ} {c : Fin r → K}
    (hc3 : ∀ i, c i ^ 3 = 1) (hc_comm : ∀ i j, Commute (c i) (c j)) :
    Nat.card (Subgroup.closure (Set.range c)) ≤ 3 ^ r :=
  CFSG.LocalAnalysis.GLTheoremA.card_closure_le_pow_of_commuting Nat.prime_three hc3 hc_comm

private lemma lift_image_closure {K R : Type} [Group K] [Group R] (π : K →* R) {r : ℕ}
    {a b : Fin r → R} {c : Fin r → K}
    (hc_pi : ∀ i, π (c i) = (a i * b i) ^ 2) :
    (Subgroup.closure (Set.range c)).map π =
      Subgroup.closure (Set.range fun i => (a i * b i) ^ 2) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (hc_pi i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨c i, ⟨i, rfl⟩, hc_pi i⟩

private lemma lift_image_card {K R : Type} [Group K] [Group R] (π : K →* R) {r : ℕ}
    {a b : Fin r → R} {c : Fin r → K}
    (hc_pi : ∀ i, π (c i) = (a i * b i) ^ 2)
    (hab3 : ∀ i, orderOf (a i * b i) = 3)
    (hgen : Nat.card (Subgroup.closure (Set.range fun i => a i * b i)) = 3 ^ r) :
    Nat.card ((Subgroup.closure (Set.range c)).map π) = 3 ^ r := by
  have hsq : ∀ i, (a i * b i) ^ 2 = (a i * b i)⁻¹ := by
    intro i
    have h3 : (a i * b i) ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hab3 i]
    have h2 : (a i * b i) ^ 3 * (a i * b i)⁻¹ = (a i * b i) ^ 2 := by
      rw [pow_succ]
      group
    calc (a i * b i) ^ 2 = (a i * b i) ^ 3 * (a i * b i)⁻¹ := h2.symm
      _ = (a i * b i)⁻¹ := by rw [h3, one_mul]
  have hclosure_inv : Subgroup.closure (Set.range fun i => (a i * b i) ^ 2) =
      Subgroup.closure (Set.range fun i => a i * b i) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x ⟨i, rfl⟩
      change (a i * b i) ^ 2 ∈ Subgroup.closure (Set.range fun i => a i * b i)
      rw [hsq i]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, rfl⟩)
    · rw [Subgroup.closure_le]
      rintro x ⟨i, rfl⟩
      change a i * b i ∈ Subgroup.closure (Set.range fun i => (a i * b i) ^ 2)
      have hx3 : (a i * b i) ^ 3 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hab3 i]
      have hx : a i * b i = ((a i * b i) ^ 2) ^ 2 := by
        rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_succ, hx3, one_mul]
      rw [hx]
      exact Subgroup.pow_mem _ (Subgroup.subset_closure
        (show (a i * b i) ^ 2 ∈ Set.range (fun i => (a i * b i) ^ 2) from ⟨i, rfl⟩)) 2
  rw [lift_image_closure π hc_pi, hclosure_inv, hgen]

private lemma lift_card_eq {K R : Type} [Group K] [Finite K] [Group R] (π : K →* R) {r : ℕ}
    {c : Fin r → K}
    (hcard_le : Nat.card (Subgroup.closure (Set.range c)) ≤ 3 ^ r)
    (hpi_card : Nat.card ((Subgroup.closure (Set.range c)).map π) = 3 ^ r) :
    Nat.card (Subgroup.closure (Set.range c)) = 3 ^ r := by
  have hcard_lower : 3 ^ r ≤ Nat.card (Subgroup.closure (Set.range c)) := by
    rw [← hpi_card]
    exact Nat.le_of_dvd (Nat.card_pos (α := ↥(Subgroup.closure (Set.range c))))
      (Subgroup.card_map_dvd _ π)
  exact le_antisymm hcard_le hcard_lower

private lemma lift_ker_bot {K R : Type} [Group K] [Finite K] [Group R] (π : K →* R) {r : ℕ}
    {c : Fin r → K}
    (hcard : Nat.card (Subgroup.closure (Set.range c)) = 3 ^ r)
    (hpi_card : Nat.card ((Subgroup.closure (Set.range c)).map π) = 3 ^ r) :
    π.ker ⊓ Subgroup.closure (Set.range c) = ⊥ ∧
      ∀ x ∈ Subgroup.closure (Set.range c), π x = 1 → x = 1 := by
  have hkerbot : π.ker ⊓ Subgroup.closure (Set.range c) = ⊥ := by
    have h := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf (G := K) π
      (Subgroup.closure (Set.range c))
    rw [hcard, hpi_card] at h
    have hk : Nat.card ↥(π.ker ⊓ Subgroup.closure (Set.range c)) = 1 := by
      apply Nat.mul_left_cancel (n := 3 ^ r) (by positivity)
      rw [mul_one]
      exact h.symm
    exact Subgroup.eq_bot_of_card_eq _ hk
  refine ⟨hkerbot, ?_⟩
  intro x hx hx1
  have hxmem : x ∈ π.ker ⊓ Subgroup.closure (Set.range c) := ⟨hx1, hx⟩
  rw [hkerbot] at hxmem
  exact hxmem

private lemma sylow_two_preimage_psi {K R : Type} [Group K] [Group R]
    (π : K →* R) {Q : Subgroup R} {ψ : MulAut K} {f : MulAut R}
    (hind : ∀ k : K, f (π k) = π (ψ k)) (hQstab : ∀ g ∈ Q, f g ∈ Q)
    {Qhat : Subgroup K} (hQhat2 : IsPGroup 2 Qhat)
    (hQhatP : Qhat ≤ Q.comap π)
    (hQhatmax : ∀ T : Subgroup K, T ≤ Q.comap π → IsPGroup 2 T → T ≤ Qhat) :
    ∀ g ∈ Qhat, ψ g ∈ Qhat := by
  have hψP : ∀ x ∈ Q.comap π, ψ x ∈ Q.comap π := by
    intro x hx
    rw [Subgroup.mem_comap] at hx ⊢
    rw [← hind x] at *
    exact hQstab (π x) hx
  have hle : Qhat.map ψ.toMonoidHom ≤ Qhat := by
    refine hQhatmax _ ?_ (hQhat2.map ψ.toMonoidHom)
    rintro _ ⟨y, hy, rfl⟩
    exact hψP y (hQhatP hy)
  intro g hg
  exact hle (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)

private lemma lift_normalizes_sylow {K R : Type} [Group K] [Finite K] [Group R]
    (π : K →* R) {r : ℕ} {a b : Fin r → R} {c : Fin r → K} {Q : Subgroup R}
    (hQnorm : ∀ i, a i * b i ∈ Subgroup.normalizer (Q : Set R))
    (hc_pi : ∀ i, π (c i) = (a i * b i) ^ 2)
    {Qhat : Subgroup K} (hQhat2 : IsPGroup 2 Qhat)
    (hQhatP : Qhat ≤ Q.comap π)
    (hQhatmax : ∀ T : Subgroup K, T ≤ Q.comap π → IsPGroup 2 T → T ≤ Qhat) :
    (∀ i, c i ∈ Subgroup.normalizer (Q.comap π : Set K)) ∧
      (∀ i, c i ∈ Subgroup.normalizer (Qhat : Set K)) ∧
      Subgroup.closure (Set.range c) ≤ Subgroup.normalizer (Qhat : Set K) := by
  have hcpi_norm : ∀ i, (a i * b i) ^ 2 ∈ Subgroup.normalizer (Q : Set R) := by
    intro i
    exact Subgroup.pow_mem _ (hQnorm i) 2
  have hcP : ∀ i, c i ∈ Subgroup.normalizer (Q.comap π : Set K) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv, hc_pi i]
      exact (Subgroup.mem_normalizer_iff.mp (hcpi_norm i) (π x)).1 hx
    · intro hx
      rw [Subgroup.mem_comap] at hx ⊢
      rw [map_mul, map_mul, map_inv, hc_pi i] at hx
      exact (Subgroup.mem_normalizer_iff.mp (hcpi_norm i) (π x)).2 hx
  have hcQhat : ∀ i, c i ∈ Subgroup.normalizer (Qhat : Set K) := by
    intro i
    have hconj : Qhat.map (MulAut.conj (c i)).toMonoidHom = Qhat := by
      apply Subgroup.eq_of_le_of_card_ge (hQhatmax _ ?_ (hQhat2.map _))
      rw [Subgroup.card_map_of_injective (MulAut.conj (c i)).injective]
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hcP i) y).1 (hQhatP hy)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : (MulAut.conj (c i)) x ∈ Qhat := by
        rw [← hconj]
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using hx'
    · intro hx
      have hx' : (MulAut.conj (c i)) x ∈ Qhat := by
        simpa [MulAut.conj_apply] using hx
      have hcinvP : (c i)⁻¹ ∈ Subgroup.normalizer (Q.comap π : Set K) :=
        (Subgroup.normalizer (Q.comap π : Set K)).inv_mem (hcP i)
      have hconj' : Qhat.map (MulAut.conj ((c i)⁻¹)).toMonoidHom = Qhat := by
        apply Subgroup.eq_of_le_of_card_ge (hQhatmax _ ?_ (hQhat2.map _))
        rw [Subgroup.card_map_of_injective (MulAut.conj ((c i)⁻¹)).injective]
        rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hcinvP y).1 (hQhatP hy)
      have h2 : (MulAut.conj ((c i)⁻¹)) ((MulAut.conj (c i)) x) ∈ Qhat := by
        rw [← hconj']
        exact Subgroup.mem_map.mpr ⟨(MulAut.conj (c i)) x, hx', rfl⟩
      have h3 : (c i)⁻¹ * (c i * x * (c i)⁻¹) * ((c i)⁻¹)⁻¹ = x := by group
      simpa only [MulAut.conj_apply, h3] using h2
  refine ⟨hcP, hcQhat, ?_⟩
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact hcQhat i

private lemma exists_central_three_subgroup {K : Type} [Group K] [Finite K] (ψ : MulAut K)
    (h3dvd : 3 ∣ Nat.card (Subgroup.center K)) :
    ∃ V : Subgroup K, (∀ x : K, x ∈ V ↔ x ∈ Subgroup.center K ∧ x ^ 3 = 1) ∧
      (∀ x ∈ V, ψ x ∈ V) ∧ (∀ x ∈ V, ψ⁻¹ x ∈ V) ∧
      IsPGroup 3 V ∧ 3 ∣ Nat.card V := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Vset : Set K := {z | z ∈ Subgroup.center K ∧ z ^ 3 = 1}
  have hV_mul : ∀ x ∈ Vset, ∀ y ∈ Vset, x * y ∈ Vset := by
    rintro x ⟨hxc, hx3⟩ y ⟨hyc, hy3⟩
    refine ⟨(Subgroup.center K).mul_mem hxc hyc, ?_⟩
    have hcommxy : Commute x y := (Subgroup.mem_center_iff.mp hxc y).symm
    rw [hcommxy.mul_pow, hx3, hy3, one_mul]
  have hV_one : (1 : K) ∈ Vset := ⟨(Subgroup.center K).one_mem, one_pow 3⟩
  have hV_inv : ∀ x ∈ Vset, x⁻¹ ∈ Vset := by
    rintro x ⟨hxc, hx3⟩
    refine ⟨(Subgroup.center K).inv_mem hxc, ?_⟩
    rw [inv_pow, hx3, inv_one]
  let V : Subgroup K :=
    { carrier := Vset
      mul_mem' := fun {a b} ha hb => hV_mul a ha b hb
      one_mem' := hV_one
      inv_mem' := fun {a} ha => hV_inv a ha }
  have hVmem : ∀ x : K, x ∈ V ↔ x ∈ Subgroup.center K ∧ x ^ 3 = 1 := by
    intro x
    change x ∈ Vset ↔ x ∈ Subgroup.center K ∧ x ^ 3 = 1
    rfl
  have hVψ : ∀ x ∈ V, ψ x ∈ V := by
    intro x hx
    rw [hVmem]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro y
      have hy : x * ψ⁻¹ y = ψ⁻¹ y * x :=
        (Subgroup.mem_center_iff.mp ((hVmem x).mp hx).1 (ψ⁻¹ y)).symm
      have h := congrArg ψ hy
      simpa using h.symm
    · rw [← map_pow, (hVmem x).mp hx |>.2, map_one]
  have hVψinv : ∀ x ∈ V, ψ⁻¹ x ∈ V := by
    intro x hx
    rw [hVmem]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro y
      have hy : ψ y * x = x * ψ y := Subgroup.mem_center_iff.mp ((hVmem x).mp hx).1 (ψ y)
      simpa using congrArg (fun z => ψ.symm z) hy
    · rw [← map_pow, (hVmem x).mp hx |>.2, map_one]
  have hVp : IsPGroup 3 ↥V := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx3 : (x : K) ^ 3 = 1 := ((hVmem x).mp x.2).2
    have hord : orderOf x ∣ 3 := by
      rw [← Subgroup.orderOf_coe x]
      exact orderOf_dvd_iff_pow_eq_one.mpr hx3
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h3
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3, pow_one]⟩
  have hVne : V ≠ ⊥ := by
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center K)) 3 h3dvd
    have hxV : (x : K) ∈ V := by
      rw [hVmem]
      refine ⟨x.2, ?_⟩
      rw [← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, hxord]
    have hxne : (x : K) ≠ 1 := by
      intro h1
      have h2 : orderOf (x : K) = 1 := by rw [h1, orderOf_one]
      rw [Subgroup.orderOf_coe, hxord] at h2
      exact (by norm_num : (3 : ℕ) ≠ 1) h2
    intro hbot
    have : (x : K) ∈ (⊥ : Subgroup K) := by rw [← hbot]; exact hxV
    exact hxne (by simpa using this)
  have hVcard : 3 ∣ Nat.card ↥V := by
    rcases hVp.card_eq_or_dvd with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_eq V h1) hVne
    · exact h3
  exact ⟨V, hVmem, hVψ, hVψinv, hVp, hVcard⟩

private lemma exists_psi_fixed_central_three {K : Type} [Group K] [Finite K] {ψ : MulAut K}
    (hψ : ψ ^ 3 = 1) {V : Subgroup K}
    (hVmem : ∀ x : K, x ∈ V ↔ x ∈ Subgroup.center K ∧ x ^ 3 = 1)
    (hVψ : ∀ x ∈ V, ψ x ∈ V) (hVψinv : ∀ x ∈ V, ψ⁻¹ x ∈ V)
    (hVcard : 3 ∣ Nat.card V) :
    ∃ z : K, z ∈ Subgroup.center K ∧ orderOf z = 3 ∧ ψ z = z ∧ z ^ 3 = 1 ∧ z ≠ 1 := by
  classical
  let αhom : ↥V →* ↥V :=
    { toFun := fun x => ⟨ψ (x : K), hVψ (x : K) x.2⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun x y => Subtype.ext (by
        change ψ ((x : K) * (y : K)) = ψ (x : K) * ψ (y : K)
        rw [map_mul]) }
  have hαinj : Function.Injective αhom := by
    intro x y h
    exact Subtype.ext (ψ.injective (congrArg Subtype.val h))
  have hαsurj : Function.Surjective αhom := by
    intro y
    refine ⟨⟨ψ⁻¹ (y : K), hVψinv (y : K) y.2⟩, ?_⟩
    exact Subtype.ext (by simp [αhom])
  let α : MulAut ↥V := MulEquiv.ofBijective αhom ⟨hαinj, hαsurj⟩
  have hα3 : α ^ 3 = 1 := by
    ext x
    have hαx : ((α ^ 3) x : K) = ψ (ψ (ψ ((x : ↥V) : K))) := by
      change ((α (α (α x)) : ↥V) : K) = ψ (ψ (ψ ((x : ↥V) : K)))
      rfl
    rw [hαx]
    have := congrArg (fun e : MulAut K => e ((x : ↥V) : K)) hψ
    simpa [pow_succ, pow_two, MulAut.mul_apply] using this
  obtain ⟨zv, hzord, hzfix⟩ :=
    CFSG.HardMathSupport.C14Group.exists_fixed_of_order_p Nat.prime_three α hα3 hVcard
  let z : K := (zv : K)
  have hzord' : orderOf z = 3 := by
    rw [show z = (zv : K) from rfl, Subgroup.orderOf_coe, hzord]
  have hzψ : ψ z = z := congrArg Subtype.val hzfix
  have hzcenter : z ∈ Subgroup.center K := ((hVmem z).mp zv.2).1
  have hz3 : z ^ 3 = 1 := ((hVmem z).mp zv.2).2
  have hzne : z ≠ 1 := by
    intro h1
    have h2 : orderOf z = 1 := by rw [h1, orderOf_one]
    rw [hzord'] at h2
    exact (by norm_num : (3 : ℕ) ≠ 1) h2
  exact ⟨z, hzcenter, hzord', hzψ, hz3, hzne⟩

private lemma enlarged_elementary_abelian {K : Type} [Group K] [Finite K] {ψ : MulAut K} {r : ℕ}
    {R₀ Qhat : Subgroup K} (hR0_card : Nat.card R₀ = 3 ^ r)
    (hR0ea : CFSG.Open.IsElemAbelian 3 R₀) (hR0ψ : ∀ x ∈ R₀, ψ x = x)
    (hR0norm : R₀ ≤ Subgroup.normalizer (Qhat : Set K))
    {z : K} (hzcenter : z ∈ Subgroup.center K) (hzord : orderOf z = 3)
    (hzψ : ψ z = z) (hzR0 : z ∉ R₀) :
    ∃ A : Subgroup K, CFSG.Open.IsElemAbelian 3 A ∧ (∀ x ∈ A, ψ x = x) ∧
      A ≤ Subgroup.normalizer (Qhat : Set K) ∧ Nat.card A = 3 ^ (r + 1) := by
  classical
  let A : Subgroup K := R₀ ⊔ Subgroup.zpowers z
  have hAdisj : Disjoint R₀ (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro x hxR hxZ
    by_contra hxne
    have hxord : orderOf x = 3 := by
      have hdvd : orderOf x ∣ 3 := by
        rw [← hzord]
        exact orderOf_dvd_of_mem_zpowers hxZ
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exfalso
        exact hxne (orderOf_eq_one_iff.mp h1)
      · exact h3
    have hzx : Subgroup.zpowers x = Subgroup.zpowers z := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxZ)
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hzord]
    have hzmem : z ∈ Subgroup.zpowers x := by
      rw [hzx]
      exact Subgroup.mem_zpowers z
    exact hzR0 ((Subgroup.zpowers_le.mpr hxR) hzmem)
  have hZnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (R₀ : Set K) :=
    (Subgroup.zpowers_le.mpr hzcenter).trans (Subgroup.center_le_normalizer (R₀ : Set K))
  have hZea : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers z) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← orderOf_dvd_iff_pow_eq_one, hzord])
  have hAea : CFSG.Open.IsElemAbelian 3 A := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute hR0ea hZea ?_
    intro x _ y hy
    have hycenter : y ∈ Subgroup.center K := (Subgroup.zpowers_le.mpr hzcenter) hy
    exact Subgroup.mem_center_iff.mp hycenter x
  have hAψ : ∀ x ∈ A, ψ x = x := by
    intro x hx
    have hZψ : ∀ y ∈ Subgroup.zpowers z, ψ y = y := by
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [map_zpow, hzψ]
    rw [Subgroup.mem_sup_of_normal_right (t := Subgroup.zpowers z)
      (ht := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzcenter))] at hx
    obtain ⟨y, hyR, w, hwZ, rfl⟩ := hx
    rw [map_mul, hR0ψ y hyR, hZψ w hwZ]
  have hAnorm : A ≤ Subgroup.normalizer (Qhat : Set K) := by
    refine sup_le hR0norm ?_
    exact (Subgroup.zpowers_le.mpr hzcenter).trans (Subgroup.center_le_normalizer (Qhat : Set K))
  have hAcard : Nat.card A = 3 ^ (r + 1) := by
    rw [show A = R₀ ⊔ Subgroup.zpowers z from rfl,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer R₀
        (Subgroup.zpowers z) hZnorm hAdisj,
      hR0_card, Nat.card_zpowers, hzord, pow_succ]
  exact ⟨A, hAea, hAψ, hAnorm, hAcard⟩

private lemma rank_bound_three_dvd {K R : Type} [Group K] [Finite K] [Group R]
    {r n : ℕ} {π : K →* R} {ψ : MulAut K} {R₀ Qhat : Subgroup K}
    (hψ : ψ ^ 3 = 1) (hker : π.ker = Subgroup.center K)
    (hR0_card : Nat.card R₀ = 3 ^ r)
    (hR0ea : CFSG.Open.IsElemAbelian 3 R₀) (hR0ψ : ∀ x ∈ R₀, ψ x = x)
    (hR0_ker : ∀ x ∈ R₀, π x = 1 → x = 1)
    (hQhat2 : IsPGroup 2 Qhat) (hQhatne : Qhat ≠ ⊥)
    (hQhatψ : ∀ g ∈ Qhat, ψ g ∈ Qhat)
    (hR0norm : R₀ ≤ Subgroup.normalizer (Qhat : Set K))
    (hRK : ∀ R₀ Q : Subgroup K, CFSG.Open.IsElemAbelian 3 R₀ → (∀ x ∈ R₀, ψ x = x) →
      IsPGroup 2 Q → Q ≠ ⊥ → (∀ g ∈ Q, ψ g ∈ Q) →
      R₀ ≤ Subgroup.normalizer (Q : Set K) →
      Nat.card R₀ * 3 ≤ n * 3 ^ 2 ∧
        (Nat.Coprime 3 (Nat.card (Subgroup.center K)) → Nat.card R₀ ≤ n))
    (h3dvd : 3 ∣ Nat.card (Subgroup.center K)) :
    3 ^ r ≤ n := by
  obtain ⟨V, hVmem, hVψ, hVψinv, -, hVcard⟩ := exists_central_three_subgroup ψ h3dvd
  obtain ⟨z, hzcenter, hzord, hzψ, -, hzne⟩ :=
    exists_psi_fixed_central_three hψ hVmem hVψ hVψinv hVcard
  have hzR0 : z ∉ R₀ := by
    intro hz
    have hzker : z ∈ π.ker := by rw [hker]; exact hzcenter
    exact hzne (hR0_ker z hz (by simpa using hzker))
  obtain ⟨A, hAea, hAψ, hAnorm, hAcard⟩ :=
    enlarged_elementary_abelian hR0_card hR0ea hR0ψ hR0norm hzcenter hzord hzψ hzR0
  have h1 := (hRK A Qhat hAea hAψ hQhat2 hQhatne hQhatψ hAnorm).1
  rw [hAcard] at h1
  have h2 : 3 ^ r * 9 ≤ n * 9 := by
    calc 3 ^ r * 9 = 3 ^ (r + 1) * 3 := by rw [pow_succ]; ring
      _ ≤ n * 3 ^ 2 := h1
      _ = n * 9 := by norm_num
  exact Nat.le_of_mul_le_mul_right h2 (by norm_num)

private lemma rank_bound_coprime {K : Type} [Group K] {r n : ℕ} {ψ : MulAut K}
    {R₀ Qhat : Subgroup K}
    (hR0ea : CFSG.Open.IsElemAbelian 3 R₀) (hR0ψ : ∀ x ∈ R₀, ψ x = x)
    (hQhat2 : IsPGroup 2 Qhat) (hQhatne : Qhat ≠ ⊥)
    (hQhatψ : ∀ g ∈ Qhat, ψ g ∈ Qhat)
    (hR0norm : R₀ ≤ Subgroup.normalizer (Qhat : Set K))
    (hR0_card : Nat.card R₀ = 3 ^ r)
    (hRK : ∀ R₀ Q : Subgroup K, CFSG.Open.IsElemAbelian 3 R₀ → (∀ x ∈ R₀, ψ x = x) →
      IsPGroup 2 Q → Q ≠ ⊥ → (∀ g ∈ Q, ψ g ∈ Q) →
      R₀ ≤ Subgroup.normalizer (Q : Set K) →
      Nat.card R₀ * 3 ≤ n * 3 ^ 2 ∧
        (Nat.Coprime 3 (Nat.card (Subgroup.center K)) → Nat.card R₀ ≤ n))
    (hcop : Nat.Coprime 3 (Nat.card (Subgroup.center K))) :
    3 ^ r ≤ n := by
  have h := (hRK R₀ Qhat hR0ea hR0ψ hQhat2 hQhatne hQhatψ hR0norm).2 hcop
  rwa [hR0_card] at h

theorem three_pow_le_card_of_config_rank {K R : Type} [Group K] [Finite K] [Group R]
    (π : K →* R) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    {ψ : MulAut K} {f : MulAut R} {r : ℕ} (hψ : ψ ^ 3 = 1)
    (hind : ∀ k : K, f (π k) = π (ψ k)) (hconf : GGL45E67Config f r) {n : ℕ}
    (hRK : ∀ R₀ Q : Subgroup K, CFSG.Open.IsElemAbelian 3 R₀ → (∀ x ∈ R₀, ψ x = x) →
      IsPGroup 2 Q → Q ≠ ⊥ → (∀ g ∈ Q, ψ g ∈ Q) →
      R₀ ≤ Subgroup.normalizer (Q : Set K) →
      Nat.card R₀ * 3 ≤ n * 3 ^ 2 ∧
        (Nat.Coprime 3 (Nat.card (Subgroup.center K)) → Nat.card R₀ ≤ n)) :
    3 ^ r ≤ n := by
  classical
  obtain ⟨a, b, Q, ha2, hb2, hab3, hfa, hfb, hcomm, hgen, hQ2, hQne, hQstab, hQnorm⟩ := hconf
  let ahat : Fin r → K := fun i => Classical.choose (hπ (a i))
  have hahat : ∀ i, π (ahat i) = a i := fun i => Classical.choose_spec (hπ (a i))
  let bhat : Fin r → K := fun i => Classical.choose (hπ (b i))
  have hbhat : ∀ i, π (bhat i) = b i := fun i => Classical.choose_spec (hπ (b i))
  let c : Fin r → K := fun i => ⁅ahat i, bhat i⁆
  have hc_def : ∀ i, c i = ⁅ahat i, bhat i⁆ := fun _ => rfl
  have hc_pi : ∀ i, π (c i) = (a i * b i) ^ 2 := by
    simpa only [c] using lift_commutator_pi π ha2 hb2 hahat hbhat
  have hc3 : ∀ i, c i ^ 3 = 1 := by
    simpa only [c] using lift_commutator_cube π hker ha2 hb2 hab3 hahat hbhat
  have hc_comm : ∀ i j, j < i → Commute (c i) (c j) :=
    lift_commutator_commute π hker hcomm hahat hbhat hc_def hc_pi
  have hcψ : ∀ i, ψ (c i) = c i := by
    simpa only [c] using lift_commutator_fixed π hker hind hfa hfb hahat hbhat
  have hR0ψ : ∀ x ∈ Subgroup.closure (Set.range c), ψ x = x := closure_lift_psi_fixed hcψ
  have hR0ea : CFSG.Open.IsElemAbelian 3 (Subgroup.closure (Set.range c)) :=
    closure_lift_isElemAbelian hc3 hc_comm
  have hc_range : ∀ i j, Commute (c i) (c j) := commute_all_of_lt hc_comm
  have hR0card_le : Nat.card (Subgroup.closure (Set.range c)) ≤ 3 ^ r :=
    closure_lift_card_le hc3 hc_range
  have hpi_card : Nat.card ((Subgroup.closure (Set.range c)).map π) = 3 ^ r :=
    lift_image_card π hc_pi hab3 hgen
  have hR0_card : Nat.card (Subgroup.closure (Set.range c)) = 3 ^ r :=
    lift_card_eq π hR0card_le hpi_card
  obtain ⟨_, hR0_ker⟩ := lift_ker_bot π hR0_card hpi_card
  obtain ⟨Qhat, hQhat2, hQhatne, hQhatP, hQhatmax⟩ :=
    exists_sylow_two_comap π hπ (le_of_eq hker) hQ2 hQne
  have hQhatψ : ∀ g ∈ Qhat, ψ g ∈ Qhat :=
    sylow_two_preimage_psi π hind hQstab hQhat2 hQhatP hQhatmax
  obtain ⟨_, _, hR0norm⟩ :=
    lift_normalizes_sylow π hQnorm hc_pi hQhat2 hQhatP hQhatmax
  by_cases hcop : Nat.Coprime 3 (Nat.card (Subgroup.center K))
  · exact rank_bound_coprime hR0ea hR0ψ hQhat2 hQhatne hQhatψ hR0norm hR0_card hRK hcop
  · have h3dvd : 3 ∣ Nat.card (Subgroup.center K) := by
      by_contra h
      exact hcop ((Nat.prime_three.coprime_iff_not_dvd).mpr h)
    exact rank_bound_three_dvd hψ hker hR0_card hR0ea hR0ψ hR0_ker hQhat2 hQhatne
      hQhatψ hR0norm hRK h3dvd

end CentralLift

open CFSG CFSG.Assembly CentralLift

theorem three_pow_le_card_of_ggL45E67Config (lab : LargeEvenLabel) {R : Type} [Group R]
    {I F : Set (MulAut R)} {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R)
    (ψ : MulAut K) (E : Subgroup (MulAut K)) (hyp : GGL45TorusKGHyp 3 lab I F θ ψ E) {r : ℕ}
    (hconf : ∀ f ∈ F, orderOf f = 3 → GGL45E67Config f r) : 3 ^ r ≤ Nat.card E := by
  obtain ⟨hψp, hfF, -, -, -, -, -, -, hRK, -⟩ := hyp
  obtain ⟨f, hfF', u, -, hf3, hind0⟩ := hfF
  have hconf' : GGL45E67Config (u * f * u⁻¹) r :=
    ggL45E67Config_conj u (hconf f hfF' hf3)
  let π : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    rw [show π = θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  have hψ : ψ ^ 3 = 1 := hψp
  have hind : ∀ k : K, (u * f * u⁻¹) (π k) = π (ψ k) := fun k => hind0 k (ψ k) rfl
  exact three_pow_le_card_of_config_rank π hπ hker hψ hind hconf' hRK



end CFSG.StandardType
