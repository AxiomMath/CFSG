module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R875
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.BarOutInner
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Setup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKAutL34Outer
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKAutL34Cent
import CFSG.Adapters.LieModelSmallOrders
import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62CenterOfNormal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62FusionPointwise
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LieModelL3U3Torus
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.GroupTheory.PRankLeOfSylowLe
import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKAutL34Conj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 IsL3)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped Pointwise

open scoped commutatorElement

@[expose] noncomputable def barFixed {G : Type} [Group G] (L : Subgroup G) (y : G) :
    Subgroup (Bar2 L) :=
  MonoidHom.eqLocus (barConjAut (L := L) y).toMonoidHom (MonoidHom.id (Bar2 L))

private theorem r876fl_normalizerMonoidHom_apply_coe {G : Type} [Group G] (L : Subgroup G)
    (n : Subgroup.normalizer (L : Set G)) (x : ↥L) :
    (((Subgroup.normalizerMonoidHom L) n) x : G) = (n : G) * (x : G) * (n : G)⁻¹ := rfl

private lemma r876fl_mulAut_zpow_apply_of_fixed {M : Type*} [Mul M] (f : MulAut M) (q : M)
    (h : f q = q) (k : ℤ) : (f ^ k) q = q := by
  let H : Subgroup (MulAut M) :=
    { carrier := {g | g q = q}
      one_mem' := by
        change (1 : MulAut M) q = q
        rw [MulAut.one_apply]
      mul_mem' := fun {a b} ha hb => by
        change (a * b) q = q
        rw [MulAut.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        change a⁻¹ q = q
        calc a⁻¹ q = a⁻¹ (a q) := by rw [ha]
          _ = q := MulEquiv.symm_apply_apply a q }
  exact Subgroup.zpow_mem H h k

private lemma r876fl_fixed_of_zpowers_fixed {A : Type*} [Group A] {M : Type*} [Mul M]
    (β : A →* MulAut M) {g : A} (hgen : Subgroup.zpowers g = ⊤) {q : M}
    (h : β g q = q) (a : A) : β a q = q := by
  have ha : a ∈ Subgroup.zpowers g := by rw [hgen]; exact Subgroup.mem_top a
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
  have h1 : β (g ^ k) q = q := by
    rw [map_zpow]
    exact r876fl_mulAut_zpow_apply_of_fixed (β g) q h k
  rw [hk] at h1
  exact h1

theorem r876_fixed_lift {G : Type} [Group G] [Finite G] {L : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (hy3 : orderOf y = 3) :
    barFixed L y = ((Subgroup.centralizer ({y} : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
  let N : Subgroup ↥L := CFSG.pCore 2 ↥L
  let n : ↥(Subgroup.normalizer (L : Set G)) := ⟨y, hy⟩
  let A : Subgroup ↥(Subgroup.normalizer (L : Set G)) := Subgroup.zpowers n
  let g : ↥A := ⟨n, Subgroup.mem_zpowers n⟩
  let α : ↥A →* MulAut ↥L := (Subgroup.normalizerMonoidHom L).comp A.subtype
  have hA3 : IsPGroup 3 ↥A := by
    refine IsPGroup.of_card (n := 1) ?_
    change Nat.card (Subgroup.zpowers n) = 3 ^ 1
    rw [Nat.card_zpowers]
    have hn3 : orderOf n = 3 := by
      rw [← Subgroup.orderOf_coe n]
      exact hy3
    rw [hn3, pow_one]
  have hNα : ∀ a : ↥A, ∀ m ∈ N, α a m ∈ N := by
    intro a m hm
    change ((Subgroup.normalizerMonoidHom L) (A.subtype a)) m ∈ N
    have hmap : N.map ((Subgroup.normalizerMonoidHom L) (A.subtype a)).toMonoidHom = N :=
      Subgroup.characteristic_iff_map_eq.mp (CFSG.pCore_characteristic (p := 2) (G := ↥L))
        ((Subgroup.normalizerMonoidHom L) (A.subtype a))
    exact hmap ▸ Subgroup.mem_map_of_mem _ hm
  have hcop : ¬ 3 ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk]
    intro h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  have hgenA : Subgroup.zpowers g = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, ha⟩ -
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hk
  have hβg : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hNα g =
      barConjAut (L := L) y := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    rw [barConjAut_of_mem (L := L) hy, barAction_mk]
    rfl
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hA3 α N hNα hcop
  apply le_antisymm
  · intro q hq
    have hq' : barConjAut (L := L) y q = q := by
      rw [barFixed] at hq
      exact hq
    have hqL : q ∈ {q : ↥L ⧸ N | ∀ a : ↥A,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hNα a q = q} := by
      intro a
      have hg : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hNα g q = q := by
        rw [hβg]; exact hq'
      exact r876fl_fixed_of_zpowers_fixed _ hgenA hg a
    rw [hlift] at hqL
    rw [Set.mem_image] at hqL
    obtain ⟨c, hc, hcq⟩ := hqL
    rw [← hcq]
    refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have hcg : α g c = c := hc g
    change ((Subgroup.normalizerMonoidHom L) n) c = c at hcg
    have hg' : y * (c : G) * y⁻¹ = (c : G) := by
      have := congrArg (fun z : ↥L => (z : G)) hcg
      rwa [r876fl_normalizerMonoidHom_apply_coe] at this
    calc (c : G) * y = (y * (c : G) * y⁻¹) * y := by rw [hg']
      _ = y * (c : G) := by group
  · intro q hq
    rw [Subgroup.mem_map] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hc
    have hgc : α g c = c := by
      change ((Subgroup.normalizerMonoidHom L) n) c = c
      apply Subtype.ext
      show y * (c : G) * y⁻¹ = (c : G)
      rw [← hc]
      group
    change barConjAut (L := L) y (QuotientGroup.mk' N c) = QuotientGroup.mk' N c
    rw [← hβg]
    rw [QuotientGroup.mk'_apply]
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    rw [hgc]

@[expose] def K762 : Prop :=
  ∀ (L : Type) [Group L], CFSG.Blueprint.LieModel L .PSL 3 2 2 → ∀ α : MulAut L,
    orderOf α = 3 → α ∉ inner L →
    Nonempty (↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id L)) ≃* alternatingGroup (Fin 5)) ∨
      (Nat.card ↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id L)) = 21 ∧
        ∃ a b : ↥(MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id L)), a * b ≠ b * a)

structure Loc876 {G : Type} [Group G] [Finite G] (M L Z : Subgroup G) : Prop where
  maxLocal : rankThreeIsMaxTwoLocal M
  le : L ≤ M
  norm : M ≤ Subgroup.normalizer (L : Set G)
  shape : IsL3 (Bar2 L) 2
  hZL : Z ≤ L
  hZ3 : Nat.card Z = 3
  hZN : Subgroup.normalizer (Z : Set G) ≤ M
  sylowU : ∀ E : Subgroup G, E ≤ L → Nat.card E = 9 → E ∈ uniqueSet M

structure Cfg0876 {G : Type} [Group G] [Finite G] (M L Z Y : Subgroup G) (g : G) : Prop where
  loc : Loc876 M L Z
  hg : g ∉ M
  hY : Y = Z.map (MulAut.conj g⁻¹).toMonoidHom
  hYM : Y ≤ M

structure Cfg876 {G : Type} [Group G] [Finite G] (M L Z Y : Subgroup G) (g : G) : Prop where
  base : Cfg0876 M L Z Y g
  hZY : Y ≤ Subgroup.centralizer (Z : Set G)

structure AConf876 {G : Type} [Group G] [Finite G] (L Z Y : Subgroup G) (g : G)
    (A : Subgroup G) : Prop where
  le : A ≤ Subgroup.centralizer (Y : Set G) ⊓ L
  card : Nat.card A = 7
  normZ : Z ≤ Subgroup.normalizer (A : Set G)
  comm : ⁅A, Z⁆ = A
  trivBar : ⁅A, L.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≤
    pCoreOf 2 (L.map (MulAut.conj g⁻¹).toMonoidHom)

@[expose] def S7_876 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  UC6S846.SigmaStd D → 3 ∉ D.sig →
    ∀ (L Z Y A : Subgroup G) (g : G), Cfg876 D.M L Z Y g → AConf876 L Z Y g A →
      Subgroup.normalizer (A : Set G) ≤ D.M

private theorem r876_card_center_eq_one {B : Type} [Group B] (hs : IsSimpleGroup B)
    (hq : CFSG.Open.IsQuasisimple B) : Nat.card (Subgroup.center B) = 1 := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center B) with h | h
  · rw [h, Subgroup.card_bot]
  · exfalso
    have : Nontrivial (B ⧸ Subgroup.center B) := hq.2.toNontrivial
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (B ⧸ Subgroup.center B)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    apply hxy
    rw [QuotientGroup.eq, h]
    exact Subgroup.mem_top _

private theorem r876_exists_E9 {G : Type} [Group G] [Finite G] {X P : Subgroup G}
    (hP : IsSylowOf 3 P X) (hX : 2 ≤ CFSG.Open.pRank 3 X) :
    ∃ E : Subgroup G, E ≤ P ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPle : CFSG.Open.pRank 3 X ≤ CFSG.Open.pRank 3 P :=
    CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hP.le hP le_rfl
  have hPrank : 2 ≤ CFSG.Open.pRank 3 P := hX.trans hPle
  obtain ⟨z, hzP, hzord⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank Nat.prime_three (H := P) (by omega)
  have hzcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzord]
  obtain ⟨E, -, hEP, hEab, hEcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime (B := P)
      (X := Subgroup.zpowers z) hP.isPGroup hPrank (Subgroup.zpowers_le.mpr hzP) hzcard
  exact ⟨E, hEP, hEab, hEcard⟩

private theorem r876_not_solvable {G : Type} [Group G] [Finite G] {D : Data G} (h873 : R873 D)
    {L X H : Subgroup G} (hmin : MinCex869 D L X H) (hXM : X ≤ D.M) :
    ¬ Group.IsSolvable ↥D.M := by
  intro hs
  have : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXM)
      (Subgroup.inclusion_injective hXM)
  obtain ⟨hperf, hsimple⟩ : CFSG.Open.IsQuasisimple ↥X :=
    (h873 L X H hmin).1.elim (fun h => h.1) (fun h => h.1)
  have : Nontrivial (↥X ⧸ Subgroup.center ↥X) := hsimple.toNontrivial
  have : Nontrivial ↥X := (QuotientGroup.mk'_surjective (Subgroup.center ↥X)).nontrivial
  exact (IsSolvable.commutator_lt_top_of_nontrivial ↥X).ne hperf

private theorem r876_ne_bot {G : Type} [Group G] [Finite G] {X P : Subgroup G}
    (hP : IsSylowOf 3 P X) (hX : 2 ≤ CFSG.Open.pRank 3 X) : P ≠ ⊥ := by
  intro hbot
  obtain ⟨E, hEP, -, hEcard⟩ := r876_exists_E9 hP hX
  rw [hbot, le_bot_iff] at hEP
  rw [hEP, Subgroup.card_bot] at hEcard
  norm_num at hEcard

private theorem r876eq_pCore_bot {G : Type} [Group G] {X : Subgroup G}
    (h : pCoreOf 2 X = ⊥) : CFSG.pCore 2 ↥X = ⊥ := by
  have h' : (CFSG.pCore 2 ↥X).map X.subtype = (⊥ : Subgroup ↥X).map X.subtype := by
    rw [Subgroup.map_bot]
    simpa [CFSG.Open.pCoreOf] using h
  exact Subgroup.map_injective X.subtype_injective h'

private noncomputable def r876eq_bar2_self {G : Type} [Group G] {X : Subgroup G}
    (h : CFSG.pCore 2 ↥X = ⊥) : Bar2 X ≃* ↥X :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem r876_equiv {G : Type} [Group G] [Finite G] {D : Data G} (h873 : R873 D)
    {L X H : Subgroup G} (hmin : MinCex869 D L X H) : Nonempty (↥X ≃* Bar2 L) := by
  have hsup : X ⊔ pCoreOf 2 L = L := hmin.hyp.2.2.1
  have hpcX : CFSG.pCore 2 ↥X = ⊥ := r876eq_pCore_bot (h873 L X H hmin).2
  obtain ⟨e⟩ := nonempty_bar2_equiv_of_sup_pCore L X hsup
  exact ⟨(r876eq_bar2_self hpcX).symm.trans e⟩

theorem r876_shape {G : Type} [Group G] [Finite G] {D : Data G} (h873 : R873 D)
    {L X H : Subgroup G} (hmin : MinCex869 D L X H) (hX : IsL3 ↥X 2) : IsL3 (Bar2 L) 2 := by
  obtain ⟨e⟩ := r876_equiv h873 hmin
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hX

theorem r876_norm {G : Type} [Group G] [Finite G] {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h870 : R870 D) (h873 : R873 D) {L X H P : Subgroup G} (hmin : MinCex869 D L X H)
    (hX : IsL3 ↥X 2) (hP : IsSylowOf 3 P X) : D.M ≤ Subgroup.normalizer (L : Set G) := by
  rcases hmin.hyp.1 with hL | ⟨-, hN, -⟩
  · by_contra hnN
    have hX2 : 2 ≤ CFSG.Open.pRank 3 X := r873M3_of_r873 h873 L X H hmin
    obtain ⟨E, hEP, hEab, hEcard⟩ := r876_exists_E9 hP hX2
    have hEL : E ≤ L := hEP.trans (hP.le.trans hmin.hyp.2.1)
    have hs : IsSimpleGroup (Bar2 L) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide)
        (r876_shape h873 hmin hX)
    have hZ : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L)) := by
      rw [r876_card_center_eq_one hs hL.2.2]
      norm_num
    have h4 := UC6S846.calCRankTwice D.M L hL hnN 3 Nat.prime_three (by norm_num) hZ E hEL hEab 2
      hEcard
    have h3 := pRank_le_three_of_minCex hSg h870 hmin Nat.prime_three (by norm_num) (by omega)
    omega
  · exact hN

private theorem r876su_le {G : Type} [Group G] [Finite G] {D : Data G}
    {L X H : Subgroup G} (hmin : MinCex869 D L X H) : L ≤ D.M := by
  rcases hmin.hyp.1 with hL | ⟨hLM, -, -⟩
  · exact CFSG.Quasithin.A3.subnormal_le hL.1
  · exact hLM

private theorem r876su_exists_E0 {G : Type} [Group G] [Finite G] {D : Data G}
    (h63 : UC6.R6_3 D) (h873 : R873 D) (h874 : R874 D) {L X H : Subgroup G}
    (hmin : MinCex869 D L X H) {Q : Subgroup G} (hQ : IsSylowOf 3 Q (H ⊓ D.M))
    (hQX : IsSylowOf 3 (Q ⊓ X) X) :
    ∃ E₀ : Subgroup G, E₀ ≤ Q ⊓ X ∧ IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ 2 ∧
      E₀ ∈ uniqueSet D.M := by
  have hX2 : 2 ≤ CFSG.Open.pRank 3 X := r873M3_of_r873 h873 L X H hmin
  have hΓP : CFSG.Open.rankThreeGamma 1 3 (Q ⊓ X) ≤ D.M :=
    (h874 L X H hmin Q hQ hQX).2
  have hQM : Q ≤ D.M := hQ.le.trans inf_le_right
  have hPle : CFSG.Open.pRank 3 X ≤ CFSG.Open.pRank 3 (Q ⊓ X) :=
    CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hQX.le hQX le_rfl
  have hPrank : 2 ≤ CFSG.Open.pRank 3 (Q ⊓ X) := hX2.trans hPle
  obtain ⟨z, hzP, hzord⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank Nat.prime_three
      (H := Q ⊓ X) (by omega)
  have hzcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzord]
  obtain ⟨E, -, hEP, hEab, hEcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime
      (B := Q ⊓ X) (X := Subgroup.zpowers z) hQX.isPGroup hPrank
      (Subgroup.zpowers_le.mpr hzP) hzcard
  have hEM : E ≤ D.M := hEP.trans (inf_le_left.trans hQM)
  have hΓE : CFSG.Open.rankThreeGamma 1 3 E ≤ D.M := by
    have hmono : CFSG.Open.rankThreeGamma 1 3 E ≤ CFSG.Open.rankThreeGamma 1 3 (Q ⊓ X) := by
      simpa [CFSG.Open.rankThreeGamma] using
        CFSG.HardMathSupport.Solomon.Proving.GLBCore_mono (p := 3) (k := 1) hEP
    exact hmono.trans hΓP
  have hUniqE : CFSG.LocalAnalysis.UniquenessCase.UC22.UniqueMax D.M E :=
    h63 3 (by norm_num) (by norm_num) E hEM hEab hEcard hΓE
  have hME : E ∈ uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_forall D.maxLocal hEM
      (fun K hK hEK => by
        have hmem : K ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calMOf E := ⟨hK, hEK⟩
        rw [hUniqE] at hmem
        exact Set.mem_singleton_iff.mp hmem)
  exact ⟨E, hEP, hEab, hEcard, hME⟩

theorem r876_factorization {G : Type} [Group G] [Finite G] {L X : Subgroup G}
    (hsup : X ⊔ CFSG.Open.pCoreOf 2 L = L) (hbot : CFSG.pCore 2 ↥X = ⊥) (hX : IsL3 ↥X 2) :
    (Nat.card ↥L).factorization 3 = 2 := by
  obtain ⟨e₁⟩ := nonempty_bar2_equiv_of_sup_pCore L X hsup
  have hcardBarX : Nat.card (Bar2 X) = Nat.card ↥X := by
    show Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = Nat.card ↥X
    rw [hbot]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  have hbar : Nat.card (Bar2 L) = 20160 := by
    rw [← Nat.card_congr e₁.toEquiv, hcardBarX,
      CFSG.Blueprint.LieModel.card_psl_three_four hX]
  have hcard : Nat.card ↥L = 20160 * Nat.card ↥(CFSG.pCore 2 ↥L) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
    rw [show Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 20160 from hbar] at h
    exact h
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  rw [hcard, hn, Nat.factorization_mul (by norm_num) (pow_ne_zero n (by norm_num)),
    Nat.factorization_pow]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have h1 : (20160 : ℕ).factorization 3 = 2 := by
    rw [Nat.factorization_def _ Nat.prime_three]
    rw [show 20160 = 3 ^ 2 * 2240 by norm_num,
      padicValNat_base_pow_mul (p := 3) (n := 2240) (by norm_num) (by norm_num)]
    rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2240)]
  have h2 : (2 : ℕ).factorization 3 = 0 := by
    rw [Nat.factorization_def _ Nat.prime_three]
    exact padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)
  rw [h1, h2]
  ring

theorem r876_conj_of_card {G : Type} [Group G] [Finite G] {L E E₀ : Subgroup G}
    (hE₀L : E₀ ≤ L) (hEL : E ≤ L) (hE₀card : Nat.card E₀ = 3 ^ 2)
    (hEcard : Nat.card E = 3 ^ 2) (hfac : (Nat.card ↥L).factorization 3 = 2) :
    ∃ l : G, l ∈ L ∧ E = E₀.map (MulAut.conj l).toMonoidHom := by
  have hcard₀ : Nat.card E₀ = 3 ^ (Nat.card ↥L).factorization 3 := by
    rw [hfac, hE₀card]
  have hcard : Nat.card E = 3 ^ (Nat.card ↥L).factorization 3 := by
    rw [hfac, hEcard]
  have hS₀ : IsSylowOf 3 E₀ L := CFSG.ABGLocalTools.isSylowOf_of_card hE₀L hcard₀
  have hS : IsSylowOf 3 E L := CFSG.ABGLocalTools.isSylowOf_of_card hEL hcard
  obtain ⟨P₀, hP₀⟩ := hS₀.exists_sylow_eq_subgroupOf
  obtain ⟨P₁, hP₁⟩ := hS.exists_sylow_eq_subgroupOf
  obtain ⟨l, hl⟩ := (inferInstance : MulAction.IsPretransitive ↥L (Sylow 3 ↥L)).exists_smul_eq
    P₀ P₁
  have hsub : E.subgroupOf L = (E₀.subgroupOf L).map (MulAut.conj l).toMonoidHom := by
    rw [← hP₁, ← hP₀, ← hl, Sylow.coe_subgroup_smul]
    rfl
  have hconj_le : MulAut.conj (l : G) • E₀ ≤ L := Subgroup.conj_smul_le_of_le hE₀L l
  have hright : ((E₀.subgroupOf L).map (MulAut.conj l).toMonoidHom).map L.subtype =
      E₀.map (MulAut.conj (l : G)).toMonoidHom := by
    have h1 : (E₀.subgroupOf L).map (MulAut.conj l).toMonoidHom =
        (MulAut.conj (l : G) • E₀).subgroupOf L :=
      Subgroup.conj_smul_subgroupOf hE₀L l
    rw [h1, Subgroup.map_subgroupOf_eq_of_le hconj_le]
    rfl
  refine ⟨(l : G), l.2, ?_⟩
  have hmap := congrArg (Subgroup.map L.subtype) hsub
  rw [Subgroup.map_subgroupOf_eq_of_le hEL, hright] at hmap
  exact hmap

private theorem r876su_conj_mem_uniqueSet {G : Type} [Group G] [Finite G] {M X : Subgroup G}
    (hX : X ∈ uniqueSet M) {m : G} (hm : m ∈ M) :
    X.map (MulAut.conj m).toMonoidHom ∈ uniqueSet M := by
  have hmM : M.map (MulAut.conj m).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hm)
  refine ⟨?_, ?_⟩
  · rw [← hmM]
    exact Subgroup.map_mono hX.1
  · intro g hg
    have hXle : X ≤ M.map (MulAut.conj (m⁻¹ * g)).toMonoidHom := by
      have h1 : (X.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom ≤
          (M.map (MulAut.conj g).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom :=
        Subgroup.map_mono hg
      simp only [Subgroup.map_map] at h1
      have hcomp₁ : (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
          MonoidHom.id G := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          MonoidHom.id_apply]
        group
      have hcomp₂ : (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj (m⁻¹ * g)).toMonoidHom := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hcomp₁, hcomp₂, Subgroup.map_id] at h1
      exact h1
    have hthis := hX.2 (m⁻¹ * g) hXle
    calc M.map (MulAut.conj g).toMonoidHom
        = (M.map (MulAut.conj (m⁻¹ * g)).toMonoidHom).map (MulAut.conj m).toMonoidHom := by
          rw [Subgroup.map_map]
          have hcomp : (MulAut.conj m).toMonoidHom.comp (MulAut.conj (m⁻¹ * g)).toMonoidHom =
              (MulAut.conj g).toMonoidHom := by
            ext x
            simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            group
          rw [hcomp]
      _ = M.map (MulAut.conj m).toMonoidHom := by rw [hthis]
      _ = M := hmM

theorem r876_sylowU {G : Type} [Group G] [Finite G] {D : Data G} (h63 : UC6.R6_3 D)
    (h873 : R873 D) (h874 : R874 D) {L X H : Subgroup G} (hmin : MinCex869 D L X H)
    (hX : IsL3 ↥X 2) {Q : Subgroup G} (hQ : IsSylowOf 3 Q (H ⊓ D.M))
    (hQX : IsSylowOf 3 (Q ⊓ X) X) :
    ∀ E : Subgroup G, E ≤ L → Nat.card E = 9 → E ∈ uniqueSet D.M := by
  intro E hEL hEcard
  have hLM : L ≤ D.M := r876su_le hmin
  obtain ⟨E₀, hE₀P, -, hE₀card, hE₀U⟩ :=
    r876su_exists_E0 h63 h873 h874 hmin hQ hQX
  have hE₀L : E₀ ≤ L := hE₀P.trans (inf_le_right.trans hmin.hyp.2.1)
  have hfac : (Nat.card ↥L).factorization 3 = 2 := by
    refine r876_factorization hmin.hyp.2.2.1 ?_ hX
    have h := (h873 L X H hmin).2
    rw [CFSG.Open.pCoreOf, ← Subgroup.map_bot X.subtype] at h
    exact (Subgroup.map_subtype_inj (H := X)).mp h
  have hEcard' : Nat.card E = 3 ^ 2 := by rw [hEcard]; norm_num
  obtain ⟨l, hlL, hEl⟩ := r876_conj_of_card hE₀L hEL hE₀card hEcard' hfac
  rw [hEl]
  exact r876su_conj_mem_uniqueSet hE₀U (hLM hlL)

private theorem r876rk_exists_E9 {G : Type} [Group G] [Finite G] {B : Subgroup G}
    (hB : 2 ≤ CFSG.Open.pRank 3 B) :
    ∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  let S : Sylow 3 ↥B := default
  let P : Subgroup G := (S : Subgroup ↥B).map B.subtype
  have hP : IsSylowOf 3 P B := ⟨S, rfl⟩
  obtain ⟨E, hEP, hEab, hEcard⟩ := r876_exists_E9 (X := B) (P := P) hP hB
  exact ⟨E, hEP.trans hP.le, hEab, hEcard⟩

private theorem r876rk_normalizer_Y_le {G : Type} [Group G] {M Z Y : Subgroup G} {g : G}
    (hY : Y = Z.map (MulAut.conj g⁻¹).toMonoidHom)
    (hZN : Subgroup.normalizer (Z : Set G) ≤ M) :
    Subgroup.normalizer (Y : Set G) ≤ M.map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [hY, ← Subgroup.map_equiv_normalizer_eq Z (MulAut.conj g⁻¹)]
  exact Subgroup.map_mono hZN

private theorem r876rk_contra {G : Type} [Group G] {M E : Subgroup G} {g : G}
    (hmax : rankThreeIsMaxTwoLocal M) (hE : E ∈ uniqueSet M)
    (hEMg : E ≤ M.map (MulAut.conj g⁻¹).toMonoidHom) (hg : g ∉ M) : False := by
  have hMeq : M.map (MulAut.conj g⁻¹).toMonoidHom = M := hE.2 g⁻¹ hEMg
  have hginv : g⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMeq
  have hgN : g ∈ Subgroup.normalizer (M : Set G) := by
    simpa using inv_mem hginv
  rw [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing M hmax] at hgN
  exact hg hgN

theorem r876_rank {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg0876 M L Z Y g) :
    CFSG.Open.pRank 3 (Subgroup.centralizer (Y : Set G) ⊓ L) ≤ 1 := by
  by_contra hle
  rw [not_le] at hle
  have hB : 2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (Y : Set G) ⊓ L) := by omega
  obtain ⟨E, hEB, -, hEcard⟩ := r876rk_exists_E9 hB
  have hEL : E ≤ L := hEB.trans inf_le_right
  have hECY : E ≤ Subgroup.centralizer (Y : Set G) := hEB.trans inf_le_left
  have hE9 : Nat.card E = 9 := by rw [hEcard]; norm_num
  have hEU : E ∈ uniqueSet M := c.loc.sylowU E hEL hE9
  have hENY : E ≤ Subgroup.normalizer (Y : Set G) :=
    hECY.trans (Subgroup.centralizer_le_normalizer (Y : Set G))
  have hEMg : E ≤ M.map (MulAut.conj g⁻¹).toMonoidHom :=
    hENY.trans (r876rk_normalizer_Y_le c.hY c.loc.hZN)
  exact r876rk_contra c.loc.maxLocal hEU hEMg c.hg

private theorem r876out_center_eq_bot {X : Type} [Group X] [Finite X]
    (hcard : Nat.card X = 20160) (hs : IsSimpleGroup X) :
    Subgroup.center X = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative X := Subgroup.center_eq_top_iff.mp h
    have hp : Nat.Prime (Nat.card X) := (Group.is_simple_iff_prime_card).mp hs
    rw [hcard] at hp
    norm_num at hp

private theorem r876out_conj_eq_one_of_center_eq_bot {X : Type} [Group X] {q : X}
    (hcenter : Subgroup.center X = ⊥) (h : MulAut.conj q = 1) : q = 1 := by
  have hmem : q ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h' := congrArg (fun f : MulAut X => f g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h'
    have h2 : q * g = g * q := by
      calc q * g = q * g * q⁻¹ * q := by group
        _ = g * q := by rw [h']
    exact h2.symm
  rw [hcenter] at hmem
  simpa using hmem

private theorem r876out_two_le_pRank_centralizer {X : Type} [Group X] [Finite X]
    (hL : CFSG.Blueprint.LieModel X .PSL 3 2 2) {q : X} (hq3 : q ^ 3 = 1) :
    2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({q} : Set X)) := by
  by_cases hq1 : q = 1
  · subst hq1
    have htop : Subgroup.centralizer ({1} : Set X) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [htop]
    exact CFSG.Blueprint.LieModel.two_le_pRank_psl3_of_dvd hL Nat.prime_three (by norm_num)
  · have hqord : orderOf q = 3 := orderOf_eq_prime hq3 hq1
    have hcard : Nat.card (Subgroup.centralizer ({q} : Set X)) = 9 :=
      card_centralizer_of_orderOf_three_psl_three_four hL hqord
    have hfac : (Nat.card X).factorization 3 = 2 := by
      rw [CFSG.Blueprint.LieModel.card_psl_three_four hL]
      rw [Nat.factorization_def _ Nat.prime_three]
      have h : (20160 : ℕ) = 3 ^ 2 * 2240 := by norm_num
      rw [h, padicValNat_base_pow_mul (by norm_num) (by norm_num)]
      have hz : padicValNat 3 2240 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
      omega
    have hsyl : IsSylowOf 3 (Subgroup.centralizer ({q} : Set X)) (⊤ : Subgroup X) := by
      refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
      rw [hcard, Subgroup.card_top, hfac]
      norm_num
    have hle := CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hsyl.le hsyl le_rfl
    have htop : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      CFSG.Blueprint.LieModel.two_le_pRank_psl3_of_dvd hL Nat.prime_three (by norm_num)
    exact htop.trans hle

private theorem r876out_pRank_le_of_barFixed_eq_map {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {y : G}
    (hfix : barFixed L y = ((Subgroup.centralizer ({y} : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
    (h2 : 2 ≤ CFSG.Open.pRank 3 (barFixed L y)) :
    2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({y} : Set G) ⊓ L) := by
  have hcop : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hn]
    intro h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  set Cl : Subgroup ↥L := (Subgroup.centralizer ({y} : Set G)).subgroupOf L with hCl
  have hquot : CFSG.Open.pRank 3 (Cl.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) =
      CFSG.Open.pRank 3 Cl :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal
      3 Nat.prime_three (CFSG.pCore 2 ↥L) hcop Cl
  have hinj : CFSG.Open.pRank 3 (Cl.map L.subtype) = CFSG.Open.pRank 3 Cl :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective
      3 Nat.prime_three L.subtype L.subtype_injective Cl
  have h2' : 2 ≤ CFSG.Open.pRank 3 (Cl.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) := by
    rwa [← hfix]
  rw [hquot] at h2'
  rw [← hinj] at h2'
  rw [hCl, Subgroup.subgroupOf_map_subtype] at h2'
  exact h2'

theorem r876_out {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg0876 M L Z Y g) {y : G} (hy : y ∈ Y) (hy1 : y ≠ 1) :
    barConjAut (L := L) y ∉ inner (Bar2 L) := by
  intro hinner
  have hsimple : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) c.loc.shape
  have hcard : Nat.card (Bar2 L) = 20160 :=
    CFSG.Blueprint.LieModel.card_psl_three_four c.loc.shape
  have hcenter : Subgroup.center (Bar2 L) = ⊥ := r876out_center_eq_bot hcard hsimple
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := c.loc.norm (c.hYM hy)
  have hYcard : Nat.card Y = 3 := by
    rw [c.hY, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact c.loc.hZ3
  have hy3 : orderOf y = 3 := by
    have hzp : Subgroup.zpowers y ≤ Y := Subgroup.zpowers_le.mpr hy
    have hdvd : orderOf y ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hzp
      rw [hYcard, Nat.card_zpowers] at h
      exact h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 (fun hh => hy1 (orderOf_eq_one_iff.mp hh))
    · exact h3
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range] at hinner
  obtain ⟨q, hq⟩ := hinner
  have hq3 : q ^ 3 = 1 := by
    have hy3pow : y ^ 3 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hy3]
    have hconj : MulAut.conj (q ^ 3) = 1 := by
      rw [map_pow, hq, barConjAut_of_mem hyN, ← map_pow]
      have h1 : (⟨y, hyN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext hy3pow
      rw [h1, map_one]
    exact r876out_conj_eq_one_of_center_eq_bot hcenter hconj
  have hfix_eq : barFixed L y = Subgroup.centralizer ({q} : Set (Bar2 L)) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff]
    change (barConjAut (L := L) y) x = x ↔ x * q = q * x
    rw [← hq, MulAut.conj_apply]
    constructor
    · intro hx
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm
    · intro hx
      rw [mul_inv_eq_iff_eq_mul]
      exact hx.symm
  have h2 : 2 ≤ CFSG.Open.pRank 3 (barFixed L y) := by
    rw [hfix_eq]
    exact r876out_two_le_pRank_centralizer c.loc.shape hq3
  have hfix_lift := r876_fixed_lift (L := L) hyN hy3
  have h2' : 2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({y} : Set G) ⊓ L) :=
    r876out_pRank_le_of_barFixed_eq_map hfix_lift h2
  have hzpy : Subgroup.zpowers y = Y :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
      (by rw [hYcard, Nat.card_zpowers, hy3])
  have hcentY : Subgroup.centralizer (Y : Set G) = Subgroup.centralizer ({y} : Set G) := by
    rw [← hzpy, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hcentY] at h2'
  have hrank := r876_rank c
  omega

private theorem r876red_sylow_conj {L' : Type} [Group L'] [Finite L'] {S : Subgroup L'}
    (hfact : (Nat.card S).factorization 3 = 1)
    {A B : Subgroup L'} (hAS : A ≤ S) (hBS : B ≤ S)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) :
    ∃ l ∈ S, B = A.map (MulAut.conj l⁻¹).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : Nat.card (A.subgroupOf S) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv, hA]
  have hB3 : Nat.card (B.subgroupOf S) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv, hB]
  let P : Sylow 3 S := Sylow.ofCard (A.subgroupOf S) (by rw [hfact, pow_one]; exact hA3)
  let Q : Sylow 3 S := Sylow.ofCard (B.subgroupOf S) (by rw [hfact, pow_one]; exact hB3)
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq S Q P
  have hmap : (P : Subgroup S) = (Q : Subgroup S).map (MulAut.conj s).toMonoidHom := by
    rw [← hs, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hcomp : S.subtype.comp (MulAut.conj s).toMonoidHom =
      (MulAut.conj (s : L')).toMonoidHom.comp S.subtype := by
    ext x
    simp
  have hsub : A = B.map (MulAut.conj (s : L')).toMonoidHom := by
    have h := congrArg (fun T : Subgroup S => T.map S.subtype) hmap
    have hP : (P : Subgroup S) = A.subgroupOf S := rfl
    have hQ : (Q : Subgroup S) = B.subgroupOf S := rfl
    rw [hP, hQ] at h
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hAS, Subgroup.map_subgroupOf_eq_of_le hBS] at h
    exact h
  refine ⟨(s : L'), s.2, ?_⟩
  rw [show A = B.map (MulAut.conj (s : L')).toMonoidHom from hsub]
  rw [Subgroup.map_map]
  rw [show (MulAut.conj (s : L')⁻¹).toMonoidHom.comp (MulAut.conj (s : L')).toMonoidHom =
    MonoidHom.id L' from by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group]
  rw [Subgroup.map_id]

private theorem r876red_conj_of_mk_eq {L' : Type} [Group L'] [Finite L'] {N : Subgroup L'}
    [N.Normal] (hN : ¬ 3 ∣ Nat.card N) {a b : L'} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : QuotientGroup.mk' N a = QuotientGroup.mk' N b) :
    ∃ l : L', Subgroup.zpowers b = (Subgroup.zpowers a).map (MulAut.conj l⁻¹).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup L' :=
    (Subgroup.zpowers (QuotientGroup.mk' N b)).comap (QuotientGroup.mk' N)
  have hAS : Subgroup.zpowers a ≤ S := by
    intro x hx
    rw [Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' N x ∈ (Subgroup.zpowers a).map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ hx
    rwa [MonoidHom.map_zpowers, hab] at h1
  have hBS : Subgroup.zpowers b ≤ S := by
    intro x hx
    rw [Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' N x ∈ (Subgroup.zpowers b).map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ hx
    rwa [MonoidHom.map_zpowers] at h1
  have hNS : N ≤ S := by
    intro n hn
    rw [Subgroup.mem_comap,
      show (QuotientGroup.mk' N) n = 1 from (QuotientGroup.eq_one_iff n).mpr hn]
    exact Subgroup.one_mem _
  have hSmap : S.map (QuotientGroup.mk' N) = Subgroup.zpowers (QuotientGroup.mk' N b) := by
    dsimp only [S]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _
  have hcardS : Nat.card S = 3 * Nat.card N := by
    have h := CFSG.GroupTheory.CoprimeTransport.card_eq_card_map_mk_mul_card_inf (N := N) S
    rw [hSmap, Nat.card_zpowers, CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime hN hb] at h
    have hinf : S ⊓ N = N := inf_eq_right.mpr hNS
    rw [hinf] at h
    exact h
  have hfactS : (Nat.card S).factorization 3 = 1 := by
    rw [hcardS]
    have hNne : Nat.card N ≠ 0 :=
      (Nat.card_pos_iff.mpr ⟨⟨1, N.one_mem⟩, inferInstance⟩).ne'
    rw [Nat.factorization_mul (by norm_num) hNne, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd hN]
  obtain ⟨l, -, hl⟩ := r876red_sylow_conj (S := S) hfactS hAS hBS
    (by rw [Nat.card_zpowers, ha]) (by rw [Nat.card_zpowers, hb])
  exact ⟨l, hl⟩

private theorem r876red_generator {G : Type} [Group G] [Finite G] {Z : Subgroup G}
    (hZ3 : Nat.card Z = 3) : ∃ z ∈ Z, orderOf z = 3 ∧ Z = Subgroup.zpowers z := by
  have hnt : Nontrivial Z := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨z, hzZ⟩, hz1'⟩ := exists_ne (1 : Z)
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Z) (x := ⟨z, hzZ⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  refine ⟨z, hzZ, hord, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ)
  rw [Nat.card_zpowers, hord]
  exact le_of_eq hZ3

private theorem r876red_conj_zpowers {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hshape : IsL3 (Bar2 L) 2)
    (hN3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L))
    {z z0 : ↥L} (hz : orderOf z = 3) (hz0 : orderOf z0 = 3) :
    ∃ l : ↥L, Subgroup.zpowers z0 =
      (Subgroup.zpowers z).map (MulAut.conj l⁻¹).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hzb : orderOf (QuotientGroup.mk' N z) = 3 :=
    CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime hN3 hz
  have hz0b : orderOf (QuotientGroup.mk' N z0) = 3 :=
    CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime hN3 hz0
  obtain ⟨m, hm⟩ := exists_conj_of_orderOf_three_psl_three_four hshape hzb hz0b
  obtain ⟨l1, hl1⟩ := QuotientGroup.mk'_surjective N m
  have hw : QuotientGroup.mk' N (l1⁻¹ * z * l1) = QuotientGroup.mk' N z0 := by
    simp only [map_mul, map_inv, hl1]
    exact hm
  have hw3 : orderOf (l1⁻¹ * z * l1) = 3 := by
    simpa [MulAut.conj_apply] using
      (orderOf_injective (MulAut.conj l1⁻¹).toMonoidHom (MulAut.conj l1⁻¹).injective z).trans hz
  obtain ⟨s, hs⟩ := r876red_conj_of_mk_eq (N := N) hN3 hw3 hz0 hw
  have hwz : Subgroup.zpowers (l1⁻¹ * z * l1) =
      (Subgroup.zpowers z).map (MulAut.conj l1⁻¹).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    simp
  refine ⟨l1 * s, ?_⟩
  rw [hs, hwz, Subgroup.map_map]
  rw [show (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj l1⁻¹).toMonoidHom =
    (MulAut.conj (l1 * s)⁻¹).toMonoidHom from by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group]

private theorem r876red_normalizer_map_conj_le {G : Type} [Group G] {M H : Subgroup G} {l : G}
    (hlM : l ∈ M) (hH : Subgroup.normalizer (H : Set G) ≤ M) :
    Subgroup.normalizer ((H.map (MulAut.conj l⁻¹).toMonoidHom : Subgroup G) : Set G) ≤ M := by
  rw [← Subgroup.map_equiv_normalizer_eq H (MulAut.conj l⁻¹)]
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
  simpa [MulAut.conj_apply] using M.mul_mem (M.mul_mem (M.inv_mem hlM) (hH hw)) hlM

private theorem r876red_lift_z0 {G : Type} [Group G] [Finite G] {L : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) (hy3 : orderOf y = 3)
    (hN3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L)) (h3 : 3 ∣ Nat.card (barFixed L y)) :
    ∃ z0 : ↥L, orderOf z0 = 3 ∧ (z0 : G) ∈ Subgroup.centralizer ({y} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq3⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hq3' : orderOf (q : Bar2 L) = 3 := (Subgroup.orderOf_coe q).trans hq3
  have hqmem : (q : Bar2 L) ∈ ((Subgroup.centralizer ({y} : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [← r876_fixed_lift hyN hy3]
    exact q.2
  obtain ⟨z0, hz0Cl, hz0ord, -⟩ :=
    CFSG.GroupTheory.CoprimeTransport.exists_mem_orderOf_eq_prime_mk_eq (p := 3) hN3 hqmem hq3'
  exact ⟨z0, hz0ord, Subgroup.mem_subgroupOf.mp hz0Cl⟩

private theorem r876red_assemble {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg0876 M L Z Y g) {z0 l y : G} (hz0L : z0 ∈ L) (hz0ord : orderOf z0 = 3)
    (hz0comm : y * z0 = z0 * y) (hYzp : Y = Subgroup.zpowers y) (hlM : l ∈ M)
    (hlG : Subgroup.zpowers z0 = Z.map (MulAut.conj l⁻¹).toMonoidHom) :
    ∃ (Z' : Subgroup G) (g' : G), Cfg876 M L Z' Y g' := by
  refine ⟨Subgroup.zpowers z0, l⁻¹ * g, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, c.hYM⟩
    · refine ⟨c.loc.maxLocal, c.loc.le, c.loc.norm, c.loc.shape, ?_, ?_, ?_, c.loc.sylowU⟩
      · exact Subgroup.zpowers_le.mpr hz0L
      · rw [Nat.card_zpowers, hz0ord]
      · rw [hlG]
        exact r876red_normalizer_map_conj_le hlM c.loc.hZN
    · intro hmem
      apply c.hg
      have hg_eq : g = l * (l⁻¹ * g) := by group
      rw [hg_eq]
      exact M.mul_mem hlM hmem
    · rw [hlG, Subgroup.map_map, c.hY]
      rw [show (MulAut.conj (l⁻¹ * g)⁻¹).toMonoidHom.comp
          (MulAut.conj l⁻¹).toMonoidHom = (MulAut.conj g⁻¹).toMonoidHom from by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group]
  · rw [hYzp, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute z0 y from hz0comm.symm) n).eq

private theorem r876red_main {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg0876 M L Z Y g) {y : G} (hy : y ∈ Y) (hy1 : y ≠ 1)
    (h3 : 3 ∣ Nat.card (barFixed L y)) : ∃ (Z' : Subgroup G) (g' : G), Cfg876 M L Z' Y g' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYcard : Nat.card Y = 3 := by
    rw [c.hY, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact c.loc.hZ3
  have hy3pow : y ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hy⟩)
    rw [hYcard] at h
    exact congrArg Subtype.val h
  have hy3 : orderOf y = 3 := orderOf_eq_prime hy3pow hy1
  have hYzp : Y = Subgroup.zpowers y := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
    rw [Nat.card_zpowers, hy3]
    exact le_of_eq hYcard
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := c.loc.norm (c.hYM hy)
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk]
    intro h
    exact (by norm_num : ¬ (3 ∣ 2)) (Nat.prime_three.dvd_of_dvd_pow h)
  obtain ⟨z0, hz0ordL, hz0comm⟩ := r876red_lift_z0 hyN hy3 hN3 h3
  have hz0ord : orderOf ((z0 : ↥L) : G) = 3 := (Subgroup.orderOf_coe z0).trans hz0ordL
  have hz0comm' : y * (z0 : G) = (z0 : G) * y :=
    Subgroup.mem_centralizer_iff.mp hz0comm y (Set.mem_singleton y)
  obtain ⟨z, hzZ, hzord, hZzp⟩ := r876red_generator c.loc.hZ3
  have hzLord : orderOf (⟨z, c.loc.hZL hzZ⟩ : ↥L) = 3 := by
    rw [← Subgroup.orderOf_coe (⟨z, c.loc.hZL hzZ⟩ : ↥L)]
    exact hzord
  obtain ⟨l, hl⟩ := r876red_conj_zpowers (L := L) c.loc.shape hN3 hzLord hz0ordL
  have hcompL : L.subtype.comp (MulAut.conj l⁻¹).toMonoidHom =
      (MulAut.conj (l : G)⁻¹).toMonoidHom.comp L.subtype := by
    ext x
    simp
  have hlG : Subgroup.zpowers ((z0 : ↥L) : G) =
      Z.map (MulAut.conj (l : G)⁻¹).toMonoidHom := by
    have h := congrArg (fun T : Subgroup ↥L => T.map L.subtype) hl
    rw [Subgroup.map_map, hcompL, ← Subgroup.map_map] at h
    simpa only [MonoidHom.map_zpowers, hZzp, Subgroup.subtype_apply] using h
  exact r876red_assemble c (z0 := ((z0 : ↥L) : G)) (l := (l : G)) z0.2 hz0ord hz0comm'
    hYzp (c.loc.le l.2) hlG


theorem r876_reduce {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg0876 M L Z Y g) {y : G} (hy : y ∈ Y) (hy1 : y ≠ 1)
    (h3 : 3 ∣ Nat.card (barFixed L y)) : ∃ (Z' : Subgroup G) (g' : G), Cfg876 M L Z' Y g' := by
  exact r876red_main c hy hy1 h3

private theorem r876sym_map_conj_mulAut {G : Type} [Group G] (φ : MulAut G) (h : G) (M : Subgroup G) :
    (M.map (MulAut.conj h).toMonoidHom).map φ.toMonoidHom =
      (M.map φ.toMonoidHom).map (MulAut.conj (φ h)).toMonoidHom := by
  have hcomp : φ.toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (φ h)).toMonoidHom.comp φ.toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv]
  rw [Subgroup.map_map, hcomp]
  exact (Subgroup.map_map M ((MulAut.conj (φ h)).toMonoidHom) (φ.toMonoidHom)).symm

private theorem r876sym_map_conj_conj_inv {G : Type} [Group G] (a : G) (M : Subgroup G) :
    (M.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = M := by
  have hcomp : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    group
  rw [Subgroup.map_map, hcomp, Subgroup.map_id]

private theorem r876sym_map_normalizer {G : Type} [Group G] (φ : MulAut G) (H : Subgroup G) :
    (Subgroup.normalizer (H : Set G)).map φ.toMonoidHom =
      Subgroup.normalizer ((H.map φ.toMonoidHom : Subgroup G) : Set G) :=
  Subgroup.map_equiv_normalizer_eq H φ

private theorem r876sym_bar2_map_conj {G : Type} [Group G] (a : G) (H : Subgroup G) :
    Nonempty (Bar2 H ≃* Bar2 (H.map (MulAut.conj a).toMonoidHom)) :=
  ⟨QuotientGroup.congr (CFSG.pCore 2 ↥H)
    (CFSG.pCore 2 ↥(H.map (MulAut.conj a).toMonoidHom))
    (MulEquiv.subgroupMap (MulAut.conj a) H)
    (CFSG.pCore_map_iso 2 (MulEquiv.subgroupMap (MulAut.conj a) H))⟩

private theorem r876sym_isL3_map_conj {G : Type} [Group G] (a : G) {H : Subgroup G} (h : IsL3 (Bar2 H) 2) :
    IsL3 (Bar2 (H.map (MulAut.conj a).toMonoidHom)) 2 := by
  obtain ⟨e⟩ := r876sym_bar2_map_conj a H
  exact CFSG.Blueprint.LieModel.of_mulEquiv e h

private theorem r876sym_mem_uniqueSet_map_mulAut {G : Type} [Group G] [Finite G] (φ : MulAut G) {M X : Subgroup G} :
    X.map φ.toMonoidHom ∈ uniqueSet (M.map φ.toMonoidHom) ↔ X ∈ uniqueSet M := by
  unfold uniqueSet
  simp only [Set.mem_setOf_eq]
  refine and_congr (Subgroup.map_le_map_iff_of_injective φ.injective) ?_
  constructor
  · intro H k hk
    have hkφ : X.map φ.toMonoidHom ≤
        (M.map φ.toMonoidHom).map (MulAut.conj (φ k)).toMonoidHom := by
      have h := Subgroup.map_mono (f := φ.toMonoidHom) hk
      rwa [r876sym_map_conj_mulAut φ k M] at h
    have hkey := H (φ k) hkφ
    rw [← r876sym_map_conj_mulAut φ k M] at hkey
    exact Subgroup.map_injective φ.injective hkey
  · intro H h hh
    have hthis := r876sym_map_conj_mulAut φ (φ.symm h) M
    simp only [MulEquiv.apply_symm_apply] at hthis
    have hh' : X ≤ M.map (MulAut.conj (φ.symm h)).toMonoidHom := by
      rw [← hthis] at hh
      exact (Subgroup.map_le_map_iff_of_injective φ.injective).mp hh
    have hkey := H (φ.symm h) hh'
    have hmap := congrArg (fun S : Subgroup G => S.map φ.toMonoidHom) hkey
    rwa [hthis] at hmap

theorem r876_cfg_symm {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg876 M L Z Y g) :
    Cfg876 (M.map (MulAut.conj g⁻¹).toMonoidHom) (L.map (MulAut.conj g⁻¹).toMonoidHom) Y Z
      g⁻¹ := by
  have hnorm : M.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.normalizer ((L.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [← r876sym_map_normalizer (MulAut.conj g⁻¹) L]
    exact Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) c.base.loc.norm
  have hZY' : Z ≤ Subgroup.centralizer (Y : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (c.hZY hy)) z hz).symm
  have hZN : Subgroup.normalizer (Y : Set G) ≤ M.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [c.base.hY, ← r876sym_map_normalizer (MulAut.conj g⁻¹) Z]
    exact Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) c.base.loc.hZN
  have hsyl : ∀ E : Subgroup G, E ≤ L.map (MulAut.conj g⁻¹).toMonoidHom →
      Nat.card E = 9 → E ∈ uniqueSet (M.map (MulAut.conj g⁻¹).toMonoidHom) := by
    intro E hE hEcard
    have hL : (L.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = L := by
      simpa only [inv_inv] using r876sym_map_conj_conj_inv g⁻¹ L
    have hE₁L : E.map (MulAut.conj g).toMonoidHom ≤ L := by
      have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hE
      rwa [hL] at h
    have hE₁card : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEcard]
    have hmem : E.map (MulAut.conj g).toMonoidHom ∈ uniqueSet M :=
      c.base.loc.sylowU _ hE₁L hE₁card
    have hm : (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom ∈
        uniqueSet (M.map (MulAut.conj g⁻¹).toMonoidHom) :=
      (r876sym_mem_uniqueSet_map_mulAut (MulAut.conj g⁻¹)).mpr hmem
    rwa [r876sym_map_conj_conj_inv g E] at hm
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · exact CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map c.base.loc.maxLocal
      (MulAut.conj g⁻¹)
  · exact Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) c.base.loc.le
  · exact hnorm
  · exact r876sym_isL3_map_conj g⁻¹ c.base.loc.shape
  · rw [c.base.hY]
    exact Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) c.base.loc.hZL
  · rw [c.base.hY, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact c.base.loc.hZ3
  · exact hZN
  · exact hsyl
  · rintro hg'
    obtain ⟨m, hmM, hmg⟩ := Subgroup.mem_map.mp hg'
    apply c.base.hg
    have h1 : m * g = 1 := by
      have hmg' : g⁻¹ * m * g = g⁻¹ := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hmg
      calc m * g = g * (g⁻¹ * m * g) := by group
        _ = g * g⁻¹ := by rw [hmg']
        _ = 1 := by group
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_mem hmM
  · have hZY : Y.map (MulAut.conj g).toMonoidHom = Z := by
      rw [c.base.hY]
      simpa only [inv_inv] using r876sym_map_conj_conj_inv g⁻¹ Z
    rw [inv_inv]
    exact hZY.symm
  · exact hZY'.trans ((Subgroup.centralizer_le_normalizer (Y : Set G)).trans hZN)
  · exact hZY'

private theorem r876a5_center_eq_bot_of_simple_of_nat_card {B : Type} [Group B] [Finite B]
    (hs : IsSimpleGroup B) (hcard : Nat.card B = 20160) : Subgroup.center B = ⊥ := by
  have hnonab : ∃ a b : B, a * b ≠ b * a := by
    by_contra h
    have hmc : ∀ a b : B, a * b = b * a := fun a b => by
      by_contra hab
      exact h ⟨a, b, hab⟩
    have : IsMulCommutative B := isMulCommutative_iff.mpr hmc
    have hprime : (Nat.card B).Prime := (Group.is_simple_iff_prime_card (α := B)).mp hs
    rw [hcard] at hprime
    norm_num at hprime
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center B) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm

private theorem r876a5_conj_injective_of_center_eq_bot {B : Type} [Group B]
    (hZ : Subgroup.center B = ⊥) :
    Function.Injective (MulAut.conj : B →* MulAut B) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hker : (MulAut.conj : B →* MulAut B).ker = Subgroup.center B := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h y
      have h' : (MulAut.conj x) y = y := by rw [h]; rfl
      rw [MulAut.conj_apply] at h'
      have : x * y = y * x := by
        calc x * y = (x * y * x⁻¹) * x := by group
          _ = y * x := by rw [h']
      exact this.symm
    · intro h
      ext y
      rw [MulAut.conj_apply]
      have := h y
      calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [← this]
        _ = y := by group
  rw [hker, hZ]

private theorem r876a5_centralizer_conj_psl_three_four {B : Type} [Group B] [Finite B]
    (hL : CFSG.Blueprint.LieModel B .PSL 3 2 2) (s : B) (hs : orderOf s = 3) :
    Group.IsSolvable ↥(Subgroup.centralizer ({MulAut.conj s} : Set (MulAut B))) := by
  have hsimp : IsSimpleGroup B :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
      (by simp [CFSG.Blueprint.classicalTags]) hL
  have hZ : Subgroup.center B = ⊥ :=
    r876a5_center_eq_bot_of_simple_of_nat_card hsimp
      (CFSG.Blueprint.LieModel.card_psl_three_four hL)
  have hcj : Function.Injective (MulAut.conj : B →* MulAut B) :=
    r876a5_conj_injective_of_center_eq_bot hZ
  let Bc : Subgroup (MulAut B) := Subgroup.centralizer ({MulAut.conj s} : Set (MulAut B))
  let I : Subgroup (MulAut B) :=
    (Subgroup.centralizer ({s} : Set B)).map (MulAut.conj : B →* MulAut B)
  have hIle : I ≤ Bc := by
    rintro x ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_iff.mp ha s (Set.mem_singleton s)
    rw [← map_mul, ← map_mul, h]
  have hIcard : Nat.card I = 9 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj : B →* MulAut B)) hcj]
    exact card_centralizer_of_orderOf_three_psl_three_four hL hs
  have hIsolv : Group.IsSolvable ↥I := by
    refine CFSG.Quasithin.C41Pf.isSolvable_of_card_eq_pow_mul_pow (p := 3) (q := 2)
      (a := 2) (b := 0) Nat.prime_three Nat.prime_two (by norm_num) ?_
    rw [hIcard]; norm_num
  have hOutsolv : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer B) := by
    refine CFSG.Quasithin.C41Pf.isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3)
      (a := 2) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
    rw [card_outer_psl_three_four hL]; norm_num
  have hker : ((QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner B)).comp Bc.subtype).ker ≤
      (Subgroup.inclusion hIle).range := by
    intro x hx
    rw [Subgroup.inclusion_range]
    rw [Subgroup.mem_subgroupOf]
    have hxinner : (x : MulAut B) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner B := by
      have h1 : (QuotientGroup.mk'
          (CFSG.ComponentClassification.OuterAutomorphisms.inner B)) (x : MulAut B) = 1 := by
        have := hx
        rwa [MonoidHom.mem_ker] at this
      exact (QuotientGroup.eq_one_iff
        (N := CFSG.ComponentClassification.OuterAutomorphisms.inner B) (x := ↑x)).mp h1
    have hxB : (x : MulAut B) ∈ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut B)) := x.2
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hxinner
    refine Subgroup.mem_map.mpr ⟨a, ?_, ha⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : (MulAut.conj a) * (MulAut.conj s) = (MulAut.conj s) * (MulAut.conj a) := by
      rw [ha]
      exact Subgroup.mem_centralizer_singleton_iff.mp hxB
    have h2' : MulAut.conj (a * s) = MulAut.conj (s * a) := by
      simpa only [map_mul] using h2
    exact hcj h2'
  have : Group.IsSolvable ↥I := hIsolv
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer B) := hOutsolv
  exact Group.isSolvable_of_ker_le_range (Subgroup.inclusion hIle)
    ((QuotientGroup.mk'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner B)).comp Bc.subtype) hker

private theorem r876a5_alt5_not_solvable : ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
  have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have : Nontrivial (alternatingGroup (Fin 5)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp)
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))

theorem r876_a5 {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg876 M L Z Y g) {y : G} (hy : y ∈ Y) (hy1 : y ≠ 1)
    (hA5 : Nonempty (↥(barFixed L y) ≃* alternatingGroup (Fin 5)))
    (hout : ∀ z ∈ Z, z ≠ 1 →
      barConjAut (L := L.map (MulAut.conj g⁻¹).toMonoidHom) z ∉
        inner (Bar2 (L.map (MulAut.conj g⁻¹).toMonoidHom))) : False := by
  have hZL : Z ≤ L := c.base.loc.hZL
  have hYM : Y ≤ M := c.base.hYM
  have hYnormL : Y ≤ Subgroup.normalizer (L : Set G) := hYM.trans c.base.loc.norm
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hYnormL hy
  have hYcard : Nat.card Y = 3 := by
    rw [c.base.hY, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact c.base.loc.hZ3
  have hy3 : orderOf y = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hpow : y ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hy⟩)
      rw [hYcard] at h
      exact congrArg Subtype.val h
    exact orderOf_eq_prime hpow hy1
  have hYzp : Y = Subgroup.zpowers y := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy) ?_).symm
    rw [hYcard, Nat.card_zpowers, hy3]
  have hcent_eq : Subgroup.centralizer (Y : Set G) = Subgroup.centralizer ({y} : Set G) := by
    rw [hYzp, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  let C : Subgroup G := Subgroup.centralizer ({y} : Set G) ⊓ L
  have hZC : Z ≤ C := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨?_, hZL hz⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (c.hZY hy) z hz
  have hfl := r876_fixed_lift (L := L) hyN hy3
  let f : ↥C →* Bar2 L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion (inf_le_right : C ≤ L))
  have hf_range : f.range = barFixed L y := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    change ((Subgroup.centralizer ({y} : Set G) ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = barFixed L y
    rw [Subgroup.inf_subgroupOf_right]
    exact hfl.symm
  let f' : ↥C →* ↥(barFixed L y) := f.codRestrict (barFixed L y) (fun x => by
    rw [← hf_range]; exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hf'_surj : Function.Surjective f' := by
    intro b
    have hb : (b : Bar2 L) ∈ f.range := by rw [hf_range]; exact b.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hb
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨e⟩ := hA5
  let π : ↥C →* alternatingGroup (Fin 5) := e.toMonoidHom.comp f'
  have hπ_surj : Function.Surjective π := by
    intro a
    obtain ⟨b, hb⟩ := e.surjective a
    obtain ⟨x, hx⟩ := hf'_surj b
    exact ⟨x, by change e (f' x) = a; rw [hx, hb]⟩
  have hπ_ker : π.ker = f.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : e (f' x) = e 1 := by rw [map_one]; exact hx
      have h2 : f' x = 1 := e.injective h1
      have h3 : f x = 1 := by
        have h4 : (f' x : Bar2 L) = (1 : ↥(barFixed L y)) := congrArg Subtype.val h2
        change f x = 1 at h4
        exact h4
      exact h3
    · intro hx
      have h2 : f' x = 1 := by
        apply Subtype.ext
        change f x = 1
        exact hx
      change e (f' x) = 1
      rw [h2, map_one]
  let Lg : Subgroup G := L.map (MulAut.conj g⁻¹).toMonoidHom
  have hcs := r876_cfg_symm c
  have hYLg : Y ≤ Lg := by
    intro x hx
    rw [c.base.hY] at hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨z, hZL hz, rfl⟩
  have hCnormLg : C ≤ Subgroup.normalizer (Lg : Set G) := by
    have h1 : C ≤ Subgroup.normalizer (Y : Set G) := by
      intro x hx
      have hx1 : x ∈ Subgroup.centralizer ({y} : Set G) := (Subgroup.mem_inf.mp hx).1
      have hx2 : x ∈ Subgroup.centralizer (Y : Set G) := by rwa [hcent_eq]
      exact Subgroup.centralizer_le_normalizer (Y : Set G) hx2
    exact h1.trans (hcs.base.loc.hZN.trans hcs.base.loc.norm)
  let Φ : ↥C →* MulAut (Bar2 Lg) :=
    (barAction Lg).comp (Subgroup.inclusion hCnormLg)
  have hyLg : y ∈ Lg := hYLg hy
  have hyNormLg : y ∈ Subgroup.normalizer (Lg : Set G) := Subgroup.le_normalizer hyLg
  have hbar_y : barAction Lg ⟨y, hyNormLg⟩ =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Lg) ⟨y, hyLg⟩) := by
    apply MulEquiv.ext
    intro a
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective a
    rw [barAction_mk, MulAut.conj_apply, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    rfl
  have hpCore_not_dvd : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥Lg) := by
    intro h3
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Lg)))
    rw [hn] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hord_y_Lg : orderOf (⟨y, hyLg⟩ : ↥Lg) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · simpa using (orderOf_eq_prime_iff.mp hy3).1
    · intro h
      exact hy1 (congrArg Subtype.val h)
  have hord_mk : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Lg) ⟨y, hyLg⟩) = 3 :=
    CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime hpCore_not_dvd hord_y_Lg
  have hB_solv : Group.IsSolvable ↥(Subgroup.centralizer
      ({MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Lg) ⟨y, hyLg⟩)} :
        Set (MulAut (Bar2 Lg)))) :=
    r876a5_centralizer_conj_psl_three_four (B := Bar2 Lg) hcs.base.loc.shape
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Lg) ⟨y, hyLg⟩) hord_mk
  have hΦ_le_B : Φ.range ≤ Subgroup.centralizer
      ({MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Lg) ⟨y, hyLg⟩)} :
        Set (MulAut (Bar2 Lg))) := by
    rintro x ⟨cc, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcy : (Subgroup.inclusion hCnormLg cc) *
        (⟨y, hyNormLg⟩ : Subgroup.normalizer (Lg : Set G)) =
        (⟨y, hyNormLg⟩ : Subgroup.normalizer (Lg : Set G)) *
          (Subgroup.inclusion hCnormLg cc) := by
      ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp cc.2).1
    have h1 : Φ cc * barAction Lg ⟨y, hyNormLg⟩ =
        barAction Lg ⟨y, hyNormLg⟩ * Φ cc := by
      rw [show Φ cc = barAction Lg (Subgroup.inclusion hCnormLg cc) from rfl]
      rw [← map_mul, ← map_mul, hcy]
    rw [hbar_y] at h1
    exact h1
  have hΦ_solv : Group.IsSolvable ↥Φ.range := by
    have : Group.IsSolvable ↥(Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Lg) ⟨y, hyLg⟩)} :
          Set (MulAut (Bar2 Lg)))) := hB_solv
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hΦ_le_B) (Subgroup.inclusion_injective hΦ_le_B)
  let K : Subgroup ↥C := Φ.ker
  have hKnormal : K.Normal := MonoidHom.normal_ker Φ
  have hπK_normal : (K.map π).Normal := Subgroup.Normal.map inferInstance π hπ_surj
  have : (K.map π).Normal := hπK_normal
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hπK_dich : K.map π = ⊥ ∨ K.map π = ⊤ :=
    IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map π)
  rcases hπK_dich with hbot | htop
  ·
    have hKle : K ≤ π.ker := by
      intro k hk
      rw [MonoidHom.mem_ker]
      have : π k ∈ K.map π := ⟨k, hk, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have hlift_surj : Function.Surjective (QuotientGroup.lift (N := K) π hKle) :=
      QuotientGroup.lift_surjective_of_surjective (N := K) π hπ_surj hKle
    have hΦrange : Group.IsSolvable ↥Φ.range := hΦ_solv
    have : Group.IsSolvable (↥C ⧸ K) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (QuotientGroup.quotientKerEquivRange Φ).toMonoidHom)
        (QuotientGroup.quotientKerEquivRange Φ).injective
    have : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_surjective hlift_surj
    exact r876a5_alt5_not_solvable this
  ·
    have hΦrange_eq : Φ.range = (f.ker).map Φ := by
      apply le_antisymm
      · rintro x ⟨cc, rfl⟩
        have hπc : π cc ∈ K.map π := by rw [htop]; exact Subgroup.mem_top _
        obtain ⟨k, hkK, hk_eq⟩ := hπc
        have hkker : Φ k = 1 := MonoidHom.mem_ker.mp hkK
        have ht_mem : cc * k⁻¹ ∈ f.ker := by
          rw [← hπ_ker, MonoidHom.mem_ker, map_mul, map_inv, hk_eq, mul_inv_cancel]
        refine Subgroup.mem_map.mpr ⟨cc * k⁻¹, ht_mem, ?_⟩
        rw [map_mul, map_inv, hkker, inv_one, mul_one]
      · exact Subgroup.map_le_range Φ _
    have hfker2 : IsPGroup 2 ↥(f.ker) := by
      have hfker_eq : f.ker = (CFSG.pCore 2 ↥L).comap
          (Subgroup.inclusion (inf_le_right : C ≤ L)) := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_comap]
        exact QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L)
          (x := Subgroup.inclusion (inf_le_right : C ≤ L) x)
      rw [hfker_eq]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).comap_of_injective
        (Subgroup.inclusion (inf_le_right : C ≤ L)) (Subgroup.inclusion_injective inf_le_right)
    have hΦ2 : IsPGroup 2 ↥Φ.range := by
      rw [hΦrange_eq]
      exact hfker2.map Φ
    have hZnt : Nontrivial ↥Z := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [c.base.loc.hZ3]; norm_num)
    obtain ⟨⟨z, hzZ⟩, hz1'⟩ := exists_ne (1 : ↥Z)
    have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
    have hzC : z ∈ C := hZC hzZ
    have hz3 : z ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hzZ⟩)
      rw [c.base.loc.hZ3] at h
      exact congrArg Subtype.val h
    have hz3C : (⟨z, hzC⟩ : ↥C) ^ 3 = 1 := by
      ext
      change z ^ 3 = 1
      exact hz3
    have hΦz3 : (Φ ⟨z, hzC⟩) ^ 3 = 1 := by
      rw [← map_pow, hz3C, map_one]
    obtain ⟨m, hm⟩ := hΦ2 ⟨Φ ⟨z, hzC⟩, MonoidHom.mem_range.mpr ⟨⟨z, hzC⟩, rfl⟩⟩
    have hm' : (Φ ⟨z, hzC⟩) ^ (2 ^ m) = 1 := congrArg Subtype.val hm
    have hord2 : orderOf (Φ ⟨z, hzC⟩) ∣ 2 ^ m := orderOf_dvd_iff_pow_eq_one.mpr hm'
    have hord3 : orderOf (Φ ⟨z, hzC⟩) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hΦz3
    have hord1 : orderOf (Φ ⟨z, hzC⟩) = 1 := by
      rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf (Φ ⟨z, hzC⟩)) hord3 with h1 | h3
      · exact h1
      · exfalso
        rw [h3] at hord2
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hord2) (by norm_num)
    have hΦz1 : Φ ⟨z, hzC⟩ = 1 := orderOf_eq_one_iff.mp hord1
    have hΦz_eq : Φ ⟨z, hzC⟩ = barConjAut (L := Lg) z := by
      rw [barConjAut_of_mem (L := Lg) (hCnormLg hzC)]
      rfl
    have hbar1 : barConjAut (L := Lg) z = 1 := hΦz_eq ▸ hΦz1
    exact hout z hzZ hz1 (by rw [hbar1]; exact Subgroup.one_mem _)

private theorem r876a_order21_unique_seven {F : Type} [Group F] [Finite F]
    (hF : Nat.card F = 21) :
    ∃ A0 : Subgroup F, Nat.card A0 = 7 ∧ A0.Normal ∧
      ∀ B : Subgroup F, Nat.card B = 7 → B = A0 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 7) (G := F)
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hk_le : k ≤ 1 := by
    have hdiv : 7 ^ k ∣ 21 := by
      rw [← hF, ← hk]
      exact Subgroup.card_subgroup_dvd_card (P : Subgroup F)
    have hle : 7 ^ k ≤ 21 := Nat.le_of_dvd (by norm_num) hdiv
    by_contra h
    have h2 : 2 ≤ k := by omega
    have hpow : 7 ^ 2 ≤ 7 ^ k := by gcongr
    norm_num at hpow
    omega
  have hk_ne : k ≠ 0 := by
    intro hk0
    have hcard : Nat.card (P : Subgroup F) = 1 := by rw [hk, hk0, pow_zero]
    have hidx : (P : Subgroup F).index = 21 := by
      have hcm := Subgroup.card_mul_index (P : Subgroup F)
      rw [hcard, hF] at hcm
      omega
    exact P.not_dvd_index (by rw [hidx]; norm_num)
  have hPcard : Nat.card (P : Subgroup F) = 7 := by
    rw [hk, show k = 1 by omega, pow_one]
  have hPidx : (P : Subgroup F).index = 3 := by
    have hcm := Subgroup.card_mul_index (P : Subgroup F)
    rw [hPcard, hF] at hcm
    omega
  have hn : Nat.card (Sylow 7 F) = 1 := by
    have h1 : Nat.card (Sylow 7 F) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 F
    have h2 : Nat.card (Sylow 7 F) ∣ (P : Subgroup F).index := P.card_dvd_index
    rw [hPidx] at h2
    have hle : Nat.card (Sylow 7 F) ≤ 3 := Nat.le_of_dvd (by norm_num) h2
    have hpos : 0 < Nat.card (Sylow 7 F) := Nat.pos_of_dvd_of_pos h2 (by norm_num)
    unfold Nat.ModEq at h1
    generalize Nat.card (Sylow 7 F) = n at *
    interval_cases n <;> omega
  have : Subsingleton (Sylow 7 F) := (Nat.card_eq_one_iff_unique.1 hn).1
  have hPnorm : (P : Subgroup F).Normal := Sylow.normal_of_subsingleton P
  refine ⟨(P : Subgroup F), hPcard, hPnorm, ?_⟩
  intro B hB
  have hBp : IsPGroup 7 B := IsPGroup.of_card (n := 1) (by rw [hB]; norm_num)
  have hidxB : B.index = 3 := by
    have hcm := Subgroup.card_mul_index B
    rw [hB, hF] at hcm
    omega
  let Q : Sylow 7 F := hBp.toSylow (by rw [hidxB]; norm_num)
  have hQ : Q = P := Subsingleton.elim _ _
  have : (Q : Subgroup F) = (P : Subgroup F) :=
    congrArg (fun S : Sylow 7 F => (S : Subgroup F)) hQ
  exact this

private theorem r876a_invariant_sylow_seven
    {actor N : Type} [Group actor] [Group N] [Finite N]
    (ha3 : IsPGroup 3 actor) (hcop : ¬ 3 ∣ Nat.card N)
    (hom : actor →* MulAut N) :
    ∃ P : Sylow 7 N, ∀ a : actor,
      (P : Subgroup N).map (hom a).toMonoidHom = P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let _ := MulDistribMulAction.compHom N hom
  obtain ⟨P⟩ := Sylow.nonempty (p := 7) (G := N)
  have hnd : ¬ 3 ∣ Nat.card (Sylow 7 N) := fun h =>
    hcop (h.trans (P.card_dvd_index.trans (P : Subgroup N).index_dvd_card))
  obtain ⟨Q, hQ⟩ := ha3.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 7 N) hnd
  refine ⟨Q, fun a => ?_⟩
  have := congrArg (fun R : Sylow 7 N => (R : Subgroup N)) (MulAction.mem_fixedPoints.mp hQ a)
  rwa [Sylow.pointwise_smul_def] at this

private theorem r876a_card_map_eq_card_of_inf_ker_eq_bot
    {C F : Type} [Group C] [Group F] [Finite C]
    (φ : C →* F) {A : Subgroup C} (h : A ⊓ φ.ker = ⊥) :
    Nat.card (A.map φ) = Nat.card A := by
  let φA : ↥A →* ↥(A.map φ) :=
    { toFun := fun x => ⟨φ x.1, Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hsurj : Function.Surjective φA := by
    intro y
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  have hker : φA.ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : x.1 ∈ A ⊓ φ.ker := by
      refine ⟨x.2, ?_⟩
      have h1 : φA x = 1 := hx
      have := congrArg Subtype.val h1
      simpa [φA] using this
    rw [h] at hx'
    exact Subtype.ext (Subgroup.mem_bot.mp hx')
  have hcm := Subgroup.card_ker_mul_card_of_surjective (f := φA) hsurj
  rw [hker, Subgroup.card_bot, one_mul] at hcm
  exact hcm

private theorem r876a_exists_order_seven_of_surjection
    {C F : Type} [Group C] [Group F] [Finite C] [Finite F]
    (φ : C →* F) (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    (hF : Nat.card F = 21) (hFnab : ∃ a b : F, a * b ≠ b * a)
    (Zc : Subgroup C) (hZc : Nat.card Zc = 3) :
    ∃ A : Subgroup C, Nat.card A = 7 ∧
      Zc ≤ Subgroup.normalizer (A : Set C) ∧ ⁅A, Zc⁆ = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨A0, hA0card, hA0norm, hA0uniq⟩ := r876a_order21_unique_seven hF
  have : A0.Normal := hA0norm
  let N : Subgroup C := A0.comap φ
  have : N.Normal := hA0norm.comap φ
  let ψ : ↥N →* ↥A0 :=
    { toFun := fun x => ⟨φ x.1, Subgroup.mem_comap.mp x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hψsurj : Function.Surjective ψ := by
    intro a
    have harange : a.1 ∈ φ.range := by
      rw [MonoidHom.range_eq_top_of_surjective φ hφ]; trivial
    obtain ⟨c, hc⟩ := harange
    refine ⟨⟨c, ?_⟩, ?_⟩
    · show φ c ∈ A0
      rw [hc]; exact a.2
    · ext; exact hc
  have hψker : ψ.ker = (φ.ker).subgroupOf N := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have := congrArg Subtype.val hx
      simpa [ψ] using this
    · intro hx
      ext
      simpa [ψ] using hx
  have hker_le : φ.ker ≤ N := by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker.mp hx]; exact A0.one_mem
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  have hNcard : Nat.card ↥N = 7 * 2 ^ k := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψsurj
    rw [hψker] at h
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv, hk, hA0card] at h
    omega
  have hZcN : Zc ≤ Subgroup.normalizer (N : Set C) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hZc3 : IsPGroup 3 Zc := IsPGroup.of_card (n := 1) (by rw [hZc]; norm_num)
  let hom : Zc →* MulAut ↥N :=
    (Subgroup.normalizerMonoidHom N).comp (Subgroup.inclusion hZcN)
  have hhom : ∀ (z : Zc) (x : ↥N), (((hom z) x : ↥N) : C) = (z : C) * (x : C) * (z : C)⁻¹ :=
    fun z x => rfl
  have hNcop : ¬ 3 ∣ Nat.card ↥N := by
    rw [hNcard, Nat.prime_three.dvd_mul]
    rintro (h | h)
    · norm_num at h
    · exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  obtain ⟨P, hP⟩ := r876a_invariant_sylow_seven hZc3 hNcop hom
  have hPcard : Nat.card ↥(P : Subgroup ↥N) = 7 := by
    obtain ⟨j, hj⟩ := P.isPGroup'.exists_card_eq
    have hj0 : j ≠ 0 := by
      intro hj0
      have hPbot : Nat.card ↥(P : Subgroup ↥N) = 1 := by rw [hj, hj0, pow_zero]
      have hidx : (P : Subgroup ↥N).index = 7 * 2 ^ k := by
        have hcm := Subgroup.card_mul_index (P : Subgroup ↥N)
        rw [hPbot, hNcard] at hcm
        omega
      exact P.not_dvd_index (by rw [hidx]; norm_num)
    have hj_le : j ≤ 1 := by
      have hdvd : 7 ^ j ∣ 7 * 2 ^ k := by
        rw [← hj, ← hNcard]
        exact Subgroup.card_subgroup_dvd_card (P : Subgroup ↥N)
      have h72 : Nat.Coprime (7 ^ j) (2 ^ k) := (by norm_num : Nat.Coprime 7 2).pow _ _
      have h7 : 7 ^ j ∣ 7 := h72.dvd_of_dvd_mul_right hdvd
      have hle : 7 ^ j ≤ 7 := Nat.le_of_dvd (by norm_num) h7
      have hpow : 7 ≤ 7 ^ j := by
        calc 7 = 7 ^ 1 := by rw [pow_one]
          _ ≤ 7 ^ j := by gcongr; omega
      have hjeq : 7 ^ j = 7 := le_antisymm hle hpow
      have : j = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 7) (hjeq.trans (pow_one 7).symm)
      omega
    rw [hj, show j = 1 by omega, pow_one]
  let A : Subgroup C := (P : Subgroup ↥N).map N.subtype
  have hAcard : Nat.card A = 7 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hPcard
  have hA_le_N : A ≤ N := by
    rintro a ha
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp ha
    exact x.2
  have hAnormZ : Zc ≤ Subgroup.normalizer (A : Set C) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    have hmem : (hom ⟨z, hz⟩) x ∈ (P : Subgroup ↥N) := by
      rw [← hP ⟨z, hz⟩]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hmemA : ((hom ⟨z, hz⟩) x : C) ∈ A :=
      Subgroup.mem_map.mpr ⟨(hom ⟨z, hz⟩) x, hmem, rfl⟩
    exact hmemA
  have hcomm_eq : ⁅A, Zc⁆ = A := by
    have hAleA : ⁅A, Zc⁆ ≤ A := by
      have h := Subgroup.le_normalizer_iff_commutator_le_right.mp hAnormZ
      rwa [Subgroup.commutator_comm] at h
    have hAker : A ⊓ φ.ker = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      exact Nat.eq_one_of_dvd_coprimes
        ((by norm_num : Nat.Coprime 7 2).pow 1 k)
        ((Subgroup.card_dvd_of_le (inf_le_left : A ⊓ φ.ker ≤ A)).trans (by rw [hAcard]))
        ((Subgroup.card_dvd_of_le (inf_le_right : A ⊓ φ.ker ≤ φ.ker)).trans (by rw [hk]))
    have hAimage : A.map φ = A0 := by
      have hle : A.map φ ≤ A0 := by
        rw [Subgroup.map_le_iff_le_comap]
        exact hA_le_N
      have hcard : Nat.card (A.map φ) = Nat.card A0 := by
        rw [r876a_card_map_eq_card_of_inf_ker_eq_bot φ hAker, hAcard, hA0card]
      exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    have hZcker : Zc ⊓ φ.ker = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      exact Nat.eq_one_of_dvd_coprimes
        ((by norm_num : Nat.Coprime 3 2).pow 1 k)
        ((Subgroup.card_dvd_of_le (inf_le_left : Zc ⊓ φ.ker ≤ Zc)).trans (by rw [hZc]))
        ((Subgroup.card_dvd_of_le (inf_le_right : Zc ⊓ φ.ker ≤ φ.ker)).trans (by rw [hk]))
    let B : Subgroup F := Zc.map φ
    have hBcard : Nat.card B = 3 := by
      rw [r876a_card_map_eq_card_of_inf_ker_eq_bot φ hZcker, hZc]
    have hAB : ⁅A0, B⁆ ≠ ⊥ := by
      intro hbot
      have hcent : A0 ≤ Subgroup.centralizer (B : Set F) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      have hA0c : IsMulCommutative ↥A0 := (isCyclic_of_prime_card hA0card).isMulCommutative
      have hBc : IsMulCommutative ↥B := (isCyclic_of_prime_card hBcard).isMulCommutative
      have hcommA0 : ∀ a a' : F, a ∈ A0 → a' ∈ A0 → a * a' = a' * a := fun a a' ha ha' =>
        congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥A0) ⟨a', ha'⟩)
      have hcommB : ∀ b b' : F, b ∈ B → b' ∈ B → b * b' = b' * b := fun b b' hb hb' =>
        congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : ↥B) ⟨b', hb'⟩)
      have htop : A0 ⊔ B = ⊤ := by
        have hdvd7 : 7 ∣ Nat.card ↥(A0 ⊔ B) := by
          have h := Subgroup.card_dvd_of_le (le_sup_left : A0 ≤ A0 ⊔ B)
          rwa [hA0card] at h
        have hdvd3 : 3 ∣ Nat.card ↥(A0 ⊔ B) := by
          have h := Subgroup.card_dvd_of_le (le_sup_right : B ≤ A0 ⊔ B)
          rwa [hBcard] at h
        have hdvd21 : 21 ∣ Nat.card ↥(A0 ⊔ B) := by
          have h := (by norm_num : Nat.Coprime 7 3).mul_dvd_of_dvd_of_dvd hdvd7 hdvd3
          simpa using h
        have hle21 : Nat.card ↥(A0 ⊔ B) ≤ 21 := by
          have h := Subgroup.card_le_card_group (H := A0 ⊔ B)
          rwa [hF] at h
        have hcard : Nat.card ↥(A0 ⊔ B) = 21 :=
          le_antisymm hle21 (Nat.le_of_dvd (by norm_num) hdvd21)
        refine Subgroup.eq_of_le_of_card_ge le_top ?_
        rw [Subgroup.card_top, hF, hcard]
      have hFab : IsMulCommutative F := by
        refine IsMulCommutative.of_comm fun x y => ?_
        have hx : x ∈ A0 ⊔ B := by rw [htop]; trivial
        have hy : y ∈ A0 ⊔ B := by rw [htop]; trivial
        obtain ⟨a1, ha1, b1, hb1, hx1⟩ := Subgroup.mem_sup_of_normal_left.mp hx
        obtain ⟨a2, ha2, b2, hb2, hx2⟩ := Subgroup.mem_sup_of_normal_left.mp hy
        rw [← hx1, ← hx2]
        have h1 : b1 * a2 = a2 * b1 := Subgroup.mem_centralizer_iff.mp (hcent ha2) b1 hb1
        have h2 : b2 * a1 = a1 * b2 := Subgroup.mem_centralizer_iff.mp (hcent ha1) b2 hb2
        have h3 : a1 * a2 = a2 * a1 := hcommA0 a1 a2 ha1 ha2
        have h4 : b1 * b2 = b2 * b1 := hcommB b1 b2 hb1 hb2
        calc (a1 * b1) * (a2 * b2) = a1 * (b1 * a2) * b2 := by group
          _ = a1 * (a2 * b1) * b2 := by rw [h1]
          _ = (a1 * a2) * (b1 * b2) := by group
          _ = (a2 * a1) * (b2 * b1) := by rw [h3, h4]
          _ = a2 * (a1 * b2) * b1 := by group
          _ = a2 * (b2 * a1) * b1 := by rw [h2]
          _ = (a2 * b2) * (a1 * b1) := by group
      obtain ⟨a, b, hab⟩ := hFnab
      exact hab (mul_comm' a b)
    have hmapAB : (⁅A, Zc⁆).map φ = ⁅A0, B⁆ := by
      rw [Subgroup.map_commutator, hAimage]
    have hcomm_ne : ⁅A, Zc⁆ ≠ ⊥ := by
      intro hbot
      have : (⁅A, Zc⁆).map φ = ⊥ := by rw [hbot, Subgroup.map_bot]
      rw [hmapAB] at this
      exact hAB this
    have hcard7 : Nat.card ↥(⁅A, Zc⁆) = 7 := by
      have hdvd : Nat.card ↥(⁅A, Zc⁆) ∣ 7 := by
        have h := Subgroup.card_dvd_of_le hAleA
        rwa [hAcard] at h
      have hne : Nat.card ↥(⁅A, Zc⁆) ≠ 1 := by
        intro h1
        exact hcomm_ne (Subgroup.eq_bot_of_card_eq (H := ⁅A, Zc⁆) h1)
      rcases Nat.prime_seven.eq_one_or_self_of_dvd (Nat.card ↥(⁅A, Zc⁆)) hdvd with h1 | h7
      · exact absurd h1 hne
      · exact h7
    exact Subgroup.eq_of_le_of_card_ge hAleA (by rw [hcard7, hAcard])
  exact ⟨A, hAcard, hAnormZ, hcomm_eq⟩

theorem r876_73a {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg876 M L Z Y g) {y : G} (hy : y ∈ Y) (hy1 : y ≠ 1)
    (hF : Nat.card (barFixed L y) = 21 ∧ ∃ a b : ↥(barFixed L y), a * b ≠ b * a) :
    ∃ A : Subgroup G, A ≤ Subgroup.centralizer (Y : Set G) ⊓ L ∧ Nat.card A = 7 ∧
      Z ≤ Subgroup.normalizer (A : Set G) ∧ ⁅A, Z⁆ = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := c.base.loc.norm (c.base.hYM hy)
  have hYcard : Nat.card Y = 3 := by
    rw [c.base.hY, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      c.base.loc.hZ3]
  have hy3 : orderOf y = 3 := by
    have hy3pow : y ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hy⟩)
      rw [hYcard] at h
      exact congrArg Subtype.val h
    exact orderOf_eq_prime hy3pow hy1
  have hYeq : Subgroup.zpowers y = Y := by
    have hle : Subgroup.zpowers y ≤ Y := Subgroup.zpowers_le.mpr hy
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hy3, hYcard])
  have hcent : Subgroup.centralizer ({y} : Set G) = Subgroup.centralizer (Y : Set G) := by
    rw [← hYeq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hZY : Z ≤ Subgroup.centralizer (Y : Set G) := Subgroup.le_centralizer_iff.mp c.hZY
  have hZcent : Z ≤ Subgroup.centralizer ({y} : Set G) := by rw [hcent]; exact hZY
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Cl : Subgroup ↥L := (Subgroup.centralizer ({y} : Set G)).subgroupOf L
  have hfix : barFixed L y = Cl.map π := r876_fixed_lift hyN hy3
  let φ : ↥Cl →* ↥(barFixed L y) :=
    { toFun := fun x => ⟨π x.1, by rw [hfix]; exact Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
      map_one' := by ext; simp [π]
      map_mul' := by intro a b; ext; simp [π] }
  have hφ : Function.Surjective φ := by
    intro f
    have hf : f.1 ∈ Cl.map π := by rw [← hfix]; exact f.2
    obtain ⟨l, hl, hlf⟩ := Subgroup.mem_map.mp hf
    exact ⟨⟨l, hl⟩, Subtype.ext hlf⟩
  have hker : IsPGroup 2 φ.ker := by
    have hK : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
    have hle : (φ.ker).map Cl.subtype ≤ CFSG.pCore 2 ↥L := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
      have hx1 : π x.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      have : x.1 ∈ π.ker := MonoidHom.mem_ker.mpr hx1
      rwa [show π.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _] at this
    exact (hK.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)).of_equiv
      (Subgroup.equivMapOfInjective φ.ker Cl.subtype Cl.subtype_injective).symm
  have hZL_le_Cl : Z.subgroupOf L ≤ Cl := Subgroup.subgroupOf_mono L hZcent
  let Zc : Subgroup ↥Cl := (Z.subgroupOf L).subgroupOf Cl
  have hZc : Nat.card Zc = 3 := by
    have h1 : Nat.card Zc = Nat.card (Z.subgroupOf L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL_le_Cl).toEquiv
    have h2 : Nat.card (Z.subgroupOf L) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.base.loc.hZL).toEquiv
    rw [h1, h2, c.base.loc.hZ3]
  obtain ⟨A, hAcard, hAnorm, hAcomm⟩ :=
    r876a_exists_order_seven_of_surjection φ hφ hker hF.1 hF.2 Zc hZc
  let ψG : ↥Cl →* G := L.subtype.comp Cl.subtype
  let AG : Subgroup G := A.map ψG
  have hψGinj : Function.Injective ψG := by
    intro a b h
    exact Subtype.ext (Subtype.ext h)
  have hZmap : Zc.map ψG = Z := by
    have h1 : Zc.map Cl.subtype = Z.subgroupOf L := by
      rw [show Zc = (Z.subgroupOf L).subgroupOf Cl from rfl, Subgroup.subgroupOf_map_subtype,
        inf_eq_left]
      exact hZL_le_Cl
    rw [show ψG = L.subtype.comp Cl.subtype from rfl, ← Subgroup.map_map, h1,
      Subgroup.subgroupOf_map_subtype, inf_eq_left]
    exact c.base.loc.hZL
  refine ⟨AG, ?_, ?_, ?_, ?_⟩
  · rintro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hxcent : (x.1 : G) ∈ Subgroup.centralizer ({y} : Set G) :=
        Subgroup.mem_subgroupOf.mp x.2
      show ψG x ∈ Subgroup.centralizer (Y : Set G)
      rw [← hcent]
      exact hxcent
    · show ψG x ∈ L
      exact x.1.2
  · rw [show AG = A.map ψG from rfl,
      Subgroup.card_map_of_injective (K := A) (f := ψG) hψGinj, hAcard]
  · rw [← hZmap, Subgroup.le_normalizer_iff]
    intro z hz a ha
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    have hza : z' * a' * z'⁻¹ ∈ A := Subgroup.le_normalizer_iff.mp hAnorm z' hz' a' ha'
    have hcoe : ψG (z' * a' * z'⁻¹) = ψG z' * ψG a' * (ψG z')⁻¹ := by simp
    rw [← hcoe]
    exact Subgroup.mem_map.mpr ⟨z' * a' * z'⁻¹, hza, rfl⟩
  · rw [show AG = A.map ψG from rfl, ← hZmap, ← Subgroup.map_commutator, hAcomm]


open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem r876b_barAction_eq_conj_mk {G : Type} [Group G] {K : Subgroup G} {y : G}
    (hyK : y ∈ K) :
    barAction K ⟨y, Subgroup.le_normalizer hyK⟩ =
      MulAut.conj (QuotientGroup.mk ⟨y, hyK⟩) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [barAction_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

private theorem r876b_mem_pCoreOf_commutator_of_barAction_eq_one {G : Type} [Group G]
    {K : Subgroup G} {d k : G} (hdN : d ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K)
    (hd : barAction K ⟨d, hdN⟩ = 1) :
    d * k * d⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have hconj : d * k * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hdN k).mp hk
  have hmem : d * k * d⁻¹ * k⁻¹ ∈ K := K.mul_mem hconj (K.inv_mem hk)
  have h1 : (QuotientGroup.mk ⟨d * k * d⁻¹, hconj⟩ : Bar2 K) =
      QuotientGroup.mk ⟨k, hk⟩ := by
    have h := barAction_mk K ⟨d, hdN⟩ ⟨k, hk⟩
    rw [hd] at h
    have h' : ((Subgroup.normalizerMonoidHom K ⟨d, hdN⟩) ⟨k, hk⟩) =
        ⟨d * k * d⁻¹, hconj⟩ := Subtype.ext rfl
    rw [h'] at h
    simpa using h.symm
  have h2 : (QuotientGroup.mk (⟨d * k * d⁻¹ * k⁻¹, hmem⟩ : ↥K) : Bar2 K) = 1 := by
    have h3 : (⟨d * k * d⁻¹ * k⁻¹, hmem⟩ : ↥K) =
        ⟨d * k * d⁻¹, hconj⟩ * ⟨k, hk⟩⁻¹ := Subtype.ext (by simp [mul_assoc])
    rw [h3, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
    simp
  have hmemCore : (⟨d * k * d⁻¹ * k⁻¹, hmem⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
    (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K) _).mp h2
  exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := K)
    ⟨d * k * d⁻¹ * k⁻¹, hmem⟩).mpr hmemCore

private theorem r876b_bar2_conj_equiv {G : Type} [Group G] (g : G) (K : Subgroup G) :
    Nonempty (Bar2 K ≃* Bar2 (K.map (MulAut.conj g).toMonoidHom)) :=
  ⟨QuotientGroup.congr (CFSG.pCore 2 ↥K)
    (CFSG.pCore 2 ↥(K.map (MulAut.conj g).toMonoidHom))
    (MulEquiv.subgroupMap (MulAut.conj g) K)
    (CFSG.pCore_map_iso 2 (MulEquiv.subgroupMap (MulAut.conj g) K))⟩

private theorem r876b_mem_inner_of_isPGroup_seven {X : Type} [Group X] [Finite X]
    {φ : MulAut X} (hφ : IsPGroup 7 (Subgroup.zpowers φ))
    (hOut : ¬ 7 ∣ Nat.card (Outer X)) : φ ∈ inner X := by
  let ψ : Outer X := QuotientGroup.mk' (inner X) φ
  have hψP : IsPGroup 7 (Subgroup.zpowers ψ) := by
    have h := hφ.map (QuotientGroup.mk' (inner X))
    rwa [MonoidHom.map_zpowers] at h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hψ1 : ψ = 1 := by
    by_contra hψ
    have hψsub : (⟨ψ, Subgroup.mem_zpowers ψ⟩ : Subgroup.zpowers ψ) ≠ 1 := by
      simpa using hψ
    have h7dvd : 7 ∣ orderOf ψ := by
      have h := hψP.dvd_orderOf hψsub
      simpa using h
    exact hOut (h7dvd.trans (orderOf_dvd_natCard ψ))
  exact (QuotientGroup.eq_one_iff (N := inner X) φ).mp (by simpa [ψ] using hψ1)

private theorem r876b_center_eq_bot_of_lieModel {B : Type} [Group B] [Finite B]
    (hL : CFSG.Blueprint.LieModel B .PSL 3 2 2) : Subgroup.center B = ⊥ := by
  have hs : IsSimpleGroup B :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  have hcard : Nat.card B = 20160 := CFSG.Blueprint.LieModel.card_psl_three_four hL
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center B) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative B := Subgroup.center_eq_top_iff.mp h
    have hp := (Group.is_simple_iff_prime_card (α := B)).mp hs
    rw [hcard] at hp
    norm_num at hp

private theorem r876b_conj_eq_conj_iff {B : Type} [Group B]
    (hcenter : Subgroup.center B = ⊥) {x y : B} :
    MulAut.conj x = MulAut.conj y ↔ x = y := by
  constructor
  · intro h
    have h1 : ∀ g : B, x * g * x⁻¹ = y * g * y⁻¹ :=
      fun g => congrArg (fun f : MulAut B => f g) h
    have hd : y⁻¹ * x ∈ Subgroup.center B := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := h1 g
      calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹ * x) := by group
        _ = y⁻¹ * (x * g * x⁻¹ * x) := by rw [← hg]
        _ = y⁻¹ * (x * g) := by group
        _ = (y⁻¹ * x) * g := by group
    rw [hcenter, Subgroup.mem_bot] at hd
    exact (eq_of_inv_mul_eq_one hd).symm
  · intro h
    rw [h]

theorem r876_73b {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg876 M L Z Y g) {A : Subgroup G} (hA : A ≤ Subgroup.centralizer (Y : Set G) ⊓ L)
    (hA7 : Nat.card A = 7) :
    ⁅A, L.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≤
      pCoreOf 2 (L.map (MulAut.conj g⁻¹).toMonoidHom) := by
  let Lg : Subgroup G := L.map (MulAut.conj g⁻¹).toMonoidHom
  have hshape : CFSG.Blueprint.LieModel (Bar2 Lg) .PSL 3 2 2 := by
    obtain ⟨eBar⟩ := r876b_bar2_conj_equiv g⁻¹ L
    exact CFSG.Blueprint.LieModel.of_mulEquiv eBar
      (show CFSG.Blueprint.LieModel (Bar2 L) .PSL 3 2 2 from c.base.loc.shape)
  have hcardOut : Nat.card (Outer (Bar2 Lg)) = 12 := card_outer_psl_three_four hshape
  have h7Out : ¬ 7 ∣ Nat.card (Outer (Bar2 Lg)) := by rw [hcardOut]; norm_num
  have hcenter : Subgroup.center (Bar2 Lg) = ⊥ := r876b_center_eq_bot_of_lieModel hshape
  have hYle : Y ≤ Lg := by
    rw [c.base.hY]
    exact Subgroup.map_mono c.base.loc.hZL
  have hY3 : Nat.card Y = 3 := by
    rw [c.base.hY, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact c.base.loc.hZ3
  have hnormY : Subgroup.normalizer (Y : Set G) ≤ M.map (MulAut.conj g⁻¹).toMonoidHom := by
    have h1 : Subgroup.normalizer (Y : Set G) =
        (Subgroup.normalizer (Z : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [c.base.hY]
      exact (Subgroup.map_normalizer_eq_of_bijective Z (MulAut.conj g⁻¹).bijective).symm
    rw [h1]
    exact Subgroup.map_mono c.base.loc.hZN
  have hnormL : M.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.normalizer (Lg : Set G) := by
    have h1 : (Subgroup.normalizer (L : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
        Subgroup.normalizer (Lg : Set G) :=
      Subgroup.map_normalizer_eq_of_bijective L (MulAut.conj g⁻¹).bijective
    rw [← h1]
    exact Subgroup.map_mono c.base.loc.norm
  have hAN : A ≤ Subgroup.normalizer (Lg : Set G) :=
    hA.trans (inf_le_left.trans <|
      (Subgroup.centralizer_le_normalizer (Y : Set G)).trans (hnormY.trans hnormL))
  have hYnontriv : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨y, hyY⟩, hy1'⟩ := exists_ne (1 : ↥Y)
  have hy1 : y ≠ 1 := fun h => hy1' (Subtype.ext h)
  have hyLg : y ∈ Lg := hYle hyY
  have hy3 : y ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hyY⟩)
    rw [hY3] at h
    exact congrArg Subtype.val h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyN : y ∈ Subgroup.normalizer (Lg : Set G) := Subgroup.le_normalizer hyLg
  let yb : Bar2 Lg := QuotientGroup.mk (⟨y, hyLg⟩ : ↥Lg)
  have hNcard : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥Lg) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := CFSG.pCore 2 ↥Lg)).mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥Lg))
    rw [hn]
    intro h
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hybord : orderOf yb = 3 := by
    have hyLgOrd : orderOf (⟨y, hyLg⟩ : ↥Lg) = 3 := by
      rw [Subgroup.orderOf_mk]; exact hyord
    have h := CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime (G := ↥Lg)
      (N := CFSG.pCore 2 ↥Lg) hNcard hyLgOrd
    simpa [yb] using h
  have htriv : ∀ a ∈ A, barConjAut (L := Lg) a = 1 := by
    intro a ha
    have haN : a ∈ Subgroup.normalizer (Lg : Set G) := hAN ha
    have ha7 : a ^ 7 = 1 := by
      have h := pow_card_eq_one' (G := ↥A) (x := ⟨a, ha⟩)
      rw [hA7] at h
      exact congrArg Subtype.val h
    have hP : IsPGroup 7 (Subgroup.zpowers (barConjAut (L := Lg) a)) := by
      let Nn : Subgroup G := Subgroup.normalizer (Lg : Set G)
      let n : ↥Nn := ⟨a, haN⟩
      have hmap : (Subgroup.zpowers n).map Nn.subtype = Subgroup.zpowers a := by
        rw [MonoidHom.map_zpowers]; rfl
      have hx7 : IsPGroup 7 (Subgroup.zpowers a) :=
        IsPGroup.of_card_dvd_pow (n := 1) (by
          rw [Nat.card_zpowers, pow_one]
          exact orderOf_dvd_iff_pow_eq_one.mpr ha7)
      have hn7 : IsPGroup 7 (Subgroup.zpowers n) := by
        have h : IsPGroup 7 ((Subgroup.zpowers n).map Nn.subtype) := by rwa [hmap]
        exact h.of_equiv (Subgroup.equivMapOfInjective (Subgroup.zpowers n) Nn.subtype
          Subtype.coe_injective).symm
      have hbar : barConjAut (L := Lg) a = barAction Lg n := barConjAut_of_mem haN
      rw [hbar, ← MonoidHom.map_zpowers (barAction Lg) n]
      exact hn7.map (barAction Lg)
    have hmem : barConjAut (L := Lg) a ∈ inner (Bar2 Lg) :=
      r876b_mem_inner_of_isPGroup_seven hP h7Out
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range] at hmem
    obtain ⟨ā, hā⟩ := hmem
    have hay : a * y = y * a :=
      (Subgroup.mem_centralizer_iff.mp (hA ha).1 y hyY).symm
    have hnmy : (⟨a, haN⟩ : ↥(Subgroup.normalizer (Lg : Set G))) * ⟨y, hyN⟩ =
        ⟨y, hyN⟩ * ⟨a, haN⟩ := Subtype.ext hay
    have hcomm : barConjAut (L := Lg) a * barConjAut (L := Lg) y =
        barConjAut (L := Lg) y * barConjAut (L := Lg) a := by
      rw [barConjAut_of_mem haN, barConjAut_of_mem hyN, ← map_mul, ← map_mul, hnmy]
    have hbarY : barConjAut (L := Lg) y = MulAut.conj yb := by
      rw [barConjAut_of_mem hyN]
      exact r876b_barAction_eq_conj_mk hyLg
    have hZY : ā * yb = yb * ā := by
      have h2 : MulAut.conj ā * MulAut.conj yb = MulAut.conj yb * MulAut.conj ā := by
        rw [hā, ← hbarY]
        exact hcomm
      exact (r876b_conj_eq_conj_iff hcenter).mp (by simpa only [map_mul] using h2)
    have hāC : ā ∈ Subgroup.centralizer ({yb} : Set (Bar2 Lg)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hZY
    have hā9 : orderOf ā ∣ 9 := by
      have h9 := card_centralizer_of_orderOf_three_psl_three_four hshape hybord
      rw [← h9]
      exact (Subgroup.centralizer ({yb} : Set (Bar2 Lg))).orderOf_dvd_natCard hāC
    have hbar7 : (barConjAut (L := Lg) a) ^ 7 = 1 := by
      have hn7 : (⟨a, haN⟩ : ↥(Subgroup.normalizer (Lg : Set G))) ^ 7 = 1 := Subtype.ext ha7
      rw [barConjAut_of_mem haN, ← map_pow, hn7, map_one]
    have hā7pow : ā ^ 7 = 1 := by
      have hpow : MulAut.conj (ā ^ 7) = 1 := by rw [map_pow, hā, hbar7]
      exact (r876b_conj_eq_conj_iff hcenter (x := ā ^ 7) (y := 1)).mp
        (by rw [map_one]; exact hpow)
    have hā7 : orderOf ā ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hā7pow
    have hā1 : ā = 1 := by
      have hdvd : orderOf ā ∣ 1 := by
        have h := Nat.dvd_gcd hā7 hā9
        rwa [show Nat.gcd 7 9 = 1 by norm_num] at h
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    rw [← hā, hā1, map_one]
  rw [Subgroup.commutator_le]
  intro a ha l hl
  have hd : barAction Lg ⟨a, hAN ha⟩ = 1 := by
    rw [← barConjAut_of_mem (L := Lg) (hAN ha)]
    exact htriv a ha
  have hmem := r876b_mem_pCoreOf_commutator_of_barAction_eq_one (K := Lg) (hAN ha) hl hd
  simpa only [commutatorElement_def] using hmem

private def r876c_fixedSub {K A : Type} [Group K] [Group A] (α : A →* MulAut K) : Subgroup K where
  carrier := {c | ∀ a : A, α a c = c}
  mul_mem' := by
    intro x y hx hy a
    rw [map_mul, hx a, hy a]
  one_mem' := by
    intro a
    rw [map_one]
  inv_mem' := by
    intro x hx a
    rw [map_inv, hx a]

private theorem r876c_mem_fixedSub {K A : Type} [Group K] [Group A] (α : A →* MulAut K)
    {c : K} : c ∈ r876c_fixedSub α ↔ ∀ a : A, α a c = c :=
  Iff.rfl

private theorem r876c_mem_pCore_iff {G : Type} [Group G] {L : Subgroup G} {x : ↥L} :
    x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 L := by
  rw [CFSG.Open.pCoreOf]
  exact (Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm

private theorem r876c_barConjAut_eq_one {G : Type} [Group G] {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ y ∈ L, ⁅x, y⁆ ∈ CFSG.Open.pCoreOf 2 L) :
    barConjAut (L := L) x = 1 := by
  rw [barConjAut_of_mem (L := L) hx]
  apply MulEquiv.ext
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  show barAction L ⟨x, hx⟩ (QuotientGroup.mk y) = QuotientGroup.mk y
  rw [barAction_mk, QuotientGroup.eq_iff_div_mem, r876c_mem_pCore_iff]
  simpa [Subgroup.coe_div, Subgroup.normalizerMonoidHom_apply_apply_coe, div_eq_mul_inv,
    commutatorElement_def] using h y y.2

private theorem r876c_fixedSub_card_dvd {K A : Type} [Group K] [Group A] [Finite K] [Finite A]
    (N : Subgroup K) [N.Normal] (p : ℕ) [Fact p.Prime] (hA : IsPGroup p A)
    (α : A →* MulAut K) (hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N)
    (hcop : ¬ p ∣ Nat.card N)
    (htriv : ∀ a : A, ∀ q : K ⧸ N,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hN a q = q) :
    Nat.card (K ⧸ N) ∣ Nat.card (r876c_fixedSub α) := by
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting p hA α N hN hcop
  let f : r876c_fixedSub α →* K ⧸ N := (QuotientGroup.mk' N).comp (r876c_fixedSub α).subtype
  have hf : Function.Surjective f := by
    intro q
    have hq : q ∈ (QuotientGroup.mk' N) '' {c : K | ∀ a : A, α a c = c} := by
      rw [← hlift]
      exact fun a => htriv a q
    obtain ⟨c, hc, hcq⟩ := hq
    exact ⟨⟨c, hc⟩, hcq⟩
  exact Subgroup.card_dvd_of_surjective (f := f) hf

private theorem r876c_exists_card_nine {K A : Type} [Group K] [Group A] [Finite K] [Finite A]
    (N : Subgroup K) [N.Normal] (hN2 : IsPGroup 2 N) (hA : IsPGroup 7 A) (α : A →* MulAut K)
    (hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N) (hcard : Nat.card (K ⧸ N) = 20160)
    (htriv : ∀ a : A, ∀ q : K ⧸ N,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hN a q = q) :
    ∃ E : Subgroup K, Nat.card E = 9 ∧ E ≤ r876c_fixedSub α := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hcop : ¬ 7 ∣ Nat.card N := by
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    rw [hn]
    intro h7
    have : 7 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_seven h7
    norm_num at this
  have hdvd := r876c_fixedSub_card_dvd N 7 hA α hN hcop htriv
  rw [hcard] at hdvd
  have h9 : 3 ^ 2 ∣ Nat.card (r876c_fixedSub α) := (by norm_num : 3 ^ 2 ∣ 20160).trans hdvd
  obtain ⟨E, hEcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := r876c_fixedSub α) 3 (n := 2) h9
  refine ⟨E.map (r876c_fixedSub α).subtype, ?_, Subgroup.map_subtype_le E⟩
  rw [Subgroup.card_map_of_injective (r876c_fixedSub α).subtype_injective, hEcard]
  norm_num

private theorem r876c_final_contradiction {G : Type} [Group G] [Finite G]
    {M Mg : Subgroup G} {g : G} {E : Subgroup G}
    (hMg : Mg = M.map (MulAut.conj g⁻¹).toMonoidHom)
    (hmax : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hEM : E ≤ M) (hEunique : E ∈ uniqueSet Mg) :
    g ∈ M := by
  have hMMg : Mg.map (MulAut.conj g).toMonoidHom = M := by
    rw [hMg, Subgroup.map_map]
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  have hEMg : E ≤ Mg.map (MulAut.conj g).toMonoidHom := by
    rw [hMMg]
    exact hEM
  have hXeq : Mg.map (MulAut.conj g).toMonoidHom = Mg := hEunique.2 g hEMg
  have hMeqMg : M = Mg := hMMg.symm.trans hXeq
  have hMeq : M.map (MulAut.conj g⁻¹).toMonoidHom = M := hMg.symm.trans hMeqMg.symm
  have hginv : g⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMeq
  have hg_norm : g ∈ Subgroup.normalizer (M : Set G) := by
    simpa using Subgroup.inv_mem _ hginv
  simpa [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing M hmax]
    using hg_norm

theorem r876_73c {G : Type} [Group G] [Finite G] {M L Z Y : Subgroup G} {g : G}
    (c : Cfg876 M L Z Y g) {A : Subgroup G} (hA : A ≤ Subgroup.centralizer (Y : Set G))
    (hA7 : Nat.card A = 7)
    (hAL : ⁅A, L.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≤
      pCoreOf 2 (L.map (MulAut.conj g⁻¹).toMonoidHom)) :
    ¬ Subgroup.normalizer (A : Set G) ≤ M := by
  intro hNM
  let Lg : Subgroup G := L.map (MulAut.conj g⁻¹).toMonoidHom
  let Mg : Subgroup G := M.map (MulAut.conj g⁻¹).toMonoidHom
  have c' : Cfg876 Mg Lg Y Z g⁻¹ := r876_cfg_symm c
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    hA.trans (Subgroup.centralizer_le_normalizer (Y : Set G))
  have hAMg : A ≤ Mg := hAY.trans c'.base.loc.hZN
  have hAnorm : A ≤ Subgroup.normalizer (Lg : Set G) := hAMg.trans c'.base.loc.norm
  let α : ↥A →* MulAut ↥Lg :=
    (Subgroup.normalizerMonoidHom Lg).comp (Subgroup.inclusion hAnorm)
  have hN : ∀ a : ↥A, ∀ n ∈ CFSG.pCore 2 ↥Lg, α a n ∈ CFSG.pCore 2 ↥Lg := by
    intro a n hn
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (CFSG.pCore_characteristic (p := 2) (G := ↥Lg)) (α a)
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ((α a).toMonoidHom) hn
  have hAct : ∀ a : ↥A, barConjAut (L := Lg) (a : G) = 1 := by
    intro a
    exact r876c_barConjAut_eq_one (hAnorm a.2)
      (fun y hy => hAL (Subgroup.commutator_mem_commutator a.2 hy))
  have htriv : ∀ a : ↥A, ∀ q : ↥Lg ⧸ CFSG.pCore 2 ↥Lg,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (CFSG.pCore 2 ↥Lg) hN a q =
        q := by
    intro a q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    have h2 : barAction Lg (Subgroup.inclusion hAnorm a) = 1 := by
      have hAB : barAction Lg (Subgroup.inclusion hAnorm a) =
          barConjAut (L := Lg) (a : G) := by
        rw [barConjAut_of_mem (L := Lg) (hAnorm a.2)]
        rfl
      rw [hAB, hAct a]
    have h3 : barAction Lg (Subgroup.inclusion hAnorm a) (QuotientGroup.mk y) =
        QuotientGroup.mk y := by
      rw [h2]
      rfl
    rw [barAction_mk] at h3
    exact h3
  have hcard : Nat.card (↥Lg ⧸ CFSG.pCore 2 ↥Lg) = 20160 :=
    CFSG.Blueprint.LieModel.card_psl_three_four c'.base.loc.shape
  have hA7pg : IsPGroup 7 ↥A := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA7)
  obtain ⟨E', hE'card, hE'le⟩ := r876c_exists_card_nine (CFSG.pCore 2 ↥Lg)
    (CFSG.pCore_isPGroup (p := 2) (G := ↥Lg)) hA7pg α hN hcard htriv
  let E : Subgroup G := E'.map Lg.subtype
  have hEcard : Nat.card E = 9 := by
    rw [Subgroup.card_map_of_injective Lg.subtype_injective, hE'card]
  have hE_le_Lg : E ≤ Lg := Subgroup.map_subtype_le E'
  have hE_cent : E ≤ Subgroup.centralizer (A : Set G) := by
    rintro x ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hfix : ∀ b : ↥A, α b c = c := (r876c_mem_fixedSub α).mp (hE'le hc)
    have hcoe : ((α ⟨a, ha⟩ c : ↥Lg) : G) = (c : G) := congrArg Subtype.val (hfix ⟨a, ha⟩)
    have hconj : a * (c : G) * a⁻¹ = (c : G) := by
      have h := hcoe
      change (((Subgroup.normalizerMonoidHom Lg) (Subgroup.inclusion hAnorm ⟨a, ha⟩)) c : G) =
        (c : G) at h
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      simpa [Subgroup.coe_inclusion] using h
    calc a * (c : G) = (a * (c : G) * a⁻¹) * a := by group
      _ = (c : G) * a := by rw [hconj]
  have hEunique : E ∈ uniqueSet Mg := c'.base.loc.sylowU E hE_le_Lg hEcard
  have hEM : E ≤ M := hE_cent.trans ((Subgroup.centralizer_le_normalizer (A : Set G)).trans hNM)
  exact c.base.hg (r876c_final_contradiction (M := M) (Mg := Mg) (g := g) (E := E) rfl
    c.base.loc.maxLocal hEM hEunique)

private theorem r876_exists_of_not_mem_uniqueSet {G : Type} [Group G] [Finite G]
    {M Z : Subgroup G} (hZM : Z ≤ M) (h : Z ∉ uniqueSet M) :
    ∃ g : G, g ∉ M ∧ Z.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
  by_contra hcon
  refine h ⟨hZM, fun g hg => ?_⟩
  by_cases hgM : g ∈ M
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgM)
  · refine absurd ⟨g, hgM, ?_⟩ hcon
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨m, hm, hmz⟩ := Subgroup.mem_map.mp (hg hz)
    have : (MulAut.conj g⁻¹).toMonoidHom z = m := by
      rw [← hmz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hm

theorem r876_mem_uniqueSet {G : Type} [Group G] [Finite G] {D : Data G} (hK : K762)
    (hS7 : S7_876 D) (hSg : UC6S846.SigmaStd D) (h3 : 3 ∉ D.sig) {L Z : Subgroup G}
    (hloc : Loc876 D.M L Z) : Z ∈ uniqueSet D.M := by
  by_contra hZ
  obtain ⟨g, hg, hYM⟩ :=
    r876_exists_of_not_mem_uniqueSet (hloc.hZL.trans hloc.le) hZ
  set Y : Subgroup G := Z.map (MulAut.conj g⁻¹).toMonoidHom with hYdef
  have c0 : Cfg0876 D.M L Z Y g := ⟨hloc, hg, rfl, hYM⟩
  have hYcard : Nat.card Y = 3 := by
    rw [hYdef, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hloc.hZ3
  have : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨y, hyY⟩, hy1'⟩ := exists_ne (1 : ↥Y)
  have hy1 : y ≠ 1 := fun h => hy1' (Subtype.ext h)
  have hy3 : y ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hyY⟩)
    rw [hYcard] at h
    exact congrArg Subtype.val h
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hloc.norm (hYM hyY)
  have hout := r876_out c0 hyY hy1
  have hα3 : (barConjAut (L := L) y) ^ 3 = 1 := by
    rw [barConjAut_of_mem hyN, ← map_pow]
    have h1 : (⟨y, hyN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext hy3
    rw [h1, map_one]
  have hα1 : barConjAut (L := L) y ≠ 1 := fun h =>
    hout (by rw [h]; exact Subgroup.one_mem _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hαord : orderOf (barConjAut (L := L) y) = 3 := orderOf_eq_prime hα3 hα1
  have hfix := hK (Bar2 L) hloc.shape (barConjAut (L := L) y) hαord hout
  have h3dvd : 3 ∣ Nat.card (barFixed L y) := by
    change 3 ∣ Nat.card ↥(MonoidHom.eqLocus (barConjAut (L := L) y).toMonoidHom
      (MonoidHom.id (Bar2 L)))
    rcases hfix with ⟨⟨e⟩⟩ | ⟨h21, -⟩
    · have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]
        decide
      rw [Nat.card_congr e.toEquiv, h60]
      norm_num
    · rw [h21]
      norm_num
  obtain ⟨Z', g', c⟩ := r876_reduce c0 hyY hy1 h3dvd
  rcases hfix with ⟨⟨e⟩⟩ | hF
  ·
    have hcs := r876_cfg_symm c
    refine r876_a5 c hyY hy1 ⟨e⟩ ?_
    intro z hz hz1
    exact r876_out hcs.base hz hz1
  ·
    obtain ⟨A, hAle, hA7, hAZ, hAcomm⟩ := r876_73a c hyY hy1 hF
    have hAL := r876_73b c hAle hA7
    have hAconf : AConf876 L Z' Y g' A := ⟨hAle, hA7, hAZ, hAcomm, hAL⟩
    have hN := hS7 hSg h3 L Z' Y A g' c hAconf
    exact r876_73c c (hAle.trans inf_le_left) hA7 hAL hN

theorem r876_of_inputs {G : Type} [Group G] [Finite G] (D : Data G) (h63 : UC6.R6_3 D)
    (hSg : UC6S846.SigmaStd D) (h870 : R870 D) (h873 : R873 D) (h874 : R874 D)
    (hQN : R875QNorm D) (hK : K762) (hS7 : S7_876 D) : R876 D := by
  intro L X H hmin hX Q hQ hQX
  have hNorm := r876_norm hSg h870 h873 hmin hX hQX
  have hShape := r876_shape h873 hmin hX
  have hSyl := r876_sylowU h63 h873 h874 hmin hX hQ hQX
  have hLM : L ≤ D.M := by
    rcases hmin.hyp.1 with hL | ⟨hLM, -, -⟩
    · exact hL.1.le
    · exact hLM
  have hXL : X ≤ L := hmin.hyp.2.1
  have hQp : IsPGroup 3 Q := hQ.isPGroup
  have hQnorm : Q ≤ Subgroup.normalizer (X : Set G) := hQN L X H hmin Q hQ hQX
  have hPn : ((Q ⊓ X).subgroupOf Q).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    obtain ⟨hhQ, hhX⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hk hhQ) (inv_mem hk), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hQnorm hk) h).mp hhX
  have hX2 : 2 ≤ CFSG.Open.pRank 3 X := r873M3_of_r873 h873 L X H hmin
  obtain ⟨Z, hZP, hZc, hZ3⟩ := exists_card_three_le_inf_center_of_normal hQp inf_le_left hPn
    (r876_ne_bot hQX hX2)
  have hZrank : 1 ≤ CFSG.Open.pRank 3 Z := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Z]
    exact CFSG.one_le_pRank_of_dvd_card Nat.prime_three (by simp [hZ3])
  have hZN : Subgroup.normalizer (Z : Set G) ≤ D.M :=
    (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 3 (Q ⊓ X) Z hZP hZrank).trans
      (h874 L X H hmin Q hQ hQX).2
  have hloc : Loc876 D.M L Z :=
    ⟨D.maxLocal, hLM, hNorm, hShape, (hZP.trans inf_le_right).trans hXL, hZ3, hZN, hSyl⟩
  have h3 : 3 ∉ D.sig := by
    intro h3sig
    have hns := r876_not_solvable h873 hmin (hXL.trans hLM)
    exact h870 L X H hmin 3 Nat.prime_three (by norm_num) (by omega)
      (UC6S846.sp_of_mem_sig hSg hns h3sig)
  have hZU : Z ∈ uniqueSet D.M := r876_mem_uniqueSet hK hS7 hSg h3 hloc
  intro A hA g hg
  exact exists_mem_conj_forall_of_center D.maxLocal hQp (hZP.trans inf_le_left) hZc hZU hA hg

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
