module

import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec4.Statements417

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Blueprint

@[expose] def IsType419 (K : Type) [Group K] : Prop :=
  (∃ n : ℕ, ChevalleyExceptionalModel K .G2 2 n) ∨ Nonempty (K ≃* projSU 3 3 1) ∨
    (∃ n : ℕ, ReeTitsModel K .twistedF4 2 n) ∨ ReeTitsModel K .Tits 2 1 ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (K ≃* projSp 2 (GaloisField 2 n))) ∨
    Nonempty (K ≃* alternatingGroup (Fin 6))

namespace Res419Two

theorem pCore_two_eq_bot {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G)
    {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) (h81 : Nat.card A = 3 ^ 4) :
    CFSG.pCore 2 G = ⊥ := by
  by_contra hne
  have hloc : CFSG.Assembly.IsTwoLocal (⊤ : Subgroup G) := by
    have : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal
    exact ⟨CFSG.pCore 2 G, hne, CFSG.pCore_isPGroup, (Subgroup.normalizer_eq_top _).symm⟩
  have h4 : 4 ≤ CFSG.Assembly.pRank 3 (⊤ : Subgroup G) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three ⊤)
      ⟨A, le_top, hA, h81⟩
  have h1 := CFSG.RankThree.Classical.pRank_le_localRank (by norm_num : 1 < 3) hloc
  have h2 := CFSG.RankThree.OddKernel.localRank_le_evenRank (G := G) Nat.prime_three
    (by norm_num)
  have h3 := hG.evenRank_le
  omega

theorem quad_le_four {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hF : ∀ A₀ ∈ partTwoF G, Nat.card A₀ ≤ 3 ^ 4) (A E : Subgroup G) (c : G) (m : ℕ)
    (h : IsQuad417 L A E c m) : m ≤ 4 := by
  obtain ⟨hA, hcard, -, -, hE, hEA, T, hT, hTE⟩ := h
  have hT2 : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT.2.1
  have hTne : T ≠ ⊥ := by
    rintro rfl
    exact hTE bot_le
  have hEmem : E ∈ partTwoE G := ⟨hE.1, hE.2, T, hTne, hT2, hT.2.2⟩
  have hAmem : A ∈ partTwoF G :=
    ⟨hA.prop, fun B hB hAB => le_antisymm (hA.2 hB hAB) hAB, E, hEmem, hEA⟩
  have hle := hF A hAmem
  rw [hcard] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

theorem exists_ne_comm_of_isComponent {G : Type} [Group G] {K M : Subgroup G}
    (h : IsComponent (K.subgroupOf M)) : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x := by
  obtain ⟨⟨-, -, a, b, hab⟩, -⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨((x : M) : G), Subgroup.mem_subgroupOf.mp x.2, ((y : M) : G),
    Subgroup.mem_subgroupOf.mp y.2, fun hxy => hab ?_⟩
  have hxy' : x * y = y * x := Subtype.ext (Subtype.ext hxy)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy']

theorem mem_normalizer_of_le {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsComponent L) {a : G} {K : Subgroup G}
    (hK : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G)) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (hxy : x * y ≠ y * x) : a ∈ Subgroup.normalizer (L : Set G) := by
  set L' : Subgroup G := L.map (MulAut.conj a).toMonoidHom with hL'
  have hL'c : IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv _ hL
  rcases CFSG.LocalCores.distinct_components_commute hL hL'c with heq | hcomm
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hmem : a * h * a⁻¹ ∈ L' := ⟨h, hh, rfl⟩
      rwa [← heq] at hmem
    · intro hh
      rw [heq] at hh
      obtain ⟨k, hk, hk'⟩ := hh
      have hkh : k = h := by
        have hk'' : a * k * a⁻¹ = a * h * a⁻¹ := hk'
        exact mul_left_cancel (mul_right_cancel hk'')
      rwa [← hkh]
  · exfalso
    have hxL' : x ∈ L' := by
      refine ⟨x, (hK hx).1, ?_⟩
      have hc : a * x = x * a := (Subgroup.mem_centralizer_singleton_iff.mp (hK hx).2).symm
      change a * x * a⁻¹ = x
      rw [hc, mul_inv_cancel_right]
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact hxy (Subgroup.mem_centralizer_iff.mp (hle (hK hy).1) x hxL')

theorem two_pow_dvd_pow {k n j : ℕ} (h : k ≤ n * j) : 2 ^ k ∣ (2 ^ n) ^ j := by
  rw [← pow_mul]
  exact pow_dvd_pow 2 h

theorem card_cases
    {K : Type} [Group K]
    (h : IsType419 K) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* projSU 3 3 1) ∨
      (2 ^ 8 ∣ Nat.card K ∧ (2 ^ 10 ∣ Nat.card K ∨ 17 ∣ Nat.card K)) := by
  rcases h with ⟨n, hG2⟩ | hU | ⟨n, hF4⟩ | hT | ⟨n, hn, ⟨e⟩⟩ | hA
  · right; right
    have hn : 2 ≤ n := by
      obtain ⟨⟨-, -, -, h3⟩, -⟩ := hG2
      by_contra hlt
      interval_cases n <;> simp at h3
    have hc := (CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hG2).1 rfl
    rw [hc, CFSG.Open.ordG2]
    have h10 : 2 ^ 10 ∣ (2 ^ n) ^ 6 := two_pow_dvd_pow (by omega)
    have h10' : 2 ^ 10 ∣ (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) :=
      (h10.mul_right _).mul_right _
    exact ⟨(pow_dvd_pow 2 (by norm_num : 8 ≤ 10)).trans h10', Or.inl h10'⟩
  · exact Or.inr (Or.inl hU)
  · right; right
    have hn : 1 ≤ n := hF4.1.2.1
    rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hF4, CFSG.Open.ordTwistedF4]
    have h10 : 2 ^ 10 ∣ (2 ^ n) ^ 12 := two_pow_dvd_pow (by omega)
    have h10' : 2 ^ 10 ∣ (2 ^ n) ^ 12 * ((2 ^ n) ^ 6 + 1) * ((2 ^ n) ^ 4 - 1) *
        ((2 ^ n) ^ 3 + 1) * (2 ^ n - 1) :=
      ((((h10.mul_right _).mul_right _).mul_right _).mul_right _)
    exact ⟨(pow_dvd_pow 2 (by norm_num : 8 ≤ 10)).trans h10', Or.inl h10'⟩
  · right; right
    rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hT, CFSG.Open.ordTits]
    exact ⟨by norm_num, Or.inl (by norm_num)⟩
  · right; right
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSp_two
      (by omega)]
    have h8 : 2 ^ 8 ∣ 2 ^ (n * 4) := pow_dvd_pow 2 (by omega)
    refine ⟨h8.mul_right _, ?_⟩
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · exact Or.inr (Dvd.dvd.mul_left (Dvd.dvd.mul_left (by norm_num) _) _)
    · exact Or.inl ((pow_dvd_pow 2 (by omega : 10 ≤ n * 4)).mul_right _)
  · exact Or.inl hA

end Res419Two

end CFSG.RankThree.PartTwo.Sec4
