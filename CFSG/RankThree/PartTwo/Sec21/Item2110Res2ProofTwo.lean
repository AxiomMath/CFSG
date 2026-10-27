module

public import CFSG.RankThree.PartTwo.Sec12.Item124Bar
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofTwelve

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def Item129Bar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12.Sec12StdBar G A c L → A ∈ partTwoE G → A ∉ partTwoS G

@[expose] def Item2110Hyp121 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∃ J ∈ thetaComponentsAt 3 d, d ∈ J ∧ c ∈ Sec4.thetaQuotCentralizer J ∧
        Nat.card (A ⊓ Sec4.thetaQuotCentralizer J : Subgroup G) = 9 ∧
        (A ⊓ Sec4.thetaQuotCentralizer J) ⊔ (A ⊓ J) = A

@[expose] def Item2110JThetaI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      d ∈ iOf218 L d ∧ ∃ J ∈ thetaComponentsAt 3 d,
        J = iOf218 L d ⊔ inSubgroup (aschbacherSolvableCore 3) J

@[expose] def Item2110ThreeUnique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∀ J₁ ∈ thetaComponentsAt 3 d, ∀ J₂ ∈ thetaComponentsAt 3 d, d ∈ J₁ → d ∈ J₂ → J₁ = J₂

@[expose] def Item2110TwoThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      CFSG.GH74.GLS.oPrimeResidualOf 3
          (Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({d} : Set G)) ≤
        Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) →
      ∀ J₁ ∈ thetaComponentsAt 3 d, ∀ J₂ ∈ thetaComponentsAt 3 d, d ∈ J₁ → d ∈ J₂ → J₁ = J₂

namespace Item2110Res2Proof

open Subgroup

variable {G : Type} [Group G]

theorem exists_sylowOf_mem [Finite G] {Y : Subgroup G} {x : G} (hx : x ∈ Y) {k : ℕ}
    (hk : x ^ (3 ^ k) = 1) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P Y ∧ x ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (zpowers (⟨x, hx⟩ : Y)) := by
    have hdvd : Nat.card (zpowers (⟨x, hx⟩ : Y)) ∣ 3 ^ k := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card hj
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  exact ⟨(Q : Subgroup Y).map Y.subtype, ⟨Q, rfl⟩,
    ⟨⟨x, hx⟩, hQ (mem_zpowers _), rfl⟩⟩

theorem commute_of_forall_sylow [Finite G] {Y : Subgroup G} {c : G}
    (h : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P Y →
      c ∈ (center P).map P.subtype)
    {x : G} (hx : x ∈ Y) {k : ℕ} (hk : x ^ (3 ^ k) = 1) : x * c = c * x := by
  obtain ⟨P, hP, hxP⟩ := exists_sylowOf_mem hx hk
  obtain ⟨z, hz, hzc⟩ := mem_map.mp (h P hP)
  have hcomm := congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hxP⟩)
  simp only [coe_mul] at hcomm
  rwa [show ((z : P) : G) = c from hzc] at hcomm

theorem mem_partTwoE_of_pair [Finite G] {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (h27 : Nat.card A = 27) :
    A ∈ partTwoE G ∧ partTwoF G = partTwoE G := by
  obtain ⟨hE, hEA⟩ := hpair.mem_E
  have hEq : E = A := eq_of_le_of_card_ge hEA (by rw [h27, hE.2.1])
  have hAE : A ∈ partTwoE G := hEq ▸ hE
  exact ⟨hAE, (hpair.side hAE).symm⟩

section Two


theorem item2110Two_of (h211 : Item211) (h129 : Item129Bar) (hH : Item2110Hyp121) :
    Item2110Two := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen
  obtain ⟨J, hJ, hdJ, hcJ, hB9, hsup⟩ := hH G A E U c L hpair hL d hdA hd1 hdcen
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hAe := hpair.mem_S.1.1
  have h27 : Nat.card A = 27 := by
    rw [Item2113Proof.card_eq_of_isList218 h211 hpair hL]; norm_num
  obtain ⟨hAE, hFE⟩ := mem_partTwoE_of_pair hpair h27
  have hsyl : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P
      (normalizer (A : Set G) ⊓ normalizer ((zpowers d : Subgroup G) : Set G)) →
      c ∈ (center P).map P.subtype := by
    intro P hP
    by_contra hnot
    refine h129 G A d J
      { toPartTwoStanding := hpair.standing, partTwoF_eq := hFE, isE27 := ⟨hAe, h27⟩,
        mem_A := hdA, ne_one := hd1, mem_thetaComponentsAt := hJ, mem_L := hdJ,
        card_B := hB9, sup_eq := hsup, exists_sylow := ⟨P, hP, fun hle => hnot ?_⟩ }
      hAE hpair.mem_S
    exact hle ⟨hcA, hcJ⟩
  have hle : normalizer (A : Set G) ⊓ centralizer ({d} : Set G) ≤
      normalizer (A : Set G) ⊓ normalizer ((zpowers d : Subgroup G) : Set G) :=
    inf_le_inf_left _ fun x hx => Item2113Res2Proof.mem_normalizer_zpowers (by
      rw [mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
      exact mem_zpowers d)
  rw [CFSG.GH74.GLS.oPrimeResidualOf, CFSG.GH74.GLS.oPrimeResidual, map_le_iff_le_comap,
    closure_le]
  rintro x ⟨k, hk⟩
  have hk' : (x : G) ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hxc := commute_of_forall_sylow hsyl (hle x.2) hk'
  show (x : G) ∈ normalizer ((zpowers c : Subgroup G) : Set G)
  exact Item2113Res2Proof.mem_normalizer_zpowers (by
    rw [hxc, mul_inv_cancel_right]
    exact mem_zpowers c)

end Two

theorem mem_of_jThetaI {L J : Subgroup G} {d : G} (hdI : d ∈ iOf218 L d)
    (hJI : J = iOf218 L d ⊔ inSubgroup (aschbacherSolvableCore 3) J) : d ∈ J := by
  have hIJ : iOf218 L d ≤ J := by
    rw [hJI]
    exact le_sup_left
  exact hIJ hdI

theorem item2110Three_of (hJ : Item2110JThetaI) (hU : Item2110ThreeUnique) : Item2110Three := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen
  obtain ⟨hdI, J, hJd, hJI⟩ := hJ G A E U c L hpair hL d hdA hd1 hdcen
  have hdJ : d ∈ J := mem_of_jThetaI hdI hJI
  exact ⟨J, ⟨hJd, hdJ⟩, fun J' ⟨hJ', hdJ'⟩ =>
    hU G A E U c L hpair hL d hdA hd1 hdcen J' hJ' J hJd hdJ' hdJ⟩

theorem jTheta_of (hJ : Item2110JThetaI) (hU : Item2110ThreeUnique) :
    ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
        ∀ J ∈ thetaComponentsAt 3 d, d ∈ J →
          J = iOf218 L d ⊔ inSubgroup (aschbacherSolvableCore 3) J := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen J hJm hdJ
  obtain ⟨hdI, J₀, hJ₀, hJ₀I⟩ := hJ G A E U c L hpair hL d hdA hd1 hdcen
  rw [hU G A E U c L hpair hL d hdA hd1 hdcen J hJm J₀ hJ₀ hdJ (mem_of_jThetaI hdI hJ₀I)]
  exact hJ₀I

theorem item2110ThreeUnique_of (h2 : Item2110Two) (h23 : Item2110TwoThree) :
    Item2110ThreeUnique := fun G _ _ A E U c L hpair hL d hdA hd1 hdcen =>
  h23 G A E U c L hpair hL d hdA hd1 hdcen (h2 G A E U c L hpair hL d hdA hd1 hdcen)

end Item2110Res2Proof

end CFSG.RankThree.PartTwo.Sec21
