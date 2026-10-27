module

public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.GroupTheory.ABGLocalTools.PStabilityFrattini
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.HallHigman

theorem pSolv3_of_coprime {X : Type} [Group X] [Finite X] (h : Nat.Coprime 3 (Nat.card X)) :
    IsPSolvable 3 X := by
  intro H _ T _ _
  right
  refine Nat.Coprime.coprime_dvd_right ?_ h
  exact (T.index_dvd_card).trans (Subgroup.card_subgroup_dvd_card H)

theorem pSolv3_of_pGroup {X : Type} [Group X] [Finite X] (h : IsPGroup 3 X) :
    IsPSolvable 3 X := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h
  refine CFSG.GroupTheory.FT63ChII.isPSolvable_of_isPiSeparable ?_
  intro H _ T _ _
  left
  intro q hq
  have h1 : q.val ∣ 3 ^ n := hn ▸ hq.trans ((T.index_dvd_card).trans
    (Subgroup.card_subgroup_dvd_card H))
  have := (Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_three).1 (q.2.dvd_of_dvd_pow h1)
  exact this

theorem pSolv3_quotient {X : Type} [Group X] [Finite X] (h : IsPSolvable 3 X) (N : Subgroup X)
    [N.Normal] : IsPSolvable 3 (X ⧸ N) :=
  CFSG.GroupTheory.FT63ChII.isPSolvable_of_isPiSeparable
    ((isPiSeparable_of_isPSolvable Nat.prime_three h).quotient N)

theorem pSolv3_subgroup {X : Type} [Group X] [Finite X] (h : IsPSolvable 3 X) (K : Subgroup X) :
    IsPSolvable 3 K :=
  CFSG.GroupTheory.FT63ChII.isPSolvable_of_isPiSeparable
    ((isPiSeparable_of_isPSolvable Nat.prime_three h).subgroup K)

theorem pSolv3_of_normal {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : IsPSolvable 3 N) (hQ : IsPSolvable 3 (X ⧸ N)) : IsPSolvable 3 X :=
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_normal N hN hQ

theorem three_solv_normal_sup {X : Type} [Group X] [Finite X] (hX : IsPSolvable 3 X)
    {P : Subgroup X} (hP : IsPGroup 3 P) (hP3 : Nat.card P ≤ 3) (hPi : ¬ 3 ∣ P.index) :
    (pPrimeCore 3 X ⊔ P).Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := pPrimeCore 3 X with hO
  haveI : O.Normal := pPrimeCore_normal
  set π := QuotientGroup.mk' O with hπ
  have hbar : IsPSolvable 3 (X ⧸ O) := pSolv3_quotient hX O
  have hO1 : pPrimeCore 3 (X ⧸ O) = ⊥ := pPrimeCore_quotient_eq_bot Nat.prime_three
  have hchar : IsCharacteristicP 3 (X ⧸ O) := isCharacteristicP_of_isPSolvable hbar hO1
  have hPbn : (P.map π).Normal := by
    set R := pCore 3 (X ⧸ O) with hR
    haveI hRn : R.Normal := pCore_normal
    have hRp : IsPGroup 3 R := pCore_isPGroup
    by_cases hRb : R = ⊥
    · have hcen : (⊤ : Subgroup (X ⧸ O)) ≤ ⊥ := by
        have := hchar
        unfold IsCharacteristicP at this
        rw [← hR, hRb] at this
        intro x _
        have hx : x ∈ Subgroup.centralizer ((⊥ : Subgroup (X ⧸ O)) : Set (X ⧸ O)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
          rw [hh]; simp
        exact this hx
      have : P.map π = ⊥ := by
        refine eq_bot_iff.2 fun x hx => ?_
        exact hcen (Subgroup.mem_top x)
      rw [this]; infer_instance
    · have hPbi : ¬ 3 ∣ (P.map π).index := fun hd =>
        hPi (hd.trans (Subgroup.index_map_dvd (H := P) (QuotientGroup.mk'_surjective O)))
      have hPbp : IsPGroup 3 (P.map π) := hP.map π
      let Q : Sylow 3 (X ⧸ O) := hPbp.toSylow hPbi
      have hRQ : R ≤ P.map π := by
        have := hRp.le_sylow_of_normal Q
        rwa [IsPGroup.toSylow_coe] at this
      have hcardR : 3 ≤ Nat.card R := by
        have hnt : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hRb
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hRp
        have hk0 : k ≠ 0 := by
          rintro rfl
          have : Nat.card R = 1 := hk
          exact (Finite.one_lt_card_iff_nontrivial.2 hnt).ne' this
        rw [hk]
        exact Nat.le_self_pow hk0 3
      have hcardP : Nat.card (P.map π) ≤ 3 :=
        (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (H := P) π)).trans hP3
      have hReq : R = P.map π := by
        refine Subgroup.eq_of_le_of_card_ge hRQ ?_
        omega
      rw [← hReq]; exact hRn
  have : O ⊔ P = (P.map π).comap π := by
    rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk', sup_comm]
  rw [this]
  exact hPbn.comap π

theorem three_solv_decomp {G : Type} [Group G] [Finite G] {J P : Subgroup G}
    (hJ : IsPSolvable 3 ↥J) (hP : IsSylowOf 3 P J) (hP3 : Nat.card P = 3) :
    ∀ x ∈ J, ∃ o ∈ Opp 3 J, ∃ n ∈ J ⊓ Nor P, x = o * n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP'p : IsPGroup 3 (P.subgroupOf J) := hP.2.1.comap_subtype
  have hPi : ¬ 3 ∣ (P.subgroupOf J).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hP.2.2
  have hcard : Nat.card (P.subgroupOf J) ≤ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv, hP3]
  have hn := three_solv_normal_sup hJ hP'p hcard hPi
  have h := CFSG.ABGLocalTools.pPrimeCore_sup_normalizer_eq_top hP'p hn
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥J) ∈ pPrimeCore 3 ↥J ⊔ Subgroup.normalizer ((P.subgroupOf J : Subgroup ↥J) : Set ↥J) := by
    rw [h]; exact Subgroup.mem_top _
  obtain ⟨o, ho, n, hn', hon⟩ := Subgroup.mem_sup_of_normal_left.1 hx'
  refine ⟨(o : G), Subgroup.mem_map.2 ⟨o, ho, rfl⟩, (n : G), Subgroup.mem_inf.2 ⟨n.2, ?_⟩, ?_⟩
  · have hn'' := Subgroup.mem_normalizer_iff.1 hn'
    show (n : G) ∈ Nor P
    rw [Nor, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact (hn'' ⟨z, hP.1 hz⟩).1 hz
    · intro hz
      have hzJ : z ∈ J := by
        have h1 : (n : G) * z * (n : G)⁻¹ ∈ J := hP.1 hz
        have : z = (n : G)⁻¹ * ((n : G) * z * (n : G)⁻¹) * n := by group
        rw [this]
        exact J.mul_mem (J.mul_mem (J.inv_mem n.2) h1) n.2
      exact (hn'' ⟨z, hzJ⟩).2 hz
  · exact (congrArg Subtype.val hon).symm

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
