module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.Lemma121Core

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank
  (eq_one_of_mem_center_of_pow_eq_one)

theorem ffs_card_le_nine_of_isPGroup {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥X))
    (hQ : ∀ R : Subgroup (↥X ⧸ Subgroup.center ↥X), IsPGroup 3 R → Nat.card R ≤ 9)
    {R : Subgroup G} (hRX : R ≤ X) (hR : IsPGroup 3 R) : Nat.card R ≤ 9 := by
  have hR' : IsPGroup 3 (R.subgroupOf X) := hR.comap_subtype (K := X)
  let φ : ↥(R.subgroupOf X) →* (↥X ⧸ Subgroup.center ↥X) :=
    (QuotientGroup.mk' (Subgroup.center ↥X)).comp (R.subgroupOf X).subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : ((a : ↥X) : ↥X ⧸ Subgroup.center ↥X) = 1 := ha
    have hmem : (a : ↥X) ∈ Subgroup.center ↥X := (QuotientGroup.eq_one_iff (a : ↥X)).1 ha'
    obtain ⟨k, hk⟩ := hR' a
    have hk' : (a : ↥X) ^ (3 ^ k) = 1 := by
      have h := congrArg Subtype.val hk
      simpa using h
    exact Subtype.ext (eq_one_of_mem_center_of_pow_eq_one Nat.prime_three hZ hmem hk')
  have hP : IsPGroup 3 φ.range :=
    hR'.of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
  have h1 : Nat.card φ.range ≤ 9 := hQ φ.range hP
  have h2 : Nat.card (R.subgroupOf X) = Nat.card φ.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have h3 : Nat.card (R.subgroupOf X) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv
  omega

end CFSG.RankThree.PartTwo.Sec21
