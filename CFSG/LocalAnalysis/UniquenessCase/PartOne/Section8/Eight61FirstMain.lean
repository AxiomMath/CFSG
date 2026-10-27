module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight61FirstBarLift
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight61FirstInner
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight61FirstOuterE9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott (OuterFixedE9 OuterFixesE9)

theorem two_le_pRank_centralizer_inf_of_autFixed
    {G : Type} [Group G] [Finite G] {L X : Subgroup G}
    (hr : CFSG.Open.pRank 3 L = 2)
    (hfix : ∀ φ : MulAut (Bar2 L), φ ^ 3 = 1 → IsPGroup 3 (Subgroup.zpowers φ) →
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 2 →
        2 ≤ CFSG.Open.pRank 3 (CFSG.autFixedSubgroup φ))
    (hXN : X ≤ Subgroup.normalizer (L : Set G)) (hX : Nat.card X = 3) :
    2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L) := by
  classical
  have hnt : Nontrivial X := by
    rw [← Finite.one_lt_card_iff_nontrivial, hX]
    norm_num
  obtain ⟨g, hg1⟩ := exists_ne (1 : X)
  have hgtop : Subgroup.zpowers g = ⊤ := zpowers_eq_top_of_prime_card hX hg1
  set x : G := (g : G) with hxdef
  have hxgen : Subgroup.zpowers x = X := by
    have hmap := congrArg (Subgroup.map X.subtype) hgtop
    simpa [hxdef, MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype] using hmap
  have hxg : x ∈ X := by
    rw [← hxgen]
    exact Subgroup.mem_zpowers x
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hXN hxg
  have hx3pow : x ^ 3 = 1 := by
    have hdvd : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hxg
    rw [hX] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, pow_orderOf_eq_one, one_pow]
  have hx3 : IsPGroup 3 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [hxgen, hX]
    norm_num
  have hφ3 : barConjAut (L := L) x ^ 3 = 1 := by
    rw [barConjAut_of_mem (L := L) hxN, ← map_pow]
    have hsub : (⟨x, hxN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, hx3pow, OneMemClass.coe_one]
    rw [hsub, map_one]
  have hφP : IsPGroup 3 (Subgroup.zpowers (barConjAut (L := L) x)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hφ3
  have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hn]
    exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hquot : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
    CFSG.SectionRank.pRank_quotient_eq (p := 3) (G := ↥L) (CFSG.pCore 2 ↥L) hN
  have hmap : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = CFSG.Open.pRank 3 L := by
    have h := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three
      L.subtype L.subtype_injective (⊤ : Subgroup ↥L)
    rw [← h]
    simp [Subgroup.map_top, Subgroup.range_subtype]
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 2 := by
    rw [hquot, hmap, hr]
  have hmain : 2 ≤ CFSG.Open.pRank 3 (CFSG.autFixedSubgroup (barConjAut (L := L) x)) :=
    hfix _ hφ3 hφP htop
  have hlift := pRank_fixed_bar_le_pRank_centralizer (L := L) (x := x) hxN hx3
  rw [hxgen] at hlift
  exact le_trans hmain hlift

theorem two_le_pRank_centralizer_inf_of_list857
    {G : Type} [Group G] [Finite G]
    {M L X : Subgroup G} (hE9 : OuterFixedE9)
    (hL : L ∈ calC M) (hr : CFSG.Open.pRank 3 L = 2)
    (hlist : List857 (Bar2 L)) (hno1 : ¬ List857Clause1 (Bar2 L))
    (hXN : X ≤ Subgroup.normalizer (L : Set G)) (hX : Nat.card X = 3) :
    2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L) :=
  two_le_pRank_centralizer_inf_of_autFixed hr (fun φ hφ3 hφP htop => by
      by_cases hinner : φ ∈ inner (Bar2 L)
      · obtain ⟨k, hk3, hkconj⟩ :=
          exists_pow_three_eq_one_of_inner_list857 hL hlist hinner hφ3
        have hK : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) := by rw [htop]
        have hconj := two_le_pRank_autFixedSubgroup_conj (K := Bar2 L) hk3 hK
        rwa [hkconj] at hconj
      · have hOut : 3 ∣ Nat.card (Outer (Bar2 L)) := by
          by_contra hOut
          exact hinner (mem_inner_of_isPGroup_three hφP hOut)
        have hE : ExceptionalOuterCapable (Bar2 L) := by
          by_contra hE
          exact (not_three_dvd_card_outer_of_list857 hlist hno1 hE) hOut
        have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ≤ 3 := by rw [htop]; norm_num
        have hOFE9 : OuterFixesE9 (Bar2 L) :=
          outerFixesE9_of_exceptionalOuterCapable hE9 hE hrk
        exact two_le_pRank_autFixedSubgroup_of_outerFixesE9 hOFE9 hφ3 hinner) hXN hX


theorem two_le_pRank_centralizer_inf_of_list857Clause2
    {G : Type} [Group G] [Finite G]
    {M L X : Subgroup G} (hL : L ∈ calC M) (hr : CFSG.Open.pRank 3 L = 2)
    (hcov : List857Clause2 (Bar2 L))
    (hXN : X ≤ Subgroup.normalizer (L : Set G)) (hX : Nat.card X = 3) :
    2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L) :=
  two_le_pRank_centralizer_inf_of_autFixed hr (fun φ hφ3 hφP htop => by
      have hinner : φ ∈ inner (Bar2 L) :=
        mem_inner_of_isPGroup_three hφP (not_three_dvd_card_outer_of_list857Clause2 hcov)
      obtain ⟨k, hk3, hkconj⟩ := exists_pow_three_eq_one_of_inner_list857 hL
        (list857_iff_clauses.mpr (Or.inr (Or.inl hcov))) hinner hφ3
      have hK : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) := by rw [htop]
      have hconj := two_le_pRank_autFixedSubgroup_conj (K := Bar2 L) hk3 hK
      rwa [hkconj] at hconj) hXN hX

theorem h61_of_list857
    {G : Type} [Group G] [Finite G]
    {D : Data G} {L Q P : Subgroup G} (hE9 : OuterFixedE9)
    (hL : L ∈ calC D.M) (hr : CFSG.Open.pRank 3 L = 2)
    (hlist : List857 (Bar2 L)) (hno1 : ¬ List857Clause1 (Bar2 L))
    (_hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L) (_hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (_hQP : Q ≤ P) (hPN : P ≤ Subgroup.normalizer (L : Set G)) :
    ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ Q →
      2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L) := by
  intro X hXP hXcard _
  exact two_le_pRank_centralizer_inf_of_list857 hE9 hL hr hlist hno1
    (hXP.trans hPN) hXcard


theorem h61_of_list857Clause2
    {G : Type} [Group G] [Finite G]
    {D : Data G} {L Q P : Subgroup G}
    (hL : L ∈ calC D.M) (hr : CFSG.Open.pRank 3 L = 2) (hcov : List857Clause2 (Bar2 L))
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) :
    ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ Q →
      2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G) ⊓ L) :=
  fun _ hXP hXcard _ =>
    two_le_pRank_centralizer_inf_of_list857Clause2 hL hr hcov (hXP.trans hPN) hXcard

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
