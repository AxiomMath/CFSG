module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Rank

variable {G : Type} [Group G] [Finite G]

theorem six_le_twoLocalRank_of_threeRank {L : Subgroup G} {x : G} {T : Subgroup G} (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hLT : L ≤ Subgroup.centralizer (T : Set G))
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (hxT : x ∈ Subgroup.centralizer (T : Set G))
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) {E : Subgroup L} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 6 ∨ (Nat.card E = 3 ^ 5 ∧ E ⊓ Subgroup.center L = ⊥)) :
    6 ≤ LargeEvenTwoLocalRank 3 G := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hE' : IsElemAbelian 3 (E.map L.subtype) := by
    haveI : IsMulCommutative E := hE.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, hx, hax⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨z, hz, hbz⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← hax, ← hbz, ← map_mul, ← map_mul]
      exact congrArg (fun w : E => ((w : ↥L) : G)) (mul_comm' (⟨x, hx⟩ : E) ⟨z, hz⟩)
    · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      rw [← map_pow, hE.2 x hx, map_one]
  have hE'card : Nat.card (E.map L.subtype) = Nat.card E :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hE'N : E.map L.subtype ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.map_subtype_le E).trans
      (hLT.trans (Subgroup.centralizer_le_normalizer (T : Set G)))
  rcases hcard with h6 | ⟨h5, hZ⟩
  · exact le_twoLocalRank_of_normalizes hp hT hT2 hE' hE'N (by rw [hE'card, h6])
  · have hEL : ∀ e ∈ E.map L.subtype, e ∈ L := fun _ he => Subgroup.map_subtype_le E he
    have hcomm : ∀ e ∈ E.map L.subtype, e * x = x * e := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.1 (hxL (hEL e he))
    have hxE : x ∉ E.map L.subtype := by
      intro hx
      obtain ⟨e, he, hex'⟩ := hx
      have hex : (e : G) = x := hex'
      have hec : e ∈ Subgroup.center L := by
        rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        change (l : G) * (e : G) = (e : G) * l
        rw [hex]
        exact Subgroup.mem_centralizer_singleton_iff.1 (hxL l.2)
      have he1 : e = 1 := by
        have : e ∈ E ⊓ Subgroup.center L := ⟨he, hec⟩
        rw [hZ] at this
        exact Subgroup.mem_bot.1 this
      apply hx1
      rw [← hex, he1]
      rfl
    obtain ⟨hab, hcard'⟩ := isElemAbelian_sup_zpowers_of_card hp hE' (k := 5)
      (by rw [hE'card, h5]) hx3 hxE hcomm
    have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (T : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ hxT
    exact le_twoLocalRank_of_normalizes hp hT hT2 hab (sup_le hE'N hxN) hcard'

end Rank

section ThreeRank

theorem largeEvenLabelAll_twE6_threeRank (h : GGTwE6ThreeRankInput) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twE6) (hs : LargeEvenSplit 3 lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ _ _ => GGTwE6ThreeRank R) := by
  have h3 := three_dvd_of_split_twE6 ht hs
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht h3
  subst ht
  intro Q hQ
  exact recipeTwisted_and (P := LargeEvenSimpleGuard fun R _ _ _ => GGTwE6ThreeRank R)
    (fun K _ _ hK hs' _ => h n hn h3 K hK hs') hQ

theorem exists_threeRank_of_twE6 (hTR : GGTwE6ThreeRankInput) {X : Type} [Group X] [Finite X]
    (hM : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .twE6 ∧ LargeEvenSplit 3 lab)) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧
      (Nat.card E = 3 ^ 6 ∨ (Nat.card E = 3 ^ 5 ∧ E ⊓ Subgroup.center X = ⊥)) := by
  have hM' := largeEvenMarking_and_labelAll_simple_imp
    (S := fun lab => lab.tag = .twE6 ∧ LargeEvenSplit 3 lab)
    (P' := fun R _ _ _ => GGTwE6ThreeRank R)
    (fun lab hlab hS => largeEvenLabelAll_twE6_threeRank hTR hlab hS.1 hS.2) hM
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hM'
  obtain ⟨R, _, I, F, hs, hna, θ, hθ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hS, hrank⟩ := hθ
  exact hrank hS X hXperf θ

end ThreeRank

section Step1

variable {G : Type} [Group G] [Finite G]

theorem ggD4OddCent_twoGroup {B : Subgroup G} {x : G} {L : Subgroup G}
    (hI : GGThmIHyp 3 B x L) (hm : LargeEvenTwoLocalRank 3 G ≤ 5) (hTR : GGTwE6ThreeRankInput)
    (hNL : B ≤ Subgroup.normalizer (L : Set G))
    (hM : LargeEvenMarking ↥L fun lab _ _ _ _ _ => lab.tag = .twE6 ∧ LargeEvenSplit 3 lab) :
    ∃ U : Subgroup (MulAut ↥L), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ a ∈ ggAutsOf L B hNL, ∀ u ∈ U, a * u * a⁻¹ ∈ U := by
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := hst.2.1
  have hT0 : T ≠ ⊥ := by
    intro h
    exact hTB (by rw [h, Subgroup.commutator_bot_left])
  obtain ⟨E, hE, hcard⟩ := exists_threeRank_of_twE6 hTR hM
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
    refine ⟨E.map L.subtype, Subgroup.map_subtype_le E,
      (isPGroup_of_isElemAbelian hE).map L.subtype, ?_⟩
    intro hcyc
    letI : IsCyclic (E.map L.subtype) := hcyc
    obtain ⟨e, he'⟩ := IsCyclic.exists_generator (α := E.map L.subtype)
    have he3 : e ^ 3 = 1 := by
      obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 e.2
      apply Subtype.ext
      change (e : G) ^ 3 = 1
      rw [← hxe, ← map_pow, hE.2 x hx, map_one]
    have hle : orderOf e ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr he3)
    have hcard_eq : orderOf e = Nat.card (E.map L.subtype) :=
      orderOf_eq_card_of_forall_mem_zpowers he'
    rw [hcard_eq] at hle
    rcases hcard with h6 | ⟨h5, -⟩
    · rw [Subgroup.card_map_of_injective L.subtype_injective, h6] at hle
      norm_num at hle
    · rw [Subgroup.card_map_of_injective L.subtype_injective, h5] at hle
      norm_num at hle
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := fun t ht =>
    mem_normalizer_of_sstar hS hnc (hTx ht)
  have hnotLT : ¬ L ≤ Subgroup.centralizer (T : Set G) := by
    intro hLT
    have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
    have hxT : x ∈ Subgroup.centralizer (T : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun t ht =>
        Subgroup.mem_centralizer_singleton_iff.mp (hTx ht)
    have hx1 : x ≠ 1 := hS.2.2.1
    have hx3 : x ^ 3 = 1 := (hS.1.1).2 x hS.2.1
    have h6 := six_le_twoLocalRank_of_threeRank hT0 hT2 hLT hxL hxT hx1 hx3 hE hcard
    omega
  have hU0 : ggAutsOf L T hTL ≠ ⊥ := by
    intro hbot
    apply hnotLT
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hmem : L.normalizerMonoidHom ⟨t, hTL ht⟩ ∈ ggAutsOf L T hTL := by
      rw [mem_ggAutsOf]
      exact ⟨t, ht, rfl⟩
    have h1 : L.normalizerMonoidHom ⟨t, hTL ht⟩ = 1 := by
      rw [hbot] at hmem
      exact Subgroup.mem_bot.1 hmem
    have htC : t ∈ Subgroup.centralizer (L : Set G) :=
      (normalizerMonoidHom_eq_one_iff (hTL ht)).mp h1
    exact (Subgroup.mem_centralizer_iff.mp htC l hl).symm
  have hU2 : IsPGroup 2 (ggAutsOf L T hTL) := by
    let ψ : ↥T →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hTL)
    have hψ : ψ.range = ggAutsOf L T hTL := rfl
    rw [← hψ]
    exact IsPGroup.of_surjective hT2 ψ.rangeRestrict ψ.rangeRestrict_surjective
  refine ⟨ggAutsOf L T hTL, hU0, hU2, ?_⟩
  intro a ha u hu
  obtain ⟨b, hb, rfl⟩ := (mem_ggAutsOf hNL).1 ha
  obtain ⟨t, ht, rfl⟩ := (mem_ggAutsOf hTL).1 hu
  have hbt : b * t * b⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht
  refine (mem_ggAutsOf hTL).2 ⟨b * t * b⁻¹, hbt, ?_⟩
  have harg : (⟨b * t * b⁻¹, hTL hbt⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨b, hNL hb⟩ * ⟨t, hTL ht⟩ * ⟨b, hNL hb⟩⁻¹ := by
    apply Subtype.ext
    rfl
  rw [harg, map_mul, map_mul, map_inv]

end Step1

end CFSG.StandardType
