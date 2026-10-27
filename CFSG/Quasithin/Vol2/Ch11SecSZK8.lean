module

public import CFSG.Quasithin.Vol2.Ch11SecSZK6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

namespace TypeData

theorem of_mulEquiv {Y Z : Type} [Group Y] [Group Z] (hD : TypeData Y) (e : Y ≃* Z) :
    TypeData Z where
  card := by
    rw [← Nat.card_congr e.toEquiv]
    exact hD.card
  simple := @MulEquiv.isSimpleGroup _ _ _ _ hD.simple e.symm
  notSL4 := fun ⟨e'⟩ => hD.notSL4 ⟨e.trans e'⟩

theorem nonabelian {Y : Type} [Group Y] [Finite Y] (hD : TypeData Y) :
    ∃ a b : Y, a * b ≠ b * a := by
  have := hD.simple
  by_contra h
  push Not at h
  let _ : CommGroup Y := { ‹Group Y› with mul_comm := h }
  have hp : (Nat.card Y).Prime := IsSimpleGroup.prime_card
  rcases hD.card with hc | hc
  · rw [hc] at hp
    norm_num at hp
  · rw [hc] at hp
    norm_num at hp

theorem isQuasisimple {Y : Type} [Group Y] [Finite Y] (hD : TypeData Y) :
    CFSG.IsQuasisimple Y := by
  have := hD.simple
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hD.nonabelian).1

theorem ne_bot {G : Type} [Group G] {L V : Subgroup G} (hD : TypeData ↥(autOn L V)) :
    autOn L V ≠ ⊥ := by
  intro hb
  have := hD.le_card
  rw [hb, Subgroup.card_bot] at this
  omega

end TypeData

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem fsuL0_eq_self_of_le_normalizer {T L : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : fsuL0 T L = L :=
  le_antisymm (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (hTL ht) l).1 hl)
    (le_conjClosure L T)

omit [Finite G] in
theorem TypeData.not_concl701J4 (hM24 : IsSimpleGroup ↥NativeSporadic.M24)
    (hM24c : Nat.card ↥NativeSporadic.M24 = 2 ^ 10 * 239085) {T L I : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) [IsMulCommutative ↥(fsuV T I)]
    (hD : TypeData ↥(autOn L (fsuV T I))) : ¬ Concl701J4 T L I := by
  rintro ⟨-, -, -, -, ⟨π, hπ⟩, -⟩
  have hM : fsuM T L = Subgroup.normalizer (L : Set G) := by
    rw [fsuM, fsuL0_eq_self_of_le_normalizer hTL]
  have hLB : L ≤ fsuM T L := by
    rw [hM]
    exact Subgroup.le_normalizer
  have hsub : autOn L (fsuV T I) ≤ autOn (fsuM T L) (fsuV T I) :=
    Subgroup.map_mono fun _ hx => hLB hx
  have := autOn_normal_subgroupOf (V := fsuV T I) hM.le
  have hne' : ∃ y : ↥(autOn (fsuM T L) (fsuV T I)), y ≠ 1 := by
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD.ne_bot
    refine ⟨⟨y, hsub hy⟩, fun h1 => hy1 ?_⟩
    have h2 : y = 1 := congrArg Subtype.val h1
    exact Subtype.ext h2
  have hinj := @injective_of_isSimpleGroup _ _ _ _ hM24 π hπ.1 hne'
  have hB : IsSimpleGroup ↥(autOn (fsuM T L) (fsuV T I)) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hM24 (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm
  have hcard : Nat.card ↥(autOn L (fsuV T I)) = 2 ^ 10 * 239085 := by
    rw [eq_of_normal_of_isSimpleGroup hsub hB hD.ne_bot,
      @card_eq_of_simple_quot _ _ _ _ hM24 π hπ.1 hne']
    exact hM24c
  rcases hD.two_part (by decide) hcard with ⟨h, -⟩ | ⟨h, -⟩
  · omega
  · omega

omit [Finite G] in
theorem TypeData.not_concl701Orth {T L I : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) [IsMulCommutative ↥(fsuV T I)]
    (hD : TypeData ↥(autOn L (fsuV T I))) : ¬ Concl701Orth T L I := by
  rintro ⟨m, hm, K, _, _, _, hK, π, hπ⟩
  have e := MulEquiv.subgroupCongr (show autOn (fsuL0 T L) (fsuV T I) = autOn L (fsuV T I) by
    rw [fsuL0_eq_self_of_le_normalizer hTL])
  have hs : IsSimpleGroup ↥(StatedSL 2 K) :=
    isSimpleGroup_statedSL (isSimpleGroup_SL_two hK (by omega))
  have hne : ∃ y : ↥(autOn L (fsuV T I)), y ≠ 1 := by
    obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD.ne_bot
    exact ⟨y, hy⟩
  have hcard := @card_eq_of_simple_quot _ _ _ _ hs (e.toMonoidHom.comp π)
    (e.surjective.comp hπ.1) hne
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv, card_SL_two hK] at hcard
  rcases hD.two_part (odd_oSL2 (by omega)) hcard with ⟨h6, ho⟩ | ⟨h7, -⟩
  · obtain rfl : m = 3 := by omega
    exact absurd ho (by decide)
  · omega

theorem not_concl701Four_of_le_normalizer {T L I : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : ¬ Concl701Four T L I := by
  rintro ⟨hlt, -⟩
  rw [fsuL0_eq_self_of_le_normalizer hTL] at hlt
  exact lt_irrefl L hlt

end CFSG.Quasithin.Vol2.Ch11.SecS
