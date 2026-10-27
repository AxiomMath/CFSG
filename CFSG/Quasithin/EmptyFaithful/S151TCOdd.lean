module

public import CFSG.Quasithin.EmptyFaithful.S151TBNorm
public import CFSG.Quasithin.EmptyFaithful.S151TBTyp

public section

namespace CFSG.Quasithin.S151TC

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.S151TB

theorem ker_eq_bot_of_statedSL_three_two {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  refine CFSG.SectionRank.OddCover.ker_eq_bot_of_sylow_conditions π hπ hC hodd (p := 2) (e := 1)
    (fun Cp => ?_) ?_ ?_
  · exact CFSG.SectionRank.OddCover.sylow_eq_bot_of_not_dvd Cp
      (fun h => Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 h))
  · intro r hr hr2 _ _
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r ↥(CFSG.Assembly.LowTwoRank.StatedSL 3
      (ZMod 2))))
    refine ⟨Q, CFSG.SectionRank.OddCover.isCyclic_of_isPGroup_of_le_GL_three ?_ ?_ Q.isPGroup'⟩
    · rw [Nat.card_zmod]
      exact fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).1 h)
    · rw [Nat.card_zmod]
      exact hr.out.not_dvd_one
  · intro r hr _ _ hre
    exact absurd (Nat.dvd_one.1 hre) hr.out.ne_one

theorem nonempty_mulEquiv_statedSL_of_isPSL {K : Type} [Group K] (h : IsPSL 3 2 1 K) :
    Nonempty (K ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h
  exact ⟨e.trans ((CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 F
    (by rw [hcard]; norm_num)).trans (specialLinearGroupEquivStatedSL 3 (ZMod 2)))⟩

theorem lStar_center_eq_bot_of_psl32 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple (LStar L)) (h : IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L))) :
    Subgroup.center (LStar L) = ⊥ := by
  have : Group.IsPerfect (LStar L) := hq.1
  obtain ⟨e⟩ := nonempty_mulEquiv_statedSL_of_isPSL h
  let π : LStar L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (LStar L)))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center (LStar L) := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker]
    exact Typ.odd_card_center_quotient_pCore (K := ↥L)
  exact hker.symm.trans (ker_eq_bot_of_statedSL_three_two π hπ hker.le hodd)

theorem exists_epi_sl3_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple (LStar L)) (h : IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L))) :
    ∃ α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)),
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L := by
  obtain ⟨e⟩ := nonempty_mulEquiv_statedSL_of_isPSL h
  exact exists_epi_of_center_bot (lStar_center_eq_bot_of_psl32 hq h) e

theorem card_lStar_of_psl32 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple (LStar L)) (h : IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L))) :
    Nat.card (LStar L) = 168 := by
  have hcen := lStar_center_eq_bot_of_psl32 hq h
  obtain ⟨e⟩ := nonempty_mulEquiv_statedSL_of_isPSL h
  let e' : (LStar L ⧸ Subgroup.center (LStar L)) ≃* LStar L :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  rw [← Nat.card_congr e'.toEquiv, Nat.card_congr e.toEquiv,
    CFSG.SectionRank.OddCover.card_statedSL_three, Nat.card_zmod]
  norm_num

end CFSG.Quasithin.S151TC
