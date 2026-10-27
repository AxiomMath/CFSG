module

public import CFSG.Quasithin.Vol2.Ch10SecKIa
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.A5N

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem not_isAlt_five_bot {G : Type} [Group G] : ¬ IsAlt 5 ↥(⊥ : Subgroup G) := fun h => by
  have := A314.card_isAlt_five h
  rw [Subgroup.card_bot] at this
  omega

theorem not_isAlt_five_of_charTwo {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (h : CharTwo X) : ¬ IsAlt 5 ↥X := by
  intro hA
  rw [charTwo_iff_internal,
    C10KH.pCore_eq_bot_of_isAlt_five hA] at h
  have hnt : Nontrivial ↥X := (C10KH.isSimpleGroup_of_isAlt_five hA).toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥X)
  refine hx (Subgroup.mem_bot.1 (h (Subgroup.mem_centralizer_iff.2 fun g hg => ?_)))
  rw [Subgroup.mem_bot.1 hg, one_mul, mul_one]

theorem not_isAlt_five_perfectCore_of_charTwo {G : Type} [Group G] [Finite G] {P : Subgroup G}
    (h : CharTwo P) : ¬ IsAlt 5 ↥(perfectCore P) :=
  not_isAlt_five_of_charTwo (CharTwo.of_normal h (perfectCore_le P) (perfectCore_normal P))

theorem not_isAlt_five_of_parabolicFacts {G : Type} [Group G] [Finite G] {P Q : Subgroup G}
    (hF : Vol2Native.L239.Lie.ParabolicFacts P Q) : ¬ IsAlt 5 ↥(perfectCore P) :=
  not_isAlt_five_perfectCore_of_charTwo hF.charTwo

theorem not_isAlt_five_perfectCore_parabolic {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P)
    (hPj : ∀ j, ¬ IsAlt 5 ↥(perfectCore (P j))) {Pa : Subgroup S}
    (hpar : IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    ¬ IsAlt 5 ↥(perfectCore Pa) := by
  intro hD
  rcases A5.G3.perfectCore_parabolic_cases hU hP hpar hne with h | ⟨j, ⟨e⟩⟩
  · rw [h] at hD
    exact not_isAlt_five_bot hD
  · exact hPj j (IsAlt.of_mulEquiv e hD)

theorem not_isAlt_five_perfectCore_of_equiv {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] (e : X ≃* Y) {Pa : Subgroup X}
    (h : ¬ IsAlt 5 ↥(perfectCore (Pa.map e.toMonoidHom))) : ¬ IsAlt 5 ↥(perfectCore Pa) :=
  fun hD => h (IsAlt.of_mulEquiv (((perfectCore Pa).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr (map_perfectCore e.toMonoidHom Pa))) hD)

theorem not_isAlt_five_perfectCore_of_subgroupOf {G : Type} [Group G] [Finite G]
    {L P : Subgroup G} (hP : IsParabolic2 L P) (hne : P ≠ L)
    (h : ∀ Pa : Subgroup ↥L, IsParabolic2 (⊤ : Subgroup ↥L) Pa → Pa ≠ ⊤ →
      ¬ IsAlt 5 ↥(perfectCore Pa)) :
    ¬ IsAlt 5 ↥(perfectCore P) := by
  have hPL : P ≤ L := hP.1
  have hmap : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  have hpar : IsParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
    rw [A312.isParabolic2_top_iff, hmap]
    exact hP
  have hne' : P.subgroupOf L ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map L.subtype) htop
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype] at this
    exact this
  intro hD
  refine h _ hpar hne' ?_
  have hcore : (perfectCore (P.subgroupOf L)).map L.subtype = perfectCore P := by
    rw [map_perfectCore, hmap]
  exact IsAlt.of_mulEquiv (((perfectCore (P.subgroupOf L)).equivMapOfInjective L.subtype
    L.subtype_injective).trans (MulEquiv.subgroupCongr hcore)).symm hD

theorem not_isAlt_five_perfectCore_subgroupOf_of {G : Type} [Group G] [Finite G]
    {C P : Subgroup G} (hPC : P ≤ C) (h : ¬ IsAlt 5 ↥(perfectCore P)) :
    ¬ IsAlt 5 ↥(perfectCore (P.subgroupOf C)) := fun hD => by
  have hcore : (perfectCore (P.subgroupOf C)).map C.subtype = perfectCore P := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPC]
  exact h (IsAlt.of_mulEquiv (((perfectCore (P.subgroupOf C)).equivMapOfInjective C.subtype
    C.subtype_injective).trans (MulEquiv.subgroupCongr hcore)) hD)

end CFSG.Quasithin.Vol2.Ch10.SecF.A5N
