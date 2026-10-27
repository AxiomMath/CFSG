module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5e
public import CFSG.Quasithin.Vol2.Ch10SecKHA5g
public import CFSG.Quasithin.Vol2.Ch10SecKHA5h
public import CFSG.Quasithin.Vol2.Ch10SecKHA5j
public import CFSG.Quasithin.Vol2.Ch10SecKHA5l
public import CFSG.Quasithin.Vol2.Ch10SecKHA5m
public import CFSG.Quasithin.Vol2.Ch10SecKHA5n

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.QuasithinUnique.A5.G3

theorem rank2NoSL25 : Rank2NoSL25 := by
  intro G _ _ L P hrk hP
  rcases hrk with ⟨f, ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hodd, hf, hm⟩⟩ | hT
  · exact not_isSL25_perfectCore_l3 L P f hf (Or.inl hm) hP
  · exact not_isSL25_perfectCore_l3 L P f hf (Or.inr hm) hP
  · exact not_isSL25_perfectCore_sp4 L P f hf hm hP
  · exact not_isSL25_perfectCore_g2 L P f hf hm hP
  · exact not_isSL25_perfectCore_d4 L P f hf hm hP
  · exact not_isSL25_perfectCore_f4 L P f hodd hf hm hP
  · exact not_isSL25_perfectCore_tits L P hT hP

theorem noSL25_of_sqtkSimpleList
    (hM : A314ModelFacts) (hR2 : Rank2NoSL25)
    (hJ4 : ∀ (X : Type) [Group X] [Finite X], IsSporadic .J4 X → NoSL25Norm X)
    {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (h : CFSG.Milestones.SQTKSimpleList X) : NoSL25In X := by
  have ofA : A312L.A312For X → NoSL25In X := fun hA => noSL25In_of_a312Case hM hR2 hJ4 hA
  rcases h with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨p, hp, hp2, ⟨f, hf, hm⟩ | hm | hm⟩ |
      (⟨f, ⟨h2, hm⟩ | ⟨h1, hm⟩ | ⟨h2, hm⟩ | ⟨h2, hm⟩ | ⟨h2, hm⟩ | ⟨h1, hm⟩ | ⟨ho, h3, hm⟩ |
        ⟨ho, h3, hm⟩⟩ | hT) | ⟨n, hn, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  · obtain rfl | rfl | rfl | rfl : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    · exact ofA (A312L.l2even X 2 hq le_rfl
        (CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five X ⟨e⟩))
    · exact ofA (A312L.alt6 X hq ⟨e⟩)
    · exact ofA (A312L.alt7 X hq ⟨e⟩)
    · exact ofA (A312L.l4 X hq
        (CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_four_two_of_alternating_eight X ⟨e⟩))
  · rcases hf with rfl | rfl
    · exact ofA (A312L.l2p X p hq hp hp2 hm)
    · exact ofA (A312L.l2psq X p hq hp hp2 hm)
  · exact noSL25In_l3odd hp hp2 hm
  · exact noSL25In_u3odd hp hp2 hm
  · exact ofA (A312L.l2even X f hq h2 hm)
  · exact ofA (A312L.l3even X f hq h1 hm)
  · exact ofA (A312L.u3even X f hq h2 hm)
  · exact ofA (A312L.sp4 X f hq h2 hm)
  · exact ofA (A312L.g2 X f hq h2 hm)
  · exact ofA (A312L.d4 X f hq h1 hm)
  · exact ofA (A312L.f4 X f hq ho h3 hm)
  · exact ofA (A312L.sz X f hq ho h3 hm)
  · exact ofA (A312L.tits X hq hT)
  · obtain rfl | rfl := hn
    · exact ofA (A312L.l4 X hq hm)
    · exact ofA (A312L.l5 X hq hm)
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ofA (A312L.m11 X hq ⟨e⟩)
    · exact ofA (A312L.m12 X hq ⟨e⟩)
    · exact (noSL25Norm_m22 ⟨e⟩).noSL25In
    · exact (noSL25Norm_m23 ⟨e⟩).noSL25In
    · exact noSL25In_m24 ⟨e⟩
    · exact noSL25In_j1 ⟨e⟩
    · exact noSL25In_j2 ⟨e⟩
    · exact (hJ4 X ⟨e⟩).noSL25In
    · exact noSL25In_hs ⟨e⟩
    · exact noSL25In_he ⟨e⟩
    · exact noSL25In_ru ⟨e⟩

theorem noSL25_of_coverList
    (hM : A314ModelFacts) (hR2 : Rank2NoSL25)
    (hJ4 : ∀ (X : Type) [Group X] [Finite X], IsSporadic .J4 X → NoSL25Norm X)
    {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X) (h : A36Case2List X) :
    NoSL25In X := by
  have ofA : A312L.A312For X → NoSL25In X := fun hA => noSL25In_of_a312Case hM hR2 hJ4 hA
  rcases h with ⟨s, p, e, hp, he, ⟨rfl, hmod⟩ | ⟨hp2, rfl⟩, hX⟩ | h6 | h7 | h22
  · exact ofA (A312L.famSl3even_of_minus A312L.sl3evenMinus X s e hq he hmod hX)
  · rw [pow_one] at hX
    exact noSL25In_sl3odd hp hp2 hX
  · exact ofA (A312L.hat6 X hq h6)
  · exact noSL25In_hat7 h7
  · exact (noSL25Norm_hat_m22 h22).noSL25In

theorem noSL25_quasisimple
    (hT : ThreeCoverFactCat) (hM : A314ModelFacts) (hR2 : Rank2NoSL25)
    (hJ4 : ∀ (X : Type) [Group X] [Finite X], IsSporadic .J4 X → NoSL25Norm X)
    (X : Type) [Group X] [Finite X] (hq : CFSG.IsQuasisimple X) (hS : IsSQTKCat X)
    (hO : CFSG.pCore 2 X = ⊥) : NoSL25In X := by
  have hodd : Odd (Nat.card (Subgroup.center X)) := A36A.odd_card_center hO
  have hstep : CatalogStepConclusion X := catalogStepHyp X hq hS hodd
  have hnonab : ∃ a b : X ⧸ Subgroup.center X, a * b ≠ b * a := hq.2.2
  have hlist : CFSG.Milestones.SQTKSimpleList (X ⧸ Subgroup.center X) :=
    CFSG.Milestones.cl_lit_sqtk_simple_list _ hnonab (hstep.2 _ le_rfl)
      (catalog_center_quotient hq hS.2)
  rcases hstep.1 with h1 | h3
  · have hZbot : Subgroup.center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact noSL25_of_sqtkSimpleList hM hR2 hJ4 hq
      (CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv
        (CFSG.QuasithinUnique.Ch1.mulEquivQuotientOfCenterEqBot hZbot) hlist)
  · exact noSL25_of_coverList hM hR2 hJ4 hq (hT X hq h3 hlist)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
