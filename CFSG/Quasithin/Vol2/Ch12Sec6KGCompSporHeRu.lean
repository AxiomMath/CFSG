module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSpor
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.HeldB.AutModelCore
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentRu
public import CFSG.RankThree.Asc83Table.He
public import CFSG.RankThree.Asc83Table.Ru

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB CFSG.Sporadic.RuSchreier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem exists_elemAbelian_nine_of_e9Basis {G : Type*} [Group G]
    (E : CFSG.RankThree.Asc83Table.E9Basis G) :
    ∃ A : Subgroup G, IsElemAbelian 3 A ∧ Nat.card A = 9 :=
  ⟨E.sub, isElemAbelian_closure_pair E.ha E.hb E.hab, E.card⟩

theorem noTwoCentralNine_he :
    NoTwoCentralNine ↥heP := by
  refine noTwoCentralNine_of_reps (R := heP) le_rfl card_heP
    [(heGenPerm 0, 161280), (heT1P, 21504)] Prod.fst Prod.snd ?_ ?_ ?_
  · intro t ht h2
    rcases involution_conj_cases ht h2 with ⟨c, hc, htc⟩ | ⟨c, hc, htc⟩
    · exact ⟨_, List.mem_cons_self .., c, hc, htc⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), c, hc, htc⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact card_heP_cent0
    · exact card_heP_cent1
  · intro r hr i hi h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only at hi ⊢ <;> omega

theorem exists_elemAbelian_nine_heP :
    ∃ E : Subgroup ↥heP, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have e : ↥heP ≃* NativeSporadic.He := heEquivP.symm
  exact exists_elemAbelian_nine_of_mulEquiv (M := ↥heP) (M' := NativeSporadic.He) e
    (exists_elemAbelian_nine_of_e9Basis (CFSG.RankThree.Asc83Table.He.E 0))

theorem card_outer_heP :
    Nat.card (Outer ↥heP) = 2 :=
  (heConjR_facts AT_He_Schreier.1).2.2.2

theorem Conf12626.not_he
    {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) (hS : Ch1.SporadicAutInner)
    (e : ↥K ≃* NativeSporadic.Carrier .He) : False :=
  h.false_of_noTwoCentralNine hQ (e.trans heEquivP) heP_center_eq_bot
    (by rw [card_outer_heP]; norm_num) exists_elemAbelian_nine_heP
    noTwoCentralNine_he
    (isInnerAut_of_sporadicAutInner hQ hS (by simp [Ch1.IsSQTKSporadicName]) (by decide) e)

theorem noTwoCentralNine_ru :
    NoTwoCentralNine ↥ruP := by
  refine NoTwoCentralNine.of_cards card_ruP' [245760, 116480] (fun t ht => ?_) (by
    intro c hc i _ _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> omega)
  rw [card_centralizer_subtype_inf]
  rcases Id2519.MathNoLayer.ru_centralizer_card t.2 (by rwa [Subgroup.orderOf_coe]) with h | h <;>
    rw [h] <;> simp

theorem exists_elemAbelian_nine_ruP :
    ∃ E : Subgroup ↥ruP, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have e : ↥ruP ≃* NativeSporadic.Ru := ruEquivP.symm
  exact exists_elemAbelian_nine_of_mulEquiv (M := ↥ruP) (M' := NativeSporadic.Ru) e
    (exists_elemAbelian_nine_of_e9Basis (CFSG.RankThree.Asc83Table.Ru.E 0))

theorem Conf12626.not_ru
    {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q} (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) (hS : Ch1.SporadicAutInner)
    (e : ↥K ≃* NativeSporadic.Carrier .Ru) : False :=
  h.false_of_noTwoCentralNine hQ (e.trans ruEquivP) center_ruP
    (by rw [card_outer_ruP]; norm_num) exists_elemAbelian_nine_ruP noTwoCentralNine_ru
    (isInnerAut_of_sporadicAutInner hQ hS (by simp [Ch1.IsSQTKSporadicName]) (by decide) e)

end CFSG.Quasithin.H13.S126C
