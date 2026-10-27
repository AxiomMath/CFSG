module

public import CFSG.Quasithin.Vol2.Ch11SecOE3B
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem two_le_pRank {r : ℕ} (hr : r.Prime) {X : Type} [Group X] [Finite X] (h : R2Shape r X) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  obtain ⟨-, -, ⟨E, hE, hEc⟩, -⟩ := h
  exact CFSG.SectionRank.le_pRank hr.one_lt le_top hE hEc

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_r2Shape
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G) {T K : Subgroup G}
    (hloc : quasithinIsLocal T K) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hX : R2Shape r (↥K ⧸ CFSG.pCore 2 ↥K)) : T ≤ Subgroup.normalizer (K : Set G) := by
  have := hs
  obtain ⟨-, hCC, -, hO2⟩ := hloc
  have hLocal : LocalSQTK G := (qtkeCore_of_cat hnab hK).1
  rcases Vol2Native.lemma_1_2_1_three hLocal h37 h38 hO2 hCC with hn | ⟨-, htypes⟩
  · exact le_sup_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn)
  · have h1 := Id2519.lemma122Rank _ htypes r hr (by omega)
    have h2 := two_le_pRank hr hX
    omega

end CFSG.Quasithin.Vol2.Ch11.OE3
