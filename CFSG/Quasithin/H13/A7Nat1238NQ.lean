module

public import CFSG.Quasithin.H13.A7Nat1238NQ22

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem nonQ_core
    (h3214 : Stmt3_2_14) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQ : QuasithinUnique.quasithinIsQTKECat G) {T K₀ Ke : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK₀ : quasithinIsLocal T K₀)
    (hTK₀ : T ≤ normalizer (K₀ : Set G)) (hKe : Ke ∈ lFamily T) (hKeK₀ : Ke ≤ K₀)
    (hq : ¬ CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) (hJ : K₀ = ⁅K₀, thompsonJ T⁆)
    (hZ : ¬ K₀ ≤ centralizer (quasithinOmegaOneCenter T : Set G)) :
    K₀ ≤ (K₀ ⊓ centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ Ke := by
  rcases nonQ_dichotomy h3214 hs hnab hQ hT hK₀ hKe hKeK₀ hq with h | ⟨p, hp, hp5, hp8, hSL⟩
  · exact h.trans (sup_le_sup_right
      (inf_le_inf_left _ (centralizer_le (le_conjClosure _ _))) _)
  · exact (false_of_case22 h3214 hs hnab hQ hT hK₀ hTK₀ hq hJ hZ hp hp5 hp8 hSL).elim

end CFSG.Quasithin.H13.A7
