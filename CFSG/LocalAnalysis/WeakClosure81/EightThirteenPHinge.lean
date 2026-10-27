module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def W3Lem813'' (G : Type) [Group G] [Finite G] : Prop :=
  ∀ {V H T A : Subgroup G} {i : ℕ}, MinCex88 V H T i → IsCalH0 V H → A ∈ E3.gammaSet V i T →
    (∃ x ∈ H, ¬ conjSubgroup A x ≤ normalizer (V : Set G)) → Concl812 V H T i A →
      ∃ L K : Subgroup G, Concl813'' V H T A L K

theorem MinCex88.eight_thirteen'' (hc : W3Lem813'' G) {V H T : Subgroup G} {i : ℕ}
    {A : Subgroup G} (h : MinCex88 V H T i) (hH0 : IsCalH0 V H) (hA : A ∈ E3.gammaSet V i T)
    (hAM : ∃ x ∈ H, ¬ conjSubgroup A x ≤ normalizer (V : Set G)) (h812 : Concl812 V H T i A) :
    ∃ L K : Subgroup G, Concl813'' V H T A L K :=
  hc h hH0 hA hAM h812

theorem Concl813''.toConcl813 {V H T A L K : Subgroup G} (h : Concl813'' V H T A L K) :
    Concl813 V H T A L K :=
  ⟨h.comp, h.sub_L, h.ge_C, h.a_le, h.b_not_le, h.c_shape, h.d_index, h.e_shape, h.t_sylow⟩

theorem Sit813.ofP {V H T A L K : Subgroup G} {i : ℕ} (hmin : MinCex88 V H T i)
    (hH0 : IsCalH0 V H) (hA : A ∈ E3.gammaSet V i T)
    (hAM : ∃ x ∈ H, ¬ conjSubgroup A x ≤ normalizer (V : Set G)) (h812 : Concl812 V H T i A)
    (h813 : Concl813'' V H T A L K) : Sit813 V H T i A L K :=
  ⟨hmin, hH0, hA, hAM, h812, h813.toConcl813⟩

end CFSG.LocalAnalysis.WeakClosure81

end
