module

public import CFSG.Quasithin.EmptyFaithful.S143Top5
public import CFSG.Quasithin.EmptyFaithful.S143KP

public section

namespace CFSG.Quasithin

namespace S143

@[expose] def Lemma14319SixDihedral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl19a T M → IsA6Block (kOf T M A) A →
      (∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X)) ∧
        (Nonempty (↥(dOf T M) ≃* DihedralGroup 4) ↔
          ((kOf T M A).relIndex (Subgroup.normalizer (kOf T M A : Set G)) = 4 ∧
            A < Subgroup.centralizer (A : Set G)))

theorem lemma14319SixRestSeven_of_dihedral (h : Lemma14319SixDihedral) :
    Lemma14319SixRestSeven := by
  intro G _ _ T M g A t c c18 c19a hK
  obtain ⟨h6b, h6c⟩ := h G T M g A t c c18 c19a hK
  exact ⟨h6b, h6c, c.normalizer_Ac_eq_normalizer_kOf c18.b c19a hK⟩

structure Inputs14316Six : Prop where
  h11 : StageLemma14111
  h113 : StageLemma14113
  h15 : Lemma14315
  h19six : Lemma14319SixDihedral
  h20 : Lemma14320
  h22 : Lemma14322

theorem Inputs14316Six.toInputsFive (h : Inputs14316Six) : Inputs14316Five :=
  { h11 := h.h11
    h113 := h.h113
    h15 := h.h15
    h19rest := lemma14319SixRestSeven_of_dihedral h.h19six
    h20 := h.h20
    h22 := h.h22 }

end S143

theorem stageTheorem14316_of_inputs6 (h : S143.Inputs14316Six) : StageTheorem14316 :=
  stageTheorem14316_of_inputs5 h.toInputsFive

end CFSG.Quasithin
