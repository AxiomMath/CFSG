
module

public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses

@[expose] public section

namespace CFSG.Milestones

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.SectionRank

@[expose] def SQTKSimpleList (S : Type) [Group S] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel S .PSL 2 p f) ∨
      StatedClassicalModel S .PSL 3 p 1 ∨ StatedClassicalModel S .PSU 3 p 1)) ∨
  ((∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel S .PSL 2 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel S .PSU 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) ∨
    (2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
    (1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ SuzukiModel S 2 f)) ∨
    ReeTitsModel S .Tits 2 1) ∨
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel S .PSL n 2 1) ∨
  (∃ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) ∧
    Nonempty (S ≃* NativeSporadic.Carrier s))

theorem cl_lit_sqtk_simple_list
    (S : Type) [Group S] [Finite S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (hSQT : IsStronglyQuasithin S) (hcat : Catalog S) :
    SQTKSimpleList S :=
  sqtk_simple_list_of_sporadic sporadicThreeRankWitnesses S hnonab hSQT hcat

theorem cl_lit_sqtk_simple_list_simple
    (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (hSQTK : IsSQTKCat S) : SQTKSimpleList S :=
  cl_lit_sqtk_simple_list S hnonab hSQTK.1
    (catalog_of_isKGroupCat_of_surjective hSQTK.2 ⊤ (⊤ : Subgroup S).subtype fun s =>
      ⟨⟨s, Subgroup.mem_top s⟩, rfl⟩)

end CFSG.Milestones
