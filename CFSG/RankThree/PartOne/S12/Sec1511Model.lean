module

public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp projOmegaMinus)

noncomputable def statedProjEquivRefl {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {H : Subgroup (GL ι K)} {P : Subgroup (ProjGenLinGroup ι K)} (hP : projImage H = P) :
    StatedProj H ≃* P :=
  statedProjEquivOfGLEquiv (MulEquiv.refl _) (by ext x; simp) (by ext x; simp) hP

theorem lieModel_projSL {G : Type} [Group G] {f : ℕ} (hf : 1 ≤ f)
    (e : G ≃* projSL 4 (GaloisField 2 f)) : Blueprint.LieModel G .PSL 4 2 f := by
  refine Or.inl ⟨by decide, ?_, ?_⟩
  · exact ⟨Nat.prime_two, hf, by norm_num, by simp, by simp⟩
  · exact ⟨GaloisField 2 f, inferInstance, inferInstance, GaloisField.card 2 f (by omega),
      ⟨e.trans (statedProjEquivRefl (projImage_statedSL_eq_projSL 4 _)).symm⟩⟩

theorem lieModel_projSp {G : Type} [Group G] {f : ℕ} (hf : 1 ≤ f)
    (e : G ≃* projSp 3 (GaloisField 2 f)) : Blueprint.LieModel G .PSp 3 2 f := by
  refine Or.inl ⟨by decide, ?_, ?_⟩
  · exact ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  · exact ⟨GaloisField 2 f, inferInstance, inferInstance, GaloisField.card 2 f (by omega),
      ⟨e.trans (statedProjEquivRefl (projImage_statedSp_eq_projSp 3 _)).symm⟩⟩

theorem lieModel_projOmegaMinus {G : Type} [Group G] {f : ℕ} (hf : 1 ≤ f)
    {b c : GaloisField 2 f} (hbc : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* projOmegaMinus 3 (GaloisField 2 f) b c) : Blueprint.LieModel G .POmegaMinus 4 2 f := by
  refine Or.inl ⟨by decide, ?_, ?_⟩
  · exact ⟨Nat.prime_two, hf, by norm_num⟩
  · exact ⟨GaloisField 2 f, inferInstance, inferInstance, GaloisField.card 2 f (by omega), b, c, hbc,
      ⟨e.trans (statedProjEquivRefl (projImage_statedOmegaMinus_eq_projOmegaMinus 4 _ b c)).symm⟩⟩

theorem lieModel_of_outcome {G : Type} [Group G] {p : ℕ} {E A I : Subgroup G}
    (h : Outcome152One p E A I ∨ Outcome152Two p E A I ∨ Outcome152Three p E A I ∨
      Outcome152Four p E A I) :
    ∃ (t : StatedLieTag) (n f : ℕ), Blueprint.LieModel ↥I t n 2 f ∧
      ((t = .PSL ∧ n = 4) ∨ (t = .PSp ∧ n = 3) ∨ (t = .POmegaMinus ∧ n = 4)) ∧
      (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) := by
  rcases h with ⟨f, hf, hp, ⟨e⟩, -⟩ | ⟨f, hf, hp, ⟨e⟩, -⟩ | ⟨f, hf, hp, ⟨b, c, hbc, ⟨e⟩⟩, -⟩ |
    ⟨f, hf, hp, ⟨b, c, hbc, ⟨e⟩⟩, -⟩
  · exact ⟨.PSL, 4, f, lieModel_projSL hf e, Or.inl ⟨rfl, rfl⟩, Or.inl hp⟩
  · exact ⟨.PSp, 3, f, lieModel_projSp hf e, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inl hp⟩
  · exact ⟨.POmegaMinus, 4, f, lieModel_projOmegaMinus hf hbc e,
      Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inl hp⟩
  · exact ⟨.POmegaMinus, 4, f, lieModel_projOmegaMinus hf hbc e,
      Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inr hp⟩

end CFSG.RankThree.PartOne
