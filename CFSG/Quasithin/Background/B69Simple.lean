module

public import CFSG.Quasithin.Background.B69Num
public import CFSG.LieType.Ree.SuzukiSimple

public section

namespace CFSG.Quasithin

namespace B69

namespace E22Fam

variable {F : Type} [Group F]

theorem isSimpleGroup (h : E22Fam F) : IsSimpleGroup F := by
  rcases h with ⟨p, e, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨p, hp, h⟩ | ⟨p, hp, h⟩
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity F 2 p e h).2
  · obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ := h
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    exact (MulEquiv.isSimpleGroup_congr e).mpr (CFSG.LieType.Ree.suzuki_simple ha hK').2.2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity F 3 2 n h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity F 3 2 n h).2
  · unfold E2.IsSp4Prime at h
    split_ifs at h with h1
    · obtain ⟨e⟩ := h
      exact (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
    · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp F 2 2 n h
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity F 3 p 1 h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity F 3 p 1 h).2

theorem congr {F' : Type} [Group F'] (e : F ≃* F') (h : E22Fam F) : E22Fam F' := by
  have hm : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ},
      CFSG.Assembly.LowTwoRank.StatedClassicalModel F t n p f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel F' t n p f := by
    intro t n p f hF
    obtain ⟨hadm, hF⟩ := hF
    refine ⟨hadm, ?_⟩
    cases t with
    | PSL | PSU | PSp | POmegaOdd | POmegaPlus =>
      obtain ⟨K, x, hfin, hK, ⟨e'⟩⟩ := hF
      exact ⟨K, x, hfin, hK, ⟨e.symm.trans e'⟩⟩
    | POmegaMinus =>
      obtain ⟨K, x, hfin, hK, b, c, hbc, ⟨e'⟩⟩ := hF
      exact ⟨K, x, hfin, hK, b, c, hbc, ⟨e.symm.trans e'⟩⟩
    | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
      exact hF.elim
  have hsz : ∀ {n : ℕ}, IsSz n F → IsSz n F' := by
    intro n hF
    obtain ⟨h2, a, ha, K, x, hfin, hfa, hK, ⟨e'⟩⟩ := hF
    exact ⟨h2, a, ha, K, x, hfin, hfa, hK, ⟨e.symm.trans e'⟩⟩
  have halt : ∀ {n : ℕ}, IsAlt n F → IsAlt n F' := fun ⟨e'⟩ => ⟨e.symm.trans e'⟩
  have hsp : ∀ {n : ℕ}, E2.IsSp4Prime n F → E2.IsSp4Prime n F' := by
    intro n hF
    unfold E2.IsSp4Prime at hF ⊢
    split_ifs at hF ⊢
    · exact halt hF
    · exact hm hF
  rcases h with ⟨p, e₁, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨p, hp, h⟩ | ⟨p, hp, h⟩
  · exact Or.inl ⟨p, e₁, hm h⟩
  · exact Or.inr (Or.inl ⟨n, hsz h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hm h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, hm h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, hsp h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hm h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hm h⟩)))))

end E22Fam

end B69

end CFSG.Quasithin
