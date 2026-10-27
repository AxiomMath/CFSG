module

public import CFSG.Quasithin.H13.A6Setting134
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Setting134

variable (S : Setting134 G T L V)
include S

theorem not_alt12_2_2 : ¬ Alt12_2_2 G := by
  intro h
  apply S.h13.not_excluded
  rcases h with ⟨t, n, f, hf, -, hadm, hLie⟩ | hU | hM | hM | hM
  · exact Or.inl ⟨t, n, f, hf, hadm, hLie⟩
  · exact Or.inl ⟨.PSU, 5, 2, le_rfl, ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩, hU⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl hM)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hM))))))

theorem normalizer_V_le :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨V, S.irr.2.1, S.isPGroup_V, rfl⟩ : IsTwoLocal (Subgroup.normalizer (V : Set G)))
  have := S.uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
  exact this ▸ hM'le

theorem normalizer_L_le (h1222 : Stmt12_2_2) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  rcases h1222 G T S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow with h | h
  · exact absurd h S.not_alt12_2_2
  · rcases ((h L S.maximal S.h13.faithful S.fsu.quasisimple).2.2 V S.irr).2.2.1 with h' | h'
    · exact h'
    · exact absurd h' S.zv

theorem normalizer_V_le_centralizer_ZV :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.centralizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rcases S.mem_ZV_iff.1 hx with rfl | rfl
  · simp
  · have := S.conj_zV ⟨g, hg⟩
    calc S.zV * g = g * S.zV * g⁻¹ * g := by rw [this]
      _ = g * S.zV := by group

theorem centralizer_ZV_le :
    Subgroup.centralizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have hZ2 : IsPGroup 2 ↥(V ⊓ Subgroup.centralizer (L : Set G)) :=
    S.isPGroup_V.to_le inf_le_left
  have hLTZ : L ⊔ T ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · exact (Subgroup.le_centralizer_iff.mp inf_le_right).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact S.frame.T_le.trans (S.normalizer_V_le_centralizer_ZV.trans
        (Subgroup.centralizer_le_normalizer _))
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨_, S.zv, hZ2, rfl⟩ : IsTwoLocal (Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)))
  have := S.uniqueM.2 M' ⟨hM', hLTZ.trans hM'le⟩
  exact (Subgroup.centralizer_le_normalizer _).trans (this ▸ hM'le)

theorem lemma13_4_2_one (h1222 : Stmt12_2_2) :
    Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G) ∧
      Subgroup.normalizer (V : Set G) =
        Subgroup.centralizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  ⟨le_antisymm (S.normalizer_L_le h1222) S.normalizer_V_le,
    le_antisymm S.normalizer_V_le_centralizer_ZV (S.centralizer_ZV_le.trans
      (S.normalizer_L_le h1222))⟩

theorem ZV_le_ZL :
    V ⊓ Subgroup.centralizer (L : Set G) ≤
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := by
  intro x hx
  rw [Subgroup.mem_inf]
  refine ⟨?_, (Subgroup.mem_inf.1 hx).2⟩
  rcases S.mem_ZV_iff.1 hx with rfl | rfl
  · exact Subgroup.one_mem _
  · rw [mem_quasithinOmegaOneCenter_iff]
    refine ⟨S.V_le_T S.zV_mem_V, ?_, S.zV_sq⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := S.conj_zV ⟨t, S.frame.T_le ht⟩
    calc t * S.zV = t * S.zV * t⁻¹ * t := by group
      _ = S.zV * t := by rw [this]

end Setting134

end CFSG.Quasithin.H13.A6
