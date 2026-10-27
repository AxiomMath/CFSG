module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open scoped Pointwise

theorem uc22p20q_tag_cases {t : StatedLieTag} {m n : ℕ} (hn : 2 < n)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t m 2 n) :
    uc22p20oExcl t m n ∨ uc22p20oNoOddMult t m n ∨ (t = .PSL ∧ m = 3) ∨ (t = .PSU ∧ m = 3) := by
  obtain ⟨-, hf, h⟩ := hadm
  cases t with
  | PSL =>
    obtain ⟨h2, -, -⟩ := h
    have : m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m := by omega
    rcases this with rfl | rfl | rfl | h5
    · simp [uc22p20oExcl, uc22p20oNoOddMult, hn]
    · simp
    · simp [uc22p20oExcl, uc22p20oNoOddMult, hn]
    · simp [uc22p20oExcl, hn, h5]
  | PSU =>
    obtain ⟨h3, -⟩ := h
    have : m = 3 ∨ m = 4 ∨ 5 ≤ m := by omega
    rcases this with rfl | rfl | h5
    · simp
    · simp [uc22p20oExcl, uc22p20oNoOddMult, hn]
    · simp [uc22p20oExcl, hn, h5]
  | PSp =>
    obtain ⟨h2, -⟩ := h
    have : m = 2 ∨ m = 3 ∨ 4 ≤ m := by omega
    rcases this with rfl | rfl | h4
    · simp [uc22p20oExcl, uc22p20oNoOddMult, hn]
    · simp [uc22p20oExcl, uc22p20oNoOddMult, hn]
    · simp [uc22p20oExcl, hn, h4]
  | POmegaOdd => exact absurd h.2 (by norm_num)
  | POmegaPlus => simp [uc22p20oExcl, hn]
  | POmegaMinus =>
    have : m = 4 ∨ 5 ≤ m := by omega
    rcases this with rfl | h5
    · simp [uc22p20oExcl, uc22p20oNoOddMult, hn]
    · simp [uc22p20oExcl, hn, h5]
  | G2 => simp [uc22p20oExcl, uc22p20oNoOddMult, hn]
  | F4 => simp [uc22p20oExcl, hn]
  | E6 => simp [uc22p20oExcl, hn]
  | E7 => simp [uc22p20oExcl, hn]
  | E8 => simp [uc22p20oExcl, hn]
  | twistedE6 => simp [uc22p20oExcl, hn]
  | trialityD4 => simp [uc22p20oExcl, uc22p20oNoOddMult, hn]
  | twistedB2 => simp [uc22p20oExcl, uc22p20oNoOddMult, hn]
  | twistedG2 => exact absurd h.2.1 (by norm_num)
  | twistedF4 => simp [uc22p20oExcl, uc22p20oNoOddMult, hn]
  | Tits => omega


theorem uc22p20q_shapeOne_of_noOddMult {X : Type} [Group X] {t : StatedLieTag} {m n : ℕ} (hn : 2 < n)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t m 2 n) (hno : uc22p20oNoOddMult t m n)
    (hM : LieModel X t m 2 n) : uc22p20oShapeOne X := by
  rcases hno with ⟨-, h⟩ | ⟨h2, -⟩ | ⟨h1, -⟩
  · refine Or.inl ⟨n, hn, ?_⟩
    obtain ⟨-, -, hadm'⟩ := hadm
    rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | rfl | rfl | rfl | rfl | ⟨rfl, rfl | rfl⟩ |
        ⟨rfl, rfl⟩
    · simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSL3, IsSU3, IsOmega8m, hM,
        true_or, or_true]
    · simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSL3, IsSU3, IsOmega8m, hM,
        true_or, or_true]
    · simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSL3, IsSU3, IsOmega8m, hM,
        true_or, or_true]
    · obtain ⟨rfl, -⟩ := hadm'
      simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSL3, IsSU3, IsOmega8m, hM,
        true_or, or_true]
    · obtain rfl := hadm'
      simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSL3, IsSU3, IsOmega8m, hM,
        true_or, or_true]
    · obtain ⟨rfl, -⟩ := hadm'
      simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSL3, IsSU3, IsOmega8m, hM,
        true_or, or_true]
    · obtain ⟨rfl, -⟩ := hadm'
      simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSL3, IsSU3, IsOmega8m, hM,
        true_or, or_true]
    · simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSL3, IsSU3, IsOmega8m, hM,
        true_or, or_true]
    · simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSL3, IsSU3, IsOmega8m, hM,
        true_or, or_true]
    · simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSL3, IsSU3, IsOmega8m, hM,
        true_or, or_true]
  · omega
  · omega


theorem uc22p20q_r1_cases (hG : Global22f) {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    (hB : Asc1930ListB (X ⧸ Subgroup.center X)) :
    uc22p20oShapeOne X ∨
      (∃ (t : StatedLieTag) (m n : ℕ), (uc22p20oExcl t m n ∨
        (t = .PSU ∧ m = 5 ∧ n = 2 ∧ Subgroup.center X ≠ ⊥)) ∧
        LieModel (X ⧸ Subgroup.center X) t m 2 n) ∨
      IsAlt (X ⧸ Subgroup.center X) 9 := by
  rcases hB with ⟨t, m, n, hn, hM⟩ | hM | hM | hM | hM | hM | hM
  · have hadm := CFSG.Blueprint.LieModel.admissible hM
    rcases uc22p20q_tag_cases hn hadm with hex | hno | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨t, m, n, Or.inl hex, hM⟩)
    · have hz := hG.center X hq hodd t m n hno hM
      exact Or.inl (uc22p20q_shapeOne_of_noOddMult hn hadm hno
        (uc22p20p_lieModel_of_center_bot hz hM))
    · have hSL : IsSL3 X n := ⟨hq, hM⟩
      refine Or.inl (Or.inl ⟨n, hn, ?_⟩)
      simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSU3, IsOmega8m, hSL, true_or,
        or_true]
    · have hSU : IsSU3 X n := ⟨hq, hM⟩
      refine Or.inl (Or.inl ⟨n, hn, ?_⟩)
      simp only [IsSz, IsL2, IsL3, IsU3, IsU4, IsG2, Is3D4, IsSp4, IsSL3, IsOmega8m, hSU, true_or,
        or_true]
  · have hz := hG.center X hq hodd .trialityD4 0 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hM
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (uc22p20p_lieModel_of_center_bot hz hM))))))
  · have hz := hG.center X hq hodd .trialityD4 0 2 (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩)) hM
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (uc22p20p_lieModel_of_center_bot hz hM))))))
  · have hz := hG.center X hq hodd .PSU 4 2 (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)) hM
    exact Or.inl (Or.inr (Or.inl (uc22p20p_lieModel_of_center_bot hz hM)))
  · by_cases hz : Subgroup.center X = ⊥
    · exact Or.inl (Or.inr (Or.inr (Or.inl (uc22p20p_lieModel_of_center_bot hz hM))))
    · exact Or.inr (Or.inl ⟨.PSU, 5, 2, Or.inr ⟨rfl, rfl, rfl, hz⟩, hM⟩)
  · have hz := hG.center X hq hodd .POmegaMinus 4 2
      (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)) hM
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (uc22p20p_lieModel_of_center_bot hz hM)))))
  · exact Or.inr (Or.inr hM)


theorem uc22p20q_r2_cases (hG : Global22f) {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    (hB : Asc1930ListB (X ⧸ Subgroup.center X)) :
    (∃ n : ℕ, 2 < n ∧ (IsSz X n ∨ IsL2 X n) ∧ Subgroup.center X = ⊥) ∨
      IsU3 (X ⧸ Subgroup.center X) 3 ∨
      (∃ (t : StatedLieTag) (m n : ℕ), uc22p20oTwo t m n ∧ ¬ (t = .PSU ∧ m = 3 ∧ n = 3) ∧
        LieModel (X ⧸ Subgroup.center X) t m 2 n) ∨
      (∃ (t : StatedLieTag) (m n : ℕ), uc22p20oExcl t m n ∧
        LieModel (X ⧸ Subgroup.center X) t m 2 n) ∨
      IsAlt (X ⧸ Subgroup.center X) 9 := by
  rcases hB with ⟨t, m, n, hn, hM⟩ | hM | hM | hM | hM | hM | hM
  · have hadm := CFSG.Blueprint.LieModel.admissible hM
    rcases uc22p20q_tag_cases hn hadm with hex | hno | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, m, n, hex, hM⟩)))
    · have hz := hG.center X hq hodd t m n hno hM
      have hMX := uc22p20p_lieModel_of_center_bot hz hM
      obtain ⟨-, -, hadm'⟩ := hadm
      rcases hno with ⟨-, h⟩ | ⟨h2, -⟩ | ⟨h1, -⟩
      · rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | rfl | rfl | rfl | rfl | ⟨rfl, rfl | rfl⟩ |
          ⟨rfl, rfl⟩
        · exact Or.inl ⟨n, hn, Or.inr hMX, hz⟩
        · exact Or.inr (Or.inr (Or.inl ⟨.PSL, 4, n, Or.inl ⟨hn, Or.inl ⟨rfl, Or.inr rfl⟩⟩,
            by simp, hM⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨.PSU, 4, n, Or.inl ⟨hn, Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)⟩,
            by simp, hM⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨.G2, m, n, Or.inl ⟨hn, Or.inr (Or.inr (Or.inl rfl))⟩,
            by simp, hM⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨.trialityD4, m, n,
            Or.inl ⟨hn, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩, by simp, hM⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨.twistedF4, m, n,
            Or.inl ⟨hn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩, by simp, hM⟩))
        · obtain ⟨rfl, -⟩ := hadm'
          exact Or.inl ⟨n, hn, Or.inl hMX, hz⟩
        · exact Or.inr (Or.inr (Or.inl ⟨.PSp, 2, n,
            Or.inl ⟨hn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))))⟩,
            by simp, hM⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨.PSp, 3, n,
            Or.inl ⟨hn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)))))⟩,
            by simp, hM⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨.POmegaMinus, 4, n,
            Or.inl ⟨hn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))⟩,
            by simp, hM⟩))
      · omega
      · omega
    · exact Or.inr (Or.inr (Or.inl ⟨.PSL, 3, n, Or.inl ⟨hn, Or.inl ⟨rfl, Or.inl rfl⟩⟩,
        by simp, hM⟩))
    · by_cases h3 : n = 3
      · subst h3
        exact Or.inr (Or.inl hM)
      · exact Or.inr (Or.inr (Or.inl ⟨.PSU, 3, n, Or.inl ⟨hn, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩,
          fun h => h3 h.2.2, hM⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨.trialityD4, 0, 1, Or.inr (Or.inr ⟨rfl, rfl⟩), by simp, hM⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨.trialityD4, 0, 2,
      Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩), by simp, hM⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨.PSU, 4, 2, Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, Or.inl rfl⟩⟩),
      by simp, hM⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨.PSU, 5, 2, Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, Or.inr rfl⟩⟩),
      by simp, hM⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨.POmegaMinus, 4, 2,
      Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩), by simp, hM⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hM)))


section Assembly

variable {G : Type} [Group G] [Finite G]

theorem uc22p20q_s20_7_of (hG : Global22f) (hB : ListBNonabelian) (hQ : QuasisimpleDichotomy)
    (D : Data G) (h20_1 : S20_1_124 D) (h20_6 : S20_6 D) : S20_7 D := by
  intro h1930 L hL
  obtain ⟨K, hK, hLK0⟩ := hL.2.2.2
  have hLK : L = uc22p20bOrb D.T K := hLK0
  rcases uc22p20p_orbit_cases D hQ hB h20_1 h1930 hL hK hLK with hLK1 | ⟨K₂, hK₂, hne, hLK2, t, -, hK₂t⟩
  ·
    subst hLK1
    have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hK.2.2
    have hodd := uc22p20p_odd_center_bar2 ↥L
    have hlist := uc22p20p_S_on_listB D hB h1930 hL hK hLK
    rcases uc22p20q_r1_cases hG hq hodd hlist with hS | ⟨t, m, n, hex, hM⟩ | hA
    · rcases hS with hS | hS | hS | hS | hS | hS
      · exact Or.inl hS
      · exact Or.inr (Or.inl hS)
      · exact Or.inr (Or.inr (Or.inl hS))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hS)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hS))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hS)))))
    · exact (uc22p20o_excl_false_one hG hB D h20_1 h1930 hL hK hodd hex hM).elim
    · exact (h20_6 h1930 L hL
        (uc22p20p_isAlt_of_center_bot (hG.a9 (Bar2 L) hq hodd hA).1 hA)).elim
  ·
    obtain ⟨A₁, A₂, hcomm, hsup, ⟨e₁⟩, ⟨e₂⟩⟩ := uc22p20p_two_setup D hL hK hK₂ hne hLK2 hK₂t
    have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
    have hodd := uc22p20p_odd_center_bar2 ↥K
    have hlist := uc22p20p_S_on_listB D hB h1930 hL hK hLK
    rcases uc22p20q_r2_cases hG hq hodd hlist with ⟨n, hn, hSz, hz⟩ | hM |
        ⟨t', m, n, htwo, hq3, hM⟩ | ⟨t', m, n, hex, hM⟩ | hA
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, ↥A₁, ↥A₂, inferInstance,
        inferInstance, ?_, ?_, ?_⟩))))))
      · exact uc22p20p_prod_equiv hcomm hsup (uc22p20p_inf_eq_bot e₁ hcomm hz)
      · rcases hSz with h | h
        · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e₁ h)
        · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e₁ h)
      · rcases hSz with h | h
        · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e₂ h)
        · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e₂ h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (uc22p20p_u38_two hG hB D h20_1 h1930 hL hcomm hsup e₁ e₂ hq hodd hM)))))))
    · exact (uc22p20p_two_false hG hB D h20_1 h1930 hL hcomm hsup e₁ e₂ hq hodd htwo hM hq3).elim
    · exact (uc22p20p_excl_false_two hG hB D h20_1 h1930 hL hcomm hsup e₁ hq hodd (Or.inl hex)
        hM).elim
    · exact (uc22p20p_alt_two_false hG hB D h20_1 h1930 hL hcomm e₁ e₂ hq hodd hA).elim

end Assembly

end CFSG.LocalAnalysis.UniquenessCase.UC22
