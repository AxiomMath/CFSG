module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20q
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20s

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

variable {G : Type} [Group G] [Finite G]

theorem uc22p20t_r1_refined (hG : Global22f) {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    (hB : Asc1930ListB (X ⧸ Subgroup.center X)) :
    (∃ n : ℕ, 2 < n ∧ (IsSz X n ∨ IsL2 X n ∨ IsSU3 X n)) ∨
      (∃ (t : StatedLieTag) (m n : ℕ), uc22p20sGraphShape t m n ∧
        LieModel (X ⧸ Subgroup.center X) t m 2 n ∧ (IsSL3 X n ∨ IsSp4 X n)) ∨
      (∃ (t : StatedLieTag) (m n : ℕ), uc22p20sRankTwo t m n ∧
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
        · exact Or.inl ⟨n, hn, Or.inr (Or.inl hMX)⟩
        · exact Or.inr (Or.inr (Or.inl ⟨.PSL, 4, n, Or.inl ⟨hn, Or.inl ⟨rfl, rfl⟩⟩, hM⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨.PSU, 4, n, Or.inl ⟨hn, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩, hM⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨.G2, m, n, Or.inl ⟨hn, Or.inr (Or.inr (Or.inl rfl))⟩, hM⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨.trialityD4, m, n,
            Or.inl ⟨hn, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩, hM⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨.twistedF4, m, n,
            Or.inl ⟨hn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩, hM⟩))
        · obtain ⟨rfl, -⟩ := hadm'
          exact Or.inl ⟨n, hn, Or.inl hMX⟩
        · exact Or.inr (Or.inl ⟨.PSp, 2, n, ⟨hn, Or.inr ⟨rfl, rfl⟩⟩, hM, Or.inr hMX⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨.PSp, 3, n,
            Or.inl ⟨hn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩, hM⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨.POmegaMinus, 4, n,
            Or.inl ⟨hn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))⟩, hM⟩))
      · omega
      · omega
    · exact Or.inr (Or.inl ⟨.PSL, 3, n, ⟨hn, Or.inl ⟨rfl, rfl⟩⟩, hM, Or.inl ⟨hq, hM⟩⟩)
    · exact Or.inl ⟨n, hn, Or.inr (Or.inr ⟨hq, hM⟩)⟩
  · exact Or.inr (Or.inr (Or.inl ⟨.trialityD4, 0, 1, Or.inr (Or.inr ⟨rfl, rfl⟩), hM⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨.trialityD4, 0, 2, Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩),
      hM⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨.PSU, 4, 2, Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, Or.inl rfl⟩⟩),
      hM⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨.PSU, 5, 2, Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, Or.inr rfl⟩⟩),
      hM⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨.POmegaMinus, 4, 2,
      Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩), hM⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hM)))

@[expose] def uc22p20tS207Ref (D : Data G) : Prop :=
  H1930 D → ∀ L ∈ calL D.T D.M,
    (CFSG.Open.IsQuasisimple (Bar2 L) ∧
      ((∃ n : ℕ, 2 < n ∧ (IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n ∨ IsSU3 (Bar2 L) n)) ∨
        (∃ (t : StatedLieTag) (m n : ℕ), uc22p20sGraphShape t m n ∧
          LieModel (Bar2 L ⧸ center (Bar2 L)) t m 2 n ∧ (IsSL3 (Bar2 L) n ∨ IsSp4 (Bar2 L) n)) ∨
        (∃ (t : StatedLieTag) (m n : ℕ), uc22p20sRankTwo t m n ∧
          LieModel (Bar2 L ⧸ center (Bar2 L)) t m 2 n))) ∨
    (∃ L₁ L₂ : Subgroup G, L₁ ∈ calC L ∧ L₂ ∈ calC L ∧ L = L₁ ⊔ L₂ ∧ L₁ ≠ L₂ ∧
      (∃ t ∈ D.T, L₂ = L₁.map (MulAut.conj t).toMonoidHom) ∧
      ∃ n : ℕ, ∀ L' ∈ ({L₁, L₂} : Set (Subgroup G)),
        IsSz (Bar2 L') n ∨ IsL2 (Bar2 L') n ∨ (n = 3 ∧ IsSU3 (Bar2 L') 3))

theorem uc22p20t_s20_7ref_of (hG : Global22f) (hB : ListBNonabelian) (hQ : QuasisimpleDichotomy)
    (D : Data G) (h20_1 : S20_1_124 D) (h20_6 : S20_6 D) : uc22p20tS207Ref D := by
  intro h1930 L hL
  obtain ⟨K, hK, hLK0⟩ := hL.2.2.2
  have hLK : L = uc22p20bOrb D.T K := hLK0
  rcases uc22p20p_orbit_cases D hQ hB h20_1 h1930 hL hK hLK with
    hLK1 | ⟨K₂, hK₂, hne, hLK2, t, htT, hK₂t⟩
  ·
    subst hLK1
    have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hK.2.2
    have hodd := uc22p20p_odd_center_bar2 ↥L
    have hlist := uc22p20p_S_on_listB D hB h1930 hL hK hLK
    refine Or.inl ⟨hq, ?_⟩
    rcases uc22p20t_r1_refined hG hq hodd hlist with hA | hBg | hC | ⟨t, m, n, hex, hM⟩ | hAlt
    · exact Or.inl hA
    · exact Or.inr (Or.inl hBg)
    · exact Or.inr (Or.inr hC)
    · exact (uc22p20o_excl_false_one hG hB D h20_1 h1930 hL hK hodd (Or.inl hex) hM).elim
    · exact (h20_6 h1930 L hL
        (uc22p20p_isAlt_of_center_bot (hG.a9 (Bar2 L) hq hodd hAlt).1 hAlt)).elim
  ·
    obtain ⟨A₁, A₂, hcomm, hsup, ⟨e₁⟩, ⟨e₂⟩⟩ := uc22p20p_two_setup D hL hK hK₂ hne hLK2 hK₂t
    have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
    have hodd := uc22p20p_odd_center_bar2 ↥K
    have hlist := uc22p20p_S_on_listB D hB h1930 hL hK hLK
    obtain ⟨f⟩ := uc22p20d_bar2_conj t K
    rw [← hK₂t] at f
    rcases uc22p20q_r2_cases hG hq hodd hlist with ⟨n, hn, hSz, hz⟩ | hM |
        ⟨t', m, n, htwo, hq3, hM⟩ | ⟨t', m, n, hex, hM⟩ | hA
    · refine Or.inr ⟨K, K₂, hK, hK₂, hLK2, hne.symm, ⟨t, htT, hK₂t⟩, n, ?_⟩
      intro L' hL'
      rcases hL' with h | h
      · rw [h]
        exact hSz.elim Or.inl (fun h' => Or.inr (Or.inl h'))
      · rw [Set.mem_singleton_iff.1 h]
        rcases hSz with h' | h'
        · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv f h')
        · exact Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv f h'))
    · refine Or.inr ⟨K, K₂, hK, hK₂, hLK2, hne.symm, ⟨t, htT, hK₂t⟩, 3, ?_⟩
      intro L' hL'
      have hSU : IsSU3 (Bar2 K) 3 := ⟨hq, hM⟩
      rcases hL' with h | h
      · rw [h]
        exact Or.inr (Or.inr ⟨rfl, hSU⟩)
      · rw [Set.mem_singleton_iff.1 h]
        exact Or.inr (Or.inr ⟨rfl, uc22p20p_isSU3_of_mulEquiv f hSU⟩)
    · exact (uc22p20p_two_false hG hB D h20_1 h1930 hL hcomm hsup e₁ e₂ hq hodd htwo hM hq3).elim
    · exact (uc22p20p_excl_false_two hG hB D h20_1 h1930 hL hcomm hsup e₁ hq hodd (Or.inl hex)
        hM).elim
    · exact (uc22p20p_alt_two_false hG hB D h20_1 h1930 hL hcomm e₁ e₂ hq hodd hA).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
