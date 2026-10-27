module

public import CFSG.Quasithin.Background.B5B42
public import CFSG.Quasithin.Background.FFC4Pair

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

namespace B59

section B42Sl2

variable {V : Type} [CommGroup V] [Finite V]

theorem b42_case1_of_sl2 (hI : B58Inputs) (hIdent : AsB42Ident) (hV : ∀ v : V, v ^ 2 = 1)
    {G L A : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hA : IsFFStarOffender G A) (hGL : G = L)
    (hno : ¬ ThreeRank2 ↥L) (h23 : (∃ n, BinaryNaturalSL L (⊤ : Subgroup V) ⊥ 3 n) → False)
    (h : B42Conclusion G L A) : B42Case1 G L A := by
  by_cases hJL : ffJ G = L
  · have h5 : ¬ B42Case5 G A := fun h5 => (hIdent V hV G L hHyp A hA (Or.inl h5)).1 hJL
    rcases h with h1 | ⟨hJ, ⟨n, hn⟩, hq⟩ | ⟨⟨n, hn, -⟩, hq⟩ | ⟨⟨n, hn, -, -⟩, hq⟩ | h5' |
      ⟨hJ, hn, -, hq, -⟩ | ⟨-, hJ, hn, -, hq, -⟩ |
      ⟨hJ, -, hq, ⟨K, hK, hf, Γ₀, hc, hdet, hhat, hcen, π, hπ, -⟩⟩ |
      ⟨hJ, n, hn4, hn, hq⟩ | ⟨hn, hrest⟩ | ⟨-, hJ, -, hq, π, hπ⟩
    · exact h1
    · exact (h23 ⟨n, hn⟩).elim
    · rw [hJL] at hn
      obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
      exact (hno (threeRank2_of_realizes (FFModel.nat_faithful _) hπ threeRank2_statedSp)).elim
    · rw [hJL] at hn
      obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
      have := charP_two_of_card_pow hc
      exact (hno (threeRank2_of_realizes (zornQ_faithful _ le_rfl) hπ (hI.g2 K ‹_›))).elim
    · exact (h5 h5').elim
    · obtain ⟨π, hπ⟩ := hn
      exact (hno (threeRank2_of_realizes (altDn_faithful (by norm_num)) hπ
        (threeRank2_alt (by norm_num)))).elim
    · obtain ⟨α, π, hπ⟩ := hn
      exact (hno (threeRank2_of_realizes (a7Four_faithful α) hπ
        (threeRank2_alt (n := 7) (by norm_num)))).elim
    · have hE9 : ThreeRank2 ↥Γ₀ := threeRank2_hat hhat
      exact (hno (threeRank2_of_realizes (FFModel.nat_faithful _) hπ hE9)).elim
    · rcases hn4 with rfl | rfl
      · obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
        exact (hno (threeRank2_of_realizes (FFModel.nat_faithful _) hπ
          (threeRank2_statedSL (by norm_num)))).elim
      · obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
        exact (hno (threeRank2_of_realizes (FFModel.nat_faithful _) hπ
          (threeRank2_statedSL (by norm_num)))).elim
    · rcases hrest with ⟨-, hJ, -, hq⟩ | ⟨hGJ, ⟨e⟩, -⟩
      · obtain ⟨π, hπ⟩ := hn
        exact (hno (threeRank2_of_realizes (hI.ext 4 (by norm_num)) hπ
          (threeRank2_statedSL (by norm_num)))).elim
      · exfalso
        have hperf : Group.IsPerfect ↥G := by
          have hq := hHyp.2.2.1
          have h1 : Group.IsPerfect ↥(ffJ G) := by rw [hJL]; exact hq.1
          rw [← hGJ] at h1
          exact h1
        have := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
        exact B5.not_isPerfect_perm 8 (by norm_num) this
    · have h11 : SLExteriorTwo L (⊤ : Subgroup V) ⊥ 5 := ⟨π, hπ.1⟩
      obtain ⟨π', hπ'⟩ := h11
      exact (hno (threeRank2_of_realizes (hI.ext 5 (by norm_num)) hπ'
        (threeRank2_statedSL (by norm_num)))).elim
  · exfalso
    obtain ⟨-, hGJ, -⟩ := hIdent V hV G L hHyp A hA (Or.inr hJL)
    exact hJL (by rw [← hGJ, hGL])

end B42Sl2

end B59

end FFC

end CFSG.Quasithin
