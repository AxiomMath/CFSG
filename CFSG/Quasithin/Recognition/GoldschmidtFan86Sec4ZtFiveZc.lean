module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4ZtFiveMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Core

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem zcFin (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (h33 : Fan33 F)
    (h48 : Fan48Two F) : ZcFin F := by
  intro T u hu hu1
  obtain ⟨-, i, hcen⟩ := hu
  obtain ⟨hui, -⟩ := T.line.edgeCirc_fix hcen.1
  have h5 : ∃ j, (j = i ∨ j = i + 1) ∧ valence Γ (T.line.vert j) = 5 := by
    have h1 := F.alternating _ _ (T.line.adj i)
    have h2 := F.valence (T.line.vert i)
    have h3 := F.valence (T.line.vert (i + 1))
    by_cases h : valence Γ (T.line.vert i) = 5
    · exact ⟨i, Or.inl rfl, h⟩
    · refine ⟨i + 1, Or.inr rfl, ?_⟩
      have h4 : Nat.card (Γ.neighborSet (T.line.vert i)) ≠ 5 := h
      show Nat.card (Γ.neighborSet (T.line.vert (i + 1))) = 5
      omega
  obtain ⟨j, hj, hj5⟩ := h5
  have hnot : u ∉ T.fixer := by
    intro huT
    have hz : u ∈ ZT T j := by
      rw [mem_ZT_iff]
      exact ⟨huT, fun k hk => hcen.2 k (T.line.nbrStab_subset_edgeCirc F hj hj5 hk)⟩
    rw [fan49_five F h40 h28 h33 h48 T j hj5] at hz
    exact hu1 (Subgroup.mem_bot.1 hz)
  exact P514.exists_fixIdx_interval' F T hnot hui

end CFSG.Quasithin.Fan86
