module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRoots

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank


@[expose] def piB (t : StatedLieTag) (p f : ℕ) : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank) :=
  match t with
  | .E6 => if p ∣ 2 ^ f - 1 then 1 else TwistTag.perm .E6
  | .twistedE6 => if p ∣ 2 ^ f + 1 then 1 else TwistTag.perm .E6
  | _ => 1

private theorem piB_E6_eq (p f : ℕ) :
    piB .E6 p f = if p ∣ 2 ^ f - 1 then 1 else TwistTag.perm .E6 := rfl

private theorem piB_twistedE6_eq (p f : ℕ) :
    piB .twistedE6 p f = if p ∣ 2 ^ f + 1 then 1 else TwistTag.perm .E6 := rfl

private theorem perm_E6_ne_one_aux : (TwistTag.perm .E6 : Equiv.Perm (Fin 6)) ≠ 1 := by
  decide +kernel

theorem piB_F4 (p f : ℕ) : piB .F4 p f = 1 := rfl

theorem piB_E7 (p f : ℕ) : piB .E7 p f = 1 := rfl

theorem piB_E8 (p f : ℕ) : piB .E8 p f = 1 := rfl

theorem piB_E6_of_dvd {p : ℕ} (f : ℕ) (h : p ∣ 2 ^ f - 1) : piB .E6 p f = 1 := by
  rw [piB_E6_eq]
  exact if_pos h

theorem piB_E6_of_not_dvd {p : ℕ} (f : ℕ) (h : ¬ p ∣ 2 ^ f - 1) :
    piB .E6 p f = TwistTag.perm .E6 := by
  rw [piB_E6_eq]
  exact if_neg h

theorem piB_twistedE6_of_dvd {p : ℕ} (f : ℕ) (h : p ∣ 2 ^ f + 1) : piB .twistedE6 p f = 1 := by
  rw [piB_twistedE6_eq]
  exact if_pos h

theorem piB_twistedE6_of_not_dvd {p : ℕ} (f : ℕ) (h : ¬ p ∣ 2 ^ f + 1) :
    piB .twistedE6 p f = TwistTag.perm .E6 := by
  rw [piB_twistedE6_eq]
  exact if_neg h

theorem perm_E6_ne_one (f : ℕ) :
    (TwistTag.perm .E6 : Equiv.Perm (Fin (ggU .E6 6 f).D.rank)) ≠ 1 :=
  perm_E6_ne_one_aux

theorem isDiagAut_piB {t : StatedLieTag} (p f : ℕ) (ht : GGExcFive t) :
    IsDiagAut (ggU (absTag t) 6 f).D (piB t p f) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact fun i j => rfl
  · by_cases h : p ∣ 2 ^ f - 1
    · rw [piB_E6_of_dvd f h]
      exact fun i j => rfl
    · rw [piB_E6_of_not_dvd f h]
      exact fun i j => TwistTag.cartan_perm .E6 i j
  · exact fun i j => rfl
  · exact fun i j => rfl
  · by_cases h : p ∣ 2 ^ f + 1
    · rw [piB_twistedE6_of_dvd f h]
      exact fun i j => rfl
    · rw [piB_twistedE6_of_not_dvd f h]
      exact fun i j => TwistTag.cartan_perm .E6 i j

theorem piCond_piB {t : StatedLieTag} (p f : ℕ) (ht : GGExcFive t) :
    GGPiCond t p f (piB t p f) := by
  refine ⟨isDiagAut_piB p f ht, ?_, ?_, ?_⟩
  · intro h
    rcases h with rfl | rfl | rfl <;> rfl
  · rintro rfl
    by_cases h : p ∣ 2 ^ f - 1
    · rw [piB_E6_of_dvd f h]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [piB_E6_of_not_dvd f h]
      exact ⟨fun h1 => absurd h1 (perm_E6_ne_one f), fun h1 => absurd h1 h⟩
  · rintro rfl
    by_cases h : p ∣ 2 ^ f + 1
    · rw [piB_twistedE6_of_dvd f h]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [piB_twistedE6_of_not_dvd f h]
      exact ⟨fun h1 => absurd h1 (perm_E6_ne_one f), fun h1 => absurd h1 h⟩

theorem piB_diag {t : StatedLieTag} (p f : ℕ) (ht : GGExcFive t)
    (j k : Fin (ggU (absTag t) 6 f).D.rank) :
    (langTag t).cartan (Fin.cast (rank_eq_langTag f ht) (piB t p f j))
        (Fin.cast (rank_eq_langTag f ht) (piB t p f k)) =
      (langTag t).cartan (Fin.cast (rank_eq_langTag f ht) j)
        (Fin.cast (rank_eq_langTag f ht) k) := by
  have h := isDiagAut_piB p f ht j k
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> exact h

end CFSG.StandardType.GGFinModel
