module

public import CFSG.Quasithin.Vol2.Ch10SecKRSc
public import CFSG.Quasithin.Vol2.Ch10SecQ9H40

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin C10P4F
open scoped Matrix

theorem mem_Q2_of_conj_B0 {g : SL5}
    (h : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * B0 * (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = B0) :
    g ∈ Q2 := by
  intro i j
  have ha : 2 ≤ ((Fin.natAdd 2 i : Fin (2 + 3)) : ℕ) := by simp
  obtain ⟨h0, h1⟩ := eq_zero_of_conj_B0 h (a := Fin.natAdd 2 i) ha
  fin_cases j
  · exact h0
  · exact h1

theorem blk_one_conj_B0 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    blk (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) A * B0 *
      (blk (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) A)ᵀ = B0 := by
  ext a b
  rw [conj_B0_apply]
  fin_cases a <;> fin_cases b <;> simp [blk, Matrix.reindex_apply, B0] <;> rfl

section Mu

variable {G : Type} [Group G]

@[expose] noncomputable def muQ2 {J P : Subgroup G} (ρ : ↥J →* SL5) (hPJ : P ≤ J)
    (hQ : ∀ x : ↥P, ρ (Subgroup.inclusion hPJ x) ∈ Q2) :
    ↥P →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (botH 2 3).comp ((ρ.comp (Subgroup.inclusion hPJ)).codRestrict (stabStd 2 3) hQ)

theorem muQ2_apply {J P : Subgroup G} (ρ : ↥J →* SL5) (hPJ : P ≤ J)
    (hQ : ∀ x : ↥P, ρ (Subgroup.inclusion hPJ x) ∈ Q2) (x : ↥P) :
    muQ2 ρ hPJ hQ x = botH 2 3 ⟨ρ (Subgroup.inclusion hPJ x), hQ x⟩ := rfl

end Mu

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
