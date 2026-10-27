module

public import CFSG.RankThree.PartOne.S15K.BlockType
public import CFSG.RankThree.PartOne.S11d.OrthCaseN

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

@[expose] def BlockModel (p : ℕ) (J : Type) [Group J] : Prop :=
  ∃ (g : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), Nat.card E = 2 ^ g ∧ 2 ≤ g ∧
    p ∣ 2 ^ g - 1 ∧
    ((∃ m : ℕ, (m = 2 ∨ m = 3) ∧ Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin m) E)) ∨
      Nonempty (J ≃* StatedSp 2 E) ∨
      ∃ (W : Type) (_ : AddCommGroup W) (_ : Module E W) (_ : FiniteDimensional E W)
        (R : QuadraticForm E W), (QuadraticMap.polarBilin R).Nondegenerate ∧
        (Module.finrank E W = 4 ∨ Module.finrank E W = 6) ∧
        (∀ U : Submodule E W, Module.finrank E U = Module.finrank E W / 2 → ∃ u ∈ U, R u ≠ 0) ∧
        Nonempty (J ≃* ↥(orthDerived R)))

theorem BlockModel.of_mulEquiv {p : ℕ} {J J' : Type} [Group J] [Group J'] (e : J ≃* J')
    (h : BlockModel p J) : BlockModel p J' := by
  obtain ⟨g, E, _, _, _, hE, hg, hpg, hm⟩ := h
  refine ⟨g, E, inferInstance, inferInstance, inferInstance, hE, hg, hpg, ?_⟩
  rcases hm with ⟨m, hm, he'⟩ | he' | ⟨W, _, _, _, R, hR, hd, hts, hφ⟩
  · obtain ⟨e'⟩ := he'
    exact Or.inl ⟨m, hm, ⟨e.symm.trans e'⟩⟩
  · obtain ⟨e'⟩ := he'
    exact Or.inr (Or.inl ⟨e.symm.trans e'⟩)
  · obtain ⟨φ⟩ := hφ
    exact Or.inr (Or.inr ⟨W, inferInstance, inferInstance, inferInstance, R, hR, hd, hts,
      ⟨e.symm.trans φ⟩⟩)

theorem BlockModel.blockType {p : ℕ} {J : Type} [Group J] (h : BlockModel p J) : BlockType p J := by
  obtain ⟨g, E, _, _, _, hE, hg, hpg, hm⟩ := h
  rcases hm with ⟨m, hm, he⟩ | he | ⟨W, _, _, _, R, hR, hd, hts, hφ⟩
  · obtain ⟨e⟩ := he
    rcases hm with rfl | rfl
    · exact BlockType.of_psl_two (by omega) hpg (statedClassicalModel_psl_of_sl hE hg le_rfl e)
    · exact BlockType.of_psl_three (by omega) hpg
        (statedClassicalModel_psl_of_sl hE hg (by norm_num) e)
  · obtain ⟨e⟩ := he
    exact BlockType.of_psp (by omega) hpg (statedClassicalModel_psp_of_sp hE hg le_rfl e)
  · obtain ⟨φ⟩ := hφ
    obtain ⟨-, -, -, -, -, h4, h6⟩ := even_minus_four_six_actual_derived_extraction R hR (by omega) hts
    rcases hd with hd4 | hd6
    · obtain ⟨E', _, _, D, ψ, ρ, -, -, hinj, hrange, -⟩ := h4 hd4
      have : CharP E' 2 := charP_two_of_algebra (K := E)
      have hE' : Nat.card E' = 2 ^ (2 * g) := by rw [D.card_E, hE, ← pow_mul, mul_comm]
      have hfin : Finite E' := Nat.finite_of_card_ne_zero (by rw [hE']; positivity)
      let e : J ≃* Matrix.SpecialLinearGroup (Fin 2) E' :=
        φ.trans ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm)
      refine BlockType.of_psl_two (g := 2 * g) (by omega) ?_
        (statedClassicalModel_psl_of_sl hE' (by omega) le_rfl e)
      have h1 : 2 ^ g - 1 ∣ (2 ^ g) ^ 2 - 1 := by
        simpa using Nat.sub_dvd_pow_sub_pow (2 ^ g) 1 2
      rw [← pow_mul, mul_comm] at h1
      exact hpg.trans h1
    · obtain ⟨E', _, _, D, ψ, ρ, -, -, hinj, hrange, -⟩ := h6 hd6
      have : CharP E' 2 := charP_two_of_algebra (K := E)
      obtain ⟨f₁, hu, hK, hbar⟩ := D.exists_unitaryFieldData
      have hff : f₁ = g := Nat.pow_right_injective (le_refl 2) (hK.symm.trans hE)
      subst hff
      obtain ⟨θ⟩ := D.nonempty_sixSU_mulEquiv hu hbar
      let e : J ≃* StatedSU 4 (2 ^ f₁) E' :=
        (φ.trans ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm)).trans
          θ
      exact BlockType.of_psu (by omega) hpg
        ((CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp
          (lieModel_quotient_of_statedSU4 hu e))

end CFSG.RankThree.PartOne.S15K
