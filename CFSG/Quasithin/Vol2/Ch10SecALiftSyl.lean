module

public import CFSG.Quasithin.Vol2.Ch10SecASL2OverMain
public import CFSG.Quasithin.Vol2.Ch10SecALift

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

variable {F : Type} [Field F]

@[expose] def unipHom : Multiplicative F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun b := unipSL (Multiplicative.toAdd b)
  map_one' := by rw [toAdd_one, unipSL_zero]
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipHom_apply (b : Multiplicative F) : unipHom b = unipSL (Multiplicative.toAdd b) :=
  rfl

theorem unipHom_injective : Function.Injective (unipHom (F := F)) := by
  intro a b h
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [unipHom_apply, coe_unipSL] using h1

variable [Finite F]

theorem exists_conj_unip {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hP : IsPGroup 2 P)
    (hidx : ¬ 2 ∣ P.index) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, (∀ p ∈ P, ∃ b : F, g * p * g⁻¹ = unipSL b) ∧
      ∀ b : F, g⁻¹ * unipSL b * g ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₀ := (unipHom (F := F)).range with hU₀
  have hU₀c : Nat.card U₀ = 2 ^ n := by
    rw [hU₀, MonoidHom.range_eq_map, Subgroup.card_map_of_injective unipHom_injective,
      Subgroup.card_top]
    exact hF
  have hG := card_SL_two_pow hF
  have hU₀2 : IsPGroup 2 U₀ := IsPGroup.of_card hU₀c
  have hU₀i : ¬ 2 ∣ U₀.index := by
    have h := U₀.card_mul_index
    rw [hU₀c, hG] at h
    have hi : U₀.index = 4 ^ n - 1 := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos n) h
    rw [hi]
    have hn : n ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card (α := F)
      rw [hF] at this
      norm_num at this
    exact Nat.not_even_iff_odd.mpr (odd_four_pow_sub_one hn) ∘ even_iff_two_dvd.mpr
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) F)
    (hP.toSylow hidx) (hU₀2.toSylow hU₀i)
  have h1 : (g • hP.toSylow hidx : Subgroup _) = U₀ := by
    rw [hg, IsPGroup.toSylow_coe]
  refine ⟨g, fun p hp => ?_, fun b => ?_⟩
  · have hmem : g * p * g⁻¹ ∈ U₀ := by
      rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨p, (IsPGroup.mem_toSylow hP hidx).mpr hp, rfl⟩
    obtain ⟨b, hb⟩ := hmem
    exact ⟨Multiplicative.toAdd b, hb.symm.trans (unipHom_apply b)⟩
  · have hmem : unipSL b ∈ (g • hP.toSylow hidx : Subgroup _) := by
      rw [h1]
      exact ⟨Multiplicative.ofAdd b, rfl⟩
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
    obtain ⟨p, hp, hpe⟩ := hmem
    have hpe' : g * p * g⁻¹ = unipSL b := hpe
    have : p = g⁻¹ * unipSL b * g := by rw [← hpe']; group
    rw [← this]
    exact (IsPGroup.mem_toSylow hP hidx).mp hp

end CFSG.Quasithin.Vol2.Ch10.SecA
