module

import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSL3
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix Subgroup

theorem exists_lift_projective_sl3 {K : Type} [Field K] {p f : ℕ} {π : Bool}
    (hK : PiField π p f K)
    (Y : Subgroup (projImage (slPi π 3 (p ^ f) K))) (hY3 : ¬ 3 ∣ Nat.card Y) :
    ∃ Ŷ : Subgroup (GL (Fin 3) K), Ŷ ≤ slPi π 3 (p ^ f) K ∧
      ∃ e : Ŷ ≃* Y, ∀ g : Ŷ,
        ((e g : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (g : GL (Fin 3) K) := by
  have : Finite K := hK.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K := by
    intro h
    subst π
    exact hK.unitary
  have hker : IsPGroup 3 (projOf (slPi π 3 (p ^ f) K)).ker := by
    intro s
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨c, hc⟩ := (mem_ker_projOf (s : slPi π 3 (p ^ f) K)).mp s.2
    have hcL : GeneralLinearGroup.scalar (Fin 3) c ∈ slPi π 3 (p ^ f) K :=
      hc ▸ (s : slPi π 3 (p ^ f) K).2
    have hc3 := pow_three_eq_one_of_scalar_mem_slPi hπ hcL
    change (s : GL (Fin 3) K) ^ (3 ^ 1) = 1
    rw [pow_one, ← hc, ← map_pow, hc3, map_one]
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (projOf (slPi π 3 (p ^ f) K)).ker) (Nat.card Y) := by
    rw [hk]
    exact ((Nat.prime_three.coprime_iff_not_dvd).mpr hY3).pow_left k
  obtain ⟨Y', hmap, hdisj⟩ := CFSG.RankThree.PartTwo.Sec6.BThreeCensus.exists_lift_of_coprime
    (projOf_surjective _) Y hcop
  let φ : Y' →* Y := ((projOf (slPi π 3 (p ^ f) K)).comp Y'.subtype).codRestrict Y
    (fun y => by rw [← hmap]; exact ⟨y, y.2, rfl⟩)
  have hφ : Function.Bijective φ := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker] at hy
      have hyker : (y : slPi π 3 (p ^ f) K) ∈ (projOf (slPi π 3 (p ^ f) K)).ker :=
        MonoidHom.mem_ker.mpr (congrArg Subtype.val hy)
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.disjoint_def.mp hdisj y.2 hyker))
    · rintro ⟨m, hm⟩
      rw [← hmap] at hm
      obtain ⟨y, hy, rfl⟩ := hm
      exact ⟨⟨y, hy⟩, rfl⟩
  let e₁ : Y' ≃* (Y'.map (slPi π 3 (p ^ f) K).subtype) :=
    Y'.equivMapOfInjective _ (slPi π 3 (p ^ f) K).subtype_injective
  refine ⟨Y'.map (slPi π 3 (p ^ f) K).subtype, Subgroup.map_subtype_le _,
    e₁.symm.trans (MulEquiv.ofBijective φ hφ), fun g => ?_⟩
  obtain ⟨y, rfl⟩ := e₁.surjective g
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.ofBijective_apply]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22
