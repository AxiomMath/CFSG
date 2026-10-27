module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Count
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem mem_comap_conj_centralizer_iff {S : Type} [Group S] (hZ : Subgroup.center S = ⊥)
    (α : MulAut S) (x : S) :
    x ∈ Subgroup.comap (MulAut.conj : S →* MulAut S)
        (Subgroup.centralizer ({α} : Set (MulAut S))) ↔ α x = x := by
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hc : (α x)⁻¹ * x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := α.surjective z
      have := congrArg (fun φ : MulAut S => φ y) h
      simp only [MulAut.mul_apply, MulAut.conj_apply] at this
      rw [map_mul, map_mul, map_inv] at this
      have h1 : ((α x)⁻¹ * x) * α y * ((α x)⁻¹ * x)⁻¹ = α y := by
        calc ((α x)⁻¹ * x) * α y * ((α x)⁻¹ * x)⁻¹
            = (α x)⁻¹ * (x * α y * x⁻¹) * α x := by group
          _ = (α x)⁻¹ * (α x * α y * (α x)⁻¹) * α x := by rw [this]
          _ = α y := by group
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc
  · intro h
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv, h]

theorem three_dvd_index_of_card_dvd {S : Type} [Group S] [Finite S] (H : Subgroup S) {M : ℕ}
    (hH : Nat.card H ∣ M) (h3 : 3 * M ∣ Nat.card S) : 3 ∣ H.index := by
  obtain ⟨k, hk⟩ := hH
  have hS : Nat.card H * H.index = Nat.card S := Subgroup.card_mul_index H
  have hpos : 0 < Nat.card H := Nat.card_pos
  have h1 : 3 * (Nat.card H * k) ∣ Nat.card H * H.index := by
    rw [hS, ← hk]
    exact h3
  have h2 : 3 * k ∣ H.index := by
    have : Nat.card H * (3 * k) ∣ Nat.card H * H.index := by
      have e : Nat.card H * (3 * k) = 3 * (Nat.card H * k) := by ring
      rw [e]
      exact h1
    exact Nat.dvd_of_mul_dvd_mul_left hpos this
  exact (Dvd.intro k rfl).trans h2

theorem outerRow_of_fixed_card_dvd {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (h : ∀ σ : MulAut S, σ ^ 3 = 1 → σ ∉ (MulAut.conj : S →* MulAut S).range →
      ∃ (H : Subgroup S) (M : ℕ), (∀ x, x ∈ H ↔ σ x = x) ∧ Nat.card H ∣ M ∧ 3 * M ∣ Nat.card S) :
    OuterRow S := by
  intro _ σ hσ hout
  obtain ⟨H, M, hH, hcard, h3⟩ := h σ hσ hout
  refine not_autWeaklyClosed_of_three_dvd_index hσ hout ?_
  have heq : Subgroup.comap (MulAut.conj : S →* MulAut S)
      (Subgroup.centralizer ({σ} : Set (MulAut S))) = H := by
    ext x
    rw [mem_comap_conj_centralizer_iff hZ, hH]
  rw [heq]
  exact three_dvd_index_of_card_dvd H hcard h3

end CFSG.RankThree.PartTwo.Sec4.RonanK432
