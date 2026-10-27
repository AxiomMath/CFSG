module

public import CFSG.Quasithin.Background.C126RFTypes
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.Quasithin.C126

open CFSG.Open

theorem exists_surjective_to_normal {Y A : Type*} [Group Y] [Group A]
    (hY : CFSG.Open.IsQuasisimple Y) (ρ : Y →* A) {L : Subgroup A} (hLr : L ≤ ρ.range)
    (hLn : ρ.range ≤ Subgroup.normalizer (L : Set A))
    (hnc : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) : ∃ f : Y →* ↥L, Function.Surjective f := by
  let P : Subgroup Y := L.comap ρ
  have hPn : P.Normal := ⟨fun s hs g => by
    have hg : ρ g ∈ Subgroup.normalizer (L : Set A) := hLn ⟨g, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 hg (ρ s)).1 hs
    simpa [P, Subgroup.mem_comap, map_mul, map_inv] using h1⟩
  by_cases htop : P = ⊤
  · refine ⟨ρ.codRestrict L fun y => ?_, fun a => ?_⟩
    · have : y ∈ P := htop ▸ Subgroup.mem_top y
      exact this
    · obtain ⟨y, hy⟩ := hLr a.2
      exact ⟨y, Subtype.ext hy⟩
  · exfalso
    have hc := normal_le_center_of_quasisimple hY P htop
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    obtain ⟨y₁, rfl⟩ := hLr ha
    obtain ⟨y₂, rfl⟩ := hLr hb
    apply hab
    have h1 : y₂ * y₁ = y₁ * y₂ := Subgroup.mem_center_iff.mp (hc ha) y₂
    rw [← map_mul, ← map_mul, h1]

theorem nonempty_quot_center_mulEquiv {Y W : Type*} [Group Y] [Group W]
    (hY : CFSG.Open.IsQuasisimple Y) (f : Y →* W) (hf : Function.Surjective f) [Nontrivial W]
    (hW : Subgroup.center W = ⊥) : Nonempty (Y ⧸ Subgroup.center Y ≃* W) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (ker_eq_center_of_surjective hY f hf hW).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

theorem isPerfect_of_sl2_equiv {L F : Type} [Group L] [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Group.IsPerfect L := by
  have h4 : 4 ≤ (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
  have hp : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_isPerfect le_rfl (Or.inr ⟨s, hs⟩)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem exists_noncomm_of_perfect {X : Type*} [Group X] [Nontrivial X] (h : Group.IsPerfect X) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative X := ⟨⟨hcon⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (G := X) this

end CFSG.Quasithin.C126
