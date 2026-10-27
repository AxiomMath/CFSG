module

public import CFSG.Quasithin.Background.F918T6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

private theorem t8_congr_congr (M N B : Matrix (Fin 5) (Fin 5) (ZMod 2)) :
    M * (N * B * Nᵀ) * Mᵀ = M * N * B * (M * N)ᵀ := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

private theorem t8_card_fix_le_map_conj (ρ : ↥(StatedSL 5 (ZMod 2)) → Matrix (Fin 5) (Fin 5) (ZMod 2))
    (hmul : ∀ a b, ρ (a * b) = ρ a * ρ b) (hone : ρ 1 = 1)
    (E : Subgroup ↥(StatedSL 5 (ZMod 2))) (h : ↥(StatedSL 5 (ZMod 2))) :
    Nat.card {B : ↥(altMat 5) //
        ∀ g ∈ E, ρ g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (ρ g)ᵀ = B} ≤
      Nat.card {B : ↥(altMat 5) //
        ∀ g ∈ E.map (MulAut.conj h).toMonoidHom,
          ρ g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (ρ g)ᵀ = B} := by
  have hinv : ρ h⁻¹ * ρ h = 1 := by rw [← hmul, inv_mul_cancel, hone]
  have hfix : ∀ B : {B : ↥(altMat 5) //
        ∀ g ∈ E, ρ g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (ρ g)ᵀ = B},
      ∀ g ∈ E.map (MulAut.conj h).toMonoidHom,
        ρ g * (ρ h * (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (ρ h)ᵀ) * (ρ g)ᵀ =
          ρ h * (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (ρ h)ᵀ := by
    rintro B _ ⟨y, hy, rfl⟩
    have hgh : (MulAut.conj h).toMonoidHom y * h = h * y := by simp
    rw [t8_congr_congr, ← hmul, hgh, hmul, ← t8_congr_congr, B.2 y hy]
  refine Nat.card_le_card_of_injective
    (fun B => ⟨⟨ρ h * (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (ρ h)ᵀ, congr_mem_altMat _ B.1.2⟩,
      hfix B⟩) ?_
  intro B C hBC
  have h1 : ρ h * (B.1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (ρ h)ᵀ = ρ h * C.1 * (ρ h)ᵀ :=
    congrArg (fun D => ((D.1 : ↥(altMat 5)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) hBC
  have h2 := congrArg (fun D => ρ h⁻¹ * D * (ρ h⁻¹)ᵀ) h1
  simp only [t8_congr_congr, hinv, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at h2
  exact Subtype.ext (Subtype.ext h2)

theorem d35InspExtSq_of_unitri
    (hsyl : ∀ E : Subgroup ↥(StatedSL 5 (ZMod 2)), IsPGroup 2 ↥E →
      ∃ g : ↥(StatedSL 5 (ZMod 2)), ∀ x ∈ E, g * x * g⁻¹ ∈ unitri5)
    (hU : D35InspExtSqU) : D35InspExtSq := by
  intro E hE hcomm hsq hoff
  have hp : IsPGroup 2 ↥E := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, sq]; exact hsq g.1 g.2)⟩
  obtain ⟨h, hh⟩ := hsyl E hp
  have hinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  have hcard : Nat.card (E.map (MulAut.conj h).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective hinj
  refine hU (E.map (MulAut.conj h).toMonoidHom) ?_ ?_ ?_ ?_ ⟨?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hh y hy
  · exact fun h0 => hE ((Subgroup.map_eq_bot_iff_of_injective E hinj).mp h0)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]
  · rw [hcard]
    exact hoff.1.trans (Nat.mul_le_mul_left _
      (t8_card_fix_le_map_conj mat B5.Ln.mat_mul B5.Ln.mat_one E h))
  · rw [hcard]
    exact hoff.2.trans (Nat.mul_le_mul_left _
      (t8_card_fix_le_map_conj dmat B5.Ln.dmat_mul B5.Ln.dmat_one E h))

end CFSG.Quasithin
