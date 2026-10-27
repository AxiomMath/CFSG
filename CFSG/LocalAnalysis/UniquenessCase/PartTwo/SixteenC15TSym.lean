module

public import CFSG.Quasithin.Background.Harris.Ln2.PermRank
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem s16c15t_rk_le_of_mulEquiv_perm {X : Type} [Group X] {n : ℕ}
    (e : X ≃* Equiv.Perm (Fin n)) {E : Subgroup X} (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h2 : ∀ a ∈ E, a ^ 2 = 1) : rk ↥E ≤ n / 2 := by
  haveI : Finite ↥E := Finite.of_injective (fun x : E => e x.1)
    (fun a b h => Subtype.ext (e.injective h))
  have hP : IsPGroup 2 ↥E := fun a => ⟨1, by simpa using Subtype.ext (h2 a a.2)⟩
  have hcard := card_eq_two_pow_of_isPGroup hP
  have hBcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective e.injective
  have hcB : ∀ a ∈ E.map e.toMonoidHom, ∀ b ∈ E.map e.toMonoidHom, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  have h2B : ∀ a ∈ E.map e.toMonoidHom, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, h2 a ha, map_one]
  have hle := CFSG.Quasithin.G11.Harris.Ln2.card_le_of_elemAbelian_perm hcB h2B
  rw [hBcard, Fintype.card_fin, hcard] at hle
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
