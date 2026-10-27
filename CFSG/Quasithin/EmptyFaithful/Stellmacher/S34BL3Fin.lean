module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin

public section

namespace CFSG.Quasithin

namespace F53.Stellmacher

namespace S34

open CFSG.Quasithin.F53 Equiv
open scoped Pointwise

namespace BL3

theorem exists_conj_of_card_eight (P Q : Subgroup (Perm (Fin 5))) (hP : Nat.card P = 8)
    (hQ : Nat.card Q = 8) : ∃ σ : Perm (Fin 5), ∀ x, x ∈ Q ↔ σ⁻¹ * x * σ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP2, hPs, -⟩ := sylow_of_card_eight P hP
  obtain ⟨hQ2, hQs, -⟩ := sylow_of_card_eight Q hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) (hP2.toSylow hPs) (hQ2.toSylow hQs)
  have h1 : Q = MulAut.conj g • P := by
    have := congrArg (fun R : Sylow 2 (Perm (Fin 5)) => (R : Subgroup (Perm (Fin 5)))) hg
    simpa [Sylow.coe_subgroup_smul] using this.symm
  refine ⟨g, fun x => ?_⟩
  rw [h1, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

set_option synthInstance.maxSize 256 in
theorem exists_conj_mem_D0fin : ∀ t : Perm (Fin 5), t * t = 1 → ∀ r : Fin 5, t r = r →
    ∃ g : Perm (Fin 5), g 4 = r ∧ g⁻¹ * t * g ∈ D0fin := by
  decide +kernel

theorem exists_card_eight_of_fix (t : Perm (Fin 5)) (ht : t * t = 1) (r : Fin 5) (hr : t r = r) :
    ∃ P : Subgroup (Perm (Fin 5)), Nat.card P = 8 ∧ t ∈ P ∧ ∀ x ∈ P, x r = r := by
  obtain ⟨g, hg4, hgt⟩ := exists_conj_mem_D0fin t ht r hr
  refine ⟨D0.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact D0_card
  · refine ⟨g⁻¹ * t * g, hgt, ?_⟩
    simp [mul_assoc]
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ D0fin := hy
    have h4 : (g⁻¹ : Perm (Fin 5)) r = 4 := by
      rw [← hg4]
      simp
    have h5 : g (y 4) = r := by rw [D0_fix y hy', hg4]
    simpa [Perm.mul_apply, h4] using h5

end BL3

end S34

end F53.Stellmacher

end CFSG.Quasithin
