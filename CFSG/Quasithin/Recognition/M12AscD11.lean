module

public import CFSG.Quasithin.Recognition.M12AscCoxData
public import CFSG.Quasithin.Recognition.M12AscL2Inputs

public section

namespace CFSG.Quasithin

open Subgroup Equiv

variable {G : Type*} [Group G] {z : G}

@[expose] def d6w (a b : Perm (Fin 6)) : Fin 9 → Perm (Fin 6) :=
  ![1, a, a * a, b, b * a, b * (a * a), b * b, b * b * a, b * b * (a * a)]

theorem D6l_eq_ofFn : D6l = List.ofFn (d6w x6 x16) := by decide +kernel

theorem mem_D6l_iff {d : Perm (Fin 6)} : d ∈ D6l ↔ ∃ k, d6w x6 x16 k = d := by
  rw [D6l_eq_ofFn, List.mem_ofFn]

@[expose] def d6idx (d : Perm (Fin 6)) : Fin 9 :=
  ((List.finRange 9).find? fun k => d6w x6 x16 k == d).getD 0

theorem d6idx_spec : ∀ k : Fin 9, d6idx (d6w x6 x16 k) = k := by decide +kernel

@[expose] def fAct (a b d : Perm (Fin 6)) : Perm (Fin 6) := d6w a b (d6idx d)

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem conj_d6w {g : G} {a b : Perm (Fin 6)} (ha : g * c.ρ x6 * g⁻¹ = c.ρ a)
    (hb : g * c.ρ x16 * g⁻¹ = c.ρ b) (k : Fin 9) :
    g * c.ρ (d6w x6 x16 k) * g⁻¹ = c.ρ (d6w a b k) := by
  let φ : Perm (Fin 6) →* G := (MulAut.conj g).toMonoidHom.comp c.ρ
  have hφ : ∀ p, φ p = g * c.ρ p * g⁻¹ := fun p => rfl
  have h6 : φ x6 = c.ρ a := by rw [hφ, ha]
  have h16 : φ x16 = c.ρ b := by rw [hφ, hb]
  rw [← hφ]
  fin_cases k <;> simp [d6w, map_mul, map_one, h6, h16]

theorem conj_fAct {g : G} {a b : Perm (Fin 6)} (ha : g * c.ρ x6 * g⁻¹ = c.ρ a)
    (hb : g * c.ρ x16 * g⁻¹ = c.ρ b) {d : Perm (Fin 6)} (hd : d ∈ D6l) :
    g * c.ρ d * g⁻¹ = c.ρ (fAct a b d) := by
  obtain ⟨k, rfl⟩ := mem_D6l_iff.1 hd
  rw [fAct, d6idx_spec]
  exact c.conj_d6w ha hb k

end AscCox

end CFSG.Quasithin
