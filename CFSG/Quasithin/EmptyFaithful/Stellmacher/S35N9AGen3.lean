module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35N9AGen2

public section

namespace CFSG.Quasithin

open Equiv CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

namespace S35.N9

theorem conj_mem_S5SylF {s a : Perm (Fin 5)} (hs : s ∈ S5SylF) (ha : a ∈ S5SylF) :
    s * a * s⁻¹ ∈ S5SylF := by
  rw [← mem_S5Syl_iff] at hs ha ⊢
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs ha) (Subgroup.inv_mem _ hs)

theorem coreA : ∀ g : Perm (Fin 5), ∀ a ∈ S5SylF, ∀ b ∈ S5SylF,
    (g * a * g⁻¹) 4 = 4 → (g * b * g⁻¹) 4 = 4 → g * a * g⁻¹ ∉ S5SylF →
    g * b * g⁻¹ ∉ S5SylF → (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹) ∉ S5SylF → False := by
  intro g a ha b hb
  obtain ⟨r, hr, s, hs, rfl⟩ := exists_rep g
  have e : ∀ x : Perm (Fin 5), r * s * x * (r * s)⁻¹ = r * (s * x * s⁻¹) * r⁻¹ := by
    intro x; group
  simp only [e]
  exact coreA' r hr _ (conj_mem_S5SylF hs ha) _ (conj_mem_S5SylF hs hb)

theorem coreB : ∀ g : Perm (Fin 5), ∀ a ∈ S5SylF, ∀ b ∈ S5SylF, ∀ c ∈ S5SylF, CondB g a b c := by
  intro g a ha b hb c hc
  obtain ⟨r, hr, s, hs, rfl⟩ := exists_rep g
  have e : ∀ x : Perm (Fin 5), r * s * x * (r * s)⁻¹ = r * (s * x * s⁻¹) * r⁻¹ := by
    intro x; group
  unfold CondB
  simp only [e]
  exact coreB' r hr _ (conj_mem_S5SylF hs ha) _ (conj_mem_S5SylF hs hb) _
    (conj_mem_S5SylF hs hc)

end S35.N9

end F53.Stellmacher

end CFSG.Quasithin
