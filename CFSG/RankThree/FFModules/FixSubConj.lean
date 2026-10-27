module

public import CFSG.RankThree.FFModules.Offenders

public section

namespace CFSG.RankThree.FFModules

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem rep_apply_mem_fixSub_of_conj_mem (ρ : Representation (ZMod 2) G W) {g : G}
    {A : Subgroup G} (hA : ∀ h ∈ A, g⁻¹ * h * g ∈ A) {w : W} (hw : w ∈ fixSub ρ A) :
    ρ g w ∈ fixSub ρ A := by
  intro a ha
  have hw' : ρ (g⁻¹ * a * g) w = w := hw _ (hA a ha)
  have e : a * g = g * (g⁻¹ * a * g) := by group
  calc ρ a (ρ g w) = ρ (a * g) w := by rw [map_mul, Module.End.mul_apply]
    _ = ρ (g * (g⁻¹ * a * g)) w := by rw [e]
    _ = ρ g (ρ (g⁻¹ * a * g) w) := by rw [map_mul, Module.End.mul_apply]
    _ = ρ g w := by rw [hw']

theorem rep_apply_mem_fixSub_of_normal (ρ : Representation (ZMod 2) G W) {A : Subgroup G}
    (hA : A.Normal) (g : G) {w : W} (hw : w ∈ fixSub ρ A) : ρ g w ∈ fixSub ρ A :=
  rep_apply_mem_fixSub_of_conj_mem ρ (fun h hh => by simpa using hA.conj_mem h hh g⁻¹) hw

end CFSG.RankThree.FFModules
