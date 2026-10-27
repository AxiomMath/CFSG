module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.Quasithin.Background.G10Basic
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace SzN28P

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [Finite V] in
theorem isSolvable_of_concl1 {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (h : G112Concl1 Γ) :
    Group.IsSolvable ↥Γ := by
  obtain ⟨-, ⟨e⟩⟩ := h
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem isSolvable_of_concl3 {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (h : G112Concl3 Γ) :
    Group.IsSolvable ↥Γ := by
  obtain ⟨-, P, hPn, -, hcard, -, hidx, -⟩ := h
  have : P.Normal := hPn
  have hP3 : IsPGroup 3 ↥P := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have : Group.IsNilpotent ↥P := hP3.isNilpotent
  obtain ⟨m, -, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 4)).mp (by simpa using hidx)
  have hQ2 : IsPGroup 2 (↥Γ ⧸ P) := IsPGroup.of_card (n := m) (by
    rw [← Subgroup.index_eq_card]
    exact hm')
  have : Group.IsNilpotent (↥Γ ⧸ P) := hQ2.isNilpotent
  exact Group.isSolvable_of_subgroup_quotient P

end SzN28P

end CFSG.Quasithin
