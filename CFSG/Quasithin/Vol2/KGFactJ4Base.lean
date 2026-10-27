module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocDef

public section

namespace CFSG.Quasithin.KGJ4

open CFSG.Sporadic.J4

@[expose] noncomputable def w1 : J := ((a * b ^ 3) ^ 4)⁻¹ * a * (a * b ^ 3) ^ 4

@[expose] noncomputable def w2 : J := ((a * b) ^ 8)⁻¹ * b * (a * b) ^ 8

@[expose] noncomputable def M4 : Subgroup J := Subgroup.closure {w1, w2}

theorem w1_mem_M4 : w1 ∈ M4 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem w2_mem_M4 : w2 ∈ M4 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def J4TwoLocalsKW : Prop :=
  ∀ P : Subgroup J, IsPGroup 2 ↥P → P ≠ ⊥ → ∃ g : J,
    Subgroup.normalizer (P : Set J) ≤ Hj.map (MulAut.conj g).toMonoidHom ∨
    Subgroup.normalizer (P : Set J) ≤
      (Subgroup.centralizer ({J4Loc.z0} : Set J)).map (MulAut.conj g).toMonoidHom ∨
    Subgroup.normalizer (P : Set J) ≤
      (Subgroup.normalizer (J4Loc.V0 : Set J)).map (MulAut.conj g).toMonoidHom ∨
    Subgroup.normalizer (P : Set J) ≤ M4.map (MulAut.conj g).toMonoidHom

end CFSG.Quasithin.KGJ4
