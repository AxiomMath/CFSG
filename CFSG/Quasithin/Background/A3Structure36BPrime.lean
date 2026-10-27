
module

public import CFSG.Quasithin.Background.A3Structure36BPrimeBase

public import CFSG.Quasithin.Background.A3Structure36BFrattini

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Open

variable {X : Type} [Group X]

theorem PrimeData.characteristic {q : ℕ} (D : PrimeData X q) : D.P.Characteristic :=
  D.supercritical.characteristic

@[expose] def PrimeData.P' {q : ℕ} (D : PrimeData X q) : Subgroup X :=
  D.P.map (CFSG.pCore q X).subtype

theorem PrimeData.mem_K_iff {q : ℕ} (D : PrimeData X q) (x : X) :
    x ∈ D.K ↔ ActsTriviallyOnFrattiniQuotient D.P' x := by
  have := D.characteristic
  rw [PrimeData.P', ← mem_ker_frattiniAction_conjNormal (CFSG.pCore q X) D.P x,
    MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, mem_ker_frattiniAction_iff]
  exact D.mem_K x

end CFSG.Quasithin.A36B
