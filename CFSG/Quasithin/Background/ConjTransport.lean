module

public import CFSG.Quasithin.Background.FixVTransport
public import CFSG.Quasithin.Background.CommVBasics

public section

namespace CFSG.Quasithin.ConjTransport

variable {V : Type*} [CommGroup V]

theorem mem_fixV_map_conj_iff {g : MulAut V} {X : Subgroup (MulAut V)} {v : V} :
    v ∈ fixV (X.map (MulAut.conj g).toMonoidHom) ↔ g⁻¹ v ∈ fixV X := by
  rw [fixV_map_conj_eq]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨g⁻¹ v, h, by simp⟩

theorem card_fixV_map_conj (X : Subgroup (MulAut V)) (g : MulAut V) :
    Nat.card (fixV (X.map (MulAut.conj g).toMonoidHom)) = Nat.card (fixV X) := by
  rw [fixV_map_conj_eq]
  exact (Nat.card_congr ((fixV X).equivMapOfInjective g.toMonoidHom g.injective).toEquiv).symm

theorem index_fixV_map_conj (X : Subgroup (MulAut V)) (g : MulAut V) :
    (fixV (X.map (MulAut.conj g).toMonoidHom)).index = (fixV X).index := by
  rw [fixV_map_conj_eq]
  exact Subgroup.index_map_equiv (fixV X) (g : V ≃* V)

theorem mem_commV_map_conj_iff {g : MulAut V} {X : Subgroup (MulAut V)} {v : V} :
    v ∈ commV (X.map (MulAut.conj g).toMonoidHom) ↔ g⁻¹ v ∈ commV X := by
  rw [commV_map_conj_eq]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨g⁻¹ v, h, by simp⟩

theorem card_commV_map_conj (X : Subgroup (MulAut V)) (g : MulAut V) :
    Nat.card (commV (X.map (MulAut.conj g).toMonoidHom)) = Nat.card (commV X) := by
  rw [commV_map_conj_eq]
  exact (Nat.card_congr ((commV X).equivMapOfInjective g.toMonoidHom g.injective).toEquiv).symm

end CFSG.Quasithin.ConjTransport
