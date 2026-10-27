module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzCount
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Certificates.Certificate551201

public section

namespace CFSG.Quasithin.H13

theorem pCore_transport {A B : Type} [Group A] [Group B] (f : A ≃* B) (U : Subgroup A) :
    CFSG.pCore 2 ↥U = ⊥ ↔ CFSG.pCore 2 ↥(U.map f.toMonoidHom) = ⊥ := by
  let e : ↥U ≃* ↥(U.map f.toMonoidHom) := U.equivMapOfInjective f.toMonoidHom f.injective
  have h := CFSG.pCore_map_iso 2 e
  constructor
  · intro h0
    rw [← h, h0, Subgroup.map_bot]
  · intro h0
    rw [← h] at h0
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have h2 : e.toMonoidHom y ∈ (CFSG.pCore 2 ↥U).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hy
    rw [h0, Subgroup.mem_bot] at h2
    apply e.injective
    rw [map_one]
    exact h2

theorem card_map_eq {A B : Type} [Group A] [Group B] (f : A ≃* B) (U : Subgroup A) :
    Nat.card ↥(U.map f.toMonoidHom) = Nat.card ↥U :=
  (Nat.card_congr (U.equivMapOfInjective f.toMonoidHom f.injective).toEquiv).symm

theorem m11Sub144O2_kz_holds : M11Sub144O2_kz := by
  unfold M11Sub144O2_kz
  intro Q _ _ hQ U hU
  obtain ⟨e⟩ := hQ
  have e' : Q ≃* ↥CFSG.Blueprint.NativeSporadic.M11 := e
  have hU' : Nat.card (U.map e'.toMonoidHom) = 144 := by
    rw [card_map_eq e' U, hU]
  exact (pCore_transport e' U).mpr (Certificates.certificate551201 _ hU')

end CFSG.Quasithin.H13

end
