module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieIsoB
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructLoc
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYam

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.D4q.Struct

@[expose] def UnOutConcl5 {D : Type} [Group D] (A : LieAmalgamExt D) : Prop :=
  ∃ (T S : Subgroup ↥A.K) (g z t : ↥A.K) (V : Subgroup ↥A.K),
    F431UnOut T S g A.Mb1 A.Mb2 z t V ∨ F431UnOut T S g A.Mb2 A.Mb1 z t V

theorem unOutConcl5_of_kiso {D D' : Type} [Group D] [Group D'] {A : LieAmalgamExt D}
    {A' : LieAmalgamExt D'} (L : KIso A A') : UnOutConcl5 A' → UnOutConcl5 A := by
  rintro ⟨T', S', g', z', t', V', hD | hD⟩
  · refine ⟨T'.map L.ψ.symm.toMonoidHom, S'.map L.ψ.symm.toMonoidHom, L.ψ.symm g', L.ψ.symm z',
      L.ψ.symm t', V'.map L.ψ.symm.toMonoidHom, Or.inl ?_⟩
    have := F431UnOut.map L.ψ.symm hD
    rwa [L.map_Mb1, L.map_Mb2] at this
  · refine ⟨T'.map L.ψ.symm.toMonoidHom, S'.map L.ψ.symm.toMonoidHom, L.ψ.symm g', L.ψ.symm z',
      L.ψ.symm t', V'.map L.ψ.symm.toMonoidHom, Or.inr ?_⟩
    have := F431UnOut.map L.ψ.symm hD
    rwa [L.map_Mb1, L.map_Mb2] at this

theorem un5_map_conj_conj_inv {H : Type} [Group H] (U : Subgroup H) (c : H) :
    (U.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = U := by
  rw [Subgroup.map_map]
  have : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id H := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

theorem un5_map_refl {H : Type} [Group H] (X : Subgroup H) :
    X.map (MulEquiv.refl H).toMonoidHom = X := by
  ext x
  simp

theorem un5_exists_normalized {D Y : Type} [Group D] [Group Y] [Finite Y] {U P₀ P₁ : Subgroup Y}
    (hY : CFSG.Quasithin.H13.Sec53F.Yam.YamStd Y U P₀ P₁) (e : D ≃* Y) (A : LieAmalgamExt D) :
    ∃ A' : LieAmalgamExt Y, A'.TD = U ∧
      ((A'.P1 = P₀ ∧ A'.P2 = P₁) ∨ (A'.P1 = P₁ ∧ A'.P2 = P₀)) ∧ Nonempty (KIso A A') := by
  let E1 : LieExt Y A.N1 A.N2 := A.toLieExt.congr e
  let L1 : LocIso A.toLieExt E1 := A.toLieExt.congrOfLocIso e _ rfl
  obtain ⟨c, hTD, hP⟩ := hY.pair (MulEquiv.refl Y) E1.yam
  rw [un5_map_refl] at hTD
  let E2 : LieExt Y A.N1 A.N2 := E1.conjSylow c⁻¹
  let L2 : LocIso E1 E2 :=
    E1.congrOfLocIso (MulAut.conj c⁻¹) E1.Mbar (E1.Mbar_eq_map_conj c⁻¹)
  refine ⟨E2.toLieAmalgamExt, ?_, ?_, ⟨(L1.trans L2).toKIso⟩⟩
  · show E1.TD.map (MulAut.conj c⁻¹).toMonoidHom = _
    rw [hTD, un5_map_conj_conj_inv]
  · show (E1.P1.map (MulAut.conj c⁻¹).toMonoidHom = _ ∧
        E1.P2.map (MulAut.conj c⁻¹).toMonoidHom = _) ∨
      (E1.P1.map (MulAut.conj c⁻¹).toMonoidHom = _ ∧
        E1.P2.map (MulAut.conj c⁻¹).toMonoidHom = _)
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [un5_map_refl] at h1 h2
      left
      rw [h1, h2, un5_map_conj_conj_inv, un5_map_conj_conj_inv]
      exact ⟨rfl, rfl⟩
    · rw [un5_map_refl] at h1 h2
      right
      rw [h1, h2, un5_map_conj_conj_inv, un5_map_conj_conj_inv]
      exact ⟨rfl, rfl⟩

end CFSG.Quasithin.H13.F431.Un.OL5
