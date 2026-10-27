module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4RigidMap
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4RigidModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4YAmalgam
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Simple

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex


theorem d4AmalgamRigid_holds : D4AmalgamRigid := by
  intro D' _ hD' TD P₁ P₂ hY
  obtain ⟨e⟩ := nonempty_equiv_trialityGroup8 D' hD'
  have hs : IsSimpleGroup D := d4_isSimpleGroup hD'
  obtain ⟨x, -, hP⟩ := d4_yamalgam_classify hs (IsYAmalgamPair.map e hY)
  let ε : D' ≃* D := e.trans (MulAut.conj x)
  have hε : ∀ P : Subgroup D', (P.map e.toMonoidHom).map (MulAut.conj x).toMonoidHom =
      P.map ε.toMonoidHom := fun P => by
    rw [Subgroup.map_map]
    rfl
  refine amalgamRigid_of_map ε ?_
  rcases hP with ⟨hP1, hP2⟩ | ⟨hP1, hP2⟩
  · rw [← hε, ← hε, hP1, hP2]
    exact amalgamRigid_d4 hs
  · rw [← hε, ← hε, hP1, hP2]
    exact amalgamRigid_symm (amalgamRigid_d4 hs)

end CFSG.Quasithin.D4Hex
