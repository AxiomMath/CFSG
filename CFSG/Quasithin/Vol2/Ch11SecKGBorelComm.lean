module

public import CFSG.Quasithin.Vol2.Ch11SecBFactsHB
public import CFSG.Quasithin.Vol2.Ch11SecKGBCb
public import CFSG.Quasithin.Vol2.Ch11SecKGBCe
public import CFSG.Quasithin.Vol2.Ch11SecKGBCf
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem factBorelComm_holds : FactBorelComm := by
  intro Y Y' _ _ _ _ n φ _ hφ _ hZ hodd htype S' hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases htype with hB | ⟨-, K, _, _, hK, ⟨e⟩⟩ | ⟨-, K, _, _, hK, ⟨e⟩⟩
  · exact C10KG.isPGroup_commutator_bender φ hφ hZ hodd hB hS
  · have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    let e' : Y' ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
      e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          3 K))
    obtain ⟨Q, rfl⟩ := C10KG.exists_sylow_of_isSylowTwoOf hS
    refine C10KG.isPGroup_commutator_of_mulEquiv φ e' Q ?_
    exact C10KG.isPGroup_commutator_l3 (e'.toMonoidHom.comp φ) (e'.surjective.comp hφ)
      ((C10KG.ker_comp_mulEquiv φ e').symm ▸ hZ) ((C10KG.ker_comp_mulEquiv φ e').symm ▸ hodd)
      (Q.mapSurjective (f := e'.toMonoidHom) e'.surjective)
  · have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    obtain ⟨Q, rfl⟩ := C10KG.exists_sylow_of_isSylowTwoOf hS
    refine C10KG.isPGroup_commutator_of_mulEquiv φ e Q ?_
    exact C10KG.isPGroup_commutator_sp4 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
      ((C10KG.ker_comp_mulEquiv φ e).symm ▸ hZ) ((C10KG.ker_comp_mulEquiv φ e).symm ▸ hodd)
      (Q.mapSurjective (f := e.toMonoidHom) e.surjective)

end CFSG.Quasithin.Vol2.Ch11.SecB
