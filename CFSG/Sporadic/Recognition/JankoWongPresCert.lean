module

public import CFSG.Sporadic.Recognition.JankoWongPres
public import Certificates.Certificate6104

public section

namespace CFSG.Sporadic.Recognition.JankoWong

theorem jwFacts_holds : JWFacts false ∧ JWFacts true :=
  ⟨⟨(Certificates.certificate6104 false).1, (Certificates.certificate6104 false).2.2.2⟩,
    ⟨(Certificates.certificate6104 true).1, (Certificates.certificate6104 true).2.2.2⟩⟩

theorem nonempty_jwPresented_mulEquiv_mcl
    (neg : Bool) :
    Nonempty (jwPresented neg ≃* CFSG.Blueprint.NativeSporadic.McL) := by
  refine ⟨jwPresentedEquivMcL (neg := neg) ?_⟩
  cases neg
  · exact jwFacts_holds.1
  · exact jwFacts_holds.2

theorem exists_mulEquiv_mcl_of_relations_of_certificate
    {G : Type*} [Group G] {ι : ℤˣ} {e : JWElements G}
    (hrel : JWRelations ι e) (hK : Subgroup.closure e.gens ≠ ⊥) :
    Nonempty (Subgroup.closure e.gens ≃* CFSG.Blueprint.NativeSporadic.McL) :=
  exists_mulEquiv_mcl_of_relations hrel jwFacts_holds hK

theorem lift_eq_one_of_relations_of_certificate
    {G : Type*} [Group G] {ι : ℤˣ} {e : JWElements G}
    (hrel : JWRelations ι e) {w : FreeGroup (Fin 6)}
    (hw : FreeGroup.lift (jwGen (decide (ι = -1))) w = 1) : FreeGroup.lift e.gen w = 1 :=
  lift_eq_one_of_relations hrel jwFacts_holds hw

end CFSG.Sporadic.Recognition.JankoWong
