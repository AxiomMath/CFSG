module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss113Core
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss18Basic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecIrred

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod

theorem hss18S5_holds (G : Type) [Group G] [Finite G] :
    ∀ X P Z : Subgroup G, PushHyp X P Z → Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)) →
      ¬ thompsonJ P ≤ pCoreOf 2 X →
      IsNatSec X (zZero X Z) Z ∨ IsOrthSec X (zZero X Z) Z := by
  intro X P Z h he hJ
  obtain ⟨θ, hθ, hker⟩ := exists_toPerm_of_quot he
  obtain ⟨A, hA, hAQ⟩ := exists_offender hJ
  have hcore := hss113_core (X := X) (Z := Z) (Y := A) (Q' := Subgroup.centralizer (A : Set G)) θ
    hθ hker h.elemAbelian h.normal h.cent_eq (hA.1.trans h.le_self) hA.2.1
    (fun y hy q hq => Subgroup.mem_centralizer_iff.mp hq y hy) hAQ (offender_count h hA)
  rw [zZero, pResidualOf_eq_oTwoRes]
  exact hcore.2

end CFSG.Quasithin.F53Push
