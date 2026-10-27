module

public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.Background.G64Realize

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem altDn_faithful {n : ℕ} (hn : 5 ≤ n) : (FFModel.altDn n).Faithful := by
  intro (σ : ↥(alternatingGroup (Fin n))) hσ
  exact Subtype.ext (G64.symDn_faithful hn (σ : Equiv.Perm (Fin n)) hσ)

theorem altCoreModel_faithful {n : ℕ} (hn : 3 ≤ n) : (altCoreModel n).Faithful := by
  intro (σ : ↥(alternatingGroup (Fin n))) hσ
  exact Subtype.ext (G64.symCore_faithful hn (σ : Equiv.Perm (Fin n)) hσ)

theorem nonempty_mulEquiv_of_realizes {V : Type*} [CommGroup V] {D : FFModel} (hD : D.Faithful)
    {H : Subgroup (MulAut V)} (h : D.Realizes H ⊤ ⊥) : Nonempty (↥H ≃* D.Gam) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨(MulEquiv.ofBijective π ⟨hπ.injective_of_faithful hD, hπ.1⟩).symm⟩

variable {G : Type} [Group G]

@[expose] noncomputable def autOnHom {L V : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (V : Set G)) : ↥L →* ↥(autOn L V) :=
  ((conjAct V).subgroupMap (L.subgroupOf (Subgroup.normalizer (V : Set G)))).comp
    (Subgroup.subgroupOfEquivOfLe hL).symm.toMonoidHom

theorem autOnHom_apply {L V : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G)) (l : ↥L) :
    ((autOnHom hL l : ↥(autOn L V)) : MulAut ↥V) = conjAct V ⟨l, hL l.2⟩ := rfl

theorem autOnHom_surjective {L V : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (autOnHom hL) :=
  (MonoidHom.subgroupMap_surjective _ _).comp (MulEquiv.surjective _)

theorem exists_surjective_autOn {L V : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (V : Set G)) :
    ∃ φ : ↥L →* ↥(autOn L V), Function.Surjective φ :=
  ⟨autOnHom hL, autOnHom_surjective hL⟩

end CFSG.Quasithin.H13.A6
