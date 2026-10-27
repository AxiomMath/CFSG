module

public import CFSG.Quasithin.Background.B4ModelsApi

public section

namespace CFSG.Quasithin

namespace FFModel

variable {V : Type*} [CommGroup V]

@[expose] noncomputable def modEquivOfSurj {D D' : FFModel} (Ê : ↥D'.sec →* ↥D.sec)
    (hÊ : Function.Surjective Ê)
    (hker : ∀ m : ↥D'.sec, ((Ê m : ↥D.sec) : D.Amb) ∈ D.ker ↔ (m : D'.Amb) ∈ D'.ker) :
    D'.Mod ≃* D.Mod :=
  MulEquiv.ofBijective
    (QuotientGroup.map (D'.ker.subgroupOf D'.sec) (D.ker.subgroupOf D.sec) Ê
      (fun m hm => (hker m).2 hm))
    ⟨by
      rw [injective_iff_map_eq_one]
      intro q hq
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      rw [QuotientGroup.eq_one_iff]
      have hq' : (QuotientGroup.mk (Ê m) : D.Mod) = 1 := hq
      exact (hker m).1 ((QuotientGroup.eq_one_iff (Ê m)).mp hq'),
    by
      intro q
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨m, rfl⟩ := hÊ n
      exact ⟨QuotientGroup.mk m, rfl⟩⟩

theorem modEquivOfSurj_mk {D D' : FFModel} (Ê : ↥D'.sec →* ↥D.sec) (hÊ : Function.Surjective Ê)
    (hker : ∀ m : ↥D'.sec, ((Ê m : ↥D.sec) : D.Amb) ∈ D.ker ↔ (m : D'.Amb) ∈ D'.ker)
    (m : ↥D'.sec) :
    modEquivOfSurj Ê hÊ hker (QuotientGroup.mk m) = QuotientGroup.mk (Ê m) := rfl

theorem RealizesVia.of_surjHom {D D' : FFModel} (hD' : D'.IsActionModel)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) (θ : D'.Gam →* D.Gam) (hθ : Function.Surjective θ)
    (Ê : ↥D'.sec →* ↥D.sec) (hÊ : Function.Surjective Ê)
    (hact : ∀ (σ : D'.Gam) (m : ↥D'.sec) (hm : D'.act σ (m : D'.Amb) ∈ D'.sec),
      ((Ê ⟨D'.act σ (m : D'.Amb), hm⟩ : ↥D.sec) : D.Amb) =
        D.act (θ σ) ((Ê m : ↥D.sec) : D.Amb))
    (hker : ∀ m : ↥D'.sec, ((Ê m : ↥D.sec) : D.Amb) ∈ D.ker ↔ (m : D'.Amb) ∈ D'.ker) :
    D'.RealizesVia H U Z (π.comp θ) := by
  obtain ⟨hπs, hZU, -, hUinv, hZinv, hsec, -, β, hβs, hβk, hβe⟩ := h
  let E : D'.Mod ≃* D.Mod := modEquivOfSurj Ê hÊ hker
  have hQ : ∀ m : ↥D'.sec, E (QuotientGroup.mk m) = QuotientGroup.mk (Ê m) := fun m => rfl
  refine ⟨hπs.comp hθ, hZU, hD'.ker_le, hUinv, hZinv, hD'.sec_inv, hD'.ker_inv,
    E.symm.toMonoidHom.comp β, E.symm.surjective.comp hβs, fun u => ?_, ?_⟩
  · exact (E.symm.map_eq_one_iff).trans (hβk u)
  · intro γ u m hu hm hum
    have hβu : β u = QuotientGroup.mk (Ê m) := by
      have h1 : E.symm (β u) = QuotientGroup.mk m := hum
      have h2 : β u = E (QuotientGroup.mk m) := by
        rw [← h1]
        exact (E.apply_symm_apply _).symm
      rw [h2]
      exact hQ m
    have hm' : D.act (θ γ) ((Ê m : ↥D.sec) : D.Amb) ∈ D.sec := hsec (θ γ) _ (Ê m).2
    have h3 := hβe (θ γ) u (Ê m) hu hm' hβu
    show E.symm (β ⟨((π (θ γ) : ↥H) : MulAut V) (u : V), hu⟩) = _
    rw [h3, MulEquiv.symm_apply_eq]
    exact (congrArg QuotientGroup.mk (Subtype.ext (hact γ m hm)).symm).trans (hQ _).symm

end FFModel

end CFSG.Quasithin
