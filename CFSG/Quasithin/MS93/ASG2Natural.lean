module

public import CFSG.Quasithin.MS93.ASBlocks
public import CFSG.Quasithin.Background.SmithB42U33

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin H13 H13.Orbit

variable {G : Type} [Group G] [Finite G]

theorem isG2BlockNatural_of_case10 {M T L : Subgroup G}
    (h : PUHyp M T L) (h10 : MS93Case10 M L) : IsG2BlockNatural L := by
  classical
  obtain ⟨hVX, hV, h10⟩ := h10
  obtain ⟨E, hE⟩ := B42U33.exists_equiv_of_g2NaturalDerived h10
  let A := ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆
  let D := FFModel.zornQ A
  let hD := FFModel.zornQ_isActionModel A (Subgroup.commutator_le_self _)
  have hinj : Function.Injective hD.modAct := by
    intro γ γ' heq
    have h1 : g2QAct (ZMod 2) ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩ =
        g2QAct (ZMod 2) ⟨γ'.1, Subgroup.commutator_le_self _ γ'.2⟩ :=
      MulEquiv.ext fun q => (B42U33.modAct_derived γ q).symm.trans
        ((congrArg (fun f : MulAut ModQ => f q) heq).trans
          (B42U33.modAct_derived γ' q))
    exact Subtype.ext
      (congrArg (fun x : ↥(quasithinG2 (ZMod 2)) => x.1) (g2QAct_injective h1))
  have hRange : hD.modAct.range = (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) := by
    ext f
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩, γ.2,
        MulEquiv.ext fun q => (B42U33.modAct_derived γ q).symm⟩
    · rintro ⟨δ, hδ, rfl⟩
      exact ⟨⟨δ.1, hδ⟩, MulEquiv.ext fun q => B42U33.modAct_derived ⟨δ.1, hδ⟩ q⟩
  let eA : ↥(autI hV L) ≃* ↥hD.modAct.range :=
    ((autI hV L).equivMapOfInjective (MulAut.congr E).toMonoidHom
      (MulAut.congr E).injective).trans (MulEquiv.subgroupCongr (hE.trans hRange.symm))
  have hLN : L ≤ Subgroup.normalizer (Vq M L : Set G) :=
    h.L_le.trans (le_normalizer_Vq h.le_normalizer)
  let c : ↥L →* ↥(autI hV L) :=
    (MulEquiv.subgroupCongr (range_convHom hV L hLN)).toMonoidHom.comp
      (convHom hV L hLN).rangeRestrict
  have hc : Function.Surjective c :=
    (MulEquiv.subgroupCongr (range_convHom hV L hLN)).surjective.comp
      (MonoidHom.rangeRestrict_surjective _)
  let α : ↥L →* ↥A :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (eA.toMonoidHom.comp c)
  have hα : Function.Surjective α :=
    (MonoidHom.ofInjective hinj).symm.surjective.comp (eA.surjective.comp hc)
  have hαker : α.ker = CFSG.pCore 2 ↥L := by
    have hker : (convHom hV L hLN).ker = CFSG.pCore 2 ↥L := by
      rw [ker_convHom, inf_centralizer_eq_pCoreOf h hVX, pCoreOf_subgroupOf]
    ext ℓ
    change (MonoidHom.ofInjective hinj).symm (eA (c ℓ)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, Subtype.ext_iff]
    change ℓ ∈ (convHom hV L hLN).ker ↔ _
    rw [hker]
  have hact (ℓ : ↥L) : hD.modAct (α ℓ) = MulAut.congr E (convHom hV L hLN ℓ) := by
    exact congrArg (fun x : ↥hD.modAct.range => x.1)
      ((MonoidHom.ofInjective hinj).apply_symm_apply (eA (c ℓ)))
  have hZ : blockZ L = ⊥ := by
    rw [blockZ_eq h]
    refine eq_bot_iff.mpr fun v hv => ?_
    let vI : IntMod (Vq M L) hV := IntMod.mk hV ⟨v, hv.1⟩
    have hvfix : vI ∈ fixV (autI hV L) :=
      (mem_fixV_autI hV hLN vI).2 hv.2
    have hq : E vI = 1 := by
      apply B42U33.eq_one_of_fixed_Q
      intro δ hδ
      have hm : g2QAct (ZMod 2) δ ∈ (autI hV L).map (MulAut.congr E).toMonoidHom := by
        rw [hE]
        exact ⟨δ, hδ, rfl⟩
      obtain ⟨φ, hφ, hφeq⟩ := hm
      calc
        g2QAct (ZMod 2) δ (E vI) = MulAut.congr E φ (E vI) :=
          congrArg (fun f : MulAut ModQ => f (E vI)) hφeq.symm
        _ = E (φ vI) := congr_apply_eq E φ vI
        _ = E vI := congrArg E (hvfix φ hφ)
    have hv1 : vI = 1 := E.injective (hq.trans E.map_one.symm)
    exact congrArg IntMod.val hv1
  let b : ↥(blockU L) ≃* IntMod (Vq M L) hV :=
    { toFun := fun u => IntMod.mk hV ⟨u, (blockU_eq h) ▸ u.2⟩
      invFun := fun v => ⟨v.val, (blockU_eq h).symm ▸ v.val_mem⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let β : ↥(blockU L) →* D.Mod := E.toMonoidHom.comp b.toMonoidHom
  refine ⟨α, hα, hαker, β, E.surjective.comp b.surjective, ?_, ?_⟩
  · rw [hZ, Subgroup.bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff β).2 (E.injective.comp b.injective)
  · intro ℓ u v representative hv hu
    have hconv : convHom hV L hLN ℓ (b u) = b v := by
      apply IntMod.val_injective
      rw [convHom_apply, convI_apply_val]
      exact hv.symm
    have hequiv : β v = hD.modAct (α ℓ) (β u) := by
      change E (b v) = hD.modAct (α ℓ) (E (b u))
      exact (congrArg E hconv).symm.trans
        ((congr_apply_eq E (convHom hV L hLN ℓ) (b u)).symm.trans
          (congrArg (fun f : MulAut ModQ => f (E (b u))) (hact ℓ).symm))
    refine ⟨hD.actSec (α ℓ) representative, rfl, ?_⟩
    exact hequiv.trans ((congrArg (hD.modAct (α ℓ)) hu).trans
      (hD.modEnd_mk (α ℓ) representative))

end CFSG.Quasithin.MS93
