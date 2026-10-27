module

public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertex

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]
variable {H : Subgroup G} {X : Type} [Group X]
variable {L N : Subgroup G}

@[expose] noncomputable def sectionAction (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) : ↥H →* MulAut ↥(Ch3z.chiefMod L N) :=
  (Ch3z.chiefAut H L N).subtype.comp (Ch3z.chiefHom hHL hHN)

theorem sectionAction_apply (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) (h : ↥H) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    sectionAction hHL hHN hE h =
      ((Ch3z.chiefHom hHL hHN h : Ch3z.chiefAut H L N) :
        MulAut (Ch3z.chiefMod L N)) := by
  simp [sectionAction]

@[expose] noncomputable def sectionQuotAction (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 H ≤ centralizerMod L H N) :
    oTwoQuot ↥H →* MulAut ↥(Ch3z.chiefMod L N) :=
  QuotientGroup.lift (pCore 2 ↥H) (sectionAction hHL hHN hE) (by
    intro r hr
    rw [MonoidHom.mem_ker]
    have hrO : (r : G) ∈ pCoreOf 2 H := Subgroup.mem_map.mpr ⟨r, hr, rfl⟩
    have hcent : (r : G) ∈ centralizerMod L H N := hO hrO
    have h1 : Ch3z.chiefHom hHL hHN r = 1 :=
      (Ch3z.chiefHom_eq_one_iff hHL hHN hNL r).2 hcent
    change (sectionAction hHL hHN hE r : MulAut (Ch3z.chiefMod L N)) = 1
    rw [sectionAction_apply, h1]
    rfl)

theorem sectionQuotAction_mk (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 H ≤ centralizerMod L H N) (h : ↥H) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    sectionQuotAction hHL hHN hNL hE hO (QuotientGroup.mk h) =
      sectionAction hHL hHN hE h := by
  unfold sectionQuotAction
  exact QuotientGroup.lift_mk' (N := pCore 2 ↥H) (φ := sectionAction hHL hHN hE) _ h

@[expose] noncomputable def sectionXAction (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 H ≤ centralizerMod L H N)
    (e : oTwoQuot ↥H ≃* X) : X →* MulAut ↥(Ch3z.chiefMod L N) :=
  (sectionQuotAction hHL hHN hNL hE hO).comp e.symm.toMonoidHom

@[expose] noncomputable def sectionRep (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 H ≤ centralizerMod L H N)
    (e : oTwoQuot ↥H ≃* X) :
    @Representation (ZMod 2) X (Additive (Ch3z.chiefMod L N)) _ _
      (@Additive.addCommGroup (Ch3z.chiefMod L N)
        (l2ChiefSectionCommGroup hE)).toAddCommMonoid
      (l2ChiefSectionModule hE) := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  exact (CFSG.RankThree.FFModules.autRep (Ch3z.chiefMod L N)).comp
    (sectionXAction hHL hHN hNL hE hO e)

theorem sectionRep_apply (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 H ≤ centralizerMod L H N)
    (e : oTwoQuot ↥H ≃* X) (h : ↥H) (w : Ch3z.chiefMod L N) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
    sectionRep hHL hHN hNL hE hO e (e (QuotientGroup.mk h)) (Additive.ofMul w) =
      Additive.ofMul (sectionAction hHL hHN hE h w) := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  rw [sectionRep]
  change (CFSG.RankThree.FFModules.autRep (Ch3z.chiefMod L N))
    (sectionQuotAction hHL hHN hNL hE hO (e.symm (e (QuotientGroup.mk h))))
      (Additive.ofMul w) = _
  rw [MulEquiv.symm_apply_apply, sectionQuotAction_mk,
    CFSG.RankThree.FFModules.autRep_apply]
  rfl

end CFSG.Quasithin.Stroth

end
