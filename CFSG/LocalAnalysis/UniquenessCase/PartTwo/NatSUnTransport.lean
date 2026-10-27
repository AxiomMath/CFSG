module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.HSecTransfer
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Background.SmithB51LnSub

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

@[expose] noncomputable def restrictTopAutEquiv (K' : Subgroup (MulAut W)) :
    ↥K' ≃* ↥(autSub K' (⊤ : Subgroup W)) :=
  let f : ↥K' →* ↥(autSub K' (⊤ : Subgroup W)) :=
    ((resHom (⊤ : Subgroup W)).comp
      (Subgroup.inclusion (le_stabSub_top K'))).codRestrict (autSub K' (⊤ : Subgroup W))
      fun k => mem_autSub.mpr
        ⟨Subgroup.inclusion (le_stabSub_top K') k, k.2, rfl⟩
  MulEquiv.ofBijective f
    (show Function.Bijective ⇑f from
      ⟨fun a b hab => Subgroup.inclusion_injective _
          (resHom_top_injective (congrArg Subtype.val hab)),
        fun x => by
          obtain ⟨g, hgX, hg⟩ := mem_autSub.mp x.2
          refine ⟨⟨(g : MulAut W), hgX⟩, Subtype.ext ?_⟩
          change (resHom (⊤ : Subgroup W)) (Subgroup.inclusion (le_stabSub_top K')
            (⟨(g : MulAut W), hgX⟩ : ↥K')) = (x : MulAut ↥(⊤ : Subgroup W))
          rw [show Subgroup.inclusion (le_stabSub_top K')
              (⟨(g : MulAut W), hgX⟩ : ↥K') = g from Subtype.ext rfl, hg]⟩)

theorem restrictTopAutEquiv_apply_coe (K' : Subgroup (MulAut W)) (k : ↥K')
    (u : ↥(⊤ : Subgroup W)) :
    (((restrictTopAutEquiv K' k : ↥(autSub K' (⊤ : Subgroup W))) :
        MulAut ↥(⊤ : Subgroup W)) u) =
      (⟨(k : MulAut W) u, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) := by
  change (resHom (⊤ : Subgroup W))
    (Subgroup.inclusion (le_stabSub_top K') k) u = _
  rfl

theorem quotHom_bot_injective :
    Function.Injective (quotHom (⊥ : Subgroup (⊤ : Subgroup W))) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_quotHom, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf, mem_centQuot] at hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  have h := hg w
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h
  simpa using h

@[expose] noncomputable def autQuotBotEquiv (X : Subgroup (MulAut (⊤ : Subgroup W))) :
    ↥X ≃* ↥(autQuot X (⊥ : Subgroup (⊤ : Subgroup W))) :=
  let f : ↥X →* ↥(autQuot X (⊥ : Subgroup (⊤ : Subgroup W))) :=
    ((quotHom (⊥ : Subgroup (⊤ : Subgroup W))).comp
      (Subgroup.inclusion (B5.Ln.stabSub_bot_le X))).codRestrict
      (autQuot X (⊥ : Subgroup (⊤ : Subgroup W)))
      fun x => mem_autQuot.mpr
        ⟨Subgroup.inclusion (B5.Ln.stabSub_bot_le X) x, x.2, rfl⟩
  MulEquiv.ofBijective f
    (show Function.Bijective ⇑f from
      ⟨fun a b hab => Subgroup.inclusion_injective _
          (quotHom_bot_injective (congrArg Subtype.val hab)),
        fun x => by
          obtain ⟨g, hgX, hg⟩ := mem_autQuot.mp x.2
          refine ⟨⟨(g : MulAut ↥(⊤ : Subgroup W)), hgX⟩, Subtype.ext ?_⟩
          change (quotHom (⊥ : Subgroup (⊤ : Subgroup W)))
            (Subgroup.inclusion (B5.Ln.stabSub_bot_le X)
              (⟨(g : MulAut ↥(⊤ : Subgroup W)), hgX⟩ : ↥X)) =
            (x : MulAut (↥(⊤ : Subgroup W) ⧸ (⊥ : Subgroup (⊤ : Subgroup W))))
          rw [show Subgroup.inclusion (B5.Ln.stabSub_bot_le X)
              (⟨(g : MulAut ↥(⊤ : Subgroup W)), hgX⟩ : ↥X) = g from Subtype.ext rfl, hg]⟩)

theorem autQuotBotEquiv_apply_mk (X : Subgroup (MulAut (⊤ : Subgroup W))) (x : ↥X)
    (u : ↥(⊤ : Subgroup W)) :
    (((autQuotBotEquiv X x : ↥(autQuot X (⊥ : Subgroup (⊤ : Subgroup W)))) :
        MulAut (↥(⊤ : Subgroup W) ⧸ (⊥ : Subgroup (⊤ : Subgroup W))))
      (QuotientGroup.mk u)) = QuotientGroup.mk ((x : MulAut ↥(⊤ : Subgroup W)) u) := by
  change (quotHom (⊥ : Subgroup (⊤ : Subgroup W)))
    (Subgroup.inclusion (B5.Ln.stabSub_bot_le X) x) (QuotientGroup.mk u) = _
  rw [quotHom_mk]
  rfl

theorem realizes_of_autQuot_autSub_top_bot {W : Type} [CommGroup W]
    (Dm : CFSG.Quasithin.FFModel) {K' : Subgroup (MulAut W)} {U : Subgroup W}
    {C : Subgroup ↥U} (hU : U = ⊤) (hC : C = ⊥)
    (h : Dm.Realizes (autQuot (autSub K' U) C) ⊤ ⊥) : Dm.Realizes K' ⊤ ⊥ := by
  subst hC
  subst hU
  let X : Subgroup (MulAut (⊤ : Subgroup W)) := autSub K' (⊤ : Subgroup W)
  let r : ↥K' ≃* ↥(autQuot X (⊥ : Subgroup (⊤ : Subgroup W))) :=
    (restrictTopAutEquiv K').trans (autQuotBotEquiv X)
  refine CFSG.Quasithin.H.FFModel.realizes_of_equiv (V := W)
    (W := (↥(⊤ : Subgroup W) ⧸ (⊥ : Subgroup (⊤ : Subgroup W))))
    (D := Dm) (H := K') (U := ⊤) (K := autQuot (autSub K' ⊤) ⊥)
    (fun _ _ _ _ => Subgroup.mem_top _) QuotientGroup.quotientBot.symm r ?_ h
  intro k u
  change ((((restrictTopAutEquiv K').trans (autQuotBotEquiv X)) k :
      ↥(autQuot X (⊥ : Subgroup (⊤ : Subgroup W)))) :
      MulAut (↥(⊤ : Subgroup W) ⧸ (⊥ : Subgroup (⊤ : Subgroup W))))
      (QuotientGroup.quotientBot.symm u) = _
  rw [QuotientGroup.quotientBot_symm_apply, MulEquiv.trans_apply, autQuotBotEquiv_apply_mk,
    restrictTopAutEquiv_apply_coe, QuotientGroup.quotientBot_symm_apply]

theorem natSUn_of_autQuot_autSub_top_bot {W : Type} [CommGroup W]
    {K' : Subgroup (MulAut W)} {U : Subgroup W} {C : Subgroup ↥U}
    (hU : U = ⊤) (hC : C = ⊥) {m a : ℕ}
    (h : NatSUn (autQuot (autSub K' U) C) ⊤ ⊥ m a) : NatSUn K' ⊤ ⊥ m a := by
  obtain ⟨K, hK, hfin, hcard, hreal⟩ := h
  exact ⟨K, hK, hfin, hcard, realizes_of_autQuot_autSub_top_bot _ hU hC hreal⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
