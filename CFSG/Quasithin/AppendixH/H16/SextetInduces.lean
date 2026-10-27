module

public import CFSG.Quasithin.AppendixH.H16.SextetAction
public import CFSG.Quasithin.AppendixH.H16.N6Coord

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.LU CFSG.Monster.Code
  CFSG.Open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc
  CFSG.Quasithin.MS93

@[expose] noncomputable def usCrd : ↥US →* Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2) :=
  n6Crd.comp usTheta.toMonoidHom

theorem usCrd_bijective : Function.Bijective usCrd :=
  n6Crd_bijective.comp usTheta.bijective

theorem usCrd_rhoOf (σ : Equiv.Perm (Fin 6)) (u : ↥US) :
    usCrd ((B42Alt6.rhoOf usTheta σ) u) =
      natHomI (Fin 2 ⊕ Fin 2) (ZMod 2)
        ((S6B.thetaTwo σ : ↥(StatedSp 2 (ZMod 2))) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (usCrd u) := by
  rw [show usCrd ((B42Alt6.rhoOf usTheta σ) u) =
      n6Crd (S143.n6Act σ (usTheta u)) from
    congrArg n6Crd (B42Alt6.rhoOf_apply usTheta σ u)]
  exact n6Crd_act_natHomI σ (usTheta u)

theorem inducesOn_imgCd_sxGen :
    InducesOn (imgCd sxGen) US ⊥ (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2))
      (natSubI (Fin 2 ⊕ Fin 2) (ZMod 2) (StatedSp 2 (ZMod 2))) := by
  refine ⟨bot_le, ?_, ?_, usCrd, usCrd_bijective.2, ?_, ?_, ?_⟩
  · intro g hg u hu
    exact (mem_stabSub.mp (imgCd_sxGen_le_stabSub hg) (u : W11)).mpr hu
  · intro g hg z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz]
    exact g.map_one
  · intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h
      have hu : u = 1 := usCrd_bijective.1 (h.trans usCrd.map_one.symm)
      exact congrArg (fun x : ↥US => (x : W11)) hu
    · intro h
      rw [show u = 1 from Subtype.ext h]
      exact usCrd.map_one
  · rintro g hg
    let gs : stabSub US := ⟨g, imgCd_sxGen_le_stabSub hg⟩
    have hgs : resHom US gs ∈ (B42Alt6.rhoOf usTheta).range := by
      rw [← autSub_imgCd_sxGen]
      exact mem_autSub.2 ⟨gs, hg, rfl⟩
    obtain ⟨σ, hσ⟩ := hgs
    refine ⟨natHomI (Fin 2 ⊕ Fin 2) (ZMod 2)
      ((S6B.thetaTwo σ : ↥(StatedSp 2 (ZMod 2))) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)),
      (mem_natSubI_iff _).2 ⟨σ, rfl⟩, ?_⟩
    intro u u' hu
    have hu' : u' = resHom US gs u := Subtype.ext (by
      change (u' : W11) = g (u : W11)
      exact hu)
    rw [hu', ← hσ]
    exact usCrd_rhoOf σ u
  · rintro γ hγ
    obtain ⟨σ, rfl⟩ := (mem_natSubI_iff γ).1 hγ
    have hmem : B42Alt6.rhoOf usTheta σ ∈ autSub (imgCd sxGen) US := by
      rw [autSub_imgCd_sxGen]
      exact ⟨σ, rfl⟩
    obtain ⟨gs, hgsX, hgsr⟩ := mem_autSub.1 hmem
    refine ⟨gs.1, hgsX, ?_⟩
    intro u u' hu
    have hu' : u' = resHom US gs u := Subtype.ext (by
      change (u' : W11) = gs.1 (u : W11)
      exact hu)
    rw [hu', hgsr]
    exact usCrd_rhoOf σ u

end CFSG.ASVolI.H16
