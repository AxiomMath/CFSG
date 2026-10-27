module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.B5Basic

public section

namespace CFSG.Quasithin

namespace FFC

namespace Sp4Off

open CFSG.Quasithin.B5

variable {V : Type} [CommGroup V] {W U : Subgroup V} {L : Subgroup (MulAut V)}

theorem realizesVia_autSec (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U)
    (hfaith : L ⊓ centSec W U = ⊥) {D : FFModel} {π : D.Gam →* ↥L}
    (h : D.RealizesVia L W U π) :
    D.RealizesVia (autSec L W U) (⊤ : Subgroup (Sec W U)) ⊥
      ((secEquiv L hLW hLU hfaith).toMonoidHom.comp π) := by
  obtain ⟨hsurj, -, hkerle, -, -, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  have hker : U.subgroupOf W ≤ β.ker := fun u hu => (hβk u).2 hu
  let β₀ : Sec W U →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    QuotientGroup.lift (U.subgroupOf W) β hker
  have hβ₀ : ∀ w : ↥W, β₀ (QuotientGroup.mk w) = β w := fun w => rfl
  let β' : ↥(⊤ : Subgroup (Sec W U)) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    β₀.comp (⊤ : Subgroup (Sec W U)).subtype
  refine ⟨(secEquiv L hLW hLU hfaith).surjective.comp hsurj, bot_le, hkerle,
    fun _ _ _ => trivial, fun g z hz => ?_, hsec, hkerinv, β', ?_, ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro y
    obtain ⟨w, rfl⟩ := hβs y
    exact ⟨⟨QuotientGroup.mk w, trivial⟩, rfl⟩
  · rintro ⟨s, -⟩
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
    change β₀ (QuotientGroup.mk w) = 1 ↔ (QuotientGroup.mk w : Sec W U) ∈ ⊥
    rw [hβ₀, hβk, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · rintro γ ⟨s, hs⟩ m hu' hm hsm
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
    have hπ : (((secEquiv L hLW hLU hfaith).toMonoidHom.comp π γ : ↥(autSec L W U)) :
        MulAut (Sec W U)) = secHom L hLW hLU (π γ) :=
      secEquiv_apply L hLW hLU hfaith (π γ)
    have hu : (((π γ : ↥L) : MulAut V)) (w : V) ∈ W := (hLW (π γ).2 w).2 w.2
    have key := hβe γ w m hu hm hsm
    change β₀ ((((secEquiv L hLW hLU hfaith).toMonoidHom.comp π γ : ↥(autSec L W U)) :
      MulAut (Sec W U)) (QuotientGroup.mk w)) = _
    rw [hπ, secHom_mk, hβ₀]
    exact key

end Sp4Off

end FFC

end CFSG.Quasithin
