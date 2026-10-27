module

public import CFSG.Quasithin.Recognition.G112M13Core
public import CFSG.Quasithin.Recognition.G112M13Defs

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem concl13ModN_of_irr
    {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (N : Subgroup ↥Γ) (hd : Module.finrank (ZMod 2) V = 12)
    (hN : N.Normal) (hi : N.index = 2)
    (hH : IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22)
    (hirr : IsIrr (N.map Γ.subtype) ⊤) : G112Concl13ModN Γ := by
  let e0 : ↥N ≃* ↥(N.map Γ.subtype) := N.equivMapOfInjective Γ.subtype Γ.subtype_injective
  have hQL : CFSG.IsQuasisimple ↥(N.map Γ.subtype) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e0 hH.1
  have hqL : CFSG.Open.IsQuasisimple ↥(N.map Γ.subtype) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hQL
  have hcen : (Subgroup.center ↥N).map e0.toMonoidHom = Subgroup.center ↥(N.map Γ.subtype) :=
    Subgroup.map_center_eq e0
  have hZ : Nat.card ↥(Subgroup.center ↥(N.map Γ.subtype)) = 3 :=
    (Nat.card_congr (Subgroup.centerCongr e0).toEquiv).symm.trans hH.2.1
  obtain ⟨φ⟩ := hH.2.2
  have e : (↥(N.map Γ.subtype) ⧸ Subgroup.center ↥(N.map Γ.subtype)) ≃*
      CFSG.Blueprint.NativeSporadic.Carrier .M22 :=
    (QuotientGroup.congr _ _ e0 hcen).symm.trans φ
  obtain ⟨ψ, hψ⟩ := (case2_model_core hqL hZ e hirr hd.le).2
  exact ⟨hd, N, hN, hi, hH, ψ, hψ⟩

end CFSG.Quasithin.G112A2
