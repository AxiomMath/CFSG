module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2Tr

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

@[expose] def AutIso.conjIso (iso : AutIso M₁ M₂) {g : G} (hg : g ∈ M₁ ⊓ M₂) : AutIso M₁ M₂ where
  φ1 := iso.φ1.trans (MulAut.conj (⟨g, hg.1⟩ : ↥M₁))
  φ12 := iso.φ12.trans (MulAut.conj (⟨g, hg⟩ : ↥(M₁ ⊓ M₂)))
  φ2 := iso.φ2.trans (MulAut.conj (⟨g, hg.2⟩ : ↥M₂))
  comm1 := fun x => by
    apply Subtype.ext
    have h := congrArg Subtype.val (iso.comm1 x)
    show g * Subtype.val (iso.φ12 x : ↥(M₁ ⊓ M₂)) * g⁻¹ =
      g * Subtype.val (iso.φ1 (AutAm.α1 x) : ↥M₁) * g⁻¹
    exact congrArg (fun w : G => g * w * g⁻¹) h
  comm2 := fun x => by
    apply Subtype.ext
    have h := congrArg Subtype.val (iso.comm2 x)
    show g * Subtype.val (iso.φ12 x : ↥(M₁ ⊓ M₂)) * g⁻¹ =
      g * Subtype.val (iso.φ2 (AutAm.α2 x) : ↥M₂) * g⁻¹
    exact congrArg (fun w : G => g * w * g⁻¹) h

theorem AutIso.toG_conjIso (iso : AutIso M₁ M₂) {g : G} (hg : g ∈ M₁ ⊓ M₂) (b : Bh) :
    (iso.conjIso hg).toG b = g * iso.toG b * g⁻¹ := rfl

theorem AutIso.imgG_conjIso (iso : AutIso M₁ M₂) {g : G} (hg : g ∈ M₁ ⊓ M₂) (K : Subgroup Ah) :
    (iso.conjIso hg).imgG K = B6.conjSub g (iso.imgG K) := by
  ext x
  rw [AutIso.mem_imgG, B6.mem_conjSub, AutIso.mem_imgG]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b, hb, ?_⟩
    rw [AutIso.toG_conjIso]
    group
  · rintro ⟨b, hb, hbx⟩
    refine ⟨b, hb, ?_⟩
    rw [AutIso.toG_conjIso, hbx]
    group

variable [Finite G] {z : G}

@[expose] def AutCtx.conj (c : AutCtx G M₁ M₂ z) {g : G} (hg : g ∈ M₁ ⊓ M₂) :
    AutCtx G M₁ M₂ z := { c with iso := c.iso.conjIso hg }

end CFSG.Quasithin.H13.F431.U42Aut
