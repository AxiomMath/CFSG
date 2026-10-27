module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin Subgroup

variable {W : Type*} [CommGroup W]

theorem isIrrOn_iff_isInv_isIrrSec {X : Subgroup (MulAut W)} {I N : Subgroup W} :
    IsIrrOn X I N ↔ XMod.IsInv ↥X I ∧ XMod.IsInv ↥X N ∧ XMod.IsIrrSec ↥X N I := by
  unfold IsIrrOn XMod.IsInv XMod.IsIrrSec StableUnder
  constructor
  · rintro ⟨hlt, hI, hN, hmin⟩
    exact ⟨fun a i hi => hI a a.2 i hi, fun a n hn => hN a a.2 n hn, hlt,
      fun J hJ hNJ hJI => hmin J (fun a ha j hj => hJ ⟨a, ha⟩ j hj) hNJ hJI⟩
  · rintro ⟨hI, hN, hlt, hmin⟩
    exact ⟨hlt, (fun a ha i hi => hI ⟨a, ha⟩ i hi),
      (fun a ha n hn => hN ⟨a, ha⟩ n hn),
      fun J hJ hNJ hJI => hmin J (fun a i hi => hJ (a : MulAut W) a.2 i hi) hNJ hJI⟩

theorem isIrrOn_bot_iff_isIrr {X : Subgroup (MulAut W)} {I : Subgroup W} :
    IsIrrOn X I ⊥ ↔ XMod.IsIrr ↥X I := by
  rw [isIrrOn_iff_isInv_isIrrSec]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, XMod.isInv_bot, h.2⟩⟩

theorem iso_of_secIsoOn_bot {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (h : SecIsoOn X A ⊥ B ⊥) : XMod.Iso ↥X A B := by
  obtain ⟨-, -, -, -, -, -, β, hβB, hβbot, hβsurj, hβeq⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h0 : β a ∈ (⊥ : Subgroup W) := ha ▸ Subgroup.one_mem ⊥
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβbot a).1 h0))
  have hinj' : Function.Injective (β.codRestrict B hβB) := by
    intro a b h
    exact hinj (congrArg Subtype.val h)
  have hsurj : Function.Surjective (β.codRestrict B hβB) := by
    intro b
    obtain ⟨a, ha⟩ := hβsurj (b : W) b.2
    have h1 : β a * (b : W)⁻¹ = 1 := Subgroup.mem_bot.1 (by simpa using ha)
    refine ⟨a, Subtype.ext ?_⟩
    exact mul_inv_eq_one.1 h1
  let φ : ↥A ≃* ↥B := MulEquiv.ofBijective (β.codRestrict B hβB) ⟨hinj', hsurj⟩
  refine ⟨φ, fun x a a' ha' => ?_⟩
  have ha'' : (a' : W) = (x : MulAut W) (a : W) := by
    simpa [Subgroup.smul_def, MulAut.smul_def] using ha'.symm
  have h1 : β a' = (x : MulAut W) (β a) := by
    have := Subgroup.mem_bot.1 (hβeq (x : MulAut W) x.2 a a' ha'')
    exact mul_inv_eq_one.1 this
  have hφa : ((φ a : ↥B) : W) = β a := rfl
  have hφa' : ((φ a' : ↥B) : W) = β a' := rfl
  rw [hφa, hφa']
  simpa [Subgroup.smul_def, MulAut.smul_def] using h1.symm

end CFSG.LocalAnalysis.WeakClosure81
