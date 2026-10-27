module

public import CFSG.Quasithin.Vol2.GoldschmidtSevenInner
public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenDef
public import CFSG.Quasithin.Vol2.KGFactHeInspJ4

public section

namespace CFSG.Quasithin.H13

theorem kgJ4SylowOvergroups_of_notReal (h : J4SevenNotReal) :
    KGInsp.KGJ4SylowOvergroups := by
  intro X _ _ hX
  have h49 := card_not_dvd_forty_nine hX
  have hreal : ∀ x g : X, orderOf x = 7 → g * x * g⁻¹ ≠ x⁻¹ := fun x g hx => h X hX x g hx
  refine ⟨fun N Y _ _ _ _ hN ρ hρ hK t htN => ?_, fun N Y _ _ hN ρ hρ hK t htN => ?_⟩
  · exact Seven.innerOn_of_not_real h49 hreal (Or.inl rfl) ρ hρ hK (hN htN)
  · exact Seven.innerOn_of_not_real h49 hreal (Or.inr rfl) ρ hρ hK (hN htN)

end CFSG.Quasithin.H13
