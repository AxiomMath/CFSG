module

public import CFSG.Quasithin.Background.F918H3

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace F918V6B

variable {W : Type} [CommGroup W] {X : Subgroup (MulAut W)} {U I : Subgroup W}

@[expose] noncomputable def resOnto (hXU : X ≤ stabSub U) : ↥X →* ↥(autSub X U) :=
  (resHomOn U hXU).codRestrict (autSub X U)
    fun x => mem_autSub.mpr ⟨⟨(x : MulAut W), hXU x.2⟩, x.2, rfl⟩

theorem resOnto_surjective (hXU : X ≤ stabSub U) : Function.Surjective (resOnto hXU) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
  exact ⟨⟨(g : MulAut W), hg⟩, rfl⟩

end F918V6B

end CFSG.Quasithin
