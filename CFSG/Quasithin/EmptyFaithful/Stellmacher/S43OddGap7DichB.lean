module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7DichA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7Model
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddThreeC

public section

namespace CFSG.Quasithin

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G]

theorem gap7At (H M : Subgroup G) : Gap7At H M := by
  intro S hA h26 α hs h3 β hβ h6
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  have hS : ∀ δ ∈ nbrs α, Nat.card (Vn δ) = 2 ^ 6 := fun δ hδ =>
    (card_Vn_eq (Sit43.vtype_true_of_adj hs.vα hδ) hβv).trans h6
  obtain ⟨α', hα', hY, -⟩ := exists_nbr_Yv_inf hA h26 hs hβ
  exact not_Vst_le_Qv_and hA h26 hs h3 hs.vα hβ hα' hY
    ⟨Gap7.Vst_le_Qv hA h26 hs h3 hs.vα hS hβ hα', Gap7.Vst_le_Qv hA h26 hs h3 hs.vα hS hα' hβ⟩

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
