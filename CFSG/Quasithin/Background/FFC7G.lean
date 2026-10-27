module

public import CFSG.Quasithin.Background.FFC7F
public import CFSG.Quasithin.Background.FFC5Final
public import CFSG.Quasithin.Background.FFC6U
public import CFSG.Quasithin.Background.FFC7E

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem b510OffendersAll_of_inputs
    (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (h57 : B57Input) (hSum : B510SumNat) : B510OffendersAll := by
  intro V _ _ G hc A L hA hL hLA hconc
  refine ⟨?_, ?_⟩
  · rintro (h1 | h3 | h4 | h5)
    · exact B510.offenders_of_natural hP4 hB51 hA21 h57 hc hL (Or.inl h1.1)
    · exact B510.offenders_of_sumNat hP4 hSum hc hL h3.1
    · obtain ⟨m, -, hm⟩ := h4.1
      have hfix := B510.fixV_inf_eq_bot_of_natural (by norm_num) hm
      exact B510.offenders_of_natural hP4 hB51 hA21 h57 hc hL
        (Or.inr ⟨m, by rw [hfix]; exact hm⟩)
    · exact B510.offenders_of_natural hP4 hB51 hA21 h57 hc hL (Or.inr ⟨1, h5.2.2.2.1.2.1⟩)
  · intro h2
    exact B510.offenders_of_sym5 hP4 hc hA hL h2

theorem asB56_of_quoted_inputs
    (hP4 : AsB15Part4) (hB51 : AsB51) (hB42 : AsB42)
    (hA21 : AsA21SQTKSection) (h57 : B57Input) (hLast : B59Last) (hI16 : AsI16Cover)
    (hSum : B510SumNat) : AsB56 :=
  asB56_of_inputs hP4 hB51 hA21 (B59.asB59_of_inputs hP4 hB51 hB42 hA21 h57 hLast hI16)
      (b510OffendersAll_of_inputs hP4 hB51 hA21 h57 hSum)

end FFC

end CFSG.Quasithin
