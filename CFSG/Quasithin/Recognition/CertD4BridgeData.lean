module

public import Certificates.Certificate19954

public section

namespace CFSG.Quasithin

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree

theorem d4b_checkX0 : D4bXOK ⟨0, by decide⟩ :=
  Certificates.certificate19954.1

theorem d4b_checkX1 : D4bXOK ⟨1, by decide⟩ :=
  Certificates.certificate19954.2.1

theorem d4b_checkX2 : D4bXOK ⟨2, by decide⟩ :=
  Certificates.certificate19954.2.2.1

theorem d4b_checkX3 : D4bXOK ⟨3, by decide⟩ :=
  Certificates.certificate19954.2.2.2.1

theorem d4b_checkY0 : D4bYOK ⟨0, by decide⟩ :=
  Certificates.certificate19954.2.2.2.2.1

theorem d4b_checkY1 : D4bYOK ⟨1, by decide⟩ :=
  Certificates.certificate19954.2.2.2.2.2.1

theorem d4b_checkY2 : D4bYOK ⟨2, by decide⟩ :=
  Certificates.certificate19954.2.2.2.2.2.2.1

theorem d4b_checkY3 : D4bYOK ⟨3, by decide⟩ :=
  Certificates.certificate19954.2.2.2.2.2.2.2.1

theorem d4b_check (i : Fin Tag.D4.rank) : D4bXOK i := by
  fin_cases i
  exacts [d4b_checkX0, d4b_checkX1, d4b_checkX2, d4b_checkX3]

theorem d4b_check_y (i : Fin Tag.D4.rank) : D4bYOK i := by
  fin_cases i
  exacts [d4b_checkY0, d4b_checkY1, d4b_checkY2, d4b_checkY3]

theorem d4bEs_mul_self :
    ∀ (i : Fin Tag.D4.rank) (s : Bool), d4bEs i s * d4bEs i s = 0 :=
  Certificates.certificate19954.2.2.2.2.2.2.2.2.1

theorem d4bTh_simple : ∀ (i : Fin Tag.D4.rank) (s : Bool),
    d4bTh (.inr ⟨d4bSimple i s, by cases s <;> fin_cases i <;> decide⟩) = d4bEs i s := by
  intro i s
  rfl

theorem d4bSimple_root : ∀ (i : Fin Tag.D4.rank) (s : Bool),
    d4Certificate.root (d4bSimple i s) = (if s then 1 else -1) • Pi.single i 1 :=
  Certificates.certificate19954.2.2.2.2.2.2.2.2.2.1

theorem d4b_root_injective :
    ∀ m n : Fin d4Certificate.roots.length,
    d4Certificate.root m = d4Certificate.root n → m = n :=
  Certificates.certificate19954.2.2.2.2.2.2.2.2.2.2

end CFSG.Quasithin
