module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdTwo

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.Lift

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
  {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hσ hf hK hσq in
theorem stdTwo_d4 : StdTwo (Cm σ) (Ust σ) (Pst0 σ) (Pst1 σ) (zC σ) (tC σ hσ) where
  z_mem := zC_mem_Ust σ hσ
  t_mem := tC_mem_Ust σ hσ
  z_two := orderOf_zC σ
  t_two := orderOf_tC σ hσ
  cls := cls_d4 σ hσ
  noconj := fun φ => no_aut_zC_tC σ hσ φ
  center := fun _ hw hc hne => center_d4 σ hσ hw hc hne
  aut_z := fun _ h0 h1 => aut_zC σ hf hK hσq h0 h1
  aut_t := fun _ h0 h1 => aut_tC σ hσ hf hK hσq h0 h1
  cent_z := Or.inl (cent_zC σ hσ)
  cent_t := Or.inr (cent_tC σ hσ)

end CFSG.Quasithin.H13.F431.D4q.Loc
