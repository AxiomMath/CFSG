module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocOrientN11
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocPerf
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStd

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.Lift

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
  {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hσ hf hK hσq in
theorem stdOrient_d4 :
    StdOrient (Cm σ) (Ust σ) (Pst0 σ) (Pst1 σ) (zC σ) (tC σ hσ) (tC σ hσ) (nrC σ) (naC σ)
      (ZC σ) (QC σ) (XC σ) (YC σ) (2 ^ f) 4 where
  cz := cent_zC σ hσ
  ct := cent_tC σ hσ
  nz := not_cent_zC_le_Pst1 σ
  nt := not_cent_tC_le_Pst0 σ hσ
  Zperf := fun x hx => by
    obtain ⟨f', hf', hx'⟩ := exists_x6 σ hσ hx
    exact d4x₆_mem_centerOf_perfectCore_Pst0 σ hσ (four_le_card hf hK) hf' hx'
  conj_tv := IsConj.refl _
  U_le_P := Ust_le_Pst0 σ
  U_le_P' := Ust_le_Pst1 σ
  Z_le_Q := ZC_le_QC σ hσ
  Q_le_T := QC_le_Ust σ
  Q_norm := fun _ hs _ hx => QC_norm σ hσ hs hx
  Z_central := fun _ hx _ hs => ZC_central σ hσ hx hs
  Z_exp := fun _ hx => ZC_exp σ hσ hx
  card_Z := card_ZC σ hσ hf hK hσq
  z_mem := zC_mem_ZC σ hσ
  z_ne := zC_ne_one σ
  Q_comm := fun _ hx _ hy => QC_comm σ hσ hx hy
  Q_sq := fun _ hx => QC_sq σ hσ hx
  card_Q := card_QC σ hf hK hσq
  card_T := card_Ust σ hf hK hσq
  T_comm := fun _ hx _ hy => Ust_comm σ hσ hx hy
  elem_abelian := fun _ hE _ hab => card_le_elem σ hσ hf hK hσq hE hab
  aut_Z := fun _ hφ _ hx => aut_ZC σ hσ hf hK hσq hφ hx
  aut_Q := fun _ hφ _ hx => aut_QC σ hf hK hσq hφ hx
  trans := fun _ hx _ hy hx1 hy1 => trans_ZC σ hσ hx hy hx1 hy1
  X_le := XC_le_QC σ hσ
  Y_le := YC_le_QC σ hσ
  Z_le_comm := ZC_le_comm σ hσ
  v_mem := tC_mem_QC σ hσ
  v_not_mem := tC_not_mem_ZC σ hσ
  v_comm_X := fun _ ha => tC_comm_X σ hσ ha
  v_comm_Y := fun _ hb => tC_comm_Y σ hσ hb
  v_not_cent := fun _ hφ => not_cent_mod_Z σ hσ hf hK hσq hφ
  nr_mem := nrC_mem_Pst0 σ
  na_mem := naC_mem_Pst1 σ
  X_eq := X_eq_cj σ hσ
  Y_eq := Y_eq_cj σ hσ

end CFSG.Quasithin.H13.F431.D4q.Loc
