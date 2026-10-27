module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2NFLieP
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentSyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentZ
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2QOneCard

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.NFLie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.F431.NF
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.GH74.GLS.Stage4.Hex CFSG.Quasithin.H13.F431.BN CFSG.Open
  CFSG.Quasithin CFSG.QuasithinUnique

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem stdOrient_g2 [Finite K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    Lift.StdOrient (C K) (U K) (Pmin K ⟨1, by decide⟩) (Pmin K ⟨0, by decide⟩) (xc 1) (xv 1)
      (xu 1) (nrC K) (naC K) (Xc K) (Q1 K) (Xa K) (Xb K) (Nat.card K) 2 where
  cz := Cent.cz one_ne_zero
  ct := Cent.ct
  nz := Cent.nz
  nt := Cent.nt
  Zperf := Cent.Xc_le_centerOf_perfectCore_Pr (four_le_card_of_pow hf hK)
  conj_tv := Cls.isConj_t_xu one_ne_zero
  U_le_P := U_le_Pmin _
  U_le_P' := U_le_Pmin _
  Z_le_Q := Xc_le_Q1
  Q_le_T := Q1_le_U
  Q_norm := fun _ hs _ hx => Q1_normal hs hx
  Z_central := fun _ hx _ hs => Xc_le_center_U hx _ hs
  Z_exp := by
    rintro _ ⟨s, rfl⟩
    exact xc_mul_self s
  card_Z := card_Xc
  z_mem := xc_mem_Xc 1
  z_ne := xc_one_ne_one
  Q_comm := fun _ hx _ hy => commutator_mem_Xc hx hy
  Q_sq := fun _ hx => mul_self_mem_Xc hx
  card_Q := card_Q1
  card_T := card_U
  T_comm := fun _ hx _ hy => commutator_mem_Q1 hx hy
  elem_abelian := fun _ hE _ hab => card_abelian_le_Q1 hE hab
  aut_Z := fun _ hφ _ hx => aut_mem_Xc hf hK hφ hx
  aut_Q := fun _ hφ _ hx => aut_mem_Q1 hf hK hφ hx
  trans := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ hs ht
    exact exists_torus_xc (fun h => hs (by rw [h]; exact xc_zero))
      (fun h => ht (by rw [h]; exact xc_zero))
  X_le := Xa_le_Q1
  Y_le := Xb_le_Q1
  Z_le_comm := Xc_le_commutator
  v_mem := xu_mem_Q1 1
  v_not_mem := xu_one_not_mem_Xc
  v_comm_X := by
    rintro _ ⟨s, rfl⟩
    exact xa_comm_xu s 1
  v_comm_Y := by
    rintro _ ⟨s, rfl⟩
    exact xb_comm_xu s 1
  v_not_cent := fun _ hφ => exists_comm_not_mem_Xc_aut hf hK (Cent.not_isConj_xc_xv 1) hφ
  nr_mem := nrC_mem_Pmin
  na_mem := naC_mem_Pmin
  X_eq := Xa_eq_cj
  Y_eq := Xb_eq_cj

end CFSG.Quasithin.H13.F431.G2.NFLie
