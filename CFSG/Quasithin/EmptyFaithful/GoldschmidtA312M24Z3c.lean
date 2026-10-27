module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z3b
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Hat

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped Pointwise

theorem rho3_surj [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    Function.Surjective rho3 ∧ Nat.card rho3.ker = 3 * 2 ^ 6 := by
  have h720 : Nat.card (Equiv.Perm (Fin T3.length)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hcard : Nat.card rho3.range = 720 :=
    Nat.le_antisymm (h720 ▸ Subgroup.card_le_card_group _)
      (Nat.le_of_dvd Nat.card_pos rho3_dvd)
  have htop : rho3.range = ⊤ := Subgroup.eq_top_of_card_eq _ (hcard.trans h720.symm)
  refine ⟨MonoidHom.range_eq_top.mp htop, ?_⟩
  have h := card_ker_mul rho3
  rw [Z3_eq_Y3.1, hcard] at h
  omega

theorem isExt_Z3 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {B : Subgroup G24} (hB : B ∈ lFamily m24CtxE.S)
    (hY : B ⊔ m24CtxE.S = Z3) :
    IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6))) :=
  isExt_hat_of_member m24_S_isPGroup hB hY rho3 rho3_surj.1 V3_le_Z3
    (fun z hz => listHom_eq_one_of_fix Z3 T3 T3_nodup Z3_inv z (V3_fix z.1 hz))
    Z3_normalizes_V3 V3_comm_all V3_sq card_V3 rho3_surj.2 ω3_mem ω3_pow ω3_ne rho3_ω3 V3_comm

end CFSG.Quasithin.A312M24
