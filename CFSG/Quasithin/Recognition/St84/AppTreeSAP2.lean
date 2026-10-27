module

public import CFSG.Quasithin.Recognition.St84.AppTreeSA

import CFSG.Quasithin.Background.F1VertexCore

public section

namespace CFSG.Quasithin.St84

open CFSG.Open

theorem isPGroup_two_of_odd_eq_one {C : Type*} [Group C] [Finite C]
    (h : ∀ c : C, Odd (orderOf c) → c = 1) : IsPGroup 2 C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro c
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hord : orderOf (c ^ 2 ^ k) = m := by
    rw [orderOf_pow, hkm, Nat.gcd_eq_right (dvd_mul_right (2 ^ k) m),
      Nat.mul_div_cancel_left m (pow_pos (by norm_num) k)]
  have hpow : c ^ 2 ^ k = 1 := h (c ^ 2 ^ k) (by rw [hord]; exact hm)
  have hm1 : m = 1 := by
    have h2 : orderOf (c ^ 2 ^ k) = 1 := orderOf_eq_one_iff.mpr hpow
    rw [hord] at h2
    exact h2
  exact ⟨k, by rw [hkm, hm1, mul_one]⟩

end CFSG.Quasithin.St84

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
  CFSG.Quasithin.St84 CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem f112saP2_oTwoRes_normal {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    f112P2 L1 L2 S ≤ Subgroup.normalizer ((oTwoRes L2 : Subgroup H) : Set H) := by
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set H) := by
    rw [← bigB_comm L1 L2 S]
    exact bigB_le_normalizer_of_hyp111 hF.1.symm
  have hSbigB : S ≤ bigB L1 L2 S := by
    show S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S
    exact le_sup_right
  have hS : S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) := by
    intro s hs
    have hsL : conjSub s L2 = L2 := by
      simpa [conjSub] using
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBL2 (hSbigB hs))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub s (oTwoRes L2) = oTwoRes L2
    rw [conjSub_oTwoRes, hsL]
  rw [f112sa_P2_eq_sup hF h1]
  exact sup_le (le_normalizer_oTwoRes L2) hS

theorem f112saP2_pCoreOf_subgroupOf_eq (L : Subgroup H) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
  ext x
  simp [CFSG.Open.pCoreOf, Subgroup.mem_subgroupOf]

@[expose] noncomputable def f112saP2_V (L2 S : Subgroup H) : Subgroup H :=
  S ⊓ L2 ⊓ oTwoRes L2

theorem f112saP2_bigB_le_P2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    bigB L1 L2 S ≤ f112P2 L1 L2 S := by
  rw [f112sa_P2_eq_sup hF h1]
  have hB1 : borelOf L1 S ≤ S := by
    rw [f112sa_borelOf_left_eq hF h1]
    exact inf_le_left
  exact sup_le (sup_le (hB1.trans le_sup_right) ((F1.borelOf_le L2 S).trans le_sup_left))
    le_sup_right

theorem f112saP2_bigB_normal_X2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    bigB L1 L2 S ≤
      Subgroup.normalizer ((oTwoRes L2 ⊓ bigB L1 L2 S : Subgroup H) : Set H) := by
  have hBM : bigB L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) :=
    (f112saP2_bigB_le_P2 hF h1).trans (f112saP2_oTwoRes_normal hF h1)
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (oTwoRes L2 ⊓ bigB L1 L2 S).map (MulAut.conj b).toMonoidHom =
    oTwoRes L2 ⊓ bigB L1 L2 S
  rw [show (oTwoRes L2 ⊓ bigB L1 L2 S).map (MulAut.conj b).toMonoidHom =
      (oTwoRes L2).map (MulAut.conj b).toMonoidHom ⊓
        (bigB L1 L2 S).map (MulAut.conj b).toMonoidHom from
    Subgroup.map_inf (oTwoRes L2) (bigB L1 L2 S) (MulAut.conj b).toMonoidHom
      (MulAut.conj b).injective]
  change (oTwoRes L2).map (↑(MulAut.conj b)) ⊓ (bigB L1 L2 S).map (↑(MulAut.conj b)) =
    oTwoRes L2 ⊓ bigB L1 L2 S
  rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBM hb),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hb)]

theorem f112saP2_V_le_M (L2 S : Subgroup H) : f112saP2_V L2 S ≤ oTwoRes L2 := inf_le_right

theorem f112saP2_le_V_of_isPGroup_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S) {P : Subgroup H}
    (hP : IsPGroup 2 P) (hPX : P ≤ oTwoRes L2 ⊓ bigB L1 L2 S) :
    P ≤ f112saP2_V L2 S := by
  have hPL : P ≤ L2 := (hPX.trans inf_le_left).trans (oTwoRes_le L2)
  have hPB : P ≤ bigB L1 L2 S := hPX.trans inf_le_right
  have hPB2 : P ≤ borelOf L2 S := by
    have h := F1.inf_bigB_eq_borelOf hR.symm
    rw [bigB_comm L1 L2 S] at h
    rw [← h]
    exact le_inf hPL hPB
  have hPN : P ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup H) : Set H) :=
    hPB2.trans (F1.borelOf_le_normalizer L2 S)
  have hjoin : IsPGroup 2 ↥((S ⊓ L2) ⊔ P) :=
    IsPGroup.to_sup_of_normal_left' hF.1.h2.sylow.2.1 hP hPN
  have hjoinL : (S ⊓ L2) ⊔ P ≤ L2 := sup_le inf_le_right hPL
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp hF.1.h2.sylow).2.2 ((S ⊓ L2) ⊔ P) hjoinL hjoin
    le_sup_left
  have hPS2 : P ≤ S ⊓ L2 := le_trans le_sup_right hmax
  exact le_inf hPS2 (hPX.trans inf_le_left)

end CFSG.Quasithin.F112R.St84
