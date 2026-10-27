module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBL31A
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBL31B
public import CFSG.Quasithin.Vol2.Ch4Sec2NoSum2

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

theorem rPlus_eq_pCoreOf {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k : ℕ}
    (hd : NoSumBigData G T M L Mm I H K m k) : rPlus T M L = pCoreOf 2 (L ⊔ T) := by
  rw [hd.1.pCoreOf_sup_eq_inf, hd.2.2.1.conjClosure_eq]

theorem lemma31_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : Lemma31 := by
  intro G _ _ T M L Mm I H K m k hd
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  have hrP : rPlus T M L = pCoreOf 2 (L ⊔ T) := rPlus_eq_pCoreOf hd
  refine ⟨?_, ?_⟩
  · rw [hrP]
    refine lt_of_le_of_ne hc.R_le fun hRR => ?_
    have hRpH : pCoreOf 2 (L ⊔ T) ≤ H := hRR ▸ (pCoreOf_le 2 I).trans hc.inH.1
    have hLH : L ≤ H := by
      intro l hl
      obtain ⟨a, ha, o, ho, rfl⟩ := (mem_sup_of_le_normalizer
        (((perfectCore_le _).trans inf_le_left).trans (le_normalizer_pCoreOf 2 L))).mp (hc.L_le hl)
      exact H.mul_mem ((perfectCore_le _).trans inf_le_right ha) (hRpH (hc.pCoreOf_L_le ho))
    have hTH : T ≤ H := by
      intro t ht
      obtain ⟨p, hp, cc, hcc, rfl⟩ := T_le_L_rPlus hd (T_acts_inner hd) t ht
      exact H.mul_mem (hLH hp) (hRpH hcc)
    exact hc.not_le_H h37 h38 h39 hd.2.1 hTH
  · rw [hrP]
    exact hc.pCoreOf_le_centralizer_V le_rfl

end CFSG.Quasithin.H13.Ch4.NSB
