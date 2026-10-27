module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213f
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Ui
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213b
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213d
import CFSG.LocalAnalysis.UniquenessCase.UC22P22o

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s13xl_B0_ne_bot {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch) (hn : 2 ≤ c.n) :
    c.B0 ≠ ⊥ := by
  intro h
  have h4 : 4 ≤ 2 ^ c.n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ c.n := Nat.pow_le_pow_right (by norm_num) hn
  have hp : (2 ^ c.n - 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hr : (2 ^ c.n - 1).minFac ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hp, Nat.minFac_dvd _⟩
  rw [h] at hr
  have hd : (2 ^ c.n - 1).minFac ∣ Nat.card (⊥ : Subgroup G) := hr.2
  rw [Subgroup.card_bot] at hd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hd)

theorem uc22s13xl_s21_21E_of_s21_21EB {D : Data G} {Ch : Choice2011 G} (h21EB : S21_21EB D Ch)
    (h12 : S22_12 D Ch) (hsig : D.sig.Nonempty) (h1930 : H1930 D) (c₀ : Ctx22b D Ch)
    (hn : 2 ≤ c₀.n) : S21_21E D Ch := fun _ _ hH =>
  h21EB h1930 { c₀.toCtx21 with B := c₀.B0, hB := c₀.hB0, hle := le_rfl }
    (uc22s13xl_B0_ne_bot c₀.toCtx21 hn)
    ((uc22p2213b_hyp2120_B0_iff D Ch h12 h1930 hsig c₀).2 hH.2.1)

theorem uc22s13xl_s22_13_14_of_s21_21EB {D : Data G}
    {Ch : Choice2011 G} (h21EB : S21_21EB D Ch) (h12 : S22_12 D Ch) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (he : 3 < CFSG.Open.evenRank G) (h117 : R117W D)
    (h869P : F08.R869NPair D) (h869NS5 : F08.R869NS5 D) (h2117 : S21_17 D Ch)
    (h2115C : S21_15C D Ch) (h9N : S21_9N D Ch) (h218E : S21_8E D Ch) (h8100E : R8100E D)
    (hn : SpU3NotList D) (hJ : J1NotSp4SU3) (hJL : J1NotL2Sz) (hJ1 : uc22p22d_J1Nontrivial)
    (h8 : S22_8 D Ch) (hSg : UC6S846.SigmaStd D) (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n)
    (h846 : F08.R846 D) : S22_13 D Ch ∧ S22_14 D Ch := by
  have hV : S22_V D Ch := uc22p22o_s22_V_derived D Ch hx h61
  have h21E : H1930 D → Ctx22b D Ch → S21_21E D Ch := fun h1930 c =>
    uc22s13xl_s21_21E_of_s21_21EB h21EB h12 hx.sig_nonempty h1930 c (by have := hn3 c; omega)
  refine ⟨fun h1930 c => ?_, fun h1930 c => ?_⟩
  · exact uc22p2213f_s22_13 D Ch hx h61 he h117 h869P h2117 h2115C (h21E h1930 c) h9N h218E
      h8100E (fun _ => hn3) h12 h1930 c
  · exact uc22p2214_s22_14_of_use5 D Ch h869NS5 h2115C h2117 hn hJ hJL hJ1 h8 hSg hV hn3 h846
      (s21_21Used_of_s21_21E he (h21E h1930 c)) h1930 c

end CFSG.LocalAnalysis.UniquenessCase.UC22
