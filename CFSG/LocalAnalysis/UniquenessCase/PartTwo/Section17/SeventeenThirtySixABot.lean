module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixAInP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem seventeen_thirtysix_a_bot
    (D : Data G) {V : Subgroup G}
    (h1 : ∀ (hV : Hyp125 D ⊥ V), R17_1At D ⊥ V hV) (hSg : SigmaStd D)
    (hK3 : Inputs1719.K_BorelTorusAbelian) (hCen : UCK.U3Center) (hSyl : UCK.U3Syl)
    (hBorel : K_U3CartanRank) (hK : K_SU3EightBorelNine) (hK9 : K_SU3EightTorusE9)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h869 : F08.R869 D) (hNat : K_SU3NaturalModule)
    (h82 : F08.R82 D) (hC : K_U34ThreeCentralizer) (h846 : F08.R846 D) (h76 : F07.R76 D)
    (h614 : UC6.R6_14 D)
    (hfix : ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D ⊥ V L n),
      fixV (barSub ⊥ V c.hyp125.isElemAbelian (UC22.conjClosure D.M L)) = ⊥) :
    R17_36aAt D ⊥ V := by
  intro L n c
  by_contra hne
  obtain ⟨X, hX⟩ := exists_inP11_of_ne_conjClosure D ⊥ V hSg hK3 hCen hSyl hBorel hK hK9 c hne
  obtain ⟨-, hk, hm4⟩ := (h1 c.hyp125).2 ⟨X, hX⟩
  let hV := c.hyp125.isElemAbelian
  let Kbar : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV L
  have hLbar_ne : Kbar ≠ ⊥ :=
    barSub_ne_bot_of_v0_bot D h869 h127 hSyl c.hyp125 c.mem_calC c.shape
  have hcomp : Kbar ∈ compBar D.M ⊥ V hV :=
    barSub_mem_compBar_of_ne_bot c.hyp125 c.mem_calC hLbar_ne
  have hSU : IsSU3 ↥Kbar n := isSU3_barSub c.hyp125 c.mem_calC hLbar_ne c.shape
  have hn2 : 2 ≤ n := UCK.u3Range Kbar n hSU
  have hm4' : mBar D.M ⊥ V hV = 4 := hm4
  have hn : n = 2 := by
    by_contra hn2'
    have hn3 : 3 ≤ n := by omega
    have hO2 : ∀ P : Subgroup (MulAut (Vtil ⊥ V hV)),
        P ≤ Mbar D.M ⊥ V hV → (P.subgroupOf (Mbar D.M ⊥ V hV)).Normal →
          IsPGroup 2 P → P = ⊥ :=
      fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D c.hyp125 hP hN h2
    have hYne : Mbar D.M ⊥ V hV ≠ ⊥ := by
      intro hbot
      exact hLbar_ne (le_bot_iff.1 (hbot ▸ hcomp.1))
    have hbasic : IsBasicModule (Mbar D.M ⊥ V hV) :=
      TwelveSeventeen.isBasicModule D hx h61 h127 h1214 c.hyp125 hYne
    have hfix' : fixV (⨆ X ∈ conjSet Kbar (Mbar D.M ⊥ V hV), X) = ⊥ := by
      rw [← barSub_conjClosure_eq_iSup_conjSet c.hyp125 c.mem_calC.1.le]
      exact hfix L n c
    have hm : E3.mParam (Mbar D.M ⊥ V hV) ≤ 2 * n + 2 := by
      change mBar D.M ⊥ V hV ≤ 2 * n + 2
      omega
    have h2n := (hNat (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV) (Mbar D.M ⊥ V hV) Kbar n
      hcomp.1 hcomp hLbar_ne hSU hn3 hO2 hbasic hfix' hm).2
    change mBar D.M ⊥ V hV = 2 * n at h2n
    omega
  subst hn
  obtain ⟨l, hnd, hmem, hjoin⟩ := exists_conjSet_list D L
  rcases Nat.lt_or_ge l.length 4 with h4 | h4
  · rcases Nat.lt_or_ge l.length 3 with h3 | h3
    · exact hne (seventeen_thirtyfive_two_L0 D hSg h846 h76 h614 hCen hC L 2 c l rfl rfl hm4
        hk hnd hmem (by omega))
    · exact absurd (Data.k_eq_one_of_isStronglyPEmbedded D
        (isStronglyPEmbedded_three_of_three_conj D h82 hCen hC c.mem_calC c.shape hnd
          (by omega) hmem hjoin)) (by omega)
  · exact absurd (Data.k_eq_one_of_isStronglyPEmbedded D
      (isStronglyPEmbedded_three_of_four_conj D hSg hCen hC c.mem_calC c.shape hnd h4
        (fun K hK => (hmem K).1 hK))) (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
