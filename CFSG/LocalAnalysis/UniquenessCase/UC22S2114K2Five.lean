module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114SolvOver
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.UC22S218G2
import CFSG.LocalAnalysis.UniquenessCase.UC22S218D4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.Quasithin.H13.NQCatBND4
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowLieF
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
import CFSG.LieType.Multipliers.U62Sylow
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Quasithin.H13.NQCat (SolvOver)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_exists_five {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hn : 4 ∣ c.n) (hBL : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) :
    ∃ b ∈ c.B0, ∃ hbL : b ∈ normalizer (L : Set G), b ^ 5 = 1 ∧
      inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5B : 5 ∣ Nat.card c.B0 := by
    have h : 5 ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨Nat.prime_five,
        (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)⟩
    exact h.2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 5 h5B
  have hb5 : (b : G) ^ 5 = 1 := by
    rw [← Subgroup.orderOf_coe] at hb
    rw [← hb]
    exact pow_orderOf_eq_one _
  refine ⟨b, b.2, hBL b.2, hb5, fun h1 => ?_⟩
  have h := uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith b.2 h1
  rw [← Subgroup.orderOf_coe, h, orderOf_one] at hb
  exact Nat.prime_five.ne_one hb.symm

theorem uc22s2114_false_of_fieldBorel_five {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hn : 4 ∣ c.n) (hBL : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    (hSO : ∀ U : Subgroup (BarInf L), IsSylowTwoOf U ⊤ → SolvOver (BarInf L) U) {f m : ℕ}
    (hFB : FieldBorel (BarInf L) f (2 ^ m - 1)) (hm : ¬ 5 ∣ m) (hE : ¬ 5 ∣ 2 ^ m - 1) :
    False := by
  obtain ⟨b, hb, hbL, hb5, hb1⟩ := uc22s2114_exists_five c hL hn hBL hfaith
  obtain ⟨U, hU, y, hy, hy1, hy5⟩ := uc22s2114_exists_of_solvOver c hL hSO hb hbL hb5 hb1
    fun _ => uc22p2214_out_mem_of_card_dvd (uc22s2114_card_outer_dvd hFB) Nat.prime_five hm
  obtain ⟨H, F, D'⟩ := hFB.exists_of_sylow hU
  exact hy1 (D'.eq_one_of_pow_eq_one Nat.prime_five (by norm_num) hE hy hy5)

section Inner


theorem uc22s2114_false_of_is3D4_two {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hX : Is3D4 (BarInf L) 1) (hn : 4 ∣ c.n)
    (hBL : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) :
    False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨b, hb, hbL, hb5, hb1⟩ := uc22s2114_exists_five c hL hn hBL hfaith
  have hα5 : inducedBarInfAutHom L ⟨b, hbL⟩ ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨b, hbL⟩ : ↥(normalizer (L : Set G))) ^ 5 = 1 := Subtype.ext (by simpa using hb5)
    rw [this, map_one]
  obtain ⟨y, -, hy1, hy5⟩ := uc22s2114_exists_of_inner (center_barInf_eq_bot hL.2.2)
    (Subgroup.map_top_of_surjective _ (MulEquiv.surjective _))
    (uc22p2214_out_mem_of_card_dvd (uc22s2114_card_outer_dvd (uc22s218_d4_fieldBorel hX))
      Nat.prime_five (by norm_num) hα5) hb1 hα5
  exact CFSG.Quasithin.H23P4.not_five_dvd_card_is3D4
    (LieModel.chevalleyExceptionalModel hX (by decide))
    ((orderOf_eq_prime hy5 hy1) ▸ orderOf_dvd_natCard y)

section Tits


theorem uc22s2114_false_of_isG2_four {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hX : IsG2 (BarInf L) 2) (hn : 4 ∣ c.n)
    (hBL : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) :
    False :=
  uc22s2114_false_of_fieldBorel_five c hL hn hBL hfaith
    (fun _ hU => CFSG.Quasithin.H13.NQCat.BN.solvOver_of_isG2 le_rfl
      (LieModel.chevalleyExceptionalModel hX (by decide)) hU)
    (uc22s218_g2_fieldBorel hX) (by norm_num) (by norm_num)

theorem uc22s2114_false_of_is3D4_four {D : Data G}
    {Ch : Choice2011 G} (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hX : Is3D4 (BarInf L) 2) (hn : 4 ∣ c.n) (hBL : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) : False :=
  uc22s2114_false_of_fieldBorel_five c hL hn hBL hfaith
    (fun _ hU => CFSG.Quasithin.H13.NQCat.BN.solvOver_of_is3D4 le_rfl
      (LieModel.chevalleyExceptionalModel hX (by decide)) hU)
    (uc22s218_d4_fieldBorel hX) (by norm_num) (by norm_num)

end Tits

end Inner

end CFSG.LocalAnalysis.UniquenessCase.UC22
