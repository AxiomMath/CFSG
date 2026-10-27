module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6MS
public import CFSG.Quasithin.Background.C134L32CorrM

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem exists_c134CaseW (hMS : C134L32CorrM)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ i : ℕ, CFSG.Quasithin.IsC134CaseM i (L ⊔ c.R1) c.R1 L := by
  obtain ⟨α, hα⟩ := c.exists_alpha
  have hcomp : L ∈ cComp (L ⊔ c.R1) := c.sup_R1_eq ▸ c.comp
  exact hMS G (L ⊔ c.R1) c.R1 L (c.isMSPair hN) hcomp c.coe_sup_R1
    ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩

theorem not_case_le_fourW {i : ℕ} (hi : CFSG.Quasithin.IsC134CaseM i (L ⊔ c.R1) c.R1 L)
    (hi4 : i ≤ 4) :
    False := by
  have hzQ : z ∈ c134Q (L ⊔ c.R1) L := c.V_le_c134Q c.f.mem_zV.1
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with h | h | h | h | h
  · subst h
    exact hi
  · subst h
    exact A38c10.MS.false_of_case_one_two_three (i := 1) hi (Or.inl rfl) hzQ c.z_ne_one c.z_fix
  · subst h
    exact A38c10.MS.false_of_case_one_two_three (i := 2) hi (Or.inr (Or.inl rfl)) hzQ c.z_ne_one
      c.z_fix
  · subst h
    exact A38c10.MS.false_of_case_one_two_three (i := 3) hi (Or.inr (Or.inr rfl)) hzQ c.z_ne_one
      c.z_fix
  · subst h
    obtain ⟨⟨n, F, _, _, α, -, hα, -, -, hU, -, -⟩, -⟩ := hi
    have hzU : z ∈ ⁅centerOf (c134Q (L ⊔ c.R1) L), L⁆ := by
      have h1 : V ≤ ⁅centerOf (c134Q (L ⊔ c.R1) L), L⁆ := by
        calc V = ⁅V, L⁆ := c.f.commutator.symm
          _ ≤ _ := Subgroup.commutator_mono c.V_le_center_c134Q le_rfl
      exact h1 c.f.mem_zV.1
    exact c.z_ne_one (Subgroup.mem_bot.mp (A38c10.MS.mem_of_fixed hα.1 hU hzU c.z_fix))

theorem commutator_Q_eqW (hMS : C134L32CorrM)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ⁅pCoreOf 2 (L ⊔ T), L⁆ = V := by
  obtain ⟨i, hi⟩ := c.exists_c134CaseW hMS hN
  have hi5 : i = 5 := by
    by_contra h5
    rcases (by omega : i ≤ 4 ∨ 5 < i) with h | h
    · exact c.not_case_le_fourW hi h
    · revert hi
      unfold CFSG.Quasithin.IsC134CaseM
      split <;> first | omega | exact id
  subst hi5
  have h16 := c.card_c134Q_of_case5 hi
  have hVQ := c.V_le_c134Q
  have heq : V = c134Q (L ⊔ c.R1) L :=
    Subgroup.eq_of_le_of_card_ge hVQ (by rw [h16, c.card16]; norm_num)
  rw [heq]
  unfold c134Q
  rw [c.sup_R1_eq]

end Ctx

end N1246

end CFSG.Quasithin.H13
