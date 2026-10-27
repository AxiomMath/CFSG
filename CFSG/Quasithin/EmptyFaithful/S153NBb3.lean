module

public import CFSG.Quasithin.Background.S1567Z7

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace Bb

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

structure ChoiceData (T Mc M E : Subgroup G) (y τ : G) : Prop where
  y_YE : y ∈ YE153 Mc M E
  y_M : y ∈ M
  y_N : y ∈ Subgroup.normalizer (E : Set G)
  τ_TE : τ ∈ TE153 T E
  τ_M : τ ∈ M
  τ_N : τ ∈ Subgroup.normalizer (E : Set G)
  y_cube : y ^ 3 ∈ Subgroup.centralizer (VE67 T M E : Set G)
  τ_sq : τ * τ ∈ S1567.K167 T M E
  y_V : ∃ v ∈ VZ T M, ⁅y, v⁆ ∉ E
  comm_y : ∀ c ∈ Subgroup.centralizer (E : Set G),
    c * y * c⁻¹ * y⁻¹ ∈ Subgroup.centralizer (VE67 T M E : Set G)
  comm_τ : ∀ c ∈ Subgroup.centralizer (E : Set G), τ * c * τ⁻¹ * c⁻¹ ∈ S1567.K167 T M E
  rel : τ * y * τ⁻¹ * y ∈ Subgroup.centralizer (VE67 T M E : Set G)

namespace ChoiceAux

omit [Finite G] in
theorem YE_le_Y (Mc M E : Subgroup G) : YE153 Mc M E ≤ Y153 Mc M :=
  (oTwoUpper_le _).trans inf_le_left

omit [Finite G] in
theorem YE_le_normalizer (Mc M E : Subgroup G) :
    YE153 Mc M E ≤ Subgroup.normalizer (E : Set G) :=
  (oTwoUpper_le _).trans inf_le_right

omit [Finite G] in
theorem YE_le_M (Mc M E : Subgroup G) : YE153 Mc M E ≤ M :=
  (YE_le_Y Mc M E).trans (Y153_le Mc M)

theorem cube_mem_centralizer_V (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {y : G}
    (hy : y ∈ YE153 Mc M E) : y ^ 3 ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have h1 := Hyp153.pow_three_mem_pCoreOf_Y153 h113 k.c.hyp (YE_le_Y Mc M E hy)
  rw [k.r49.case_one.1] at h1
  exact h1.2

theorem cube_mem_centralizer_VE (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {y : G}
    (hy : y ∈ YE153 Mc M E) : y ^ 3 ∈ Subgroup.centralizer (VE67 T M E : Set G) :=
  S1567.YE_inf_centralizer_le_centralizer_VE h113 k
    ⟨(YE153 Mc M E).pow_mem hy 3,
      Subgroup.centralizer_le k.L.le_V (cube_mem_centralizer_V h113 k hy)⟩

theorem comm_mem_centralizer_VE (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {y c : G}
    (hy : y ∈ YE153 Mc M E) (hc : c ∈ Subgroup.centralizer (E : Set G)) :
    c * y * c⁻¹ * y⁻¹ ∈ Subgroup.centralizer (VE67 T M E : Set G) := by
  have hyE : y ∈ Subgroup.normalizer (E : Set G) := YE_le_normalizer Mc M E hy
  have hcE : c ∈ Subgroup.normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _ hc
  refine S1567.YE_inf_centralizer_le_centralizer_VE h113 k ⟨?_, ?_⟩
  · have h1 : c * y * c⁻¹ ∈ YE153 Mc M E :=
      (Subgroup.mem_normalizer_iff.mp (S1567.normalizer_le_normalizer_YE h113 k hcE) y).mp hy
    exact (YE153 Mc M E).mul_mem h1 ((YE153 Mc M E).inv_mem hy)
  · have h1 : y * c⁻¹ * y⁻¹ ∈ Subgroup.centralizer (E : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (S1567.normalizer_le_normalizer_CE E hyE) c⁻¹).mp
        ((Subgroup.centralizer _).inv_mem hc)
    have e : c * y * c⁻¹ * y⁻¹ = c * (y * c⁻¹ * y⁻¹) := by group
    rw [e]
    exact (Subgroup.centralizer _).mul_mem hc h1

theorem rel_mem_centralizer_E (k : Ctx67 G T Mc M V₁ V₂ E t) {y τ : G}
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) (hτN : τ ∈ Subgroup.normalizer (E : Set G))
    (hy3 : y ^ 3 ∈ Subgroup.centralizer (E : Set G))
    (hτ2 : τ * τ ∈ Subgroup.centralizer (E : Set G))
    (hy : ∃ e ∈ E, y * e * y⁻¹ ≠ e) (hτ : ∃ e ∈ E, τ * e * τ⁻¹ ≠ e) :
    τ * y * τ⁻¹ * y ∈ Subgroup.centralizer (E : Set G) := by
  have := isKleinFour_E k.c k.L
  obtain ⟨e₁, he₁E, hye₁⟩ := hy
  obtain ⟨e₂, he₂E, hτe₂⟩ := hτ
  have hε1 : conjAct E ⟨y, hyN⟩ ≠ 1 := fun h => by
    have h0 := (conjAct_eq_one_iff''' E ⟨y, hyN⟩).1 h
    apply hye₁
    have h1 := Subgroup.mem_centralizer_iff.mp h0 e₁ he₁E
    rw [← h1]
    group
  have hε3 : conjAct E ⟨y, hyN⟩ ^ 3 = 1 := by
    have hy3N : y ^ 3 ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).pow_mem hyN 3
    have e1 : conjAct E ⟨y, hyN⟩ ^ 3 = conjAct E ⟨y ^ 3, hy3N⟩ := by
      rw [← map_pow]
      rfl
    rw [e1, conjAct_eq_one_iff''']
    exact hy3
  have hσ1 : conjAct E ⟨τ, hτN⟩ ≠ 1 := fun h => by
    have h0 := (conjAct_eq_one_iff''' E ⟨τ, hτN⟩).1 h
    apply hτe₂
    have h1 := Subgroup.mem_centralizer_iff.mp h0 e₂ he₂E
    rw [← h1]
    group
  have hσ2 : conjAct E ⟨τ, hτN⟩ ^ 2 = 1 := by
    have hττN : τ * τ ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).mul_mem hτN hτN
    have e1 : conjAct E ⟨τ, hτN⟩ ^ 2 = conjAct E ⟨τ * τ, hττN⟩ := by
      rw [← map_pow, pow_two]
      rfl
    rw [e1, conjAct_eq_one_iff''']
    exact hτ2
  have hrel := S1567.mulAut_conj_inv _ _ hε1 hε3 hσ1 hσ2
  have hzN : τ * y * τ⁻¹ * y ∈ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem
      ((Subgroup.normalizer _).mul_mem hτN hyN) ((Subgroup.normalizer _).inv_mem hτN)) hyN
  have h2 : conjAct E ⟨τ * y * τ⁻¹ * y, hzN⟩ =
      conjAct E ⟨τ, hτN⟩ * conjAct E ⟨y, hyN⟩ * (conjAct E ⟨τ, hτN⟩)⁻¹ * conjAct E ⟨y, hyN⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  have h3 : conjAct E ⟨τ * y * τ⁻¹ * y, hzN⟩ = 1 := by
    rw [h2, hrel, inv_mul_cancel]
  exact (conjAct_eq_one_iff''' E _).1 h3

theorem rel_mem_centralizer_VE (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {y τ : G}
    (hyYE : y ∈ YE153 Mc M E) (hy : ∃ e ∈ E, y * e * y⁻¹ ≠ e) (hτTE : τ ∈ TE153 T E)
    (hττ : τ * τ ∈ Subgroup.centralizer (VZ T M : Set G)) (hτ : ∃ e ∈ E, τ * e * τ⁻¹ ≠ e) :
    τ * y * τ⁻¹ * y ∈ Subgroup.centralizer (VE67 T M E : Set G) := by
  have hyN : y ∈ Subgroup.normalizer (E : Set G) := YE_le_normalizer Mc M E hyYE
  have hτN : τ ∈ Subgroup.normalizer (E : Set G) := hτTE.2
  have hzC : τ * y * τ⁻¹ * y ∈ Subgroup.centralizer (E : Set G) :=
    rel_mem_centralizer_E k hyN hτN
      (Subgroup.centralizer_le k.L.le_V (cube_mem_centralizer_V h113 k hyYE))
      (Subgroup.centralizer_le k.L.le_V hττ) hy hτ
  have hzY : τ * y * τ⁻¹ * y ∈ YE153 Mc M E :=
    (YE153 Mc M E).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (S1567.normalizer_le_normalizer_YE h113 k hτN) y).mp hyYE) hyYE
  exact S1567.YE_inf_centralizer_le_centralizer_VE h113 k ⟨hzY, hzC⟩

theorem exists_y (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) :
    ∃ y ∈ YE153 Mc M E, (∃ e ∈ E, y * e * y⁻¹ ≠ e) ∧ ∃ v ∈ VZ T M, ⁅y, v⁆ ∉ E := by
  obtain ⟨-, y₁, hy₁, hy₁E, -⟩ := Y_facts h113 k.c k.L
  obtain ⟨y₂, hy₂, hy₂V, -⟩ := S1567.exists_YE_move_quot h113 k
  by_cases h1 : ∃ v ∈ VZ T M, ⁅y₁, v⁆ ∉ E
  · exact ⟨y₁, hy₁, hy₁E, h1⟩
  push Not at h1
  by_cases h2 : ∃ e ∈ E, y₂ * e * y₂⁻¹ ≠ e
  · exact ⟨y₂, hy₂, h2, hy₂V⟩
  push Not at h2
  refine ⟨y₁ * y₂, (YE153 Mc M E).mul_mem hy₁ hy₂, ?_, ?_⟩
  · obtain ⟨e, heE, hne⟩ := hy₁E
    refine ⟨e, heE, ?_⟩
    have e' : y₁ * y₂ * e * (y₁ * y₂)⁻¹ = y₁ * (y₂ * e * y₂⁻¹) * y₁⁻¹ := by group
    rw [e', h2 e heE]
    exact hne
  · obtain ⟨v, hv, hvE⟩ := hy₂V
    refine ⟨v, hv, fun hmem => hvE ?_⟩
    have hy₂M : y₂ ∈ M := YE_le_M Mc M E hy₂
    have hv' : y₂ * v * y₂⁻¹ ∈ VZ T M :=
      (Subgroup.mem_normalizer_iff.mp (k.c.hyp.le_normalizer hy₂M) v).mp hv
    have e' : ⁅y₁ * y₂, v⁆ = ⁅y₁, y₂ * v * y₂⁻¹⁆ * ⁅y₂, v⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e'] at hmem
    have := E.mul_mem (E.inv_mem (h1 _ hv')) hmem
    rwa [inv_mul_cancel_left] at this

end ChoiceAux

theorem exists_choice (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) :
    ∃ y τ : G, ChoiceData T Mc M E y τ := by
  obtain ⟨τ, hτQ, hτTE, hττ, hmove⟩ := S1567.exists_tau k
  obtain ⟨y, hyYE, hyE, hyV⟩ := ChoiceAux.exists_y h113 k
  exact ⟨y, τ,
    { y_YE := hyYE
      y_M := ChoiceAux.YE_le_M Mc M E hyYE
      y_N := ChoiceAux.YE_le_normalizer Mc M E hyYE
      τ_TE := hτTE
      τ_M := k.c.hyp.T_le hτTE.1
      τ_N := hτTE.2
      y_cube := ChoiceAux.cube_mem_centralizer_VE h113 k hyYE
      τ_sq := S1567.mul_self_tau_mem_K167 h113 k hτQ hττ
      y_V := hyV
      comm_y := fun _ hc => ChoiceAux.comm_mem_centralizer_VE h113 k hyYE hc
      comm_τ := fun _ hc => S1567.commutator_tau_CE_le_K167 h113 k hτQ hτTE hc
      rel := ChoiceAux.rel_mem_centralizer_VE h113 k hyYE hyE hτTE hττ hmove }⟩

theorem exists_conj_decomp (k : Ctx67 G T Mc M V₁ V₂ E t) {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) {v : G} (hv : v ∈ VZ T M) :
    ∃ c ∈ Subgroup.centralizer (E : Set G), ∃ v' ∈ VZ T M, g * v * g⁻¹ = c * v' * c⁻¹ := by
  obtain ⟨y, hy, u, hu, w, hw, rfl⟩ := S1567.exists_decomp_GE k.c k.r66 hg
  have hyE : y ∈ Subgroup.normalizer (E : Set G) := ChoiceAux.YE_le_normalizer Mc M E hy
  have hyM : y ∈ M := ChoiceAux.YE_le_M Mc M E hy
  have huM : u ∈ M := k.c.hyp.T_le hu.1
  have hmN : y * u ∈ Subgroup.normalizer (VZ T M : Set G) :=
    k.c.hyp.le_normalizer (M.mul_mem hyM huM)
  have hmE : y * u ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).mul_mem hyE hu.2
  refine ⟨(y * u) * w * (y * u)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (S1567.normalizer_le_normalizer_CE E hmE) w).mp hw,
    (y * u) * v * (y * u)⁻¹, (Subgroup.mem_normalizer_iff.mp hmN v).mp hv, ?_⟩
  group

theorem le_centralizer_of_isMaxElemAbelian (k : Ctx67 G T Mc M V₁ V₂ E t) {A : Subgroup G}
    (hA : IsMaxElemAbelian (TE153 T E) A) : A ≤ Subgroup.centralizer (E : Set G) :=
  ((le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ (TE153 T E)).trans
    (C1Pack153.thompsonJ_TE_le_centralizer k.c k.L k.r66)).trans
      (Subgroup.centralizer_le k.L.le_V)

end Bb

end CFSG.Quasithin.S153N
