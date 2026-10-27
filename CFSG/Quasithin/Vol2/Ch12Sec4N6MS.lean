module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6S
public import CFSG.Quasithin.EmptyFaithful.A38c10MSb
public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Quasithin.Vol2.Ch4Sec1Defs
public import CFSG.Quasithin.Background.C134L32Corr

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem R1_le_NL : c.R1 ≤ Subgroup.normalizer (L : Set G) :=
  c.R1_le_T.trans c.cx.hyp.normalizes

theorem T_le_sup_R1 : T ≤ L ⊔ c.R1 := by
  intro t ht
  obtain ⟨l, hl, hlt⟩ := cx_mem_mul_of_mem_T c.f c.Tbar ht
  have hq : l⁻¹ * t ∈ c.R1 := by
    have : l⁻¹ * t ∈ pCoreOf 2 (L ⊔ T) := by rw [c.Q]; exact hlt
    exact c.Q_le_R1 this
  have : t = l * (l⁻¹ * t) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl.2) (Subgroup.mem_sup_right hq)

theorem sup_R1_eq : L ⊔ c.R1 = L ⊔ T :=
  le_antisymm (sup_le_sup_left c.R1_le_T L) (sup_le le_sup_left c.T_le_sup_R1)

theorem coe_sup_R1 : ((L ⊔ c.R1 : Subgroup G) : Set G) = (L : Set G) * (c.R1 : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left L _ c.R1_le_NL

theorem exists_alpha :
    ∃ α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), IsModO2Surj L α := by
  obtain ⟨e⟩ := c.q3
  let e' := e.trans (specialLinearGroupEquivStatedSL 3 (ZMod 2))
  refine ⟨e'.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
    e'.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  show (e'.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).ker = CFSG.pCore 2 ↥L
  rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) e'.toMonoidHom
    e'.injective, QuotientGroup.ker_mk']

theorem isRankTwoLie2Derived :
    IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  obtain ⟨e⟩ := c.q3
  have hsl := isSimpleGroup_sl_zmod_two (m := 3) le_rfl
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have := hsl.1
    exact e.isSimpleGroup
  have hc : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
      with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hsl.2
      apply hab
      have hm : e.symm a ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := h ▸ Subgroup.mem_top _
      have h1 := Subgroup.mem_center_iff.1 hm (e.symm b)
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact h1.symm
  let e2 : ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ≃*
      (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact Or.inl ⟨1, isPSL_three_two_iff.mpr ⟨e2.trans e⟩⟩

theorem isMSPair
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    IsMSPair (L ⊔ c.R1) c.R1 := by
  obtain ⟨D⟩ := c.nat.toL3Coord
  have hyp := c.cx.hyp
  have heq := c.sup_R1_eq
  refine ⟨⟨heq ▸ c.sqtk, heq ▸ c.char, L, heq ▸ c.comp, c.coe_sup_R1, c.isRankTwoLie2Derived⟩,
    Or.inl ⟨c.Hp, heq ▸ c.Hp_lt, heq ▸ c.Hp_odd, (c.pCore_Hp_eq D).symm⟩, ?_⟩
  intro C hCR hC1 hchar hLN
  apply hN
  have hNC : Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have := hchar
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := c.R1) (C.subgroupOf c.R1)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at h1
  have hC2 : IsPGroup 2 ↥C := hyp.sylow.1.to_le (hCR.trans c.R1_le_T)
  rw [heq] at hLN
  exact hNC.trans (Ch4.isUniqueM_normalizer_le c.uniq hC1 hC2 hLN)

theorem exists_c134Case (hMS : C134L32Corr)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ i : ℕ, C134CorrLocal.IsC134CaseCorr i (L ⊔ c.R1) c.R1 L := by
  obtain ⟨α, hα⟩ := c.exists_alpha
  have hcomp : L ∈ cComp (L ⊔ c.R1) := c.sup_R1_eq ▸ c.comp
  exact hMS G (L ⊔ c.R1) c.R1 L (c.isMSPair hN) hcomp c.coe_sup_R1
    ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩

theorem c134Q_le : c134Q (L ⊔ c.R1) L ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  unfold c134Q
  rw [c.sup_R1_eq, ← c.Q, Subgroup.commutator_le]
  intro q hq l hl
  have hlN : l ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hl)
  rw [commutatorElement_def, show q * l * q⁻¹ * l⁻¹ = q * (l * q⁻¹ * l⁻¹) by group]
  exact Subgroup.mul_mem _ hq ((Subgroup.mem_normalizer_iff.1 hlN _).1 (Subgroup.inv_mem _ hq))

theorem V_le_c134Q : V ≤ c134Q (L ⊔ c.R1) L := by
  unfold c134Q
  rw [c.sup_R1_eq]
  calc V = ⁅V, L⁆ := c.f.commutator.symm
    _ ≤ ⁅pCoreOf 2 (L ⊔ T), L⁆ := Subgroup.commutator_mono c.V_le_Q le_rfl

theorem V_le_center_c134Q : V ≤ centerOf (c134Q (L ⊔ c.R1) L) :=
  le_inf c.V_le_c134Q (Subgroup.le_centralizer_iff.mp (c.c134Q_le.trans inf_le_right))

theorem z_fix : ∀ a ∈ L, a * z * a⁻¹ = z := fun a ha => by
  rw [(Subgroup.mem_centralizer_iff.1 c.f.mem_zV.2 a ha), mul_inv_cancel_right]

theorem not_case_le_four {i : ℕ} (hi : C134CorrLocal.IsC134CaseCorr i (L ⊔ c.R1) c.R1 L)
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
    obtain ⟨⟨n, F, _, _, α, -, hα, -, -, -, hU, -, -, -⟩, -⟩ := hi
    have hzU : z ∈ ⁅centerOf (c134Q (L ⊔ c.R1) L), L⁆ := by
      have h1 : V ≤ ⁅centerOf (c134Q (L ⊔ c.R1) L), L⁆ := by
        calc V = ⁅V, L⁆ := c.f.commutator.symm
          _ ≤ _ := Subgroup.commutator_mono c.V_le_center_c134Q le_rfl
      exact h1 c.f.mem_zV.1
    exact c.z_ne_one (Subgroup.mem_bot.mp (A38c10.MS.mem_of_fixed hα.1 hU hzU c.z_fix))

theorem card_c134Q_of_case5 (hi : IsC134Case5 (L ⊔ c.R1) c.R1 L) :
    Nat.card (c134Q (L ⊔ c.R1) L) = 16 := by
  obtain ⟨⟨α, -, hcard, hmod⟩, -⟩ := hi
  obtain ⟨-, hle, β, hβ, hker, -⟩ := hmod
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  have h2 : Nat.card (↥(c134Q (L ⊔ c.R1) L) ⧸ β.ker) = 8 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβ).toEquiv]
    simp [Nat.card_eq_fintype_card]
  have h3 : Nat.card β.ker = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
  rw [h1, h2, h3]

theorem commutator_Q_eq (hMS : C134L32Corr)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ⁅pCoreOf 2 (L ⊔ T), L⁆ = V := by
  obtain ⟨i, hi⟩ := c.exists_c134Case hMS hN
  have hi5 : i = 5 := by
    by_contra h5
    rcases (by omega : i ≤ 4 ∨ 5 < i) with h | h
    · exact c.not_case_le_four hi h
    · revert hi
      unfold C134CorrLocal.IsC134CaseCorr
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
