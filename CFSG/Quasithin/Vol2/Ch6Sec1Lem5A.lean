module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem6Three
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Mod
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516R

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem isA5ModuleSum_inf_centralizer_ch615 {L U : Subgroup G} (hU : IsA5ModuleSum L U)
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) : U ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rcases hU with hU1 | ⟨W₁, W₂, h₁, h₂, hdisj, hsup⟩
  · exact hU1.inf_centralizer_eq_bot
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxC⟩
  have hW₁U : W₁ ≤ U := hsup ▸ le_sup_left
  have hW₂U : W₂ ≤ U := hsup ▸ le_sup_right
  have hc : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
    hUc a (hW₁U ha) b (hW₂U hb)
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute W₁ W₂ hc
  have hx : x ∈ ((W₁ ⊔ W₂ : Subgroup G) : Set G) := by rw [hsup]; exact hxU
  rw [hset] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
  have hfix : ∀ l ∈ L, l * a * l⁻¹ = a ∧ l * b * l⁻¹ = b := by
    intro l hl
    have hla : l * a * l⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (h₁.1 hl) a).mp ha
    have hlb : l * b * l⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (h₂.1 hl) b).mp hb
    have hab : l * (a * b) * l⁻¹ = a * b := by
      rw [Subgroup.mem_centralizer_iff.mp hxC l hl, mul_inv_cancel_right]
    have e1 : (l * a * l⁻¹) * (l * b * l⁻¹) = a * b := by
      calc (l * a * l⁻¹) * (l * b * l⁻¹) = l * (a * b) * l⁻¹ := by group
        _ = a * b := hab
    have hd : (l * a * l⁻¹)⁻¹ * a ∈ W₁ ⊓ W₂ := by
      refine ⟨W₁.mul_mem (W₁.inv_mem hla) ha, ?_⟩
      have e : (l * a * l⁻¹)⁻¹ * a = (l * b * l⁻¹) * b⁻¹ := by
        calc (l * a * l⁻¹)⁻¹ * a = (l * a * l⁻¹)⁻¹ * (a * b) * b⁻¹ := by group
          _ = (l * a * l⁻¹)⁻¹ * ((l * a * l⁻¹) * (l * b * l⁻¹)) * b⁻¹ := by rw [e1]
          _ = (l * b * l⁻¹) * b⁻¹ := by group
      rw [e]
      exact W₂.mul_mem hlb (W₂.inv_mem hb)
    rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at hd
    refine ⟨hd, ?_⟩
    rw [hd] at e1
    exact mul_left_cancel e1
  have haC : a ∈ W₁ ⊓ Subgroup.centralizer (L : Set G) := ⟨ha,
    Subgroup.mem_centralizer_iff.mpr fun l hl => by
      have := (hfix l hl).1
      calc l * a = (l * a * l⁻¹) * l := by group
        _ = a * l := by rw [this]⟩
  have hbC : b ∈ W₂ ⊓ Subgroup.centralizer (L : Set G) := ⟨hb,
    Subgroup.mem_centralizer_iff.mpr fun l hl => by
      have := (hfix l hl).2
      calc l * b = (l * b * l⁻¹) * l := by group
        _ = b * l := by rw [this]⟩
  rw [h₁.inf_centralizer_eq_bot, Subgroup.mem_bot] at haC
  rw [h₂.inf_centralizer_eq_bot, Subgroup.mem_bot] at hbC
  rw [haC, hbC, mul_one]
  exact Subgroup.one_mem _

namespace Hyp611

theorem reduced_ch615 (h614 : Stmt6_1_4) (h : Hyp611 G T M L V n) :
    Hyp611 G T M L (reducedAggregate (L ⊔ T)) n := by
  have hVR := h.le_reducedAggregate
  have hRred := isTwoReducedIn_reducedAggregate (L ⊔ T)
  have hVL : ⁅V, L⁆ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ := Subgroup.commutator_mono hVR le_rfl
  have hRL0 : ⁅reducedAggregate (L ⊔ T), L⁆ ≠ ⊥ := fun h0 =>
    h.module.2.2 (eq_bot_iff.mpr (h0 ▸ hVL))
  have hRLR : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ reducedAggregate (L ⊔ T) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hRred.2.1)
  have hRc : ∀ a ∈ ⁅reducedAggregate (L ⊔ T), L⁆, ∀ b ∈ ⁅reducedAggregate (L ⊔ T), L⁆,
      a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hRred.2.2.1 (hRLR ha) (hRLR hb)
  exact
    { toHyp5_0_1 := h.toHyp5_0_1
      module := ⟨hRred.1, (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hRred).2, hRL0⟩
      not_a5 := by
        rintro ⟨rfl, hA5⟩
        have hq := h614 G T M L V 2 h
        have hC : ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rw [← isA5ModuleSum_inf_centralizer_ch615 hA5 hRc]
          exact ⟨hVL hx.1, hx.2⟩
        exact false_of_isNatModCh5_le_isA5ModuleSum (isNatModCh5_of_isNatQuotCh5 hq hC) hVL
          hRc hA5
      nParam_eq_one := h.nParam_eq_one
      noLie := h.noLie }

theorem omega_le_reduced_ch615 (h : Hyp611 G T M L V n) :
    quasithinOmegaOneCenter T ≤ reducedAggregate (L ⊔ T) :=
  h.toHyp5_0_1.omega_le_reducedAggregate

end Hyp611

end CFSG.Quasithin.H13
