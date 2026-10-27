module

public import CFSG.Quasithin.MS93.MSPOmega
public import CFSG.Quasithin.MS93.S5Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S510

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem rad_eq_of_transv {v : MSP.V4 F} (hv : v ≠ 0) {c₀ : F} (hc₀ : c₀ ≠ 0)
    {g : MSP.Sp4 F} (hg : ∀ x ∈ MSP.perp (F ∙ v), MSP.mat g *ᵥ x - x ∈ F ∙ v)
    (hx₀ : ∃ x₀ ∈ MSP.perp (F ∙ v), MSP.mat g *ᵥ x₀ ≠ x₀) (s : F) :
    ∃ y y' : Multiplicative (MSP.V4 F × F), (Multiplicative.toAdd y').1 ∈ MSP.perp (F ∙ v) ∧
      Multiplicative.ofAdd ((0 : MSP.V4 F), s) =
        (omega5Act F (MSP.transv v c₀) y * y⁻¹) * (omega5Act F g y' * y'⁻¹)⁻¹ := by
  obtain ⟨x₀, hx₀p, hx₀g⟩ := hx₀
  obtain ⟨e₀, he₀⟩ := Submodule.mem_span_singleton.1 (hg x₀ hx₀p)
  have he₀0 : e₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at he₀
    exact hx₀g (sub_eq_zero.1 he₀.symm)
  obtain ⟨e, he⟩ := isSquare_of_charTwo' (s * c₀)
  obtain ⟨w, hw⟩ := MSP.exists_form_eq_one hv
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨x', hx'⟩ : ∃ x' : MSP.V4 F, x' = (e * e₀⁻¹) • x₀ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : MSP.V4 F, x = (e * c₀⁻¹) • w := ⟨_, rfl⟩
  have hx'p : x' ∈ MSP.perp (F ∙ v) := hx' ▸ Submodule.smul_mem _ _ hx₀p
  have hgx' : MSP.mat g *ᵥ x' = x' + e • v := by
    have : MSP.mat g *ᵥ x' - x' = e • v := by
      rw [hx', Matrix.mulVec_smul, ← smul_sub, ← he₀, smul_smul, mul_assoc, inv_mul_cancel₀ he₀0,
        mul_one]
    rw [← this]
    abel
  have hvx : MSP.form F v x = e * c₀⁻¹ := by
    rw [hx, map_smul, smul_eq_mul, hw, mul_one]
  have htx : MSP.mat (MSP.transv v c₀) *ᵥ x = x + e • v := by
    rw [MSP.transv_mulVec, hvx, mul_comm e, ← mul_assoc, mul_inv_cancel₀ hc₀, one_mul]
  have hvx' : MSP.form F v x' = 0 := MSP.mem_perp_span.1 hx'p
  have hQ : ∀ u : MSP.V4 F, MSP.quad₀ (u + e • v) =
      MSP.quad₀ u + e ^ 2 * MSP.quad₀ v - e * MSP.form F v u := by
    intro u
    rw [MSP.isQuadOf_quad₀.map_add, MSP.isQuadOf_quad₀.map_smul, map_smul, smul_eq_mul,
      MSP.form_swap u v]
    ring
  refine ⟨Multiplicative.ofAdd (x, 0), Multiplicative.ofAdd (x', 0), hx'p, ?_⟩
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv, MSP.toAdd_omega5Act, toAdd_ofAdd]
  rw [htx, hgx']
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_neg]
    abel
  · simp only [Prod.snd_add, Prod.snd_neg]
    rw [hQ x, hQ x', hvx, hvx']
    have hs : s = e * e * c₀⁻¹ := by
      rw [← he, mul_assoc, mul_inv_cancel₀ hc₀, mul_one]
    rw [hs]
    linear_combination (e * e * c₀⁻¹ - MSP.quad₀ x + MSP.quad₀ x') * h2

end Model

section ClaimX

variable {G : Type} [Group G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem uq_inf_le_of_transv (hd : S5.IsSp4Data M T L k F a)
    {ψ : Multiplicative (MSP.V4 F × F) →* G} (hψU : ∀ y, ψ y ∈ Uq M T L)
    (hψs : ∀ u ∈ Uq M T L, ∃ y, ψ y = u)
    (hψe : ∀ (m : ↥M) y, ψ (omega5Act F (a m) y) = (m : G) * ψ y * (m : G)⁻¹)
    (hψZ : ∀ y, ψ y ∈ Subgroup.centralizer (L : Set G) ↔ y ∈ omega5Rad F)
    {E A₀ : Subgroup G} (hEM : E ≤ M) {v : MSP.V4 F} (hv : v ≠ 0)
    (hEX : (E.subgroupOf M).map a ≤ MSP.xPoint (F ∙ v)) (hE1 : (E.subgroupOf M).map a ≠ ⊥)
    {a₀ : ↥M} (ha₀ : (a₀ : G) ∈ A₀)
    (hg : ∀ x ∈ MSP.perp (F ∙ v), MSP.mat (a a₀) *ᵥ x - x ∈ F ∙ v)
    (hx₀ : ∃ x₀ ∈ MSP.perp (F ∙ v), MSP.mat (a a₀) *ᵥ x₀ ≠ x₀) :
    Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤
      ⁅Uq M T L, E⁆ ⊔ ⁅Uq M T L ⊓ Subgroup.centralizer (E : Set G), A₀⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hd.2.1
  obtain ⟨e, heE, he1⟩ : ∃ e : ↥M, (e : G) ∈ E ∧ a e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hE1
    rw [eq_bot_iff]
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_bot.2 (hcon e (Subgroup.mem_subgroupOf.1 he))
  obtain ⟨c₀, hc₀⟩ := (MSP.mem_xPoint_span hv).1 (hEX ⟨e, Subgroup.mem_subgroupOf.2 heE, rfl⟩)
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [MSP.transv_zero] at hc₀
    exact he1 hc₀.symm
  have hfixE : ∀ y : Multiplicative (MSP.V4 F × F),
      (Multiplicative.toAdd y).1 ∈ MSP.perp (F ∙ v) →
        ψ y ∈ Subgroup.centralizer (E : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro e' he'
    have hxe : MSP.mat (a ⟨e', hEM he'⟩) *ᵥ (Multiplicative.toAdd y).1 =
        (Multiplicative.toAdd y).1 :=
      hEX ⟨⟨e', hEM he'⟩, Subgroup.mem_subgroupOf.2 he', rfl⟩ _ hy
    have hfix : omega5Act F (a ⟨e', hEM he'⟩) y = y := by
      apply Multiplicative.toAdd.injective
      rw [MSP.toAdd_omega5Act, hxe]
      refine Prod.ext rfl ?_
      show (Multiplicative.toAdd y).2 + MSP.quad₀ (Multiplicative.toAdd y).1 +
        MSP.quad₀ (Multiplicative.toAdd y).1 = (Multiplicative.toAdd y).2
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have h1 := hψe ⟨e', hEM he'⟩ y
    rw [hfix] at h1
    calc e' * ψ y = e' * ψ y * e'⁻¹ * e' := by group
      _ = ψ y * e' := by rw [← h1]
  rintro z ⟨hzU, hzL⟩
  obtain ⟨y₀, rfl⟩ := hψs z hzU
  have hy₀ : (Multiplicative.toAdd y₀).1 = 0 := (hψZ y₀).1 hzL
  have ey₀ : y₀ = Multiplicative.ofAdd ((0 : MSP.V4 F), (Multiplicative.toAdd y₀).2) := by
    apply Multiplicative.toAdd.injective
    exact Prod.ext hy₀ rfl
  obtain ⟨y, y', hy', hyy⟩ := rad_eq_of_transv hv hc₀0 hg hx₀ (Multiplicative.toAdd y₀).2
  rw [ey₀, hyy, hc₀, map_mul, map_inv, map_mul, map_mul, map_inv, map_inv, hψe, hψe]
  refine mul_mem (Subgroup.mem_sup_left ?_) (inv_mem (Subgroup.mem_sup_right ?_))
  · rw [Subgroup.commutator_comm]
    have := Subgroup.commutator_mem_commutator heE (hψU y)
    rwa [commutatorElement_def] at this
  · rw [Subgroup.commutator_comm]
    have := Subgroup.commutator_mem_commutator ha₀
      (Subgroup.mem_inf.2 ⟨hψU y', hfixE y' hy'⟩)
    rwa [commutatorElement_def] at this

end ClaimX

end S510

end CFSG.Quasithin.MS93
