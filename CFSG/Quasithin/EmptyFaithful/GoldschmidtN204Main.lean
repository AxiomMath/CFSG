module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204Five
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204Cen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204Mod

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.N204
open scoped commutatorElement Pointwise

set_option linter.unusedSectionVars false

@[expose] def Input15204F112Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5),
    Ctx15204 T Mc M H K₁ K₂ π → pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥ →
    IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁) →
    CharTwoMod (g1Of T Mc M K₁) (pCoreOf 2 (g0Of T Mc M K₁)) →
    CharTwoMod (g2Of T K₁) (pCoreOf 2 (g0Of T Mc M K₁)) → False

variable {G : Type} [Group G] [Finite G]

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem charTwoMod_G₂ (hcen : ∀ k ∈ K₁, ∀ q ∈ pCoreOf 2 (g0Of T Mc M K₁), k * q = q * k) :
    CharTwoMod (g2Of T K₁) (pCoreOf 2 (g0Of T Mc M K₁)) := by
  have hX : g2Of T K₁ ≤ Subgroup.normalizer (pCoreOf 2 (g0Of T Mc M K₁) : Set G) :=
    c.G₂_le_G₀.trans (le_normalizer_pCoreOf 2 _)
  refine charTwoMod_of_odd hX fun x hx hodd hxP => ?_
  have hxK : x ∈ K₁ := mem_of_odd_of_mem_sup c.S_pgroup S_le_normalizer_K₁ hx hodd
  exact eq_one_of_odd_of_centralizes c.charTwo_K₁S hx hodd (hcen x hxK) hxP

theorem charTwoMod_G₁ (hJ : thompsonJ T ≤ sOf T K₁) (hU : IsUniqueM (yOf152 T Mc M ⊔ T) M)
    (hne : pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥) (hG₀ : ¬ CharTwo (g0Of T Mc M K₁))
    (hcen : ∀ k ∈ K₁, ∀ q ∈ pCoreOf 2 (g0Of T Mc M K₁), k * q = q * k) :
    CharTwoMod (g1Of T Mc M K₁) (pCoreOf 2 (g0Of T Mc M K₁)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₀ := pCoreOf 2 (g0Of T Mc M K₁) with hQ₀
  set P₁ := pCoreOf 2 (g1Of T Mc M K₁) with hP₁
  have hX : g1Of T Mc M K₁ ≤ Subgroup.normalizer (Q₀ : Set G) :=
    c.G₁_le_G₀.trans (le_normalizer_pCoreOf 2 _)
  refine charTwoMod_of_odd hX fun x hx hodd hxP => ?_
  by_contra hx1
  have hord1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hord1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := Nat.odd_iff.mp hodd
    omega
  set x' := x ^ (orderOf x / p) with hx'
  have hx'ord : orderOf x' = p := orderOf_pow_orderOf_div (orderOf_pos x).ne' hpd
  have hx'G₁ : x' ∈ g1Of T Mc M K₁ := Subgroup.pow_mem _ hx _
  have hx'odd : Odd (orderOf x') := by rw [hx'ord]; exact hp.odd_of_ne_two hp2
  have hx'G₀ : x' ∈ g0Of T Mc M K₁ := c.G₁_le_G₀ hx'G₁
  have hxG₀ : x ∈ g0Of T Mc M K₁ := c.G₁_le_G₀ hx
  have hx'P : ∀ q ∈ P₁, ⁅x', q⁆ ∈ Q₀ := fun q hq => c.commutator_pow_mem hxG₀ hxP _ hq
  have hx'N : x' ∈ yOf152 T Mc M ⊔ borelOf K₁ (sOf T K₁) := by
    refine mem_of_odd_of_mem_sup c.S_pgroup c.S_le_normalizer_YB₂ ?_ hx'odd
    rw [← c.G₁_eq]
    exact hx'G₁
  have hx'p : x' ^ p ^ 1 = 1 := by rw [pow_one, ← hx'ord]; exact pow_orderOf_eq_one x'
  have hconj : ∀ g ∈ yOf152 T Mc M ⊔ borelOf K₁ (sOf T K₁), ∀ q ∈ P₁,
      ⁅g⁻¹ * x' * g, q⁆ ∈ Q₀ := by
    intro g hg q hq
    have hgG₁ : g ∈ g1Of T Mc M K₁ := by
      rw [c.G₁_eq]
      exact Subgroup.mem_sup_left hg
    have hgq : g * q * g⁻¹ ∈ P₁ := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 _ hgG₁) q).mp hq
    have e : ⁅g⁻¹ * x' * g, q⁆ = g⁻¹ * ⁅x', g * q * g⁻¹⁆ * g := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hg0 : g⁻¹ ∈ Subgroup.normalizer (Q₀ : Set G) :=
      Subgroup.inv_mem _ (hX hgG₁)
    have := (Subgroup.mem_normalizer_iff.mp hg0 _).mp (hx'P _ hgq)
    simpa using this
  have hconjord : ∀ g : G, orderOf (g⁻¹ * x' * g) = p := by
    intro g
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x'
    simpa [hx'ord, MulAut.conj_apply] using this
  by_cases h5 : p = 5
  · subst h5
    obtain ⟨g, hg, hgy⟩ := c.exists_conj_mem_Y (k := 1) hx'N hx'p
    apply hG₀
    exact c.charTwo_G₀_of_five hJ hU hne hgy (hconjord g) (hconj g hg)
  · obtain ⟨g, hg, hgb⟩ := c.exists_conj_mem_B₂ hp hp2 h5 hx'N hx'p
    have hgG₁ : g ∈ g1Of T Mc M K₁ := by
      rw [c.G₁_eq]
      exact Subgroup.mem_sup_left hg
    have hbG₁ : g⁻¹ * x' * g ∈ g1Of T Mc M K₁ :=
      mul_mem (mul_mem (Subgroup.inv_mem _ hgG₁) hx'G₁) hgG₁
    have hb1 : g⁻¹ * x' * g = 1 :=
      eq_one_of_odd_of_centralizes c.charTwo_L₁SB hbG₁
        (by rw [hconjord g]; exact hp.odd_of_ne_two hp2)
        (fun q hq => hcen _ (F1.borelOf_le _ _ hgb) q hq) (hconj g hg)
    have := hconjord g
    rw [hb1, orderOf_one] at this
    exact hp.one_lt.ne this

end Ctx15204

theorem input15204CharTwoLc_of_F112Q (h15112 : StageLemma15112) (h15206 : StageLemma15206)
    (h15207 : StageLemma15207) (hQ : Input15204F112Q) : Input15204CharTwoLc := by
  intro G _ _ T Mc M H K₁ K₂ π c ho2 hS hP Lc hLc hKL hn
  by_contra hnot
  have hJ := c.thompsonJ_le_S h15112 h15206 h15207
  have hU := c.isUniqueM_YT h15206 h15207
  have hodd := c.oddCoreIn_G₀_eq_bot ho2
  have hLcG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp hLc
  have hq : CFSG.IsQuasisimple ↥Lc := isQuasisimple_of_not_charTwo_of_oddCore hLc hodd hnot
  have hXL : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLcG).mp hn
  have hcomm : ⁅Lc, pCoreOf 2 (g0Of T Mc M K₁)⁆ = ⊥ :=
    commutator_eq_bot_of_quasisimple hq hLcG hXL (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      (le_normalizer_pCoreOf 2 _) (pCoreOf_isPGroup 2 _)
  have hcenL : ∀ k ∈ Lc, ∀ q ∈ pCoreOf 2 (g0Of T Mc M K₁), k * q = q * k := fun k hk q hq =>
    ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hk)) q hq).symm
  have hG₀ : ¬ CharTwo (g0Of T Mc M K₁) := fun h =>
    hnot (Ctx15204.charTwo_Lc_of_charTwo_G₀ hn hLcG h)
  exact hQ G T Mc M H K₁ K₂ π c ho2 hS
    (c.charTwoMod_G₁ hJ hU ho2 hG₀ fun k hk => hcenL k (hKL hk))
    (c.charTwoMod_G₂ fun k hk => hcenL k (hKL hk))

theorem input15204Dichotomy_of_F112Q (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h15112 : StageLemma15112) (h15206 : StageLemma15206) (h15207 : StageLemma15207)
    (hQ : Input15204F112Q) : Input15204Dichotomy :=
  input15204Dichotomy_of_charTwoLc h37 h38 h39
    (input15204CharTwoLc_of_F112Q h15112 h15206 h15207 hQ)

end CFSG.Quasithin.He9
