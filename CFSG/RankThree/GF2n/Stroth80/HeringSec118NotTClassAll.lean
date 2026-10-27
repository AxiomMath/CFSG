module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4PartATwo
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTClass
import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTTransportHom
import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTTransportLin

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {G : Type} [Group G] {M Q Z B : Subgroup G}


theorem Ctx.exists_lineElt_of_not_cmSpTransvAt_of_three_le [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {m x : ℕ}
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hnT : ¬ CMSpTransvAt M Q Z B m x a h)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ x) (hm3 : 3 ≤ m)
    (ψ : ↥(Xbar M Q Z B) ≃* StatedSp m F) :
    ∃ a₁ c₁ : Fin m ⊕ Fin m → F, spForm m F a₁ c₁ = 0 ∧
      LinearIndependent F ![a₁, c₁] ∧
      spEquiv (ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩) =
        lineElt spForm_isAlt a₁ c₁ := by
  classical
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφk, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  have hKZ : Nat.card K = Nat.card Z := hD.card
  let Θ : ↥(XbarH M Q Z B) →* StatedSp m F := ψ.toMonoidHom.comp (xbarHToXbar M Q Z B)
  have hΘsurj : Function.Surjective Θ := ψ.surjective.comp (xbarHToXbar_surjective hc)
  have hΘker : ∀ s, Θ s = 1 → φ (s : ↥(H0 M Z)) = 1 := fun s hs => by
    refine (hφk _).mpr ((xbarHToXbar_eq_one_iff s).mp (ψ.injective ?_))
    rw [map_one]
    exact hs
  obtain ⟨ρV, hρV⟩ := hc.exists_rho_factor φ Θ hΘsurj hΘker
  obtain ⟨s₀, hs₀a, hs₀ψ⟩ := hc.exists_lift_a2 (h := h)
  have hΘs₀ : Θ s₀ = ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ := by
    change ψ (xbarHToXbar M Q Z B s₀) = _
    rw [hs₀ψ]
  have hspΘ : ∀ g : Gsp (spForm m F), ∃ s : ↥(XbarH M Q Z B), spEquiv (Θ s) = g := fun g => by
    obtain ⟨t, ht⟩ := hΘsurj ((spEquiv (m := m) (K := F)).symm g)
    exact ⟨t, by rw [ht]; exact MulEquiv.apply_symm_apply _ _⟩
  have hρQ : ∀ g v, cmCommQf B φ (ρV g v) = cmCommQf B φ v := by
    intro g v
    obtain ⟨s, rfl⟩ := hspΘ g
    rw [hρV s]
    exact cmCommQf_cmCommAct hc φ hφQ s v
  obtain ⟨hg2, hg1⟩ := image_mul_self_eq_one_and_ne_one (h := h) ψ
  exact exists_lineElt_of_six_le_finrank (by rw [finrank_spSpace]; omega) spForm_isAlt
    spForm_nondegenerate (cmCommQf B φ) (hc.cmCommQf_nondegenerate hD φ hφπ) ρV hρQ
    (spEquiv (ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩))
    (by rw [← map_mul, hg2, map_one])
    (fun h1 => hg1 ((spEquiv (m := m) (K := F)).injective (h1.trans (map_one _).symm)))
    (by
      rw [← hΘs₀, hρV s₀]
      exact hc.cmCommAct_moved hD hKZ φ hφπ ha2 (by rw [hs₀a]; exact h.1)
        (by rw [hs₀a]; exact h.2))
    (by
      rw [finrank_range_spEquiv_sub_one]
      exact hc.rank_ne_one_of_not_cmSpTransvAt hLm hnT hF ψ)

theorem Ctx.exists_lineElt_of_not_cmSpTransvAt' [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {m x : ℕ}
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hnT : ¬ CMSpTransvAt M Q Z B m x a h)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ x)
    (ψ : ↥(Xbar M Q Z B) ≃* StatedSp m F) :
    3 ≤ m ∧ ∃ a₁ c₁ : Fin m ⊕ Fin m → F, spForm m F a₁ c₁ = 0 ∧
      LinearIndependent F ![a₁, c₁] ∧
      spEquiv (ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩) =
        lineElt spForm_isAlt a₁ c₁ := by
  by_cases hm3 : 3 ≤ m
  · exact ⟨hm3, hc.exists_lineElt_of_not_cmSpTransvAt_of_three_le hLm ha2 hnT hF hm3 ψ⟩
  · have hadm := hLm.admissible
    have hm2 : m = 2 := by have := hadm.2.2.1; omega
    have hx : 2 ≤ x := by
      have hne := hadm.2.2.2
      subst hm2
      by_contra hx
      interval_cases x
      · have h1 : Nat.card F = 1 := by rw [hF]; rfl
        exact absurd h1 (Finite.one_lt_card (α := F)).ne'
      · exact hne rfl
    have hF4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx
    exact hc.exists_lineElt_of_not_cmSpTransvAt hLm ha2 hnT hF hF4 ψ

end CFSG.RankThree.GF2n.Stroth80
