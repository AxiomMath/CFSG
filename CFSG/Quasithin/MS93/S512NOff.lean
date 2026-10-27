module

public import CFSG.Quasithin.MS93.S512NS0

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512N

section Coord

variable {S₀ : Type} [CommGroup S₀] {X : Subgroup (MulAut S₀)} {F' : Type} [Field F']
  {φ : ↥X →* MSP.Sp4 F'} {θ : S₀ ≃* Multiplicative (MSP.V4 F')}

theorem card_fixV_eq_of_coord
    (hθ : ∀ (x : ↥X) (s : S₀), Multiplicative.toAdd (θ ((x : MulAut S₀) s)) =
      MSP.mat (φ x) *ᵥ Multiplicative.toAdd (θ s))
    {A : Subgroup (MulAut S₀)} (hAX : A ≤ X) :
    Nat.card (fixV A) = Nat.card (MSP.fixSp ((A.subgroupOf X).map φ)) := by
  have hiff : ∀ s : S₀, s ∈ fixV A ↔
      Multiplicative.toAdd (θ s) ∈ MSP.fixSp ((A.subgroupOf X).map φ) := by
    intro s
    rw [mem_fixV, MSP.mem_fixSp]
    constructor
    · rintro hs _ ⟨x, hx, rfl⟩
      rw [← hθ, hs _ (Subgroup.mem_subgroupOf.1 hx)]
    · intro hs y hy
      have h1 := hs (φ ⟨y, hAX hy⟩) ⟨⟨y, hAX hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
      rw [← hθ] at h1
      exact θ.injective (Multiplicative.toAdd.injective h1)
  exact Nat.card_congr
    { toFun := fun s => ⟨Multiplicative.toAdd (θ s), (hiff s).1 s.2⟩
      invFun := fun v => ⟨θ.symm (Multiplicative.ofAdd v), (hiff _).2 (by simp)⟩
      left_inv := fun s => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }

theorem exists_point_of_coord [Finite F']
    (hθ : ∀ (x : ↥X) (s : S₀), Multiplicative.toAdd (θ ((x : MulAut S₀) s)) =
      MSP.mat (φ x) *ᵥ Multiplicative.toAdd (θ s))
    {A : Subgroup (MulAut S₀)} (hAX : A ≤ X) (hA1 : A ≠ ⊥)
    (hAf : Nat.card S₀ ≤ Nat.card F' * Nat.card (fixV A)) :
    ∃ p : Submodule F' (MSP.V4 F'), MSP.IsPoint p ∧
      MSP.fixSp ((A.subgroupOf X).map φ) = MSP.perp p ∧
      (A.subgroupOf X).map φ ≤ MSP.xPoint p := by
  set Ab := (A.subgroupOf X).map φ with hAb
  have hφi := injective_of_coord hθ
  have hcS : Nat.card S₀ = Nat.card F' ^ 4 := by
    rw [Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd), MSP.card_V4]
  rw [card_fixV_eq_of_coord hθ hAX, MSP.card_fixSp, hcS] at hAf
  have hq : 1 < Nat.card F' := Finite.one_lt_card
  set d := Module.finrank F' (MSP.fixSp Ab)
  have hd3 : 3 ≤ d := by
    have h1 : Nat.card F' ^ 4 ≤ Nat.card F' ^ (d + 1) :=
      calc Nat.card F' ^ 4 ≤ Nat.card F' * Nat.card F' ^ d := hAf
        _ = Nat.card F' ^ (d + 1) := by ring
    have := (Nat.pow_le_pow_iff_right hq).1 h1
    omega
  have hle4 : d ≤ 4 := by
    have := Submodule.finrank_le (MSP.fixSp Ab)
    simpa using this
  rcases (show d = 3 ∨ d = 4 by omega) with h3 | h4
  · exact MSP.exists_point_of_finrank_fixSp_three h3
  · exfalso
    have h4' : Module.finrank F' (MSP.fixSp Ab) = Module.finrank F' (MSP.V4 F') := by
      rw [show Module.finrank F' (MSP.V4 F') = 4 by simp]
      exact h4
    have htop : MSP.fixSp Ab = ⊤ := Submodule.eq_top_of_finrank_eq h4'
    have hbot := MSP.fixSp_eq_top_iff.1 htop
    apply hA1
    rw [eq_bot_iff]
    intro y hy
    have h1 : φ ⟨y, hAX hy⟩ ∈ Ab := ⟨⟨y, hAX hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have := hφi (h1.trans (map_one φ).symm)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

theorem card_le_of_coord [Finite F']
    (hθ : ∀ (x : ↥X) (s : S₀), Multiplicative.toAdd (θ ((x : MulAut S₀) s)) =
      MSP.mat (φ x) *ᵥ Multiplicative.toAdd (θ s))
    {A : Subgroup (MulAut S₀)} (hAX : A ≤ X) (hA1 : A ≠ ⊥)
    (hAf : Nat.card S₀ ≤ Nat.card F' * Nat.card (fixV A)) : Nat.card A ≤ Nat.card F' := by
  obtain ⟨p, hp, -, hle⟩ := exists_point_of_coord hθ hAX hA1 hAf
  have hφi := injective_of_coord hθ
  have hcA : Nat.card ((A.subgroupOf X).map φ) = Nat.card A := by
    rw [Subgroup.card_map_of_injective hφi]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv
  rw [← hcA, ← MSP.card_xPoint hp]
  exact Subgroup.card_le_of_le hle

end Coord

section Offender

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem relIndex_qv_le_of_offender (h14 : MS14AS)
    (hSQ : SQTKQuot) (hT : S32.TypeFacts) {h : PUHyp M T L} (hd : S5.IsSp4Data M T L k F a)
    {V : Subgroup (puAmalgam h.le).Universal} (hV : SecHyp h V)
    {E : Subgroup (puAmalgam h.le).Universal} (hEs : E ≤ stab _ (baseA (puAmalgam h.le)))
    (hEe : CFSG.Open.IsElemAbelian 2 E)
    (hEW : (S36E.fixSec V (V ⊓ S5.bSub h.le L (baseA _)) E
      (hV.le_stab.trans hV.le_normalizer_inf)).relIndex V ≤ 2 ^ k) :
    (Qv _ (baseA (puAmalgam h.le))).relIndex E ≤ 2 ^ k := by
  by_contra hlt
  push Not at hlt
  obtain ⟨S, _, p, ρ, hs⟩ := hV.exists_secMod
  have := hV.finite_S hs
  obtain ⟨S₀, hne, hS₀, hmin⟩ := exists_minimal_invariant ρ (hV.nontrivial_S hs)
  have hρ := hV.isIrrRep_restrict hs hS₀ hne hmin
  set ρM := (restrict ρ hS₀).comp (eM h.le) with hρM
  set A := (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map (restrict ρ hS₀) with hAdef
  have hAX : A ≤ ρM.range := by
    rintro _ ⟨g, -, rfl⟩
    obtain ⟨m, rfl⟩ := eM_surjective h.le g
    exact ⟨m, rfl⟩
  have hEc : E ≤ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hEe.1
  have hA : IsElemAbelian2 A := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.1 (hEc (Subgroup.mem_subgroupOf.1 hg')) _
        (Subgroup.mem_subgroupOf.1 hg)
    · rintro _ ⟨g, hg, rfl⟩
      rw [← map_pow]
      have : g ^ 2 = 1 := Subtype.ext (by simpa using hEe.2 _ (Subgroup.mem_subgroupOf.1 hg))
      rw [this, map_one]
  have hcA : Nat.card A = (Qv _ (baseA (puAmalgam h.le))).relIndex E :=
    hV.card_map_restrict hs hS₀ hne hmin hEs hEe
  have hidx : (fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ)).index ≤ 2 ^ k := by
    rw [hs.index_fixV hEs (hV.le_stab.trans hV.le_normalizer_inf)]
    exact hEW
  have hAf := hV.card_le_fixV_restrict hs hS₀ hidx
  obtain ⟨F', iF, fF, φ, θ, hcard, -, hθ⟩ := exists_coord h14 hSQ hT h hd hρ hAX hA
    (by rw [hcA]; exact hlt.le) hAf (fun hk2 => hV.range_le_imL hs hd hk2 hS₀ hne hmin)
  have hA1 : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcA
    have : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
    omega
  have hF' : Nat.card F' = 2 ^ k := by rw [Nat.card_eq_fintype_card, hcard]
  have hle := card_le_of_coord hθ hAX hA1 (by rw [hF']; exact hAf)
  rw [hcA, hF'] at hle
  omega

end Offender

end S512N

end CFSG.Quasithin.MS93
