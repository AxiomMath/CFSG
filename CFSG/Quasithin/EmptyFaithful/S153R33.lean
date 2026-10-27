module

public import CFSG.Quasithin.EmptyFaithful.S153H33
public import CFSG.Quasithin.EmptyFaithful.S153D52
public import CFSG.Quasithin.EmptyFaithful.S153D26

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153R

section Perfect

variable {G : Type} [Group G]

theorem le_of_isPerfect_of_le_sup_solvable {N D K : Subgroup G}
    (hDN : D ≤ Subgroup.normalizer (N : Set G)) (hKND : K ≤ N ⊔ D)
    [Group.IsSolvable ↥D] [Group.IsPerfect ↥K] : K ≤ N := by
  set X : Subgroup G := Subgroup.normalizer (N : Set G) with hX
  have hNX : N ≤ X := Subgroup.le_normalizer
  have hKX : K ≤ X := hKND.trans (sup_le hNX hDN)
  have hnorm : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr le_rfl
  let π : ↥X →* ↥X ⧸ N.subgroupOf X := QuotientGroup.mk' (N.subgroupOf X)
  let ψ : ↥K →* ↥X ⧸ N.subgroupOf X := π.comp (Subgroup.inclusion hKX)
  let φ : ↥D →* ↥X ⧸ N.subgroupOf X := π.comp (Subgroup.inclusion hDN)
  have hψφ : ψ.range ≤ φ.range := by
    rintro _ ⟨k, rfl⟩
    have hk : (k : G) ∈ ((D ⊔ N : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hKND k.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right D N hDN] at hk
    obtain ⟨d, hd, n, hn, hdn⟩ := hk
    refine ⟨⟨d, hd⟩, ?_⟩
    have h1 : π ⟨n, hNX hn⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hn)
    have e : π (Subgroup.inclusion hKX k) =
        π (Subgroup.inclusion hDN ⟨d, hd⟩) * π ⟨n, hNX hn⟩ := by
      rw [← map_mul]
      exact congrArg π (Subtype.ext hdn.symm)
    show π (Subgroup.inclusion hDN ⟨d, hd⟩) = π (Subgroup.inclusion hKX k)
    rw [e, h1, mul_one]
  have : Group.IsSolvable ↥φ.range :=
    Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
  have : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have : Group.IsSolvable ↥ψ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hψφ)
  intro k hk
  have h1 : ψ ⟨k, hk⟩ = 1 := by
    have := S153D.eq_one_of_isPerfect_of_isSolvable (⟨ψ ⟨k, hk⟩, ⟨_, rfl⟩⟩ : ↥ψ.range)
    exact congrArg Subtype.val this
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

end Perfect

variable {G : Type} [Group G] [Finite G]

theorem input33CharTwoSup_holds (h113 : StageLemma14113) : Input33CharTwoSup := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t _hS25 c hL L₁ hL₁ hN hcL hnot
  have hDI : Yp ⊔ Sgp153 T V₁ ≤ I := c.inH.1.1
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans hDI
  have hL₁I : L₁ ≤ I := hL₁.trans (conjClosure_le fun s hs l hl =>
    I.mul_mem (I.mul_mem (hSI hs) (hL.1 hl)) (I.inv_mem (hSI hs)))
  have hXn : L₁ ⊔ (Yp ⊔ Sgp153 T V₁) ≤ Subgroup.normalizer (L₁ : Set G) :=
    sup_le Subgroup.le_normalizer hN
  have hL₁ne : L₁ ≠ ⊥ := fun hb => hnot (hb ▸ bot_le)
  have hO₂ : pCoreOf 2 L₁ ≠ ⊥ := by
    intro hb
    apply hL₁ne
    have h1 : L₁ ⊓ Subgroup.centralizer (pCoreOf 2 L₁ : Set G) ≤ pCoreOf 2 L₁ := hcL
    rw [hb] at h1
    rw [eq_bot_iff]
    intro x hx
    refine Subgroup.mem_bot.mpr (Subgroup.mem_bot.mp (h1 ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩))
    rw [show (y : G) = 1 from by simpa using hy, mul_one, one_mul]
  have hO₂X : pCoreOf 2 L₁ ≤ pCoreOf 2 (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L₁).trans le_sup_left)
      (hXn.trans (normalizer_le_normalizer_pCoreOf 2 L₁)) (pCoreOf_isPGroup 2 L₁)
  have hX : IsHPlus Yp (Sgp153 T V₁) M (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) :=
    ⟨⟨le_sup_right, fun hb => hO₂ (le_bot_iff.mp (hO₂X.trans hb.le))⟩,
      fun hXM => hnot (le_inf (le_sup_left.trans hXM) hL₁I)⟩
  have hodd : oddCoreIn (L₁ ⊔ (Yp ⊔ Sgp153 T V₁)) = ⊥ :=
    S153D.input15311Eight_of_stages h113 G T Mc M V₁ V₂ Yp t c.hyp _ hX
  have hsolv : Group.IsSolvable ↥(Yp ⊔ Sgp153 T V₁) := S153D.isSolvable_Yp_sup' h113 c.hyp
  refine DoubleA3.charTwo_of_no_component (fun K hK => ?_) hodd
  have hperf : Group.IsPerfect ↥K := (BenderBranch.isQuasisimple_of_isComponentIn hK).1
  have hKL₁ : K ≤ L₁ := le_of_isPerfect_of_le_sup_solvable hN hK.1
  exact DoubleA3.not_isComponentIn_of_charTwo hcL K
    (BenderBranch.isComponentIn_of_le hK hKL₁ le_sup_left)

end S153R

end CFSG.Quasithin
