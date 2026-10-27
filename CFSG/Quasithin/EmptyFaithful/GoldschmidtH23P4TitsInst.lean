module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Inst
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4ActT
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.EmptyFaithful.S14113Layer
public import CFSG.Quasithin.EmptyFaithful.S146F13
public import CFSG.Quasithin.EmptyFaithful.S146F16
public import CFSG.Quasithin.EmptyFaithful.S146P10
public import CFSG.Quasithin.EmptyFaithful.S146P13
public import CFSG.Quasithin.EmptyFaithful.S146P17
public import CFSG.Quasithin.EmptyFaithful.S146P20
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.EmptyFaithful.SBc14Call
public import CFSG.Quasithin.EmptyFaithful.T1515Der2
public import CFSG.Quasithin.EmptyFaithful.T1515Der3
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem false_of_rowTits {L S Y V : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSyl : IsSylowTwoOf (S ⊓ L) L) (hY5 : IsPGroup 5 Y)
    (hYN : Y ≤ Subgroup.normalizer (L : Set G)) (hSY : (S : Set G) * Y = Y * S)
    (hQ : pCoreOf 2 L = ⊥) (hV : V ≤ Subgroup.normalizer (L : Set G)) (hVS : V ≤ S)
    (hVSn : ∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ ∈ V) (hVYn : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V)
    (hVc : Nat.card V ≤ 16) (hVY : ⁅V, Y⁆ = V) (hLV : ⁅L, V⁆ ≠ ⊥)
    (hrow : RowTits (↥L ⧸ CFSG.pCore 2 ↥L)) : False := by
  obtain ⟨ρ, S₀, hX', hY', hXY', hS₀, hsub, hker⟩ := action_data hS2 hSyl hY5 hYN hSY
  generalize hN : Subgroup.normalizer (L : Set G) = N at *
  have hVSN : V ≤ S ⊓ N := le_inf hVS hV
  have hWX : V.subgroupOf N ≤ (S ⊓ N).subgroupOf N := fun x hx => hVSN hx
  have hWXn : ∀ x ∈ (S ⊓ N).subgroupOf N, ∀ w ∈ V.subgroupOf N, x * w * x⁻¹ ∈ V.subgroupOf N :=
    fun x hx w hw => hVSn x hx.1 w hw
  have hWYn : ∀ y ∈ Y.subgroupOf N, ∀ w ∈ V.subgroupOf N, y * w * y⁻¹ ∈ V.subgroupOf N :=
    fun y hy w hw => hVYn y hy w hw
  have hWc : Nat.card (V.subgroupOf N) ≤ 16 := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv]
  have hWY : ⁅V.subgroupOf N, Y.subgroupOf N⁆ = V.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hV,
      Subgroup.map_subgroupOf_eq_of_le hYN, hVY]
  have hWne : ¬ V.subgroupOf N ≤ ρ.ker := by
    intro h
    apply hLV
    refine le_bot_iff.1 (Subgroup.commutator_le.2 fun x hx v hv => ?_)
    have hvk : ρ ⟨v, hV hv⟩ = 1 :=
      MonoidHom.mem_ker.1 (h (show (⟨v, hV hv⟩ : ↥N) ∈ V.subgroupOf N from hv))
    have := (SBc17.mem_cMod.1 (hker ⟨v, hV hv⟩ hvk)).2 x hx
    rw [hQ] at this
    exact this
  exact false_of_overgroup_cen hrow.center hrow.out hrow.cen ρ hX' hY' hXY' hS₀ hsub hWX hWXn
    hWYn hWc hWY hWne

end CFSG.Quasithin.H23P4
