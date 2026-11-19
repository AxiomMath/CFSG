module

public import CFSG.RankThree.GF2n.Tim77.Cor2BetaBasic
public import CFSG.Goldschmidt.Basic

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup
open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups

@[expose] def Cor2BetaShultDecompStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {S : Sylow 2 G} {t : G} (_hs : ShultSetup S t),
    ∃ E Y : Subgroup G, Cor2BetaDecomp (normalClosure ({t} : Set G)) E Y

@[expose] def Cor2BetaComponentDataStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {S : Sylow 2 G} {t : G} (_hs : ShultSetup S t)
    {N : Subgroup G} [N.Normal]
    (_hN : N = CFSG.Goldschmidt.oddCoreOf (normalClosure ({t} : Set G)))
    {Kb : Subgroup (G ⧸ N)}
    (_hK : IsComponentOf Kb ((normalClosure ({t} : Set G)).map (QuotientGroup.mk' N))),
    CFSG.BenderSuzuki.IsBenderGroup (↥Kb ⧸ Subgroup.center ↥Kb) ∧
      ∃ V : Subgroup (G ⧸ N), V ≤ Kb ∧
        V ≤ (CFSG.LargeExtraspecial.S11.wcl t).map (QuotientGroup.mk' N) ∧ IsKleinFour ↥V ∧
        ∀ v ∈ V, v ≠ 1 → ∃ k ∈ Kb, k * v ≠ v * k

@[expose] def Cor2BetaNormalizesComponentStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {S : Sylow 2 G} {t : G} (_hs : ShultSetup S t)
    {E Y : Subgroup G} (_hd : Cor2BetaDecomp (normalClosure ({t} : Set G)) E Y) {a : G}
    (_haH : a ∈ normalizer (normalClosure ({t} : Set G) : Set G))
    (_hac : ∀ w ∈ CFSG.LargeExtraspecial.S11.wcl t, a * w = w * a) {K : Subgroup G}
    (_hK : IsComponentOf K (normalClosure ({t} : Set G))), a ∈ normalizer (K : Set G)

@[expose] def Cor2BetaInnerOnComponentStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {S : Sylow 2 G} {t : G} (_hs : ShultSetup S t)
    {E Y : Subgroup G} (_hd : Cor2BetaDecomp (normalClosure ({t} : Set G)) E Y) {a : G}
    (_ha2 : a * a = 1) (_haH : a ∈ normalizer (normalClosure ({t} : Set G) : Set G))
    (_hac : ∀ w ∈ CFSG.LargeExtraspecial.S11.wcl t, a * w = w * a)
    (_hstar : ∀ g : G, a * (g * t * g⁻¹) = (g * t * g⁻¹) * a →
      g * t * g⁻¹ ∈ CFSG.LargeExtraspecial.S11.wcl t) {K : Subgroup G}
    (_hK : IsComponentOf K (normalClosure ({t} : Set G))),
    ∃ k ∈ K, ∀ x ∈ K, a * x * a⁻¹ = k * x * k⁻¹

end CFSG.RankThree.GF2n.Tim77
