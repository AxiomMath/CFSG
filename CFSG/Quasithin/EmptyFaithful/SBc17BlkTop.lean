module

public import CFSG.Quasithin.EmptyFaithful.SBc17BlkStd
public import CFSG.Quasithin.EmptyFaithful.SBc17SL2Syl
public import CFSG.Quasithin.EmptyFaithful.SBc17SL2Coc
public import CFSG.Quasithin.EmptyFaithful.SBc17Blk
public import CFSG.Quasithin.EmptyFaithful.SBc17Out

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc17

theorem sylowConj_holds : SylowConjStatement := fun _ _ _ _ _ hq _ hP hidx =>
  exists_conj_upperSub hq hP hidx

theorem normalizerUpper_holds : NormalizerUpperStatement := fun _ _ _ _ _ _ => normalizer_upperSub

theorem stdPosition_holds : StdPositionStatement := fun hq α hα hker hB =>
  exists_std_position sylowConj_holds normalizerUpper_holds hq α hα hker hB

theorem cocycle_holds : CocycleStatement := fun hq d hd hB => cocycle_eq_zero hq d hd hB

theorem center_holds : CenterStatement := fun hq => center_borelSub hq

theorem innerAut_holds : InnerAutStatement := fun hq φ hφ => inner_of_trivial_mod_upper hq φ hφ

theorem leUpper_holds : LeUpperStatement := by
  intro F _ _ _ _ hq W hW hn
  exact le_upperSub_of_normalized_two hq hW hn

theorem centralizer_block_of_borel_proved {G : Type} [Group G] [Finite G] {L B : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hshort : IsShort2 L) (hlin : IsLin2Type L n) (hB : IsBorelOfBlock L B) :
    B ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (L : Set G) :=
  centralizer_block_of_borel stdPosition_holds cocycle_holds center_holds hn hshort hlin hB

theorem mem_innerSub_of_commutator_two_proved {G : Type} [Group G] [Finite G] {L B W : Subgroup G}
    {k : G} {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n) (hB : IsBorelOfBlock L B)
    (hk : k ∈ Subgroup.normalizer (L : Set G)) (hW : IsPGroup 2 W)
    (hBW : B ≤ Subgroup.normalizer (W : Set G)) (hcomm : ∀ b ∈ B, ⁅b, k⁆ ∈ W) :
    k ∈ innerSub L :=
  mem_innerSub_of_commutator_two stdPosition_holds innerAut_holds leUpper_holds hn hlin hB hk hW hBW
    hcomm

end SBc17

end CFSG.Quasithin
