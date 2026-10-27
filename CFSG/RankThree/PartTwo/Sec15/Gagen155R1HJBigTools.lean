module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixBigDefs
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofON
public import CFSG.RankThree.PartTwo.KFacts.KS12Moves
public import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

variable {G : Type} [Group G]

theorem big152_of_isTripleCover_on [Finite G] {Y : Subgroup G}
    (h : Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON) :
    Big152 Y := by
  unfold Big152
  rw [KFacts.card_of_isTripleCover h, CFSG.Sporadic.ON.card_ON]
  norm_num

theorem big152_of_surjective {K : Subgroup G} {H : Type*} [Group H] (f : ↥K →* H)
    (hf : Function.Surjective f)
    (h2 : ∀ N : Subgroup H, N.Normal → IsPGroup 2 N → N = ⊥) (h8 : 8 ∣ Nat.card H) :
    Big152 K := by
  have himg_bot : (CFSG.pCore 2 ↥K).map f = ⊥ :=
    h2 _ (Subgroup.Normal.map CFSG.pCore_normal f hf) (IsPGroup.map CFSG.pCore_isPGroup f)
  have hle : CFSG.pCore 2 ↥K ≤ f.ker :=
    (Subgroup.map_eq_bot_iff (CFSG.pCore 2 ↥K)).mp himg_bot
  have hidx : f.ker.index ∣ (CFSG.pCore 2 ↥K).index := Subgroup.index_dvd_of_le hle
  have hker : f.ker.index = Nat.card H := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]
  rw [Subgroup.index_eq_card] at hidx
  unfold Big152
  exact (hker ▸ h8).trans hidx

theorem big152_of_map_isTripleCover_alt6 [Finite G] {K Y : Subgroup G} (hKY : K ≤ Y)
    (h : Sec4.IsTripleCover ↥((K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)))
      (alternatingGroup (Fin 6))) : Big152 K := by
  let Q : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    (K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
  let f : ↥K →* ↥Q :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hKY)).codRestrict Q
      (fun x => Subgroup.mem_map.mpr
        ⟨Subgroup.inclusion hKY x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨m, hm, hmy⟩
    exact ⟨⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩, Subtype.ext hmy⟩
  refine big152_of_surjective f hf (fun N hN hNp => ?_) ?_
  · exact Proof153Twin3.eq_bot_of_isTripleCover h hNp
  · rw [KFacts.card_of_isTripleCover h, card_alternatingGroup_six]
    norm_num

end CFSG.RankThree.PartTwo.Sec15
