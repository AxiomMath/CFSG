module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapKill
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShapes

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

private theorem wcgapp_subgroupOf_inf_centralizer {Y : Type} [Group Y] {L S : Subgroup Y}
    (hSL : S ≤ L) :
    (S ⊓ centralizer (S : Set Y)).subgroupOf L =
      S.subgroupOf L ⊓ centralizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hxS, hxc⟩
    exact ⟨hxS, fun s' hs' => Subtype.ext (hxc (s' : Y) hs')⟩
  · rintro ⟨hxS, hxc⟩
    exact ⟨hxS, fun s hs => congrArg Subtype.val (hxc ⟨s, hSL hs⟩ hs)⟩

theorem borelKills_pull {Y : Type} [Group Y] {L S T : Subgroup Y} (hSL : S ≤ L) (hTS : T ≤ S)
    (h : BorelKills (S.subgroupOf L) (T.subgroupOf L)) {E : Type} [Group E]
    (hE : ElemAbOrderEight E) (W : Subgroup (MulAut E)) {X : Type} [Group X] (ψ : ↥W →* X)
    (hψ : Function.Surjective ψ) (φ : ↥(L ⊓ normalizer (S : Set Y)) →* X) :
    T.subgroupOf (L ⊓ normalizer (S : Set Y)) ≤ φ.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  let N' : Subgroup ↥L := Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L)
  have hB : (L ⊓ normalizer (S : Set Y)).subgroupOf L = N' := by
    rw [Subgroup.inf_subgroupOf_left]
    exact Subgroup.subgroupOf_normalizer_eq hSL
  have hmem : ∀ g : ↥N', ((g : ↥L) : Y) ∈ L ⊓ normalizer (S : Set Y) := by
    intro g
    have hg : (g : ↥L) ∈ (L ⊓ normalizer (S : Set Y)).subgroupOf L := by
      rw [hB]
      exact g.2
    exact hg
  let j : ↥N' →* ↥(L ⊓ normalizer (S : Set Y)) :=
    { toFun := fun g => ⟨((g : ↥L) : Y), hmem g⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hkill := h E hE W X ψ hψ (φ.comp j)
  let x' : ↥N' := ⟨⟨(x : Y), x.2.1⟩, by rw [← hB]; exact x.2⟩
  have hx' : x' ∈ (T.subgroupOf L).subgroupOf N' := by
    show ((x' : ↥L) : Y) ∈ T
    exact hx
  have hx'ker : (φ.comp j) x' = 1 := hkill hx'
  have hjx : j x' = x := Subtype.ext rfl
  rw [← hjx]
  exact hx'ker

theorem borelGL32SylowOn_of_kills (Sh : ShapePred)
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), Sh L →
      ∀ S : Subgroup Y, IsSylowIn 2 S L → BorelKills (S.subgroupOf L) (S.subgroupOf L)) :
    BorelGL32SylowOn Sh := by
  intro Y _ _ L S hL hSy E _ hE W X _ ψ hψ φ
  exact borelKills_pull hSy.le le_rfl (h Y L hL S hSy) hE W ψ hψ φ

theorem borelGL32CenterOn_of_kills (Sh : ShapePred)
    (h : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), Sh L →
      ∀ S : Subgroup Y, IsSylowIn 2 S L →
        BorelKills (S.subgroupOf L)
          (S.subgroupOf L ⊓ centralizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L))) :
    BorelGL32CenterOn Sh := by
  intro Y _ _ L S hL hSy E _ hE W X _ ψ hψ φ
  have hK : BorelKills (S.subgroupOf L)
      ((S ⊓ centralizer (S : Set Y)).subgroupOf L) := by
    rw [wcgapp_subgroupOf_inf_centralizer hSy.le]
    exact h Y L hL S hSy
  exact borelKills_pull hSy.le inf_le_left hK hE W ψ hψ φ

end CFSG.LocalAnalysis.WeakClosure81

end
