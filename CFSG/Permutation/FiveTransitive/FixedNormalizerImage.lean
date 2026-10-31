module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.FixedNormalizerImage

open MulAction FixedNormalizerAction

abbrev Ambient {G:Type*} [Group G] {Q:Subgroup G} (B:Subgroup (Normalizer Q)) :=
  B.map (Normalizer Q).subtype
abbrev Restricted {G X:Type*} [Group G] [MulAction G X] {Q:Subgroup G}
    (B:Subgroup (Normalizer Q)) :=
  B.map (toPermHom (Normalizer Q) (Fixed (X:=X) Q)).rangeRestrict

theorem mem_fixed_iff {G X:Type*} [Group G] [MulAction G X]
    {Q:Subgroup G} (B:Subgroup (Normalizer Q)) (x:Fixed (X:=X) Q) :
    x∈fixedPoints (Restricted (X:=X) B) (Fixed (X:=X) Q) ↔
      x.val∈fixedPoints (Ambient B) X := by
  constructor
  · intro hx
    rw [mem_fixedPoints]
    intro r
    obtain ⟨s,hs,he⟩ := r.property
    have h := mem_fixedPoints.mp hx
      ⟨(toPermHom (Normalizer Q) (Fixed (X:=X) Q)).rangeRestrict s,⟨s,hs,rfl⟩⟩
    have h' := congrArg Subtype.val h
    change s.val • x.val=x.val at h'
    change r.val • x.val=x.val
    change s.val=r.val at he
    rwa [he] at h'
  · intro hx
    rw [mem_fixedPoints]
    intro r
    obtain ⟨s,hs,he⟩ := r.property
    apply Subtype.ext
    have h := mem_fixedPoints.mp hx ⟨s.val,⟨s,hs,rfl⟩⟩
    change s.val • x.val=x.val at h
    change (r.val • x).val=x.val
    rw [← he]
    exact h

@[expose] def fixedEquiv {G X:Type*} [Group G] [MulAction G X]
    {Q:Subgroup G} (B:Subgroup (Normalizer Q)) (hQ:Q≤Ambient B) :
    fixedPoints (Restricted (X:=X) B) (Fixed (X:=X) Q) ≃
      fixedPoints (Ambient B) X where
  toFun x := ⟨x.val.val,(mem_fixed_iff B x.val).mp x.property⟩
  invFun x := ⟨⟨x.val,by
    rw [fixed_eq]
    exact mem_fixedPoints.mpr fun q => mem_fixedPoints.mp x.property ⟨q.val,hQ q.property⟩⟩,
    (mem_fixed_iff B _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nontrivial_of_moves {G X:Type*} [Group G] [MulAction G X]
    {Q:Subgroup G} (B:Subgroup (Normalizer Q))
    (hmove:∃r:G,r∈Ambient B ∧ ∃x∈fixedPoints Q X,r • x≠x) :
    Restricted (X:=X) B≠⊥ := by
  obtain ⟨r,hr,x,hx,hmove⟩ := hmove
  obtain ⟨s,hs,he⟩ := hr
  let y:Fixed (X:=X) Q := ⟨x,by rwa [fixed_eq]⟩
  let t := (toPermHom (Normalizer Q) (Fixed (X:=X) Q)).rangeRestrict s
  have ht:t∈Restricted (X:=X) B := ⟨s,hs,rfl⟩
  intro hbot
  have ht1:t=1 := by simpa [hbot] using ht
  have hty:t • y=y := by rw [ht1,one_smul]
  have hv := congrArg Subtype.val hty
  change s.val • x=x at hv
  exact hmove (he ▸ hv)

theorem semiregular {G X:Type*} [Group G] [MulAction G X]
    {Q:Subgroup G} (B:Subgroup (Normalizer Q))
    (hsemi:∀r:G,r∈Ambient B → r∉Q → ∀x∈fixedPoints Q X,
      x∉fixedPoints (Ambient B) X → r • x≠x) :
    ∀t:Image (X:=X) Q,t∈Restricted (X:=X) B → t≠1 →
      ∀x:Fixed (X:=X) Q,x∉fixedPoints (Restricted (X:=X) B) (Fixed (X:=X) Q) →
        t • x≠x := by
  intro t ht ht1 x hx
  obtain ⟨r,hr,rfl⟩ := ht
  have hrQ:r.val∉Q := by
    intro hrQ
    apply ht1
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro y
    apply Subtype.ext
    have hy:y.val∈fixedPoints Q X := by simpa only [fixed_eq] using y.property
    exact mem_fixedPoints.mp hy ⟨r.val,hrQ⟩
  have hxQ:x.val∈fixedPoints Q X := by simpa only [fixed_eq] using x.property
  have hxA:x.val∉fixedPoints (Ambient B) X := fun h => hx ((mem_fixed_iff B x).mpr h)
  intro he
  exact hsemi r.val ⟨r,hr,rfl⟩ hrQ x.val hxQ hxA (congrArg Subtype.val he)

end FiveTransitive.FixedNormalizerImage

end CFSG
