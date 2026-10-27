module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG

namespace FiveTransitive.SylowNormalizerSandwich

theorem sylow_image_eq_inf_normalizer
    {G : Type*} [Group G] {p : ℕ}
    (K H Q : Subgroup G) (R : Sylow p K) (hH : IsPGroup p H)
    (hRH : (R : Subgroup K).map K.subtype ≤ H)
    (hRN : (R : Subgroup K).map K.subtype ≤ Subgroup.normalizer (Q : Set G))
    (hHK : H ⊓ Subgroup.normalizer (Q : Set G) ≤ K) :
    (R : Subgroup K).map K.subtype = H ⊓ Subgroup.normalizer (Q : Set G) := by
  let J := (H ⊓ Subgroup.normalizer (Q : Set G)).subgroupOf K
  let f : J →* H :=
    { toFun := fun x => ⟨x.val.val,x.property.1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : H => z.val) hxy
  have hJ : IsPGroup p J := hH.of_injective f hf
  have hRJ : (R : Subgroup K) ≤ J := by
    intro r hr
    have hrimage : (r:G) ∈ (R : Subgroup K).map K.subtype := ⟨r,hr,rfl⟩
    exact ⟨hRH hrimage,hRN hrimage⟩
  have heq := R.is_maximal' hJ hRJ
  apply le_antisymm (le_inf hRH hRN)
  intro x hx
  let k : K := ⟨x,hHK hx⟩
  have hk : k∈J := hx
  rw [heq] at hk
  exact ⟨k,hk,rfl⟩

theorem lt_sylow_image_of_normalizer_sandwich
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K H Q : Subgroup G) (R : Sylow p K) (hH : IsPGroup p H)
    (hQH : Q < H)
    (hRH : (R : Subgroup K).map K.subtype ≤ H)
    (hRN : (R : Subgroup K).map K.subtype ≤ Subgroup.normalizer (Q : Set G))
    (hHK : H ⊓ Subgroup.normalizer (Q : Set G) ≤ K) :
    Q < (R : Subgroup K).map K.subtype := by
  rw [sylow_image_eq_inf_normalizer K H Q R hH hRH hRN hHK]
  have : Group.IsNilpotent H := hH.isNilpotent
  have hproper : Q.subgroupOf H ≠ ⊤ := by
    intro he
    apply hQH.not_ge
    intro x hx
    have hmem : (⟨x,hx⟩ : H) ∈ Q.subgroupOf H := by rw [he]; trivial
    exact hmem
  have hlt := Group.normalizerCondition_of_isNilpotent (Q.subgroupOf H)
    (lt_top_iff_ne_top.mpr hproper)
  have he : (Subgroup.normalizer (Q : Set G)).comap H.subtype =
      Subgroup.normalizer ((Q.subgroupOf H : Subgroup H) : Set H) := by
    apply Subgroup.comap_normalizer_eq_of_le_range
    simpa only [Subgroup.range_subtype] using hQH.le
  apply lt_of_le_of_ne (le_inf hQH.le Q.le_normalizer)
  intro hEq
  apply hlt.ne
  apply le_antisymm (Q.subgroupOf H).le_normalizer
  intro x hx
  rw [←he] at hx
  have hxQN : (x:G)∈H ⊓ Subgroup.normalizer (Q:Set G) := ⟨x.property,hx⟩
  rw [←hEq] at hxQN
  exact hxQN

end FiveTransitive.SylowNormalizerSandwich

end CFSG
