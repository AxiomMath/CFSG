module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.MaximalSylowPointStabilizer

open MulAction

theorem exists_sylow_with_same_image_of_orbit_max
    (K Y : Type*) [Group K] [Finite K] [MulAction K Y]
    {p : ℕ} [Fact p.Prime] (S : Sylow p K) (x : Y)
    (hmax : ∀ k : K, Nat.card (stabilizer S (k • x)) ≤ Nat.card (stabilizer S x)) :
    ∃ T : Sylow p (stabilizer K x),
      (T : Subgroup (stabilizer K x)).map (stabilizer K x).subtype =
        (stabilizer S x).map (S : Subgroup K).subtype := by
  let Q := (stabilizer S x).map (S : Subgroup K).subtype
  have hQp : IsPGroup p Q := (S.isPGroup'.to_subgroup (stabilizer S x)).map _
  have hQx : Q ≤ stabilizer K x := by
    rintro q ⟨r,hr,rfl⟩
    exact hr
  obtain ⟨T,hQT⟩ := hQp.comap_subtype.exists_le_sylow (G := stabilizer K x)
  let R := (T : Subgroup (stabilizer K x)).map (stabilizer K x).subtype
  have hRp : IsPGroup p R := T.isPGroup'.map _
  obtain ⟨U,hRU⟩ := hRp.exists_le_sylow
  obtain ⟨k,hk⟩ := exists_smul_eq K U S
  have hkmap : (U : Subgroup K).map (MulAut.conj k).toMonoidHom = (S : Subgroup K) :=
    congrArg Sylow.toSubgroup hk
  let f : T → stabilizer S (k • x) := fun r =>
    ⟨⟨MulAut.conj k r.val.val, by
      rw [← hkmap]
      exact ⟨r.val.val,hRU ⟨r.val,r.property,rfl⟩,rfl⟩⟩, by
      change (k * r.val.val * k⁻¹) • (k • x) = k • x
      rw [mul_smul,mul_smul,inv_smul_smul,r.val.property]⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply (MulAut.conj k).injective
    exact congrArg (fun q : stabilizer S (k • x) => q.val.val) hab
  have hTcard : Nat.card T ≤ Nat.card (stabilizer S x) :=
    (Nat.card_le_card_of_injective f hf).trans (hmax k)
  have hRcard : Nat.card R = Nat.card T :=
    (Nat.card_congr ((T : Subgroup (stabilizer K x)).equivMapOfInjective
      (stabilizer K x).subtype (stabilizer K x).subtype_injective).toEquiv).symm
  have hQcard : Nat.card Q = Nat.card (stabilizer S x) :=
    (Nat.card_congr ((stabilizer S x).equivMapOfInjective
      (S : Subgroup K).subtype (S : Subgroup K).subtype_injective).toEquiv).symm
  refine ⟨T, ?_⟩
  apply (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · intro q hq
    exact ⟨⟨q,hQx hq⟩,hQT hq,rfl⟩
  · change Nat.card R ≤ Nat.card Q
    rwa [hRcard,hQcard]

end FiveTransitive.MaximalSylowPointStabilizer

end CFSG
