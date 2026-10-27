module

public import CFSG.Fischer.Uniq.HyperovalFacts
public import CFSG.Fischer.Uniq.LHTransport

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X}

@[expose] def starConjEquiv (hP : Pair X E) (g s : X) :
    LocalClass E s ≃ LocalClass E (g * s * g⁻¹) where
  toFun x := ⟨g * x * g⁻¹, (Pair.conj_mem_localClass_iff hP g).2 x.2⟩
  invFun y := ⟨g⁻¹ * y * g, by
    have h := (Pair.conj_mem_localClass_iff hP g⁻¹ (e := g * s * g⁻¹) (f := (y : X))).2 y.2
    simpa [mul_assoc] using h⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])

theorem starConjEquiv_val (hP : Pair X E) (g s : X) (x : LocalClass E s) :
    (starConjEquiv hP g s x : X) = g * x * g⁻¹ := rfl

theorem imgIn_starConjEquiv (hP : Pair X E) (g s : X) {U : Set X} (hU : U ⊆ LocalClass E s) :
    imgIn (starConjEquiv hP g s) U = (fun x => g * x * g⁻¹) '' U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hU hx⟩, hx, rfl⟩

theorem IsHyperovalIn.conj (hP : Pair X E) (g : X) {s : X} {U : Set X}
    (hU : IsHyperovalIn (LocalClass E s) U) :
    IsHyperovalIn (LocalClass E (g * s * g⁻¹)) ((fun x => g * x * g⁻¹) '' U) := by
  rw [← imgIn_starConjEquiv hP g s hU.subset]
  refine hU.transport (starConjEquiv hP g s) (fun x y => (conj_commute_iff g x y).symm)
    fun x y => ?_
  have hxy : (x : X) * y * x ∈ LocalClass E s := by
    have hx : (x : X) * x = 1 := Pair.mul_self hP x.2.1
    have h1 : Commute (x : X) s := x.2.2.2
    have h2 : Commute (y : X) s := y.2.2.2
    refine ⟨Pair.mul_mul_mem hP x.2.1 y.2.1, fun h => y.2.2.1 ?_,
      ((h1.mul_left h2).mul_left h1 : Commute ((x : X) * y * x) s)⟩
    calc (y : X) = x * (x * y * x) * x := by
          rw [show (x : X) * (x * y * x) * x = (x * x) * y * (x * x) by group, hx, one_mul, mul_one]
      _ = x * s * x := by rw [h]
      _ = s := by rw [h1.eq, mul_assoc, hx, mul_one]
  refine ⟨hxy, ?_⟩
  simp only [starConjEquiv_val]
  group

theorem image_conj_inter (g : X) (U V : Set X) :
    (fun x => g * x * g⁻¹) '' (U ∩ V) = (fun x => g * x * g⁻¹) '' U ∩ (fun x => g * x * g⁻¹) '' V :=
  Set.image_inter (conj_injective g)

theorem IsLocallyHyperoval.conj (hP : Pair X E) (g : X) {T : Set X}
    (hT : IsLocallyHyperoval E T) : IsLocallyHyperoval E ((fun x => g * x * g⁻¹) '' T) := by
  have hstar : ∀ s, (fun x => g * x * g⁻¹) '' T ∩ LocalClass E (g * s * g⁻¹) =
      (fun x => g * x * g⁻¹) '' (T ∩ LocalClass E s) := by
    intro s
    rw [image_conj_inter, Pair.image_conj_localClass hP]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Pair.conj_mem hP (hT.subset hx) g
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    refine ⟨s * t * s, hT.closed s hs t ht, by group⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [hstar]
    exact (hT.nonempty s hs).image _
  · rintro _ ⟨s, hs, rfl⟩
    rw [hstar]
    exact (hT.hyperoval s hs).conj hP g

variable {Z : Type} [Group Z] {D : Set Z} {s : Z}

theorem IsHyperovalIn.eq_of_inter
    (hHF : HyperovalFacts) (hP : Pair Z D)
    (L : LocalPoints polarModel D s) {U V : Set Z} (hU : IsHyperovalIn (LocalClass D s) U)
    (hV : IsHyperovalIn (LocalClass D s) V) {p : Z} (hpU : p ∈ U) (hpV : p ∈ V)
    (h : U ∩ LocalClass D p = V ∩ LocalClass D p) : U = V := by
  have hOU := (L.isHyperovalIn_iff hHF.linesByPerp hP hU.subset).1 hU
  have hOV := (L.isHyperovalIn_iff hHF.linesByPerp hP hV.subset).1 hV
  have hps : p ∈ LocalClass D s := hU.subset hpU
  apply L.eq_of_pts_eq hU.subset hV.subset
  refine hHF.eq_of_inter_perp _ _ hOU hOV (L.χ ⟨p, hps⟩) ((L.χ_mem_pts _).2 hpU)
    ((L.χ_mem_pts _).2 hpV) fun q hq => ?_
  obtain ⟨x, rfl⟩ := L.χ.surjective q
  rw [L.χ_mem_pts, L.χ_mem_pts]
  have hc : p * (x : Z) = x * p := (L.comm ⟨p, hps⟩ x).2 hq
  by_cases hxp : (x : Z) = p
  · rw [hxp]
    exact ⟨fun _ => hpV, fun _ => hpU⟩
  · have hxE : (x : Z) ∈ LocalClass D p := ⟨x.2.1, hxp, hc.symm⟩
    constructor
    · intro hxU
      have : (x : Z) ∈ U ∩ LocalClass D p := ⟨hxU, hxE⟩
      rw [h] at this
      exact this.1
    · intro hxV
      have : (x : Z) ∈ V ∩ LocalClass D p := ⟨hxV, hxE⟩
      rw [← h] at this
      exact this.1

theorem IsHyperovalIn.not_linear
    (hHF : HyperovalFacts) (hP : Pair Z D)
    (L : LocalPoints polarModel D s) {U : Set Z} (hU : IsHyperovalIn (LocalClass D s) U) {p q : Z}
    (hpU : p ∈ U) (hq : q ∈ LocalClass D s) (hpq : p * q ≠ q * p) :
    ¬ ∀ x ∈ LocalClass D s, x ∈ LocalClass D p → (x ∈ U ↔ x * q = q * x) := by
  intro hall
  have hO := (L.isHyperovalIn_iff hHF.linesByPerp hP hU.subset).1 hU
  have hps : p ∈ LocalClass D s := hU.subset hpU
  refine hHF.not_linear _ hO (L.χ ⟨p, hps⟩) ((L.χ_mem_pts _).2 hpU) (L.χ ⟨q, hq⟩)
    (fun h => hpq ((L.comm ⟨p, hps⟩ ⟨q, hq⟩).2 h)) fun w hwp hwne => ?_
  obtain ⟨x, rfl⟩ := L.χ.surjective w
  rw [L.χ_mem_pts]
  have hxp : (x : Z) * p = p * x := (L.comm x ⟨p, hps⟩).2 hwp
  have hxne : (x : Z) ≠ p := fun h => hwne (congrArg L.χ (Subtype.ext h))
  rw [hall x x.2 ⟨x.2.1, hxne, hxp⟩]
  exact L.comm x ⟨q, hq⟩

end CFSG.Fischer
