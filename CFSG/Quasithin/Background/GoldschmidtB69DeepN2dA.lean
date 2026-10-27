module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.B6Maschke

public section

namespace CFSG.Quasithin

open B6

namespace B69

variable {V : Type} [CommGroup V]

theorem exists_aut_sec {L : Subgroup (MulAut V)} {W U : Subgroup V} (hLW : L ≤ stabSub W)
    (hLU : L ≤ stabSub U) {t : MulAut V} (ht : ∀ x ∈ L, t * x * t⁻¹ ∈ L)
    (hW : ∀ w, w ∈ W ↔ t w ∈ W) (hU : ∀ w, w ∈ U ↔ t w ∈ U) :
    ∃ τ : MulAut (Sec W U), ∀ (l : ↥L) (s : Sec W U),
      τ (B5.secHom L hLW hLU l s) = B5.secHom L hLW hLU ⟨t * l * t⁻¹, ht l l.2⟩ (τ s) := by
  let eT : ↥W ≃* ↥W :=
    { toFun := fun w => ⟨t (w : V), (hW w).1 w.2⟩
      invFun := fun w => ⟨t⁻¹ (w : V), (hW _).2 (by simp)⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hmapC : (U.subgroupOf W).map eT.toMonoidHom = U.subgroupOf W := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hU _).1 hx
    · intro hy
      refine ⟨eT.symm y, ?_, eT.apply_symm_apply y⟩
      have h1 : ((y : ↥W) : V) ∈ U := hy
      show t⁻¹ (y : V) ∈ U
      rw [hU]
      simpa using h1
  let τ : Sec W U ≃* Sec W U := QuotientGroup.congr _ _ eT hmapC
  refine ⟨τ, fun l s => ?_⟩
  induction s using QuotientGroup.induction_on with
  | H w =>
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    show t ((l : MulAut V) (w : V)) = (t * (l : MulAut V) * t⁻¹) (t (w : V))
    simp [MulAut.mul_apply]

theorem mem_autSec_conj_iff {L : Subgroup (MulAut V)} {W U : Subgroup V} (hLW : L ≤ stabSub W)
    (hLU : L ≤ stabSub U) {t : MulAut V} (ht : ∀ x ∈ L, t * x * t⁻¹ ∈ L)
    (ht' : ∀ x ∈ L, t⁻¹ * x * t ∈ L) {τ : MulAut (Sec W U)}
    (hτ : ∀ (l : ↥L) (s : Sec W U),
      τ (B5.secHom L hLW hLU l s) = B5.secHom L hLW hLU ⟨t * l * t⁻¹, ht l l.2⟩ (τ s))
    (m : MulAut (Sec W U)) :
    m ∈ autSec L W U ↔ τ * m * τ⁻¹ ∈ autSec L W U := by
  have hconj : ∀ l : ↥L, τ * B5.secHom L hLW hLU l * τ⁻¹ =
      B5.secHom L hLW hLU ⟨t * l * t⁻¹, ht l l.2⟩ := by
    intro l
    refine MulEquiv.ext fun s => ?_
    have := hτ l (τ⁻¹ s)
    simpa [MulAut.mul_apply] using this
  rw [← B5.range_secHom L hLW hLU]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨⟨t * l * t⁻¹, ht l l.2⟩, (hconj l).symm⟩
  · rintro ⟨l₂, hl₂⟩
    refine ⟨⟨t⁻¹ * l₂ * t, ht' l₂ l₂.2⟩, ?_⟩
    have h1 := hconj ⟨t⁻¹ * l₂ * t, ht' l₂ l₂.2⟩
    have h2 : (⟨t * (t⁻¹ * (l₂ : MulAut V) * t) * t⁻¹, ht _ (ht' l₂ l₂.2)⟩ : ↥L) = l₂ := by
      apply Subtype.ext
      show t * (t⁻¹ * (l₂ : MulAut V) * t) * t⁻¹ = l₂
      group
    simp only [h2] at h1
    rw [hl₂] at h1
    have h3 : τ⁻¹ * (τ * B5.secHom L hLW hLU ⟨t⁻¹ * l₂ * t, ht' l₂ l₂.2⟩ * τ⁻¹) * τ =
        τ⁻¹ * (τ * m * τ⁻¹) * τ := by rw [h1]
    simpa [mul_assoc] using h3

end B69

end CFSG.Quasithin
