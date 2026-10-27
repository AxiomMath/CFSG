module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314D
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314H

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Quasithin CFSG.Quasithin.H13.CZL32

variable {V : Type} [CommGroup V]

theorem conjSub_stabIn (y : MulAut V) (H : Subgroup (MulAut V)) (C : Set V) :
    conjSub y (stabIn H C) = stabIn (conjSub y H) (⇑y⁻¹ ⁻¹' C) := by
  ext x
  rw [mem_conjSub, mem_stabIn, mem_stabIn, mem_conjSub]
  refine and_congr_right fun _ => ⟨fun h w => ?_, fun h v => ?_⟩
  · have := h (y⁻¹ w)
    simp only [Set.mem_preimage]
    rwa [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self] at this
  · have := h (y v)
    simp only [Set.mem_preimage, MulAut.inv_apply_self] at this
    rwa [MulAut.mul_apply, MulAut.mul_apply]

theorem preimage_fixMod (y : MulAut V) {U Z : Subgroup V} (hU : ∀ v, v ∈ U ↔ y v ∈ U)
    (hZ : ∀ v, v ∈ Z ↔ y v ∈ Z) (S : Subgroup (MulAut V)) :
    ⇑y⁻¹ ⁻¹' fixMod U Z S = fixMod U Z (conjSub y S) := by
  ext v
  simp only [Set.mem_preimage, fixMod, Set.mem_ofPred_eq]
  have hU' : y⁻¹ v ∈ U ↔ v ∈ U := by rw [hU, MulAut.apply_inv_self]
  rw [hU']
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have h1 := h (y⁻¹ * x * y) (mem_conjSub.mp hx)
    rw [hZ, map_mul, map_inv] at h1
    simpa [MulAut.mul_apply] using h1
  · have h1 := h (y * x * y⁻¹) (mul_mem_conjSub hx)
    rw [hZ, map_mul, map_inv]
    simpa [MulAut.mul_apply] using h1

theorem conjSub_stabIn_fixMod {y : MulAut V} {H S : Subgroup (MulAut V)} {U Z : Subgroup V}
    (hH : conjSub y H = H) (hS : conjSub y S = S) (hU : ∀ v, v ∈ U ↔ y v ∈ U)
    (hZ : ∀ v, v ∈ Z ↔ y v ∈ Z) :
    conjSub y (stabIn H (fixMod U Z S)) = stabIn H (fixMod U Z S) := by
  rw [conjSub_stabIn, hH, preimage_fixMod y hU hZ, hS]

theorem conjSub_cenSub (y : MulAut V) (S : Subgroup (MulAut V)) :
    conjSub y (cenSub S) = cenSub (conjSub y S) := by
  rw [cenSub, cenSub, conjSub_inf, conjSub_centralizer]

namespace Coord

variable {H : Subgroup (MulAut V)} {U Z : Subgroup V} {k : ℕ} (c : Coord H U Z k)

theorem img_injective : Function.Injective c.img := by
  intro γ δ h
  exact c.π.injective (Subtype.ext h)

theorem img_mem_imgSub_iff {Q : Subgroup L3.Γ} {γ : L3.Γ} : c.img γ ∈ c.imgSub Q ↔ γ ∈ Q :=
  ⟨c.mem_of_img_mem, fun h => (c.mem_imgSub).mpr ⟨γ, h, rfl⟩⟩

theorem imgSub_le (Q : Subgroup L3.Γ) : c.imgSub Q ≤ H := by
  rintro _ ⟨γ, -, rfl⟩
  exact c.img_mem γ

theorem imgSub_top : c.imgSub ⊤ = H := by
  refine le_antisymm (c.imgSub_le ⊤) fun x hx => ?_
  obtain ⟨γ, rfl⟩ := c.exists_img hx
  exact (c.mem_imgSub).mpr ⟨γ, Subgroup.mem_top γ, rfl⟩

theorem imgSub_injective' : Function.Injective (H.subtype.comp c.π.toMonoidHom) :=
  H.subtype_injective.comp c.π.injective

theorem imgSub_sup (Q₁ Q₂ : Subgroup L3.Γ) : c.imgSub (Q₁ ⊔ Q₂) = c.imgSub Q₁ ⊔ c.imgSub Q₂ :=
  Subgroup.map_sup _ _ _

theorem card_imgSub (Q : Subgroup L3.Γ) : Nat.card (c.imgSub Q) = Nat.card Q :=
  Subgroup.card_map_of_injective c.imgSub_injective'

theorem imgSub_le_imgSub_iff {Q₁ Q₂ : Subgroup L3.Γ} : c.imgSub Q₁ ≤ c.imgSub Q₂ ↔ Q₁ ≤ Q₂ :=
  Subgroup.map_le_map_iff_of_injective c.imgSub_injective'

theorem imgSub_inj {Q₁ Q₂ : Subgroup L3.Γ} : c.imgSub Q₁ = c.imgSub Q₂ ↔ Q₁ = Q₂ :=
  ⟨fun h => le_antisymm (c.imgSub_le_imgSub_iff.mp h.le) (c.imgSub_le_imgSub_iff.mp h.ge),
    fun h => h ▸ rfl⟩

theorem exists_imgSub {D : Subgroup (MulAut V)} (hD : D ≤ H) : ∃ Q, D = c.imgSub Q := by
  refine ⟨D.comap (H.subtype.comp c.π.toMonoidHom), le_antisymm (fun x hx => ?_) ?_⟩
  · obtain ⟨γ, rfl⟩ := c.exists_img (hD hx)
    exact (c.mem_imgSub).mpr ⟨γ, hx, rfl⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    exact hγ

theorem imgSub_conjSub (γ : L3.Γ) (Q : Subgroup L3.Γ) :
    c.imgSub (conjSub γ Q) = conjSub (c.img γ) (c.imgSub Q) := by
  ext x
  rw [mem_conjSub]
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    refine (c.mem_imgSub).mpr ⟨γ⁻¹ * δ * γ, mem_conjSub.mp hδ, ?_⟩
    show c.img (γ⁻¹ * δ * γ) = (c.img γ)⁻¹ * c.img δ * c.img γ
    rw [c.img_mul, c.img_mul]
    simp [img, map_inv]
  · intro hx
    have hxH : x ∈ H := by
      have h1 := c.imgSub_le Q hx
      have h2 : x = c.img γ * ((c.img γ)⁻¹ * x * c.img γ) * (c.img γ)⁻¹ := by group
      rw [h2]
      exact H.mul_mem (H.mul_mem (c.img_mem γ) h1) (H.inv_mem (c.img_mem γ))
    obtain ⟨δ, rfl⟩ := c.exists_img hxH
    refine (c.mem_imgSub).mpr ⟨δ, mem_conjSub.mpr ?_, rfl⟩
    have e : (c.img γ)⁻¹ * c.img δ * c.img γ = c.img (γ⁻¹ * δ * γ) := by
      rw [c.img_mul, c.img_mul]
      simp [img, map_inv]
    rw [e] at hx
    exact c.mem_of_img_mem hx

@[expose] def diagAct (k : ℕ) (γ : L3.Γ) :
    Multiplicative (Fin k → L3.Vec) →* Multiplicative (Fin k → L3.Vec) where
  toFun x := Multiplicative.ofAdd fun i => L3.act γ (Multiplicative.toAdd x i)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    exact L3.act_zero γ
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    exact L3.act_add γ _ _

theorem diagAct_inv (γ : L3.Γ) (x : Multiplicative (Fin k → L3.Vec)) :
    diagAct k γ⁻¹ (diagAct k γ x) = x := by
  apply Multiplicative.toAdd.injective
  funext i
  exact L3.act_inv_act γ _

theorem diagAct_inv' (γ : L3.Γ) (x : Multiplicative (Fin k → L3.Vec)) :
    diagAct k γ (diagAct k γ⁻¹ x) = x := by
  apply Multiplicative.toAdd.injective
  funext i
  exact L3.act_act_inv γ _

@[expose] noncomputable def conj (g : L3.Γ) : Coord H U Z k where
  π := (MulAut.conj g).trans c.π
  β := (diagAct k g⁻¹).comp c.β
  β_surj := by
    intro x
    obtain ⟨u, hu⟩ := c.β_surj (diagAct k g x)
    exact ⟨u, by simp only [MonoidHom.comp_apply, hu, diagAct_inv]⟩
  ker_β := by
    intro u
    rw [← c.ker_β u]
    constructor
    · intro h
      have h1 := congrArg (diagAct k g) h
      simpa only [MonoidHom.comp_apply, diagAct_inv', map_one] using h1
    · intro h
      simp only [MonoidHom.comp_apply, h, map_one]
  Z_le := c.Z_le
  inv_U := c.inv_U
  equi := by
    intro γ u hu
    have e : (((MulAut.conj g).trans c.π γ : ↥H) : MulAut V) =
        ((c.π (g * γ * g⁻¹) : ↥H) : MulAut V) := by
      simp only [MulEquiv.trans_apply, MulAut.conj_apply]
    have hu' : ((c.π (g * γ * g⁻¹) : ↥H) : MulAut V) (u : V) ∈ U := e ▸ hu
    have h1 := c.equi (g * γ * g⁻¹) u hu'
    have h2 : (⟨_, hu⟩ : ↥U) = ⟨_, hu'⟩ := Subtype.ext (by simp only [e])
    simp only [MonoidHom.comp_apply]
    rw [h2, h1]
    apply Multiplicative.toAdd.injective
    funext i
    show L3.act g⁻¹ (L3.act (g * γ * g⁻¹) _) = L3.act γ (L3.act g⁻¹ _)
    rw [← L3.act_mul, ← L3.act_mul, show g⁻¹ * (g * γ * g⁻¹) = γ * g⁻¹ by group]
    rfl

theorem conj_π (g : L3.Γ) : (c.conj g).π = (MulAut.conj g).trans c.π := rfl

theorem conj_img (g γ : L3.Γ) : (c.conj g).img γ = c.img (g * γ * g⁻¹) := by
  simp only [img, conj_π, MulEquiv.trans_apply, MulAut.conj_apply]

theorem conj_imgSub (g : L3.Γ) (Q : Subgroup L3.Γ) :
    (c.conj g).imgSub Q = c.imgSub (conjSub g Q) := by
  ext x
  rw [mem_imgSub, mem_imgSub]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨g * γ * g⁻¹, mul_mem_conjSub hγ, (conj_img c g γ).symm⟩
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨g⁻¹ * δ * g, mem_conjSub.mp hδ, ?_⟩
    rw [conj_img, show g * (g⁻¹ * δ * g) * g⁻¹ = δ by group]

include c in
theorem exists_imgSub_bSub {S : Subgroup (MulAut V)} (hS : S ≤ H) (h8 : Nat.card S = 8) :
    ∃ c' : Coord H U Z k, c'.imgSub bSub = S := by
  obtain ⟨Q, rfl⟩ := c.exists_imgSub hS
  rw [card_imgSub] at h8
  obtain ⟨g, rfl⟩ := exists_conjSub_eq_bSub h8
  exact ⟨c.conj g, conj_imgSub c g bSub⟩

end Coord

end CFSG.Quasithin.H13.Ins314
