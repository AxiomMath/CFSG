module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314C

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Quasithin CFSG.Quasithin.H13.CZL32

variable {V : Type} [CommGroup V]

structure Coord (H : Subgroup (MulAut V)) (U Z : Subgroup V) (k : ℕ) where
  π : L3.Γ ≃* ↥H
  β : ↥U →* Multiplicative (Fin k → L3.Vec)
  β_surj : Function.Surjective β
  ker_β : ∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z
  Z_le : Z ≤ U
  inv_U : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U
  equi : ∀ (γ : L3.Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
    β ⟨_, hu⟩ = Multiplicative.ofAdd (fun i => L3.act γ (Multiplicative.toAdd (β u) i))

@[expose] def fixMod (U Z : Subgroup V) (S : Subgroup (MulAut V)) : Set V :=
  {v | v ∈ U ∧ ∀ x ∈ S, x v * v⁻¹ ∈ Z}

@[expose] def stabIn (H : Subgroup (MulAut V)) (C : Set V) : Subgroup (MulAut V) where
  carrier := {x | x ∈ H ∧ ∀ v, v ∈ C ↔ x v ∈ C}
  one_mem' := ⟨H.one_mem, fun v => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, fun v => by
    rw [hb.2 v, ha.2 (b v)]
    rfl⟩
  inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, fun v => by
    rw [ha.2 (a⁻¹ v)]
    simp⟩

theorem mem_stabIn {H : Subgroup (MulAut V)} {C : Set V} {x : MulAut V} :
    x ∈ stabIn H C ↔ x ∈ H ∧ ∀ v, v ∈ C ↔ x v ∈ C := Iff.rfl

@[expose] def cenSub (S : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  S ⊓ Subgroup.centralizer (S : Set (MulAut V))

namespace Coord

variable {H : Subgroup (MulAut V)} {U Z : Subgroup V} {k : ℕ} (c : Coord H U Z k)

@[expose] def img (γ : L3.Γ) : MulAut V := ((c.π γ : ↥H) : MulAut V)

theorem img_mem (γ : L3.Γ) : c.img γ ∈ H := (c.π γ).2

theorem img_mul (γ δ : L3.Γ) : c.img (γ * δ) = c.img γ * c.img δ := by
  simp [img, map_mul]

theorem img_mem_U (γ : L3.Γ) {v : V} (hv : v ∈ U) : c.img γ v ∈ U := c.inv_U _ v hv

theorem β_img (γ : L3.Γ) (u : ↥U) :
    Multiplicative.toAdd (c.β ⟨c.img γ u, c.img_mem_U γ u.2⟩) =
      fun i => L3.act γ (Multiplicative.toAdd (c.β u) i) :=
  congrArg Multiplicative.toAdd (c.equi γ u (c.img_mem_U γ u.2))

theorem mul_inv_mem_iff (u u' : ↥U) : (u' : V) * (u : V)⁻¹ ∈ Z ↔ c.β u' = c.β u := by
  rw [← mul_inv_eq_one, ← map_inv c.β u, ← map_mul c.β, c.ker_β]
  rfl

theorem img_inv_mem_U (γ : L3.Γ) {v : V} (hv : c.img γ v ∈ U) : v ∈ U := by
  have h := c.img_mem_U γ⁻¹ hv
  have e : c.img γ⁻¹ (c.img γ v) = v := by
    rw [← MulAut.mul_apply, ← c.img_mul, inv_mul_cancel]
    simp [img]
  rwa [e] at h

@[expose] def imgSub (Q : Subgroup L3.Γ) : Subgroup (MulAut V) :=
  Q.map (H.subtype.comp c.π.toMonoidHom)

theorem mem_imgSub {Q : Subgroup L3.Γ} {x : MulAut V} :
    x ∈ c.imgSub Q ↔ ∃ γ ∈ Q, c.img γ = x := by
  simp [imgSub, img]

theorem exists_img {x : MulAut V} (hx : x ∈ H) : ∃ γ, c.img γ = x := by
  obtain ⟨γ, hγ⟩ := c.π.surjective ⟨x, hx⟩
  exact ⟨γ, by simp [img, hγ]⟩

theorem mem_fixMod_iff (Q : Subgroup L3.Γ) {v : V} (hv : v ∈ U) :
    v ∈ fixMod U Z (c.imgSub Q) ↔
      ∀ i, ∀ γ ∈ Q, L3.act γ (Multiplicative.toAdd (c.β ⟨v, hv⟩) i) =
        Multiplicative.toAdd (c.β ⟨v, hv⟩) i := by
  constructor
  · rintro ⟨-, h⟩ i γ hγ
    have h1 := h (c.img γ) ((c.mem_imgSub).mpr ⟨γ, hγ, rfl⟩)
    have h2 := (c.mul_inv_mem_iff ⟨v, hv⟩ ⟨c.img γ v, c.img_mem_U γ hv⟩).mp h1
    have h3 := congrArg (fun w : Multiplicative (Fin k → L3.Vec) => Multiplicative.toAdd w i) h2
    have h4 := congrFun (c.β_img γ ⟨v, hv⟩) i
    exact h4.symm.trans h3
  · intro h
    refine ⟨hv, fun x hx => ?_⟩
    obtain ⟨γ, hγ, rfl⟩ := (c.mem_imgSub).mp hx
    apply (c.mul_inv_mem_iff ⟨v, hv⟩ ⟨c.img γ v, c.img_mem_U γ hv⟩).mpr
    apply Multiplicative.toAdd.injective
    rw [c.β_img γ ⟨v, hv⟩]
    funext i
    exact h i γ hγ

theorem mem_of_img_mem {Q : Subgroup L3.Γ} {γ : L3.Γ} (h : c.img γ ∈ c.imgSub Q) : γ ∈ Q := by
  obtain ⟨δ, hδ, e⟩ := (c.mem_imgSub).mp h
  have : δ = γ := c.π.injective (Subtype.ext e)
  exact this ▸ hδ

theorem stab_of_coords {X : Set L3.Vec} {C : Set V}
    (hC : ∀ v (hv : v ∈ U), v ∈ C ↔ ∀ i, Multiplicative.toAdd (c.β ⟨v, hv⟩) i ∈ X)
    (hCU : ∀ v ∈ C, v ∈ U) {γ : L3.Γ} (hγ : ∀ w, w ∈ X ↔ L3.act γ w ∈ X) :
    ∀ v, v ∈ C ↔ c.img γ v ∈ C := by
  intro v
  by_cases hv : v ∈ U
  · rw [hC v hv, hC _ (c.img_mem_U γ hv)]
    have e := c.β_img γ ⟨v, hv⟩
    constructor
    · intro h i
      rw [e]
      exact (hγ _).mp (h i)
    · intro h i
      have h1 := h i
      rw [e] at h1
      exact (hγ _).mpr h1
  · constructor
    · intro h
      exact absurd (hCU v h) hv
    · intro h
      exact absurd (c.img_inv_mem_U γ (hCU _ h)) hv

theorem coords_of_stab (hk : 0 < k) {X : Set L3.Vec} {C : Set V}
    (hC : ∀ v (hv : v ∈ U), v ∈ C ↔ ∀ i, Multiplicative.toAdd (c.β ⟨v, hv⟩) i ∈ X)
    {γ : L3.Γ} (hγ : ∀ v, v ∈ C ↔ c.img γ v ∈ C) : ∀ w, w ∈ X ↔ L3.act γ w ∈ X := by
  intro w
  obtain ⟨u, hu⟩ := c.β_surj (Multiplicative.ofAdd fun _ => w)
  have h1 := hγ u
  rw [hC u u.2, hC _ (c.img_mem_U γ u.2)] at h1
  have e := c.β_img γ u
  rw [hu] at e
  have i0 : Fin k := ⟨0, hk⟩
  constructor
  · intro hw
    have h2 := h1.mp (fun i => by rw [hu]; exact hw) i0
    rw [show (⟨c.img γ u, c.img_mem_U γ u.2⟩ : ↥U) = ⟨_, c.img_mem_U γ u.2⟩ from rfl, e] at h2
    exact h2
  · intro hw
    have h2 := h1.mpr (fun i => by
      rw [show (⟨c.img γ u, c.img_mem_U γ u.2⟩ : ↥U) = ⟨_, c.img_mem_U γ u.2⟩ from rfl, e]
      exact hw) i0
    rw [hu] at h2
    exact h2

theorem mem_fixMod_bSub_iff {v : V} (hv : v ∈ U) :
    v ∈ fixMod U Z (c.imgSub bSub) ↔
      ∀ i, Multiplicative.toAdd (c.β ⟨v, hv⟩) i ∈ {w : L3.Vec | w = 0 ∨ w = e1} := by
  rw [c.mem_fixMod_iff bSub hv]
  exact forall_congr' fun i => (fix_bSub_iff _)

theorem stabIn_fixMod_bSub (hk : 0 < k) :
    stabIn H (fixMod U Z (c.imgSub bSub)) = c.imgSub (L3.ptSub e1) := by
  have hC : ∀ v (hv : v ∈ U), v ∈ fixMod U Z (c.imgSub bSub) ↔
      ∀ i, Multiplicative.toAdd (c.β ⟨v, hv⟩) i ∈ {w : L3.Vec | w = 0 ∨ w = e1} :=
    fun v hv => c.mem_fixMod_bSub_iff hv
  have hCU : ∀ v ∈ fixMod U Z (c.imgSub bSub), v ∈ U := fun v hv => hv.1
  ext x
  rw [mem_stabIn, c.mem_imgSub]
  constructor
  · rintro ⟨hxH, hx⟩
    obtain ⟨γ, rfl⟩ := c.exists_img hxH
    have h := c.coords_of_stab hk hC hx e1
    have h1 := h.mp (Or.inr rfl)
    refine ⟨γ, ?_, rfl⟩
    rcases h1 with h0 | h1
    · exfalso
      have := L3.act_inv_act γ e1
      rw [h0, L3.act_zero] at this
      exact absurd this.symm (by decide)
    · exact h1
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨c.img_mem γ, c.stab_of_coords hC hCU fun w => ?_⟩
    have hγe : L3.act γ e1 = e1 := hγ
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl (L3.act_zero γ)
      · exact Or.inr hγe
    · rintro (h | h)
      · left
        have := L3.act_inv_act γ w
        rw [h, L3.act_zero] at this
        exact this.symm
      · right
        have := L3.act_inv_act γ w
        rw [h, ← hγe, L3.act_inv_act] at this
        exact this.symm

theorem img_zB_mem_cenSub : c.img zB ∈ cenSub (c.imgSub bSub) := by
  refine Subgroup.mem_inf.mpr ⟨(c.mem_imgSub).mpr ⟨zB, zB_mem, rfl⟩,
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨b, hb, rfl⟩ := (c.mem_imgSub).mp hy
  rw [← c.img_mul, ← c.img_mul, ((mem_center_bSub_iff zB_mem).mpr (Or.inr rfl) b hb).symm]

theorem eq_of_mem_cenSub {x : MulAut V} (hx : x ∈ cenSub (c.imgSub bSub)) :
    x = c.img 1 ∨ x = c.img zB := by
  obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨γ, hγ, rfl⟩ := (c.mem_imgSub).mp hxS
  have h : ∀ h ∈ bSub, γ * h = h * γ := by
    intro h hh
    have h1 := Subgroup.mem_centralizer_iff.mp hxc (c.img h) ((c.mem_imgSub).mpr ⟨h, hh, rfl⟩)
    rw [← c.img_mul, ← c.img_mul] at h1
    exact (c.π.injective (Subtype.ext h1)).symm
  rcases (mem_center_bSub_iff hγ).mp h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem mem_fixMod_cen_iff {v : V} (hv : v ∈ U) :
    v ∈ fixMod U Z (cenSub (c.imgSub bSub)) ↔
      ∀ i, Multiplicative.toAdd (c.β ⟨v, hv⟩) i ∈ {w : L3.Vec | w ∈ P12} := by
  constructor
  · rintro ⟨-, h⟩ i
    have h1 := (c.mul_inv_mem_iff ⟨v, hv⟩ ⟨c.img zB v, c.img_mem_U zB hv⟩).mp
      (h _ c.img_zB_mem_cenSub)
    have h3 := congrArg (fun w : Multiplicative (Fin k → L3.Vec) => Multiplicative.toAdd w i) h1
    have h4 := congrFun (c.β_img zB ⟨v, hv⟩) i
    exact (fix_zB_iff _).mp (h4.symm.trans h3)
  · intro h
    refine ⟨hv, fun x hx => ?_⟩
    have hfix : ∀ γ, (γ = 1 ∨ γ = zB) → c.img γ v * v⁻¹ ∈ Z := by
      intro γ hγ
      apply (c.mul_inv_mem_iff ⟨v, hv⟩ ⟨c.img γ v, c.img_mem_U γ hv⟩).mpr
      apply Multiplicative.toAdd.injective
      rw [c.β_img γ ⟨v, hv⟩]
      funext i
      rcases hγ with rfl | rfl
      · exact L3.act_one _
      · exact (fix_zB_iff _).mpr (h i)
    rcases c.eq_of_mem_cenSub hx with rfl | rfl
    · exact hfix 1 (Or.inl rfl)
    · exact hfix zB (Or.inr rfl)

theorem stabIn_fixMod_cen (hk : 0 < k) :
    stabIn H (fixMod U Z (cenSub (c.imgSub bSub))) = c.imgSub (L3.stabSub P12) := by
  have hC : ∀ v (hv : v ∈ U), v ∈ fixMod U Z (cenSub (c.imgSub bSub)) ↔
      ∀ i, Multiplicative.toAdd (c.β ⟨v, hv⟩) i ∈ {w : L3.Vec | w ∈ P12} :=
    fun v hv => c.mem_fixMod_cen_iff hv
  have hCU : ∀ v ∈ fixMod U Z (cenSub (c.imgSub bSub)), v ∈ U := fun v hv => hv.1
  ext x
  rw [mem_stabIn, c.mem_imgSub]
  constructor
  · rintro ⟨hxH, hx⟩
    obtain ⟨γ, rfl⟩ := c.exists_img hxH
    exact ⟨γ, fun w => c.coords_of_stab hk hC hx w, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨c.img_mem γ, c.stab_of_coords hC hCU fun w => hγ w⟩

end Coord

end CFSG.Quasithin.H13.Ins314
