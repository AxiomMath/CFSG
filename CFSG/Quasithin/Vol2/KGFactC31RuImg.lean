
module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefDefs

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31

abbrev G₀ : Type := ↥ruP

variable {A : Type} [Group A]

@[expose] def img (e : G₀ ≃* A) (X : Subgroup (Equiv.Perm (Fin 4060))) : Subgroup A :=
  (X.subgroupOf ruP).map e.toMonoidHom

variable (e : G₀ ≃* A)

theorem mem_img {X : Subgroup (Equiv.Perm (Fin 4060))} {a : A} :
    a ∈ img e X ↔ ((e.symm a : G₀) : Equiv.Perm (Fin 4060)) ∈ X := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    simpa [Subgroup.mem_subgroupOf] using hg
  · intro h
    exact ⟨e.symm a, h, by simp⟩

theorem apply_mem_img {X : Subgroup (Equiv.Perm (Fin 4060))} {g : G₀} :
    e g ∈ img e X ↔ (g : Equiv.Perm (Fin 4060)) ∈ X := by
  rw [mem_img, MulEquiv.symm_apply_apply]

theorem img_mono {X Y : Subgroup (Equiv.Perm (Fin 4060))} (h : X ≤ Y) : img e X ≤ img e Y :=
  Subgroup.map_mono fun _ hx => h hx

theorem img_le_img_iff {X Y : Subgroup (Equiv.Perm (Fin 4060))} (hX : X ≤ ruP) :
    img e X ≤ img e Y ↔ X ≤ Y := by
  refine ⟨fun h x hx => ?_, img_mono e⟩
  have := h ((apply_mem_img e (g := ⟨x, hX hx⟩)).mpr hx)
  exact (apply_mem_img e).mp this

theorem card_img {X : Subgroup (Equiv.Perm (Fin 4060))} (hX : X ≤ ruP) :
    Nat.card (img e X) = Nat.card X := by
  rw [img, Subgroup.card_map_of_injective e.injective, card_subgroupOf_of_le hX]

theorem img_inf (X Y : Subgroup (Equiv.Perm (Fin 4060))) :
    img e (X ⊓ Y) = img e X ⊓ img e Y := by
  ext a
  simp only [Subgroup.mem_inf, mem_img]

theorem img_top_le : img e ruP = ⊤ := by
  ext a
  simp only [mem_img, Subgroup.mem_top, iff_true]
  exact (e.symm a).2

theorem eq_img (Y : Subgroup A) :
    Y = img e ((Y.comap e.toMonoidHom).map ruP.subtype) := by
  ext a
  rw [mem_img]
  constructor
  · intro h
    exact ⟨e.symm a, by simpa using h, rfl⟩
  · rintro ⟨g, hg, hge⟩
    have : g = e.symm a := Subtype.ext hge
    rw [this] at hg
    simpa using hg

theorem map_img_le (Y : Subgroup A) : (Y.comap e.toMonoidHom).map ruP.subtype ≤ ruP := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem centralizer_img {X : Subgroup (Equiv.Perm (Fin 4060))} (hX : X ≤ ruP) :
    Subgroup.centralizer (img e X : Set A) =
      img e (ruP ⊓ Subgroup.centralizer (X : Set (Equiv.Perm (Fin 4060)))) := by
  ext a
  rw [mem_img, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨(e.symm a).2, fun x hx => ?_⟩
    have h1 := h (e ⟨x, hX hx⟩) ((apply_mem_img e).mpr hx)
    have h2 := congrArg (fun b => ((e.symm b : G₀) : Equiv.Perm (Fin 4060))) h1
    simpa using h2
  · rintro ⟨-, h⟩ b hb
    rw [SetLike.mem_coe, mem_img] at hb
    have h1 := h _ hb
    apply e.symm.injective
    apply Subtype.ext
    simpa using h1

theorem normalizer_img {X : Subgroup (Equiv.Perm (Fin 4060))} (hX : X ≤ ruP) :
    Subgroup.normalizer (img e X : Set A) =
      img e (ruP ⊓ Subgroup.normalizer (X : Set (Equiv.Perm (Fin 4060)))) := by
  ext a
  rw [mem_img, Subgroup.mem_inf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  set g := e.symm a with hg
  have ha : a = e g := by rw [hg, MulEquiv.apply_symm_apply]
  constructor
  · intro h
    refine ⟨g.2, fun x => ?_⟩
    by_cases hx : x ∈ ruP
    · have h1 := h (e ⟨x, hx⟩)
      rw [apply_mem_img, ha, ← map_inv, ← map_mul, ← map_mul, apply_mem_img] at h1
      simpa using h1
    · constructor
      · intro h'
        exact absurd (hX h') hx
      · intro h'
        exfalso
        apply hx
        have h2 := hX h'
        have : x = (g : Equiv.Perm (Fin 4060))⁻¹ * ((g : Equiv.Perm (Fin 4060)) * x *
            (g : Equiv.Perm (Fin 4060))⁻¹) * g := by group
        rw [this]
        exact ruP.mul_mem (ruP.mul_mem (ruP.inv_mem g.2) h2) g.2
  · rintro ⟨-, h⟩ b
    have hb : b = e (e.symm b) := by simp
    rw [hb, apply_mem_img, ha, ← map_inv, ← map_mul, ← map_mul, apply_mem_img]
    simpa using h ((e.symm b : G₀) : Equiv.Perm (Fin 4060))

@[expose] def conjE (g : G₀) : G₀ ≃* A := (MulAut.conj g).trans e

theorem conjE_apply (g x : G₀) : conjE e g x = e (g * x * g⁻¹) := rfl

theorem img_conjE (g : G₀) (X : Subgroup (Equiv.Perm (Fin 4060))) :
    img (conjE e g) X = img e (X.map (MulAut.conj (g : Equiv.Perm (Fin 4060))).toMonoidHom) := by
  ext a
  rw [mem_img, mem_img]
  have h1 : (conjE e g).symm a = g⁻¹ * e.symm a * g := by
    apply (conjE e g).injective
    rw [MulEquiv.apply_symm_apply, conjE_apply]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
    simp
  rw [h1]
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · rintro ⟨x, hx, hxe⟩
    have : ((g⁻¹ * e.symm a * g : G₀) : Equiv.Perm (Fin 4060)) = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxe
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hxe]
      group
    rw [this]
    exact hx

theorem mem_centralizer_subgroupOf_iff {X : Subgroup (Equiv.Perm (Fin 4060))} (hX : X ≤ ruP)
    (x : G₀) : x ∈ Subgroup.centralizer (X.subgroupOf ruP : Set G₀) ↔
      (x : Equiv.Perm (Fin 4060)) ∈ Subgroup.centralizer (X : Set (Equiv.Perm (Fin 4060))) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h u hu
    have := h ⟨u, hX hu⟩ (by rwa [SetLike.mem_coe, Subgroup.mem_subgroupOf])
    exact congrArg Subtype.val this
  · intro h u hu
    exact Subtype.ext (h u hu)

@[expose] def liftV {k : ℕ} (v : Fin k → Equiv.Perm (Fin 4060)) (hv : ∀ i, v i ∈ ruP) :
    Fin k → G₀ :=
  fun i => ⟨v i, hv i⟩

theorem liftV_basis {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} (hv : ∀ i, v i ∈ ruP)
    (hb : EBasis v) : EBasis (liftV v hv) where
  sq i := Subtype.ext (by simpa [liftV] using hb.sq i)
  comm i j := by
    have := hb.comm i j
    exact Subtype.ext this.eq
  ne_one c hc := hb.ne_one c (by
    have h := congrArg Subtype.val hc
    rwa [show ((eElt (liftV v hv) c : G₀) : Equiv.Perm (Fin 4060)) = eElt v c from
      map_eElt ruP.subtype c] at h)

theorem eSub_liftV {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} (hv : ∀ i, v i ∈ ruP)
    (hb : EBasis v) : eSub (liftV_basis hv hb) = (refSub v).subgroupOf ruP := by
  ext x
  rw [mem_eSub_iff, Subgroup.mem_subgroupOf, refSub_eq hb, mem_eSub_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, (map_eElt (v := liftV v hv) ruP.subtype c).symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, Subtype.ext ?_⟩
    rw [← hc]
    exact map_eElt ruP.subtype c

theorem eSub_liftV_map {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} (hv : ∀ i, v i ∈ ruP)
    (hb : EBasis v) : (eSub (liftV_basis hv hb)).map e.toMonoidHom = img e (refSub v) := by
  rw [eSub_liftV hv hb, img]

end CFSG.Quasithin.KGC31.Ru

end
