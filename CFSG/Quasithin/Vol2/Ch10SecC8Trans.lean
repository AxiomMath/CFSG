module

public import CFSG.Quasithin.Vol2.Ch10SecBInner3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13

section Transport

variable {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂] (e : W₁ ≃* W₂)

theorem fixV_map_congr (X : Subgroup (MulAut W₁)) :
    fixV (X.map (MulAut.congr e).toMonoidHom) = (fixV X).map e.toMonoidHom :=
  fixV_map_congr_equiv e X

theorem commV_map_congr (X : Subgroup (MulAut W₁)) :
    commV (X.map (MulAut.congr e).toMonoidHom) = (commV X).map e.toMonoidHom :=
  commV_map_congr_equiv e X

theorem isElemAbelian2_map {X : Subgroup (MulAut W₁)} {Y : Type} [Group Y]
    (f : MulAut W₁ →* Y) (hX : (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) ∧ ∀ a ∈ X, a ^ 2 = 1) :
    (∀ a ∈ X.map f, ∀ b ∈ X.map f, a * b = b * a) ∧ ∀ a ∈ X.map f, a ^ 2 = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hX.1 x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hX.2 x hx, map_one]

theorem exists_L3Data_map {Gm : Subgroup (MulAut W₁)} {Z : Subgroup W₁} (D : L3Data Gm ⊤ Z)
    {Gm' : Subgroup (MulAut W₂)} (hG : Gm' = Gm.map (MulAut.congr e).toMonoidHom)
    {Z' : Subgroup W₂} (hZ : ∀ w, w ∈ Z' ↔ e.symm w ∈ Z) :
    ∃ D' : L3Data Gm' ⊤ Z', ∀ γ, ((D'.π γ : ↥Gm') : MulAut W₂) = MulAut.congr e (D.π γ) := by
  have hmem : ∀ g ∈ Gm, MulAut.congr e g ∈ Gm' := fun g hg => by
    rw [hG]
    exact ⟨g, hg, rfl⟩
  let π' : L3.Γ →* ↥Gm' :=
    ((MulAut.congr e).toMonoidHom.comp (Gm.subtype.comp D.π)).codRestrict Gm' fun γ =>
      hmem _ (D.π γ).2
  let f : ↥(⊤ : Subgroup W₂) →* ↥(⊤ : Subgroup W₁) :=
    MonoidHom.codRestrict (e.symm.toMonoidHom.comp (⊤ : Subgroup W₂).subtype) ⊤
      fun _ => Subgroup.mem_top _
  refine ⟨{ π := π'
            β := D.β.comp f
            π_surj := fun g => ?_
            β_surj := fun y => ?_
            ker_β := fun u => ?_
            Z_le := le_top
            inv_U := fun _ _ _ _ => Subgroup.mem_top _
            inv_Z := fun g hg z hz => ?_
            equi := fun γ u hu => ?_ }, fun γ => rfl⟩
  · obtain ⟨g, hg⟩ := g
    rw [hG] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    obtain ⟨γ, hγ⟩ := D.π_surj ⟨g', hg'⟩
    refine ⟨γ, Subtype.ext ?_⟩
    change MulAut.congr e (D.π γ) = _
    rw [hγ]
    rfl
  · obtain ⟨x, hx⟩ := D.β_surj y
    refine ⟨⟨e x, Subgroup.mem_top _⟩, ?_⟩
    change D.β ⟨e.symm (e x), _⟩ = y
    rw [← hx]
    congr 1
    exact Subtype.ext (e.symm_apply_apply _)
  · change D.β ⟨e.symm u, _⟩ = 1 ↔ (u : W₂) ∈ Z'
    rw [D.ker_β, hZ]
  · rw [hG] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    rw [hZ] at hz ⊢
    change e.symm (e (g' (e.symm z))) ∈ Z
    rw [e.symm_apply_apply]
    exact D.inv_Z g' hg' _ hz
  · change D.β ⟨e.symm (e ((D.π γ : MulAut W₁) (e.symm u))), _⟩ =
      Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd (D.β ⟨e.symm u, _⟩)))
    rw [← D.equi γ ⟨e.symm u, Subgroup.mem_top _⟩ (Subgroup.mem_top _)]
    congr 1
    exact Subtype.ext (e.symm_apply_apply _)

end Transport

variable {G : Type} [Group G]

@[expose] def conjIso {W W' : Subgroup G} (t : G) (hW : ∀ x, x ∈ W' ↔ t * x * t⁻¹ ∈ W) :
    ↥W ≃* ↥W' where
  toFun w := ⟨t⁻¹ * w * t, (hW _).mpr (by
    have e : t * (t⁻¹ * (w : G) * t) * t⁻¹ = w := by group
    rw [e]; exact w.2)⟩
  invFun w := ⟨t * w * t⁻¹, (hW w).mp w.2⟩
  left_inv w := Subtype.ext (by simp only; group)
  right_inv w := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjIso_symm_apply {W W' : Subgroup G} (t : G) (hW : ∀ x, x ∈ W' ↔ t * x * t⁻¹ ∈ W)
    (w : ↥W') : (((conjIso t hW).symm w : ↥W) : G) = t * w * t⁻¹ := rfl

theorem autOn_conjugate_eq_map {X X' W W' : Subgroup G} (t : G)
    (hX : ∀ x, x ∈ X' ↔ t * x * t⁻¹ ∈ X) (hW : ∀ x, x ∈ W' ↔ t * x * t⁻¹ ∈ W) :
    autOn X' W' = (autOn X W).map (MulAut.congr (conjIso t hW)).toMonoidHom := by
  have hN : ∀ x, x ∈ Subgroup.normalizer (W : Set G) →
      t⁻¹ * x * t ∈ Subgroup.normalizer (W' : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hW, hW]
    have e : t * (t⁻¹ * x * t * w * (t⁻¹ * x * t)⁻¹) * t⁻¹ = x * (t * w * t⁻¹) * x⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hx _
  have hN' : ∀ y, y ∈ Subgroup.normalizer (W' : Set G) →
      t * y * t⁻¹ ∈ Subgroup.normalizer (W : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have e1 : w = t * (t⁻¹ * w * t) * t⁻¹ := by group
    have e2 : t * y * t⁻¹ * w * (t * y * t⁻¹)⁻¹ = t * (y * (t⁻¹ * w * t) * y⁻¹) * t⁻¹ := by
      group
    rw [e2]
    conv_lhs => rw [e1]
    rw [← hW, ← hW]
    exact Subgroup.mem_normalizer_iff.mp hy _
  have hcomp : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (W : Set G)),
      MulAut.congr (conjIso t hW) (conjAct W ⟨x, hx⟩) = conjAct W' ⟨t⁻¹ * x * t, hN x hx⟩ := by
    intro x hx
    ext w
    change t⁻¹ * (x * (t * w * t⁻¹) * x⁻¹) * t = t⁻¹ * x * t * w * (t⁻¹ * x * t)⁻¹
    group
  ext a
  constructor
  · intro ha
    obtain ⟨⟨y, hy⟩, hyX, rfl⟩ := SecB.mem_autOn_iff.mp ha
    refine ⟨conjAct W ⟨t * y * t⁻¹, hN' y hy⟩, SecB.mem_autOn_iff.mpr
      ⟨⟨t * y * t⁻¹, hN' y hy⟩, (hX y).mp hyX, rfl⟩, ?_⟩
    change MulAut.congr (conjIso t hW) (conjAct W ⟨t * y * t⁻¹, hN' y hy⟩) = _
    rw [hcomp]
    congr 2
    group
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨⟨x, hx⟩, hxX, rfl⟩ := SecB.mem_autOn_iff.mp hb
    change MulAut.congr (conjIso t hW) (conjAct W ⟨x, hx⟩) ∈ _
    rw [hcomp]
    refine SecB.mem_autOn_iff.mpr ⟨⟨t⁻¹ * x * t, hN x hx⟩, (hX _).mpr ?_, rfl⟩
    have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rw [e]
    exact hxX

end CFSG.Quasithin.Vol2.Ch10.SecC
