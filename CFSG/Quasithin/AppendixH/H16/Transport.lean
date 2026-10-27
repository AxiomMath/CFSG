module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.AppendixH.H15.Vocab

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H

variable {V W : Type*} [CommGroup V] [CommGroup W]

private theorem congrHom_mul_inv (e : V ≃* W) (g : MulAut V) (y : V) :
    congrHom e g (e y) * (e y)⁻¹ = e.toMonoidHom (g y * y⁻¹) := by
  simp [congrHom_apply]

private theorem congrHom_mul_inv_mul_inv (e : V ≃* W) (g : MulAut V) (y c : V) :
    congrHom e g (e y) * (e y)⁻¹ * (e c)⁻¹ = e.toMonoidHom (g y * y⁻¹ * c⁻¹) := by
  simp [congrHom_apply]

private theorem congrHom_conj (e : V ≃* W) (h g : MulAut V) :
    congrHom e (h * g * h⁻¹) = congrHom e h * congrHom e g * (congrHom e h)⁻¹ := by
  simp only [map_mul, map_inv]

private theorem congrHom_apply_apply (e : V ≃* W) (h : MulAut V) (c : V) :
    congrHom e h (e c) = e (h c) := by
  simp [congrHom_apply]

private theorem mulAut_congr_apply (e : V ≃* W) (a : MulAut V) (w : W) :
    (MulAut.congr e) a w = e (a (e.symm w)) := rfl

private theorem isActsInv_actsOnModule_map_iff (e : V ≃* W) (G : Subgroup (MulAut V))
    (X : Subgroup V) :
    IsActsInv (actsOnModule (G.map (congrHom e))) (X.map e.toMonoidHom) ↔
      IsActsInv (actsOnModule G) X := by
  constructor
  · intro h f hf x hx
    obtain ⟨y, hy, rfl⟩ := hf
    have hres := h (fun w : W => congrHom e y w)
      ⟨congrHom e y, Subgroup.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩ (e x)
      (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    rw [show congrHom e y (e x) = e (y x) by simp [congrHom_apply]] at hres
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hres
  · intro h f hf x hx
    obtain ⟨y, hy, rfl⟩ := hf
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨g x₀, h (fun v => g v) ⟨g, hg, rfl⟩ x₀ hx₀,
      by simp [congrHom_apply]⟩

private theorem forall_map_iff (e : V ≃* W) (G : Subgroup (MulAut V)) (X : Subgroup V) :
    (∀ g ∈ G.map (congrHom e), ∀ x ∈ X.map e.toMonoidHom, g x ∈ X.map e.toMonoidHom) ↔
      ∀ g ∈ G, ∀ x ∈ X, g x ∈ X := by
  constructor
  · intro h g hg x hx
    have hres := h (congrHom e g) (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩) (e x)
      (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    rw [show congrHom e g (e x) = e (g x) by simp [congrHom_apply]] at hres
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hres
  · intro h g' hg' x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨g x₀, h g hg x₀ hx₀, by simp [congrHom_apply]⟩

private theorem isTranspAxis_map (e : V ≃* W) (g : MulAut V) (U Z : Subgroup V) (c : V) :
    IsTranspAxis (congrHom e g) (U.map e.toMonoidHom) (Z.map e.toMonoidHom) (e c) ↔
      IsTranspAxis g U Z c := by
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hh := h.1 (e y) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
      rwa [congrHom_mul_inv e g y, Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective] at hh
    · have hh := h.2 (e y) (fun hmem => hy ((Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hmem))
      rwa [congrHom_mul_inv_mul_inv e g y c, Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective] at hh
  · intro h
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨y, rfl⟩ := e.surjective x
      have hy : y ∈ Z := (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hx
      have hh := h.1 y hy
      rwa [congrHom_mul_inv e g y, Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective]
    · obtain ⟨y, rfl⟩ := e.surjective x
      have hy : y ∉ Z := fun hy => hx ((Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mpr hy)
      have hh := h.2 y hy
      rwa [congrHom_mul_inv_mul_inv e g y c, Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective]

private theorem isTranspAxis_conj_iff (e : V ≃* W) (h g : MulAut V) (U Z : Subgroup V) (c : V) :
    IsTranspAxis (congrHom e h * congrHom e g * (congrHom e h)⁻¹) (U.map e.toMonoidHom)
        (Z.map e.toMonoidHom) (congrHom e h (e c)) ↔
      IsTranspAxis (h * g * h⁻¹) U Z (h c) := by
  rw [← congrHom_conj e h g, congrHom_apply_apply e h c]
  exact isTranspAxis_map e (h * g * h⁻¹) U Z (h c)

private theorem exists_beta_map_iff (e : V ≃* W) (U Z : Subgroup V)
    (G : Subgroup (MulAut V)) {A : Type*} [CommGroup A] (Γ : Subgroup (MulAut A)) :
    (∃ β : ↥(U.map e.toMonoidHom) →* A, Function.Surjective β ∧
        (∀ u : ↥(U.map e.toMonoidHom), β u = 1 ↔ (u : W) ∈ Z.map e.toMonoidHom) ∧
        (∀ g ∈ G.map (congrHom e), ∃ γ ∈ Γ, ∀ u u' : ↥(U.map e.toMonoidHom),
          (u' : W) = g u → β u' = γ (β u)) ∧
        (∀ γ ∈ Γ, ∃ g ∈ G.map (congrHom e), ∀ u u' : ↥(U.map e.toMonoidHom),
          (u' : W) = g u → β u' = γ (β u))) ↔
    (∃ β : ↥U →* A, Function.Surjective β ∧
        (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
        (∀ g ∈ G, ∃ γ ∈ Γ, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u)) ∧
        (∀ γ ∈ Γ, ∃ g ∈ G, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u))) := by
  let φ : ↥U ≃* ↥(U.map e.toMonoidHom) := U.equivMapOfInjective e.toMonoidHom e.injective
  have hφ : ∀ u : ↥U, (φ u : W) = e (u : V) := fun u =>
    Subgroup.coe_equivMapOfInjective_apply U e.toMonoidHom e.injective u
  have key : ∀ (g : MulAut V) (u u₂ : ↥U),
      (φ u₂ : W) = congrHom e g (φ u) ↔ (u₂ : V) = g u := by
    intro g u u₂
    rw [hφ u₂, hφ u, congrHom_apply, e.symm_apply_apply]
    exact e.injective.eq_iff
  constructor
  · rintro ⟨β', hsurj, hker, hfwd, hbwd⟩
    refine ⟨β'.comp φ, hsurj.comp φ.surjective, ?_, ?_, ?_⟩
    · intro u
      have h1 : (φ u : W) ∈ Z.map e.toMonoidHom ↔ (u : V) ∈ Z := by
        rw [hφ u]
        exact Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective
      rw [MonoidHom.comp_apply]
      exact (hker (φ u)).trans h1
    · intro g hg
      obtain ⟨γ, hγ, hγc⟩ := hfwd (congrHom e g) (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
      refine ⟨γ, hγ, fun u u₂ hu => ?_⟩
      change (β'.comp φ) u₂ = γ ((β'.comp φ) u)
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
      exact hγc (φ u) (φ u₂) ((key g u u₂).mpr hu)
    · intro γ hγ
      obtain ⟨g', hg', hgc⟩ := hbwd γ hγ
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      refine ⟨g, hg, fun u u₂ hu => ?_⟩
      change (β'.comp φ) u₂ = γ ((β'.comp φ) u)
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
      exact hgc (φ u) (φ u₂) ((key g u u₂).mpr hu)
  · rintro ⟨β, hsurj, hker, hfwd, hbwd⟩
    refine ⟨β.comp φ.symm, hsurj.comp φ.symm.surjective, ?_, ?_, ?_⟩
    · intro u'
      have h1 : (u' : W) ∈ Z.map e.toMonoidHom ↔ ((φ.symm u' : ↥U) : V) ∈ Z := by
        have h2 : (u' : W) = e ((φ.symm u' : ↥U) : V) := by
          rw [← hφ (φ.symm u'), φ.apply_symm_apply]
        rw [h2]
        exact Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective
      rw [MonoidHom.comp_apply]
      exact (hker (φ.symm u')).trans h1.symm
    · intro g' hg'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨γ, hγ, hγc⟩ := hfwd g hg
      refine ⟨γ, hγ, fun u' u₂' hu => ?_⟩
      obtain ⟨u, rfl⟩ := φ.surjective u'
      obtain ⟨u₂, rfl⟩ := φ.surjective u₂'
      have hu' : (u₂ : V) = g u := (key g u u₂).mp hu
      have h2 : (β.comp φ.symm) (φ u₂) = β u₂ :=
        congrArg β (MulEquiv.symm_apply_apply φ u₂)
      have h1 : (β.comp φ.symm) (φ u) = β u :=
        congrArg β (MulEquiv.symm_apply_apply φ u)
      rw [h2, h1]
      exact hγc u u₂ hu'
    · intro γ hγ
      obtain ⟨g, hg, hgc⟩ := hbwd γ hγ
      refine ⟨congrHom e g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩, fun u' u₂' hu => ?_⟩
      obtain ⟨u, rfl⟩ := φ.surjective u'
      obtain ⟨u₂, rfl⟩ := φ.surjective u₂'
      have hu' : (u₂ : V) = g u := (key g u u₂).mp hu
      have h2 : (β.comp φ.symm) (φ u₂) = β u₂ :=
        congrArg β (MulEquiv.symm_apply_apply φ u₂)
      have h1 : (β.comp φ.symm) (φ u) = β u :=
        congrArg β (MulEquiv.symm_apply_apply φ u)
      rw [h2, h1]
      exact hgc u u₂ hu'

theorem rk_map_mulEquiv (e : V ≃* W) (U : Subgroup V) :
    rk ↥(U.map e.toMonoidHom) = rk ↥U := by
  unfold rk
  rw [Subgroup.card_map_of_injective e.injective]

theorem rk_fixV_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) :
    rk ↥(fixV (X.map (congrHom e))) = rk ↥(fixV X) := by
  rw [fixV_map_congrHom, rk_map_mulEquiv]

theorem commV_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) :
    commV (X.map (congrHom e)) = (commV X).map e.toMonoidHom := by
  unfold commV
  rw [MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨x', hx', v', rfl⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    refine ⟨x (e.symm v') * (e.symm v')⁻¹, ⟨x, hx, e.symm v', rfl⟩, ?_⟩
    simp only [map_mul, map_inv, congrHom_apply, e.symm_apply_apply, e.apply_symm_apply, MulEquiv.coe_toMonoidHom, mulAut_congr_apply]
  · rintro ⟨w₀, ⟨x, hx, v, rfl⟩, rfl⟩
    refine ⟨congrHom e x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, e v, ?_⟩
    simp only [map_mul, map_inv, congrHom_apply, e.symm_apply_apply, MulEquiv.coe_toMonoidHom, mulAut_congr_apply]

theorem commOn_map_congrHom (e : V ≃* W) (U : Subgroup V) (X : Subgroup (MulAut V)) :
    commOn (U.map e.toMonoidHom) (X.map (congrHom e)) = (commOn U X).map e.toMonoidHom := by
  unfold commOn
  rw [MonoidHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨a', ha', w', hw', rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hw'
    refine ⟨a w * w⁻¹, ⟨a, ha, w, hw, rfl⟩, ?_⟩
    simp only [map_mul, map_inv, congrHom_apply, e.symm_apply_apply, e.apply_symm_apply, MulEquiv.coe_toMonoidHom, mulAut_congr_apply]
  · rintro ⟨u₀, ⟨a, ha, w, hw, rfl⟩, rfl⟩
    refine ⟨congrHom e a, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, e w,
      Subgroup.mem_map.mpr ⟨w, hw, rfl⟩, ?_⟩
    simp only [map_mul, map_inv, congrHom_apply, e.symm_apply_apply, MulEquiv.coe_toMonoidHom, mulAut_congr_apply]

theorem isChiefFactorUnder_map (e : V ≃* W) (G : Subgroup (MulAut V)) (X Y : Subgroup V) :
    IsChiefFactorUnder (actsOnModule (G.map (congrHom e))) (X.map e.toMonoidHom)
        (Y.map e.toMonoidHom) ↔
      IsChiefFactorUnder (actsOnModule G) X Y := by
  unfold IsChiefFactorUnder
  rw [Subgroup.map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective]
  refine and_congr_right fun _ => and_congr (isActsInv_actsOnModule_map_iff e G X)
    (and_congr (isActsInv_actsOnModule_map_iff e G Y) ?_)
  constructor
  · intro h W hXW hWY hWi
    have hres := h (W.map e.toMonoidHom) (Subgroup.map_mono hXW) (Subgroup.map_mono hWY)
      ((isActsInv_actsOnModule_map_iff e G W).mpr hWi)
    have hinj : Function.Injective (Subgroup.map e.toMonoidHom) :=
      Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rcases hres with hres | hres
    · exact Or.inl (hinj hres)
    · exact Or.inr (hinj hres)
  · intro h W' hX'W' hW'Y' hWi'
    let W₀ : Subgroup V := W'.comap e.toMonoidHom
    have hmap : W₀.map e.toMonoidHom = W' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective W'
    have hX0 : X ≤ W₀ := by
      refine (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp ?_
      rwa [hmap]
    have hW0 : W₀ ≤ Y := by
      refine (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp ?_
      rwa [hmap]
    have hWi0 : IsActsInv (actsOnModule G) W₀ :=
      (isActsInv_actsOnModule_map_iff e G W₀).mp (by rwa [hmap])
    rcases h W₀ hX0 hW0 hWi0 with hres | hres
    · left; rw [← hmap, hres]
    · right; rw [← hmap, hres]

theorem inducesOn_map (e : V ≃* W) (G : Subgroup (MulAut V)) (U Z : Subgroup V) {A : Type*}
    [CommGroup A] (Γ : Subgroup (MulAut A)) :
    InducesOn (G.map (congrHom e)) (U.map e.toMonoidHom) (Z.map e.toMonoidHom) A Γ ↔
      InducesOn G U Z A Γ := by
  unfold InducesOn
  rw [Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective]
  refine and_congr_right fun _ => and_congr (forall_map_iff e G U)
    (and_congr (forall_map_iff e G Z) (exists_beta_map_iff e U Z G Γ))

theorem fullTranspAxis_map (e : V ≃* W) (G X : Subgroup (MulAut V)) (U Z : Subgroup V) :
    FullTranspAxis (G.map (congrHom e)) (X.map (congrHom e)) (U.map e.toMonoidHom)
        (Z.map e.toMonoidHom) ↔
      FullTranspAxis G X U Z := by
  unfold FullTranspAxis
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨c', hc', hc'ax⟩ := h.1 (congrHom e g) (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hc'
      exact ⟨c, hc, (isTranspAxis_map e g U Z c).mp hc'ax⟩
    · intro c hc
      obtain ⟨g', hg', hg'ax⟩ := h.2.1 (e c) (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      exact ⟨g, hg, (isTranspAxis_map e g U Z c).mp hg'ax⟩
    · intro g hg hgtriv
      have hc : congrHom e g = 1 := h.2.2.1 (congrHom e g)
        (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩) fun x => by
          obtain ⟨y, rfl⟩ := e.surjective x
          rw [congrHom_mul_inv e g y, Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective]
          exact hgtriv y
      exact congrHom_injective e (by rw [hc, map_one])
    · intro h₀ hh₀ g hg c hcax
      have hres := h.2.2.2 (congrHom e h₀) (Subgroup.mem_map.mpr ⟨h₀, hh₀, rfl⟩)
        (congrHom e g) (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩) (e c)
        ((isTranspAxis_map e g U Z c).mpr hcax)
      exact (isTranspAxis_conj_iff e h₀ g U Z c).mp hres
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g' hg'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨c, hc, hcax⟩ := h.1 g hg
      exact ⟨e c, Subgroup.mem_map.mpr ⟨c, hc, rfl⟩, (isTranspAxis_map e g U Z c).mpr hcax⟩
    · intro c' hc'
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hc'
      obtain ⟨g, hg, hgax⟩ := h.2.1 c hc
      exact ⟨congrHom e g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩,
        (isTranspAxis_map e g U Z c).mpr hgax⟩
    · intro g' hg' hgtriv
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      have hg1 : g = 1 := h.2.2.1 g hg fun y => by
        have := hgtriv (e y)
        rwa [congrHom_mul_inv e g y, Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective] at this
      rw [hg1, map_one]
    · intro h' hh' g' hg' c' hc'ax
      obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hh'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨c, rfl⟩ := e.surjective c'
      have hcax : IsTranspAxis g U Z c := (isTranspAxis_map e g U Z c).mp hc'ax
      exact (isTranspAxis_conj_iff e h₀ g U Z c).mpr (h.2.2.2 h₀ hh₀ g hg c hcax)

end CFSG.ASVolI.H16
