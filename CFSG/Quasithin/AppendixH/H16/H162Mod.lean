module

public import CFSG.Quasithin.AppendixH.H16.ConjNat

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Open

variable {V W : Type*} [CommGroup V] [CommGroup W]

private theorem congrHom_apply_apply' (e : V ≃* W) (h : MulAut V) (c : V) :
    congrHom e h (e c) = e (h c) := by simp [congrHom_apply]

private theorem congrHom_mul_inv' (e : V ≃* W) (g : MulAut V) (y : V) :
    congrHom e g (e y) * (e y)⁻¹ = e.toMonoidHom (g y * y⁻¹) := by
  simp [congrHom_apply]

private theorem coe_toMonoidHom (e : V ≃* W) (v : V) : e.toMonoidHom v = e v := rfl

private theorem congrHom_conj' (e : V ≃* W) (h g : MulAut V) :
    congrHom e (h * g * h⁻¹) = congrHom e h * congrHom e g * (congrHom e h)⁻¹ := by
  simp only [map_mul, map_inv]

private theorem mulAut_congr_apply_apply (φ : V ≃* W) (f : MulAut V) (v : V) :
    (MulAut.congr φ) f (φ v) = φ (f v) := by
  change φ (f (φ.symm (φ v))) = φ (f v)
  rw [MulEquiv.symm_apply_apply]

theorem fullTranspCenter_map (e : V ≃* W) (G X : Subgroup (MulAut V)) (A V₁ : Subgroup V) :
    FullTranspCenter (G.map (congrHom e)) (X.map (congrHom e)) (A.map e.toMonoidHom)
        (V₁.map e.toMonoidHom) ↔
      FullTranspCenter G X A V₁ := by
  let φ : ↥A ≃* ↥(A.map e.toMonoidHom) := MulEquiv.subgroupMap e A
  have hφ : ∀ a : ↥A, (φ a : W) = e (a : V) := fun a => MulEquiv.coe_subgroupMap_apply e A a
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg x hx
      have h1 := h.1 (congrHom e g) (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩) (e x)
        (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      rwa [congrHom_mul_inv' e g x,
        Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective] at h1
    · intro τ hτ
      let τ' : MulAut ↥(A.map e.toMonoidHom) := (MulAut.congr φ) τ
      have hτ' : ∀ x : ↥(A.map e.toMonoidHom),
          ((τ' x : ↥(A.map e.toMonoidHom)) : W) *
            ((x : ↥(A.map e.toMonoidHom)) : W)⁻¹ ∈ V₁.map e.toMonoidHom := by
        intro x
        obtain ⟨y, rfl⟩ := φ.surjective x
        have hthis : (τ' (φ y) : W) = e ((τ y : ↥A) : V) := by
          show ((MulAut.congr φ) τ (φ y) : W) = e ((τ y : ↥A) : V)
          rw [mulAut_congr_apply_apply]
          exact hφ (τ y)
        rw [hthis, hφ y, ← map_inv, ← map_mul]
        exact Subgroup.mem_map.mpr ⟨_, hτ y, rfl⟩
      obtain ⟨g', hg', hg'v⟩ := h.2.1 τ' hτ'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      refine ⟨g, hg, fun x => e.injective ?_⟩
      calc e (g (x : V)) = congrHom e g (e (x : V)) := (congrHom_apply_apply' e g (x:V)).symm
        _ = congrHom e g (φ x) := by rw [hφ x]
        _ = (τ' (φ x) : W) := hg'v (φ x)
        _ = (φ (τ x) : W) := by
              show ((MulAut.congr φ) τ (φ x) : W) = (φ (τ x) : W)
              rw [mulAut_congr_apply_apply]
        _ = e ((τ x : ↥A) : V) := hφ (τ x)
    · intro g hg hgtriv
      have hg1 : congrHom e g = 1 := h.2.2.1 (congrHom e g)
        (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩) fun x hx => by
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
          rw [coe_toMonoidHom, congrHom_apply_apply' e g y, hgtriv y hy]
      exact congrHom_injective e (by rw [hg1, map_one])
    · intro h₀ hh₀ g₀ hg₀
      have h1 := h.2.2.2 (congrHom e h₀) (Subgroup.mem_map.mpr ⟨h₀, hh₀, rfl⟩)
        (congrHom e g₀) (Subgroup.mem_map.mpr ⟨g₀, hg₀, rfl⟩)
      rw [← congrHom_conj' e h₀ g₀] at h1
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp h1
      rwa [congrHom_injective e hyeq] at hy
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g' hg' x' hx'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
      change congrHom e g (e x) * (e x)⁻¹ ∈ V₁.map e.toMonoidHom
      rw [congrHom_mul_inv' e g x]
      exact Subgroup.mem_map.mpr ⟨g x * x⁻¹, h.1 g hg x hx, rfl⟩
    · intro τ' hτ'
      let τ : MulAut ↥A := (MulAut.congr φ).symm τ'
      have hτ : ∀ y : ↥A, ((τ y : ↥A) : V) * ((y : ↥A) : V)⁻¹ ∈ V₁ := by
        intro y
        refine (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp ?_
        change e (((τ y : ↥A) : V) * ((y : ↥A) : V)⁻¹) ∈ V₁.map e.toMonoidHom
        rw [map_mul, map_inv, ← hφ (τ y), ← hφ y]
        have h1 := hτ' (φ y)
        rwa [← show (MulAut.congr φ) τ = τ' from MulEquiv.apply_symm_apply (MulAut.congr φ) τ',
          show ((MulAut.congr φ) τ (φ y) : W) = (φ (τ y) : W) by
            rw [mulAut_congr_apply_apply]] at h1
      obtain ⟨g, hg, hgv⟩ := h.2.1 τ hτ
      refine ⟨congrHom e g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩, fun x => ?_⟩
      obtain ⟨y, rfl⟩ := φ.surjective x
      calc congrHom e g (φ y) = congrHom e g (e (y : V)) := by rw [hφ y]
        _ = e (g (y : V)) := congrHom_apply_apply' e g (y:V)
        _ = e ((τ y : ↥A) : V) := by rw [hgv y]
        _ = (φ (τ y) : W) := (hφ (τ y)).symm
        _ = ((MulAut.congr φ) τ (φ y) : W) := by
              show (φ (τ y) : W) = ((MulAut.congr φ) τ (φ y) : W)
              rw [mulAut_congr_apply_apply]
        _ = (τ' (φ y) : W) := by
              rw [show (MulAut.congr φ) τ = τ' from MulEquiv.apply_symm_apply (MulAut.congr φ) τ']
    · intro g' hg' hgtriv
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      have hg1 : g = 1 := h.2.2.1 g hg fun x hx => e.injective (by
        have hh := hgtriv (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
        rwa [congrHom_apply_apply' e g x] at hh)
      rw [hg1, map_one]
    · intro h' hh' g' hg'
      obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hh'
      obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg'
      rw [← congrHom_conj' e h₀ g₀]
      exact Subgroup.mem_map.mpr ⟨h₀ * g₀ * h₀⁻¹, h.2.2.2 h₀ hh₀ g₀ hg₀, rfl⟩

theorem inducesOnVia_top_map (e : V ≃* W) (G : Subgroup (MulAut V)) (Z : Subgroup V) {A : Type*}
    [CommGroup A] (Γ : Subgroup (MulAut A)) (β' : W →* A) :
    InducesOnVia (G.map (congrHom e)) ⊤ (Z.map e.toMonoidHom) A Γ
        (β'.comp (⊤ : Subgroup W).subtype) ↔
      InducesOnVia G ⊤ Z A Γ ((β'.comp e.toMonoidHom).comp (⊤ : Subgroup V).subtype) := by
  have hβW : ∀ w : ↥(⊤ : Subgroup W), (β'.comp (⊤ : Subgroup W).subtype) w = β' (w : W) :=
    fun _ => rfl
  have hβV : ∀ u : ↥(⊤ : Subgroup V),
      ((β'.comp e.toMonoidHom).comp (⊤ : Subgroup V).subtype) u = β' (e (u : V)) :=
    fun _ => rfl
  constructor
  · intro h
    obtain ⟨hZU, hGU, hGZ, hsurj, hker, hfwd, hbwd⟩ := h
    refine ⟨le_top, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg u hu; trivial
    · intro g hg z hz
      have h1 := hGZ (congrHom e g) (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩) (e z)
        (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
      rw [congrHom_apply_apply' e g z] at h1
      exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp (by
        rw [coe_toMonoidHom]; exact h1)
    · intro a
      obtain ⟨w, hw⟩ := hsurj a
      refine ⟨⟨e.symm (w : W), trivial⟩, ?_⟩
      change β' (e (e.symm (w : W))) = a
      rw [e.apply_symm_apply, ← hβW w]
      exact hw
    · intro u
      change β' (e (u : V)) = 1 ↔ (u : V) ∈ Z
      have h1 := hker ⟨e (u : V), trivial⟩
      rw [hβW] at h1
      exact h1.trans (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective)
    · intro g hg
      obtain ⟨γ, hγ, hγv⟩ := hfwd (congrHom e g) (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
      refine ⟨γ, hγ, fun u u' hu => ?_⟩
      have huu : e (u' : V) = congrHom e g (e (u : V)) := by
        rw [hu, congrHom_apply_apply' e g (u:V)]
      change β' (e (u' : V)) = γ (β' (e (u : V)))
      exact hγv ⟨e (u : V), trivial⟩ ⟨e (u' : V), trivial⟩ huu
    · intro γ hγ
      obtain ⟨g', hg', hγv⟩ := hbwd γ hγ
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      refine ⟨g, hg, fun u u' hu => ?_⟩
      have huu : e (u' : V) = congrHom e g (e (u : V)) := by
        rw [hu, congrHom_apply_apply' e g (u:V)]
      change β' (e (u' : V)) = γ (β' (e (u : V)))
      exact hγv ⟨e (u : V), trivial⟩ ⟨e (u' : V), trivial⟩ huu
  · intro h
    obtain ⟨hZU, hGU, hGZ, hsurj, hker, hfwd, hbwd⟩ := h
    refine ⟨le_top, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg u hu; trivial
    · intro g' hg' z' hz'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hz'
      exact Subgroup.mem_map.mpr ⟨g z, hGZ g hg z hz, by simp [congrHom_apply]⟩
    · intro a
      obtain ⟨u, hu⟩ := hsurj a
      refine ⟨⟨e (u : V), trivial⟩, ?_⟩
      change β' (e (u : V)) = a
      rw [← hβV u]
      exact hu
    · intro w
      have h1 := hker ⟨e.symm (w : W), trivial⟩
      change β' (e (e.symm (w : W))) = 1 ↔ e.symm (w : W) ∈ Z at h1
      rw [e.apply_symm_apply] at h1
      change β' (w : W) = 1 ↔ (w : W) ∈ Z.map e.toMonoidHom
      have hw : (w : W) = e.toMonoidHom (e.symm (w : W)) := by
        rw [coe_toMonoidHom, e.apply_symm_apply]
      have h2 : (w : W) ∈ Z.map e.toMonoidHom ↔ e.symm (w : W) ∈ Z := by
        conv_lhs => rw [hw]
        exact Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective
      exact h1.trans h2.symm
    · intro g' hg'
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
      obtain ⟨γ, hγ, hγv⟩ := hfwd g hg
      refine ⟨γ, hγ, fun w w' hw => ?_⟩
      let u : ↥(⊤ : Subgroup V) := ⟨e.symm (w : W), trivial⟩
      let u' : ↥(⊤ : Subgroup V) := ⟨e.symm (w' : W), trivial⟩
      have huu : (u' : V) = g u := by
        apply e.injective
        change e (e.symm (w' : W)) = e (g (e.symm (w : W)))
        rw [e.apply_symm_apply, ← congrHom_apply_apply' e g (e.symm (w : W)), e.apply_symm_apply]
        exact hw
      have hres := hγv u u' huu
      change β' (w' : W) = γ (β' (w : W))
      rw [show (w' : W) = e (e.symm (w' : W)) from (e.apply_symm_apply (w' : W)).symm,
        show (w : W) = e (e.symm (w : W)) from (e.apply_symm_apply (w : W)).symm]
      exact hres
    · intro γ hγ
      obtain ⟨g, hg, hγv⟩ := hbwd γ hγ
      refine ⟨congrHom e g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩, fun w w' hw => ?_⟩
      let u : ↥(⊤ : Subgroup V) := ⟨e.symm (w : W), trivial⟩
      let u' : ↥(⊤ : Subgroup V) := ⟨e.symm (w' : W), trivial⟩
      have huu : (u' : V) = g u := by
        apply e.injective
        change e (e.symm (w' : W)) = e (g (e.symm (w : W)))
        rw [e.apply_symm_apply, ← congrHom_apply_apply' e g (e.symm (w : W)), e.apply_symm_apply]
        exact hw
      have hres := hγv u u' huu
      change β' (w' : W) = γ (β' (w : W))
      rw [show (w' : W) = e (e.symm (w' : W)) from (e.apply_symm_apply (w' : W)).symm,
        show (w : W) = e (e.symm (w : W)) from (e.apply_symm_apply (w : W)).symm]
      exact hres

theorem isDualOfConj_of_twist (ρ : ↥M24g →* MulAut V) (ρ' : ↥M24g →* MulAut W) (e : V ≃* W)
    (τ : ↥M24g) (hcongr : ∀ γ : ↥M24g, congrHom e (ρ γ) = ρ' (τ⁻¹ * γ * τ))
    {G G' K K' : Subgroup S24} {A B : Subgroup V}
    (hG : G' = conjSubg ((τ : S24)⁻¹) G) (hK : K' = conjSubg ((τ : S24)⁻¹) K) :
    IsDualOfConj ρ' G' (A.map e.toMonoidHom) (B.map e.toMonoidHom) K' →
      IsDualOfConj ρ G A B K := by
  rintro ⟨pr', hpr1, hpr2, hpr3, hpr4, hpr5, hpr6⟩
  have hKmem : ∀ k : S24, (τ : S24)⁻¹ * k * (τ : S24) ∈ K' ↔ k ∈ K := by
    intro k
    rw [hK, mem_conjSubg_iff]
    rw [show ((τ : S24)⁻¹)⁻¹ * ((τ : S24)⁻¹ * k * (τ : S24)) * (τ : S24)⁻¹ = k by group]
  have hGmem : ∀ g : S24, (τ : S24)⁻¹ * g * (τ : S24) ∈ G' ↔ g ∈ G := by
    intro g
    rw [hG, mem_conjSubg_iff]
    rw [show ((τ : S24)⁻¹)⁻¹ * ((τ : S24)⁻¹ * g * (τ : S24)) * (τ : S24)⁻¹ = g by group]
  let pr : V → S24 → ZMod 2 := fun x k => pr' (e x) ((τ : S24)⁻¹ * k * (τ : S24))
  refine ⟨pr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx k hk k' hk'
    dsimp only [pr]
    have h1 := hpr1 (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      ((τ : S24)⁻¹ * k * (τ : S24)) ((hKmem k).mpr hk)
      ((τ : S24)⁻¹ * k' * (τ : S24)) ((hKmem k').mpr hk')
    rw [show (τ : S24)⁻¹ * (k * k') * (τ : S24) =
        ((τ : S24)⁻¹ * k * (τ : S24)) * ((τ : S24)⁻¹ * k' * (τ : S24)) by group]
    exact h1
  · intro x hx x' hx' k hk
    dsimp only [pr]
    have h1 := hpr2 (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩) (e x')
      (Subgroup.mem_map.mpr ⟨x', hx', rfl⟩) ((τ : S24)⁻¹ * k * (τ : S24))
      ((hKmem k).mpr hk)
    rw [map_mul]
    exact h1
  · intro x hx k hk
    dsimp only [pr]
    exact hpr3 (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩) ((τ : S24)⁻¹ * k * (τ : S24))
      ((hKmem k).mpr hk)
  · intro x hx hxB
    dsimp only [pr]
    have hxA : e x ∈ A.map e.toMonoidHom := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxBn : e x ∉ B.map e.toMonoidHom := fun hmem =>
      hxB ((Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hmem)
    obtain ⟨k', hk', hne⟩ := hpr4 (e x) hxA hxBn
    refine ⟨(τ : S24) * k' * (τ : S24)⁻¹, ?_, ?_⟩
    · exact (hKmem ((τ : S24) * k' * (τ : S24)⁻¹)).mp (by convert hk' using 1; group)
    · rw [show (τ : S24)⁻¹ * ((τ : S24) * k' * (τ : S24)⁻¹) * (τ : S24) = k' by group]
      exact hne
  · intro k hk hk1
    dsimp only [pr]
    have hk' : (τ : S24)⁻¹ * k * (τ : S24) ∈ K' := (hKmem k).mpr hk
    have hk'1 : (τ : S24)⁻¹ * k * (τ : S24) ≠ 1 := by
      intro h
      exact hk1 (by
        calc k = (τ : S24) * ((τ : S24)⁻¹ * k * (τ : S24)) * (τ : S24)⁻¹ := by group
          _ = (τ : S24) * 1 * (τ : S24)⁻¹ := by rw [h]
          _ = 1 := by group)
    obtain ⟨x', hx', hne⟩ := hpr5 ((τ : S24)⁻¹ * k * (τ : S24)) hk' hk'1
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    exact ⟨x, hx, hne⟩
  · intro g hg x hx k hk
    dsimp only [pr]
    have hg'' : (τ : S24)⁻¹ * (g : S24) * (τ : S24) ∈ G' := (hGmem (g : S24)).mpr hg
    have hg' : ((τ⁻¹ * g * τ : ↥M24g) : S24) ∈ G' := by
      simpa using hg''
    have hk' : (τ : S24)⁻¹ * k * (τ : S24) ∈ K' := (hKmem k).mpr hk
    have hkey := hpr6 (τ⁻¹ * g * τ) hg' (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      ((τ : S24)⁻¹ * k * (τ : S24)) hk'
    have hee : e (ρ g x) = ρ' (τ⁻¹ * g * τ) (e x) := by
      rw [← congrHom_apply_apply' e (ρ g) x, hcongr g]
    have hconj : ((τ⁻¹ * g * τ : ↥M24g) : S24) * ((τ : S24)⁻¹ * k * (τ : S24)) *
        (((τ⁻¹ * g * τ : ↥M24g) : S24))⁻¹
        = (τ : S24)⁻¹ * ((g : S24) * k * (g : S24)⁻¹) * (τ : S24) := by
      push_cast
      group
    calc pr' (e (ρ g x)) ((τ : S24)⁻¹ * ((g : S24) * k * (g : S24)⁻¹) * (τ : S24))
        = pr' (ρ' (τ⁻¹ * g * τ) (e x))
            (((τ⁻¹ * g * τ : ↥M24g) : S24) * ((τ : S24)⁻¹ * k * (τ : S24)) *
              (((τ⁻¹ * g * τ : ↥M24g) : S24))⁻¹) := by rw [hee, ← hconj]
      _ = pr' (e x) ((τ : S24)⁻¹ * k * (τ : S24)) := hkey

end CFSG.ASVolI.H16
