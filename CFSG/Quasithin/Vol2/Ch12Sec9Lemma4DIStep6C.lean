module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep3

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

section Norm

variable {G : Type} [Group G] [Finite G]

@[expose] def preimgSub {V V₁ : Subgroup G} (D : HatModelU (u128 V V₁)) (Dh : Subgroup (D.V ≃ₗ[ZMod 2] D.V)) :
    Subgroup G where
  carrier := {x | ∃ hx : x ∈ Subgroup.normalizer (u128 V V₁ : Set G), D.ρ ⟨x, hx⟩ ∈ Dh}
  mul_mem' := by
    rintro x y ⟨hx, hxD⟩ ⟨hy, hyD⟩
    refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
    have e : D.ρ ⟨x * y, Subgroup.mul_mem _ hx hy⟩ = D.ρ ⟨x, hx⟩ * D.ρ ⟨y, hy⟩ := by
      rw [← map_mul]
      rfl
    rw [e]
    exact Dh.mul_mem hxD hyD
  one_mem' := ⟨Subgroup.one_mem _, by
    have e : D.ρ ⟨1, Subgroup.one_mem _⟩ = 1 := map_one D.ρ
    rw [e]
    exact Dh.one_mem⟩
  inv_mem' := by
    rintro x ⟨hx, hxD⟩
    refine ⟨Subgroup.inv_mem _ hx, ?_⟩
    have e : D.ρ ⟨x⁻¹, Subgroup.inv_mem _ hx⟩ = (D.ρ ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e]
    exact Dh.inv_mem hxD

theorem rho_normalizes_Dg (h12812 : Lemma12_8_12_two) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    (D : HatModelU (u128 V V₁))
    (hDgN1 : ∀ d ∈ CFSG.conjugate (zU128 V V₁) g, d ∈ Subgroup.normalizer (V₁ : Set G))
    {y : G} (hyV₁ : y ∈ Subgroup.normalizer (V₁ : Set G))
    (hyV₂ : y ∈ Subgroup.normalizer (V₂ : Set G))
    (hyU : y ∈ Subgroup.normalizer (u128 V V₁ : Set G)) :
    ∀ γ ∈ D.img (CFSG.conjugate (zU128 V V₁) g),
      D.ρ ⟨y, hyU⟩ * γ * (D.ρ ⟨y, hyU⟩)⁻¹ ∈ D.img (CFSG.conjugate (zU128 V V₁) g) := by
  classical
  set Dg := CFSG.conjugate (zU128 V V₁) g with hDg
  set Dh := D.img Dg with hDh
  have hN1U : ∀ x ∈ Subgroup.normalizer (V₁ : Set G),
      x ∈ Subgroup.normalizer (u128 V V₁ : Set G) := fun x hx =>
    le_normalizer_conjClosure V _ hx
  have hDgU : ∀ d ∈ Dg, d ∈ Subgroup.normalizer (u128 V V₁ : Set G) := fun d hd =>
    hN1U d (hDgN1 d hd)
  have hyN : y ∈ Subgroup.normalizer ((Dg ⊔ centralizerMod (zU128 V V₁)
      (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) : Subgroup G) : Set G) :=
    (h12812 G T L V 4 V₁ V₂ hs g hgP hgN).2 (Subgroup.mem_inf.2 ⟨hyV₁, hyV₂⟩)
  have hK : Dg ⊔ centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) ≤
      preimgSub D Dh := by
    apply sup_le
    · intro d hd
      exact ⟨hDgU d hd, L128A.HatU.rho_mem_img D hd (hDgU d hd)⟩
    · intro c hc
      have hcN1 : c ∈ Subgroup.normalizer (V₁ : Set G) := hc.1
      have hcU : c ∈ Subgroup.normalizer (u128 V V₁ : Set G) := hN1U c hcN1
      refine ⟨hcU, ?_⟩
      have h1 : D.ρ ⟨c, hcU⟩ = 1 := by
        rw [L128A.HatU.rho_eq_one_iff]
        intro u hu
        exact hc.2.2 u hu
      rw [h1]
      exact Dh.one_mem
  intro γ hγ
  obtain ⟨d, hd, hdN, rfl⟩ := (L128A.HatU.mem_img D).1 hγ
  have hdDg : d ∈ Dg := hd
  have hydN : y * d * y⁻¹ ∈ Subgroup.normalizer (u128 V V₁ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hyU hdN) (Subgroup.inv_mem _ hyU)
  have e : D.ρ ⟨y, hyU⟩ * D.ρ ⟨d, hdN⟩ * (D.ρ ⟨y, hyU⟩)⁻¹ = D.ρ ⟨y * d * y⁻¹, hydN⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  have hmem : y * d * y⁻¹ ∈ Dg ⊔ centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G))
      (u128 V V₁) :=
    (Subgroup.mem_normalizer_iff.1 hyN d).1 (Subgroup.mem_sup_left hdDg)
  exact (hK hmem).2

theorem rho_stab_S {V V₁ : Subgroup G} (D : HatModelU (u128 V V₁)) {S : Submodule (ZMod 2) D.V}
    (hSV : ∀ v ∈ V, D.π v ∈ S) (hSπ : ∀ s ∈ S, ∃ v ∈ V, D.π v = s)
    {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hxU : x ∈ Subgroup.normalizer (u128 V V₁ : Set G)) :
    D.ρ ⟨x, hxU⟩ ∈ stabS S := by
  have fwd : ∀ g : G, ∀ hg : g ∈ Subgroup.normalizer (V : Set G),
      ∀ hgU : g ∈ Subgroup.normalizer (u128 V V₁ : Set G), ∀ w ∈ S, D.ρ ⟨g, hgU⟩ w ∈ S := by
    intro g hg hgU w hw
    obtain ⟨v, hv, rfl⟩ := hSπ w hw
    have e : D.ρ ⟨g, hgU⟩ (D.π v) = D.π (g * v * g⁻¹) :=
      D.ρ_π ⟨g, hgU⟩ v (le_conjClosure V _ hv)
    rw [e]
    exact hSV _ ((Subgroup.mem_normalizer_iff.1 hg v).1 hv)
  rw [mem_stabS_iff]
  intro w
  constructor
  · exact fun hw => fwd x hxV hxU w hw
  · intro hw
    have h1 := fwd x⁻¹ (Subgroup.inv_mem _ hxV) (Subgroup.inv_mem _ hxU) _ hw
    have hinv : D.ρ ⟨x⁻¹, Subgroup.inv_mem _ hxU⟩ (D.ρ ⟨x, hxU⟩ w) = w := by
      rw [← LinearEquiv.mul_apply, ← map_mul]
      have h1' : (⟨x⁻¹, Subgroup.inv_mem _ hxU⟩ * ⟨x, hxU⟩ :
          Subgroup.normalizer (u128 V V₁ : Set G)) = 1 := Subtype.ext (by simp)
      rw [h1', map_one]
      rfl
    rw [hinv] at h1
    exact h1

theorem rho_Dg_ne_one (h12813 : Lemma12_8_13) {T L V V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V 4 V₁ V₂) {g : G} (hgP : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    (D : HatModelU (u128 V V₁))
    (hDgN1 : ∀ d ∈ CFSG.conjugate (zU128 V V₁) g, d ∈ Subgroup.normalizer (V₁ : Set G))
    (hlt : V₁ < zU128 V V₁) :
    ∃ d ∈ CFSG.conjugate (zU128 V V₁) g, ∃ hd : d ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨d, hd⟩ ≠ 1 := by
  have hnot := (h12813 G T L V 4 V₁ V₂ hs g hgP hgN).2.2.1 hlt
  rw [SetLike.le_def] at hnot
  push Not at hnot
  obtain ⟨d, hd, hdC⟩ := hnot
  have hdN : d ∈ Subgroup.normalizer (u128 V V₁ : Set G) := le_normalizer_conjClosure V _ (hDgN1 d hd)
  refine ⟨d, hd, hdN, ?_⟩
  intro h1
  apply hdC
  refine ⟨hDgN1 d hd, CFSG.Quasithin.A4.normalizer_le_normalizer_centerOf (u128 V V₁) hdN, ?_⟩
  intro u hu
  rw [L128A.HatU.rho_eq_one_iff] at h1
  exact h1 u hu

end Norm

end CFSG.Quasithin.H13.C1294
