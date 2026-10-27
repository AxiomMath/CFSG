module

public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Quasithin.EmptyFaithful.SzPS8Torus

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.G11
open scoped MatrixGroups

namespace SzPS8

open L28

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Fix

@[expose] def fixSet (S : Subgroup (GLV V)) : AddSubgroup V where
  carrier := {v | ∀ s ∈ S, s v = v}
  zero_mem' := fun s _ => map_zero s
  add_mem' := fun {a b} ha hb s hs => by rw [map_add, ha s hs, hb s hs]
  neg_mem' := fun {a} ha s hs => by rw [map_neg, ha s hs]

@[expose] def oneSet (S : Subgroup (GLV V)) : AddSubgroup V where
  carrier := {v | ∀ s ∈ S, s v - v ∈ fixSet S}
  zero_mem' := fun s _ => by simp
  add_mem' := fun {a b} ha hb s hs => by
    have := (fixSet S).add_mem (ha s hs) (hb s hs)
    rw [map_add]
    convert this using 1
    abel
  neg_mem' := fun {a} ha s hs => by
    have := (fixSet S).neg_mem (ha s hs)
    rw [map_neg]
    convert this using 1
    abel

theorem map_mem_fixSet {S : Subgroup (GLV V)} {g : GLV V}
    (hg : g ∈ Subgroup.normalizer (S : Set (GLV V))) {v : V} (hv : v ∈ fixSet S) :
    g v ∈ fixSet S := by
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (S : Set (GLV V))).inv_mem hg) s).mp hs
    simpa using this
  have h2 : g⁻¹ (s (g v)) = v := hv _ hs'
  have h3 : g⁻¹ (g v) = v := LinearEquiv.symm_apply_apply g v
  exact (g⁻¹).injective (h2.trans h3.symm)

theorem map_mem_oneSet {S : Subgroup (GLV V)} {g : GLV V}
    (hg : g ∈ Subgroup.normalizer (S : Set (GLV V))) {v : V} (hv : v ∈ oneSet S) :
    g v ∈ oneSet S := by
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (S : Set (GLV V))).inv_mem hg) s).mp hs
    simpa using this
  have h1 := hv _ hs'
  have e : s (g v) - g v = g ((g⁻¹ * s * g) v - v) := by
    rw [map_sub]
    congr 1
    show s (g v) = g (g⁻¹ (s (g v)))
    exact (LinearEquiv.apply_symm_apply g _).symm
  rw [e]
  exact map_mem_fixSet hg h1

end Fix

section Y

@[expose] def yOne (F S : Subgroup (GLV V)) : Subgroup (GLV V) where
  carrier := {g | g ∈ F ∧ g ∈ Subgroup.normalizer (S : Set (GLV V)) ∧ ∀ v ∈ fixSet S, g v = v}
  one_mem' := ⟨F.one_mem, Subgroup.one_mem _, fun v _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨F.mul_mem ha.1 hb.1, Subgroup.mul_mem _ ha.2.1 hb.2.1,
    fun v hv => by
      show a (b v) = v
      rw [hb.2.2 v hv, ha.2.2 v hv]⟩
  inv_mem' := fun {a} ha => ⟨F.inv_mem ha.1, Subgroup.inv_mem _ ha.2.1, fun v hv => by
    show a.symm v = v
    exact (LinearEquiv.symm_apply_eq a).mpr (ha.2.2 v hv).symm⟩

@[expose] def yTwo (F S : Subgroup (GLV V)) : Subgroup (GLV V) where
  carrier := {g | g ∈ F ∧ g ∈ Subgroup.normalizer (S : Set (GLV V)) ∧
    ∀ v ∈ oneSet S, g v - v ∈ fixSet S}
  one_mem' := ⟨F.one_mem, Subgroup.one_mem _, fun v _ => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨F.mul_mem ha.1 hb.1, Subgroup.mul_mem _ ha.2.1 hb.2.1,
    fun v hv => by
      have h1 := map_mem_fixSet ha.2.1 (hb.2.2 v hv)
      have h2 := ha.2.2 v hv
      have := (fixSet S).add_mem h1 h2
      show a (b v) - v ∈ fixSet S
      convert this using 1
      rw [map_sub]
      abel⟩
  inv_mem' := fun {a} ha => ⟨F.inv_mem ha.1, Subgroup.inv_mem _ ha.2.1, fun v hv => by
    have h1 := map_mem_fixSet (Subgroup.inv_mem _ ha.2.1) (ha.2.2 v hv)
    have := (fixSet S).neg_mem h1
    show a.symm v - v ∈ fixSet S
    convert this using 1
    have e : a.symm (a v - v) = v - a.symm v := by
      rw [map_sub, LinearEquiv.symm_apply_apply]
    show _ = -(a.symm (a v - v))
    rw [e]
    abel⟩

theorem yOne_le (F S : Subgroup (GLV V)) :
    yOne F S ≤ F ⊓ Subgroup.normalizer (S : Set (GLV V)) := fun _ hg => ⟨hg.1, hg.2.1⟩

theorem yTwo_le (F S : Subgroup (GLV V)) :
    yTwo F S ≤ F ⊓ Subgroup.normalizer (S : Set (GLV V)) := fun _ hg => ⟨hg.1, hg.2.1⟩

theorem conj_mem_yOne {F S : Subgroup (GLV V)} {g b : GLV V}
    (hgF : g ∈ Subgroup.normalizer (F : Set (GLV V)))
    (hgS : g ∈ Subgroup.normalizer (S : Set (GLV V))) (hb : b ∈ yOne F S) :
    g * b * g⁻¹ ∈ yOne F S := by
  obtain ⟨hbF, hbS, hbfix⟩ := hb
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hgF b).mp hbF
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgS hbS) (Subgroup.inv_mem _ hgS)
  · show g (b (g⁻¹ v)) = v
    have h1 : g⁻¹ v ∈ fixSet S := map_mem_fixSet (Subgroup.inv_mem _ hgS) hv
    rw [hbfix _ h1]
    exact LinearEquiv.apply_symm_apply g v

theorem conj_mem_yTwo {F S : Subgroup (GLV V)} {g b : GLV V}
    (hgF : g ∈ Subgroup.normalizer (F : Set (GLV V)))
    (hgS : g ∈ Subgroup.normalizer (S : Set (GLV V))) (hb : b ∈ yTwo F S) :
    g * b * g⁻¹ ∈ yTwo F S := by
  obtain ⟨hbF, hbS, hbfix⟩ := hb
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hgF b).mp hbF
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgS hbS) (Subgroup.inv_mem _ hgS)
  · have h1 : g⁻¹ v ∈ oneSet S := map_mem_oneSet (Subgroup.inv_mem _ hgS) hv
    have h2 := map_mem_fixSet hgS (hbfix _ h1)
    show g (b (g⁻¹ v)) - v ∈ fixSet S
    have e : g (b (g⁻¹ v) - g⁻¹ v) = g (b (g⁻¹ v)) - v := by
      rw [map_sub]
      congr 1
      exact LinearEquiv.apply_symm_apply g v
    rw [← e]
    exact h2

theorem normalizer_yOne {F S : Subgroup (GLV V)} {g : GLV V}
    (hgF : g ∈ Subgroup.normalizer (F : Set (GLV V)))
    (hgS : g ∈ Subgroup.normalizer (S : Set (GLV V))) :
    g ∈ Subgroup.normalizer (yOne F S : Set (GLV V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨conj_mem_yOne hgF hgS, fun hb => ?_⟩
  have := conj_mem_yOne ((Subgroup.normalizer (F : Set (GLV V))).inv_mem hgF)
    ((Subgroup.normalizer (S : Set (GLV V))).inv_mem hgS) hb
  simpa [mul_assoc] using this

theorem normalizer_yTwo {F S : Subgroup (GLV V)} {g : GLV V}
    (hgF : g ∈ Subgroup.normalizer (F : Set (GLV V)))
    (hgS : g ∈ Subgroup.normalizer (S : Set (GLV V))) :
    g ∈ Subgroup.normalizer (yTwo F S : Set (GLV V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨conj_mem_yTwo hgF hgS, fun hb => ?_⟩
  have := conj_mem_yTwo ((Subgroup.normalizer (F : Set (GLV V))).inv_mem hgF)
    ((Subgroup.normalizer (S : Set (GLV V))).inv_mem hgS) hb
  simpa [mul_assoc] using this

end Y

section Frame

theorem frame_sylow {F S : Subgroup (GLV V)} (hSF : S ≤ F) (θ : ↥F ≃* Pr)
    (e : V ≃+ Matrix (Fin 2) (Fin 2) F4)
    (hint : ∀ (x : ↥F) (v : V), e ((x : GLV V) v) = act (θ x) (e v))
    (hS : ∀ x : ↥F, (x : GLV V) ∈ S ↔ θ x ∈ UU) :
    S ≤ yOne F S ∧ S ≤ yTwo F S ∧ S.relIndex (yOne F S) = 3 ∧ S.relIndex (yTwo F S) = 3 ∧
      F ⊓ Subgroup.normalizer (S : Set (GLV V)) ≤ yOne F S ⊔ yTwo F S := by
  classical
  set τ : Pr →* GLV V := F.subtype.comp θ.symm.toMonoidHom with hτ
  have hτinj : Function.Injective τ := fun a b h =>
    θ.symm.injective (Subtype.ext h)
  have hτF : ∀ u : Pr, τ u ∈ F := fun u => (θ.symm u).2
  have hτθ : ∀ x : ↥F, τ (θ x) = (x : GLV V) := fun x => by simp [hτ]
  have hτe : ∀ (u : Pr) (v : V), e ((τ u) v) = act u (e v) := fun u v => by
    have := hint (θ.symm u) v
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have K1 : ∀ u : Pr, τ u ∈ S ↔ u ∈ UU := fun u => by
    have := hS (θ.symm u)
    rwa [MulEquiv.apply_symm_apply] at this
  have hSmap : S = UU.map τ := by
    ext x
    constructor
    · intro hx
      have hxF : x ∈ F := hSF hx
      refine ⟨θ ⟨x, hxF⟩, (hS ⟨x, hxF⟩).mp hx, ?_⟩
      exact hτθ ⟨x, hxF⟩
    · rintro ⟨u, hu, rfl⟩
      exact (K1 u).mpr hu
  have K2 : F ⊓ Subgroup.normalizer (S : Set (GLV V)) = BB.map τ := by
    ext g
    constructor
    · rintro ⟨hgF, hgS⟩
      refine ⟨θ ⟨g, hgF⟩, ?_, hτθ ⟨g, hgF⟩⟩
      show θ ⟨g, hgF⟩ ∈ Subgroup.normalizer ((UU : Subgroup Pr) : Set Pr)
      rw [Subgroup.mem_normalizer_iff]
      intro u
      have h1 := Subgroup.mem_normalizer_iff.mp hgS (τ u)
      have h2 : τ (θ ⟨g, hgF⟩ * u * (θ ⟨g, hgF⟩)⁻¹) = g * τ u * g⁻¹ := by
        rw [map_mul, map_mul, map_inv, hτθ]
      rw [← K1, ← K1 (θ ⟨g, hgF⟩ * u * (θ ⟨g, hgF⟩)⁻¹), h2]
      exact h1
    · rintro ⟨b, hb, rfl⟩
      refine ⟨hτF b, ?_⟩
      show τ b ∈ Subgroup.normalizer (S : Set (GLV V))
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        rw [hSmap] at hs
        obtain ⟨u, hu, rfl⟩ := hs
        rw [hSmap]
        refine ⟨b * u * b⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
        exact (Subgroup.mem_normalizer_iff.mp hb u).mp hu
      · intro hs
        rw [hSmap] at hs ⊢
        obtain ⟨u', hu', hu's⟩ := hs
        refine ⟨b⁻¹ * u' * b, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer ((UU : Subgroup Pr) : Set Pr)).inv_mem hb) u').mp hu'
          simpa using this
        · rw [map_mul, map_mul, hu's, map_inv]
          group
  have hint' : ∀ (u : Pr) (v : V), e ((τ u) v) = act u (e v) := hτe
  have K4 : ∀ v : V, v ∈ fixSet S ↔ e v ∈ Fsp := by
    intro v
    constructor
    · intro hv u hu
      have h1 := hv (τ u) ((K1 u).mpr hu)
      have h2 := hτe u v
      rw [h1] at h2
      exact h2.symm
    · intro hy s hs
      have hsF : s ∈ F := hSF hs
      have h1 := hint ⟨s, hsF⟩ v
      have h2 := hy (θ ⟨s, hsF⟩) ((hS ⟨s, hsF⟩).mp hs)
      rw [h2] at h1
      exact e.injective h1
  have K5 : ∀ v : V, v ∈ oneSet S ↔ e v ∈ Vone := by
    intro v
    constructor
    · intro hv u hu
      have h1 := hv (τ u) ((K1 u).mpr hu)
      have h2 := (K4 _).mp h1
      rw [map_sub, hτe] at h2
      exact h2
    · intro hy s hs
      have hsF : s ∈ F := hSF hs
      have h1 := hy (θ ⟨s, hsF⟩) ((hS ⟨s, hsF⟩).mp hs)
      refine (K4 _).mpr ?_
      rw [map_sub]
      have h3 := hint ⟨s, hsF⟩ v
      rw [h3]
      exact h1
  have K3a : yOne F S = Y1.map τ := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgF, hgS, hfix⟩ := hg
      obtain ⟨b, hb, rfl⟩ : g ∈ BB.map τ := K2 ▸ ⟨hgF, hgS⟩
      refine ⟨b, (mem_Y1_iff_act hb).mpr fun y hy => ?_, rfl⟩
      obtain ⟨v, rfl⟩ := e.surjective y
      have h1 := hfix v ((K4 v).mpr hy)
      have h2 := hτe b v
      rw [h1] at h2
      exact h2.symm
    · rintro ⟨b, hb, rfl⟩
      have hbB : b ∈ BB := Y1_le_BB hb
      have hmem : τ b ∈ F ⊓ Subgroup.normalizer (S : Set (GLV V)) := K2 ▸ ⟨b, hbB, rfl⟩
      refine ⟨hmem.1, hmem.2, fun v hv => ?_⟩
      have h1 := (mem_Y1_iff_act hbB).mp hb _ ((K4 v).mp hv)
      have h2 := hτe b v
      rw [h1] at h2
      exact e.injective h2
  have K3b : yTwo F S = Y2.map τ := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgF, hgS, hfix⟩ := hg
      obtain ⟨b, hb, rfl⟩ : g ∈ BB.map τ := K2 ▸ ⟨hgF, hgS⟩
      refine ⟨b, (mem_Y2_iff_act hb).mpr fun X hX => ?_, rfl⟩
      obtain ⟨v, rfl⟩ := e.surjective X
      have h1 := (K4 _).mp (hfix v ((K5 v).mpr hX))
      rw [map_sub, hτe] at h1
      exact h1
    · rintro ⟨b, hb, rfl⟩
      have hbB : b ∈ BB := Y2_le_BB hb
      have hmem : τ b ∈ F ⊓ Subgroup.normalizer (S : Set (GLV V)) := K2 ▸ ⟨b, hbB, rfl⟩
      refine ⟨hmem.1, hmem.2, fun v hv => ?_⟩
      have h1 := (mem_Y2_iff_act hbB).mp hb _ ((K5 v).mp hv)
      refine (K4 _).mpr ?_
      rw [map_sub, hτe]
      exact h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [K3a, hSmap]
    exact Subgroup.map_mono UU_le_Y1
  · rw [K3b, hSmap]
    exact Subgroup.map_mono UU_le_Y2
  · rw [K3a]
    have := Subgroup.relIndex_map_map_of_injective UU Y1 hτinj
    rw [hSmap, this, relIndex_Y1]
  · rw [K3b]
    have := Subgroup.relIndex_map_map_of_injective UU Y2 hτinj
    rw [hSmap, this, relIndex_Y2]
  · rw [K2, K3a, K3b, ← Subgroup.map_sup]
    exact Subgroup.map_mono BB_le_sup

end Frame

end SzPS8

end CFSG.Quasithin
