module

public import CFSG.Milestones.ASVolI.B4Ext.GL4

public section

namespace CFSG.ASVolI

open Module Submodule CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem burnsideB49x_gl5_range_comm {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (φ : E →* (V ≃ₗ[ZMod 2] V)) : ∀ g ∈ φ.range, ∀ g' ∈ φ.range, g * g' = g' * g := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext (hc a a.2 b b.2)]

theorem burnsideB49x_gl5_range_mul_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (h2 : ∀ e ∈ E, e * e = 1)
    (φ : E →* (V ≃ₗ[ZMod 2] V)) : ∀ g ∈ φ.range, g * g = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_mul, show a * a = 1 from Subtype.ext (h2 a a.2), map_one]

theorem burnsideB49x_gl5_card_ker_quotHom [FiniteDimensional (ZMod 2) W]
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) :
    Nat.card (burnsideB49x_gl_quotHom E).ker ≤
      2 ^ ((finrank (ZMod 2) W -
        finrank (ZMod 2) ↥(burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E)) *
          finrank (ZMod 2) (burnsideB49x_gl_fix E)) :=
  burnsideB49x_gl_card_le
    (fun k : (burnsideB49x_gl_quotHom E).ker => ((k : E) : W ≃ₗ[ZMod 2] W))
    (fun _ _ h => Subtype.ext (Subtype.ext h))
    (burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E) (burnsideB49x_gl_fix E)
    (fun k => burnsideB49x_gl_fix_sup_of_sub_mem_fix hc (k : E).2
      (burnsideB49x_gl_sub_mem_fix_of_mem_ker k.2))
    (fun k => burnsideB49x_gl_sub_mem_fix_of_mem_ker k.2)

theorem burnsideB49x_gl5_apply_mem_comm {E : Subgroup (W ≃ₗ[ZMod 2] W)} {e : W ≃ₗ[ZMod 2] W}
    (he : e ∈ E) {x : W} (hx : x ∈ burnsideB49x_gl_comm E) : e x ∈ burnsideB49x_gl_comm E := by
  simpa only [add_sub_cancel] using add_mem hx (burnsideB49x_gl_sub_mem_comm he x)

theorem burnsideB49x_gl5_map_comm {E : Subgroup (W ≃ₗ[ZMod 2] W)} {e : W ≃ₗ[ZMod 2] W}
    (he : e ∈ E) :
    (burnsideB49x_gl_comm E).map (e : W →ₗ[ZMod 2] W) = burnsideB49x_gl_comm E := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact burnsideB49x_gl5_apply_mem_comm he hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have h := burnsideB49x_gl5_apply_mem_comm (E.inv_mem he) hx
    rwa [LinearEquiv.coe_inv] at h

@[expose] def burnsideB49x_gl5_resHom (E : Subgroup (W ≃ₗ[ZMod 2] W)) :
    E →* (burnsideB49x_gl_comm E ≃ₗ[ZMod 2] burnsideB49x_gl_comm E) where
  toFun e := (e : W ≃ₗ[ZMod 2] W).ofSubmodules _ _ (burnsideB49x_gl5_map_comm e.2)
  map_one' := by
    ext x
    rfl
  map_mul' e e' := by
    ext x
    rfl

theorem burnsideB49x_gl5_fix_of_mem_ker_resHom {E : Subgroup (W ≃ₗ[ZMod 2] W)} {k : E}
    (hk : k ∈ (burnsideB49x_gl5_resHom E).ker) {x : W} (hx : x ∈ burnsideB49x_gl_comm E) :
    (k : W ≃ₗ[ZMod 2] W) x = x :=
  congrArg (fun φ : burnsideB49x_gl_comm E ≃ₗ[ZMod 2] burnsideB49x_gl_comm E =>
    ((φ ⟨x, hx⟩ : burnsideB49x_gl_comm E) : W)) (MonoidHom.mem_ker.1 hk)

theorem burnsideB49x_gl5_sub_mem_fix_of_fix_comm {E : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) {f : W ≃ₗ[ZMod 2] W} (hfE : f ∈ E)
    (hf : ∀ x ∈ burnsideB49x_gl_comm E, f x = x) (x : W) : f x - x ∈ burnsideB49x_gl_fix E := by
  intro e he
  have h := hf _ (burnsideB49x_gl_sub_mem_comm he x)
  rw [map_sub] at h ⊢
  rw [burnsideB49x_gl_apply_comm (hc e he f hfE)]
  calc f (e x) - e x = (f (e x) - f x) + f x - e x := by abel
    _ = (e x - x) + f x - e x := by rw [h]
    _ = f x - x := by abel

theorem burnsideB49x_gl5_card_ker_resHom [FiniteDimensional (ZMod 2) W]
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) :
    Nat.card (burnsideB49x_gl5_resHom E).ker ≤
      2 ^ ((finrank (ZMod 2) W - finrank (ZMod 2) (burnsideB49x_gl_comm E)) *
        finrank (ZMod 2) (burnsideB49x_gl_fix E)) :=
  burnsideB49x_gl_card_le
    (fun k : (burnsideB49x_gl5_resHom E).ker => ((k : E) : W ≃ₗ[ZMod 2] W))
    (fun _ _ h => Subtype.ext (Subtype.ext h))
    (burnsideB49x_gl_comm E) (burnsideB49x_gl_fix E)
    (fun k _ hx => burnsideB49x_gl5_fix_of_mem_ker_resHom k.2 hx)
    (fun k => burnsideB49x_gl5_sub_mem_fix_of_fix_comm hc (k : E).2
      fun _ hx => burnsideB49x_gl5_fix_of_mem_ker_resHom k.2 hx)

theorem burnsideB49x_gl5_quad_of_fix_le_comm [FiniteDimensional (ZMod 2) W]
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (h2 : ∀ e ∈ E, e * e = 1) (hle : burnsideB49x_gl_fix E ≤ burnsideB49x_gl_comm E)
    (hdim : finrank (ZMod 2) (burnsideB49x_gl_comm E) ≤
      finrank (ZMod 2) (burnsideB49x_gl_fix E) + 1) :
    burnsideB49x_gl_comm E ≤ burnsideB49x_gl_fix E := by
  rw [burnsideB49x_gl_comm, Submodule.span_le]
  rintro _ ⟨e, he, x, rfl⟩
  by_contra hy
  change e x - x ∉ burnsideB49x_gl_fix E at hy
  have hey : e (e x - x) = e x - x := burnsideB49x_gl_apply_sub (h2 e he) x
  have hyH : e x - x ∈ burnsideB49x_gl_comm E := burnsideB49x_gl_sub_mem_comm he x
  set y := e x - x with hy_def
  set D := burnsideB49x_gl_fix E ⊔ (ZMod 2) ∙ y with hD_def
  have hD : finrank (ZMod 2) (burnsideB49x_gl_fix E) < finrank (ZMod 2) D :=
    burnsideB49x_gl_finrank_lt le_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)) hy
  have hDH : D = burnsideB49x_gl_comm E :=
    Submodule.eq_of_le_of_finrank_le
      (sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).2 hyH) :
        D ≤ burnsideB49x_gl_comm E) (by omega)
  have hfix : ∀ z ∈ burnsideB49x_gl_comm E, e z = z := by
    intro z hz
    rw [← hDH] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [map_add, map_smul, ha e he, hey]
  exact hy (burnsideB49x_gl5_sub_mem_fix_of_fix_comm hc he hfix x)

theorem burnsideB49x_gl5_quad [FiniteDimensional (ZMod 2) W]
    (hW : Module.finrank (ZMod 2) W = 5) {E : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (h2 : ∀ e ∈ E, e * e = 1)
    (hE : 64 ≤ Nat.card E) : burnsideB49x_gl_comm E ≤ burnsideB49x_gl_fix E := by
  have hc1 := burnsideB49x_gl_one_le_finrank_fix (by omega) h2
  by_cases hc3 : 3 ≤ finrank (ZMod 2) (burnsideB49x_gl_fix E)
  · exact burnsideB49x_gl_quad_of_codim hc h2 (by omega)
  by_cases hb2 : finrank (ZMod 2) (burnsideB49x_gl_comm E) ≤ 2
  · exact burnsideB49x_gl_quad_of_comm_le hc h2 hb2
  have hQ := Submodule.finrank_quotient_add_finrank (burnsideB49x_gl_fix E)
  have hd := Submodule.finrank_mono
    (le_sup_left : burnsideB49x_gl_comm E ≤ burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E)
  have hker := burnsideB49x_gl5_card_ker_quotHom hc
  rw [hW] at hQ hker
  by_cases hd4 : 4 ≤ finrank (ZMod 2) ↥(burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E)
  ·
    exfalso
    obtain h1 | h1 : finrank (ZMod 2) (burnsideB49x_gl_fix E) = 1 ∨
        finrank (ZMod 2) (burnsideB49x_gl_fix E) = 2 := by omega
    · have hQ4 : finrank (ZMod 2) (W ⧸ burnsideB49x_gl_fix E) = 4 := by omega
      have hr := burnsideB49x_gl_four_card_le hQ4
        (burnsideB49x_gl5_range_comm hc (burnsideB49x_gl_quotHom E))
        (burnsideB49x_gl5_range_mul_self h2 (burnsideB49x_gl_quotHom E))
      rw [h1] at hker
      have hk : Nat.card (burnsideB49x_gl_quotHom E).ker ≤ 2 :=
        calc Nat.card (burnsideB49x_gl_quotHom E).ker
            ≤ 2 ^ ((5 - finrank (ZMod 2) ↥(burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E)) *
              1) := hker
          _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
      have h := Nat.mul_le_mul hk hr
      rw [Subgroup.card_ker_mul_card_range] at h
      omega
    · have hQ3 : finrank (ZMod 2) (W ⧸ burnsideB49x_gl_fix E) = 3 := by omega
      have hr := burnsideB49x_gl_three hQ3
        (burnsideB49x_gl5_range_comm hc (burnsideB49x_gl_quotHom E))
        (burnsideB49x_gl5_range_mul_self h2 (burnsideB49x_gl_quotHom E))
      rw [h1] at hker
      have hk : Nat.card (burnsideB49x_gl_quotHom E).ker ≤ 4 :=
        calc Nat.card (burnsideB49x_gl_quotHom E).ker
            ≤ 2 ^ ((5 - finrank (ZMod 2) ↥(burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E)) *
              2) := hker
          _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 4 := by norm_num
      have h := Nat.mul_le_mul hk hr
      rw [Subgroup.card_ker_mul_card_range] at h
      omega
  have hb3 : finrank (ZMod 2) (burnsideB49x_gl_comm E) = 3 := by omega
  have hCH : burnsideB49x_gl_fix E ≤ burnsideB49x_gl_comm E := by
    have h := Submodule.eq_of_le_of_finrank_le
      (le_sup_left : burnsideB49x_gl_comm E ≤ burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E)
      (by omega)
    exact le_sup_right.trans h.ge
  obtain h1 | h1 : finrank (ZMod 2) (burnsideB49x_gl_fix E) = 1 ∨
      finrank (ZMod 2) (burnsideB49x_gl_fix E) = 2 := by omega
  ·
    exfalso
    have hk := burnsideB49x_gl5_card_ker_resHom hc
    rw [hW, hb3, h1] at hk
    have hk' : Nat.card (burnsideB49x_gl5_resHom E).ker ≤ 4 := hk.trans (by norm_num)
    have hr := burnsideB49x_gl_three hb3
      (burnsideB49x_gl5_range_comm hc (burnsideB49x_gl5_resHom E))
      (burnsideB49x_gl5_range_mul_self h2 (burnsideB49x_gl5_resHom E))
    have h := Nat.mul_le_mul hk' hr
    rw [Subgroup.card_ker_mul_card_range] at h
    omega
  ·
    exact burnsideB49x_gl5_quad_of_fix_le_comm hc h2 hCH (by omega)

end CFSG.ASVolI
