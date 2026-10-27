module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection

public section

namespace CFSG.Quasithin.G31

open Module CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

structure Hyp (G : Subgroup (W ≃ₗ[ZMod 2] W)) (Δ : Set W)
    (F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)) : Prop where
  ne_zero : ∀ x ∈ Δ, x ≠ 0
  apply_self : ∀ x ∈ Δ, ∀ φ ∈ F x, φ x = 0
  mem : ∀ x ∈ Δ, ∀ φ ∈ F x, ∀ h : φ x = 0, LinearEquiv.transvection h ∈ G
  map_mem : ∀ g ∈ G, ∀ x ∈ Δ, g x ∈ Δ
  mem_F_map : ∀ g ∈ G, ∀ x ∈ Δ, ∀ φ : Dual (ZMod 2) W,
    φ ∈ F (g x) ↔ φ ∘ₗ (g : W →ₗ[ZMod 2] W) ∈ F x
  trans : ∀ x ∈ Δ, ∀ y ∈ Δ, ∃ g ∈ G, g x = y

abbrev C (F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)) (x : W) : Submodule (ZMod 2) W :=
  (F x).dualCoannihilator

@[expose] def gens (Δ : Set W) (F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)) :
    Set (W ≃ₗ[ZMod 2] W) :=
  {t | ∃ x ∈ Δ, ∃ φ ∈ F x, ∃ h : φ x = 0, t = LinearEquiv.transvection h}

theorem mem_C {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)} {x w : W} :
    w ∈ C F x ↔ ∀ φ ∈ F x, φ w = 0 :=
  Submodule.mem_dualCoannihilator w

theorem exists_eq_one_of_not_mem_C {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)} {x w : W}
    (h : w ∉ C F x) : ∃ φ ∈ F x, φ w = 1 := by
  rw [mem_C] at h
  push Not at h
  obtain ⟨φ, hφ, hw⟩ := h
  exact ⟨φ, hφ, zmod_two_eq_one_of_ne_zero hw⟩

namespace Hyp

variable {G : Subgroup (W ≃ₗ[ZMod 2] W)} {Δ : Set W}
  {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)}

theorem self_mem_C (hH : Hyp G Δ F) {x : W} (hx : x ∈ Δ) : x ∈ C F x :=
  mem_C.2 fun φ hφ => hH.apply_self x hx φ hφ

theorem F_map (hH : Hyp G Δ F) {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ G) {x : W} (hx : x ∈ Δ) :
    F (g x) = (F x).comap (g.dualMap : Dual (ZMod 2) W →ₗ[ZMod 2] Dual (ZMod 2) W) := by
  ext φ
  rw [hH.mem_F_map g hg x hx, Submodule.mem_comap]
  rfl

theorem mem_C_map (hH : Hyp G Δ F) {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ G) {x : W} (hx : x ∈ Δ)
    (w : W) : w ∈ C F (g x) ↔ g.symm w ∈ C F x := by
  rw [mem_C, mem_C]
  constructor
  · intro h ψ hψ
    have hψ' : ψ ∘ₗ (g.symm : W →ₗ[ZMod 2] W) ∈ F (g x) := by
      rw [hH.mem_F_map g hg x hx]
      convert hψ using 1
      ext v
      simp
    simpa using h _ hψ'
  · intro h φ hφ
    have := h _ ((hH.mem_F_map g hg x hx φ).1 hφ)
    simpa using this

theorem C_map (hH : Hyp G Δ F) {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ G) {x : W} (hx : x ∈ Δ) :
    C F (g x) = (C F x).map (g : W →ₗ[ZMod 2] W) := by
  ext w
  rw [hH.mem_C_map hg hx, Submodule.mem_map]
  constructor
  · intro h
    exact ⟨g.symm w, h, by simp⟩
  · rintro ⟨v, hv, rfl⟩
    simpa using hv

theorem finrank_F (hH : Hyp G Δ F) {x y : W} (hx : x ∈ Δ) (hy : y ∈ Δ) :
    finrank (ZMod 2) (F x) = finrank (ZMod 2) (F y) := by
  obtain ⟨g, hg, rfl⟩ := hH.trans x hx y hy
  rw [hH.F_map hg hx, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

theorem finrank_C (hH : Hyp G Δ F) {x y : W} (hx : x ∈ Δ) (hy : y ∈ Δ) :
    finrank (ZMod 2) (C F x) = finrank (ZMod 2) (C F y) := by
  obtain ⟨g, hg, rfl⟩ := hH.trans x hx y hy
  rw [hH.C_map hg hx]
  exact (LinearEquiv.finrank_map_eq g _).symm

variable [Finite W]

theorem mem_C_comm (hH : Hyp G Δ F) {x y : W} (hx : x ∈ Δ) (hy : y ∈ Δ) (h : x ∈ C F y) :
    y ∈ C F x := by
  by_contra hyx
  obtain ⟨φ, hφ, hφy⟩ := exists_eq_one_of_not_mem_C hyx
  have hle : F y ≤ F x := by
    intro ψ hψ
    have hψy : ψ y = 0 := hH.apply_self y hy ψ hψ
    have htx : LinearEquiv.transvection hψy x = x := by
      rw [transvection_apply, mem_C.1 h ψ hψ, zero_smul, add_zero]
    have h1 := (hH.mem_F_map _ (hH.mem y hy ψ hψ hψy) x hx φ).1 (by rw [htx]; exact hφ)
    have h2 : φ ∘ₗ (LinearEquiv.transvection hψy : W →ₗ[ZMod 2] W) = φ + ψ := by
      ext w
      show φ (LinearEquiv.transvection hψy w) = φ w + ψ w
      rw [transvection_apply, map_add, map_smul, hφy, smul_eq_mul, mul_one]
    rw [h2] at h1
    simpa using (F x).sub_mem h1 hφ
  have heq : F y = F x := Submodule.eq_of_le_of_finrank_eq hle (hH.finrank_F hy hx)
  have hφy' : φ y = 0 := hH.apply_self y hy φ (heq ▸ hφ)
  rw [hφy] at hφy'
  exact one_ne_zero hφy'

theorem not_mem_C_comm (hH : Hyp G Δ F) {x y : W} (hx : x ∈ Δ) (hy : y ∈ Δ) (h : y ∉ C F x) :
    x ∉ C F y :=
  fun h' => h (hH.mem_C_comm hx hy h')

theorem add_mem (hH : Hyp G Δ F) {x y : W} (hx : x ∈ Δ) (hy : y ∈ Δ) (hyx : y ∉ C F x) :
    x + y ∈ Δ := by
  obtain ⟨ψ, hψ, hψx⟩ := exists_eq_one_of_not_mem_C (hH.not_mem_C_comm hx hy hyx)
  have hψy : ψ y = 0 := hH.apply_self y hy ψ hψ
  have := hH.map_mem _ (hH.mem y hy ψ hψ hψy) x hx
  rwa [transvection_apply, hψx, one_smul] at this

theorem not_mem_C_add (hH : Hyp G Δ F) {x y : W} (hx : x ∈ Δ) (hy : y ∈ Δ)
    (hyx : y ∉ C F x) : x ∉ C F (x + y) := by
  obtain ⟨φ, hφ, hφy⟩ := exists_eq_one_of_not_mem_C hyx
  obtain ⟨ψ, hψ, hψx⟩ := exists_eq_one_of_not_mem_C (hH.not_mem_C_comm hx hy hyx)
  have hψy : ψ y = 0 := hH.apply_self y hy ψ hψ
  have ht : LinearEquiv.transvection hψy ∈ G := hH.mem y hy ψ hψ hψy
  have htx : LinearEquiv.transvection hψy x = x + y := by
    rw [transvection_apply, hψx, one_smul]
  have hmem : φ ∘ₗ (LinearEquiv.transvection hψy : W →ₗ[ZMod 2] W) ∈ F (x + y) := by
    rw [← htx, hH.mem_F_map _ ht x hx]
    convert hφ using 1
    ext w
    show φ (LinearEquiv.transvection hψy (LinearEquiv.transvection hψy w)) = φ w
    rw [← LinearEquiv.mul_apply, transvection_mul_self]
    rfl
  intro hmemC
  have h1 := mem_C.1 hmemC _ hmem
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, htx, map_add, hH.apply_self x hx φ hφ, hφy,
    zero_add] at h1
  exact one_ne_zero h1

theorem inf_le_C_add (hH : Hyp G Δ F) {x y : W} (hx : x ∈ Δ) (hy : y ∈ Δ)
    (hyx : y ∉ C F x) : C F x ⊓ C F y ≤ C F (x + y) := by
  obtain ⟨ψ, hψ, hψx⟩ := exists_eq_one_of_not_mem_C (hH.not_mem_C_comm hx hy hyx)
  have hψy : ψ y = 0 := hH.apply_self y hy ψ hψ
  have ht : LinearEquiv.transvection hψy ∈ G := hH.mem y hy ψ hψ hψy
  have htx : LinearEquiv.transvection hψy x = x + y := by
    rw [transvection_apply, hψx, one_smul]
  rintro w ⟨hwx, hwy⟩
  rw [← htx, hH.mem_C_map ht hx]
  show (LinearEquiv.transvection hψy)⁻¹ w ∈ C F x
  rw [transvection_inv, transvection_apply, mem_C.1 hwy ψ hψ, zero_smul, add_zero]
  exact hwx

theorem mem_F_of_mem_F (hH : Hyp G Δ F) {x y : W} (hx : x ∈ Δ) (hy : y ∈ Δ)
    (hyx : y ∉ C F x) {ψ' : Dual (ZMod 2) W} (hψ' : ψ' ∈ F y) (hψ'x : ψ' x = 0) :
    ψ' ∈ F x := by
  obtain ⟨φ, hφ, hφy⟩ := exists_eq_one_of_not_mem_C hyx
  obtain ⟨ψ, hψ, hψx⟩ := exists_eq_one_of_not_mem_C (hH.not_mem_C_comm hx hy hyx)
  have hφx : φ x = 0 := hH.apply_self x hx φ hφ
  have hψy : ψ y = 0 := hH.apply_self y hy ψ hψ
  have ht' : LinearEquiv.transvection hφx ∈ G := hH.mem x hx φ hφ hφx
  have ht'y : LinearEquiv.transvection hφx y = x + y := by
    rw [transvection_apply, hφy, one_smul, add_comm]
  have h1 : ψ' ∈ F (x + y) := by
    rw [← ht'y, hH.mem_F_map _ ht' y hy]
    convert hψ' using 1
    ext w
    show ψ' (LinearEquiv.transvection hφx w) = ψ' w
    rw [transvection_apply, map_add, map_smul, hψ'x, smul_zero, add_zero]
  have ht : LinearEquiv.transvection hψy ∈ G := hH.mem y hy ψ hψ hψy
  have htxy : LinearEquiv.transvection hψy (x + y) = x := by
    rw [transvection_apply, map_add, hψx, hψy, add_zero, one_smul, add_assoc, two_add_self,
      add_zero]
  rw [← htxy, hH.mem_F_map _ ht _ (hH.add_mem hx hy hyx)]
  convert h1 using 1
  ext w
  show ψ' (LinearEquiv.transvection hψy w) = ψ' w
  rw [transvection_apply, map_add, map_smul, hH.apply_self y hy ψ' hψ', smul_zero, add_zero]

theorem C_le_sup (hH : Hyp G Δ F) {x y : W} (hx : x ∈ Δ) (hy : y ∈ Δ) (hyx : y ∉ C F x) :
    C F x ≤ Submodule.span (ZMod 2) {x} ⊔ (C F x ⊓ C F y) := by
  obtain ⟨ψ, hψ, hψx⟩ := exists_eq_one_of_not_mem_C (hH.not_mem_C_comm hx hy hyx)
  intro w hw
  have key : ∀ ψ' ∈ F y, ψ' w = ψ' x * ψ w := by
    intro ψ' hψ'
    have hmem : ψ' + ψ' x • ψ ∈ F y := (F y).add_mem hψ' ((F y).smul_mem _ hψ)
    have h0 : (ψ' + ψ' x • ψ) x = 0 := by
      rw [LinearMap.add_apply, LinearMap.smul_apply, hψx, smul_eq_mul, mul_one,
        zmod_two_add_self]
    have h1 := mem_C.1 hw _ (hH.mem_F_of_mem_F hx hy hyx hmem h0)
    rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 := eq_neg_of_add_eq_zero_left h1
    rwa [ZMod.neg_eq_self_mod_two] at h2
  rcases zmod_two_eq_zero_or_one (ψ w) with h0 | h1
  · refine Submodule.mem_sup_right ⟨hw, mem_C.2 fun ψ' hψ' => ?_⟩
    rw [key ψ' hψ', h0, mul_zero]
  · have hwx : w + x ∈ C F x ⊓ C F y := ⟨(C F x).add_mem hw (hH.self_mem_C hx),
      mem_C.2 fun ψ' hψ' => by rw [map_add, key ψ' hψ', h1, mul_one, zmod_two_add_self]⟩
    have hw' : w = x + (w + x) := by rw [add_comm w x, ← add_assoc, two_add_self, zero_add]
    rw [hw']
    exact Submodule.add_mem_sup (Submodule.mem_span_singleton_self x) hwx

theorem forall_mem_of_closed (hH : Hyp G Δ F) (hgen : G ≤ Subgroup.closure (gens Δ F))
    {S : Set W} (hS : S ⊆ Δ) (hne : S.Nonempty)
    (hcl : ∀ u ∈ S, ∀ v ∈ Δ, v ∉ C F u → v ∈ S) {v : W} (hv : v ∈ Δ) : v ∈ S := by
  have hgen_mem : ∀ t ∈ gens Δ F, ∀ u ∈ S, t u ∈ S := by
    rintro t ⟨x, hx, φ, hφ, h, rfl⟩ u hu
    rw [transvection_apply]
    rcases zmod_two_eq_zero_or_one (φ u) with h0 | h1
    · rw [h0, zero_smul, add_zero]
      exact hu
    · rw [h1, one_smul]
      have huΔ := hS hu
      have hux : u ∉ C F x := fun hm => by
        rw [mem_C.1 hm φ hφ] at h1
        exact zero_ne_one h1
      have hxS : x ∈ S := hcl u hu x hx (hH.not_mem_C_comm hx huΔ hux)
      have hadd : x + u ∈ Δ := hH.add_mem hx huΔ hux
      rw [add_comm]
      exact hcl x hxS (x + u) hadd (hH.not_mem_C_comm hadd hx (hH.not_mem_C_add hx huΔ hux))
  have hG : ∀ g ∈ Subgroup.closure (gens Δ F), (∀ u ∈ S, g u ∈ S) ∧ ∀ u ∈ S, g⁻¹ u ∈ S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem t ht =>
      refine ⟨hgen_mem t ht, ?_⟩
      obtain ⟨x, hx, φ, hφ, h, rfl⟩ := ht
      rw [transvection_inv]
      exact hgen_mem _ ⟨x, hx, φ, hφ, h, rfl⟩
    | one => exact ⟨fun u hu => hu, fun u hu => by simpa using hu⟩
    | mul a b _ _ ha hb =>
      exact ⟨fun u hu => ha.1 _ (hb.1 u hu), fun u hu => by
        rw [mul_inv_rev, LinearEquiv.mul_apply]
        exact hb.2 _ (ha.2 u hu)⟩
    | inv a _ ha => exact ⟨ha.2, fun u hu => by rw [inv_inv]; exact ha.1 u hu⟩
  obtain ⟨u, hu⟩ := hne
  obtain ⟨g, hg, rfl⟩ := hH.trans u (hS hu) v hv
  exact (hG g (hgen hg)).1 u hu

end Hyp

end CFSG.Quasithin.G31
