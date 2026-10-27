module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULinDefs

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

theorem hdRo7SUReduceUAux_coord_ones' {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) (i : Fin m) :
    b.coord i (SUOnes p b) = 1 := by
  unfold SUOnes
  rw [map_sum]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  simp

theorem hdRo7SUReduceUAux_sum_ones {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} (b : Module.Basis (Fin m) (ZMod p) V) :
    (∑ i, b.coord i) (SUOnes p b) = (m : ZMod p) := by
  rw [LinearMap.sum_apply]
  simp_rw [hdRo7SUReduceUAux_coord_ones']
  simp

theorem hdRo7SUReduceUAux_ones_ne_zero {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} [NeZero m] (b : Module.Basis (Fin m) (ZMod p) V)
    (hm : (m : ZMod p) ≠ 0) : SUOnes p b ≠ 0 := by
  intro h
  have h1 := hdRo7SUReduceUAux_sum_ones b
  rw [h, map_zero] at h1
  exact hm h1.symm

theorem hdRo7SUReduceUAux_ones_notMem_aug {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0) :
    SUOnes p b ∉ SUAug p b := by
  intro hx
  have h1 := hdRo7SUReduceUAux_sum_ones b
  have h0 := LinearMap.mem_ker.mp hx
  rw [h1] at h0
  exact hm h0

theorem hdRo7SUReduceUAux_inf_span_ones_eq_bot {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0) :
    SUAug p b ⊓ Submodule.span (ZMod p) {SUOnes p b} = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_inf, Submodule.mem_span_singleton] at hw
  obtain ⟨hwU, c, rfl⟩ := hw
  have hc : c * (m : ZMod p) = 0 := by
    have h0 := LinearMap.mem_ker.mp hwU
    rw [map_smul, hdRo7SUReduceUAux_sum_ones b] at h0
    exact h0
  have hcz : c = 0 := (mul_eq_zero.mp hc).resolve_right hm
  rw [hcz, zero_smul]

theorem hdRo7SUReduceUAux_sup_span_ones_eq_top {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0) :
    SUAug p b ⊔ Submodule.span (ZMod p) {SUOnes p b} = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  have hmem : (v - ((∑ i, b.coord i) v / (m : ZMod p)) • SUOnes p b) ∈ SUAug p b := by
    change (∑ i, b.coord i) (v - ((∑ i, b.coord i) v / (m : ZMod p)) • SUOnes p b) = 0
    rw [map_sub, map_smul, hdRo7SUReduceUAux_sum_ones b]
    rw [smul_eq_mul, div_mul_cancel₀ _ hm]
    exact sub_self _
  refine Submodule.mem_sup.mpr ⟨_, hmem, ((∑ i, b.coord i) v / (m : ZMod p)) • SUOnes p b,
    Submodule.mem_span_singleton.mpr ⟨_, rfl⟩, ?_⟩
  abel

theorem hdRo7SUReduceUAux_finrank_aug {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} [NeZero m] (b : Module.Basis (Fin m) (ZMod p) V)
    (hm : (m : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) (SUAug p b) = m - 1 := by
  haveI : FiniteDimensional (ZMod p) V := Module.Finite.of_basis b
  have hsup := hdRo7SUReduceUAux_sup_span_ones_eq_top b hm
  have hinf := hdRo7SUReduceUAux_inf_span_ones_eq_bot b hm
  have hx0 := hdRo7SUReduceUAux_ones_ne_zero b hm
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq (SUAug p b)
    (Submodule.span (ZMod p) {SUOnes p b})
  rw [hsup, hinf, finrank_top, finrank_bot, finrank_span_singleton hx0] at hfin
  have hV : Module.finrank (ZMod p) V = m := by
    rw [Module.finrank_eq_card_basis b]; simp
  omega

@[expose] def hdRo7SUReduceUAux_kerAug (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (U : Submodule (ZMod p) V) : Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {g | ∀ v, g v - v ∈ U}
  mul_mem' := by
    intro g h hg hh v
    have h1 : g (h v) - h v ∈ U := hg (h v)
    have h2 : h v - v ∈ U := hh v
    have heq : (g * h) v - v = (g (h v) - h v) + (h v - v) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [heq]; exact U.add_mem h1 h2
  one_mem' := by
    intro v
    change (1 : V ≃ₗ[ZMod p] V) v - v ∈ U
    simp
  inv_mem' := by
    intro g hg v
    change g.symm v - v ∈ U
    have h1 : g (g.symm v) - g.symm v ∈ U := hg (g.symm v)
    have h1' : v - g.symm v ∈ U := by
      rwa [LinearEquiv.apply_symm_apply] at h1
    have heq : g.symm v - v = -(v - g.symm v) := by abel
    rw [heq]; exact U.neg_mem h1' 

theorem hdRo7SUReduceUAux_kerAug_map {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (U : Submodule (ZMod p) V) (g : V ≃ₗ[ZMod p] V)
    (hg : g ∈ hdRo7SUReduceUAux_kerAug p U) (u : V) (hu : u ∈ U) : g u ∈ U := by
  have h := hg u
  have heq : g u = u + (g u - u) := by abel
  rw [heq]; exact U.add_mem hu h

@[expose] noncomputable def hdRo7SUReduceUAux_restrict {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (U : Submodule (ZMod p) V) (g : V ≃ₗ[ZMod p] V)
    (hg : g ∈ hdRo7SUReduceUAux_kerAug p U) : U ≃ₗ[ZMod p] U :=
  LinearEquiv.ofLinearMap
    { toFun := fun u => ⟨g u, hdRo7SUReduceUAux_kerAug_map U g hg u u.2⟩
      map_add' := by intro a b; ext; simp [map_add]
      map_smul' := by intro c a; ext; simp [map_smul] }
    { toFun := fun u => ⟨g⁻¹ u,
        hdRo7SUReduceUAux_kerAug_map U g⁻¹ ((hdRo7SUReduceUAux_kerAug p U).inv_mem hg) u u.2⟩
      map_add' := by intro a b; ext; simp [map_add]
      map_smul' := by intro c a; ext; simp [map_smul] }
    (by ext u; simp) (by ext u; simp)

theorem hdRo7SUReduceUAux_restrict_apply {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (U : Submodule (ZMod p) V) (g : V ≃ₗ[ZMod p] V)
    (hg : g ∈ hdRo7SUReduceUAux_kerAug p U) (u : U) :
    ((hdRo7SUReduceUAux_restrict U g hg : U ≃ₗ[ZMod p] U) u : V) = g u := rfl

@[expose] noncomputable def hdRo7SUReduceUAux_res {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (U : Submodule (ZMod p) V) (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hHK : H ≤ hdRo7SUReduceUAux_kerAug p U) : ↥H →* (U ≃ₗ[ZMod p] U) where
  toFun g := hdRo7SUReduceUAux_restrict U g.1 (hHK g.2)
  map_one' := by
    ext u
    rfl
  map_mul' g h := by
    ext u
    rfl

theorem hdRo7SUReduceUAux_move_eq_span {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0)
    (g : V ≃ₗ[ZMod p] V) (hg : g ∈ hdRo7SUReduceUAux_kerAug p (SUAug p b))
    (hfix : ∀ u ∈ SUAug p b, g u = u) :
    ggLinMove g = Submodule.span (ZMod p) {g (SUOnes p b) - SUOnes p b} := by
  have hsup := hdRo7SUReduceUAux_sup_span_ones_eq_top b hm
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    change g v - v ∈ Submodule.span (ZMod p) {g (SUOnes p b) - SUOnes p b}
    have hv : v ∈ SUAug p b ⊔ Submodule.span (ZMod p) {SUOnes p b} := by rw [hsup]; trivial
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
    have hgu : g u - u = 0 := by rw [hfix u hu, sub_self]
    have hgw : g w - w = c • (g (SUOnes p b) - SUOnes p b) := by
      rw [← hc, map_smul, smul_sub]
    rw [show g v - v = (g u - u) + (g w - w) from by rw [← huw, map_add]; abel, hgu, hgw,
      zero_add]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · rw [Submodule.span_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨SUOnes p b, by
      change g (SUOnes p b) - SUOnes p b = g (SUOnes p b) - SUOnes p b
      rfl⟩

theorem hdRo7SUReduceUAux_eq_one_of_fixes {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0)
    (g : V ≃ₗ[ZMod p] V) (hfix : ∀ u ∈ SUAug p b, g u = u)
    (hgx : g (SUOnes p b) = SUOnes p b) : g = 1 := by
  have hsup := hdRo7SUReduceUAux_sup_span_ones_eq_top b hm
  ext v
  have hv : v ∈ SUAug p b ⊔ Submodule.span (ZMod p) {SUOnes p b} := by rw [hsup]; trivial
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  calc g v = g (u + w) := by rw [huw]
    _ = g u + g w := map_add g u w
    _ = u + c • g (SUOnes p b) := by rw [hfix u hu, ← hc, map_smul]
    _ = u + c • SUOnes p b := by rw [hgx]
    _ = u + w := by rw [hc]
    _ = v := huw

theorem hdRo7SUReduceUAux_transv_of_fixes {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0)
    (g : V ≃ₗ[ZMod p] V) (hg : g ∈ hdRo7SUReduceUAux_kerAug p (SUAug p b))
    (hfix : ∀ u ∈ SUAug p b, g u = u) (hne : g ≠ 1) : C2Transv p g := by
  have hspan := hdRo7SUReduceUAux_move_eq_span b hm g hg hfix
  have hu0 : g (SUOnes p b) - SUOnes p b ≠ 0 := by
    intro h0
    have hgx : g (SUOnes p b) = SUOnes p b := sub_eq_zero.mp h0
    exact hne (hdRo7SUReduceUAux_eq_one_of_fixes b hm g hfix hgx)
  refine ⟨?_, ?_⟩
  · rw [hspan, finrank_span_singleton hu0]
  · intro w
    have hw : g w - w ∈ SUAug p b := hg w
    rw [hfix (g w - w) hw]

theorem hdRo7SUReduceUAux_res_injective {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) (ZMod p) V) (hm : (m : ZMod p) ≠ 0)
    (H A : Subgroup (V ≃ₗ[ZMod p] V)) (hHK : H ≤ hdRo7SUReduceUAux_kerAug p (SUAug p b))
    (hHA : H ≤ A) (hNoT : ∀ a ∈ A, ¬ C2Transv p a) :
    Function.Injective (hdRo7SUReduceUAux_res (SUAug p b) H hHK) := by
  have key : ∀ g : ↥H, hdRo7SUReduceUAux_res (SUAug p b) H hHK g = 1 → g = 1 := by
    intro g hg
    by_contra hne
    have hg1 : (g : V ≃ₗ[ZMod p] V) ≠ 1 := fun h => hne (Subtype.ext h)
    have hfix : ∀ u ∈ SUAug p b, (g : V ≃ₗ[ZMod p] V) u = u := by
      intro u hu
      have happ := congrArg (fun (e : SUAug p b ≃ₗ[ZMod p] SUAug p b) => (e ⟨u, hu⟩ : V)) hg
      exact happ
    exact hNoT g.1 (hHA g.2) (hdRo7SUReduceUAux_transv_of_fixes b hm g.1 (hHK g.2) hfix hg1)
  intro g h hgh
  have h1 : g * h⁻¹ = 1 := by
    apply key
    rw [map_mul, map_inv, hgh, mul_inv_cancel]
  exact mul_inv_eq_one.mp h1

end CFSG.StandardType.HdRo7SU
