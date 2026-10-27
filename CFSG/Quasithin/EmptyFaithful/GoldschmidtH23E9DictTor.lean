module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9DictRefl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModComm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModSub
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9Pre

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {T Mc M : Subgroup G} {hVe : IsElemAbelian 2 (V154 T Mc M)}
  {d : Six5Data T M (V154 T Mc M) hVe}

theorem exists_torus {x₁ x₂ : MulAut (IntMod (V154 T Mc M) hVe)} (r : ReflData T Mc M d x₁ x₂)
    (hE9 : HasE9 T Mc M) :
    ∃ ε₁ ε₂ : MulAut (IntMod (V154 T Mc M) hVe),
      (ε₁ ∈ SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂) ∧ orderOf ε₁ = 3 ∧
        (∀ w ∈ d.S.W₂, ε₁ w = w) ∧ ε₁ * d.S.a₁ = d.S.a₁ * ε₁ ∧
        (∀ w ∈ d.S.W₁, w ≠ 1 → ε₁ w ≠ w) ∧ d.S.Stab₁ ε₁ ∧ d.S.Stab₂ ε₁) ∧
      (ε₂ ∈ SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂) ∧ orderOf ε₂ = 3 ∧
        (∀ w ∈ d.S.W₁, ε₂ w = w) ∧ ε₂ * d.S.a₂ = d.S.a₂ * ε₂ ∧
        (∀ w ∈ d.S.W₂, w ≠ 1 → ε₂ w ≠ w) ∧ d.S.Stab₁ ε₂ ∧ d.S.Stab₂ ε₂) := by
  have hW : ∀ w : IntMod (V154 T Mc M) hVe, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hA0M : d.S.A₁ ⊔ d.S.A₂ ≤ autI hVe M := by
    rw [d.hsup]
    exact Jhat_le _
  have hτ : d.S.τ ∈ autI hVe M := autI_mono hVe d.hTM d.hτ
  have hE9' : ∃ E : Subgroup (MulAut (IntMod (V154 T Mc M) hVe)),
      E ≤ autI hVe M ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := hE9
  obtain ⟨ε₂, h1, h2, h3, h4, h5, h6, h7⟩ :=
    d.S.exists_eps_with_stab hW d.hcard d.hnorm hτ hE9'
  obtain ⟨ε₁, g1, g2, g3, g4, g5, g6, g7⟩ :=
    d.S.exists_eps₁_with_stab hW d.hcard d.hnorm hτ hE9'
  refine ⟨ε₁, ε₂, ⟨⟨g1, ?_⟩, g2, g3, g4, g5, g6, g7⟩, ⟨⟨h1, ?_⟩, h2, h3, h4, h5, h6, h7⟩⟩
  · have hc : ε₁ * x₁ = x₁ * ε₁ :=
      d.S.reflection_commute_eps₁ hW d.hcard d.hnorm hτ hA0M g1 g2 g3 g4 g5 r.x₁_mem.1 r.x₁_two
    exact SixData151b.iff_of_forall_mem'
      (d.S.maps_vEMod_of_comm₁ g3 (fun w hw => (g6 w).mp hw) hc)
  · have hc : ε₂ * x₂ = x₂ * ε₂ :=
      d.S.reflection_commute_eps hW d.hcard d.hnorm hτ hA0M h1 h2 h3 h4 h5 r.x₂_mem.1 r.x₂_two
    exact SixData151b.iff_of_forall_mem'
      (d.S.maps_vEMod_of_comm h3 (fun w hw => (h7 w).mp hw) hc)

theorem ReflData.tau_mem_stab {x₁ x₂ : MulAut (IntMod (V154 T Mc M) hVe)}
    (r : ReflData T Mc M d x₁ x₂) :
    d.S.τ ∈ SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂) ∧ d.S.Swap₁₂ d.S.τ ∧
      d.S.τ ∈ autI hVe T := by
  have hτM : d.S.τ ∈ autI hVe M := autI_mono hVe d.hTM d.hτ
  have hW : ∀ w : IntMod (V154 T Mc M) hVe, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  refine ⟨⟨hτM, ?_⟩, d.S.swap_of_conj hW (d.hnorm _ hτM) d.S.τ₁₂, d.hτ⟩
  have hfix : d.S.vEMod x₁ x₂ = fixV (autI hVe T ⊓ (d.S.A₁ ⊔ d.S.A₂)) := by
    rw [r.closure_eq]
    exact (d.S.fixV_closure_pair r.x₁_mem.1 r.x₂_mem.1).symm
  have hmap : ∀ w ∈ d.S.vEMod x₁ x₂, d.S.τ w ∈ d.S.vEMod x₁ x₂ := by
    intro w hw
    rw [hfix] at hw ⊢
    refine mem_fixV.mpr fun y hy => ?_
    have hy' : d.S.τ⁻¹ * y * d.S.τ ∈ autI hVe T ⊓ (d.S.A₁ ⊔ d.S.A₂) := by
      refine ⟨(autI hVe T).mul_mem ((autI hVe T).mul_mem ((autI hVe T).inv_mem d.hτ) hy.1) d.hτ, ?_⟩
      have := d.hnorm d.S.τ⁻¹ ((autI hVe M).inv_mem hτM) y hy.2
      simpa [mul_assoc] using this
    have h1 := mem_fixV.mp hw _ hy'
    calc y (d.S.τ w) = (y * d.S.τ) w := rfl
      _ = (d.S.τ * (d.S.τ⁻¹ * y * d.S.τ)) w := by group
      _ = d.S.τ ((d.S.τ⁻¹ * y * d.S.τ) w) := rfl
      _ = d.S.τ w := by rw [h1]
  exact SixData151b.iff_of_forall_mem' hmap

theorem ReflData.exists_lift {x₁ x₂ : MulAut (IntMod (V154 T Mc M) hVe)}
    (_r : ReflData T Mc M d x₁ x₂) {φ : MulAut (IntMod (V154 T Mc M) hVe)}
    (hφ : φ ∈ SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂)) :
    ∃ (γ : G) (hγ : γ ∈ Subgroup.normalizer (V154 T Mc M : Set G)), γ ∈ M ∧
      γ ∈ Subgroup.normalizer ((d.S.vEMod x₁ x₂).map (valHomI hVe) : Set G) ∧
      convI hVe ⟨γ, hγ⟩ = φ := by
  obtain ⟨⟨γ, hγN⟩, hγM, hγφ⟩ := (mem_autI hVe).1 hφ.1
  refine ⟨γ, hγN, hγM, mem_normalizer_map hγN ?_, hγφ⟩
  rw [hγφ]
  exact hφ.2

theorem mem_centralizer_map_iff {L : Subgroup (IntMod (V154 T Mc M) hVe)} {g : G}
    (hg : g ∈ Subgroup.normalizer (V154 T Mc M : Set G)) :
    g ∈ Subgroup.centralizer ((L.map (valHomI hVe) : Subgroup G) : Set G) ↔
      ∀ z ∈ L, convI hVe ⟨g, hg⟩ z = z := by
  constructor
  · intro h z hz
    apply IntMod.val_injective
    rw [← conj_val hg z]
    have := Subgroup.mem_centralizer_iff.mp h (IntMod.val z) (Subgroup.mem_map.2 ⟨z, hz, rfl⟩)
    show g * IntMod.val z * g⁻¹ = IntMod.val z
    rw [← this]
    group
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    have h2 := conj_val (hV := hVe) hg z
    rw [h z hz] at h2
    show IntMod.val z * g = g * IntMod.val z
    calc IntMod.val z * g = (g * IntMod.val z * g⁻¹) * g := by rw [h2]
      _ = g * IntMod.val z := by group

theorem autI_inf_centralizer_map {K : Subgroup G}
    (_hK : K ≤ Subgroup.normalizer (V154 T Mc M : Set G))
    (L : Subgroup (IntMod (V154 T Mc M) hVe)) :
    autI hVe (K ⊓ Subgroup.centralizer ((L.map (valHomI hVe) : Subgroup G) : Set G)) =
      SixData151b.ptFix (autI hVe K) L := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hVe).1 hφ
    refine ⟨(mem_autI hVe).2 ⟨g, hg.1, rfl⟩, fun z hz => ?_⟩
    exact (mem_centralizer_map_iff g.2).1 hg.2 z hz
  · rintro ⟨hφ, hfix⟩
    obtain ⟨g, hg, rfl⟩ := (mem_autI hVe).1 hφ
    exact (mem_autI hVe).2 ⟨g, ⟨hg, (mem_centralizer_map_iff g.2).2 hfix⟩, rfl⟩

end CFSG.Quasithin.E9
