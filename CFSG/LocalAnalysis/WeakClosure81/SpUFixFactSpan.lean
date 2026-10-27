module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

namespace SpUFixGeom

variable {L : Type} [Group L] {R : Subgroup L} {F V : Type} [Field F] [AddCommGroup V]
  [Module F V]

theorem form_eq_zero_of_le (G : SpUFixGeom L R F V) {Sy : Subgroup L} (hSy2 : IsPGroup 2 Sy)
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) (hvv : G.β v v = 0) (hww : G.β w w = 0)
    (hvS : G.X v ≤ Sy) (hwS : G.X w ≤ Sy) : G.β v w = 0 := by
  by_contra h
  obtain ⟨x, hx, y, hy, h3, hne⟩ := G.X_order_three v w hv hw hvv hww h
  have hxy : x * y ∈ Sy := mul_mem (hvS hx) (hwS hy)
  obtain ⟨k, hk⟩ := hSy2 ⟨x * y, hxy⟩
  have hk' : (x * y) ^ (2 ^ k) = 1 := by
    have := congrArg (fun z : Sy => (z : L)) hk
    simpa using this
  have hcop : Nat.Coprime (2 ^ k) 3 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0]; simp
    · exact (Nat.coprime_pow_left_iff hkpos 2 3).mpr (by decide)
  have hg : (x * y) ^ ((2 ^ k).gcd 3) = 1 := pow_gcd_eq_one.mpr ⟨hk', h3⟩
  rw [hcop.gcd_eq_one, pow_one] at hg
  exact hne hg

theorem form_eq_zero_of_mem_rootSpan (G : SpUFixGeom L R F V) {Sy : Subgroup L}
    (hSy2 : IsPGroup 2 Sy) {s t : V} (hs : s ∈ G.rootSpan Sy) (ht : t ∈ G.rootSpan Sy) :
    G.β s t = 0 := by
  have key : ∀ s ∈ G.rootSpan Sy, ∀ t ∈ G.rootSpan Sy, G.β s t = 0 := by
    intro s hs
    refine Submodule.span_induction
      (p := fun s _ => ∀ t ∈ G.rootSpan Sy, G.β s t = 0) ?_ ?_ ?_ ?_ hs
    · intro v hv t ht
      refine Submodule.span_induction (p := fun t _ => G.β v t = 0) ?_ ?_ ?_ ?_ ht
      · intro w hw
        exact G.form_eq_zero_of_le hSy2 hv.1 hw.1 hv.2.1 hw.2.1 hv.2.2 hw.2.2
      · simpa using G.β_smul_right 0 v 0
      · intro x y _ _ hx hy
        rw [G.β_add_right, hx, hy, add_zero]
      · intro c x _ hx
        rw [G.β_smul_right, hx, mul_zero]
    · intro t _
      simpa using G.β_smul_left 0 0 t
    · intro x y _ _ hx hy t ht
      rw [G.β_add_left, hx t ht, hy t ht, add_zero]
    · intro c x _ hx t ht
      rw [G.β_smul_left, hx t ht, mul_zero]
  exact key s hs t ht

theorem mem_rootSpan_of_conj (G : SpUFixGeom L R F V) {Sy : Subgroup L} {y : L} (hy : y ∈ Sy)
    {M : V →ₗ[F] V} (hMi : Function.Injective M) (hMβ : ∀ v w, G.β (M v) (M w) = G.β v w)
    (hMX : ∀ v, G.β v v = 0 → (G.X v).map (MulAut.conj y).toMonoidHom = G.X (M v)) {s : V}
    (hs : s ∈ G.rootSpan Sy) : M s ∈ G.rootSpan Sy := by
  refine Submodule.span_induction (p := fun s _ => M s ∈ G.rootSpan Sy) ?_ ?_ ?_ ?_ hs
  · intro v hv
    refine Submodule.subset_span ⟨?_, ?_, ?_⟩
    · intro h
      exact hv.1 (hMi (by rw [h, map_zero]))
    · rw [hMβ v v, hv.2.1]
    · rw [← hMX v hv.2.1]
      rintro z hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      have hnorm := (Subgroup.mem_normalizer_iff.mp (Sy.le_normalizer hy)) w
      simpa [MulAut.conj_apply] using hnorm.mp (hv.2.2 hw)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

theorem mem_rootSpan_of_aut (G : SpUFixGeom L R F V) {Sy : Subgroup L} (α : MulAut L)
    (hαSy : Sy.map α.toMonoidHom = Sy) {σ : F ≃+* F} (ψ : V →+ V)
    (hψ : ∀ (c : F) (v : V), ψ (c • v) = σ c • ψ v) (hψinj : Function.Injective ψ)
    (hψβ : ∀ v w, G.β v w = 0 → G.β (ψ v) (ψ w) = 0)
    (hψX : ∀ v, G.β v v = 0 → (G.X v).map α.toMonoidHom = G.X (ψ v)) {s : V}
    (hs : s ∈ G.rootSpan Sy) :
    ψ s ∈ G.rootSpan Sy := by
  refine Submodule.span_induction (p := fun s _ => ψ s ∈ G.rootSpan Sy) ?_ ?_ ?_ ?_ hs
  · intro v hv
    refine Submodule.subset_span ⟨?_, ?_, ?_⟩
    · intro h
      exact hv.1 (hψinj (by rw [h, map_zero]))
    · exact hψβ v v hv.2.1
    · rw [← hψX v hv.2.1]
      exact (Subgroup.map_mono hv.2.2).trans_eq hαSy
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [hψ c x]
    exact Submodule.smul_mem _ _ hx

end SpUFixGeom

end CFSG.LocalAnalysis.WeakClosure81

end
