module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigMonoTrans
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreRescale
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CorePerms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2s08am_coord_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) (i : Fin N) : b.coord i (b i) = 1 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

private lemma ggQ2s08am_coord_of_ne {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) {i j : Fin N} (h : i ≠ j) : b.coord i (b j) = 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  exact Finsupp.single_eq_of_ne h

private lemma ggQ2s08am_coord_mono {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) {w : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin N)}
    {ε : Fin N → ZMod 3} (hw : ∀ i, w (b i) = ε i • b (σ i)) (v : V) (i : Fin N) :
    b.coord (σ i) (w v) = ε i * b.coord i v := by
  have hmap : (b.coord (σ i)).comp w.toLinearMap = ε i • b.coord i := by
    apply Module.Basis.ext b
    intro j
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_toLinearMap, hw j,
      map_smul, smul_eq_mul]
    by_cases hji : j = i
    · subst hji
      rw [ggQ2s08am_coord_self, ggQ2s08am_coord_self]
      ring
    · have hσ : σ j ≠ σ i := fun h => hji (σ.injective h)
      rw [ggQ2s08am_coord_of_ne b (Ne.symm hσ), ggQ2s08am_coord_of_ne b (Ne.symm hji)]
      ring
  exact congrArg (fun f : V →ₗ[ZMod 3] ZMod 3 => f v) hmap

private lemma ggQ2s08am_repr_mono {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) {w : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin N)}
    {ε : Fin N → ZMod 3} (hw : ∀ i, w (b i) = ε i • b (σ i)) (v : V) (i : Fin N) :
    b.repr (w v) (σ i) = ε i * b.repr v i := by
  have h := ggQ2s08am_coord_mono b hw v i
  simpa only [Module.Basis.coord_apply] using h

private lemma ggQ2s08am_all_ne {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) {W : Subgroup (V ≃ₗ[ZMod 3] V)} {xv : V}
    (hWm : ∀ w ∈ W, GGQ2S08Mono b w) (hx : xv ≠ 0) (hfix : ∀ w ∈ W, w xv = xv)
    (htrans : ∀ i j, ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b j) :
    ∀ j, b.repr xv j ≠ 0 := by
  classical
  have hex : ∃ i, b.repr xv i ≠ 0 := by
    by_contra h
    apply hx
    rw [← b.sum_repr xv]
    apply Finset.sum_eq_zero
    intro i _
    have hi : b.repr xv i = 0 := by
      by_contra hi
      exact h ⟨i, hi⟩
    rw [hi, zero_smul]
  obtain ⟨i₀, hi₀⟩ := hex
  intro j
  obtain ⟨w, hw, ε, hε, hwj⟩ := htrans i₀ j
  obtain ⟨σ, δ, hδ, hwσ⟩ := hWm w hw
  have hσ : σ i₀ = j := by
    refine b.linearIndependent.eq_of_smul_apply_eq_smul_apply (δ i₀) ε (σ i₀) j (hδ i₀) ?_
    rw [← hwσ i₀, hwj]
  have hσsymm : σ.symm j = i₀ := by
    rw [← hσ]
    exact σ.symm_apply_apply i₀
  have hδε : δ i₀ = ε := by
    have h : δ i₀ • b j = ε • b j := by
      calc δ i₀ • b j = w (b i₀) := by rw [hwσ i₀, hσ]
        _ = ε • b j := hwj
    have h1 : b.repr (δ i₀ • b j) j = δ i₀ := by
      rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    have h2 : b.repr (ε • b j) j = ε := by
      rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    have h' := congrArg (fun v => b.repr v j) h
    rw [h1, h2] at h'
    exact h'
  have hcoeff := ggQ2s08am_repr_mono b hwσ xv (σ.symm j)
  rw [σ.apply_symm_apply, hfix w hw, hσsymm, hδε] at hcoeff
  rw [hcoeff]
  exact mul_ne_zero hε hi₀

theorem ggQ2s08_bigA_mono {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ} (hN : 10 ≤ N)
    (b : Module.Basis (Fin N) (ZMod 3) V) (R W : Subgroup (V ≃ₗ[ZMod 3] V))
    (hR : (∀ a, a ∈ R ↔ GGQ2S08Mono b a) ∨ (∀ a, a ∈ R ↔ GGQ2S08MonoEven b a))
    (hWR : W ≤ R) (hWgen : W = Subgroup.closure {s | s ∈ W ∧ GGLinRefl s})
    (e : ↥W ≃* Equiv.Perm (Fin N)) (xv : V) (hx : xv ≠ 0)
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (r : V ≃ₗ[ZMod 3] V) (hrR : r ∈ R) (hr : GGLinRefl r)
    (hrx : ¬ ∃ c : ZMod 3, r xv = c • xv) :
    GGQ2S08M0 R W r xv = R ∨ GGQ2S08CoreRO (N := N) R W r xv := by
  have hRm : ∀ a ∈ R, GGQ2S08Mono b a := by
    intro a ha
    rcases hR with h | h
    · exact (h a).1 ha
    · obtain ⟨σ, ε, h1, -, h3⟩ := (h a).1 ha
      exact ⟨σ, ε, h1, h3⟩
  have hWm : ∀ w ∈ W, GGQ2S08Mono b w := fun w hw => hRm w (hWR hw)
  have hfixx : ∀ w ∈ W, w xv = xv := (hWfix xv).2 (Submodule.mem_span_singleton_self xv)
  have htrans : ∀ i j, ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b j :=
    ggQ2s08_big_mono_trans (N := N) (by omega) b e hWm
  have hxall : ∀ i, b.repr xv i ≠ 0 := ggQ2s08am_all_ne b hWm hx hfixx htrans
  obtain ⟨f, hxf, hWf, hRf⟩ :=
    ggQ2s08core_rescale (by omega) b R W hR hWR hWgen xv hxall hfixx htrans
  subst hxf
  rcases ggQ2s08core_all_perms (by omega) f R W hRf hWf r hrR hr hrx with h | ⟨hev, hRb, hM⟩
  · exact Or.inl h
  · exact Or.inr ⟨hev, f, f.linearIndependent, f.span_eq, rfl, fun w hw => (hWf w).1 hw, hRb, hM⟩

end CFSG.StandardType

end
