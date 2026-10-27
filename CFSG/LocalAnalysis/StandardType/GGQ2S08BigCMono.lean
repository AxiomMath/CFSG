module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigMonoTrans

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

private lemma ggQ2s08cm_repr_mono {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) {g : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin N)}
    {δ : Fin N → ZMod 3} (hg : ∀ a, g (b a) = δ a • b (σ a)) (v : V) (k : Fin N) :
    b.repr (g v) (σ k) = b.repr v k * δ k := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, hg, Module.Basis.repr_self, Finsupp.smul_single,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp [mul_comm]
  · intro x _ hx
    rw [ite_eq_right (fun h => hx (σ.injective h))]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem ggQ2s08_bigC_mono_false {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (h3 : 3 ∣ N) (hN : 5 ≤ N) (b : Module.Basis (Fin N) (ZMod 3) V)
    {W : Subgroup (V ≃ₗ[ZMod 3] V)} (e : ↥W ≃* Equiv.Perm (Fin N))
    (hWm : ∀ w ∈ W, GGQ2S08Mono b w) (xv : V) (hWx : ∀ w ∈ W, w xv = xv)
    (f : V →ₗ[ZMod 3] ZMod 3) (hf : f xv ≠ 0) (hWf : ∀ w ∈ W, ∀ v, f (w v) = f v) : False := by
  have htrans := ggQ2s08_big_mono_trans hN b e hWm
  have hNpos : 0 < N := by omega
  let i0 : Fin N := ⟨0, hNpos⟩
  have hstep : ∀ (i j : Fin N) (w : V ≃ₗ[ZMod 3] V), w ∈ W →
      ∀ ε : ZMod 3, ε ≠ 0 → w (b i) = ε • b j →
      f (b i) = ε * f (b j) ∧ b.repr xv j = ε * b.repr xv i := by
    intro i j w hw ε _hε hwij
    obtain ⟨σ, δ, hδ, hg⟩ := hWm w hw
    have h : δ i • b (σ i) = ε • b j := (hg i).symm.trans hwij
    have hrepr : Finsupp.single (σ i) (δ i) = Finsupp.single j ε := by
      have h' := congrArg b.repr h
      simpa [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one] using h'
    have hσδ : σ i = j ∧ δ i = ε := by
      rcases (Finsupp.single_eq_single_iff (σ i) j (δ i) ε).mp hrepr with ⟨h1, h2⟩ | ⟨h1, -⟩
      · exact ⟨h1, h2⟩
      · exact absurd h1 (hδ i)
    refine ⟨?_, ?_⟩
    · have hwf := hWf w hw (b i)
      rw [hwij, map_smul, smul_eq_mul] at hwf
      exact hwf.symm
    · have hco := ggQ2s08cm_repr_mono b hg xv i
      rw [hWx w hw, hσδ.1, hσδ.2] at hco
      exact hco.trans (mul_comm _ _)
  have hprod : ∀ i : Fin N, f (b i) * b.repr xv i = f (b i0) * b.repr xv i0 := by
    intro i
    obtain ⟨w, hw, ε, hε, hwij⟩ := htrans i0 i
    obtain ⟨hf', hx'⟩ := hstep i0 i w hw ε hε hwij
    rw [hx', hf']
    ring
  have hfxv : f xv = ∑ i : Fin N, b.repr xv i * f (b i) := by
    conv_lhs => rw [← b.sum_repr xv]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hsum : (∑ i : Fin N, b.repr xv i * f (b i)) =
      ∑ _i : Fin N, f (b i0) * b.repr xv i0 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_comm (b.repr xv i) (f (b i)), hprod i]
  have hzero : f xv = 0 := by
    rw [hfxv, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hN0 : (N : ZMod 3) = 0 := by
      obtain ⟨q, rfl⟩ := h3
      rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [hN0, zero_mul]
  exact hf hzero

end CFSG.StandardType

end
