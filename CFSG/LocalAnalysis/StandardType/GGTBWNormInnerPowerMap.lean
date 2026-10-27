module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly TableB

theorem ggLin_apply_of_forall_pow {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V) {u : MulAut E} {k : ℕ}
    (hu : ∀ a, u a = a ^ k) (v : V) : ggLin (p := p) ι u v = (k : ZMod p) • v := by
  rw [ggLin_apply, hu, ofMul_pow, ofMul_toMul, map_nsmul, AddEquiv.apply_symm_apply,
    Nat.cast_smul_eq_nsmul]

theorem exists_pow_mem_ggAutomizer_of_innerModel {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hZ : Subgroup.center R = ⊥) (hIp : GGOutdiagPrime p R I)
    (hcp : GGCenterPrime p R) {L' : Type} [Group L'] [Finite L'] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (hsc : GGTorusSelfCent p A) {k : ℕ}
    (hpow : ∀ E : Subgroup R, IsElemAbelian p E → Nat.card E = Nat.card A →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
      ∃ z : R, ∀ x ∈ E, z * x * z⁻¹ = x ^ k) :
    ∃ u ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ∀ a, u a = a ^ k := by
  obtain ⟨Λ, hΛeq, -, -, hAΛ, hE, hEc, hEsc⟩ :=
    TwE6TB.exists_innerModel hp hZ hIp hcp ψ hψ hker hperf hA hAI hsc
  obtain ⟨z, hz⟩ := hpow (A.comap Λ) hE hEc hEsc
  obtain ⟨n, rfl⟩ := hψ z
  have hΛn : Λ (ψ n) = MulAut.conj n := hΛeq rfl
  have hconj : ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ = a ^ k := by
    intro a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have he : e ∈ A.comap Λ := ha
    rw [← hΛn, ← map_inv, ← map_mul, ← map_mul, hz e he, map_pow]
  have hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    Subgroup.mem_normalizer_fintype fun a ha => by
      rw [hconj a ha]
      exact A.pow_mem ha k
  refine ⟨ggConjAut A hn, ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn,
    fun a => Subtype.ext ?_⟩
  rw [ggConjAut_apply, Subgroup.coe_pow]
  exact hconj a a.2

end CFSG.StandardType

end
