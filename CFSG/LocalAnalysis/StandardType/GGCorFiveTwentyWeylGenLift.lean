module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative

section Lift

variable {p : ℕ} {R : Type} [Group R]

theorem pow_eq_one_of_multiplicative_fin_zmod {m : ℕ}
    (a : Multiplicative (Fin m → ZMod p)) : a ^ p = 1 := by
  apply (MulEquiv.piMultiplicative (fun _ : Fin m => ZMod p)).injective
  rw [map_pow, map_one, ReflInner.pow_eq_one_of_zmod]

theorem ggTorusWeylElt_of_model {k : ℕ} {L' : Type} [Group L'] {ψ : L' →* R}
    (hker : ψ.ker ≤ Subgroup.center L') {A : Subgroup (MulAut L')}
    {σ : Multiplicative (Fin k → ZMod p) →* L'} (Θ : Multiplicative (Fin k → ZMod p) ≃* ↥A)
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) {n : L'}
    (hn : ∀ f, ∃ f', ψ n * ψ (σ f) * (ψ n)⁻¹ = ψ (σ f')) :
    GGTorusWeylElt p A n := by
  have hσc : ∀ f g, σ f * σ g = σ g * σ f := fun f g => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hform : ∀ f, ∃ g, ∃ z ∈ ψ.ker, z ^ p = 1 ∧
      n * (MulAut.conj (σ f) n)⁻¹ = σ g * z := by
    intro f
    obtain ⟨f', hf'⟩ := hn f
    set z := (σ f')⁻¹ * (n * σ f * n⁻¹) with hz
    have hzk : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, map_mul, map_mul, map_inv, ← hf',
        inv_mul_cancel]
    have hzc := Subgroup.mem_center_iff.mp (hker hzk)
    have hzp : z ^ p = 1 := by
      have h1 : (n * σ f * n⁻¹) ^ p = 1 := by
        rw [conj_pow, ← map_pow, pow_eq_one_of_multiplicative_fin_zmod, map_one, mul_one,
          mul_inv_cancel]
      have h2 : n * σ f * n⁻¹ = σ f' * z := by rw [hz, mul_inv_cancel_left]
      rw [h2, (show Commute (σ f') z from hzc (σ f')).mul_pow, ← map_pow,
        pow_eq_one_of_multiplicative_fin_zmod, map_one, one_mul] at h1
      exact h1
    refine ⟨f' * f⁻¹, z, hzk, hzp, ?_⟩
    rw [MulAut.conj_apply, map_mul, map_inv, mul_assoc (σ f'), hzc (σ f)⁻¹, hz]
    group
  intro a ha
  obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
  have haσ : a = MulAut.conj (σ f) := by rw [← hΘ, hf]
  obtain ⟨g, z, hzk, hzp, he⟩ := hform f
  have hzc := Subgroup.mem_center_iff.mp (hker hzk)
  rw [haσ, he]
  refine ⟨?_, fun a' ha' => ?_⟩
  · rw [(show Commute (σ g) z from hzc (σ g)).mul_pow, ← map_pow,
      pow_eq_one_of_multiplicative_fin_zmod, map_one, one_mul, hzp]
  · obtain ⟨f'', hf''⟩ := Θ.surjective ⟨a', ha'⟩
    have ha'σ : a' = MulAut.conj (σ f'') := by rw [← hΘ, hf'']
    rw [ha'σ, MulAut.conj_apply]
    calc σ f'' * (σ g * z) * (σ f'')⁻¹ = σ g * (σ f'' * z) * (σ f'')⁻¹ := by
          rw [← mul_assoc, hσc]; group
      _ = σ g * (z * σ f'') * (σ f'')⁻¹ := by rw [hzc]
      _ = σ g * z := by group

theorem exists_ggConjAut_eq_congr {V L' : Type} [Group V] [Group L'] [Finite L'] {ψ : L' →* R}
    (hker : ψ.ker ≤ Subgroup.center L') {A : Subgroup (MulAut L')}
    {σ : V →* L'} (Θ : V ≃* ↥A)
    (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) {n : L'}
    {s : MulAut (V)}
    (hs : ∀ f, ψ n * ψ (σ f) * (ψ n)⁻¹ = ψ (σ (s f))) :
    ∃ hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')),
      ggConjAut A hn = MulAut.congr Θ s := by
  have hconjΘ : ∀ f, MulAut.conj n * ((Θ f : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ =
      ((Θ (s f) : ↥A) : MulAut L') := by
    intro f
    rw [hΘ f, hΘ (s f)]
    have hconj_mul : MulAut.conj n * MulAut.conj (σ f) * (MulAut.conj n)⁻¹ =
        MulAut.conj (n * σ f * n⁻¹) := by
      rw [← map_mul, ← map_inv, ← map_mul]
    have hmap : ψ (n * σ f * n⁻¹) = ψ (σ (s f)) := by
      rw [map_mul, map_mul, map_inv]
      exact hs f
    rw [hconj_mul]
    exact ReflInner.conj_eq_conj_of_map_eq hker hmap
  have hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    refine mem_normalizer_of_forall_conj_mem fun a ha => ?_
    obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
    have h1 := hconjΘ (s⁻¹ f)
    rw [MulAut.apply_inv_self, hf] at h1
    have h2 : a = MulAut.conj n * ((Θ (s⁻¹ f) : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ :=
      h1.symm
    have he : (MulAut.conj n)⁻¹ * a * MulAut.conj n = ((Θ (s⁻¹ f) : ↥A) : MulAut L') := by
      rw [h2]; group
    rw [he]
    exact (Θ (s⁻¹ f)).2
  refine ⟨hn, ?_⟩
  refine MulEquiv.ext fun a => Subtype.ext ?_
  obtain ⟨f, rfl⟩ := Θ.surjective a
  rw [ggConjAut_apply, hconjΘ, MulAut.congr_apply]
  simp

end Lift

end CFSG.StandardType

end
