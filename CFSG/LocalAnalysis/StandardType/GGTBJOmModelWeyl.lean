module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType

theorem ggTorusWeylElt_of_section {p : ℕ} {R : Type} [Group R] {L' : Type} [Group L']
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') {T : Type} [CommGroup T] (σ : T →* L')
    (hσp : ∀ v, σ v ^ p = 1) {A : Subgroup (MulAut L')}
    (hAσ : ∀ a ∈ A, ∃ v, a = MulAut.conj (σ v)) {n : L'}
    (hn : ∀ v, ∃ v', ψ n * ψ (σ v) * (ψ n)⁻¹ = ψ (σ v')) : GGTorusWeylElt p A n := by
  intro a ha
  obtain ⟨f, rfl⟩ := hAσ a ha
  obtain ⟨v', hv'⟩ := hn f
  set z := (σ v')⁻¹ * (n * σ f * n⁻¹) with hz
  have hzk : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, map_mul, map_mul, map_inv, hv', inv_mul_cancel]
  have hzc := Subgroup.mem_center_iff.mp (hker hzk)
  have hzp : z ^ p = 1 := by
    have h1 : (n * σ f * n⁻¹) ^ p = 1 := by
      rw [← MulAut.conj_apply, ← map_pow, hσp f, map_one]
    have h2 : n * σ f * n⁻¹ = σ v' * z := by rw [hz, mul_inv_cancel_left]
    rw [h2, (show Commute (σ v') z from hzc (σ v')).mul_pow, hσp v', one_mul] at h1
    exact h1
  have he : n * (MulAut.conj (σ f) n)⁻¹ = σ (v' * f⁻¹) * z := by
    have h2 : n * σ f * n⁻¹ = σ v' * z := by rw [hz, mul_inv_cancel_left]
    calc n * (MulAut.conj (σ f) n)⁻¹
        = (n * σ f * n⁻¹) * (σ f)⁻¹ := by rw [MulAut.conj_apply]; group
      _ = (σ v' * z) * (σ f)⁻¹ := by rw [h2]
      _ = σ v' * ((σ f)⁻¹ * z) := by
            rw [mul_assoc]
            congr 1
            exact (hzc ((σ f)⁻¹)).symm
      _ = σ (v' * f⁻¹) * z := by rw [map_mul, map_inv]; group
  refine ⟨?_, fun a' ha' => ?_⟩
  · rw [he, (show Commute (σ (v' * f⁻¹)) z from hzc (σ (v' * f⁻¹))).mul_pow,
      hσp (v' * f⁻¹), one_mul, hzp]
  · obtain ⟨g, rfl⟩ := hAσ a' ha'
    rw [he, MulAut.conj_apply]
    have hc : σ g * σ (v' * f⁻¹) = σ (v' * f⁻¹) * σ g := by
      rw [← map_mul, mul_comm g (v' * f⁻¹), map_mul]
    calc σ g * (σ (v' * f⁻¹) * z) * (σ g)⁻¹
        = (σ g * σ (v' * f⁻¹)) * z * (σ g)⁻¹ := by group
      _ = (σ (v' * f⁻¹) * σ g) * z * (σ g)⁻¹ := by rw [hc]
      _ = σ (v' * f⁻¹) * (σ g * z) * (σ g)⁻¹ := by group
      _ = σ (v' * f⁻¹) * (z * σ g) * (σ g)⁻¹ := by rw [hzc (σ g)]
      _ = σ (v' * f⁻¹) * z := by group

theorem exists_mulEquiv_of_range_comap {T R L' : Type} [Group T] [Group R] [Group L']
    (Λ : R →* MulAut L') (hΛinj : Function.Injective Λ) {A : Subgroup (MulAut L')}
    (hAΛ : ∀ a ∈ A, ∃ e, Λ e = a) (τ : T →* R) (hτinj : Function.Injective τ)
    (hτA : ∀ f, Λ (τ f) ∈ A) (hsurj : ∀ e, Λ e ∈ A → e ∈ τ.range) :
    ∃ Θ : T ≃* ↥A, ∀ f, ((Θ f : ↥A) : MulAut L') = Λ (τ f) := by
  let Θ₀ : T →* ↥A := (Λ.comp τ).codRestrict A hτA
  have hbij : Function.Bijective Θ₀ := by
    refine ⟨fun f g hfg => hτinj (hΛinj (congrArg Subtype.val hfg)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    have heA : Λ e ∈ A := by rw [he]; exact a.2
    obtain ⟨f, hf⟩ := hsurj e heA
    refine ⟨f, Subtype.ext ?_⟩
    show Λ (τ f) = ↑a
    rw [hf, he]
  exact ⟨MulEquiv.ofBijective Θ₀ hbij, fun f => rfl⟩

theorem exists_torus_conj_of_normalizer {T R L' : Type} [Group T] [Group R] [Group L']
    {ψ : L' →* R} (Λ : R →* MulAut L') (hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n)
    {A : Subgroup (MulAut L')} {E : Subgroup R} (hE : ∀ e, e ∈ E ↔ Λ e ∈ A) (τ : T →* R)
    (hτE : ∀ f, τ f ∈ E) (hrange : ∀ e ∈ E, e ∈ τ.range) {n : L'}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) (f : T) :
    ∃ f', ψ n * τ f * (ψ n)⁻¹ = τ f' := by
  have h1 : Λ (ψ n * τ f * (ψ n)⁻¹) ∈ A := by
    rw [map_mul, map_mul, map_inv, hΛn]
    exact (Subgroup.mem_normalizer_iff.mp hn (Λ (τ f))).mp ((hE (τ f)).mp (hτE f))
  have h2 : ψ n * τ f * (ψ n)⁻¹ ∈ E := (hE _).mpr h1
  obtain ⟨f', hf'⟩ := hrange _ h2
  exact ⟨f', hf'.symm⟩

end CFSG.StandardType

end
