module

public import CFSG.GroupTheory.OddOrderLift
public import CFSG.ClassicalInvolution.Asc77.AscIHWitness

public section

namespace CFSG.GroupTheory

theorem normalizerMonoidHom_mem_range_conj_iff
    {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    K.normalizerMonoidHom ⟨g, hg⟩ ∈
        (MulAut.conj : ↥K →* MulAut ↥K).range ↔
      ∃ r ∈ K, ∀ x ∈ K, g * x * g⁻¹ = r * x * r⁻¹ := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, r.2, ?_⟩
    intro x hx
    have h := congrArg (fun e : MulAut ↥K => ((e ⟨x, hx⟩ : ↥K) : G)) hr
    simpa [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] using h.symm
  · rintro ⟨r, hr, hconj⟩
    refine ⟨⟨r, hr⟩, ?_⟩
    ext x
    rw [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simpa using (hconj x x.2).symm

theorem exists_inner_normalizer_of_central_image
    {M X : Type*} [Group M] [Finite M] [Group X]
    (ψ : M →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center M)
    (R : Subgroup M) (hR : Group.IsPerfect R)
    (hinner : ∀ g : M, g ∈ Subgroup.normalizer (R : Set M) → Odd (orderOf g) →
      ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹)
    {g : X} (hgN : g ∈ Subgroup.normalizer ((R.map ψ : Subgroup X) : Set X))
    (hgodd : Odd (orderOf g)) :
    ∃ r ∈ R.map ψ,
      ∀ x ∈ R.map ψ, g * x * g⁻¹ = r * x * r⁻¹ := by
  obtain ⟨y, hyg, hyodd⟩ := exists_odd_orderOf_preimage ψ hψ hgodd
  have hyN : y ∈ Subgroup.normalizer (R : Set M) := by
    apply CFSG.ClassicalInvolution.Asc77.mem_normalizer_of_map_mem_normalizer ψ hker hR
    rwa [hyg]
  obtain ⟨r, hr, hconj⟩ := hinner y hyN hyodd
  refine ⟨ψ r, Subgroup.mem_map_of_mem ψ hr, ?_⟩
  intro x' hx'
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
  calc
    g * ψ x * g⁻¹ = ψ y * ψ x * (ψ y)⁻¹ := by rw [← hyg]
    _ = ψ (y * x * y⁻¹) := by simp only [map_mul, map_inv]
    _ = ψ (r * x * r⁻¹) := by rw [hconj x hx]
    _ = ψ r * ψ x * (ψ r)⁻¹ := by simp only [map_mul, map_inv]

end CFSG.GroupTheory

end
