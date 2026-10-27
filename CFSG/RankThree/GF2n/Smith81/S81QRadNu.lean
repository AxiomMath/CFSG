module

public import CFSG.RankThree.GF2n.Smith81.S81D6Ops

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

abbrev nodeA2 : Fin (Tag.rank .E7) := ⟨1, by decide⟩

abbrev nodeNu : Fin (Tag.rank .E7) := ⟨2, by decide⟩

private theorem pr_a0_check : ∀ k : Fin 126,
    MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0 →
    pr (⟨8, by decide⟩ : Fin e7Data.d) ((Tag.rootCertificate .E7).root k) =
      (Tag.rootCertificate .E7).root k nodeA2 := by
  unfold pr
  decide +kernel

theorem pr_a0_eq {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) : pr (a0 : Fin e7Data.d) γ = γ nodeA2 := by
  obtain ⟨hroot, hperp⟩ := hγ
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hroot
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  exact pr_a0_check ⟨k, by omega⟩ hperp

variable (K : Type) [Field K]

@[expose] def rootSetν : Set (W K ≃ₗ[K] W K) :=
  {g | ∃ γ ∈ Perp, γ nodeNu = 1 ∧ ∃ c : K, ∀ w : W K,
    emb K (g w) = (e7Data_valid.xu K γ c : Module.End K (V K)) (emb K w)}

@[expose] def rootRadν : Subgroup (W K ≃ₗ[K] W K) := Subgroup.closure (rootSetν K)

variable {K} [CharP K 2]

theorem xuWUnit_congr {β β' : Fin (Tag.rank .E7) → ℤ} (h : β = β') (hβ : β ∈ Perp) (hβ' : β' ∈ Perp)
    (c : K) : xuWUnit hβ c = xuWUnit hβ' c := by
  subst h
  rfl

theorem vAut0_xuWUnit_mem_EAut0 {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) (c : K) :
    vAut0 K (xuWUnit hβ c) ∈ EAut0 K :=
  Subgroup.mem_map_of_mem _ (xuWUnit_mem_LamW hβ c)

theorem eq_vAut0_xuWUnit_of_emb {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp) (c : K)
    {g : W K ≃ₗ[K] W K}
    (h : ∀ w : W K, emb K (g w) = (e7Data_valid.xu K γ c : Module.End K (V K)) (emb K w)) :
    g = vAut0 K (xuWUnit hγ c) := by
  apply LinearEquiv.ext
  intro w
  apply emb_injective
  rw [h w, vAut0_apply]
  exact (xuWUnit_induces hγ c w).symm

theorem mem_rootSet0_iff {g : W K ≃ₗ[K] W K} :
    g ∈ rootSet0 K ↔ ∃ γ, ∃ hγ : γ ∈ Perp, γ nodeA2 = 1 ∧ ∃ c : K, g = vAut0 K (xuWUnit hγ c) := by
  constructor
  · rintro ⟨γ, hγ, h1, c, h⟩
    exact ⟨γ, hγ, by rw [← pr_a0_eq hγ]; exact h1, c, eq_vAut0_xuWUnit_of_emb hγ c h⟩
  · rintro ⟨γ, hγ, h1, c, rfl⟩
    exact ⟨γ, hγ, by rw [pr_a0_eq hγ]; exact h1, c, fun w => xuWUnit_induces hγ c w⟩

theorem mem_rootSetν_iff {g : W K ≃ₗ[K] W K} :
    g ∈ rootSetν K ↔ ∃ γ, ∃ hγ : γ ∈ Perp, γ nodeNu = 1 ∧ ∃ c : K, g = vAut0 K (xuWUnit hγ c) := by
  constructor
  · rintro ⟨γ, hγ, h1, c, h⟩
    exact ⟨γ, hγ, h1, c, eq_vAut0_xuWUnit_of_emb hγ c h⟩
  · rintro ⟨γ, hγ, h1, c, rfl⟩
    exact ⟨γ, hγ, h1, c, fun w => xuWUnit_induces hγ c w⟩

theorem rootSet0_subset_EAut0 : rootSet0 K ⊆ (EAut0 K : Set (W K ≃ₗ[K] W K)) := by
  intro g hg
  obtain ⟨γ, hγ, -, c, rfl⟩ := mem_rootSet0_iff.1 hg
  exact vAut0_xuWUnit_mem_EAut0 hγ c

theorem rootSetν_subset_EAut0 : rootSetν K ⊆ (EAut0 K : Set (W K ≃ₗ[K] W K)) := by
  intro g hg
  obtain ⟨γ, hγ, -, c, rfl⟩ := mem_rootSetν_iff.1 hg
  exact vAut0_xuWUnit_mem_EAut0 hγ c

theorem rootRad0_le_EAut0 : rootRad0 K ≤ EAut0 K :=
  (Subgroup.closure_le _).2 rootSet0_subset_EAut0

end CFSG.RankThree.GF2n.Smith81.D6Spin
