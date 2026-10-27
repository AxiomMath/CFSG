module

public import CFSG.RankThree.GF2n.Smith81.S81E5Uni
public import CFSG.RankThree.GF2n.Smith81.S81WGeomGen

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
  CFSG.RankThree.GF2n.Smith81.EGeom


abbrev i7 : Fin e7Data.d := ⟨0, by decide⟩

@[expose] def Far7 (b : Fin e7Data.d) : Prop :=
  ∃ k : Fin 126, pr i7 ((Tag.rootCertificate .E7).root k) = 1 ∧
    pr b ((Tag.rootCertificate .E7).root k) = -1 ∧
    ¬ (e7Data.wt i7 = e7Data.wt b + MinData.toWeight ((Tag.rootCertificate .E7).root k))

instance (b : Fin e7Data.d) : Decidable (Far7 b) := by unfold Far7; infer_instance

@[expose] def Near7 : Finset (Fin e7Data.d) := Finset.univ.filter fun b => ¬ Far7 b

theorem card_Near7 : Near7.card = 28 := by
  decide +kernel

theorem far7_root {b : Fin e7Data.d} (hb : Far7 b) :
    ∃ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ ∧ pr i7 γ = 1 ∧ pr b γ = -1 ∧ shift γ b ≠ i7 := by
  obtain ⟨k, h1, h2, h3⟩ := hb
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  have hγ : IsRoot .E7 ((Tag.rootCertificate .E7).root k) :=
    RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)
  refine ⟨(Tag.rootCertificate .E7).root k, hγ, h1, h2, fun hs => h3 ?_⟩
  have hw := wt_shift hγ h2
  rw [hs] at hw
  exact hw

private theorem s81w_mu7_index : ∃ μ : Fin e7Data.d, ∃ k : Fin 126, μ ≠ i7 ∧
    pr i7 ((Tag.rootCertificate .E7).root k) = 1 ∧ pr μ ((Tag.rootCertificate .E7).root k) = -1 ∧
    ∀ k' : Fin 126, pr i7 ((Tag.rootCertificate .E7).root k') = 1 →
      pr μ ((Tag.rootCertificate .E7).root k') = -1 →
      e7Data.wt i7 = e7Data.wt μ + MinData.toWeight ((Tag.rootCertificate .E7).root k') := by
  unfold pr
  decide +kernel

theorem exists_mu7 : ∃ μ : Fin e7Data.d, ∃ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ ∧ μ ≠ i7 ∧
    pr i7 γ = 1 ∧ pr μ γ = -1 ∧ shift γ μ = i7 ∧
    ∀ δ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 δ → pr i7 δ = 1 → pr μ δ = -1 → shift δ μ = i7 := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨μ, k, hμ, hk1, hk2, hall⟩ := s81w_mu7_index
  have hγ : IsRoot .E7 ((Tag.rootCertificate .E7).root k) :=
    RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)
  refine ⟨μ, (Tag.rootCertificate .E7).root k, hγ, hμ, hk1, hk2, shift_eq (hall k hk1 hk2), ?_⟩
  intro δ hδ h1 h2
  obtain ⟨k', hk', hkδ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hδ
  subst hkδ
  exact shift_eq (hall ⟨k', by omega⟩ h1 h2)


variable {K : Type} [Field K]

theorem rootSet7_subset : rootSet7 K ⊆ (EAut K : Set (V K ≃ₗ[K] V K)) :=
  fun _ hs => rootRad7_le_EAut (Subgroup.subset_closure hs)

theorem rootSet7_fix [CharP K 2] :
    ∀ s ∈ rootSet7 K, s (Finsupp.single i7 1 : V K) = Finsupp.single i7 1 := by
  rintro s ⟨γ, hγ, hpr, c, rfl⟩
  have hpr' : pr i7 γ = 1 := hpr
  have hne : ¬ (pr i7 γ = -1) := by rw [hpr']; norm_num
  rw [vAut_apply, e7Data_valid.xu_apply, rootOp_single hγ, if_neg hne, smul_zero, add_zero]

theorem far7_witness [CharP K 2] {b : Fin e7Data.d} (hb : Far7 b) :
    ∃ s ∈ rootSet7 K, ∃ b' : Fin e7Data.d, b' ≠ i7 ∧ ∀ v : V K, (s v - v) b' = v b := by
  obtain ⟨γ, hγ, h1, h2, h3⟩ := far7_root hb
  refine ⟨vAut K (e7Data_valid.xu K γ 1), ⟨γ, hγ, h1, 1, rfl⟩, shift γ b, h3, fun v => ?_⟩
  rw [Finsupp.sub_apply, vAut_apply, xu_apply_coord hγ (1 : K) v (shift γ b), pr_shift_self hγ h2,
    if_pos rfl, shift_neg_shift hγ h2]
  ring

theorem mu7_W [CharP K 2] {μ : Fin e7Data.d}
    (hμ : ∀ δ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 δ → pr i7 δ = 1 → pr μ δ = -1 →
      shift δ μ = i7) :
    ∀ s ∈ rootSet7 K, s (Finsupp.single μ 1 : V K) - Finsupp.single μ 1 ∈
      Submodule.span K {(Finsupp.single i7 1 : V K)} := by
  rintro s ⟨γ, hγ, hpr, c, rfl⟩
  have hpr' : pr i7 γ = 1 := hpr
  rw [vAut_apply, e7Data_valid.xu_apply, rootOp_single hγ]
  by_cases h : pr μ γ = -1
  · rw [if_pos h, hμ γ hγ hpr' h]
    have hmem : c • (Finsupp.single i7 1 : V K) ∈ Submodule.span K {(Finsupp.single i7 1 : V K)} :=
      Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
    convert hmem using 1
    abel
  · rw [if_neg h, smul_zero, add_zero, sub_self]
    exact Submodule.zero_mem _

theorem plane7 [CharP K 2] {μ : Fin e7Data.d} {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (hpi : pr i7 γ = 1) (hpμ : pr μ γ = -1) (hsh : shift γ μ = i7) (c : K) :
    vAut K (e7Data_valid.xu K γ c) (Finsupp.single i7 1 : V K) = Finsupp.single i7 1 ∧
    vAut K (e7Data_valid.xu K γ c) (Finsupp.single μ 1 : V K) =
      Finsupp.single μ 1 + c • Finsupp.single i7 1 ∧
    vAut K (e7Data_valid.xu K (-γ) c) (Finsupp.single i7 1 : V K) =
      Finsupp.single i7 1 + c • Finsupp.single μ 1 ∧
    vAut K (e7Data_valid.xu K (-γ) c) (Finsupp.single μ 1 : V K) = Finsupp.single μ 1 := by
  have hne1 : ¬ (pr i7 γ = -1) := by rw [hpi]; norm_num
  have hpi' : pr i7 (-γ) = -1 := by rw [pr_neg, hpi]
  have hpμ' : pr μ (-γ) = 1 := by rw [pr_neg, hpμ, neg_neg]
  have hne4 : ¬ (pr μ (-γ) = -1) := by rw [hpμ']; norm_num
  have hsh' : shift (-γ) i7 = μ := by
    have h := shift_neg_shift hγ hpμ
    rw [hsh] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [vAut_apply, e7Data_valid.xu_apply, rootOp_single hγ, if_neg hne1, smul_zero, add_zero]
  · rw [vAut_apply, e7Data_valid.xu_apply, rootOp_single hγ, if_pos hpμ, hsh]
  · rw [vAut_apply, e7Data_valid.xu_apply, rootOp_single (isRoot_neg hγ), if_pos hpi', hsh']
  · rw [vAut_apply, e7Data_valid.xu_apply, rootOp_single (isRoot_neg hγ), if_neg hne4, smul_zero,
      add_zero]

theorem e7MinuscGeom [Finite K] [CharP K 2] :
    MinuscGeom (EAut K) (w0 : V K) (rootRad7 K) 28 := by
  obtain ⟨μ, γ, hγ, hμ, hpi, hpμ, hsh, hall⟩ := exists_mu7
  exact minuscGeom_of_basis (S := rootSet7 K) (i₀ := i7) (μ := μ) (N := Near7) (n := 28)
    rootSet7_subset rootSet7_fix card_Near7
    (fun b hb => far7_witness (by simpa [Near7] using hb)) hμ (mu7_W hall)
    (fun c => vAut K (e7Data_valid.xu K γ c)) (fun c => vAut K (e7Data_valid.xu K (-γ) c))
    (fun c => Subgroup.mem_map_of_mem _ (e7Data_valid.xu_mem K γ c))
    (fun c => Subgroup.mem_map_of_mem _ (e7Data_valid.xu_mem K (-γ) c))
    (fun c => (plane7 hγ hpi hpμ hsh c).1) (fun c => (plane7 hγ hpi hpμ hsh c).2.1)
    (fun c => (plane7 hγ hpi hpμ hsh c).2.2.1) (fun c => (plane7 hγ hpi hpμ hsh c).2.2.2)

end CFSG.RankThree.GF2n.Smith81.E7Model
