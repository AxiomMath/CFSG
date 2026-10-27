module

public import CFSG.RankThree.GF2n.Smith81.S81D6Ops
public import CFSG.RankThree.GF2n.Smith81.S81WGeomGen

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.EGeom


@[expose] def Far6 (b : Fin e7Data.d) : Prop :=
  ∃ k : Fin 126, MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0 ∧
    pr (a0 : Fin e7Data.d) ((Tag.rootCertificate .E7).root k) = 1 ∧
    pr b ((Tag.rootCertificate .E7).root k) = -1 ∧
    ¬ (e7Data.wt (a0 : Fin e7Data.d) =
      e7Data.wt b + MinData.toWeight ((Tag.rootCertificate .E7).root k))

instance (b : Fin e7Data.d) : Decidable (Far6 b) := by unfold Far6; infer_instance

@[expose] def Near6 : Finset Idx0 := Finset.univ.filter fun b => ¬ Far6 (b : Fin e7Data.d)

theorem card_Near6 : Near6.card = 16 := by
  have hset : Near6 = Finset.filter (fun b : Idx0 => ¬ ∃ k : Fin 126,
      MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0 ∧
      pr (⟨8, by decide⟩ : Fin e7Data.d) ((Tag.rootCertificate .E7).root k) = 1 ∧
      pr (b : Fin e7Data.d) ((Tag.rootCertificate .E7).root k) = -1 ∧
      ¬ (e7Data.wt (⟨8, by decide⟩ : Fin e7Data.d) =
        e7Data.wt (b : Fin e7Data.d) + MinData.toWeight ((Tag.rootCertificate .E7).root k)))
      Finset.univ := by
    ext b
    simp only [Near6, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  rw [hset]
  decide +kernel

theorem far6_root {b : Fin e7Data.d} (hb : Far6 b) :
    ∃ γ ∈ Perp, pr (a0 : Fin e7Data.d) γ = 1 ∧ pr b γ = -1 ∧ shift γ b ≠ (a0 : Fin e7Data.d) := by
  unfold Far6 at hb
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hb
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  have hγ : IsRoot .E7 ((Tag.rootCertificate .E7).root k) :=
    RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)
  refine ⟨(Tag.rootCertificate .E7).root k, ?_, hk2, hk3, fun h => hk4 ?_⟩
  · show IsRoot .E7 ((Tag.rootCertificate .E7).root k) ∧
      MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0
    exact ⟨hγ, hk1⟩
  · have h1 := wt_shift hγ hk3
    rw [h] at h1
    exact h1

private theorem s81w_mu6_index : ∃ μ : Fin e7Data.d,
    pr μ theta = 0 ∧ μ ≠ (⟨8, by decide⟩ : Fin e7Data.d) ∧
    ∃ k : Fin 126,
      MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0 ∧
      pr (⟨8, by decide⟩ : Fin e7Data.d) ((Tag.rootCertificate .E7).root k) = 1 ∧
      pr μ ((Tag.rootCertificate .E7).root k) = -1 ∧
      e7Data.wt (⟨8, by decide⟩ : Fin e7Data.d) =
        e7Data.wt μ + MinData.toWeight ((Tag.rootCertificate .E7).root k) ∧
      ∀ k' : Fin 126, MinData.toWeight ((Tag.rootCertificate .E7).root k') ⬝ᵥ theta = 0 →
        pr (⟨8, by decide⟩ : Fin e7Data.d) ((Tag.rootCertificate .E7).root k') = 1 →
        pr μ ((Tag.rootCertificate .E7).root k') = -1 →
        e7Data.wt (⟨8, by decide⟩ : Fin e7Data.d) =
          e7Data.wt μ + MinData.toWeight ((Tag.rootCertificate .E7).root k') := by
  unfold pr
  decide +kernel

theorem exists_mu6 : ∃ μ : Idx0, ∃ γ ∈ Perp, μ ≠ a0 ∧
    pr (a0 : Fin e7Data.d) γ = 1 ∧ pr (μ : Fin e7Data.d) γ = -1 ∧
    shift γ (μ : Fin e7Data.d) = (a0 : Fin e7Data.d) ∧
    ∀ δ ∈ Perp, pr (a0 : Fin e7Data.d) δ = 1 → pr (μ : Fin e7Data.d) δ = -1 →
      shift δ (μ : Fin e7Data.d) = (a0 : Fin e7Data.d) := by
  obtain ⟨μ, hμ0, hμa, k, hk1, hk2, hk3, hk4, hk5⟩ := s81w_mu6_index
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  have hγ : IsRoot .E7 ((Tag.rootCertificate .E7).root k) :=
    RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)
  have hμI : μ ∈ idx0 := mem_idx0.2 hμ0
  refine ⟨⟨μ, hμI⟩, (Tag.rootCertificate .E7).root k, ?_, ?_, hk2, hk3, ?_, ?_⟩
  · show IsRoot .E7 ((Tag.rootCertificate .E7).root k) ∧
      MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0
    exact ⟨hγ, hk1⟩
  · intro h
    apply hμa
    exact congrArg Subtype.val h
  · exact shift_eq hk4
  · intro δ hδ hδa hδμ
    have hδ' : IsRoot .E7 δ ∧ MinData.toWeight δ ⬝ᵥ theta = 0 := hδ
    obtain ⟨j, hj, hjδ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hδ'.1
    have hjP : MinData.toWeight ((Tag.rootCertificate .E7).root j) ⬝ᵥ theta = 0 := by
      rw [hjδ]
      exact hδ'.2
    have hja : pr (a0 : Fin e7Data.d) ((Tag.rootCertificate .E7).root j) = 1 := by
      rw [hjδ]
      exact hδa
    have hjμ : pr μ ((Tag.rootCertificate .E7).root j) = -1 := by
      rw [hjδ]
      exact hδμ
    have key := hk5 ⟨j, by omega⟩ hjP hja hjμ
    rw [← hjδ]
    exact shift_eq key


variable {K : Type} [Field K]

theorem rootSet0_subset [CharP K 2] : rootSet0 K ⊆ (EAut0 K : Set (W K ≃ₗ[K] W K)) := by
  rintro g ⟨γ, hγ, -, c, hg⟩
  rw [SetLike.mem_coe, EAut0, Subgroup.mem_map]
  refine ⟨xuWUnit hγ c, xuWUnit_mem_LamW hγ c, LinearEquiv.ext fun w => ?_⟩
  exact emb_injective ((xuWUnit_induces hγ c w).trans (hg w).symm)

theorem rootSet0_fix [CharP K 2] : ∀ s ∈ rootSet0 K, s (Finsupp.single a0 1 : W K) =
    Finsupp.single a0 1 := by
  rintro s ⟨γ, hγ, hpr, c, hs⟩
  have hn1 : ¬ (pr (a0 : Fin e7Data.d) γ = -1) := by rw [hpr]; norm_num
  apply emb_injective
  rw [hs, emb_single, e7Data_valid.xu_apply, rootOp_single hγ.1, if_neg hn1, smul_zero, add_zero]

theorem far6_witness [CharP K 2] {b : Idx0} (hb : Far6 (b : Fin e7Data.d)) :
    ∃ s ∈ rootSet0 K, ∃ b' : Idx0, b' ≠ a0 ∧ ∀ v : W K, (s v - v) b' = v b := by
  obtain ⟨γ, hγ, h1, h2, h3⟩ := far6_root hb
  have hb' : pr (shiftW γ b : Fin e7Data.d) γ = 1 := by
    rw [shiftW_val hγ h2]
    exact pr_shift_self hγ.1 h2
  have hbb : shiftW (-γ) (shiftW γ b) = b := by
    apply Subtype.ext
    have h4 : pr (shiftW γ b : Fin e7Data.d) (-γ) = -1 := by rw [pr_neg, hb']
    rw [shiftW_val (neg_mem_Perp hγ) h4, shiftW_val hγ h2, shift_neg_shift hγ.1 h2]
  refine ⟨vAut0 K (xuWUnit hγ 1), ⟨γ, hγ, h1, 1, fun w => xuWUnit_induces hγ 1 w⟩,
    shiftW γ b, ?_, fun v => ?_⟩
  · intro hba
    apply h3
    have h5 := shiftW_val hγ h2
    rw [hba] at h5
    exact h5.symm
  · have key := xuWUnit_apply_coord hγ 1 v (shiftW γ b)
    rw [if_pos hb', hbb, one_mul] at key
    rw [Finsupp.sub_apply, vAut0_apply, key]
    ring

theorem mu6_W [CharP K 2] {μ : Idx0}
    (hμ : ∀ δ ∈ Perp, pr (a0 : Fin e7Data.d) δ = 1 → pr (μ : Fin e7Data.d) δ = -1 →
      shift δ (μ : Fin e7Data.d) = (a0 : Fin e7Data.d)) :
    ∀ s ∈ rootSet0 K, s (Finsupp.single μ 1 : W K) - Finsupp.single μ 1 ∈
      Submodule.span K {(Finsupp.single a0 1 : W K)} := by
  rintro s ⟨γ, hγ, hpr, c, hs⟩
  have key : s (Finsupp.single μ 1) - Finsupp.single μ 1 = c • EW K γ (Finsupp.single μ 1) := by
    apply emb_injective
    rw [map_sub, map_smul, emb_EW hγ, hs, emb_single, e7Data_valid.xu_apply]
    abel
  rw [key, EW_single hγ μ]
  by_cases h : pr (μ : Fin e7Data.d) γ = -1
  · rw [if_pos h]
    have hsμ : shiftW γ μ = a0 := Subtype.ext (by rw [shiftW_val hγ h]; exact hμ γ hγ hpr h)
    rw [hsμ]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  · rw [if_neg h, smul_zero]
    exact Submodule.zero_mem _

theorem plane6 [CharP K 2] {μ : Idx0} {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp)
    (hpa : pr (a0 : Fin e7Data.d) γ = 1) (hpμ : pr (μ : Fin e7Data.d) γ = -1)
    (hsh : shift γ (μ : Fin e7Data.d) = (a0 : Fin e7Data.d)) (c : K) :
    vAut0 K (xuWUnit hγ c) (Finsupp.single a0 1 : W K) = Finsupp.single a0 1 ∧
    vAut0 K (xuWUnit hγ c) (Finsupp.single μ 1 : W K) =
      Finsupp.single μ 1 + c • Finsupp.single a0 1 ∧
    vAut0 K (xuWUnit (neg_mem_Perp hγ) c) (Finsupp.single a0 1 : W K) =
      Finsupp.single a0 1 + c • Finsupp.single μ 1 ∧
    vAut0 K (xuWUnit (neg_mem_Perp hγ) c) (Finsupp.single μ 1 : W K) = Finsupp.single μ 1 := by
  have hn1 : ¬ (pr (a0 : Fin e7Data.d) γ = -1) := by rw [hpa]; norm_num
  have hpa' : pr (a0 : Fin e7Data.d) (-γ) = -1 := by rw [pr_neg, hpa]
  have hpμ' : ¬ (pr (μ : Fin e7Data.d) (-γ) = -1) := by rw [pr_neg, hpμ]; norm_num
  have hsμ : shiftW γ μ = a0 := Subtype.ext (by rw [shiftW_val hγ hpμ]; exact hsh)
  have hsa : shiftW (-γ) a0 = μ := by
    apply Subtype.ext
    rw [shiftW_val (neg_mem_Perp hγ) hpa', ← hsh]
    exact shift_neg_shift hγ.1 hpμ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [vAut0_apply, xuWUnit_apply, EW_single hγ, if_neg hn1, smul_zero, add_zero]
  · rw [vAut0_apply, xuWUnit_apply, EW_single hγ, if_pos hpμ, hsμ]
  · rw [vAut0_apply, xuWUnit_apply, EW_single (neg_mem_Perp hγ), if_pos hpa', hsa]
  · rw [vAut0_apply, xuWUnit_apply, EW_single (neg_mem_Perp hγ), if_neg hpμ', smul_zero, add_zero]

theorem d6MinuscGeom [Finite K] [CharP K 2] :
    MinuscGeom (EAut0 K) (p0 K) (rootRad0 K) 16 := by
  obtain ⟨μ, γ, hγ, hμ, hpa, hpμ, hsh, hall⟩ := exists_mu6
  exact minuscGeom_of_basis (S := rootSet0 K) (i₀ := a0) (μ := μ) (N := Near6) (n := 16)
    rootSet0_subset rootSet0_fix card_Near6
    (fun b hb => far6_witness (by simpa [Near6] using hb)) hμ (mu6_W hall)
    (fun c => vAut0 K (xuWUnit hγ c)) (fun c => vAut0 K (xuWUnit (neg_mem_Perp hγ) c))
    (fun c => Subgroup.mem_map_of_mem _ (xuWUnit_mem_LamW hγ c))
    (fun c => Subgroup.mem_map_of_mem _ (xuWUnit_mem_LamW (neg_mem_Perp hγ) c))
    (fun c => (plane6 hγ hpa hpμ hsh c).1) (fun c => (plane6 hγ hpa hpμ hsh c).2.1)
    (fun c => (plane6 hγ hpa hpμ hsh c).2.2.1) (fun c => (plane6 hγ hpa hpμ hsh c).2.2.2)

end CFSG.RankThree.GF2n.Smith81.D6Spin
