module

public import CFSG.RankThree.GF2n.Smith81.S81D6Ops

public section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin


open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule
  CFSG.Blueprint.Chevalley

private theorem moved6_index : ∀ b : Fin e7Data.d, pr b theta = 0 →
    b ≠ (⟨8, by decide⟩ : Fin e7Data.d) →
    ∃ k : Fin 126, MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta = 0 ∧
      pr (⟨8, by decide⟩ : Fin e7Data.d) ((Tag.rootCertificate .E7).root k) = 1 ∧
      pr b ((Tag.rootCertificate .E7).root k) = -1 := by
  unfold pr
  decide +kernel

theorem exists_moving_root6 {b : Idx0} (hb : b ≠ a0) :
    ∃ γ ∈ Perp, pr (a0 : Fin e7Data.d) γ = 1 ∧ pr (b : Fin e7Data.d) γ = -1 := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk1, hk2, hk3⟩ := moved6_index (b : Fin e7Data.d) (mem_idx0.1 b.2)
    (fun h => hb (Subtype.ext h))
  have hγ : IsRoot .E7 ((Tag.rootCertificate .E7).root k) :=
    RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)
  exact ⟨(Tag.rootCertificate .E7).root k, ⟨hγ, hk1⟩, hk2, hk3⟩

theorem moved6_witness {K : Type} [Field K] [CharP K 2] {b : Idx0}
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Perp)
    (h1 : pr (a0 : Fin e7Data.d) γ = 1) (h2 : pr (b : Fin e7Data.d) γ = -1) :
    ∃ s ∈ rootSet0 K, ∃ b' : Idx0, ∀ v : W K, (s v - v) b' = v b := by
  have hb' : pr (shiftW γ b : Fin e7Data.d) γ = 1 := by
    rw [shiftW_val hγ h2]
    exact pr_shift_self hγ.1 h2
  have hbb : shiftW (-γ) (shiftW γ b) = b := by
    apply Subtype.ext
    have h4 : pr (shiftW γ b : Fin e7Data.d) (-γ) = -1 := by rw [pr_neg, hb']
    rw [shiftW_val (neg_mem_Perp hγ) h4, shiftW_val hγ h2, shift_neg_shift hγ.1 h2]
  refine ⟨vAut0 K (xuWUnit hγ 1), ⟨γ, hγ, h1, 1, fun w => xuWUnit_induces hγ 1 w⟩,
    shiftW γ b, fun v => ?_⟩
  have key := xuWUnit_apply_coord hγ 1 v (shiftW γ b)
  rw [if_pos hb', hbb, one_mul] at key
  rw [Finsupp.sub_apply, vAut0_apply, key]
  ring

theorem fix_rootRad0 {K : Type} [Field K] [CharP K 2] (v : W K)
    (h : ∀ u ∈ rootRad0 K, u v = v) : v ∈ Submodule.span K {p0 K} := by
  rw [Submodule.mem_span_singleton]
  refine ⟨v a0, ?_⟩
  ext b
  by_cases hb : b = a0
  · subst hb
    simp [p0]
  · obtain ⟨γ, hγ, h1, h2⟩ := exists_moving_root6 hb
    obtain ⟨s, hs, _, hsb⟩ := moved6_witness (K := K) hγ h1 h2
    have h3 := hsb v
    rw [h s (Subgroup.subset_closure hs), sub_self] at h3
    simp [p0, Finsupp.single_apply, hb, ← h3]

end CFSG.RankThree.GF2n.Smith81.D6Spin
