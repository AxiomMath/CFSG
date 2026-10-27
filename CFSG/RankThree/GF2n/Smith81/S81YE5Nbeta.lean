module

public import CFSG.RankThree.GF2n.Smith81.S81YE5Weights
public import CFSG.RankThree.GF2n.Smith81.S81YE5Def

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE5

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.RootGen

variable
  {K : Type} [Field K]


@[expose] noncomputable def nBeta (K : Type) [Field K] (β : Fin (Tag.rank .E7) → ℤ) : G7 K :=
  e7Data_valid.xm K β 1 * e7Data_valid.xm K (-β) 1 * e7Data_valid.xm K β 1

theorem v7_add_self_eq_zero [CharP K 2] (v : V K) : v + v = 0 := by
  ext a
  rw [Finsupp.add_apply, Finsupp.zero_apply]
  exact CharTwo.add_self_eq_zero (v a)

theorem act7_xm_one_single [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (a : Fin e7Data.d) :
    act7 (e7Data_valid.xm K γ 1) (Finsupp.single a 1) =
      Finsupp.single a 1 + (if pr a γ = -1 then Finsupp.single (shift γ a) 1 else 0) := by
  rw [act7_xm, one_smul, rootOp_single (K := K) hγ]

theorem act7_nBeta_single [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    {ν : Fin e7Data.d} (h : pr ν β = -1) :
    act7 (nBeta K β) (Finsupp.single ν 1) = Finsupp.single (shift β ν) 1 := by
  have hβn : IsRoot .E7 (-β) := isRoot_neg hβ
  have h1 : ¬ pr ν (-β) = -1 := by rw [pr_neg, h]; norm_num
  have h2 : pr (shift β ν) β = 1 := pr_shift_self hβ h
  have h3 : pr (shift β ν) (-β) = -1 := by simp [pr_neg, h2]
  have h4 : shift (-β) (shift β ν) = ν := shift_neg_shift hβ h
  have h5 : ¬ pr (shift β ν) β = -1 := by rw [h2]; norm_num
  have hA := act7_xm_one_single (K := K) hβ ν
  have hB := act7_xm_one_single (K := K) hβn ν
  have hC := act7_xm_one_single (K := K) hβn (shift β ν)
  have hD := act7_xm_one_single (K := K) hβ (shift β ν)
  rw [if_pos h] at hA
  rw [if_neg h1, add_zero] at hB
  rw [if_pos h3, h4] at hC
  rw [if_neg h5, add_zero] at hD
  have hX : act7 (e7Data_valid.xm K (-β) 1) (act7 (e7Data_valid.xm K β 1) (Finsupp.single ν 1)) =
      Finsupp.single (shift β ν) 1 := by
    rw [hA, map_add, hB, hC, ← add_assoc,
      add_comm (Finsupp.single ν 1) (Finsupp.single (shift β ν) 1), add_assoc,
      v7_add_self_eq_zero, add_zero]
  unfold nBeta
  rw [act7_mul, act7_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hX, hD]

private theorem theta_perp_aux : ∀ k : Fin 126,
    (Tag.rootCertificate .E7).root k node1 = 0 →
      ((theta + (Tag.rootCertificate .E7).root k ≠ 0) ∧
        (theta + -((Tag.rootCertificate .E7).root k) ≠ 0)) ∧
      ∀ k' : Fin 126,
        ((Tag.rootCertificate .E7).root k' ≠ theta + (Tag.rootCertificate .E7).root k) ∧
        ((Tag.rootCertificate .E7).root k' ≠ theta + -((Tag.rootCertificate .E7).root k)) := by
  decide +kernel

theorem theta_add_perp_facts {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) :
    (¬ IsRoot .E7 (theta + β) ∧ theta + β ≠ 0) ∧
      (¬ IsRoot .E7 (theta + -β) ∧ theta + -β ≠ 0) := by
  obtain ⟨hβr, hβ1⟩ := perp_iff.1 hβ
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hβr
  have hk126 : k < 126 := by omega
  obtain ⟨⟨hz1, hz2⟩, hnr⟩ := theta_perp_aux ⟨k, hk126⟩ hβ1
  refine ⟨⟨fun hr => ?_, hz1⟩, ⟨fun hr => ?_, hz2⟩⟩
  · obtain ⟨k', hk', hδ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hr
    have hk'126 : k' < 126 := by omega
    exact (hnr ⟨k', hk'126⟩).1 hδ
  · obtain ⟨k', hk', hδ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hr
    have hk'126 : k' < 126 := by omega
    exact (hnr ⟨k', hk'126⟩).2 hδ

theorem nBeta_comm_theta [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) (a : K) :
    nBeta K β * e7Data_valid.xm K theta a = e7Data_valid.xm K theta a * nBeta K β := by
  obtain ⟨hnr1, hne1⟩ := (theta_add_perp_facts hβ).1
  obtain ⟨hnr2, hne2⟩ := (theta_add_perp_facts hβ).2
  have hβr : IsRoot .E7 β := (perp_iff.1 hβ).1
  have hc1 : Commute (e7Data_valid.xm K theta a) (e7Data_valid.xm K β 1) :=
    commutatorElement_eq_one_iff_commute.1
      ((e7Data_valid.commutator_xm K isRoot_theta hβr hne1).2 hnr1 a 1)
  have hc2 : Commute (e7Data_valid.xm K theta a) (e7Data_valid.xm K (-β) 1) :=
    commutatorElement_eq_one_iff_commute.1
      ((e7Data_valid.commutator_xm K isRoot_theta (isRoot_neg hβr) hne2).2 hnr2 a 1)
  have hc : Commute (e7Data_valid.xm K theta a) (nBeta K β) := by
    unfold nBeta
    exact (hc1.mul_right hc2).mul_right hc1
  exact hc.symm.eq

theorem exists_levi_move [CharP K 2] {μ γ : Fin e7Data.d} (hμ : pr μ theta = 1)
    (hγ : pr γ theta = 1) :
    ∃ n : G7 K, (∀ a : K, n * e7Data_valid.xm K theta a = e7Data_valid.xm K theta a * n) ∧
      act7 n (Finsupp.single μ 1) = Finsupp.single γ 1 := by
  rcases exists_two_steps hμ hγ with h | ⟨β, hβP, hμβ, hshift⟩ |
    ⟨β₁, β₂, ν, hβ₁P, hμβ₁, hν, hβ₂P, hνβ₂, hshift⟩
  · subst h
    exact ⟨1, fun a => by simp, by simp [act7_one]⟩
  · refine ⟨nBeta K β, fun a => nBeta_comm_theta hβP a, ?_⟩
    rw [act7_nBeta_single (K := K) (perp_iff.1 hβP).1 hμβ, hshift]
  · refine ⟨nBeta K β₂ * nBeta K β₁, fun a => ?_, ?_⟩
    · have hc₁ : Commute (nBeta K β₁) (e7Data_valid.xm K theta a) := nBeta_comm_theta hβ₁P a
      have hc₂ : Commute (nBeta K β₂) (e7Data_valid.xm K theta a) := nBeta_comm_theta hβ₂P a
      exact hc₂.mul_left hc₁
    · rw [act7_mul, LinearEquiv.mul_apply,
        act7_nBeta_single (K := K) (perp_iff.1 hβ₁P).1 hμβ₁, hν,
        act7_nBeta_single (K := K) (perp_iff.1 hβ₂P).1 hνβ₂, hshift]

end CFSG.RankThree.GF2n.Smith81.RootGenE5
