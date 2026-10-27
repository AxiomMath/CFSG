module

public import CFSG.RankThree.GF2n.Smith81.S81YE4Def
public import CFSG.RankThree.GF2n.Smith81.S81YE5Nbeta
public import CFSG.RankThree.GF2n.Smith81.S81YE4Weights

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5

variable
  {K : Type} [Field K]


theorem nBeta_mem_LG [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) :
    nBeta K β ∈ LG K := by
  unfold nBeta
  have h1 : e7Data_valid.xm K β 1 ∈ LG K := mem_LG.2 (xu_mem_Lam hβ 1)
  have h2 : e7Data_valid.xm K (-β) 1 ∈ LG K := mem_LG.2 (xu_mem_Lam (neg_mem_Perp hβ) 1)
  exact mul_mem (mul_mem h1 h2) h1

private theorem theta4_perp4_aux : ∀ k : Fin 126,
    MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta4 = 0 →
      ((theta4 + (Tag.rootCertificate .E7).root k ≠ 0) ∧
        (theta4 + -((Tag.rootCertificate .E7).root k) ≠ 0)) ∧
      ∀ k' : Fin 126,
        ((Tag.rootCertificate .E7).root k' ≠ theta4 + (Tag.rootCertificate .E7).root k) ∧
        ((Tag.rootCertificate .E7).root k' ≠ theta4 + -((Tag.rootCertificate .E7).root k)) := by
  unfold MinData.toWeight
  decide +kernel

theorem theta4_add_perp4_facts {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp4) :
    (¬ IsRoot .E7 (theta4 + β) ∧ theta4 + β ≠ 0) ∧
      (¬ IsRoot .E7 (theta4 + -β) ∧ theta4 + -β ≠ 0) := by
  have hβr : IsRoot .E7 β := (perp_iff.1 (Perp4_subset_Perp hβ)).1
  have hβ4 : MinData.toWeight β ⬝ᵥ theta4 = 0 := (mem_Perp4.1 hβ).2
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hβr
  have hk126 : k < 126 := by omega
  obtain ⟨⟨hz1, hz2⟩, hnr⟩ := theta4_perp4_aux ⟨k, hk126⟩ hβ4
  refine ⟨⟨fun hr => ?_, hz1⟩, ⟨fun hr => ?_, hz2⟩⟩
  · obtain ⟨k', hk', hδ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hr
    have hk'126 : k' < 126 := by omega
    exact (hnr ⟨k', hk'126⟩).1 hδ
  · obtain ⟨k', hk', hδ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hr
    have hk'126 : k' < 126 := by omega
    exact (hnr ⟨k', hk'126⟩).2 hδ

theorem nBeta_comm_theta4 [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp4) (a : K) :
    nBeta K β * e7Data_valid.xm K theta4 a = e7Data_valid.xm K theta4 a * nBeta K β := by
  obtain ⟨⟨hnr1, hne1⟩, ⟨hnr2, hne2⟩⟩ := theta4_add_perp4_facts hβ
  have hβr : IsRoot .E7 β := (perp_iff.1 (Perp4_subset_Perp hβ)).1
  have hc1 : Commute (e7Data_valid.xm K theta4 a) (e7Data_valid.xm K β 1) :=
    commutatorElement_eq_one_iff_commute.1
      ((e7Data_valid.commutator_xm K isRoot_theta4 hβr hne1).2 hnr1 a 1)
  have hc2 : Commute (e7Data_valid.xm K theta4 a) (e7Data_valid.xm K (-β) 1) :=
    commutatorElement_eq_one_iff_commute.1
      ((e7Data_valid.commutator_xm K isRoot_theta4 (isRoot_neg hβr) hne2).2 hnr2 a 1)
  have hc : Commute (e7Data_valid.xm K theta4 a) (nBeta K β) := by
    unfold nBeta
    exact (hc1.mul_right hc2).mul_right hc1
  exact hc.symm.eq

theorem exists_levi_move4 [CharP K 2] {μ γ : Fin e7Data.d} (hμ : μ ∈ idx0) (hμ1 : pr μ theta4 = 1)
    (hγ : γ ∈ idx0) (hγ1 : pr γ theta4 = 1) :
    ∃ n : G7 K, n ∈ LG K ∧
      (∀ a : K, n * e7Data_valid.xm K theta4 a = e7Data_valid.xm K theta4 a * n) ∧
      act7 n (Finsupp.single μ 1) = Finsupp.single γ 1 := by
  rcases exists_two_steps4 hμ hμ1 hγ hγ1 with h | ⟨β, hβP, hμβ, hshift⟩ |
    ⟨β₁, β₂, ν, hβ₁P, hμβ₁, hν, hβ₂P, hνβ₂, hshift⟩
  · subst h
    exact ⟨1, (LG K).one_mem, fun a => by simp, by simp [act7_one]⟩
  · refine ⟨nBeta K β, nBeta_mem_LG (Perp4_subset_Perp hβP), fun a => nBeta_comm_theta4 hβP a, ?_⟩
    rw [act7_nBeta_single (K := K) (perp_iff.1 (Perp4_subset_Perp hβP)).1 hμβ, hshift]
  · refine ⟨nBeta K β₂ * nBeta K β₁,
      mul_mem (nBeta_mem_LG (Perp4_subset_Perp hβ₂P)) (nBeta_mem_LG (Perp4_subset_Perp hβ₁P)),
      fun a => ?_, ?_⟩
    · have hc₁ : Commute (nBeta K β₁) (e7Data_valid.xm K theta4 a) := nBeta_comm_theta4 hβ₁P a
      have hc₂ : Commute (nBeta K β₂) (e7Data_valid.xm K theta4 a) := nBeta_comm_theta4 hβ₂P a
      exact hc₂.mul_left hc₁
    · rw [act7_mul, LinearEquiv.mul_apply,
        act7_nBeta_single (K := K) (perp_iff.1 (Perp4_subset_Perp hβ₁P)).1 hμβ₁, hν,
        act7_nBeta_single (K := K) (perp_iff.1 (Perp4_subset_Perp hβ₂P)).1 hνβ₂, hshift]

end CFSG.RankThree.GF2n.Smith81.RootGenE4
