module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LieType.Chevalley

namespace Res148BD4

theorem eq_or_eq_inv_of_pow_three {C : Type*} [Group C] [Finite C] [IsCyclic C] {a b : C}
    (ha : orderOf a = 3) (hb3 : b ^ 3 = 1) : b = 1 ∨ b = a ∨ b = a⁻¹ := by
  classical
  have := Fintype.ofFinite C
  by_contra hne
  push Not at hne
  obtain ⟨hb1, hba, hbai⟩ := hne
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    omega
  have haa : a ≠ a⁻¹ := by
    intro h
    have h2 : a ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [h]; exact mul_inv_cancel a
    have := orderOf_dvd_of_pow_eq_one h2
    rw [ha] at this
    omega
  have hsub : ({1, a, a⁻¹, b} : Finset C) ⊆ Finset.univ.filter (fun x : C => x ^ 3 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · exact ha3
    · rw [inv_pow, ha3, inv_one]
    · exact hb3
  have hcard : ({1, a, a⁻¹, b} : Finset C).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hbai h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨haa, fun h => hba h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => ha1 h.symm, fun h => ha1 (inv_eq_one.mp h.symm), fun h => hb1 h.symm⟩
  have hle := Finset.card_le_card hsub
  have hcyc := IsCyclic.card_pow_eq_one_le (α := C) (n := 3) (by norm_num)
  rw [hcard] at hle
  omega

theorem mulAut_congr_conj {M N : Type*} [Group M] [Group N] (φ : M ≃* N) (s : M) :
    MulAut.congr φ (MulAut.conj s) = MulAut.conj (φ s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

section Certs


theorem exists_innerOn_of_trialityD4 {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ} {n : ℕ}
    (hm : ChevalleyExceptionalModel ↥S .trialityD4 2 n) {e a : Γ}
    (heN : e ∈ Subgroup.normalizer (S : Set Γ)) (haN : a ∈ Subgroup.normalizer (S : Set Γ))
    (he3 : e ^ 3 = 1) (ha3 : a ^ 3 = 1) (hout : ¬ InnerOn148 S e) :
    ∃ k : ℕ, InnerOn148 S (a * e ^ k) := by
  obtain ⟨K, _, _, _, σ, hK, hσ, -, hf, -, ⟨φ⟩⟩ :=
    Sec4.Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hm
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have : Finite (K ≃+* K) := inferInstance
  haveI : IsCyclic (K ≃+* K) := hcyc
  set N := Subgroup.normalizer (S : Set Γ) with hNdef
  set ψ : ↥N →* (K ≃+* K) :=
    Θ.comp ((MulAut.congr φ).toMonoidHom.comp S.normalizerMonoidHom) with hψ
  have hinner : ∀ x : ↥N, ψ x = 1 → InnerOn148 S x := by
    intro x hx
    have hmem : MulAut.congr φ (S.normalizerMonoidHom x) ∈ Θ.ker := hx
    rw [hker] at hmem
    obtain ⟨g, hg⟩ := hmem
    refine ⟨(φ.symm g : Γ), (φ.symm g).2, fun y hy => ?_⟩
    have h1 : S.normalizerMonoidHom x = MulAut.conj (φ.symm g) := by
      have h0 : S.normalizerMonoidHom x = (MulAut.congr φ).symm (MulAut.conj g) := by
        rw [hg, MulEquiv.symm_apply_apply]
      rw [h0]
      ext z
      change ((φ.symm (MulAut.conj g (φ z)) : ↥S) : Γ) = _
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply,
        MulAut.conj_apply]
    have h2 := congrArg (fun τ : MulAut ↥S => ((τ ⟨y, hy⟩ : ↥S) : Γ)) h1
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv] at h2
    exact h2
  have hinner' : ∀ x : ↥N, InnerOn148 S x → ψ x = 1 := by
    rintro x ⟨s, hs, hsx⟩
    have h1 : S.normalizerMonoidHom x = MulAut.conj (⟨s, hs⟩ : ↥S) := by
      ext z
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
      simpa using hsx z z.2
    change Θ (MulAut.congr φ (S.normalizerMonoidHom x)) = 1
    rw [h1, mulAut_congr_conj]
    have hmem : MulAut.conj (φ ⟨s, hs⟩) ∈ Θ.ker := by
      rw [hker]
      exact ⟨_, rfl⟩
    exact hmem
  set e' : ↥N := ⟨e, heN⟩ with he'def
  set a' : ↥N := ⟨a, haN⟩ with ha'def
  have hψe : ψ e' ≠ 1 := fun h => hout (hinner e' h)
  have hψe3 : ψ e' ^ 3 = 1 := by
    rw [← map_pow]
    have : e' ^ 3 = 1 := Subtype.ext (by simpa using he3)
    rw [this, map_one]
  have hψa3 : ψ a' ^ 3 = 1 := by
    rw [← map_pow]
    have : a' ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [this, map_one]
  have hord : orderOf (ψ e') = 3 := orderOf_eq_prime hψe3 hψe
  have hmemN : ∀ k : ℕ, a * e ^ k ∈ N := fun k => N.mul_mem haN (N.pow_mem heN k)
  have key : ∀ k : ℕ, ψ ⟨a * e ^ k, hmemN k⟩ = ψ a' * ψ e' ^ k := by
    intro k
    have : (⟨a * e ^ k, hmemN k⟩ : ↥N) = a' * e' ^ k := Subtype.ext (by simp [ha'def, he'def])
    rw [this, map_mul, map_pow]
  rcases eq_or_eq_inv_of_pow_three hord hψa3 with h1 | h1 | h1
  · refine ⟨0, ?_⟩
    have := hinner ⟨a * e ^ 0, hmemN 0⟩ (by rw [key, pow_zero, mul_one, h1])
    exact this
  · refine ⟨2, hinner ⟨a * e ^ 2, hmemN 2⟩ ?_⟩
    rw [key, h1, ← pow_succ', hψe3]
  · refine ⟨1, hinner ⟨a * e ^ 1, hmemN 1⟩ ?_⟩
    rw [key, h1, pow_one, inv_mul_cancel]

end Certs

end Res148BD4

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
