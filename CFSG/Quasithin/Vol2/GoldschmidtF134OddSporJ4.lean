module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporJ4Core
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporCore
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.Blueprint

theorem not_sq_dvd_of_squarefree_of_coprime {p n c u : ℕ} (hp : p.Prime) (hc : Nat.Coprime p c)
    (hu : Squarefree u) (hn : n = c * u) : ¬ p ^ 2 ∣ n := by
  intro h
  have h1 : p ^ 2 ∣ u := (Nat.Coprime.pow_left 2 hc).dvd_of_dvd_mul_left (hn ▸ h)
  have h2 := hu p (by rw [← sq]; exact h1)
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp h2)

theorem exists_overgroup_model {X Γ : Type} [Group X] [Finite X] [Group Γ] [Finite Γ]
    (e : X ≃* Γ) {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤) {S H : Subgroup X}
    (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hSH : S ≤ H) :
    ∃ K : Subgroup Γ, S₀ ≤ K ∧ Nat.card K = Nat.card H ∧ Nat.card S₀ = Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' := isSylowTwoOf_map e (isSylowTwoOf_top_of hS2 hSi)
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hS'
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S₀ = (S.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg
    exact this.symm
  let ψ : X ≃* Γ := e.trans (MulAut.conj g)
  have hψ : S.map ψ.toMonoidHom = S₀ := by
    rw [hST, Subgroup.map_map]
    rfl
  refine ⟨H.map ψ.toMonoidHom, ?_, ?_, ?_⟩
  · rw [← hψ]
    exact Subgroup.map_mono hSH
  · exact (Nat.card_congr (H.equivMapOfInjective _ ψ.injective).toEquiv).symm
  · rw [← hψ]
    exact (Nat.card_congr (S.equivMapOfInjective _ ψ.injective).toEquiv).symm

theorem noPowerOvergroup_j4 :
    NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .J4) := by
  intro X _ _ ⟨e⟩ p a hp h5 ha H S hS2 hSi hSH hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := j4Facts.mat
  have hF := j4Facts
  let ψ : X ≃* J := e.trans (seedEquiv hM)
  have hX : Nat.card X = 86775571046077562880 := by
    rw [Nat.card_congr ψ.toEquiv, card_J hF]
  by_cases hp11 : p = 11
  · subst hp11
    have hP0card : Nat.card P0 = 2 ^ 21 := card_P0 hM hF
    have hP0i : ¬ 2 ∣ P0.index := by
      have h1 := P0.card_mul_index
      rw [hP0card, card_J hF] at h1
      have h2 : P0.index = 41377816699065 := by omega
      rw [h2]; norm_num
    have hP0syl : IsSylowTwoOf P0 ⊤ := isSylowTwoOf_top_of (IsPGroup.of_card hP0card) hP0i
    obtain ⟨K, hP0K, hKH, hSS⟩ := @exists_overgroup_model X ↥J inferInstance inferInstance
      inferInstance inferInstance ψ P0 hP0syl S H hS2 hSi hSH
    refine false_of_overgroup_J4 ha hP0K ?_
    rw [hKH, hH, ← hSS, hP0card]
  ·
    have hdvd : p ^ a ∣ Nat.card X := by
      have := Subgroup.card_subgroup_dvd_card H
      rw [hH] at this
      exact (Dvd.intro _ rfl).trans this
    have hsq : p ^ 2 ∣ Nat.card X := by
      rcases ha with rfl | rfl
      · exact hdvd
      · exact (pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans hdvd
    have hc : Nat.Coprime p (2 ^ 21 * 3 ^ 3 * 11 ^ 3) := by
      have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
      have h3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
      have h11 : Nat.Coprime p 11 := (Nat.coprime_primes hp (by norm_num)).mpr hp11
      exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ h2)
        (Nat.Coprime.pow_right _ h3)) (Nat.Coprime.pow_right _ h11)
    have hu : Squarefree 1151398745 := by
      rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
      norm_num
    exact not_sq_dvd_of_squarefree_of_coprime hp hc hu (by rw [hX]; norm_num) hsq

end CFSG.Quasithin.H13.NQCore
