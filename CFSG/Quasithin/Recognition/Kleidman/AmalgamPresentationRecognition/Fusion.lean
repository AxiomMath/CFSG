module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.RecognitionClosure
public import Certificates.Certificate272038

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

noncomputable def fusGen (j : ℕ) : J3Model := ev (fusGl.getD j [])

noncomputable def fusS : Subgroup J3Model := Subgroup.closure (Set.range fun j : Fin 3 => fusGen j)

section Sylow


theorem card_fusS : Nat.card fusS = 2 ^ 7 := Certificates.certificate272038.1

theorem factorization_card_J3Model : (Nat.card J3Model).factorization 2 = 7 := by
  rw [card_J3Model', Nat.factorization_def _ Nat.prime_two]
  have : (50232960 : ℕ) = 2 ^ 7 * 392445 := by norm_num
  rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem sylow_eq_fusS : ∃ P : Sylow 2 J3Model, (P : Subgroup J3Model) = fusS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite J3Model := Nat.finite_of_card_ne_zero (by rw [card_J3Model']; norm_num)
  have hp : IsPGroup 2 fusS := IsPGroup.of_card card_fusS
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hcard : Nat.card P = 2 ^ 7 := by
    rw [Sylow.card_eq_multiplicity, factorization_card_J3Model]
  exact ⟨P, (Subgroup.eq_of_le_of_card_ge hP (by rw [card_fusS, hcard])).symm⟩

theorem one_class_involutions_J3Model : ∀ t : J3Model, t * t = 1 → t ≠ 1 →
    ∃ k : J3Model, k * uJ 3 * k⁻¹ = t := by
  intro t ht1 ht2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite J3Model := Nat.finite_of_card_ne_zero (by rw [card_J3Model']; norm_num)
  obtain ⟨P, hP⟩ := sylow_eq_fusS
  have hord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht2
  have hz : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq J3Model P Q
  have htQ : t ∈ (Q : Subgroup J3Model) := hQ (Subgroup.mem_zpowers t)
  rw [← hm, Sylow.smul_def] at htQ
  obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp htQ
  have hyS : y ∈ fusS := hP ▸ hy
  have hty : t = m * y * m⁻¹ := by simpa using hyt.symm
  have hyy : y * y = 1 := by
    have e : y = m⁻¹ * t * m := by rw [hty]; group
    rw [e]
    calc m⁻¹ * t * m * (m⁻¹ * t * m) = m⁻¹ * (t * t) * m := by group
      _ = 1 := by rw [ht1]; group
  have hy1 : y ≠ 1 := by
    intro h
    apply ht2
    rw [hty, h]
    group
  obtain ⟨k, hk⟩ := Certificates.certificate272038.2 y hyS hyy hy1
  refine ⟨m * k, ?_⟩
  rw [hty, ← hk]
  group

end Sylow

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
