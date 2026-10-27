module

public import CFSG.Monster.B.Recog.GenericStrongEmbedding
public import CFSG.Goldschmidt.Steps.StrongEmb

public section

namespace CFSG.Monster.B.GSide

open CFSG.BenderSuzuki

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_le_of_isStronglyEmbeddedOrder {M : Subgroup G}
    (hM : IsStronglyEmbeddedOrder M) (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M) :
    Subgroup.normalizer (S : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro n hn
  by_contra hnM
  have hS : (S : Subgroup G) ≤ M ⊓ M.map (MulAut.conj n).toMonoidHom := by
    intro s hs
    refine ⟨hSM hs, Subgroup.mem_map.2 ⟨n⁻¹ * s * n, hSM ?_, ?_⟩⟩
    · have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (S : Set G)).inv_mem hn) s).1
        hs
      simpa using this
    · simp [MulAut.conj_apply, mul_assoc]
  have h2G : 2 ∣ Nat.card G :=
    (even_iff_two_dvd.1 hM.2.1).trans (Subgroup.card_subgroup_dvd_card M)
  have h2S : 2 ∣ Nat.card S := by
    rcases S.isPGroup'.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) (S.ne_bot_of_dvd_card h2G)
    · exact h
  exact (Nat.not_even_iff_odd.2 (hM.2.2 n hnM))
    (even_iff_two_dvd.2 (h2S.trans (Subgroup.card_dvd_of_le hS)))

theorem isStronglyEmbeddedOrder_iff {M : Subgroup G} :
    IsStronglyEmbeddedOrder M ↔ M ≠ ⊤ ∧ Even (Nat.card M) ∧
      (∀ t ∈ M, orderOf t = 2 → Subgroup.centralizer {t} ≤ M) ∧
      ∃ S : Sylow 2 G, Subgroup.normalizer (S : Set G) ≤ M := by
  constructor
  · intro hM
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hC : ∀ t ∈ M, orderOf t = 2 → Subgroup.centralizer {t} ≤ M := fun t htM ht =>
      CFSG.Goldschmidt.centralizer_le_of_stronglyEmbedded hM ht htM
    refine ⟨hM.1, hM.2.1, hC, ?_⟩
    obtain ⟨P, ⟨hP2, hPM⟩, hmax⟩ := Set.exists_max_image
      {Q : Subgroup G | IsPGroup 2 Q ∧ Q ≤ M} (fun Q => Nat.card Q) (Set.toFinite _)
      ⟨⊥, IsPGroup.of_bot, bot_le⟩
    have hP : P ≠ ⊥ := by
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 (even_iff_two_dvd.1 hM.2.1)
      have hu2 : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe, hu]
      have hZ : IsPGroup 2 (Subgroup.zpowers (u : G)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
      have := hmax _ ⟨hZ, Subgroup.zpowers_le.2 u.2⟩
      rw [Nat.card_zpowers, hu2] at this
      intro hbot
      rw [hbot, Subgroup.card_bot] at this
      omega
    obtain ⟨S, hS⟩ := CFSG.Monster.B.Recog.StrongEmbedding.exists_sylow_eq hC hP2 hPM hP
      fun Q hQ hQM => hmax Q ⟨hQ, hQM⟩
    exact ⟨S, normalizer_le_of_isStronglyEmbeddedOrder hM S (hS ▸ hPM)⟩
  · rintro ⟨hMtop, heven, hC, S, hN⟩
    exact CFSG.Monster.B.Recog.isStronglyEmbeddedOrder_of_centralizer_le hMtop heven hC S hN

end CFSG.Monster.B.GSide
