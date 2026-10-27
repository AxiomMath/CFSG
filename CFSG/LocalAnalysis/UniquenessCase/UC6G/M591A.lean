module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.K591Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C632c
public import CFSG.LocalAnalysis.UniquenessCase.UC6M591A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC6.Mz614 (centralizer_singleton_le_normalizer_zpowers)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem OL_le_L : m.OL ≤ m.L := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem coprime_card_OL : Nat.Coprime m.r (Nat.card m.OL) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have h : Nat.Coprime m.r (Nat.card (CFSG.pPrimeCore m.r ↥m.L)) := CFSG.pPrimeCore_coprime_card
  rwa [← Subgroup.card_map_of_injective m.L.subtype_injective] at h

theorem mem_normalizer_OL {n : G} (hn : n ∈ normalizer (m.L : Set G)) :
    n ∈ normalizer (m.OL : Set G) := by
  refine mem_normalizer_of_forward_uc6 fun o ho => ?_
  obtain ⟨p, hp, rfl⟩ := ho
  have hfix : (CFSG.pPrimeCore m.r ↥m.L).map
      (Subgroup.normalizerMonoidHom m.L ⟨n, hn⟩).toMonoidHom = CFSG.pPrimeCore m.r ↥m.L :=
    Subgroup.characteristic_iff_map_eq.1 inferInstance _
  have hmem : Subgroup.normalizerMonoidHom m.L ⟨n, hn⟩ p ∈ CFSG.pPrimeCore m.r ↥m.L := by
    rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hp
  exact ⟨_, hmem, by simp⟩

theorem L_le_normalizer_OL : m.L ≤ normalizer (m.OL : Set G) := fun x hx =>
  m.mem_normalizer_OL (Subgroup.le_normalizer hx)

theorem not_L_le_M (h619 : m.C619) : ¬ m.L ≤ m.M := by
  intro hLM
  apply m.hZ.not_le
  have : m.H ≤ m.M := by
    rw [h619]
    exact sup_le hLM inf_le_right
  exact this

theorem normalizer_le_M_of_le_EL (h632 : m.C632) {B : Subgroup G} (hB : B ≤ m.EL) (hB1 : B ≠ ⊥) :
    normalizer (B : Set G) ≤ m.M :=
  (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 m.r m.EL m.M).1 h632 B hB
    (one_le_pRank_of_ne_bot m.hr (m.isPGroup_of_le_A_inf_L hB) hB1)

theorem normalizer_le_M_of_E_le (h63 : R6_3 Dat) (h620 : m.C620)
    (h632 : m.C632) {Q : Subgroup G} (hQp : IsPGroup 2 Q) (hQ : Q ≠ ⊥)
    (hEQ : m.EL ≤ normalizer (Q : Set G)) : normalizer (Q : Set G) ≤ m.M := by
  have hE₀M : m.A ⊓ m.L ≤ m.M := fun a ha => m.R_le_M (m.A_le_R ha.1)
  have hU := h63 m.r m.hr m.d.odd (m.A ⊓ m.L) hE₀M ((m.isElemAbelian_A).mono inf_le_left)
    (m.card_A_inf_L h620) h632
  have hloc : IsTwoLocal (normalizer (Q : Set G)) := ⟨Q, hQ, hQp, rfl⟩
  obtain ⟨N, hN, hQN⟩ := exists_rankThreeIsMaxTwoLocal_ge_uc6 hloc
  have hNM : N = m.M := by
    have hmem : N ∈ calMOf (m.A ⊓ m.L) := ⟨hN, hEQ.trans hQN⟩
    rw [hU] at hmem
    exact hmem
  exact hNM ▸ hQN

theorem OL_le_M (h620 : m.C620) (h632 : m.C632) : m.OL ≤ m.M := by
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity m.hr
    (A := m.EL) (X := m.OL) ((m.isElemAbelian_A).mono inf_le_left)
    (by rw [m.card_A_inf_L h620]) (fun e he => m.L_le_normalizer_OL he.2) m.coprime_card_OL
  rw [← hgen]
  refine iSup_le fun a => iSup_le fun haE => iSup_le fun ha1 => ?_
  intro x hx
  have hzp : zpowers a ≤ m.EL := Subgroup.zpowers_le.2 haE
  have hzne : zpowers a ≠ ⊥ := fun h => ha1 (Subgroup.zpowers_eq_bot.1 h)
  exact m.normalizer_le_M_of_le_EL h632 hzp hzne
    (centralizer_singleton_le_normalizer_zpowers a hx.2)

theorem odd_card_OL (h63 : R6_3 Dat) (h619 : m.C619) (h620 : m.C620)
    (h632 : m.C632) : ¬ 2 ∣ Nat.card m.OL := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨T, hT, -, hET⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing m.hr
    Nat.prime_two (A := m.EL) (M := m.OL) (Q := ⊥)
    (m.isPGroup_of_le_A_inf_L le_rfl) ((Nat.Prime.coprime_iff_not_dvd m.hr).1 m.coprime_card_OL)
    (fun e he => m.L_le_normalizer_OL he.2) bot_le (IsPGroup.of_card (n := 0) (by simp))
    (fun e _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      simp [mul_inv_eq_one])
  obtain ⟨P, hP⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hT
  have hSyl : IsSylowOf 2 T m.OL := ⟨P, hP⟩
  have hTne : T ≠ ⊥ := by
    intro hTb
    have hc := hSyl.card_eq
    rw [hTb, Subgroup.card_bot] at hc
    have hf : 1 ≤ (Nat.card m.OL).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2
    have : 2 ^ 1 ≤ 2 ^ (Nat.card m.OL).factorization 2 := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hNle := m.normalizer_le_M_of_E_le h63 h620 h632 hSyl.isPGroup hTne hET
  have hfr := frattini_of_isSylowOf m.OL_le_L m.L_le_normalizer_OL hSyl
  exact m.not_L_le_M h619 ((le_of_eq hfr).trans
    (sup_le (m.OL_le_M h620 h632) (fun x hx => hNle hx.2)))

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
