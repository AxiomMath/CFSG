module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructNorm

public section

namespace CFSG.Quasithin.H13.F431.D4q.Struct

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Setup.X6
  CFSG.Quasithin.H13.Sec53F.Yam

set_option linter.unusedSectionVars false

section Field

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ}

theorem charP_two_of_card (hK : Nat.card K = (2 ^ f) ^ 3) : CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])

theorem sigma_cube (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))
    (c : K) : σ (σ (σ c)) = c := by
  have h : ∀ c, σ c = c ^ (2 ^ f) := hσ
  have hc : 2 ^ f * (2 ^ f * 2 ^ f) = Nat.card K := by rw [hK]; ring
  have := Fintype.ofFinite K
  rw [h, h, h, ← pow_mul, ← pow_mul, hc, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

end Field

section Iso


variable {D : Type} [Group D] {G : Type} [Group G] {M1 M2 : Subgroup G}

theorem map_trans_eq {X Y Z : Type} [Group X] [Group Y] [Group Z] (S : Subgroup X) (e : X ≃* Y)
    (e' : Y ≃* Z) : S.map (e.trans e').toMonoidHom = (S.map e.toMonoidHom).map e'.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem exists_std_iso {f : ℕ} (hD : ChevalleyExceptionalModel D .trialityD4 2 f)
    (E : LieExt D M1 M2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), 1 ≤ f ∧ Nat.card K = (2 ^ f) ^ 3 ∧
      (∀ c, σ.toRingHom c = c ^ (2 ^ f)) ∧
      ∃ ε : D ≃* Cm σ, E.TD.map ε.toMonoidHom = Ust σ ∧
        ((E.P1.map ε.toMonoidHom = Pst0 σ ∧ E.P2.map ε.toMonoidHom = Pst1 σ) ∨
          (E.P1.map ε.toMonoidHom = Pst1 σ ∧ E.P2.map ε.toMonoidHom = Pst0 σ)) := by
  obtain ⟨hf, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hD
  have hS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf hK (fun c => hσ c)
  obtain ⟨c, hTD, hP⟩ := hS.pair e E.yam
  refine ⟨K, hF, hFin, σ, hf, hK, fun c => hσ c, e.trans (MulAut.conj c⁻¹), ?_, ?_⟩
  · rw [map_trans_eq, hTD]
    exact map_conj_conj_inv _ c
  · rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [map_trans_eq, map_trans_eq, h1, h2, map_conj_conj_inv, map_conj_conj_inv]
      exact ⟨rfl, rfl⟩
    · right
      rw [map_trans_eq, map_trans_eq, h1, h2, map_conj_conj_inv, map_conj_conj_inv]
      exact ⟨rfl, rfl⟩

end Iso

end CFSG.Quasithin.H13.F431.D4q.Struct
