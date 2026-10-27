module

public import CFSG.Quasithin.Vol2.Ch11SecBK11E
public import CFSG.Quasithin.Vol2.Ch11SecBK11F
public import CFSG.RankThree.SubgroupLists.DicksonGL2
public import CFSG.Quasithin.Vol2.Ch11SecAKE17

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.RankThree.SubgroupLists (mem_statedSL_iff)
open CFSG.LieType.Universal.Unitary (conjTr SUid_eq_statedSU mem_SUid)

namespace BK11

theorem card_sylow_of_card {S : Type} [Group S] [Finite S] {R : Subgroup S}
    (hR : IsSylowTwoOf R ⊤) {N : ℕ} (hS : Nat.card S = N) (hN : N = 372000 ∨ N = 126000) :
    (N = 372000 → Nat.card R = 32) ∧ (N = 126000 → Nat.card R = 16) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hR2, hRidx⟩ := hR
  have hidx : ¬ 2 ∣ R.index := by rwa [← Subgroup.relIndex_top_right]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR2
  have hmul := R.card_mul_index
  rw [ha, hS] at hmul
  have ha6 : a ≤ 5 := by
    by_contra h
    have h64 : 2 ^ 6 ∣ N := (Nat.pow_dvd_pow 2 (by omega)).trans ⟨_, hmul.symm⟩
    rcases hN with rfl | rfl <;> norm_num at h64
  rw [ha]
  constructor
  · rintro rfl
    interval_cases a <;> first | rfl | (exfalso; apply hidx; norm_num at hmul ⊢; omega)
  · rintro rfl
    interval_cases a <;> first | rfl | (exfalso; apply hidx; norm_num at hmul ⊢; omega)

end BK11

open BK11 in
theorem factOuterLeviL35U35_holds : FactOuterLeviL35U35 := by
  intro S _ _ hS R B hR hRB hB hF
  classical
  have hR2 := hR.2.1
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases hS with h | h | h
  ·
    obtain ⟨K, _, _, hK, ⟨eS⟩⟩ := h
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 5 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (k := 1) (by norm_num) le_rfl (by rw [hK]; norm_num)
    have h2 : (2 : K) ≠ 0 := fun h => by
      have := (CharP.cast_eq_zero_iff K 5 2).mp (by exact_mod_cast h)
      norm_num at this
    have hN : Nat.card S = 372000 := by
      rw [Nat.card_congr (eS.trans (specialLinearGroupEquivStatedSL 3 K).symm).toEquiv,
        CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num), hK]
      decide
    have hR32 := (card_sylow_of_card hR hN (Or.inl rfl)).1 rfl
    have hdet : ∀ x ∈ StatedSL 3 K, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := fun x hx =>
      (mem_statedSL_iff x).mp hx
    have hΛ : (Finset.univ.erase (0 : K)).card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, hK]
    exact outerLevi_of_model h2 hdet bot_le
      (fun z hz => by rw [Subgroup.mem_bot.mp hz, one_pow])
      (eS.trans (QuotientGroup.quotientBot (G := ↥(StatedSL 3 K))).symm) (Finset.univ.erase 0)
      (fun z t P l m k _ ht _ hD _ => by
        rw [Finset.mem_erase]
        refine ⟨fun hl => ?_, Finset.mem_univ _⟩
        have hd := det_conj P t
        rw [hD, Matrix.det_diagonal, Fin.prod_univ_three, hdet t ht] at hd
        simp [hl] at hd)
      (by rw [hN]; norm_num) hR2 (by rw [hR32, hΛ]; norm_num) (by rw [hR32]; norm_num) hRB hB hF
  ·
    have hN : Nat.card S = 372000 := H13.NotLie.card_psl35 h
    have hR32 := (card_sylow_of_card hR hN (Or.inl rfl)).1 rfl
    obtain ⟨-, K, _, _, hK, ⟨eS⟩⟩ := h
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 5 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (k := 1) (by norm_num) le_rfl hK
    have h2 : (2 : K) ≠ 0 := fun h => by
      have := (CharP.cast_eq_zero_iff K 5 2).mp (by exact_mod_cast h)
      norm_num at this
    have hdet : ∀ x ∈ StatedSL 3 K, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := fun x hx =>
      (mem_statedSL_iff x).mp hx
    have hΛ : (Finset.univ.erase (0 : K)).card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, hK]
      norm_num
    exact outerLevi_of_model h2 hdet (scalars_le_center _) (scalars_pow_three hdet) eS
      (Finset.univ.erase 0)
      (fun z t P l m k _ ht _ hD _ => by
        rw [Finset.mem_erase]
        refine ⟨fun hl => ?_, Finset.mem_univ _⟩
        have hd := det_conj P t
        rw [hD, Matrix.det_diagonal, Fin.prod_univ_three, hdet t ht] at hd
        simp [hl] at hd)
      (by rw [hN]; norm_num) hR2 (by rw [hR32, hΛ]; norm_num) (by rw [hR32]; norm_num) hRB hB hF
  ·
    obtain ⟨-, K, _, _, hK, ⟨eS⟩⟩ := h
    have : CharP K 5 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (k := 2) (by norm_num) (by norm_num) (by rw [hK]; norm_num)
    have h2 : (2 : K) ≠ 0 := fun h => by
      have := (CharP.cast_eq_zero_iff K 5 2).mp (by exact_mod_cast h)
      norm_num at this
    have hN : Nat.card S = 126000 := by
      rw [Nat.card_congr eS.toEquiv]
      exact H13.NotLie.card_psu35 (by rw [hK]; norm_num)
    have hR16 := (card_sylow_of_card hR hN (Or.inr rfl)).2 rfl
    set σ := CFSG.LieType.BorelTits.unitaryInvolution K 5 1 with hσ
    have hmem : ∀ x ∈ StatedSU 3 (5 ^ 1) K, (x : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
        conjTr σ (x : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) = 1 := by
      intro x hx
      rw [← SUid_eq_statedSU hK 3] at hx
      exact mem_SUid.mp hx
    have hdet : ∀ x ∈ StatedSU 3 (5 ^ 1) K, (x : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      fun x hx => (hmem x hx).1
    have hΛ : ({1, -1} : Finset K).card ≤ 2 := Finset.card_le_two
    exact outerLevi_of_model h2 hdet (scalars_le_center _) (scalars_pow_three hdet) eS {1, -1}
      (fun z t P l m k hz ht hP hD hk => by
        have h1 := sigma_mul_eq_one h2 σ (hmem z hz).2 (hmem t ht).2 hP hD
        rw [hσ, CFSG.LieType.BorelTits.unitaryInvolution_apply] at h1
        have h6 : l ^ 6 = 1 := by rw [← h1]; ring
        have hc : (P⁻¹ * t * P) ^ 2 ^ k = 1 := by
          have := conj_pow (a := P⁻¹) (b := t) (i := 2 ^ k)
          rw [inv_inv] at this
          rw [this, hk, mul_one, inv_mul_cancel]
        have hc' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hc
        simp only [Units.val_pow_eq_pow_val, hD, Matrix.diagonal_pow, Units.val_one] at hc'
        have hlk : l ^ 2 ^ k = 1 := by simpa using hc'
        rcases eq_one_or_neg_one_of_pow h6 hlk with h | h <;> simp [h])
      (by rw [hN]; norm_num) hR2 (by rw [hR16]; omega) (by rw [hR16]; norm_num) hRB hB hF

theorem factOuterLevi_holds : FactOuterLevi :=
  factOuterLevi_of_cases factOuterLeviL225_holds factOuterLeviL35U35_holds

end CFSG.Quasithin.Vol2.Ch11.SecA
