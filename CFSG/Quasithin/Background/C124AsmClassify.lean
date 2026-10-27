module

public import CFSG.Quasithin.Background.C124AsmQuot
public import CFSG.Quasithin.Background.C124AsmOrder
public import CFSG.Quasithin.Background.FFC4Ext
public import CFSG.Quasithin.Background.FFC4Real

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Vol2.Ch10.SecA
open scoped commutatorElement

@[expose] def ClassCases {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (U Z : Subgroup W)
    (m : ℕ) : Prop :=
  (m = 5 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    ∃ π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F) →* ↥H,
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 F)).RealizesVia H U Z π ∧
        Function.Injective π) ∨
  (m = 5 ∧ ∃ π : ↥(alternatingGroup (Fin 5)) →* ↥H,
    (FFModel.altDn 5).RealizesVia H U Z π ∧ Function.Injective π) ∨
  (m = 6 ∧ ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥H,
    (FFModel.altDn 6).RealizesVia H U Z π ∧ Function.Injective π) ∨
  (m = 7 ∧ ∃ π : ↥(alternatingGroup (Fin 7)) →* ↥H,
    (FFModel.altDn 7).RealizesVia H U Z π ∧ Function.Injective π) ∨
  (m = 6 ∧ TripleA6Six H U Z ∧ IsHat ↥H ↥(alternatingGroup (Fin 6))) ∨
  (m = 7 ∧ A7Four H U Z ∧ Nonempty (↥H ≃* ↥(alternatingGroup (Fin 7))))

section Classify

variable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {U Z : Subgroup W} {m : ℕ}

theorem card_eq_of_faithful {D : FFModel} (hD : D.Faithful) {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) : Nat.card ↥H = Nat.card D.Gam :=
  (Nat.card_congr (MulEquiv.ofBijective π ⟨FFC.injective_of_faithful_sec hD h, h.1⟩).toEquiv).symm

theorem sixteen_dvd_pow_mul {k : ℕ} (hk : 4 ≤ k) (a : ℕ) : 16 ∣ 2 ^ k * a :=
  Dvd.dvd.mul_right ((show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 hk) _

theorem eq_of_alt_model {n : ℕ} (hn : 5 ≤ n) (hm : 5 ≤ m) {Γ : Type} [Group Γ]
    (π : Γ →* ↥H) (hs : Function.Surjective π) (e : Γ ≃* ↥(alternatingGroup (Fin n)))
    (ψ : ↥H →* ↥(alternatingGroup (Fin m))) (hψ : Function.Surjective ψ) : n = m :=
  eq_of_surjective_alt hn hm ((ψ.comp π).comp e.symm.toMonoidHom)
    (hψ.comp (hs.comp e.symm.surjective))

theorem eq_five_of_card {z N : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7) (hz : Odd z)
    (hN : N = Nat.card ↥(alternatingGroup (Fin m)) * z) (h60 : N = 60) : m = 5 := by
  obtain ⟨k, rfl⟩ := hz
  rcases card_alt_cases hm with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hN <;> omega

theorem eq_six_of_card {z N : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7) (hz : Odd z)
    (hN : N = Nat.card ↥(alternatingGroup (Fin m)) * z) (h1080 : N = 1080) : m = 6 := by
  obtain ⟨k, rfl⟩ := hz
  rcases card_alt_cases hm with ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;> rw [h] at hN <;> omega

variable [Finite W]

theorem classify (hm : m = 5 ∨ m = 6 ∨ m = 7)
    (hz : ∃ z : ℕ, Odd z ∧ Nat.card ↥H = Nat.card ↥(alternatingGroup (Fin m)) * z)
    (hψ : ∃ ψ : ↥H →* ↥(alternatingGroup (Fin m)), Function.Surjective ψ)
    (hB : B42ModulePair H U Z) : ClassCases H U Z m := by
  obtain ⟨z, hzo, hzN⟩ := hz
  obtain ⟨ψ, hψs⟩ := hψ
  obtain ⟨h60, h16⟩ := sixty_dvd_not_sixteen_dvd hm hzo hzN
  have hm5 : 5 ≤ m := by omega
  rcases hB with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨K, _, _, hK, π, hπ⟩ := h
    have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    have hN : Nat.card ↥H = 2 ^ n * (2 ^ (2 * n) - 1) := by
      rw [card_eq_of_faithful (FFModel.nat_faithful _) hπ]
      exact card_statedSL_two_pow hK
    have hn : n = 2 := by
      rw [hN] at h60 h16
      rcases Nat.lt_or_ge n 4 with hn | hn
      · interval_cases n
        · simp at h16
        · norm_num at h60
        · rfl
        · norm_num at h60
      · exact absurd (sixteen_dvd_pow_mul hn _) h16
    subst hn
    have h60' : Nat.card ↥H = 60 := by rw [hN]; norm_num
    exact Or.inl ⟨eq_five_of_card hm hzo hzN h60', K, inferInstance, inferInstance,
      by rw [hK]; norm_num, π, hπ, hinj⟩
  ·
    obtain ⟨K, _, _, hK, π, hπ⟩ := h
    exfalso
    have hN : Nat.card ↥H = 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
      rw [card_eq_of_faithful (FFModel.nat_faithful _) hπ]
      exact (card_statedSL 3 K).trans (card_SL_three_pow hK)
    rw [hN] at h60 h16
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp at h16
      · norm_num at h60
    · exact h16 (sixteen_dvd_pow_mul (by omega) _)
  ·
    obtain ⟨K, _, _, hK, π, hπ⟩ := h
    exfalso
    have hN : Nat.card ↥H = 2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) := by
      rw [card_eq_of_faithful (FFModel.nat_faithful _) hπ]
      exact card_Sp4_pow hK
    rw [hN] at h16
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at h16
    · exact h16 (sixteen_dvd_pow_mul (by omega) _)
  ·
    obtain ⟨K, _, _, hK, π, hπ⟩ := h
    exfalso
    have hn : n ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card (α := K)
      rw [hK] at this
      omega
    have : CharP K 2 := Vol2.KGNat.charP_two_of_card hn hK
    have hN := card_eq_of_faithful (FFC.zornQ_faithful _ le_rfl) hπ
    have h64 := sixty_four_dvd_card_G2 (Nat.one_le_iff_ne_zero.2 hn) hK
    exact h16 (hN ▸ (show 16 ∣ 64 by norm_num).trans h64)
  ·
    obtain ⟨K, _, _, hK, π, hπ⟩ := h
    exfalso
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hdvd : Nat.card ↥H ∣ Nat.card ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
      Subgroup.card_dvd_of_surjective hπ.1
    have hle : ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ ≤ CFSG.Open.quasithinG2 K := by
      refine Subgroup.commutator_le.2 fun g hg h hh => ?_
      rw [commutatorElement_def]
      exact (CFSG.Open.quasithinG2 K).mul_mem ((CFSG.Open.quasithinG2 K).mul_mem
        ((CFSG.Open.quasithinG2 K).mul_mem hg hh) ((CFSG.Open.quasithinG2 K).inv_mem hg))
        ((CFSG.Open.quasithinG2 K).inv_mem hh)
    have h2 := (Subgroup.card_dvd_of_le hle).trans (card_G2_two hK2).dvd
    have : 60 ∣ 12096 := h60.trans (hdvd.trans h2)
    norm_num at this
  ·
    obtain ⟨π, hπ⟩ := h
    have hinj := FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
    have hnm : 5 = m := eq_of_alt_model (by norm_num) hm5 π hπ.1 (MulEquiv.refl _) ψ hψs
    subst hnm
    exact Or.inr (Or.inl ⟨rfl, π, hπ, hinj⟩)
  ·
    obtain ⟨π, hπ⟩ := h
    have hinj := FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
    have hnm : 6 = m := eq_of_alt_model (by norm_num) hm5 π hπ.1 (MulEquiv.refl _) ψ hψs
    subst hnm
    exact Or.inr (Or.inr (Or.inl ⟨rfl, π, hπ, hinj⟩))
  ·
    obtain ⟨π, hπ⟩ := h
    have hinj := FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
    have hnm : 7 = m := eq_of_alt_model (by norm_num) hm5 π hπ.1 (MulEquiv.refl _) ψ hψs
    subst hnm
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, π, hπ, hinj⟩)))
  ·
    have h' := h
    obtain ⟨α, π, hπ⟩ := h
    have hinj := FFC.injective_of_faithful_sec (FFC.a7Four_faithful α) hπ
    have hnm : 7 = m := eq_of_alt_model (by norm_num) hm5 π hπ.1 (MulEquiv.refl _) ψ hψs
    subst hnm
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, h', ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩))))
  ·
    have h' := h
    obtain ⟨K, _, _, Γ₀, hK, -, hhat, -, π, hπ⟩ := h
    have hinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful Γ₀) hπ
    let π' : ↥Γ₀ →* ↥H := π
    have e : ↥Γ₀ ≃* ↥H := MulEquiv.ofBijective π' ⟨hinj, hπ.1⟩
    have hN : Nat.card ↥H = 1080 := by
      obtain ⟨-, h3, ⟨e6⟩⟩ := hhat
      rw [← Nat.card_congr e.toEquiv, (Subgroup.center ↥Γ₀).card_eq_card_quotient_mul_card_subgroup,
        h3, Nat.card_congr e6.toEquiv, card_alt_six]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨eq_six_of_card hm hzo hzN hN, h', IsHat.of_mulEquiv e hhat⟩))))
  ·
    obtain ⟨K, _, _, hK, π, hπ⟩ := h
    exfalso
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hN : Nat.card ↥H = 20160 := by
      rw [card_eq_of_faithful (FFModel.nat_faithful _) hπ]
      exact (card_statedSL 4 K).trans (card_SL_four_of_two hK2)
    rw [hN] at h16
    exact h16 (by norm_num)
  ·
    obtain ⟨K, _, _, hK, π, hπ⟩ := h
    exfalso
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hN : Nat.card ↥H = 9999360 := by
      rw [card_eq_of_faithful (FFModel.nat_faithful _) hπ]
      exact (card_statedSL 5 K).trans (card_SL_five_of_two hK2)
    rw [hN] at h16
    exact h16 (by norm_num)
  ·
    obtain ⟨π, hπ⟩ := h
    exfalso
    have hN : Nat.card ↥H = 20160 := by
      rw [card_eq_of_faithful (FFC.extSq_faithful (by norm_num)) hπ]
      exact (card_statedSL 4 (ZMod 2)).trans (card_SL_four_of_two (Nat.card_zmod 2))
    rw [hN] at h16
    exact h16 (by norm_num)
  ·
    obtain ⟨π, hπ⟩ := h
    exfalso
    have hN : Nat.card ↥H = 9999360 := by
      rw [card_eq_of_faithful (FFC.extSq_faithful (by norm_num)) hπ]
      exact (card_statedSL 5 (ZMod 2)).trans (card_SL_five_of_two (Nat.card_zmod 2))
    rw [hN] at h16
    exact h16 (by norm_num)

end Classify

theorem spec4a_holds :
    ∀ (G : Type) [Group G] [Finite G] (X T V L R : Subgroup G) (m : ℕ) (hV : IsElemAbelian 2 V),
      Entry X T V L R m hV →
        CaseL2 hV L m ∨ CaseAlt5 hV L m ∨ CaseAlt6 hV L m ∨ CaseAlt7 hV L m ∨ CaseHat6 hV L m ∨
          CaseA7Four hV L m := by
  intro G _ _ X T V L R m hV E
  have hm : m = 5 ∨ m = 6 ∨ m = 7 := by
    rcases E.mcase with h | h | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  exact classify hm E.card (E.exists_surj_alt (by omega)) E.case1i.2.1

end CFSG.Quasithin.C124
