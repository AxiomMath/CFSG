module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamNSetup
public import CFSG.Quasithin.Background.F6GoldschmidtList

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

namespace GoldAmN

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem card_pCore_eq_card_pCoreOf (H : Subgroup D) :
    Nat.card ↥(Open.pCore 2 ↥H) = Nat.card ↥(pCoreOf 2 H) :=
  Nat.card_congr ((Open.pCore 2 ↥H).equivMapOfInjective H.subtype H.subtype_injective).toEquiv

omit [Finite D] in
theorem nonempty_mulEquiv_perm_three_of_card_pCoreOf (H : Subgroup D)
    (hq : Nonempty (↥H ⧸ Open.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)))
    (hQ : Nat.card ↥(pCoreOf 2 H) = 1) :
    Nonempty (↥H ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := hq
  have hbot : Open.pCore 2 ↥H = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [card_pCore_eq_card_pCoreOf]; exact hQ)
  exact ⟨((QuotientGroup.quotientBot).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e⟩

theorem isGoldCaseI_of_card_two (h : IsGoldschmidtAmalgam G₁ G₂)
    (hT : Nat.card ↥(G₁ ⊓ G₂) = 2) : IsGoldCaseI G₁ G₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(pCoreOf 2 G₁) = 1 := by
    have := card_inf_eq_two_mul_left h.toIsGoldschmidtTriple
    omega
  have h2 : Nat.card ↥(pCoreOf 2 G₂) = 1 := by
    have := card_inf_eq_two_mul_right h.toIsGoldschmidtTriple
    omega
  exact ⟨nonempty_mulEquiv_perm_three_of_card_pCoreOf G₁ h.quotient₁ h1,
    ⟨mulEquivOfPrimeCardEq hT (by simp)⟩,
    nonempty_mulEquiv_perm_three_of_card_pCoreOf G₂ h.quotient₂ h2⟩

theorem nonempty_mulEquiv_dihedral_six_left (h : IsGoldschmidtAmalgam G₁ G₂)
    (hT : Nat.card ↥(G₁ ⊓ G₂) = 4) : Nonempty (↥G₁ ≃* DihedralGroup 6) := by
  have hT' := h.toIsGoldschmidtTriple
  have hQ1 : Nat.card ↥(pCoreOf 2 G₁) = 2 := by
    have := card_inf_eq_two_mul_left hT'
    omega
  have hne := pCoreOf_ne_of_card_ne h (by omega)
  have hRcard := card_inf_pCoreOf_left hT' hne
  have hR : pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ = ⊥ := Subgroup.eq_bot_of_card_eq _ (by omega)
  have hsq : ∀ t ∈ G₁ ⊓ G₂, t ^ 2 = 1 := by
    intro t ht
    have h1 := sq_mem_of_relIndex_two (pCoreOf_le_inf_left hT') inf_le_normalizer_left
      (relIndex_pCoreOf_left hT') ht
    have h2 := sq_mem_of_relIndex_two (pCoreOf_le_inf_right hT') inf_le_normalizer_right
      (relIndex_pCoreOf_right hT') ht
    have : t ^ 2 ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ := ⟨h1, h2⟩
    rw [hR] at this
    exact this
  obtain ⟨q, hq, hq1⟩ := exists_ne_one_of_card_two hQ1
  have hcentral : ∀ g ∈ G₁, ∀ q' ∈ pCoreOf 2 G₁, g * q' * g⁻¹ = q' := by
    intro g hg q' hq'
    have hgq : g * q' * g⁻¹ ∈ pCoreOf 2 G₁ :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₁ hg) q').mp hq'
    rcases eq_one_or_eq_of_card_two hQ1 hq hq1 hq' with h0 | h0
    · rw [h0]; group
    · rw [h0] at hgq ⊢
      rcases eq_one_or_eq_of_card_two hQ1 hq hq1 hgq with h1 | h1
      · exfalso
        apply hq1
        have := congrArg (fun z => g⁻¹ * z * g) h1
        simpa [mul_assoc] using this
      · exact h1
  have hqsq : q ^ 2 = 1 := by
    have := orderOf_dvd_natCard (⟨q, hq⟩ : pCoreOf 2 G₁)
    rw [Subgroup.orderOf_mk, hQ1] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hqord : orderOf q = 2 := by
    have hdvd : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one hqsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h0 | h0
    · exact absurd (orderOf_eq_one_iff.mp h0) hq1
    · exact h0
  have hnc : ¬ CharTwo G₁ := by
    intro hc
    have hle : G₁ ≤ pCoreOf 2 G₁ := by
      intro g hg
      refine hc ⟨hg, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro q' hq'
      have := hcentral g hg q' hq'
      calc q' * g = (g * q' * g⁻¹) * g := by rw [this]
        _ = g * q' := by group
    have h12 : Nat.card ↥G₁ = 12 := by rw [card_left hT', hT]
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨x, hxG, hx3, -, hxinv⟩ := exists_order_three_centralizing G₁ h.quotient₁ hnc
  obtain ⟨σ, hσT, hσQ⟩ := exists_mem_not_mem_of_card_lt (Q := pCoreOf 2 G₁) (T := G₁ ⊓ G₂)
    (by omega)
  have hσG : σ ∈ G₁ := hσT.1
  have hσ2 : σ ^ 2 = 1 := hsq σ hσT
  have hσx : σ * x * σ⁻¹ = x⁻¹ :=
    hxinv σ hσG hσQ (by rw [hσ2]; exact (pCoreOf 2 G₁).one_mem)
  have hσq : σ * q * σ⁻¹ = q⁻¹ := by
    rw [hcentral σ hσG q hq]
    exact (inv_eq_of_mul_eq_one_right (by simpa [sq] using hqsq)).symm
  have hxq : x * q = q * x := by
    have := hcentral x hxG q hq
    calc x * q = x * q * x⁻¹ * x := by group
      _ = q * x := by rw [this]
  have hcard : Nat.card ↥G₁ = 6 * orderOf q := by rw [card_left hT', hT, hqord]
  have := nonempty_mulEquiv_dihedral_vertex G₁ h.quotient₁ hxG hq hσG hx3 hxq hσQ hσ2 hσx hσq hcard
  rw [hqord] at this
  exact this

theorem isGoldCaseII_of_card_four (h : IsGoldschmidtAmalgam G₁ G₂)
    (hT : Nat.card ↥(G₁ ⊓ G₂) = 4) : IsGoldCaseII G₁ G₂ := by
  have hT' := h.toIsGoldschmidtTriple
  have hQ1 : Nat.card ↥(pCoreOf 2 G₁) = 2 := by
    have := card_inf_eq_two_mul_left hT'
    omega
  have hne := pCoreOf_ne_of_card_ne h (by omega)
  have hRcard := card_inf_pCoreOf_left hT' hne
  have hR : pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ = ⊥ := Subgroup.eq_bot_of_card_eq _ (by omega)
  have hsq : ∀ t ∈ G₁ ⊓ G₂, t ^ 2 = 1 := by
    intro t ht
    have h1 := sq_mem_of_relIndex_two (pCoreOf_le_inf_left hT') inf_le_normalizer_left
      (relIndex_pCoreOf_left hT') ht
    have h2 := sq_mem_of_relIndex_two (pCoreOf_le_inf_right hT') inf_le_normalizer_right
      (relIndex_pCoreOf_right hT') ht
    have : t ^ 2 ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ := ⟨h1, h2⟩
    rw [hR] at this
    exact this
  refine ⟨nonempty_mulEquiv_dihedral_six_left h hT, nonempty_mulEquiv_klein_subgroup _ hT hsq, ?_⟩
  exact nonempty_mulEquiv_dihedral_six_left (amalgam_symm h) (by rw [inf_comm]; exact hT)

end GoldAmN

end F6

end CFSG.Quasithin
