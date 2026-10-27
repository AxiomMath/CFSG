module

public import CFSG.Quasithin.Vol2.Ch11SecAKN6
public import CFSG.Quasithin.Vol2.Ch11SecAKN4
public import CFSG.Quasithin.Vol2.Ch11SecAKN5

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint Matrix CFSG.SL2MinimalFaithful

theorem factModulesSL3_holds : FactModulesSL3 := by
  rintro K₀ _ _ W _ _ hW ρ n hn - hperf hX hρ S B hS hSB hBperf ⟨F, _, _, hF, ⟨eB⟩⟩
  by_contra hall
  push Not at hall
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy, hρy⟩ := AKN.exists_odd_ne_one hperf hρ
  obtain ⟨V, _, _, -, -, σ, hσy, hσO, hσρ⟩ :=
    AKN.exists_section_of_ne hy (Nat.card W) W le_rfl hW ρ hρy
  obtain ⟨K, _, _, hK, θ, hθ, hθker⟩ := AKN.exists_theta hX
  have hK4 : 4 ≤ Nat.card K := hK ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  have hKchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  have hFchar : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
  have hFK : Nat.card F = Nat.card K := hF.trans hK.symm
  have hoddθ : Odd (Nat.card θ.ker) :=
    Odd.of_dvd_nat (by decide) ((Subgroup.card_dvd_of_le hθker).trans (C10KH.card_center_sl3_dvd K))
  set φ := QuotientGroup.mk' (CFSG.pCore 2 K₀) with hφ
  let σb : (K₀ ⧸ CFSG.pCore 2 K₀) →* MulAut V :=
    QuotientGroup.lift (CFSG.pCore 2 K₀) σ fun x hx => (MonoidHom.mem_ker).mpr (hσO x hx)
  have hσb : ∀ x, σb (φ x) = σ x := fun x => rfl
  have hσbt : σb.ker ≠ ⊤ := by
    intro h
    apply hσy
    have hm : φ y ∈ σb.ker := h ▸ Subgroup.mem_top _
    rwa [MonoidHom.mem_ker, hσb] at hm
  have h2el : ∀ x ∈ σb.ker, ∀ k : ℕ, x ^ 2 ^ k = 1 → x = 1 := fun x hx k hxk =>
    AKN.eq_one_of_ker hθ σb.normal_ker hσbt hx hxk
  set ψ : ↥B →* K₀ ⧸ CFSG.pCore 2 K₀ := φ.comp B.subtype with hψ
  have hker : ψ.ker = CFSG.pCore 2 ↥B := by
    apply le_antisymm
    · apply le_sSup
      refine ⟨ψ.normal_ker, fun b => ?_⟩
      have hb : ((b : ↥B) : K₀) ∈ CFSG.pCore 2 K₀ := (QuotientGroup.eq_one_iff _).mp b.2
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, hb⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
    · intro b hb
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨b, hb⟩
      have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hOpen : b ∈ CFSG.Open.pCore 2 ↥B := hb
      have hρb : ρ b = 1 := hall _ (Subgroup.mem_map_of_mem B.subtype hOpen)
      rw [MonoidHom.mem_ker]
      refine h2el _ ?_ k ?_
      · rw [MonoidHom.mem_ker]
        exact hσρ _ hρb
      · rw [← map_pow, hbk, map_one]
  have hrange : ψ.range = B.map φ := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  let eB₁ : ↥(B.map φ) ≃* SpecialLinearGroup (Fin 2) F :=
    (MulEquiv.subgroupCongr hrange).symm.trans
      ((QuotientGroup.quotientKerEquivRange ψ).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans eB))
  have hperfB₁ : ⁅B.map φ, B.map φ⁆ = B.map φ := by rw [← Subgroup.map_commutator, hBperf]
  have hB2 : ¬ IsPGroup 2 (B.map φ) := by
    intro h
    have hbot := C10KH.eq_bot_of_perfect_of_isPGroup hperfB₁ h
    have h1 : eB₁.symm (unipotent 1) = 1 :=
      Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp hbot _ (eB₁.symm (unipotent 1)).2)
    have h2 : unipotent (1 : F) = unipotent 0 := by
      rw [unipotent_zero, ← eB₁.apply_symm_apply (unipotent 1), h1, map_one]
    exact one_ne_zero (unipotent_injective h2)
  have hBcard : Nat.card (B.map φ) = Nat.card F * (Nat.card F ^ 2 - 1) :=
    (Nat.card_congr eB₁.toEquiv).trans (card_specialLinearGroup_fin_two F)
  have hS₁ : QuasithinUnique.IsSylowTwoOf (S.map φ) ⊤ := by
    refine ⟨le_top, hS.2.1.map φ, fun h2 => hS.2.2 ?_⟩
    rw [show ((S.map φ).subgroupOf ⊤).index = (S.map φ).relIndex ⊤ from rfl,
      Subgroup.relIndex_top_right] at h2
    rw [show (S.subgroupOf ⊤).index = S.relIndex ⊤ from rfl, Subgroup.relIndex_top_right]
    exact h2.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _))
  have hSB₁ : S.map φ ≤ Subgroup.normalizer ((B.map φ : Subgroup _) : Set _) :=
    (Subgroup.map_mono hSB).trans (Subgroup.le_normalizer_map φ)
  obtain ⟨hS₁card, Z₀, hZ₀S, hZ₀card, hZ₀c⟩ :=
    AKN.exists_center_of_isSylowTwoOf θ hθ hoddθ hK (by omega) hS₁
  set D := S.map φ ⊓ B.map φ with hD
  have hq1 : 1 ≤ n := by omega
  have hodd2 : Odd (Nat.card F ^ 2 - 1) := by
    rw [hF, ← pow_mul]
    obtain ⟨m, hm⟩ : ∃ m, n * 2 = m + 1 := ⟨n * 2 - 1, by omega⟩
    rw [hm, pow_succ]
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    exact ⟨2 ^ m - 1, by omega⟩
  have hDcard : Nat.card D = Nat.card F := by
    have hDp : IsPGroup 2 D := IsPGroup.to_inf_left hS₁.2.1
    obtain ⟨j, hj⟩ := hDp.exists_card_eq
    have hcop : ∀ m : ℕ, Nat.Coprime (2 ^ m) (Nat.card F ^ 2 - 1) := fun m =>
      Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd2)
    apply Nat.dvd_antisymm
    · have h1 : Nat.card D ∣ Nat.card F * (Nat.card F ^ 2 - 1) :=
        hBcard ▸ Subgroup.card_dvd_of_le inf_le_right
      rw [hj] at h1 ⊢
      exact (hcop j).dvd_of_dvd_mul_right h1
    · have h1 := AKN.card_sup_mul_card_inf hSB₁
      have h2 := Subgroup.relIndex_mul_card (H := S.map φ) (K := S.map φ ⊔ B.map φ)
      rw [inf_of_le_left le_sup_left] at h2
      have h3 : ¬ 2 ∣ (S.map φ).relIndex (S.map φ ⊔ B.map φ) := by
        intro h
        apply hS₁.2.2
        rw [show ((S.map φ).subgroupOf ⊤).index = (S.map φ).relIndex ⊤ from rfl,
          Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index (le_sup_left :
            S.map φ ≤ S.map φ ⊔ B.map φ)]
        exact h.mul_right _
      rw [← h2, hS₁card, hBcard, ← hFK] at h1
      have h4 : (S.map φ).relIndex (S.map φ ⊔ B.map φ) * Nat.card D =
          Nat.card F * (Nat.card F ^ 2 - 1) := by
        have hpos : 0 < Nat.card F ^ 3 := by rw [hF]; positivity
        apply Nat.eq_of_mul_eq_mul_left hpos
        rw [← h1]
        ring
      have h5 : Nat.card F ∣ (S.map φ).relIndex (S.map φ ⊔ B.map φ) * Nat.card D :=
        h4 ▸ dvd_mul_right _ _
      rw [hF] at h5 ⊢
      exact (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr
        (Nat.two_dvd_ne_zero.mp h3)))).dvd_of_dvd_mul_left h5
  have hq3 : Nat.card K < Nat.card (S.map φ) := by
    rw [hS₁card]
    have : 1 < Nat.card K := by omega
    calc Nat.card K = Nat.card K ^ 1 := (pow_one _).symm
      _ < Nat.card K ^ 3 := Nat.pow_lt_pow_right this (by norm_num)
  obtain ⟨s, hs, hsD, hsc⟩ :=
    AKN.exists_mem_not_mem_comm hq3 inf_le_left (hDcard.trans hFK).le hZ₀S hZ₀card hZ₀c
  obtain ⟨c, hc1, ⟨k, hck⟩, hcB⟩ := AKN.exists_two_element_centralizer (by omega) eB₁ hS₁.2.1 hSB₁
    hDcard hs hsD hsc
  have hcent : ∀ z ∈ θ.ker, ∀ g, z * g = g * z := fun z hz g =>
    (Subgroup.mem_center_iff.mp (hθker hz) g).symm
  exact AKN.false_of_centralizer θ hθ hcent hoddθ SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective hperfB₁ hB2 hc1 hck hcB

end CFSG.Quasithin.Vol2.Ch11.SecA
