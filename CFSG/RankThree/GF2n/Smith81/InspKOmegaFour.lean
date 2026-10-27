module

public import CFSG.RankThree.GF2n.Smith81.InspOrth
public import CFSG.RankThree.GF2n.Smith81.InspKOmega
public import CFSG.RankThree.GF2n.Smith81.InspKOmegaFourCard

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.RankOne
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.SeitzReduction.OmegaPilot
  CFSG.StandardType.KGOm Matrix

section CertBound


theorem KFact.exists_frame_pomega_plus_four {Y : Type} [Group Y] {D : Set Y} (hH : Hyp Y D)
    {f : ℕ} (hf : 2 ≤ f) (hL : LieModel Y .POmegaPlus 4 2 f)
    (hroot : ∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (Ψ : spinGroup (quadPlus 4 K) →* Y),
      Nat.card K = 2 ^ f ∧ Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      ∃ g : spinGroup (quadPlus 4 K),
        Ψ (g * KFact.stdLongRootPlus K (by norm_num : 3 ≤ 4) * g⁻¹) ∈ D := by
  classical
  have hsgn : StatedLieTag.POmegaPlus = .POmegaPlus ∨ StatedLieTag.POmegaPlus = .POmegaMinus :=
    Or.inl rfl
  obtain ⟨d₀, hd₀⟩ : D.Nonempty := by
    obtain ⟨d, hd, -⟩ := hH.nondeg
    exact ⟨d, hd⟩
  have hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d :=
    ⟨d₀, hd₀, KFact.exists_ne_mem_rootSet_of_card hH.root hf hroot hd₀⟩
  obtain ⟨hc, hs, hm⟩ := largeClosures hH hl
  have h := arsHyp_rootClass hH hc hs hm
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have hcardR : ∀ E ∈ rootClass D, Nat.card E = 2 ^ f := by
    rintro E ⟨d, hd, rfl⟩
    exact hroot d hd
  have hne2 : ∀ A ∈ rootClass D, Nat.card A ≠ 2 := by
    intro A hA h2
    have h3 := hcardR A hA
    rw [h2] at h3
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  rcases ARS.output_of_hyp Y (rootClass D) h with ⟨m', hm2, A, B, hX, hgen⟩ |
      ⟨m', hm4, A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | hns
  · exfalso
    rcases Nat.lt_or_ge m' 3 with hm3 | hm3
    · obtain rfl : m' = 2 := by omega
      obtain ⟨f', hf', -, hL'⟩ := hX.lieModel_A_two hR hiso hZ hgen
      exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
    · obtain ⟨f', hf', -, hL'⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
  · obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_D hR hiso hZ hm4 hgen
    obtain ⟨-, hnm, -⟩ := lieModel_POmega_two_unique hsgn hL hL'
    obtain ⟨f'', hf'', hE'', Ψ, hA, -, hsurj, hker⟩ := hX.exists_surjective_D hR hiso hm4 hgen
    have hf''f : f'' = f := by
      have h1 := hE'' _ ⟨d₀, hd₀, rfl⟩
      have h2 := hcardR _ ⟨d₀, hd₀, rfl⟩
      rw [h1] at h2
      exact Nat.pow_right_injective (le_refl 2) h2
    subst hnm
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h0 : 0 < 4 := by norm_num
    obtain ⟨d₁, hd₁, hd₁A⟩ := hX.memA ⟨0, h0⟩
    have hd₁mem : d₁ ∈ A ⟨0, h0⟩ := by
      rw [hd₁A]
      exact rootSet_subset_rootGroup D d₁ ⟨hd₁, fun _ _ => Iff.rfl⟩
    rw [← hA ⟨0, h0⟩] at hd₁mem
    obtain ⟨x, hx, hxd⟩ := Subgroup.mem_map.mp hd₁mem
    obtain ⟨i, j, hij, s, t, -, hXeq⟩ := exists_plusRootGroup_eq (K := GaloisField 2 f'')
      (by norm_num : 3 ≤ 4) (KFact.single_mem_roots_D ⟨0, h0⟩)
    have hx' : x ∈ ((plusFrame 4 (GaloisField 2 f'') (by omega)).longRoot hij s t).range := by
      rw [← hXeq]
      exact hx
    obtain ⟨c₀, rfl⟩ := hx'
    have hc₀ : Multiplicative.toAdd c₀ ≠ 0 := by
      intro h0'
      have hc1 : c₀ = 1 := by rw [← ofAdd_toAdd c₀, h0', ofAdd_zero]
      rw [hc1, map_one, map_one] at hxd
      have := hH.root.1 d₁ hd₁
      rw [← hxd, orderOf_one] at this
      omega
    obtain ⟨w, hw⟩ := exists_conj_longRoot_std (K := GaloisField 2 f'') (by norm_num : 3 ≤ 4)
      hij s t hc₀
    refine ⟨GaloisField 2 f'', inferInstance, inferInstance, inferInstance, Ψ, ?_, hsurj, hker, w,
      ?_⟩
    · rw [GaloisField.card 2 f'' (by omega), hf''f]
    · have hw' : w * KFact.stdLongRootPlus (GaloisField 2 f'') (by norm_num : 3 ≤ 4) * w⁻¹ =
          (plusFrame 4 (GaloisField 2 f'') (by omega)).longRoot hij s t c₀ := by
        have := hw
        rwa [ofAdd_toAdd] at this
      rw [hw', hxd]
      exact hd₁
  · exfalso
    obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E6 hR hiso hZ hgen
    exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
  · exfalso
    obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E7 hR hiso hZ hgen
    exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
  · exfalso
    obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E8 hR hiso hZ hgen
    exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
  · exfalso
    obtain ⟨-, hdata⟩ := hns
    rcases hdata with hS | ⟨⟨F⟩⟩
    · rcases KFact.exists_lieModel_of_sigmaEqLambda h hS hne2 with ⟨n', f', hL'⟩ | ⟨f', hL'⟩ |
          ⟨f', hL'⟩
      · exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
      · exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
      · exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
    · have hmem : Nat.card ((F.D.rootGroup (Pi.single F.i₀ 1)).map F.Ψ) = 2 ^ f :=
        hcardR _ F.mem
      rcases KFact.nslFrame_cases F hZ hf hmem with
        ⟨n, K, _, _, _, Ψ, hn, hK, hLm, -⟩ |
        ⟨n, K, _, _, b, c, hirr, Ψ, hn, hK, hLm, -⟩ | ⟨t, n, f', ht1, ht2, ht3, hL'⟩
      · exact absurd (lieModel_POmega_two_unique hsgn hL hLm).1 (by simp)
      · exact absurd (lieModel_POmega_two_unique hsgn hL hLm).1 (by simp)
      · exact ht3 (lieModel_POmega_two_unique hsgn hL hL').1

theorem KFact.exists_frame_pomega_minus_four {Y : Type} [Group Y] {D : Set Y} (hH : Hyp Y D)
    {f : ℕ} (hf : 2 ≤ f) (hL : LieModel Y .POmegaMinus 4 2 f)
    (hroot : ∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (Ψ : spinGroup (quadMinus 4 K b c) →* Y),
      Nat.card K = 2 ^ f ∧ Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      ∃ g : spinGroup (quadMinus 4 K b c),
        Ψ (g * KFact.stdLongRootMinus K (by norm_num : 4 ≤ 4) b c * g⁻¹) ∈ D := by
  classical
  have hsgn : StatedLieTag.POmegaMinus = .POmegaPlus ∨ StatedLieTag.POmegaMinus = .POmegaMinus :=
    Or.inr rfl
  obtain ⟨d₀, hd₀⟩ : D.Nonempty := by
    obtain ⟨d, hd, -⟩ := hH.nondeg
    exact ⟨d, hd⟩
  have hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d :=
    ⟨d₀, hd₀, KFact.exists_ne_mem_rootSet_of_card hH.root hf hroot hd₀⟩
  obtain ⟨hc, hs, hm⟩ := largeClosures hH hl
  have h := arsHyp_rootClass hH hc hs hm
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have hcardR : ∀ E ∈ rootClass D, Nat.card E = 2 ^ f := by
    rintro E ⟨d, hd, rfl⟩
    exact hroot d hd
  have hne2 : ∀ A ∈ rootClass D, Nat.card A ≠ 2 := by
    intro A hA h2
    have h3 := hcardR A hA
    rw [h2] at h3
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  rcases ARS.output_of_hyp Y (rootClass D) h with ⟨m', hm2, A, B, hX, hgen⟩ |
      ⟨m', hm4, A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | hns
  · exfalso
    rcases Nat.lt_or_ge m' 3 with hm3 | hm3
    · obtain rfl : m' = 2 := by omega
      obtain ⟨f', hf', -, hL'⟩ := hX.lieModel_A_two hR hiso hZ hgen
      exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
    · obtain ⟨f', hf', -, hL'⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
  · exfalso
    obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_D hR hiso hZ hm4 hgen
    exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
  · exfalso
    obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E6 hR hiso hZ hgen
    exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
  · exfalso
    obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E7 hR hiso hZ hgen
    exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
  · exfalso
    obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E8 hR hiso hZ hgen
    exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
  · obtain ⟨-, hdata⟩ := hns
    rcases hdata with hS | ⟨⟨F⟩⟩
    · exfalso
      rcases KFact.exists_lieModel_of_sigmaEqLambda h hS hne2 with ⟨n', f', hL'⟩ | ⟨f', hL'⟩ |
          ⟨f', hL'⟩
      · exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
      · exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
      · exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 (by simp)
    · have hmem : Nat.card ((F.D.rootGroup (Pi.single F.i₀ 1)).map F.Ψ) = 2 ^ f :=
        hcardR _ F.mem
      rcases KFact.nslFrame_cases F hZ hf hmem with
        ⟨n, K, _, _, _, Ψ, hn, hK, hLm, -⟩ |
        ⟨n, K, _, _, b, c, hirr, Ψ, hn, hK, hLm, hsurj, hker, i, hi, hmemR⟩ |
        ⟨t, n, f', ht1, ht2, ht3, hL'⟩
      · exact absurd (lieModel_POmega_two_unique hsgn hL hLm).1 (by simp)
      · obtain ⟨-, hnm, -⟩ := lieModel_POmega_two_unique hsgn hL hLm
        subst hnm
        haveI hch : CharP K 2 := KFact.charP_two_of_card (by omega) hK
        obtain ⟨d₁, hd₁, hmd⟩ := hmemR
        have hd₁mem : d₁ ∈ Subgroup.map Ψ
            ((minusDatum 4 hirr).rootGroup (Pi.single i 1)) := by
          rw [hmd]
          exact rootSet_subset_rootGroup D d₁ ⟨hd₁, fun _ _ => Iff.rfl⟩
        obtain ⟨x, hx, hxd⟩ := Subgroup.mem_map.mp hd₁mem
        have hx1 : x ≠ 1 := by
          rintro rfl
          rw [map_one] at hxd
          have := hH.root.1 d₁ hd₁
          rw [← hxd, orderOf_one] at this
          omega
        obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff 4 hirr
          (succ_ne_of_lt 4 hi) true false (toStdB_single_of_lt' 4 hi)).mp hx
        have ha : a ≠ 0 := by
          rintro rfl
          exact hx1 (map_one _)
        obtain ⟨w, hw⟩ := exists_conj_longRoot_std_minus (by norm_num : 4 ≤ 4) hirr
          (succ_ne_of_lt 4 hi) true false ha
        refine ⟨K, inferInstance, inferInstance, hch, b, c, hirr, Ψ, hK, hsurj, hker, w, ?_⟩
        have hw' : w * KFact.stdLongRootMinus K (by norm_num : 4 ≤ 4) b c * w⁻¹ =
            (minusFrame 4 b c).longRoot (succ_ne_of_lt 4 hi) true false (.ofAdd a) := hw
        rw [hw', hxd]
        exact hd₁
      · exact absurd (lieModel_POmega_two_unique hsgn hL hL').1 ht2


theorem kCOmegaFour_holds : KCOmegaFourStatement := by
  intro Y _ D f hH hf hroot
  have hf1 : 1 ≤ f := by omega
  refine ⟨fun hL d hd => ?_, fun hL d hd => ?_⟩
  · obtain ⟨K, _, _, _, Ψ, hK, hsurj, hker, g, hgD⟩ :=
      KFact.exists_frame_pomega_plus_four hH hf hL hroot
    have hinj : Function.Injective Ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact le_bot_iff.mp (hker.trans
        (CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo
          (by norm_num)).le)
    obtain ⟨w, hw⟩ := KFact.exists_conj_preimage hH Ψ hsurj g hgD hd
    let e : spinGroup (quadPlus 4 K) ≃* Y := MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
    have hcard : Nat.card (Subgroup.centralizer ({d} : Set Y)) =
        Nat.card (Subgroup.centralizer ({KFact.stdLongRootPlus K (by norm_num : 3 ≤ 4)} :
          Set (spinGroup (quadPlus 4 K)))) := by
      rw [hw]
      exact KFact.card_centralizer_conj_mulEquiv e w _
    rw [hcard]
    exact KFact.card_centralizer_longRoot_plus_four_dvd hf hK
      (KFact.card_spinGroup_quadPlus (by norm_num) hf1 hK)
  · obtain ⟨K, _, _, _, b, c, hirr, Ψ, hK, hsurj, hker, g, hgD⟩ :=
      KFact.exists_frame_pomega_minus_four hH hf hL hroot
    have hinj : Function.Injective Ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact le_bot_iff.mp (hker.trans
        (CFSG.StandardType.PsiDiag.SpinM.center_eq_bot hirr (by norm_num)).le)
    obtain ⟨w, hw⟩ := KFact.exists_conj_preimage hH Ψ hsurj g hgD hd
    let e : spinGroup (quadMinus 4 K b c) ≃* Y := MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
    have hcard : Nat.card (Subgroup.centralizer ({d} : Set Y)) =
        Nat.card (Subgroup.centralizer ({KFact.stdLongRootMinus K (by norm_num : 4 ≤ 4) b c} :
          Set (spinGroup (quadMinus 4 K b c)))) := by
      rw [hw]
      exact KFact.card_centralizer_conj_mulEquiv e w _
    rw [hcard]
    exact KFact.card_centralizer_longRoot_minus_four_dvd hirr hf1 hK
      (KFact.card_spinGroup_quadMinus hirr (by norm_num) hf1 hK)

end CertBound

end CFSG.RankThree.GF2n.Smith81.Insp
