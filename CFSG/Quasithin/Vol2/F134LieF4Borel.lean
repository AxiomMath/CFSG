module

public import CFSG.Quasithin.Vol2.F134LieF4Group
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersParabolic
public import CFSG.LieType.Ree.LargeReeFixedGroupSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.Quasithin.F134.LieF4

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem exists_le_reeLocalParabolic {Q : Subgroup (ModGL F4.tag K)}
    (hBQ : F4.reeFixedBorel K a ≤ Q) (hQΓ : Q ≤ F4.reeGamma K a) (hQ : Q ≠ F4.reeGamma K a) :
    ∃ i, Q ≤ F4.reeLocalParabolic K a i := by
  obtain ⟨hA, -⟩ := ree_Borel_overgroup_classification F4 a K Q hBQ hQΓ
  by_cases h : ∀ j : Fin F4.fixedOrbitCount,
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ Q
  · refine absurd (le_antisymm hQΓ ?_) hQ
    rw [(ree_Borel_overgroup_classification F4 a K (F4.reeGamma K a) reeFixedBorel_le_reeGamma
      le_rfl).1]
    refine sup_le hBQ ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨j, -, rfl⟩
    exact h j
  · obtain ⟨j, hj⟩ := not_forall.1 h
    have h2 : F4.fixedOrbitCount = 2 := rfl
    let i : Fin F4.fixedOrbitCount := ⟨1 - (j : ℕ), by have := j.2; omega⟩
    refine ⟨i, ?_⟩
    rw [hA]
    refine reeParabolic_le_reeGamma_inf fun k hk => ?_
    have hkj : k ≠ j := fun e => hj (e ▸ hk)
    have hk2 := k.2
    have hj2 := j.2
    have hkj' : (k : ℕ) ≠ j := fun e => hkj (Fin.ext e)
    exact Fin.ext (by simp only [i]; omega)

theorem le_reeFixedBorel_or_dvd {i : Fin F4.fixedOrbitCount} {H : Subgroup (ModGL F4.tag K)}
    (hHP : H ≤ F4.reeLocalParabolic K a i) (hUH : F4.reeFixedPosUnipotent K a ≤ H) :
    H ≤ F4.reeFixedBorel K a ∨
      Nat.card (F4.reeFixedOrbitUnipotent K a i) + 1 ∣
        (F4.reeFixedPosUnipotent K a).relIndex H := by
  by_cases hHB : H ≤ F4.reeFixedBorel K a
  · exact Or.inl hHB
  right
  obtain ⟨h, hh, hhB⟩ := Set.not_subset.1 hHB
  have hO : (fun g : ModGL F4.tag K => (g : ModGL F4.tag K ⧸ F4.reeFixedBorel K a)) ''
      (H : Set (ModGL F4.tag K)) = F4.reeLocalCosets K a i := by
    refine Set.Subset.antisymm (Set.image_mono hHP) fun ω hω => ?_
    by_cases hω1 : ω = ((1 : ModGL F4.tag K) : ModGL F4.tag K ⧸ F4.reeFixedBorel K a)
    · exact ⟨1, H.one_mem, hω1.symm⟩
    have hhω : ((h : ModGL F4.tag K) : ModGL F4.tag K ⧸ F4.reeFixedBorel K a) ∈
        F4.reeLocalCosets K a i := ⟨h, hHP hh, rfl⟩
    have hh1 : ((h : ModGL F4.tag K) : ModGL F4.tag K ⧸ F4.reeFixedBorel K a) ≠
        ((1 : ModGL F4.tag K) : _) := fun e => hhB (mk_eq_one_iff.1 e)
    obtain ⟨⟨x, hx⟩, hxω, -⟩ := existsUnique_smul_eq hhω hh1 hω hω1
    exact ⟨x * h, H.mul_mem (hUH (LargeReeInvolution.reeFixedOrbitUnipotent_le i hx)) hh, hxω⟩
  have hcard := ncard_image_coset_eq_relIndex (F4.reeFixedBorel K a) H
  rw [hO, ncard_reeLocalCosets] at hcard
  rw [hcard]
  exact Subgroup.relIndex_dvd_of_le_left H reeFixedPosUnipotent_le_reeFixedBorel

theorem eq_one_of_mem_reeFixedBorel (hK : Nat.card K % 3 = 2) {x : ModGL F4.tag K}
    (hx : x ∈ F4.reeFixedBorel K a) (h3 : x ^ 3 = 1) : x = 1 := by
  have h1 := pow_card_sub_one_mem_reeFixedPosUnipotent hx
  have hq : x ^ (Nat.card K - 1) = x := by
    rw [show Nat.card K - 1 = 3 * ((Nat.card K - 1) / 3) + 1 by omega, pow_add, pow_mul, h3,
      one_pow, one_mul, pow_one]
  rw [hq] at h1
  have hp : IsPGroup 2 (F4.reeFixedPosUnipotent K a) :=
    (isPGroup_posUnipotent 2 F4.tag).to_le inf_le_left
  obtain ⟨k, hk⟩ := hp ⟨x, h1⟩
  have h2 : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hg : x ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.2 ⟨h2, h3⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left _ (by norm_num)), pow_one] at hg

theorem not_three_dvd_card_reeFixedBorel (hK : Nat.card K % 3 = 2) :
    ¬ 3 ∣ Nat.card (F4.reeFixedBorel K a) := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
  have hx1 : (x : ModGL F4.tag K) = 1 := by
    refine eq_one_of_mem_reeFixedBorel hK x.2 ?_
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  have : x = 1 := Subtype.ext hx1
  rw [this, orderOf_one] at hx
  omega

theorem false_of_le_reeLocalParabolic_zero
    (hK8 : Nat.card K = 8) {P : Subgroup (ModGL F4.tag K)}
    (hPP : P ≤ F4.reeLocalParabolic K 1 ⟨0, by decide⟩) (hP : Nat.card P = 9)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hK : Nat.card K = 2 ^ (2 * 1 + 1) := hK8
  have hK3 : Nat.card K % 3 = 2 := by rw [hK8]
  have hBP : F4.reeFixedBorel K 1 ≤ F4.reeLocalParabolic K 1 ⟨0, by decide⟩ :=
    reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
  have hidx : (F4.reeFixedBorel K 1).relIndex (F4.reeLocalParabolic K 1 ⟨0, by decide⟩) = 9 := by
    rw [← ncard_image_coset_eq_relIndex]
    change (F4.reeLocalCosets K 1 ⟨0, by decide⟩).ncard = 9
    rw [ncard_reeLocalCosets, card_reeFixedOrbitUnipotent_zero hK, hK8]
  have hcardP₀ : Nat.card (F4.reeLocalParabolic K 1 ⟨0, by decide⟩) =
      9 * Nat.card (F4.reeFixedBorel K 1) := by
    have := Subgroup.relIndex_mul_card (F4.reeFixedBorel K 1)
      (F4.reeLocalParabolic K 1 ⟨0, by decide⟩)
    rw [inf_eq_left.2 hBP, hidx] at this
    exact this.symm
  have hB3 := not_three_dvd_card_reeFixedBorel (a := 1) hK3
  have hsyl : ∀ S : Subgroup (ModGL F4.tag K), S ≤ F4.reeLocalParabolic K 1 ⟨0, by decide⟩ →
      Nat.card S = 9 → IsSylowOf 3 S (F4.reeLocalParabolic K 1 ⟨0, by decide⟩) := by
    intro S hS hS9
    rw [isSylowOf_iff]
    refine ⟨hS, IsPGroup.of_card (n := 2) (by rw [hS9]; norm_num), ?_⟩
    have := Subgroup.relIndex_mul_card S (F4.reeLocalParabolic K 1 ⟨0, by decide⟩)
    rw [inf_eq_left.2 hS, hS9, hcardP₀] at this
    have h : S.relIndex (F4.reeLocalParabolic K 1 ⟨0, by decide⟩) =
        Nat.card (F4.reeFixedBorel K 1) := by
      omega
    rwa [h]
  have hM : (largeReeA1Hom K 1).range ≤ F4.reeLocalParabolic K 1 ⟨0, by decide⟩ := by
    rw [largeReeA1Hom_range hK]
    exact (large_Ree_local_block_Sylow_action F4 1 K ⟨0, by decide⟩).1
  have hf : Function.Injective (largeReeA1Hom K 1) :=
    (injective_iff_map_eq_one _).2 fun _ hg => eq_one_of_largeReeA1Hom_eq_one 1 hg
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := SL2 K) 3 (n := 2)
    (by rw [card_sl2_eight hK8]; norm_num)
  have hSG := hsyl (S.map (largeReeA1Hom K 1)) ((Subgroup.map_le_range _ S).trans hM)
    (by rw [Subgroup.card_map_of_injective hf, hS]; norm_num)
  obtain ⟨g, -, hSg⟩ := exists_mem_eq_map_conj_of_isSylowOf (hsyl P hPP hP) hSG
  refine noElemNine_sl2_eight hK8 S (by rw [hS]; norm_num) fun s hs => hf ?_
  have hfs : largeReeA1Hom K 1 s ∈ P.map (MulAut.conj g).toMonoidHom := hSg ▸ ⟨s, hs, rfl⟩
  obtain ⟨x, hx, hxs⟩ := hfs
  rw [map_pow, ← hxs, map_one, ← map_pow, hexp x hx, map_one]

theorem false_of_le_reeGamma (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {Q H P : Subgroup (ModGL F4.tag K)}
    (hBQ : F4.reeFixedBorel K a ≤ Q) (hQΓ : Q ≤ F4.reeGamma K a) (hQ : Q ≠ F4.reeGamma K a)
    (hHQ : H ≤ Q) (hUH : F4.reeFixedPosUnipotent K a ≤ H)
    (hH : Nat.card H = 9 * Nat.card (F4.reeFixedPosUnipotent K a)) (hPH : P ≤ H)
    (hP : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1) : False := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hK3 : Nat.card K % 3 = 2 := by
    rw [hK, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  obtain ⟨i, hi⟩ := exists_le_reeLocalParabolic hBQ hQΓ hQ
  have hrel : (F4.reeFixedPosUnipotent K a).relIndex H = 9 := by
    have h := Subgroup.relIndex_mul_card (F4.reeFixedPosUnipotent K a) H
    rw [inf_eq_left.2 hUH, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  rcases le_reeFixedBorel_or_dvd (hHQ.trans hi) hUH with hB | hdvd
  · have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun x hx =>
      eq_one_of_mem_reeFixedBorel hK3 (hB (hPH hx)) (hexp x hx)
    rw [hbot, Subgroup.card_bot] at hP
    omega
  rw [hrel] at hdvd
  have hq8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨i, hi2⟩ := i
  have hi2' : i < 2 := hi2
  interval_cases i
  · rw [card_reeFixedOrbitUnipotent_zero hK] at hle
    obtain rfl : a = 1 := by
      by_contra ha1
      have : 2 ^ 5 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact false_of_le_reeLocalParabolic_zero (hK.trans (by norm_num)) ((hPH.trans hHQ).trans hi)
      hP hexp
  · rw [card_reeFixedOrbitUnipotent_one hK] at hle
    nlinarith

end CFSG.Quasithin.F134.LieF4
