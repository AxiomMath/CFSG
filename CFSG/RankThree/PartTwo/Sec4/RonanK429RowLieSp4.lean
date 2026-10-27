module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieG2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieRows
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieArithSp4
public import CFSG.RankThree.PartTwo.KFacts.K71Sp4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.Assembly.RankThreeEven (projSp)

theorem sp4Excl429
    (k : Type) [Field k] [Finite k] [CharP k 2] (m : ℕ) (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m)
    (G : Type) [Group G] [Finite G] (C J : Subgroup G)
    (hC : Nonempty (C ≃* StatedProj (StatedSp 2 k))) (hJC : J ≤ C) (hJperf : Group.IsPerfect J)
    (hsub : (J.subgroupOf C).IsSubnormal) (htype : IsType429 (J ⧸ CFSG.pCore 2 J)) : False := by
  obtain ⟨eC⟩ := hC
  haveI := hJperf
  obtain ⟨E, hEJ, -, hE3, hE9, -⟩ := exists_e9_of_type429 htype
  obtain ⟨k₀, hk₀E, hk₀1, hk₀3⟩ := exists_ne_one_pow_three hE3 hE9
  have hk₀J : k₀ ∈ J := hEJ hk₀E
  have hJnt : J ≠ ⊥ := fun hb => hk₀1 ((Subgroup.mem_bot).mp (hb ▸ hk₀J))
  have hk₀1' : (⟨k₀, hk₀J⟩ : J) ≠ 1 := fun h => hk₀1 (congrArg Subtype.val h)
  have hk₀3' : (⟨k₀, hk₀J⟩ : J) ^ 3 = 1 := Subtype.ext (by simpa using hk₀3)
  obtain ⟨hQperf, hQnt⟩ := quot_pCore_facts hk₀1' hk₀3'
  haveI := hQnt
  have hcardC : Nat.card C = (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) := by
    rw [Nat.card_congr eC.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo,
      hk, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
    norm_num
  have hQJ : Nat.card (J ⧸ CFSG.pCore 2 J) ∣ Nat.card J := by
    haveI : (CFSG.pCore 2 J).Normal := CFSG.pCore_normal
    exact Subgroup.card_quotient_dvd_card _
  have hJCd : Nat.card J ∣ Nat.card C := Subgroup.card_dvd_of_le hJC
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  ·
    have hdvd : Nat.card (J ⧸ CFSG.pCore 2 J) ∣ 720 := by
      have := hQJ.trans hJCd
      rw [hcardC] at this
      simpa using this
    have hle : Nat.card (J ⧸ CFSG.pCore 2 J) ≤ 720 := Nat.le_of_dvd (by norm_num) hdvd
    rcases card_of_isType429 htype with ⟨p, e, hp, hp3, he, ⟨hq, hc⟩ | ⟨hq, hc, hsol⟩⟩ |
      hc | hc | hc | hc
    · exact sp4two_L3 hdvd (Nat.le_trans hp.two_le (Nat.le_self_pow (by omega) p)) hq hc
    · have h2 := sp4two_U3 hdvd (Nat.le_trans hp.two_le (Nat.le_self_pow (by omega) p)) hq hc
      exact Group.IsPerfect.not_isSolvable _ (hsol h2)
    all_goals omega
  ·
    have h4 : 4 ≤ Nat.card k := by
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    haveI hCs : IsSimpleGroup (StatedProj (StatedSp 2 k)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k 2 (by norm_num)
        (Or.inl (Or.inr h4))
    have hCs' : IsSimpleGroup C := eC.isSimpleGroup
    have hJC' : J = C := eq_of_subnormal_of_le_simple hJC le_rfl hsub hCs' hJnt
    haveI hJs : IsSimpleGroup J := by
      rw [hJC']
      exact hCs'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hN : CFSG.pCore 2 J = ⊥ := by
      haveI : (CFSG.pCore 2 J).Normal := CFSG.pCore_normal
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 J) with h | h
      · exact h
      · exfalso
        have hkN : (⟨k₀, hk₀J⟩ : J) ∈ CFSG.pCore 2 J := h ▸ Subgroup.mem_top _
        exact hk₀1' (eq_one_of_isPGroup_two_of_pow_three CFSG.pCore_isPGroup hkN hk₀3')
    have hcardQ : Nat.card (J ⧸ CFSG.pCore 2 J) =
        (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) := by
      have e1 : (J ⧸ CFSG.pCore 2 J) ≃* J :=
        (QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot
      rw [Nat.card_congr e1.toEquiv, ← hcardC]
      exact congrArg (fun H : Subgroup G => Nat.card H) hJC'
    have hbig : 604800 < (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) := by
      have h4' : 4 ≤ 2 ^ m := by rw [← hk]; exact h4
      have h1 : 4 ^ 4 ≤ (2 ^ m) ^ 4 := Nat.pow_le_pow_left h4' 4
      have h2 : 4 ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h4' 2
      have hA : 15 ≤ (2 ^ m) ^ 2 - 1 := by omega
      have hB : 255 ≤ (2 ^ m) ^ 4 - 1 := by omega
      calc 604800 < 4 ^ 4 * (15 * 255) := by norm_num
        _ ≤ (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) :=
          Nat.mul_le_mul h1 (Nat.mul_le_mul hA hB)
    rcases card_of_isType429 htype with ⟨p, e, hp, hp3, he, ⟨hq, hc⟩ | ⟨hq, hc, -⟩⟩ |
      hc | hc | hc | hc
    · exact sp4_mul_three_ne_L3 hm2 hp hp3 he (hcardQ ▸ hc)
    · exact sp4_mul_three_ne_U3 hm2 hp hp3 he (hcardQ ▸ hc)
    all_goals omega

section Sp4Row


theorem charP_fixedField_two {F : Type} [Field F] [Finite F] (φ : F ≃+* F) {m : ℕ}
    (hm : Nat.card (fixedField φ) = 2 ^ m) (hm1 : 1 ≤ m) : CharP (fixedField φ) 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite (fixedField φ)
  exact charP_of_card_eq_prime_pow (p := 2) (f := m) (by rw [← Nat.card_eq_fintype_card, hm])

theorem noCfgS429_seven_Sp4 (n : ℕ) (hn : 1 ≤ n) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* projSp 2 (GaloisField 2 n)) → NoCfgS429 S := by
  intro S _ _ hs hna ⟨eS⟩ A σ K hc
  haveI := hc.isPerfect
  have hσ3 := cfgS429_pow_three hc
  obtain ⟨E, hEK, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_type429 hc.isType
  have hfix : ∀ k ∈ K, σ k = k := fun k hk => Sec4.mem_autFix.mp (hc.le_autFix hk)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 n with hF
  have hFcard : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
  set τ : S ≃* StatedProj (StatedSp 2 F) := eS.trans (CFSG.PGLModel.projSpEquivStatedProj 2 F) with hτ
  have hnaP : ∃ a b : StatedProj (StatedSp 2 F), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨τ a, τ b, fun h => hab (τ.injective (by rw [map_mul, map_mul, h]))⟩
  have hsP : IsSimpleGroup (StatedProj (StatedSp 2 F)) := τ.symm.isSimpleGroup
  have hZ := center_trivial_of_isSimpleGroup hsP hnaP
  have h3F : ¬ 3 ∣ Nat.card F := by
    rw [hFcard]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  set α := MulAut.congr τ σ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hσ3, map_one]
  by_cases hD : α ∈ (conjAut 2 F).range
  ·
    obtain ⟨H, hH⟩ := hD
    have hin : IsInnerAut α := hH ▸ conjAut_mem_inner_of_charTwo H
    refine false_of_fix_e9_of_mulEquiv τ
      (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut _).range ?_ (fun s => ⟨s, rfl⟩) hZ hin
      hσ3 hc.ne_one hEK hEc hE3 hE9 hfix hEZ
    intro B hB h3B hcB
    exact card_le_nine_inn (fun E hE h27 =>
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.noE27_projSp_two h3F
        ⟨E, hE, h27⟩) hZ hB h3B hcB
  ·
    obtain ⟨φ, hφ, H, hαH⟩ := sp4_even_order_three_field_descent α hα3 hD
    obtain ⟨h3n, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two hn hFcard hφ
    obtain ⟨m, rfl⟩ := h3n
    have hm : 1 ≤ m := by omega
    have hcard : Nat.card (fixedField φ) = 2 ^ m :=
      card_fixedField_of_orderOf_eq_three hφ (by rw [hFcard, ← pow_mul, mul_comm])
    haveI := charP_fixedField_two φ hcard hm
    have hfixeq : Sec4.autFix (fieldAut 2 F φ) = ((proj 2 F).comp (spIncl φ)).range := by
      ext y
      rw [Sec4.mem_autFix, mem_range_proj_spIncl_iff φ y]
    have eSp : StatedSp 2 (fixedField φ) ≃* StatedProj (StatedSp 2 (fixedField φ)) :=
      MulEquiv.ofBijective (proj 2 (fixedField φ)) ⟨proj_injective_of_charTwo, proj_surjective⟩
    have eα : Sec4.autFix α ≃* StatedProj (StatedSp 2 (fixedField φ)) := by
      rw [hαH]
      exact (((autFixConjEquiv (conjAut 2 F H) (fieldAut 2 F φ)).trans
        (MulEquiv.subgroupCongr hfixeq)).trans
          (MonoidHom.ofInjective (proj_spIncl_injective φ)).symm).trans eSp
    exact sp4Excl429 (fixedField φ) m hcard hm S (Sec4.autFix σ) K
      ⟨(Sec4.autFixCongrEquiv τ σ).symm.trans eα⟩ hc.le_autFix hc.isPerfect hc.isSubnormal
      hc.isType

end Sp4Row

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
