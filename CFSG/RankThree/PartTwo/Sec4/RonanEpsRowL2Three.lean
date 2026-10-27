module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsOrders
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVL2

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.GorensteinWalter (PSL2)
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem not_isTypeEpsCube_of_two_mul_card_eq {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hX : 2 * Nat.card X = 3 ^ f * ((3 ^ f) ^ 2 - 1)) : ¬ IsTypeEpsCube X := by
  intro h
  have hlt : 3 ^ f * ((3 ^ f) ^ 2 - 1) < (3 ^ f) ^ 3 := by
    have hm : 0 < 3 ^ f := by positivity
    have h1 : (3 ^ f) ^ 2 - 1 < (3 ^ f) ^ 2 := by
      have : 1 ≤ (3 ^ f) ^ 2 := Nat.one_le_pow _ _ hm
      omega
    calc 3 ^ f * ((3 ^ f) ^ 2 - 1) < 3 ^ f * (3 ^ f) ^ 2 := Nat.mul_lt_mul_of_pos_left h1 hm
      _ = (3 ^ f) ^ 3 := by ring
  obtain ⟨r, hr, ⟨hr3, hc⟩ | ⟨hr3, hc⟩⟩ := card_of_isTypeEpsCube h
  ·
    have hr9 : r ^ 9 % 3 = 2 := by rw [Nat.pow_mod, hr3]
    have hcop : Nat.Coprime (3 ^ f) (2 * r ^ 9 * (r ^ 9 - 1)) := by
      refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_
      · exact Nat.Coprime.pow_left f (by norm_num)
      · exact Nat.Coprime.pow_left f (Nat.Coprime.pow_right 9
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)))
      · exact Nat.Coprime.pow_left f
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
    have h6 : 3 ^ f ∣ r ^ 6 - 1 := by
      have hdvd : 3 ^ f ∣ (2 * r ^ 9 * (r ^ 9 - 1)) * (r ^ 6 - 1) := by
        have e : (2 * r ^ 9 * (r ^ 9 - 1)) * (r ^ 6 - 1) = 2 * Nat.card X := by
          rw [hc]; ring
        rw [e, hX]
        exact dvd_mul_right _ _
      exact hcop.dvd_of_dvd_mul_left hdvd
    have hr6 : 64 ≤ r ^ 6 := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ r ^ 6 := Nat.pow_le_pow_left hr 6
    have hle : 3 ^ f ≤ r ^ 6 := le_trans (Nat.le_of_dvd (by omega) h6) (Nat.sub_le _ _)
    have hm3 : (3 ^ f) ^ 3 ≤ r ^ 18 := by
      calc (3 ^ f) ^ 3 ≤ (r ^ 6) ^ 3 := Nat.pow_le_pow_left hle 3
        _ = r ^ 18 := by ring
    have hb : r ^ 18 ≤ 2 * Nat.card X := by
      rw [hc]
      have h9 : 2 ≤ r ^ 9 := by
        calc 2 ≤ r := hr
          _ = r ^ 1 := (pow_one r).symm
          _ ≤ r ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have hB : 1 * (r ^ 9 - 1) ≤ (r ^ 6 - 1) * (r ^ 9 - 1) :=
        Nat.mul_le_mul (by omega) le_rfl
      have e18 : r ^ 18 = r ^ 9 * r ^ 9 := by ring
      rw [e18]
      calc r ^ 9 * r ^ 9 ≤ r ^ 9 * (2 * ((r ^ 6 - 1) * (r ^ 9 - 1))) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 - 1))) := by ring
    exact lt_irrefl _ (hlt.trans_le (hm3.trans (hb.trans_eq hX)))
  ·
    have hr9 : r ^ 9 % 3 = 1 := by rw [Nat.pow_mod, hr3]
    have hcop : Nat.Coprime (3 ^ f) (2 * r ^ 9 * (r ^ 9 + 1)) := by
      refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_
      · exact Nat.Coprime.pow_left f (by norm_num)
      · exact Nat.Coprime.pow_left f (Nat.Coprime.pow_right 9
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)))
      · exact Nat.Coprime.pow_left f
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
    have h6 : 3 ^ f ∣ r ^ 6 - 1 := by
      have hdvd : 3 ^ f ∣ (2 * r ^ 9 * (r ^ 9 + 1)) * (r ^ 6 - 1) := by
        have e : (2 * r ^ 9 * (r ^ 9 + 1)) * (r ^ 6 - 1) = 2 * Nat.card X := by
          rw [hc]; ring
        rw [e, hX]
        exact dvd_mul_right _ _
      exact hcop.dvd_of_dvd_mul_left hdvd
    have hr6 : 64 ≤ r ^ 6 := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ r ^ 6 := Nat.pow_le_pow_left hr 6
    have hle : 3 ^ f ≤ r ^ 6 := le_trans (Nat.le_of_dvd (by omega) h6) (Nat.sub_le _ _)
    have hm3 : (3 ^ f) ^ 3 ≤ r ^ 18 := by
      calc (3 ^ f) ^ 3 ≤ (r ^ 6) ^ 3 := Nat.pow_le_pow_left hle 3
        _ = r ^ 18 := by ring
    have hb : r ^ 18 ≤ 2 * Nat.card X := by
      rw [hc]
      have hB : 1 * (r ^ 9 + 1) ≤ (r ^ 6 - 1) * (r ^ 9 + 1) :=
        Nat.mul_le_mul (by omega) le_rfl
      have e18 : r ^ 18 = r ^ 9 * r ^ 9 := by ring
      rw [e18]
      calc r ^ 9 * r ^ 9 ≤ r ^ 9 * (2 * ((r ^ 6 - 1) * (r ^ 9 + 1))) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (r ^ 9 * ((r ^ 6 - 1) * (r ^ 9 + 1))) := by ring
    exact lt_irrefl _ (hlt.trans_le (hm3.trans (hb.trans_eq hX)))

theorem noCfgSEps_psl2_char_three {F : Type} [Field F] [Finite F] [CharP F 3]
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (φ : S ≃* CFSG.GorensteinWalter.PSL2 F) : NoCfgSEps S := by
  intro A σ K hc
  have hZ := RowV.center_eq_bot_of_simple hs hna
  have h3 : σ ^ 3 = 1 := hc.isE27.1.2 σ hc.mem
  haveI : Group.IsPerfect K := hc.isPerfect
  have hX : ¬ Nat.card K ∣ 12 := fun h => by
    have h1 := le_card_of_isTypeEpsCube (isTypeEpsCube_of_cfgSEps hc)
    have h2 : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ 12 := (Subgroup.card_quotient_dvd_card _).trans h
    have h5 := Nat.le_of_dvd (by norm_num) h2
    omega
  by_cases hin : IsInnerAut σ
  ·
    obtain ⟨s, rfl⟩ := hin
    have hs3 : s ^ 3 = 1 := by
      have h3' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow]; exact h3
      have hmem : s ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h := congrArg (fun τ : MulAut S => τ g) h3'
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [h]
          _ = s ^ 3 * g := by group
      rw [hZ, Subgroup.mem_bot] at hmem
      exact hmem
    have hs1 : s ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
    have hle : K ≤ Subgroup.centralizer ({s} : Set S) := by
      rw [← RowV.autFix_conj_eq_centralizer]
      exact hc.le_autFix
    have hπ : GH74.GLS.IVK.Proofs2.IsCentralQuot
        (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) :=
      ⟨QuotientGroup.mk'_surjective _, fun x => QuotientGroup.eq_one_iff x⟩
    have hcomm : ∀ a b : K, a * b = b * a := by
      intro a b
      have hcen : ∀ y : K, φ (y : S) * φ s = φ s * φ (y : S) := by
        intro y
        have hy : (y : S) * s = s * y :=
          Subgroup.mem_centralizer_singleton_iff.mp (hle y.2)
        rw [← map_mul, ← map_mul, hy]
      have h := GH74.GLS.IVK.Proofs2.IsCentralQuot.centralizer_comm_of_odd hπ
        (x := φ s) (fun h => hs1 (φ.injective (by rw [h, map_one]))) (r := 3) (by decide)
        (by rw [← map_pow, hs3, map_one]) (hcen a) (hcen b)
      apply Subtype.ext
      apply φ.injective
      simpa only [Subgroup.coe_mul, map_mul] using h
    haveI : IsMulCommutative K := ⟨⟨hcomm⟩⟩
    exact hX (by rw [Nat.card_unique]; exact one_dvd _)
  ·
    set β := MulAut.congr φ σ with hβ
    have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, h3, map_one]
    have hβout : ¬ IsInnerAut β := by rwa [hβ, isInnerAut_congr]
    obtain ⟨σ', hσ'3, ⟨e⟩⟩ := exists_eqLocus_mulEquiv_psl2 hβ3 hβout
    have hfix : autFix β = β.toMonoidHom.eqLocus (MonoidHom.id (PSL2 F)) := by
      ext x
      exact Iff.rfl
    let E : autFix σ ≃* PSL2 (GH74.GLS.IVK.fixedField σ') :=
      ((autFixCongrEquiv φ σ).symm.trans (MulEquiv.subgroupCongr hfix)).trans e
    have hcard3 : Nat.card (GH74.GLS.IVK.fixedField σ') ^ 3 = Nat.card F := by
      have := GH74.GLS.IVK.fixedField_card_pow σ'
      rwa [hσ'3] at this
    obtain ⟨k, hk⟩ : ∃ k, Nat.card (GH74.GLS.IVK.fixedField σ') = 3 ^ k := by
      have : Fintype F := Fintype.ofFinite F
      obtain ⟨n, -, hn⟩ := FiniteField.card F 3
      have hd : Nat.card (GH74.GLS.IVK.fixedField σ') ∣ 3 ^ (n : ℕ) := by
        rw [← hn, ← Nat.card_eq_fintype_card, ← hcard3]
        exact dvd_pow_self _ (by norm_num)
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
      exact ⟨k, hk⟩
    have hodd : Odd (Nat.card (GH74.GLS.IVK.fixedField σ')) := by
      rw [hk]
      exact Odd.pow (by decide)
    have hcardC := CFSG.Semidihedral.AllPrime.SL2Sections.card_psl2_mul_two hodd
    by_cases h4 : 4 ≤ Nat.card (GH74.GLS.IVK.fixedField σ')
    · have hk2 : 2 ≤ k := by
        by_contra h'
        interval_cases k <;> simp at hk <;> omega
      have hQ : IsQuasisimple (autFix σ) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv E.symm (isQuasisimple_psl2_of_four_le_card h4)
      have hK1 : Nontrivial K := by
        by_contra hnt
        rw [not_nontrivial_iff_subsingleton] at hnt
        exact hX (by rw [Nat.card_unique]; exact one_dvd _)
      have hKeq : K = autFix σ :=
        Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hc.le_autFix hQ hc.isPerfect hK1
          hc.isSubnormal
      let EK : K ≃* PSL2 (GH74.GLS.IVK.fixedField σ') := (MulEquiv.subgroupCongr hKeq).trans E
      have hKq : IsQuasisimple K := CFSG.LocalCores.isQuasisimple_of_mulEquiv EK.symm
        (isQuasisimple_psl2_of_four_le_card h4)
      have hZK : Subgroup.center K = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        have hy : EK x ∈ Subgroup.center (PSL2 (GH74.GLS.IVK.fixedField σ')) := by
          rw [Subgroup.mem_center_iff]
          intro y
          obtain ⟨z, rfl⟩ := EK.surjective y
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
        rw [CFSG.GorensteinWalter.psl2_center_eq_bot, Subgroup.mem_bot] at hy
        exact EK.injective (by rw [hy, map_one])
      have hO2 : CFSG.pCore 2 K = ⊥ :=
        eq_bot_iff.mpr (hZK ▸ RowV.pCore_two_le_center_of_quasisimple hKq)
      have hcardX : Nat.card (K ⧸ CFSG.pCore 2 K) = Nat.card K := by
        have h := (CFSG.pCore 2 K).card_eq_card_quotient_mul_card_subgroup
        have h1 : Nat.card (CFSG.pCore 2 K) = 1 := by rw [hO2]; exact Subgroup.card_bot
        rw [h1, mul_one] at h
        exact h.symm
      refine not_isTypeEpsCube_of_two_mul_card_eq (X := K ⧸ CFSG.pCore 2 K) (f := k) (by omega)
        ?_ (isTypeEpsCube_of_cfgSEps hc)
      rw [hcardX, Nat.card_congr EK.toEquiv, mul_comm, hcardC, hk]
    ·
      have hk1 : k = 1 := by
        rcases Nat.lt_or_ge k 2 with h | h
        · interval_cases k
          · exfalso
            have : 1 < Nat.card (GH74.GLS.IVK.fixedField σ') := Finite.one_lt_card
            omega
          · rfl
        · exfalso
          have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
          omega
      have hc12 : Nat.card (PSL2 (GH74.GLS.IVK.fixedField σ')) * 2 = 24 := by
        have h := hcardC
        rw [hk, hk1] at h
        norm_num at h
        exact h
      have h12 : Nat.card (autFix σ) = 12 := by
        rw [Nat.card_congr E.toEquiv]
        omega
      exact hX (h12 ▸ Subgroup.card_dvd_of_le hc.le_autFix)

theorem rowSEpsOf_one_three : ∀ e : ℕ, 3 ≤ e → RowSEpsOf (projSL 2 (GaloisField 3 e)) :=
  fun e _ _ _ _ hs hna ⟨φ⟩ =>
    noCfgSEps_psl2_char_three hs hna (φ.trans (projSLEquivPSL (GaloisField 3 e)))

end CFSG.RankThree.PartTwo.Sec4.RonanEps
