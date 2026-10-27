module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowCover
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.RankThree.PartTwo.KFacts.K426RestON
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714L2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.GorensteinWalter (PSL2)
open CFSG.Assembly.RankThreeEven (projSU)

theorem two_pow_nine_dvd_card_projSU {m : ℕ} (hm3 : 3 ≤ m) :
    2 ^ 9 ∣ Nat.card (projSU 3 2 m) := by
  have hU := padicValNat_card_projSU (by omega : 1 ≤ m)
  have h2 : 2 ^ (3 * m) ∣ Nat.card (projSU 3 2 m) := hU ▸ pow_padicValNat_dvd
  exact (pow_dvd_pow 2 (by omega)).trans h2

section L2


theorem rowU3_L2char3 {F : Type} [Field F] [Finite F] [CharP F 3] {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (φ : S ≃* PSL2 F)
    {σ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) {Y : Subgroup S} (hYC : Y ≤ Sec4.autFix σ)
    [Group.IsPerfect Y] (hsub : (Y.subgroupOf (Sec4.autFix σ)).IsSubnormal) {m : ℕ}
    (hmo : Odd m) (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (_hker : Nat.Coprime (Nat.card π.ker) 3) : False := by
  have hZ := RonanK429.RowV.center_eq_bot_of_simple hs hna
  have hm3 : 3 ≤ m := by
    obtain ⟨j, rfl⟩ := hmo
    omega
  have hU1 := one_lt_card_projSU (by omega : 1 ≤ m)
  have hdU : Nat.card (projSU 3 2 m) ∣ Nat.card Y := Subgroup.card_dvd_of_surjective hπ
  have h512 : 2 ^ 9 ∣ Nat.card Y := (two_pow_nine_dvd_card_projSU hm3).trans hdU
  by_cases hin : IsInnerAut σ
  ·
    obtain ⟨s, rfl⟩ := hin
    have hs3 : s ^ 3 = 1 := by
      have h3' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow]; exact hσ3
      have hmem : s ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h := congrArg (fun τ : MulAut S => τ g) h3'
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [h]
          _ = s ^ 3 * g := by group
      rw [hZ, Subgroup.mem_bot] at hmem
      exact hmem
    have hs1 : s ≠ 1 := fun h => hσ1 (by rw [h, map_one])
    have hle : Y ≤ Subgroup.centralizer ({s} : Set S) := by
      rw [← RonanK429.RowV.autFix_conj_eq_centralizer]
      exact hYC
    have hπc : GH74.GLS.IVK.Proofs2.IsCentralQuot
        (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) :=
      ⟨QuotientGroup.mk'_surjective _, fun x => QuotientGroup.eq_one_iff x⟩
    have hcomm : ∀ a b : Y, a * b = b * a := by
      intro a b
      have hcen : ∀ y : Y, φ (y : S) * φ s = φ s * φ (y : S) := by
        intro y
        have hy : (y : S) * s = s * y :=
          Subgroup.mem_centralizer_singleton_iff.mp (hle y.2)
        rw [← map_mul, ← map_mul, hy]
      have h := GH74.GLS.IVK.Proofs2.IsCentralQuot.centralizer_comm_of_odd hπc
        (x := φ s) (fun h => hs1 (φ.injective (by rw [h, map_one]))) (r := 3) (by decide)
        (by rw [← map_pow, hs3, map_one]) (hcen a) (hcen b)
      apply Subtype.ext
      apply φ.injective
      simpa only [Subgroup.coe_mul, map_mul] using h
    obtain ⟨u, w, huw⟩ := exists_not_commute_projSU hmo
    obtain ⟨a, rfl⟩ := hπ u
    obtain ⟨b, rfl⟩ := hπ w
    exact huw (by rw [← map_mul, ← map_mul, hcomm a b])
  ·
    set β := MulAut.congr φ σ with hβ
    have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hσ3, map_one]
    have hβout : ¬ IsInnerAut β := by rwa [hβ, isInnerAut_congr]
    obtain ⟨σ', hσ'3, ⟨e⟩⟩ := exists_eqLocus_mulEquiv_psl2 hβ3 hβout
    have hfix : Sec4.autFix β = β.toMonoidHom.eqLocus (MonoidHom.id (PSL2 F)) := by
      ext x
      exact Iff.rfl
    let E : Sec4.autFix σ ≃* PSL2 (GH74.GLS.IVK.fixedField σ') :=
      ((Sec4.autFixCongrEquiv φ σ).symm.trans (MulEquiv.subgroupCongr hfix)).trans e
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
    · have hk1 : 1 ≤ k := by
        by_contra h'
        interval_cases k
        simp at hk
        omega
      have hQ : IsQuasisimple (Sec4.autFix σ) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv E.symm (isQuasisimple_psl2_of_four_le_card h4)
      have hY1 : Nontrivial Y := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        have := Nat.le_of_dvd Nat.card_pos hdU
        omega
      have hYeq : Y = Sec4.autFix σ :=
        Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hYC hQ inferInstance hY1 hsub
      let EY : Y ≃* PSL2 (GH74.GLS.IVK.fixedField σ') := (MulEquiv.subgroupCongr hYeq).trans E
      have hYq : IsQuasisimple Y := CFSG.LocalCores.isQuasisimple_of_mulEquiv EY.symm
        (isQuasisimple_psl2_of_four_le_card h4)
      have hZY : Subgroup.center Y = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        have hy : EY x ∈ Subgroup.center (PSL2 (GH74.GLS.IVK.fixedField σ')) := by
          rw [Subgroup.mem_center_iff]
          intro y
          obtain ⟨z, rfl⟩ := EY.surjective y
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
        rw [CFSG.GorensteinWalter.psl2_center_eq_bot, Subgroup.mem_bot] at hy
        exact EY.injective (by rw [hy, map_one])
      have hinj : Function.Injective π := by
        rcases CFSG.LocalCores.quasisimple_normal_subgroups hYq (MonoidHom.normal_ker π) with
          h | h
        · exfalso
          have h1 : ∀ z : projSU 3 2 m, z = 1 := by
            intro z
            obtain ⟨y, rfl⟩ := hπ z
            have : y ∈ π.ker := by rw [h]; exact Subgroup.mem_top y
            exact this
          have : Nat.card (projSU 3 2 m) = 1 :=
            Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [h1 a, h1 b]⟩, ⟨1⟩⟩
          omega
        · rw [hZY, le_bot_iff] at h
          exact (MonoidHom.ker_eq_bot_iff π).mp h
      let eπ : Y ≃* projSU 3 2 m := MulEquiv.ofBijective π ⟨hinj, hπ⟩
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hchar : CharP (GH74.GLS.IVK.fixedField σ') 3 := by
        have := Fintype.ofFinite (GH74.GLS.IVK.fixedField σ')
        exact charP_of_card_eq_prime_pow (p := 3) (f := k)
          (by rw [← Nat.card_eq_fintype_card, hk])
      have hring : ringChar (GH74.GLS.IVK.fixedField σ') ≠ 2 := by
        rw [ringChar.eq (GH74.GLS.IVK.fixedField σ') 3]
        norm_num
      exact not_oddCharStdModel_of_mulEquiv_projSU (by omega) eπ
        ⟨GH74.GLS.IVK.fixedField σ', inferInstance, inferInstance, hring, Or.inl ⟨EY⟩⟩
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
      have h12 : Nat.card (Sec4.autFix σ) = 12 := by
        rw [Nat.card_congr E.toEquiv]
        omega
      have h := h512.trans (Subgroup.card_dvd_of_le hYC)
      rw [h12] at h
      norm_num at h

end L2

section ON


theorem rowU3_ON {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (eS : S ≃* Blueprint.NativeSporadic.Carrier .ONan)
    {σ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) {Y : Subgroup S} (hYC : Y ≤ Sec4.autFix σ)
    [Group.IsPerfect Y] (_hsub : (Y.subgroupOf (Sec4.autFix σ)).IsSubnormal) {m : ℕ}
    (hmo : Odd m) (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (_hker : Nat.Coprime (Nat.card π.ker) 3) : False := by
  haveI := hs
  have hZ := RonanK429H.center_eq_bot_of_simple_nonab hna
  have hout := RonanK429H.not_three_dvd_outer_of_mulEquiv eS inputs47Core_outON
  obtain ⟨s, rfl⟩ := cubeInner_of_not_three_dvd_card_outer hout σ hσ3
  have hs3 : s ^ 3 = 1 := by
    have h' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, hσ3]
    have hz : s ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut S => φ g) h'
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [this]
        _ = s ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hz
    exact hz
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hσ1 (map_one _)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Y ≤ Subgroup.centralizer ({s} : Set S) := by
    rw [← RonanK429H.autFix_conj]
    exact hYC
  have hs' : orderOf (eS s) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hs3 hs1
  have hc := KFacts.K426Rest.onThreeCentralizer (eS s) hs'
  have hcard := RonanK429H.card_centralizer_mulEquiv eS s
  have h3240 : Nat.card (Subgroup.centralizer ({s} : Set S)) = 3240 := hcard.symm.trans hc
  have hm3 : 3 ≤ m := by
    obtain ⟨j, rfl⟩ := hmo
    omega
  have h := ((two_pow_nine_dvd_card_projSU hm3).trans (Subgroup.card_dvd_of_surjective hπ)).trans
    (Subgroup.card_dvd_of_le hle)
  rw [h3240] at h
  norm_num at h

end ON

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
