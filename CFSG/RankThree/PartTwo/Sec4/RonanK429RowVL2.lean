module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVL2Ord
public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof429
public import CFSG.RankThree.PartTwo.KFacts.K72FixL2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714L2
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.CharacterTheory.Semidihedral.AllPrimeSL2Sections
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.GorensteinWalter (PSL2)

namespace RowV

theorem pCore_two_le_center_of_quasisimple {K : Type} [Group K] [Finite K]
    (hK : IsQuasisimple K) : CFSG.pCore 2 K ≤ Subgroup.center K := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK
      (inferInstance : (CFSG.pCore 2 K).Normal) with h | h
  · exfalso
    have h2 : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
    rw [h] at h2
    have hp : IsPGroup 2 K := h2.of_equiv Subgroup.topEquiv
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := hK.1
    haveI : Nontrivial K := by
      haveI : Nontrivial (K ⧸ Subgroup.center K) := hK.2.1.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
    exact Group.IsPerfect.not_isNilpotent K hp.isNilpotent
  · exact h

theorem not_isType429_of_card_dvd_twelve {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (h : Nat.card X ∣ 12) : ¬ IsType429 X :=
  not_isType429_of_dvd (N := 12) (B := 3) (by norm_num) h (by norm_num) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem noCfgS429_psl2_char_three {F : Type} [Field F] [Finite F] [CharP F 3]
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (φ : S ≃* PSL2 F) : NoCfgS429 S := by
  intro A σ K hc
  have hZ := center_eq_bot_of_simple hs hna
  have h3 : σ ^ 3 = 1 := hc.isE27.1.2 σ hc.mem
  haveI : Group.IsPerfect K := hc.isPerfect
  have hX : ¬ Nat.card K ∣ 12 := fun h =>
    not_isType429_of_card_dvd_twelve ((Subgroup.card_quotient_dvd_card _).trans h) hc.isType
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
      rw [← autFix_conj_eq_centralizer]
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
        eq_bot_iff.mpr (hZK ▸ pCore_two_le_center_of_quasisimple hKq)
      have hcardX : Nat.card (K ⧸ CFSG.pCore 2 K) = Nat.card K := by
        have h := (CFSG.pCore 2 K).card_eq_card_quotient_mul_card_subgroup
        have h1 : Nat.card (CFSG.pCore 2 K) = 1 := by rw [hO2]; exact Subgroup.card_bot
        rw [h1, mul_one] at h
        exact h.symm
      refine not_isType429_of_two_mul_card_eq (X := K ⧸ CFSG.pCore 2 K) hk2 ?_ hc.isType
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

theorem noCfgS429_projSL_two_three {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {e : ℕ}
    (φ : S ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 3 e)) : NoCfgS429 S :=
  noCfgS429_psl2_char_three hs hna (φ.trans (projSLEquivPSL (GaloisField 3 e)))

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
