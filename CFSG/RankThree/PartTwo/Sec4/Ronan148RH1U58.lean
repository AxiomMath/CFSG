module

public import CFSG.HardMathSupport.Dickson.Bal207.UniGood
public import CFSG.HardMathSupport.Dickson.Bal207.UniFamOuter
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Shape

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim (oneGram)
open CFSG.HardMathSupport.Dickson.Bal207.Uni

section Crit

variable {S : Type} [Group S] [Finite S]

theorem good427_of_nine_dvd {C : Subgroup S}
    (h : ∀ L : Subgroup S, CFSG.Open.IsComponentOf L C → 9 ∣ Nat.card L) : Good427 C := by
  intro K hKC hKq hKs hT
  have hA : CFSG.Assembly.IsComponentOf K C :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKC).2
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm hKq, hKs⟩
  obtain ⟨a, ha⟩ := exists_card_eq_sixty_mul hT
  have h9 := h K (CFSG.Assembly.isComponentOf_iff_open.1 hA)
  rw [ha] at h9
  exact not_dvd_sixty_of_nine_dvd dvd_rfl a h9

theorem good427_fixSubgroup_of_conj (γ β : MulAut S)
    (h : Good427 (fixSubgroup (γ⁻¹ * β * γ))) : Good427 (fixSubgroup β) := by
  refine Good427.of_map γ⁻¹.toMonoidHom γ⁻¹.injective ?_
  have hmap : (fixSubgroup β).map γ⁻¹.toMonoidHom = fixSubgroup (γ⁻¹ * β * γ) := by
    ext x
    rw [mem_fixSubgroup]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : β y = y := hy
      show γ⁻¹ (β (γ (γ⁻¹ y))) = γ⁻¹ y
      rw [MulAut.apply_inv_self, hy']
    · intro hx
      refine ⟨γ x, ?_, ?_⟩
      · show β (γ x) = γ x
        have hx' : γ⁻¹ (β (γ x)) = x := hx
        have := congrArg γ hx'
        rwa [MulAut.apply_inv_self] at this
      · show γ⁻¹ (γ x) = x
        exact MulAut.inv_apply_self S γ x
  rw [hmap]
  exact h

end Crit

section Model

abbrev F64 : Type := GaloisField 2 (2 * 3)

instance : NeZero (2 * 3) := ⟨by norm_num⟩

theorem card_F64 : Nat.card F64 = 2 ^ (2 * 3) := GaloisField.card 2 (2 * 3) (by norm_num)

theorem hU8 : UnitaryFieldData 2 3 F64 := ⟨Nat.prime_two, by norm_num, card_F64⟩

abbrev P58 : Type := primeFormP hU8 (oneGram F64 5)

noncomputable def u58Equiv : projSU 5 2 3 ≃* P58 :=
  (CFSG.PGLModel.projSUEquivStatedProj 5 2 3).trans
    ((unitaryPSUEquiv hU8 (by norm_num)).symm.trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization hU8
        (C := (1 : GL (Fin 5) F64)) uni_isPrimeFormGram_one (by norm_num) (by norm_num)).1).symm)

theorem card_gramSU_one {f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData 2 f E) {m : ℕ}
    (hm : 1 ≤ m) :
    (Nat.card (gramSU h (oneGram E m)) : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ (m * (m - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 m, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  rw [← CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h hm]
  congr 1
  have e : CFSG.Open.StatedSU m (2 ^ f) E = gramSU h (1 : Matrix (Fin m) (Fin m) E) :=
    unitarySU_eq_gramSU h m
  rw [e]
  have e1 : oneGram E m = (1 : Matrix (Fin m) (Fin m) E) := Units.val_one
  rw [e1]

theorem nine_dvd_card_blockSU {m : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) :
    9 ∣ Nat.card (CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.blockSU hU8 m) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.gramSU_le_primeFormUnitary hU8)).toEquiv]
  have hc := card_gramSU_one hU8 (m := m) (by omega)
  have h9 : (9 : ℤ) ∣ (Nat.card (gramSU hU8 (oneGram F64 m)) : ℤ) := by
    rw [hc]
    interval_cases m <;> decide
  exact_mod_cast h9

theorem nine_dvd_card_primeFormP_two {E : Type} [Field E] (h : UnitaryFieldData 2 1 E) :
    9 ∣ Nat.card (primeFormP h (oneGram E 5)) := by
  have hbot := uni_normOneScalars_eq_bot h (Or.inl rfl) (by norm_num) (n := 5) (by norm_num)
  have e : primeFormP h (oneGram E 5) ≃* gramSU h (oneGram E 5) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  rw [Nat.card_congr e.toEquiv]
  have hc := card_gramSU_one h (m := 5) (by norm_num)
  have h9 : (9 : ℤ) ∣ (Nat.card (gramSU h (oneGram E 5)) : ℤ) := by
    rw [hc]
    decide
  exact_mod_cast h9

end Model

section Good

theorem good427_P58 (β : MulAut P58) (h3 : β ^ 3 = 1) (h1 : β ≠ 1) : Good427 (fixSubgroup β) := by
  haveI := hU8.finite
  obtain ⟨P0, σ, hσ3, hP⟩ := uni_aut_normal_form hU8 (Or.inr rfl) (by norm_num) (by norm_num)
    ({β} : Set (MulAut P58)) (by simp) (by simp [h3])
  obtain ⟨D, hD, hD3, k, hk⟩ := hP β rfl
  set γ := primeFormConjHom hU8 (oneGram F64 5) P0 with hγ
  refine good427_fixSubgroup_of_conj γ β ?_
  rw [hk]
  by_cases hσk : σ ^ k = 1
  · rw [hσk, map_one, mul_one, uni_psi_inl]
    have hD1 : primeFormConjHom hU8 (oneGram F64 5) D ≠ 1 := by
      intro h0
      apply h1
      have h2 : γ⁻¹ * β * γ = 1 := by
        rw [hk, hσk, map_one, mul_one, uni_psi_inl, h0]
      calc β = γ * (γ⁻¹ * β * γ) * γ⁻¹ := by group
        _ = 1 := by rw [h2]; group
    refine good427_of_nine_dvd fun L hL => ?_
    obtain ⟨I, ⟨j, hj⟩, h2I, -, rfl⟩ :=
      uni_inner_component_good (Or.inr rfl) (by norm_num) (by norm_num) D hD hD3 hD1 hL
    rw [Subgroup.card_map_of_injective
      (uni_theta_uniBlk_injective (h := hU8) (Or.inr rfl) (by norm_num) (by norm_num) hj)]
    have hI5 : I.card ≤ 4 := by
      have : I.card < 5 := by
        calc I.card < Finset.univ.card := Finset.card_lt_card
              (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ I, fun h => hj (h ▸ Finset.mem_univ j)⟩)
          _ = 5 := by simp
      omega
    exact nine_dvd_card_blockSU h2I hI5
  · have hτ3 : (σ ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm k 3, pow_mul, hσ3, one_pow]
    refine good427_of_nine_dvd fun L hL => ?_
    obtain ⟨-, -, F0, _, k0, h0, hk0, ⟨e⟩⟩ :=
      uni_outer_shape (h := hU8) (Or.inr rfl) (by norm_num) (by norm_num) D hD hD3 hτ3 hσk hL
    subst hk0
    rw [Nat.card_congr e.toEquiv]
    exact nine_dvd_card_primeFormP_two h0

end Good

section Row



theorem rowOf427_su58
    : RowOf427 (projSU 5 2 3) :=
  rowOf427_of_noCfgS fun S _ _ hs hna ⟨e⟩ => by
    haveI := hs
    let φ : S ≃* P58 := e.trans u58Equiv
    haveI : Finite P58 := Finite.of_equiv S φ.toEquiv
    refine ⟨NoCfgS427.of_mulEquiv φ fun β h3 h1 => ?_, noONS427_of_card ?_⟩
    · rw [autFix_eq_fixSubgroup]
      exact good427_P58 β h3 h1
    · rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.Sec21.card_projSU (m := 5) (by norm_num)
        (by norm_num), show CFSG.Open.ordTwistedA (5 - 1) (2 ^ 3) = 3 ^ 9 * 236583028271349760 by
          decide]
      norm_num

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
