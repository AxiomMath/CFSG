module

public import CFSG.RankThree.PartTwo.KFacts.KS21LocalRankOmega
public import CFSG.RankThree.PartTwo.Census.Spin.Consumers
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21LocalRank

open Matrix CFSG.Assembly.LowTwoRank TauCeti
open CFSG.Assembly.RankThreeEven (localRank projImage projOmegaMinus)
open CFSG.Adapters.RankTwoModelTransports (statedProjEquivMapMk statedProjCongr)

section Four

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
include hK

omit [CharP K 2] in
theorem pow_four_eq_self (x : K) : x ^ 4 = x := by
  let _ := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem mul_mul_eq_zero (x : K) : x * (x + 1) * (x ^ 2 + x + 1) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h := pow_four_eq_self hK x
  linear_combination h + (x ^ 3 + x ^ 2 + x) * h2

theorem exists_root_four : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let _ := Fintype.ofFinite K
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω ∉ ({0, 1} : Finset K) := by
    by_contra h
    push Not at h
    have h1 : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => h x
    have h2 := Finset.card_le_card h1
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK] at h2
    have h3 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  have h := mul_mul_eq_zero hK ω
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h0 | h1
    · exact absurd h0 hω.1
    · exact absurd (by linear_combination h1 - h2 : ω = 1) hω.2
  · exact ⟨ω, h'⟩

theorem root_of_irreducible {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    b ≠ 0 ∧ (c / b ^ 2) ^ 2 + c / b ^ 2 + 1 = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb : b ≠ 0 := by
    rintro rfl
    apply hirr (c ^ 2)
    have := pow_four_eq_self hK c
    linear_combination this + c * h2
  refine ⟨hb, ?_⟩
  set d := c / b ^ 2 with hd
  have hc : c = d * b ^ 2 := by
    rw [hd]
    field_simp
  have h := mul_mul_eq_zero hK d
  rcases mul_eq_zero.mp h with h' | h'
  · exfalso
    rcases mul_eq_zero.mp h' with h0 | h1
    · apply hirr 0
      rw [hc, h0]
      ring
    · obtain ⟨ω, hω⟩ := exists_root_four hK
      apply hirr (b * ω)
      rw [hc, show d = 1 by linear_combination h1 - h2]
      linear_combination b ^ 2 * hω
  · exact h'

end Four

section Isometry

variable {K : Type} [Field K]

@[expose] noncomputable def substOm (e : K) (f : Kˣ) : GL Om K :=
  diagOm (Function.update (1 : Om → Kˣ) (.inr (.inr 1)) f) *
    ⟨1 + e • single (.inr (.inr 0)) (.inr (.inr 1)) 1,
      1 - e • single (.inr (.inr 0)) (.inr (.inr 1)) 1, by
        rw [mul_sub, mul_one, add_mul, one_mul, smul_mul_smul_comm,
          single_mul_single_of_ne _ _ _ _ (by decide), smul_zero, add_zero, add_sub_cancel_right],
      by
        rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm,
          single_mul_single_of_ne _ _ _ _ (by decide), smul_zero, add_zero,
          add_sub_cancel_right]⟩

theorem mulVec_substOm (e : K) (f : Kˣ) (v : Om → K) (j : Om) :
    (((substOm e f : GL Om K) : Matrix Om Om K) *ᵥ v) j =
      (Function.update (1 : Om → Kˣ) (.inr (.inr 1)) f j : Kˣ) *
        (v j + if j = .inr (.inr 0) then e * v (.inr (.inr 1)) else 0) := by
  rw [substOm, Units.val_mul, ← mulVec_mulVec, coe_diagOm, mulVec_diagonal]
  congr 1
  change ((1 + e • single (.inr (.inr 0)) (.inr (.inr 1)) 1 : Matrix Om Om K) *ᵥ v) j = _
  rw [add_mulVec, one_mulVec, smul_mulVec, single_mulVec, Pi.add_apply, Pi.smul_apply,
    Function.update_apply]
  split_ifs <;> simp

theorem quadMinus_substOm [CharP K 2] {b c b' c' e : K} {f : Kˣ} (hf : b * f = b')
    (he : e ^ 2 + b' * e + c * (f : K) ^ 2 = c') (v : Om → K) :
    StatedQuadMinus 4 K b c (((substOm e f : GL Om K) : Matrix Om Om K) *ᵥ v) =
      StatedQuadMinus 4 K b' c' v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [show (((substOm e f : GL Om K) : Matrix Om Om K) *ᵥ v) = fun j =>
      (Function.update (1 : Om → Kˣ) (.inr (.inr 1)) f j : Kˣ) *
        (v j + if j = .inr (.inr 0) then e * v (.inr (.inr 1)) else 0) from
      funext (mulVec_substOm e f v), quadMinus_apply, quadMinus_apply]
  simp
  rw [← he, ← hf]
  linear_combination (e * v (.inr (.inr 0)) * v (.inr (.inr 1))) * h2

theorem exists_isometry_four [Finite K] [CharP K 2] (hK : Nat.card K = 4) {b c b' c' : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hirr' : ∀ s : K, s ^ 2 + b' * s + c' ≠ 0) :
    ∃ T : GL Om K, ∀ v, StatedQuadMinus 4 K b c (((T : GL Om K) : Matrix Om Om K) *ᵥ v) =
      StatedQuadMinus 4 K b' c' v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hb, hd⟩ := root_of_irreducible hK hirr
  obtain ⟨hb', hd'⟩ := root_of_irreducible hK hirr'
  set d := c / b ^ 2 with hddef
  set d' := c' / b' ^ 2 with hd'def
  have hc : c = d * b ^ 2 := by rw [hddef]; field_simp
  have hc' : c' = d' * b' ^ 2 := by rw [hd'def]; field_simp
  have hfb : b' / b ≠ 0 := div_ne_zero hb' hb
  let f : Kˣ := Units.mk0 (b' / b) hfb
  have hf : b * (f : K) = b' := by
    change b * (b' / b) = b'
    field_simp
  have hcf : c * (f : K) ^ 2 = d * b' ^ 2 := by
    change c * (b' / b) ^ 2 = d * b' ^ 2
    rw [hc]
    field_simp
  have hdd : (d' + d) * (d' + d + 1) = 0 := by
    linear_combination hd' + hd + (d * d' - 1) * h2
  rcases mul_eq_zero.mp hdd with h | h
  · refine ⟨substOm 0 f, quadMinus_substOm hf ?_⟩
    rw [hcf, hc']
    linear_combination (-b' ^ 2) * h + (d * b' ^ 2) * h2
  · refine ⟨substOm (d * b') f, quadMinus_substOm hf ?_⟩
    rw [hcf, hc']
    linear_combination b' ^ 2 * hd - b' ^ 2 * h + (d * b' ^ 2) * h2

end Isometry

noncomputable def statedProjOmegaMinusEquiv (K : Type) [Field K] (b c : K) :
    StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) ≃* projOmegaMinus 3 K b c :=
  (statedProjEquivMapMk (StatedOmega (StatedQuadMinus 4 K b c))).trans
    (MulEquiv.subgroupCongr
      (CFSG.RankThree.PartOne.projImage_statedOmegaMinus_eq_projOmegaMinus 4 K b c))

theorem exists_le_localRank_projOmegaMinus_four {b c : GaloisField 2 2}
    (hirr : ∀ s : GaloisField 2 2, s ^ 2 + b * s + c ≠ 0)
    [Finite (projOmegaMinus 3 (GaloisField 2 2) b c)] :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ 3 ≤ localRank r (projOmegaMinus 3 (GaloisField 2 2) b c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  let q4 : PrimePower := ⟨2, 2, Nat.prime_two, two_pos⟩
  have hv : (LieTypeIndex.twistedD 4 q4).Valid := by simp
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q4 hv rfl
    (MulEquiv.refl _)
  obtain ⟨b', c', hirr', ⟨φ⟩⟩ := CFSG.RankThree.PartOne.projOmegaMinus_of_statedClassicalModel hm
  obtain ⟨T, hT⟩ := exists_isometry_four hK hirr hirr'
  let ψ : projOmegaMinus 3 (GaloisField 2 2) b' c' ≃* projOmegaMinus 3 (GaloisField 2 2) b c :=
    ((statedProjOmegaMinusEquiv _ b' c').symm.trans
      (statedProjCongr (MulAut.conj T)
        (CFSG.ClassicalInvolution.Upgrade.map_statedOmega_conj T hT)
        (CFSG.ClassicalInvolution.Upgrade.map_conj_statedScalars T))).trans
      (statedProjOmegaMinusEquiv _ b c)
  have : Finite (CFSGIndex.lie ⟨.twistedD 4 q4, hv⟩).Group :=
    Finite.of_equiv _ (φ.trans ψ).symm.toEquiv
  obtain ⟨r, hr, hr3, hloc⟩ :=
    CFSG.RankThree.PartTwo.Census.Spin.spinLarge_twistedD4 q4 hv rfl le_rfl
  refine ⟨r, hr, hr3, ?_⟩
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv (φ.trans ψ) hr]
  exact hloc

end CFSG.RankThree.PartTwo.KFacts.KS21LocalRank
