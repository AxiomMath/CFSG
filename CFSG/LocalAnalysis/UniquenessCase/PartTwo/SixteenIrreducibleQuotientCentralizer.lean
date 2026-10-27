module

public import CFSG.LinearAlgebra.IrreducibleBinaryCentralizerExponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixedQuotientCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKQuotMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank
public import CFSG.RankThree.FFModules.BinaryTransport
public import CFSG.Quasithin.Background.F918E1
public import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}

theorem centralizer_cube_eq_one_of_irreducible_quotient_rank_eight
    (hW : ∀ w : W, w ^ 2 = 1)
    (hq : CFSG.Open.IsQuasisimple ↥H)
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (hdim : E3.mQuot (⊤ : Subgroup W) (fixV H) = 8)
    (hord : 5 ≤ (Nat.card ↥H).factorization 2) :
    ∀ a ∈ Subgroup.centralizer (H : Set (MulAut W)), a ^ 3 = 1 := by
  classical
  obtain ⟨Q, hQc, hQf, q, rho, hqsurj, hqker, hρinj, heq, hexp, hcardQ, hirrQ⟩ :=
    s16k_qm_quotMap (W := W) (H := H) hq hcomm hW
  letI := hQc
  letI := hQf
  letI : Module (ZMod 2) (Additive Q) := CFSG.RankThree.FFModules.moduleOfSq hexp
  let e : MulAut Q ≃* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q) :=
    (CFSG.Quasithin.mulAutLin Q).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive Q)).symm
  let Hlin : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q)) :=
    rho.range.map e.toMonoidHom
  have hcardRange : Nat.card rho.range = Nat.card ↥H := by
    rw [MonoidHom.range_eq_map]
    simpa using (Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥H)) hρinj)
  have hcardHlin : Nat.card Hlin = Nat.card ↥H := by
    rw [Subgroup.card_map_of_injective (K := rho.range) e.injective]
    exact hcardRange
  have h2 : 5 ≤ (Nat.card Hlin).factorization 2 := by
    rw [hcardHlin]
    exact hord
  have hcardQ8 : Nat.card Q = 2 ^ 8 := by rw [hcardQ, hdim]
  have hcardAdd : Nat.card (Additive Q) = 2 ^ 8 :=
    (Nat.card_congr (Additive.ofMul : Q ≃ Additive Q)).symm.trans hcardQ8
  have hfr : Module.finrank (ZMod 2) (Additive Q) = 8 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q)
    rw [hcardAdd, Nat.card_zmod] at h
    exact ((Nat.pow_right_inj (by norm_num : 1 < 2)).1 h).symm
  have hirrLin : ∀ U : Submodule (ZMod 2) (Additive Q),
      (∀ h ∈ Hlin, ∀ u ∈ U,
        (h : Additive Q →ₗ[ZMod 2] Additive Q) u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    let B : Subgroup Q :=
      { carrier := {b | Additive.ofMul b ∈ U}
        mul_mem' := by
          intro a b ha hb
          show Additive.ofMul (a * b) ∈ U
          rw [ofMul_mul]
          exact U.add_mem ha hb
        one_mem' := by
          show Additive.ofMul (1 : Q) ∈ U
          simp
        inv_mem' := by
          intro a ha
          show Additive.ofMul a⁻¹ ∈ U
          rw [ofMul_inv]
          exact U.neg_mem ha }
    have hB : ∀ l : ↥H, ∀ b ∈ B, (rho l : MulAut Q) b ∈ B := by
      intro l b hb
      have hmem : e (rho l) ∈ Hlin :=
        Subgroup.mem_map_of_mem e.toMonoidHom (MonoidHom.mem_range.mpr ⟨l, rfl⟩)
      have h := hU (e (rho l)) hmem (Additive.ofMul b) hb
      have hcoe : (e (rho l) : Additive Q →ₗ[ZMod 2] Additive Q) =
          (CFSG.RankThree.FFModules.autRep Q (rho l) :
            Additive Q →ₗ[ZMod 2] Additive Q) := rfl
      rw [hcoe, CFSG.RankThree.FFModules.autRep_apply] at h
      exact h
    rcases hirrQ hirr B hB with hB0 | hBtop
    · left
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hxB : Additive.toMul x ∈ B := hx
      rw [hB0, Subgroup.mem_bot] at hxB
      exact Additive.toMul.injective (by simpa using hxB)
    · right
      rw [Submodule.eq_top_iff']
      intro x
      exact (show Additive.toMul x ∈ B from by rw [hBtop]; trivial)
  have hexpLin : ∀ a ∈ Subgroup.centralizer (Hlin :
      Set (LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q))), a ^ 3 = 1 :=
    CFSG.LinearAlgebra.centralizer_cube_eq_one_of_irreducible_binary_eight hfr Hlin hirrLin h2
  have hexpQ : ∀ a ∈ Subgroup.centralizer (rho.range : Set (MulAut Q)), a ^ 3 = 1 := by
    intro a ha
    have hcent : e a ∈ Subgroup.centralizer (Hlin :
        Set (LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hh
      have hxa : x * a = a * x := Subgroup.mem_centralizer_iff.mp ha x hx
      change e x * e a = e a * e x
      rw [← map_mul, ← map_mul, hxa]
    have h3 := hexpLin (e a) hcent
    have h3' : e (a ^ 3) = 1 := by simpa using h3
    exact e.injective (by simpa using h3')
  exact centralizer_pow_eq_one_of_fixed_quotient (n := 3) q rho hqsurj hqker heq hcomm hexpQ

theorem pRank_le_of_normalizes_irreducible_quotient_rank_eight
    {A : Subgroup (MulAut W)}
    (hW : ∀ w : W, w ^ 2 = 1)
    (hq : CFSG.Open.IsQuasisimple ↥H)
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (hdim : E3.mQuot (⊤ : Subgroup W) (fixV H) = 8)
    (hord : 5 ≤ (Nat.card ↥H).factorization 2)
    (hAN : A ≤ Subgroup.normalizer (H : Set (MulAut W)))
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    CFSG.Open.pRank p A ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥H)) := by
  classical
  have hcent := centralizer_cube_eq_one_of_irreducible_quotient_rank_eight
    hW hq hcomm hirr hdim hord
  have hN : ∀ n ∈ A, ∀ l ∈ H, n * l * n⁻¹ ∈ H := Subgroup.le_normalizer_iff.mp hAN
  have hmain := s16k_pRank_le_of_normalizer (Q := W) (L' := H) (N := A) hN hp
  have hcent0 : CFSG.Open.pRank p
      (A ⊓ Subgroup.centralizer (H : Set (MulAut W))) = 0 := by
    refine le_antisymm ?_ (Nat.zero_le _)
    refine CFSG.SectionRank.pRank_le hp.one_lt (k := 0) ?_
    intro E hE hEel
    rw [pow_zero]
    have hE3 : ∀ x : E, x ^ 3 = 1 := by
      intro x
      apply Subtype.ext
      simpa using hcent (x : MulAut W) ((hE x.2).2)
    have h3E : IsPGroup 3 E := by
      apply IsPGroup.of_exponent_dvd_pow (n := 1)
      rw [pow_one]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one hE3
    have hsub : Subsingleton E :=
      IsPGroup.subsingleton_of_coprime hEel.isPGroup h3E
        ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
    exact Finite.card_le_one_iff_subsingleton.mpr hsub
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
