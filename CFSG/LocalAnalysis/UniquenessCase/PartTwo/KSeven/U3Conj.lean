module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.U3Defs
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFieldFixed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)
open CFSG.LieType.Chevalley (fixSubfield)
open CFSG.RankThree.Classical (dvd_and_card_fixSubfield_unitary)
open CFSG.RankThree.PartTwo.KFacts (mem_primeFormUnitary_one exists_psuConj_mul_psuField
  exists_psuConj_conj_psuField_of_prime psuPrimeFormEquiv psuConj psuField congr_psuConj
  congr_psuField)

theorem exists_conj_zpowers_u3Field_of_card_seven {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) (h7 : ¬ 7 ∣ Nat.card (U3 h))
    (W : Subgroup (MulAut (U3 h))) (hW : Nat.card W = 7) :
    ∃ (g : MulAut (U3 h)) (σ : K ≃+* K), orderOf σ = 7 ∧
      Nat.card K = Nat.card (fixSubfield σ) ^ 7 ∧
      W = (Subgroup.zpowers (u3Field h σ)).map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Finite K := h.finite
  have hcyc : IsCyclic ↥W := isCyclic_of_prime_card hW
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hordg : orderOf g = 7 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hW]
  set a : MulAut (U3 h) := (g : MulAut (U3 h)) with ha
  have haord : orderOf a = 7 := by
    rw [ha, Subgroup.orderOf_coe, hordg]
  have hWz : W = Subgroup.zpowers a := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le, ha]
      exact g.2
    · simp only [hW, Nat.card_zpowers, haord, le_refl]
  have hp2 : 2 ≤ p := h.prime.two_le
  have hf1 : 1 ≤ f := h.one_le
  have hpf_ge : 2 ≤ p ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := pow_le_pow_right' (by norm_num) hf1
      _ ≤ p ^ f := pow_le_pow_left' hp2 f
  have hpf_ne : p ^ f ≠ 2 := by
    intro h2
    rw [h2] at hq
    norm_num at hq
  have hq3 : 2 < p ^ f := by omega
  let b : MulAut (unitaryPSU h 3) := (MulAut.congr (psuPrimeFormEquiv h)).symm a
  have haeq : a = MulAut.congr (psuPrimeFormEquiv h) b :=
    ((MulAut.congr (psuPrimeFormEquiv h)).apply_symm_apply a).symm
  have hbord : orderOf b = 7 := by
    rw [← MulEquiv.orderOf_eq (MulAut.congr (psuPrimeFormEquiv h)) b, ← haeq, haord]
  obtain ⟨A, σ, hbA⟩ := exists_psuConj_mul_psuField (h := h) hq3 b
  have hanf : a = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        ⟨A, mem_primeFormUnitary_one A.2⟩ *
      primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ := by
    rw [haeq, hbA, map_mul, congr_psuConj, congr_psuField]
  have hpow : (psuConj h A * psuField h σ) ^ 7 = 1 := by
    rw [← hbA, ← hbord]
    exact pow_orderOf_eq_one b
  have hσ1 : σ ≠ 1 := by
    intro hσ
    have hq' : ¬(3 = 3 ∧ p ^ f = 2) := by
      rintro ⟨-, h2⟩
      exact hpf_ne h2
    let C0 : Matrix (Fin 3) (Fin 3) K := ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    let D : Subgroup (MulAut (U3 h)) := primeFormD h C0
    let I : Subgroup (MulAut (U3 h)) :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner (U3 h)
    have hmemD : a ∈ D := by
      change a ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      rw [hanf, hσ, map_one, mul_one]
      exact ⟨⟨A, mem_primeFormUnitary_one A.2⟩, rfl⟩
    have houter := unitary_full_diagonal_outer_order (h := h) (n := 3) (by norm_num) hq'
    have hgcd : Nat.gcd 3 (p ^ f + 1) = 1 := by
      rw [← Nat.coprime_iff_gcd_eq_one]
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro hd
      have h0 : (p ^ f + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
      have h2 : (p ^ f + 1) % 3 = 2 := by norm_num [Nat.add_mod, hq]
      omega
    have hquot : Nat.card (D ⧸ I.subgroupOf D) = 1 := by
      have houter' : Nat.card (D ⧸ I.subgroupOf D) = Nat.gcd 3 (p ^ f + 1) :=
        houter.2.2.1
      rw [houter', hgcd]
    haveI : Subsingleton (D ⧸ I.subgroupOf D) :=
      Finite.card_le_one_iff_subsingleton.mp (by simp [hquot])
    have hDleI : D ≤ I := by
      intro x hx
      have hx1 : (QuotientGroup.mk (s := I.subgroupOf D) ⟨x, hx⟩ : D ⧸ I.subgroupOf D) = 1 :=
        Subsingleton.elim _ _
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hx1)
    have hinnerA : a ∈ I := hDleI hmemD
    change a ∈ (MulAut.conj : U3 h →* MulAut (U3 h)).range at hinnerA
    obtain ⟨t, ht⟩ := hinnerA
    have hdvd : 7 ∣ Nat.card (U3 h) := by
      rw [← haord, ← ht]
      exact (orderOf_map_dvd (MulAut.conj : U3 h →* MulAut (U3 h)) t).trans
        (orderOf_dvd_natCard t)
    exact h7 hdvd
  obtain ⟨hσord, H, hH⟩ :=
    exists_psuConj_conj_psuField_of_prime (h := h) hq3 A σ Nat.prime_seven
      (by norm_num) hσ1 hpow
  set g₀ : MulAut (U3 h) := MulAut.congr (psuPrimeFormEquiv h) (psuConj h H) with hg₀
  have hac : a = MulAut.conj g₀ (u3Field h σ) := by
    rw [MulAut.conj_apply, haeq, hbA, hH, hg₀]
    simp only [map_mul, map_inv, congr_psuConj, congr_psuField]
  have hfix := dvd_and_card_fixSubfield_unitary (h := h) (p := 7) Nat.prime_seven
    (by norm_num) hσord
  have hf7 : f / 7 * 7 = f := Nat.div_mul_cancel hfix.1
  have hpowK : Nat.card K = Nat.card (fixSubfield σ) ^ 7 := by
    have hexp : 2 * (f / 7) * 7 = 2 * f := by rw [mul_assoc, hf7]
    rw [h.card, hfix.2, ← pow_mul, hexp]
  refine ⟨g₀, σ, hσord, hpowK, ?_⟩
  rw [hWz, hac, MonoidHom.map_zpowers]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
