module

public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.RankThree.GF2n.Stroth80.Conclusion

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

private theorem center_sl2_eq_bot_of_char_two {K : Type*} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hcA, hc1]
  simp [Matrix.one_apply]

private theorem nonempty_mulEquiv_psl2Model_of_isSLModel {Y : Type} [Group Y] {r : ℕ}
    (hr : 1 ≤ r) (h : IsSLModel 2 (2 ^ r) Y) :
    Nonempty (Y ≃* CFSG.Theory.Comparator.PSL2Model r) := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hr
      hKcard
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (GaloisField 2 r) := Fintype.ofFinite _
  have hcardF : Fintype.card K = Fintype.card (GaloisField 2 r) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKcard,
      GaloisField.card 2 r (by omega)]
  let iso : K ≃+* GaloisField 2 r := FiniteField.ringEquivOfCardEq hcardF
  let eP : Matrix.SpecialLinearGroup (Fin 2) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq center_sl2_eq_bot_of_char_two.symm)
  exact ⟨e.trans ((specialLinearGroupEquivStatedSL 2 K).symm.trans
    (eP.trans (CFSG.GorensteinWalter.psl2RingEquiv iso)))⟩

theorem benderType_of_isSLModel_two {Y : Type} [Group Y] {r : ℕ} (hr : 2 ≤ r)
    (h : IsSLModel 2 (2 ^ r) Y) : CFSG.GH74.Uniqueness.Bender.BenderType Y r 1 1 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2Model_of_isSLModel (by omega) h
  exact CFSG.GH74.Uniqueness.Bender.BenderType.linear r hr e

theorem card_le_mul_card_inf_centralizer_of_sl2 {Γ : Type}
    [Group Γ] [Finite Γ] {Y E : Subgroup Γ} {r : ℕ} (hr : 2 ≤ r) (hY : IsSLModel 2 (2 ^ r) ↥Y)
    (hEN : E ≤ Subgroup.normalizer (Y : Set Γ)) (hE2 : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ r * Nat.card ↥(E ⊓ Subgroup.centralizer (Y : Set Γ)) := by
  classical
  let ψ : ↥E →* MulAut ↥Y := (Subgroup.normalizerMonoidHom Y).comp (Subgroup.inclusion hEN)
  have hker : ψ.ker = (E ⊓ Subgroup.centralizer (Y : Set Γ)).subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h := congrArg (fun f : MulAut ↥Y => ((f ⟨y, hy⟩ : ↥Y) : Γ)) hx
      change (x : Γ) * y * (x : Γ)⁻¹ = y at h
      calc y * (x : Γ) = ((x : Γ) * y * (x : Γ)⁻¹) * (x : Γ) := by rw [h]
        _ = (x : Γ) * y := by group
    · rintro ⟨-, hx⟩
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      have h := Subgroup.mem_centralizer_iff.mp hx (y : Γ) y.2
      change (x : Γ) * (y : Γ) * (x : Γ)⁻¹ = (y : Γ)
      rw [← h]
      group
  have hcard : Nat.card ↥E =
      Nat.card ψ.range * Nat.card ↥(E ⊓ Subgroup.centralizer (Y : Set Γ)) := by
    have h := (Subgroup.card_ker_mul_card_range ψ).symm
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
    exact h.trans (mul_comm _ _)
  have hsq : ∀ x ∈ ψ.range, x * x = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hE2 x x.2), map_one]
  have hrange : Nat.card ψ.range ≤ 2 ^ r :=
    ((benderType_of_isSLModel_two hr hY).card_le_of_sq_eq_one_aut ψ.range hsq).2 (by decide)
  calc Nat.card ↥E
      = Nat.card ψ.range * Nat.card ↥(E ⊓ Subgroup.centralizer (Y : Set Γ)) := hcard
    _ ≤ 2 ^ r * Nat.card ↥(E ⊓ Subgroup.centralizer (Y : Set Γ)) :=
      Nat.mul_le_mul_right _ hrange

end CFSG.RankThree.GF2n.Stroth80
