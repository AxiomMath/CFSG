module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl4_fpf_of_row {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hrow : s16h_H5RowSL2 L U Z 2) {a : MulAut W}
    (haL : a ∈ L) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    ∀ u ∈ U, a u * u⁻¹ ∈ Z → u ∈ Z := by
  obtain ⟨-, K, hKf, hKfin, hKcard, hReal⟩ := hrow
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Fintype.card K = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) hcard
  obtain ⟨π, hπ⟩ := hReal
  have hπi : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful (StatedSL 2 K)) hπ
  obtain ⟨β, hβs, hβk, hβe⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (StatedSL 2 K)) rfl rfl hπ
  obtain ⟨hπs, hZU, hkerle, hUinv, hZinv, hsec, hkerinv, -⟩ := hπ
  obtain ⟨γ, hγ⟩ := hπs ⟨a, haL⟩
  have hγ3 : γ ^ 3 = 1 := by
    apply hπi
    rw [map_pow, hγ,
      show (⟨a, haL⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using ha3), map_one]
  have hγ1 : γ ≠ 1 := by
    intro h
    apply ha1
    have h1 : (⟨a, haL⟩ : ↥L) = 1 := by rw [← hγ, h, map_one]
    exact Subtype.ext_iff.mp h1
  have hac : ((π γ : ↥L) : MulAut W) = a := congrArg Subtype.val hγ
  intro u hu huZ
  let uU : ↥U := ⟨u, hu⟩
  have hu' : ((π γ : ↥L) : MulAut W) u ∈ U := hUinv (π γ) u hu
  have hβae := hβe γ uU hu'
  have hauU : a u ∈ U := hac ▸ hUinv (π γ) u hu
  have hauZ : a u * u⁻¹ ∈ U := U.mul_mem hauU (U.inv_mem hu)
  have hβZ : β ⟨a u * u⁻¹, hauZ⟩ = 1 := (hβk ⟨a u * u⁻¹, hauZ⟩).2 huZ
  have hsame : (⟨a u, hauU⟩ : ↥U) =
      ⟨((π γ : ↥L) : MulAut W) (uU : W), hu'⟩ := by
    apply Subtype.ext
    exact (congrArg (fun f : MulAut W => f (uU : W)) hac).symm
  have hβmul : β (⟨a u, hauU⟩ * uU⁻¹) = 1 := by
    have heq : (⟨a u, hauU⟩ * uU⁻¹ : ↥U) = ⟨a u * u⁻¹, hauZ⟩ := by
      apply Subtype.ext
      show a u * (uU : W)⁻¹ = a u * u⁻¹
      rfl
    rw [heq, hβZ]
  have hact : (FFModel.nat (StatedSL 2 K)).act γ (β uU) = β uU := by
    have h1 : β ⟨a u, hauU⟩ * (β uU)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using hβmul
    rw [hsame, hβae] at h1
    exact mul_inv_eq_one.mp h1
  let γ' : ↥(StatedSL 2 K) := γ
  have hγ'3 : γ' ^ 3 = 1 := hγ3
  have hγ'1 : γ' ≠ 1 := hγ1
  have hact' : (FFModel.nat (StatedSL 2 K)).act γ' (β uU) = β uU := hact
  have hv : (((γ' : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      Multiplicative.toAdd (β uU) = Multiplicative.toAdd (β uU) := by
    have h := congrArg Multiplicative.toAdd hact'
    change (((γ' : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      Multiplicative.toAdd (β uU) = Multiplicative.toAdd (β uU) at h
    exact h
  have hβu1 : β uU = 1 := by
    have h0 := CFSG.LocalAnalysis.UniquenessCase.UC22.P22sq.eq_zero_of_mulVec_eq_self
      (g := γ') hγ'3 hγ'1 hv
    let w : Multiplicative (Fin 2 → K) := β uU
    have h0w : w.toAdd = 0 := h0
    have hw1 : w = 1 := by rw [← ofAdd_toAdd w, h0w, ofAdd_zero]
    exact hw1
  exact (hβk uU).mp hβu1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
