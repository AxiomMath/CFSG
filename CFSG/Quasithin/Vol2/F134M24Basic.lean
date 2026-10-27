module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Vol2.F134PermCode

public section

namespace CFSG.Quasithin.F134

open Equiv

theorem eq_one_of_commute_of_pow_seven {α : Type*} [Fintype α] [DecidableEq α] {x y : Perm α}
    (hxy : x * y = y * x) (hx : x ^ 7 = 1) (hy : y ^ 3 = 1)
    (hF : (Finset.univ.filter fun i => y i = i).card < 7)
    (hN : Fintype.card α < 21 + (Finset.univ.filter fun i => y i = i).card) : x = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F : Finset α := Finset.univ.filter fun i => y i = i with hFdef
  have hcomm : ∀ i, x (y i) = y (x i) := fun i => by
    rw [← Perm.mul_apply, hxy, Perm.mul_apply]
  have hmemF : ∀ i, i ∈ F ↔ y i = i := fun i => by simp [hFdef]
  have hxF : ∀ i, x i ∈ F ↔ i ∈ F := by
    intro i
    rw [hmemF, hmemF, ← hcomm]
    exact x.injective.eq_iff
  have hfixF : ∀ i ∈ F, x i = i := by
    let xF : Perm {i // i ∈ F} := x.subtypePerm hxF
    have hxF7 : xF ^ 7 ^ 1 = 1 := by
      rw [pow_one, Perm.subtypePerm_pow]
      ext ⟨i, hi⟩
      simp [hx]
    have hmod := Perm.card_compl_support_modEq hxF7
    have hcardF : Fintype.card {i // i ∈ F} = F.card := Fintype.card_coe F
    have hle : xF.supportᶜ.card ≤ Fintype.card {i // i ∈ F} := Finset.card_le_univ _
    have heq : xF.supportᶜ.card = Fintype.card {i // i ∈ F} := by
      unfold Nat.ModEq at hmod
      rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hle (hcardF ▸ hF)),
        Nat.mod_eq_of_lt (hcardF ▸ hF)] at hmod
      exact hmod
    have hsupp : xF.support = ∅ := by
      have h1 : xF.supportᶜ = Finset.univ := Finset.eq_univ_of_card _ heq
      rw [← Finset.compl_univ, ← h1, compl_compl]
    have h1 : xF = 1 := Perm.support_eq_empty_iff.mp hsupp
    intro i hi
    have := congrArg (fun σ : Perm {i // i ∈ F} => (σ ⟨i, hi⟩ : α)) h1
    simpa [xF] using this
  have hyS : ∀ i, y i ∈ x.support ↔ i ∈ x.support := by
    intro i
    rw [Perm.mem_support, Perm.mem_support, hcomm i]
    exact y.injective.ne_iff
  let yS : Perm {i // i ∈ x.support} := y.subtypePerm hyS
  have hyS3 : yS ^ 3 ^ 1 = 1 := by
    rw [pow_one, Perm.subtypePerm_pow]
    ext ⟨i, hi⟩
    simp [hy]
  have hmod3 := Perm.card_compl_support_modEq hyS3
  have hySc : yS.supportᶜ = ∅ := by
    ext ⟨i, hi⟩
    simp only [Finset.mem_compl, Perm.mem_support, not_not, Finset.notMem_empty, iff_false]
    intro h
    have hyi : y i = i := congrArg Subtype.val h
    exact (Perm.mem_support.mp hi) (hfixF i ((hmemF i).mpr hyi))
  rw [hySc, Finset.card_empty, Fintype.card_coe] at hmod3
  have h3 : 3 ∣ x.support.card := (Nat.modEq_zero_iff_dvd.mp hmod3.symm)
  have hx7 : x ^ 7 ^ 1 = 1 := by rw [pow_one]; exact hx
  have hmod7 := Perm.card_compl_support_modEq hx7
  have h7 : 7 ∣ x.support.card := by
    have hc := Finset.card_compl x.support
    unfold Nat.ModEq at hmod7
    have hle : x.support.card ≤ Fintype.card α := Finset.card_le_univ _
    omega
  have hsub : x.support ⊆ Fᶜ := by
    intro i hi
    rw [Finset.mem_compl]
    intro hiF
    exact (Perm.mem_support.mp hi) (hfixF i hiF)
  have hcardS : x.support.card < 21 := by
    have := Finset.card_le_card hsub
    rw [Finset.card_compl] at this
    omega
  have h0 : x.support.card = 0 := by omega
  exact Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h0)

theorem card_fixedPoints_eq_permCode (σ : Perm (Fin 24)) :
    (Finset.univ.filter fun i => σ i = i).card =
      ((Finset.range 24).filter fun i => digW 5 (permCode σ) i = i).card := by
  have h : ((Finset.range 24).filter fun i => digW 5 (permCode σ) i = i) =
      (Finset.univ.filter fun i : Fin 24 => σ i = i).map Fin.valEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply]
    constructor
    · rintro ⟨hi, h⟩
      refine ⟨⟨i, hi⟩, ?_, rfl⟩
      have := digW_permCode (by norm_num) σ ⟨i, hi⟩
      apply Fin.ext
      rw [← this]
      exact h
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j.2, ?_⟩
      rw [digW_permCode (by norm_num) σ j, hj]
  rw [h, Finset.card_map]

end CFSG.Quasithin.F134
