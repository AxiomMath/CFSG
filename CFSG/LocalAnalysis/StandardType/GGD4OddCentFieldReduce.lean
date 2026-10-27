module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldSchur

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGD4FieldCentralizerInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 2 ^ n → Odd n →
    ∀ s : MulAut (D4Recipe K), s ^ 3 = 1 →
      GGInnField (LargeEvenInnSet (D4Recipe K)) (D4FieldSet K) s →
      s ∉ LargeEvenInnSet (D4Recipe K) →
      ∀ J : Subgroup (D4Recipe K), IsComponentOf J (ggAutFixedSubgroup s) →
        ∃ (k : Type) (_ : Field k) (_ : Finite k) (n' : ℕ),
          Nat.card k = 2 ^ n' ∧ n = 3 * n' ∧ IsSimpleGroup (D4Recipe k) ∧
          (∃ x y : D4Recipe k, x * y ≠ y * x) ∧ Nonempty (D4Recipe k ≃* ↥J) ∧
          ∀ a : MulAut (D4Recipe K),
            ¬ GGInnField (LargeEvenInnSet (D4Recipe K)) (D4FieldSet K) a →
              ¬ ∃ j ∈ J, ∀ x ∈ J, a x = j * x * j⁻¹

theorem ggD4OddCentField_core (h : GGD4FieldCentralizerInput) {K : Type} [Group K] [Finite K]
    (hK : commutator K = ⊤) {A : Subgroup (MulAut K)} {σ : MulAut K} {J : Subgroup K}
    (hloc : GGKLocal A σ J) (hA : Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4)
    {F₁ : Type} [Field F₁] [Finite F₁] {n : ℕ} (hF₁ : Nat.card F₁ = 2 ^ n)
    (θ : K ⧸ Subgroup.center K ≃* D4Recipe F₁)
    (hdatum : GGOddCentDatum A ⟨.D, 4, n⟩ (LargeEvenInnSet (D4Recipe F₁)) (D4FieldSet F₁) θ)
    (hinn : GGInnField (LargeEvenInnSet (D4Recipe F₁)) (D4FieldSet F₁) (ggInducedAut θ σ))
    (hout : ggInducedAut θ σ ∉ LargeEvenInnSet (D4Recipe F₁)) :
    LargeEvenMarking J fun lab' _ _ I' _ θ' =>
      lab'.tag = .D ∧ lab'.rank = 4 ∧ Odd lab'.n ∧ ¬ GGAutsInduceOn A J θ' I' := by
  obtain ⟨hAutLocal, -⟩ := hloc
  obtain ⟨hEA, hσA, -, hcomp, hJsA⟩ := hAutLocal
  have hpow : σ ^ 3 = 1 := hEA.2 σ hσA
  have hodd : Odd n := hdatum.2.2.1
  obtain ⟨a₀, ha₀A, ha₀out⟩ := hdatum.2.2.2.2.2
  have hcardA : Nat.card A = 3 ^ 4 := by
    rcases hA with h3 | h4
    · exact absurd (hdatum.2.2.2.2.1 h3 σ hσA hinn) hout
    · exact h4
  have h3dvd : 3 ∣ n := hdatum.2.2.2.1 hcardA
  have hn2 : 2 ≤ n := by
    have hodd1 := hodd
    obtain ⟨m, hm⟩ := h3dvd
    obtain ⟨t, ht⟩ := hodd1
    omega
  have hZ : Subgroup.center K = ⊥ := ggD4_center_eq_bot (X := K) (K := F₁) hK hn2 hF₁ θ
  let e : K ≃* D4Recipe F₁ := mulEquivOfCenterBot θ hZ
  let s : MulAut (D4Recipe F₁) := ggInducedAut θ σ
  have hs3 : s ^ 3 = 1 := by
    show (ggInducedAut θ σ) ^ 3 = 1
    rw [← map_pow, hpow, map_one]
  let J' : Subgroup (D4Recipe F₁) := J.map e.toMonoidHom
  have hJ' : IsComponentOf J' (ggAutFixedSubgroup s) := by
    show IsComponentOf (J.map e.toMonoidHom) (ggAutFixedSubgroup (ggInducedAut θ σ))
    rw [ggAutFixedSubgroup_ggInducedAut θ hZ σ]
    exact isComponentOf_map_mulEquiv e hcomp
  obtain ⟨k, _, _, n', hk, hn3, hksimp, hkna, ⟨fk⟩, hkey⟩ :=
    h F₁ n hF₁ hodd s hs3 hinn hout J' hJ'
  let fJ : ↥J ≃* ↥J' := Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
  let f : D4Recipe k ≃* ↥J := fk.trans fJ.symm
  have hn'1 : 1 ≤ n' := by omega
  have hodd' : Odd n' := by
    rw [hn3] at hodd
    exact (Nat.odd_mul.mp hodd).2
  have hJperf : commutator ↥J = ⊤ := hcomp.2.2.1
  have hinv : ∀ x ∈ J, a₀ x ∈ J := fun x hx => hJsA a₀ ha₀A x hx
  have hout' : ¬ ∃ j ∈ J, ∀ x ∈ J, a₀ x = j * x * j⁻¹ := by
    rintro ⟨j, hjJ, hj⟩
    refine hkey (ggInducedAut θ a₀) ha₀out
      ⟨e j, Subgroup.mem_map_of_mem e.toMonoidHom hjJ, ?_⟩
    intro x' hx'
    obtain ⟨x, hxJ, rfl⟩ := Subgroup.mem_map.mp hx'
    calc ggInducedAut θ a₀ (e x) = e (a₀ x) :=
          ggInducedAut_mulEquivOfCenterBot θ hZ a₀ x
      _ = e (j * x * j⁻¹) := by rw [hj x hxJ]
      _ = e j * e x * (e j)⁻¹ := by simp only [map_mul, map_inv]
  refine largeEvenMarking_D4_of_mulEquiv (X := ↥J) hJperf hn'1 hk f.symm hksimp hkna ?_
  intro hZ'
  exact ⟨rfl, rfl, hodd', not_ggAutsInduceOn_of_outer f.symm hZ' ha₀A hinv hout'⟩

theorem ggD4OddCentFieldInput_of_kg5 (h : GGD4FieldCentralizerInput) : GGD4OddCentFieldInput := by
  intro K _ _ hK A σ J hloc hA P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  obtain ⟨tag, rank, n⟩ := lab
  by_cases hD : tag = .D ∧ rank = 4
  ·
    obtain ⟨rfl, rfl⟩ := hD
    refine ⟨hperf, ⟨.D, 4, n⟩, hlab, ?_⟩
    unfold LargeEvenRawDatumLegacy at hraw ⊢
    rw [if_neg (by norm_num : ¬ (4 : ℕ) = 3)] at hraw
    rw [if_neg (by norm_num : ¬ (4 : ℕ) = 3)]
    obtain ⟨F₁, i1, i2, hF₁, hs, hna, θ, hPθ⟩ := hraw
    exact ⟨F₁, i1, i2, hF₁, hs, hna, θ, hPθ, fun hdat hinn hout =>
      ggD4OddCentField_core h hK hloc hA hF₁ θ hdat hinn hout⟩
  ·
    refine ⟨hperf, ⟨tag, rank, n⟩, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hdat _ _ => absurd ⟨hdat.1, hdat.2.1⟩ hD⟩

end CFSG.StandardType
