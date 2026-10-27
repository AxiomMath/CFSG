module

public import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclBasic
import CFSG.RankThree.PartOne.N1322.CaseHess

public section

namespace CFSG.LocalAnalysis.UniquenessCase.GL3Excl

open Matrix CFSG.RepresentationTheory
open CFSG.RankThree.PartOne.N1322 (Cz)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem mul_self_eq_one_of_diagonal {r : ℕ} {t : GL (Fin 3) (ZMod r)}
    {β : Fin 3 → ZMod r} (htd : (t : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal β)
    (hβ : ∀ i, β i * β i = 1) : t * t = 1 :=
  Units.ext (by rw [Units.val_mul, htd, diagonal_mul_diagonal, funext hβ, diagonal_one,
    Units.val_one])

theorem false_of_extraspecial {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {W K : Subgroup (GL (Fin 3) (ZMod r))} (hnorm : ∀ g ∈ W, ∀ x ∈ K, g * x * g⁻¹ ∈ K)
    (hK : IsIrreducibleMatrixRep K.subtype) (hcard : Nat.card K = 27)
    (hext : CFSG.IsExtraspecialPGroup 3 K) {t₁ t₂ : GL (Fin 3) (ZMod r)} (ht₁ : t₁ ∈ W)
    (ht₁d : (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![-1, 1, 1]) (ht₂ : t₂ ∈ W)
    (ht₂d : (t₂ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![1, -1, 1]) : False := by
  have hneg : (-1 : ZMod r) ≠ 1 := by
    haveI : Fact (2 < r) := ⟨lt_of_le_of_ne (Fact.out : r.Prime).two_le (Ne.symm hr2)⟩
    exact ZMod.neg_one_ne_one
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hnc : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := CFSG.RankThree.PartOne.N1322.ext27_noncomm hcard hext
    exact ⟨a, a.2, b, b.2, fun hc => hab (Subtype.ext hc)⟩
  have hsch := CFSG.RankThree.PartOne.N1322.scalar_commutant_of_noncomm hK hnc
  have hcenGL : ∀ z : K, z ∈ Subgroup.center K → Cz (z : GL (Fin 3) (ZMod r)) := by
    intro z hz g
    exact CFSG.RankThree.PartOne.N1322.central_of_center hsch (fun x hx => by
      simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)) g
  have hdich : ∀ u ∈ W, u * u = 1 →
      (∀ a ∈ K, Cz (u * a * u⁻¹ * a⁻¹)) ∨ (∀ a ∈ K, Cz (u * a * u⁻¹ * a)) := by
    intro u hu hu2
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    obtain ⟨φ, hφ⟩ : ∃ φ : K ≃* K, ∀ x : K, ((φ x : K) : GL (Fin 3) (ZMod r)) = u * x * u⁻¹ :=
      ⟨CFSG.RankThree.PartOne.N1322.actOn hnorm hu, fun x => rfl⟩
    have hφz : ∀ z ∈ Subgroup.center K, φ z = z := by
      intro z hz
      apply Subtype.ext
      rw [hφ, hcenGL z hz u]
      group
    have hφ2 : ∀ x, φ (φ x) = x := by
      intro x
      apply Subtype.ext
      rw [hφ, hφ, huinv]
      calc u * (u * (x : GL (Fin 3) (ZMod r)) * u) * u
          = (u * u) * (x : GL (Fin 3) (ZMod r)) * (u * u) := by group
        _ = x := by rw [hu2]; group
    rcases CFSG.RankThree.PartOne.N1322.ext27_pm hcard hext φ hφz hφ2 with h1 | h1
    · exact Or.inl fun a ha => by simpa [hφ] using hcenGL _ (h1 ⟨a, ha⟩)
    · exact Or.inr fun a ha => by simpa [hφ] using hcenGL _ (h1 ⟨a, ha⟩)
  have hscal : ∀ u ∈ W, u * u = 1 → (∀ a ∈ K, Cz (u * a * u⁻¹ * a⁻¹)) →
      ∀ β : Fin 3 → ZMod r, (u : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal β →
        ∀ i j, β i = β j := by
    intro u hu hu2 htr β hβ
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    refine diagonal_apply_eq_of_commute_irreducible hK (fun x hx => ?_)
    obtain ⟨ζ, hζdef⟩ : ∃ z, z = u * x * u⁻¹ * x⁻¹ := ⟨_, rfl⟩
    have hζ := htr x hx
    rw [← hζdef] at hζ
    have hζK : ζ ∈ K := by
      rw [hζdef]
      exact K.mul_mem (hnorm u hu x hx) (K.inv_mem hx)
    have hux : u * x * u⁻¹ = ζ * x := by rw [hζdef]; group
    have e0 : u * (u * x * u⁻¹) * u⁻¹ = x := by
      rw [huinv]
      calc u * (u * x * u) * u = (u * u) * x * (u * u) := by group
        _ = x := by rw [hu2]; group
    have hζ2 : ζ * ζ = 1 := by
      have e1 : ζ * ζ * x = x := by
        calc ζ * ζ * x = ζ * (u * x * u⁻¹) := by rw [hux, mul_assoc]
          _ = (ζ * u) * x * u⁻¹ := by group
          _ = (u * ζ) * x * u⁻¹ := by rw [← hζ u]
          _ = u * (ζ * x) * u⁻¹ := by group
          _ = u * (u * x * u⁻¹) * u⁻¹ := by rw [hux]
          _ = x := e0
      exact mul_right_cancel (by rw [one_mul]; exact e1)
    have hζmem : (⟨ζ, hζK⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr (fun y => Subtype.ext (hζ y))
    have hζ3 : ζ ^ 3 = 1 := by
      simpa using congrArg Subtype.val
        (CFSG.RankThree.PartOne.N1322.ext27_center_cube hext _ hζmem)
    have hζ1 : ζ = 1 := by
      calc ζ = ζ * (ζ * ζ) := by rw [hζ2, mul_one]
        _ = ζ ^ 3 := (pow_three ζ).symm
        _ = 1 := hζ3
    have hxu : u * x = x * u := mul_inv_eq_iff_eq_mul.mp (by rw [hux, hζ1, one_mul])
    rw [← hβ, ← Units.val_mul, ← Units.val_mul, hxu]
  have h1sq : t₁ * t₁ = 1 := mul_self_eq_one_of_diagonal ht₁d (fun i => by fin_cases i <;> simp)
  have h2sq : t₂ * t₂ = 1 := mul_self_eq_one_of_diagonal ht₂d (fun i => by fin_cases i <;> simp)
  have hneg₁ : ∀ a ∈ K, Cz (t₁ * a * t₁⁻¹ * a) := (hdich t₁ ht₁ h1sq).resolve_left
    fun htr => hneg (by simpa using hscal t₁ ht₁ h1sq htr _ ht₁d 0 1)
  have hneg₂ : ∀ a ∈ K, Cz (t₂ * a * t₂⁻¹ * a) := (hdich t₂ ht₂ h2sq).resolve_left
    fun htr => hneg (by simpa using hscal t₂ ht₂ h2sq htr _ ht₂d 1 0)
  have hsd : ((t₁ * t₂ : GL (Fin 3) (ZMod r)) : Matrix (Fin 3) (Fin 3) (ZMod r)) =
      diagonal ![-1, -1, 1] := by
    rw [Units.val_mul, ht₁d, ht₂d, diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  have hssq : t₁ * t₂ * (t₁ * t₂) = 1 :=
    mul_self_eq_one_of_diagonal hsd (fun i => by fin_cases i <;> simp)
  have h02 := hscal _ (W.mul_mem ht₁ ht₂) hssq
    (CFSG.RankThree.PartOne.N1322.trv_of_neg hneg₁ hneg₂) _ hsd 0 2
  exact hneg (by simpa using h02)

end CFSG.LocalAnalysis.UniquenessCase.GL3Excl
