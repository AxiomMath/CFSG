module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU58OuterField
public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.KFacts.KS21.U58
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Assembly.RankThreeEven (projSU)

theorem exists_conj_sylow_le {G : Type} [Group G] [Finite G] (P : Sylow 3 G) (H : Subgroup G)
    (h3 : ¬ 3 ∣ H.index) : ∃ g : G, ∀ y ∈ (P : Subgroup G), g * y * g⁻¹ ∈ H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 H) := inferInstance
  have hQp : IsPGroup 3 ((Q : Subgroup H).map H.subtype) := Q.isPGroup'.map H.subtype
  obtain ⟨R, hQR⟩ := IsPGroup.exists_le_sylow hQp
  have hfac : (Nat.card H).factorization 3 = (Nat.card G).factorization 3 := by
    rw [← H.card_mul_index, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h3, add_zero]
  have hcard : Nat.card ((Q : Subgroup H).map H.subtype) = Nat.card (R : Subgroup G) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective H),
      Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity R, hfac]
  have hQR' : (Q : Subgroup H).map H.subtype = (R : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hQR hcard.ge
  have hRle : (R : Subgroup G) ≤ H := by
    rw [← hQR']
    exact Subgroup.map_subtype_le _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P R
  refine ⟨g, fun y hy => hRle ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  have h := Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (P : Subgroup G) hy
  rwa [MulAut.smul_def, MulAut.conj_apply] at h

theorem outerRow_SUI : OuterRow SUI := by
  intro _ σ hσ hout hwc
  have h3 := three_not_dvd_index_of_autWeaklyClosed hσ hout hwc
  obtain ⟨P0s, hP0s⟩ := exists_sylow_P₀
  obtain ⟨g, hg⟩ := exists_conj_sylow_le P0s _ h3
  have hgy : ∀ y ∈ P₀, σ (g * y * g⁻¹) = g * y * g⁻¹ := fun y hy =>
    (mem_comap_conj_centralizer_iff center_SUI σ _).mp (hg y (by rw [hP0s]; exact hy))
  obtain ⟨α, hα⟩ : ∃ α : MulAut SUI, α = (MulAut.conj g)⁻¹ * σ * MulAut.conj g := ⟨_, rfl⟩
  have hαy : ∀ y ∈ P₀, α y = y := by
    intro y hy
    rw [hα, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply,
      hgy y hy]
    group
  have hα3 : α ^ 3 = 1 := by
    have e : α = (MulAut.conj g)⁻¹ * σ * ((MulAut.conj g)⁻¹)⁻¹ := by rw [inv_inv, hα]
    rw [e, conj_pow, hσ, mul_one, mul_inv_cancel]
  have hσe : σ = MulAut.conj g * α * (MulAut.conj g)⁻¹ := by
    rw [hα]
    group
  have hαout : α ∉ (MulAut.conj : SUI →* MulAut SUI).range := by
    rintro ⟨y, hy⟩
    apply hout
    refine ⟨g * y * g⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hy, ← hσe]
  obtain ⟨A, hA, φ, hαA, hφk⟩ := exists_unitary_field α
  have hφ3 : φ ^ 3 = 1 := by
    have h := hφk 1 (by rw [pow_one]; exact hα3)
    rwa [pow_one] at h
  set v : (Fin 3 → ZMod 9) × ZMod 9 := (![1, 0, 0], 0) with hv
  have hxP : τS (Multiplicative.ofAdd v) ∈ P₀ := ⟨v, 0, by rw [pow_zero, mul_one]⟩
  have hE : A * glAut φ (TauCeti.diagGL (ev v)) * A⁻¹ = TauCeti.diagGL (ev v) := by
    have h1 := hαA (τS (Multiplicative.ofAdd v))
    rw [hαy _ hxP, coe_τS'] at h1
    exact h1.symm
  have hval1 : (1 : ZMod 9).val = 1 := rfl
  have hval0 : (0 : ZMod 9).val = 0 := rfl
  have hev : ev v = ![(ζ9 : Kˣ), 1, 1, 1, (ζ9 : Kˣ)⁻¹] := by
    funext i
    fin_cases i <;> simp [ev, e5, hv, hval1, hval0]
  have htr := congrArg (fun X : GL (Fin 5) K => (X : Matrix (Fin 5) (Fin 5) K).trace) hE
  simp only [Units.val_mul] at htr
  rw [Matrix.trace_units_conj, glAut_diagGL, TauCeti.diagGL_coe, TauCeti.diagGL_coe,
    Matrix.trace_diagonal, Matrix.trace_diagonal, hev] at htr
  simp [Fin.sum_univ_five] at htr
  have hz0 : (ζ9 : K) ≠ 0 := Units.ne_zero ζ9
  have hkey : (ζ9 : K) + (ζ9 : K)⁻¹ = φ (ζ9 : K) + (φ (ζ9 : K))⁻¹ := by
    linear_combination -htr
  have hηz : (φ (ζ9 : K) - (ζ9 : K)) * (φ (ζ9 : K) - (ζ9 : K)⁻¹) = 0 := by
    have hη0 : φ (ζ9 : K) ≠ 0 := (map_ne_zero φ).mpr hz0
    have h1 : φ (ζ9 : K) * (φ (ζ9 : K))⁻¹ = 1 := mul_inv_cancel₀ hη0
    have h2 : (ζ9 : K) * (ζ9 : K)⁻¹ = 1 := mul_inv_cancel₀ hz0
    linear_combination (-(φ (ζ9 : K))) * hkey + h2 - h1
  have hz : φ (ζ9 : K) = (ζ9 : K) ∨ φ (ζ9 : K) = (ζ9 : K)⁻¹ := by
    rcases mul_eq_zero.mp hηz with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hφ1 : φ = 1 := eq_one_of_pow_three_of_zeta hφ3 hz
  obtain ⟨g₀, hg₀⟩ := exists_SUI_conj_eq hA
  apply hαout
  refine ⟨g₀, MulEquiv.ext fun x => Subtype.ext ?_⟩
  have h1 : glAut φ ((x : SUI) : GL (Fin 5) K) = ((x : SUI) : GL (Fin 5) K) := by
    rw [hφ1, map_one]
    rfl
  rw [MulAut.conj_apply, hαA x, h1, hg₀]
  simp

theorem outerRow_u58 : OuterRow (projSU 5 2 3) :=
  OuterRow.of_mulEquiv equivSUI.symm outerRow_SUI

end CFSG.RankThree.PartTwo.Sec4.RonanK432
