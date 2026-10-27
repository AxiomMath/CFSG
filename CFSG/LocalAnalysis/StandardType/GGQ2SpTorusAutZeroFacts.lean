module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
import CFSG.LocalAnalysis.StandardType.GGSpJoinCentralizerLam
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIso
import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_range_zeta_of_commute (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {h : SpecialLinearGroup (Fin 2) K}
    (hh : h * ζ (Multiplicative.ofAdd 1) = ζ (Multiplicative.ofAdd 1) * h) : h ∈ ζ.range := by
  let g : SpecialLinearGroup (Fin 2) K := ζ (Multiplicative.ofAdd 1)
  let C : Subgroup (SpecialLinearGroup (Fin 2) K) :=
    Subgroup.centralizer ({g} : Set (SpecialLinearGroup (Fin 2) K))
  have hg3 : g ^ 3 = 1 := zeta_pow_three (ζ := ζ) 1
  have hg1 : g ≠ 1 := zeta_ne_one hζ (by decide : (1 : ZMod 3) ≠ 0)
  have hCmem : h ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hh
  have hrange_le : ζ.range ≤ C := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ζ a * g = ζ a * ζ (Multiplicative.ofAdd 1) := rfl
      _ = ζ (a * Multiplicative.ofAdd 1) := (map_mul ζ a _).symm
      _ = ζ (Multiplicative.ofAdd 1 * a) := by rw [mul_comm]
      _ = ζ (Multiplicative.ofAdd 1) * ζ a := map_mul ζ _ a
      _ = g * ζ a := rfl
  have hCne : C ≠ ⊤ := by
    intro htop
    have hwC : sl2W ∈ C := htop ▸ Subgroup.mem_top sl2W
    have hwcomm : sl2W * g = g * sl2W :=
      Subgroup.mem_centralizer_singleton_iff.mp hwC
    have hginv : g⁻¹ = g := by
      rw [← sl2W_conj_eq_inv hK hg3 hg1, hwcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hg2 : g ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp hginv.symm
    have hg_eq_one : g = 1 := by
      have h : g ^ 3 = g := by rw [pow_succ, hg2, one_mul]
      rw [hg3] at h
      exact h.symm
    exact hg1 hg_eq_one
  have hcardSL : Nat.card (SpecialLinearGroup (Fin 2) K) = 6 := by
    let : Fintype K := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card, hK]
    rw [Matrix.card_SL_field, hK']
    decide
  have h3range : Nat.card ζ.range = 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hζ).toEquiv]
    rw [Nat.card_congr Multiplicative.toAdd]
    simp
  have hdvd : Nat.card ζ.range ∣ Nat.card C := Subgroup.card_dvd_of_le hrange_le
  have hCcard_ge : 3 ≤ Nat.card C := by
    rw [h3range] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hCcard_lt : Nat.card C < Nat.card (SpecialLinearGroup (Fin 2) K) := by
    have hne : (C : Set (SpecialLinearGroup (Fin 2) K)) ≠ Set.univ := by
      intro h
      exact hCne (Subgroup.coe_eq_univ.mp h)
    exact Set.ncard_lt_card hne
  have hCcard_lt6 : Nat.card C < 6 := by
    rw [← hcardSL]
    exact hCcard_lt
  have hdvd6 : Nat.card C ∣ 6 := by
    have h := Subgroup.card_dvd_of_le (le_top : C ≤ ⊤)
    rwa [Subgroup.card_top, hcardSL] at h
  have hCcard_eq : Nat.card C = 3 := by
    have hle : Nat.card C ≤ 5 := by omega
    interval_cases h : Nat.card C
    · rfl
    · norm_num at hdvd6
    · norm_num at hdvd6
  have hCeq : ζ.range = C :=
    Subgroup.eq_of_le_of_card_ge hrange_le (by rw [h3range, hCcard_eq])
  rw [hCeq]
  exact hCmem

theorem exists_tau_eq_of_commute (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {c : ↥(StatedSp m K)} (hc : ∀ u, c * tau ζ m u = tau ζ m u * c) :
    ∃ u₀, c = tau ζ m u₀ := by
  let T₀ : SpecialLinearGroup (Fin 2) K := ζ (Multiplicative.ofAdd 1)
  have hg1 : T₀ ≠ 1 := zeta_ne_one hζ (by decide : (1 : ZMod 3) ≠ 0)
  have htr : ((T₀ : Matrix (Fin 2) (Fin 2) K)).trace ≠ 0 :=
    trace_ne_zero_of_pow_eq_one (p := 3) hg1 (by decide : Odd 3)
      (zeta_pow_three (ζ := ζ) 1)
  have hcent : ∀ h : SpecialLinearGroup (Fin 2) K, h * T₀ = T₀ * h → h ∈ ζ.range :=
    fun h hh => mem_range_zeta_of_commute hK hζ hh
  have hcomm : ∀ i : Fin m, c * lam i T₀ = lam i T₀ * c := by
    intro i
    have h := hc (Pi.single i (1 : ZMod 3))
    simpa [T₀, tau_single] using h
  obtain ⟨f, hf⟩ := TorC.mem_range_spPlaneTorus_of_commute (F := K) (ζ := ζ) (T₀ := T₀)
    htr hcent m c hcomm
  refine ⟨fun i => Multiplicative.toAdd (f i), ?_⟩
  rw [← hf]
  rfl

theorem ycode_zero_eq_levi (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {S : Finset (Fin m)} (hS : 3 ≤ S.card) :
    Ycode ζ m (.zero S) = levi m S := by
  let B : Subgroup ↥(StatedSp m K) := blockGroup ζ m (.zero S)
  have hperfS : Group.IsPerfect (StatedSp S.card K) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple (n := S.card) (F := K)
      (by omega) (Or.inr (Or.inr ⟨hK, hS⟩))).1
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e⟩ := nonempty_blockGroup_zero_mulEquiv (ζ := ζ) (m := m) hK hζ (S := S) hSne
  have hperfB : Group.IsPerfect ↥B :=
    @Group.IsPerfect.ofSurjective (StatedSp S.card K) ↥B _ _ e.symm.toMonoidHom hperfS
      e.symm.surjective
  have hcommB : commutator ↥B = ⊤ := hperfB.commutator_eq_top
  have hcommA : ⁅B, B⁆ = B := by
    rw [← Subgroup.map_subtype_commutator B, hcommB, Subgroup.map_top, Subgroup.range_subtype]
  change ⁅B, B⁆ = B
  exact hcommA

end CFSG.StandardType.GGQ2Frame.SpBlocks
