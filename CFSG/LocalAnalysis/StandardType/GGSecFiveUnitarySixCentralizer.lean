module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
import CFSG.LocalAnalysis.StandardType.GGQ2UnitDiag
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcSixCore
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixCover
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSp

public section

namespace CFSG.StandardType.USixTwo

open Matrix CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag

theorem commute_of_map_commute_of_scalar_kernel
    {K : Type} [Field K] {n : ℕ} {U : Subgroup (GL (Fin n) K)}
    {H : Type} [Group H] (ψ : U →* H)
    (hker : ∀ u : U, ψ u = 1 → ∃ c : K,
      ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal (fun _ => c))
    {s t : U} (ht : (((t : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).trace ≠ 0)
    (hc : ψ s * ψ t = ψ t * ψ s) : s * t = t * s := by
  let z : U := s * t * s⁻¹ * t⁻¹
  have hz : ψ z = 1 := by
    simp only [z, map_mul, map_inv]
    rw [hc]
    group
  obtain ⟨c, hcm⟩ := hker z hz
  have hst : s * t * s⁻¹ = z * t := by dsimp [z]; group
  have hmt := congrArg (fun u : U => ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hst
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at hmt
  have he := congrArg Matrix.trace hmt
  rw [Matrix.trace_units_conj, hcm] at he
  have htEq : (((t : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).trace =
      c * (((t : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).trace := by
    simpa only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Finset.mul_sum] using he
  have hc1 : c = 1 := by
    apply mul_right_cancel₀ ht
    simpa using htEq.symm
  have hz1 : z = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hcm, hc1]
    simp
  rw [hz1, one_mul] at hst
  exact mul_inv_eq_iff_eq_mul.mp hst

theorem isDiag_of_commute_three_pairs
    {K : Type} [Field K] [Finite K] {ω : K}
    (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {M : Matrix (Fin 6) (Fin 6) K}
    (h01 : M * USixTwo.diagTwo ω 0 1 = USixTwo.diagTwo ω 0 1 * M)
    (h12 : M * USixTwo.diagTwo ω 1 2 = USixTwo.diagTwo ω 1 2 * M)
    (h34 : M * USixTwo.diagTwo ω 3 4 = USixTwo.diagTwo ω 3 4 * M) : M.IsDiag := by
  let δ : Fin 3 → Fin 6 → K :=
    ![USixTwo.diagVec ω 0 1, USixTwo.diagVec ω 1 2, USixTwo.diagVec ω 3 4]
  have hw1 := USixTwo.omega_ne_one hK hω
  have hw21 := USixTwo.omega_sq_ne_one hK hω
  have hw2w := USixTwo.omega_sq_ne_omega hK hω
  have h1w : (1 : K) ≠ ω := Ne.symm hw1
  have h1w2 : (1 : K) ≠ ω ^ 2 := Ne.symm hw21
  have hww2 : ω ≠ ω ^ 2 := Ne.symm hw2w
  apply RestSp.isDiag_of_commute_diagonal (δ := δ)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [δ, USixTwo.diagVec, Fin.exists_fin_succ]
  · intro k
    fin_cases k
    · exact h01
    · exact h12
    · exact h34

theorem isDiag_of_map_commute_three_pairs
    {K : Type} [Field K] [Finite K] [CharP K 2] {ω : K}
    (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    {H : Type} [Group H]
    (ψ : ↥(unitarySU 2 1 K 6) →* H)
    (hker : ∀ u : ↥(unitarySU 2 1 K 6), ψ u = 1 → ∃ c : K,
      ((u : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal (fun _ => c))
    {s : ↥(unitarySU 2 1 K 6)}
    (h01 : ψ s * ψ (USixTwo.diagTwoSU hω (by decide : (0 : Fin 6) ≠ 1)) =
      ψ (USixTwo.diagTwoSU hω (by decide : (0 : Fin 6) ≠ 1)) * ψ s)
    (h12 : ψ s * ψ (USixTwo.diagTwoSU hω (by decide : (1 : Fin 6) ≠ 2)) =
      ψ (USixTwo.diagTwoSU hω (by decide : (1 : Fin 6) ≠ 2)) * ψ s)
    (h34 : ψ s * ψ (USixTwo.diagTwoSU hω (by decide : (3 : Fin 6) ≠ 4)) =
      ψ (USixTwo.diagTwoSU hω (by decide : (3 : Fin 6) ≠ 4)) * ψ s) :
    (((s : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K).IsDiag := by
  have hf (i j : Fin 6) (hij : i ≠ j)
      (hc : ψ s * ψ (USixTwo.diagTwoSU hω hij) = ψ (USixTwo.diagTwoSU hω hij) * ψ s) :
      ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * USixTwo.diagTwo ω i j =
        USixTwo.diagTwo ω i j * ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    have htr : (((USixTwo.diagTwoSU hω hij :
        ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K).trace ≠ 0 := by
      rw [USixTwo.coe_diagTwoSU, USixTwo.trace_diagTwoGL hK hω hij]
      exact one_ne_zero
    have h := commute_of_map_commute_of_scalar_kernel ψ hker htr hc
    have hgl := congrArg (unitarySU 2 1 K 6).subtype h
    change (s : GL (Fin 6) K) * (USixTwo.diagTwoSU hω hij : GL (Fin 6) K) =
      (USixTwo.diagTwoSU hω hij : GL (Fin 6) K) * (s : GL (Fin 6) K) at hgl
    have hm := congrArg (fun u : GL (Fin 6) K =>
      (u : Matrix (Fin 6) (Fin 6) K)) hgl
    simpa only [Units.val_mul, USixTwo.coe_diagTwoSU_matrix] using hm
  exact isDiag_of_commute_three_pairs hK hω
    (hf 0 1 (by decide) h01) (hf 1 2 (by decide) h12) (hf 3 4 (by decide) h34)

end CFSG.StandardType.USixTwo

namespace CFSG.StandardType.USixTwo

open Matrix CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.StandardType.QTwoExcSix
open Multiplicative

theorem character_pair_diagonal {K : Type} [Field K]
    (χ : Multiplicative (ZMod 3) →* Kˣ) {i j : Fin 6} (hij : i ≠ j) :
    Matrix.diagonal (fun k => ((χ ((exv i / exv j) k) : Kˣ) : K)) =
      USixTwo.diagTwo ((χ (ofAdd 1) : Kˣ) : K) i j := by
  have hexp : (ofAdd (1 : ZMod 3))⁻¹ = (ofAdd (1 : ZMod 3)) ^ 2 := by decide
  have hinv : (χ (ofAdd (1 : ZMod 3)))⁻¹ = χ (ofAdd (1 : ZMod 3)) ^ 2 := by
    rw [← map_inv, hexp, map_pow]
  unfold USixTwo.diagTwo
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [exv, USixTwo.diagVec, Function.update, hij]
  · by_cases hkj : k = j
    · subst k
      simp [exv, hij, USixTwo.diagVec, Function.update, hinv]
    · simp [exv, hki, hkj, USixTwo.diagVec, Function.update]

end CFSG.StandardType.USixTwo

namespace CFSG.StandardType.QTwoExcSix

open Matrix CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open GGQ2Frame.UnitPlacement
open CFSG.StandardType.Line63.H5 Multiplicative

theorem exists_eq_mul_central_of_commute_redFrame
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod 3)))
    (eta' : ↥(redMkB hN).range ≃* (Fin 6 → Multiplicative (ZMod 3)))
    (heta' : ∀ b : Bs, eta' ⟨redMkB hN b, b, rfl⟩ = eta b)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4)
    {σ : ↥(unitarySU 2 1 K 6) →* RedGrp L}
    {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hF : GGSecFiveBPermUniLFrame (redMkB hN).range (redMkL L).range eta' 1 σ χ)
    (hLp : commutator L = ⊤)
    (hA0 : ∀ v : Fin 6 → Multiplicative (ZMod 3), ∏ i, v i = 1 → bv eta v ∈ L) :
    ∀ l ∈ L,
      l * bv eta (exv 0 / exv 1) = bv eta (exv 0 / exv 1) * l →
      l * bv eta (exv 1 / exv 2) = bv eta (exv 1 / exv 2) * l →
      l * bv eta (exv 3 / exv 4) = bv eta (exv 3 / exv 4) * l →
      ∃ v : Fin 6 → Multiplicative (ZMod 3), ∏ i, v i = 1 ∧
        ∃ c ∈ L, (∀ m ∈ L, c * m = m * c) ∧ l = bv eta v * c := by
  classical
  intro l hl h01 h12 h34
  let l' : L := ⟨l, hl⟩
  have hχ : Function.Injective χ := hF.2.2.1
  let ω : K := ((χ (ofAdd 1) : Kˣ) : K)
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have hcub : ω ^ 3 = 1 := by
      simpa only [ω, ← Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg (fun z : Kˣ => (z : K)) (zeta_pow_three χ (ofAdd 1))
    have hne : ω ≠ 1 := by
      intro h
      have hunit : χ (ofAdd (1 : ZMod 3)) = 1 := by
        apply Units.ext
        exact h
      have he : (ofAdd (1 : ZMod 3)) = 1 := hχ (hunit.trans χ.map_one.symm)
      exact (by decide : (ofAdd (1 : ZMod 3)) ≠ 1) he
    have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hcub
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
  have hlbar : redMkL L l' ∈ σ.range := by
    rw [hF.1]
    exact ⟨l', rfl⟩
  obtain ⟨s, hs⟩ := hlbar
  have hf (i j : Fin 6) (hij : i ≠ j)
      (hc : l * bv eta (exv i / exv j) = bv eta (exv i / exv j) * l) :
      σ s * σ (USixTwo.diagTwoSU hω hij) = σ (USixTwo.diagTwoSU hω hij) * σ s := by
    let d : ↥(unitarySU 2 1 K 6) := USixTwo.diagTwoSU hω hij
    let b : Bs := eta.symm (exv i / exv j)
    let br : (redMkB hN).range := ⟨redMkB hN b, b, rfl⟩
    have hbr : eta' br = exv i / exv j := by
      rw [heta']
      exact eta.apply_symm_apply _
    obtain ⟨D, hDN, hDM, hact⟩ := hF.2.2.2 br
    have hDmat : (D : Matrix (Fin 6) (Fin 6) K) = USixTwo.diagTwo ω i j := by
      rw [hDM]
      simpa only [hbr, Equiv.Perm.one_apply, ω] using USixTwo.character_pair_diagonal χ hij
    have hD : D = (d : GL (Fin 6) K) := by
      apply Units.ext
      rw [hDmat, USixTwo.coe_diagTwoSU_matrix]
    have hconj : LineU.conjN D hDN s = d * s * d⁻¹ := by
      apply Subtype.ext
      rw [LineU.coe_conjN, hD]
      rfl
    have hfix : (br : RedGrp L) * σ s * (br : RedGrp L)⁻¹ = σ s := by
      rw [hs]
      change redMk L (Subgroup.inclusion hN b) * redMkL L l' *
        (redMk L (Subgroup.inclusion hN b))⁻¹ = redMkL L l'
      rw [redMk_conj]
      congr 1
      apply Subtype.ext
      change bv eta (exv i / exv j) * l * (bv eta (exv i / exv j))⁻¹ = l
      rw [← hc]
      group
    have he : σ d * σ s * (σ d)⁻¹ = σ s := by
      rw [← map_inv, ← map_mul, ← map_mul, ← hconj, ← hact]
      exact hfix
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hdiag := USixTwo.isDiag_of_map_commute_three_pairs hK hω σ hF.2.1
    (hf 0 1 (by decide) h01) (hf 1 2 (by decide) h12) (hf 3 4 (by decide) h34)
  obtain ⟨w, hw⟩ := exists_diagOf_eq χ (zeta_surjective χ hK hχ) (s : GL (Fin 6) K) hdiag
  have hsum : ∑ i, w i = 0 := by
    have hd := ((mem_unitarySU_iff (USixTwo.fieldDataFour hK)).mp s.2).1
    rw [← hw, det_diagOf] at hd
    have he : ofAdd (∑ i, w i) = (1 : Multiplicative (ZMod 3)) :=
      hχ ((Units.ext hd).trans χ.map_one.symm)
    exact Multiplicative.ofAdd.injective he
  let v : Fin 6 → Multiplicative (ZMod 3) := fun i => ofAdd (w i)
  have hv : ∏ i, v i = 1 := by
    dsimp [v]
    rw [← ofAdd_sum, hsum, ofAdd_zero]
  let a : L := ⟨bv eta v, hA0 v hv⟩
  let c : L := a⁻¹ * l'
  let b : Bs := eta.symm v
  let br : (redMkB hN).range := ⟨redMkB hN b, b, rfl⟩
  have hbr : eta' br = v := by
    rw [heta']
    exact eta.apply_symm_apply _
  obtain ⟨D, hDN, hDM, hact⟩ := hF.2.2.2 br
  have hD : D = (s : GL (Fin 6) K) := by
    apply Units.ext
    rw [hDM, ← hw, coe_diagOf]
    simp only [hbr, Equiv.Perm.one_apply, v]
  have hba : (br : RedGrp L) = redMkL L a := rfl
  have hinner (t : ↥(unitarySU 2 1 K 6)) :
      redMkL L a * σ t * (redMkL L a)⁻¹ = redMkL L l' * σ t * (redMkL L l')⁻¹ := by
    rw [← hba, hact]
    have he : LineU.conjN D hDN t = s * t * s⁻¹ := by
      apply Subtype.ext
      rw [LineU.coe_conjN, hD]
      rfl
    rw [he, map_mul, map_mul, map_inv, hs]
  let pi := (redMkL L).rangeRestrict
  have hcbar : pi c ∈ Subgroup.center (redMkL L).range := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨m, rfl⟩ := (redMkL L).rangeRestrict_surjective y
    have hmbar : redMkL L m ∈ σ.range := by
      rw [hF.1]
      exact ⟨m, rfl⟩
    obtain ⟨t, ht⟩ := hmbar
    have he := hinner t
    rw [ht] at he
    apply Subtype.ext
    change redMkL L m * redMkL L c = redMkL L c * redMkL L m
    dsimp [c]
    rw [map_mul, map_inv]
    calc
      _ = (redMkL L a)⁻¹ * (redMkL L a * redMkL L m * (redMkL L a)⁻¹) *
          redMkL L l' := by group
      _ = (redMkL L a)⁻¹ * (redMkL L l' * redMkL L m * (redMkL L l')⁻¹) *
          redMkL L l' := by rw [he]
      _ = _ := by group
  have hperfect : Group.IsPerfect L := ⟨hLp⟩
  have hker : pi.ker ≤ Subgroup.center L := by
    dsimp [pi]
    rw [redMkL_rangeRestrict_ker]
    exact USixTwo.zTwo_le_center
  have hcentral : c ∈ Subgroup.center L := by
    have hcpre : c ∈ (Subgroup.center (redMkL L).range).comap pi := hcbar
    rwa [CFSG.LocalCores.comap_center_eq_of_perfect hperfect pi
      (redMkL L).rangeRestrict_surjective hker] at hcpre
  refine ⟨v, hv, (c : G), c.2, ?_, ?_⟩
  · intro m hm
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcentral (⟨m, hm⟩ : L))).symm
  · have he : l' = a * c := by dsimp [c]; group
    exact congrArg Subtype.val he

end CFSG.StandardType.QTwoExcSix
