module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusU4Tools
public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusGlue
public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofPlusU4
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcInner
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU projImage)
open CFSG.RankThree.PartOne.KFU
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg (fixedSubfield hypEquiv card_fixedSubfield mem_fixedSubfield)
open scoped MatrixGroups

namespace Item211Res4Proof

open Item228Census3Proof Item228Census5Proof U4Lines

local notation "V₄" => Fin 2 ⊕ Fin 2

set_option hygiene false in
local notation "SU₄" => SUid (unitaryInvolution K p 1) 4

set_option hygiene false in
local notation "PSU₄" => projImage (SUid (unitaryInvolution K p 1) 4)

theorem iotaSo_neg_one {F : Type} [Field F] (σ : F ≃+* F) : iotaSo σ (-1) = -1 := by
  apply Units.ext
  rw [coe_iotaSo, Units.val_neg, Units.val_one, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkSo]

theorem mapF_neg_one {F : Type} [Field F] (E : Subfield F) : mapF E (-1) = -1 := by
  apply Subtype.ext
  rw [coe_mapF, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

set_option maxHeartbeats 400000 in
theorem excMinus_U4_short {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp3 : 3 < p) (hp1 : p % 3 = 1) (hK : Nat.card K = (p ^ 1) ^ 2)
    (hZ : Subgroup.center PSU₄ = ⊥)
    {D T : Subgroup (MulAut PSU₄)} (hDi : D ≤ (MulAut.conj : PSU₄ →* MulAut PSU₄).range)
    (hTi : T ≤ (MulAut.conj : PSU₄ →* MulAut PSU₄).range)
    (hDe : IsElemAbelian 3 D) (hTe : IsElemAbelian 2 T) (hT4 : Nat.card T = 4)
    (hTD : ⁅T, D⁆ = T) {A : SU₄} (hA3 : A ^ 3 = 1) {R : GL (Fin 4) K} {α : Kˣ}
    (hQ : ∀ g, g ∈ SU₄ ↔ R * g * R⁻¹ ∈ SU (unitaryInvolution K p 1) 4) (hα3 : α ^ 3 = 1)
    (hα1 : α ≠ 1) (hQA : R * (A : GL (Fin 4) K) * R⁻¹ = diagU ![α, α, α⁻¹, α⁻¹])
    (hfD : MulAut.conj (projRestrict SU₄ A) ∈ D)
    (hfT : MulAut.conj (projRestrict SU₄ A) ∈ Subgroup.centralizer (T : Set (MulAut PSU₄)))
    {u : MulAut PSU₄} (hu : u ∈ T) (hu1 : u ≠ 1) {q : MulAut PSU₄}
    (hq : q ∈ inSubgroup (CFSG.pCore 2)
      (threeGen ((MulAut.conj : PSU₄ →* MulAut PSU₄).range ⊓
        Subgroup.centralizer ({u} : Set (MulAut PSU₄))) ⊓
          Subgroup.centralizer (T : Set (MulAut PSU₄)))) :
    q * MulAut.conj (projRestrict SU₄ A) = MulAut.conj (projRestrict SU₄ A) * q := by
  classical
  have hp' : p.Prime := Fact.out
  have hσ : ∀ c, unitaryInvolution K p 1 (unitaryInvolution K p 1 c) = c :=
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK).invol
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hZ4 : ∀ s : Kˣ, GeneralLinearGroup.scalar (Fin 4) s ∈ SU₄ → s ^ 4 = 1 :=
    fun s hs => pow_four_eq_one_of_det_scalar (mem_SUid.1 hs).1
  have hinj := Item211Lie2Proof.conj_injective' hZ
  obtain ⟨hφ, hker, hdec⟩ := data_U4_short hK hQ hα3 hα1 hQA
  obtain ⟨-, hcomm, -⟩ := bridge _ hZ hZ4 hA3 _ hφ hdec hDi hDe hfD
  have hTC : T ≤ (MulAut.conj : PSU₄ →* MulAut PSU₄).range ⊓
      Subgroup.centralizer ({MulAut.conj (projRestrict SU₄ A)} : Set (MulAut PSU₄)) :=
    fun t ht => Subgroup.mem_inf.mpr ⟨hTi ht, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hfT t ht)⟩
  have hTr := le_range_of_commutator_eq hTC (le_inf_centralizer hDe hfD hDi) hTD hcomm
  set φ := (MulAut.conj R⁻¹).toMonoidHom.comp (iotaSo (unitaryInvolution K p 1)) with hφdef
  set ι4 := iotaOf _ φ hφ.1 with hι4
  have hιker : ∀ x, ι4 x = 1 ↔ x = 1 ∨ x = -1 := fun x => by
    rw [hι4, iotaOf_eq_one_iff _ hZ, hker]
    refine ⟨sl2_eq_one_or_neg_one_of_mem_center, ?_⟩
    rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (by simp)
  obtain ⟨t₂, ht₂T, ht₂1, ht₂u⟩ := exists_ne_one_ne hT4 u
  obtain ⟨U, hUu⟩ := hTr hu
  obtain ⟨V, hVt⟩ := hTr ht₂T
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hTe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ T, x * x = 1 := fun x hx => by rw [← sq]; exact hTe.2 x hx
  obtain ⟨hUm, hVm, hUVm⟩ := quat_of_commuting_involutions h2 ι4 hιker (U := U) (V := V)
    (by rw [hUu]; exact hsq u hu) (by rw [hVt]; exact hsq t₂ ht₂T)
    (by rw [hUu, hVt]; exact hTcomm u hu t₂ ht₂T) (by rw [hUu]; exact hu1)
    (by rw [hVt]; exact ht₂1) (by rw [hUu, hVt]; exact ht₂u)
  have : NeZero p := ⟨hp'.ne_zero⟩
  obtain ⟨a₀, c₀, hac₀⟩ := CharP.sq_add_sq K p (-1)
  have hac : (a₀ : K) * a₀ + (c₀ : K) * c₀ = -1 := by
    rw [← sq, ← sq, hac₀]
    push_cast
    rfl
  obtain ⟨PR, PiR, hPP, hPP', hUq, hVq⟩ :=
    exists_quat_normal_form (fun r hr => hr.isUnit) h2 hac hUm hVm hUVm
  have hl0 : unitaryInvolution K p 1 PiR.det ≠ 0 := by
    rw [map_ne_zero]
    intro h0
    have := congrArg Matrix.det hPP
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  let Z : GL V₄ K := ⟨zMat (unitaryInvolution K p 1) PR (unitaryInvolution K p 1 PiR.det),
    zMatInv (unitaryInvolution K p 1) PiR (unitaryInvolution K p 1 PiR.det),
    zMat_mul_zMatInv hPP hl0, zMatInv_mul_zMat hPP' hl0⟩
  have hZform : cstar (unitaryInvolution K p 1) (Z : Matrix V₄ V₄ K) * formQ *
      (Z : Matrix V₄ V₄ K) = formV := cstar_zMat_formQ hσ hPP
  set Z' := Z * (reindexV₄ K).symm R with hZ'
  have htrans := mem_SUid_iff_formQ hQ Z hZform
  have hconjφ : ∀ S : SL(2, K), ((coordZ Z' (φ S) : GL V₄ K) : Matrix V₄ V₄ K) =
      zMat (unitaryInvolution K p 1) PR (unitaryInvolution K p 1 PiR.det) *
        fromBlocks (S : Matrix (Fin 2) (Fin 2) K) 0 0
          (dMat * (S : Matrix (Fin 2) (Fin 2) K).map (unitaryInvolution K p 1) * dMat) *
        zMatInv (unitaryInvolution K p 1) PiR (unitaryInvolution K p 1 PiR.det) := by
    intro S
    rw [hZ', coordZ_mul_reindex]
    have e : R * φ S * R⁻¹ = iotaSo (unitaryInvolution K p 1) S := by
      change R * (R⁻¹ * iotaSo (unitaryInvolution K p 1) S * R⁻¹⁻¹) * R⁻¹ = _
      group
    rw [e, Units.val_mul, Units.val_mul, coe_reindexV₄_symm, coe_iotaSo, submatrix_blkSo]
    rfl
  have hUZ : ((coordZ Z' (φ U) : GL V₄ K) : Matrix V₄ V₄ K) = quatBlockU (a₀ : K) c₀ := by
    have hU' : PR * (U : Matrix (Fin 2) (Fin 2) K) * PiR = !![-(a₀ : K), -c₀; -c₀, a₀] := by
      rw [Matrix.mul_assoc, hUq, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
    have hfix : (!![-(a₀ : K), -c₀; -c₀, a₀] : Matrix (Fin 2) (Fin 2) K).map
        (unitaryInvolution K p 1) = !![-(a₀ : K), -c₀; -c₀, a₀] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hconjφ, zMat_conj_blkSo hU' hfix hl0, quatBlockU]
    simp
  have hVZ : ((coordZ Z' (φ V) : GL V₄ K) : Matrix V₄ V₄ K) = quatBlockV := by
    have hV' : PR * (V : Matrix (Fin 2) (Fin 2) K) * PiR = !![0, -1; 1, 0] := by
      rw [Matrix.mul_assoc, hVq, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
    have hfix : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K).map
        (unitaryInvolution K p 1) = !![0, -1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hconjφ, zMat_conj_blkSo hV' hfix hl0, quatBlockV]
    simp
  let X₀K : SL(2, K) := ⟨!![(α : K), 0; 0, ((α⁻¹ : Kˣ) : K)], by
    rw [Matrix.det_fin_two]
    simp⟩
  have hAZ : coordZ Z' (A : GL (Fin 4) K) = blkDiag X₀K := by
    apply Units.ext
    rw [hZ', coordZ_mul_reindex, Units.val_mul, Units.val_mul, coe_reindexV₄_symm, hQA, diagU_val,
      coe_blkDiag]
    have e : (diagonal fun i => ((![α, α, α⁻¹, α⁻¹] : Fin 4 → Kˣ) i : K)) =
        diagonal ![(α : K), α, ((α⁻¹ : Kˣ) : K), ((α⁻¹ : Kˣ) : K)] := by
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [e, submatrix_diagonal_four]
    exact zMat_conj_diag hPP hl0 _ _
  set F := fixedSubfield K p 1 with hFdef
  have hF : ∀ c, c ∈ F ↔ unitaryInvolution K p 1 c = c := fun c => mem_fixedSubfield
  have hcardF : Nat.card F = p := by rw [hFdef, card_fixedSubfield hK, pow_one]
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hcardF]; exact hp'.ne_zero)
  have hfixB : ∀ B : SL(2, F), ((mapF F B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map
      (unitaryInvolution K p 1) = (mapF F B : SL(2, K)) := by
    intro B
    ext i j
    rw [Matrix.map_apply, coe_mapF, Matrix.map_apply]
    exact (hF _).mp (B.1 i j).2
  set psiU : SL(2, F) →* GL (Fin 4) K := (psiZ Z').comp (mapF F) with hpsiU
  have hpsi : ∀ B, coordZ Z' (psiU B) = blkDiag (mapF F B) := fun B => coordZ_psiZ Z' _
  have hpsiMem : ∀ B, psiU B ∈ SU₄ := fun B => by
    rw [htrans, hpsi]
    exact isFormQ_blkDiag (hfixB B)
  set κ := iotaOf _ psiU hpsiMem with hκ
  have hκa : ∀ B, κ B = MulAut.conj (projRestrict SU₄ ⟨psiU B, hpsiMem B⟩) := fun B => rfl
  have hαF : (α : K) ∈ F := by
    rw [hF, unitaryInvolution_apply, pow_one]
    obtain ⟨k, hk⟩ : ∃ k, p = 3 * k + 1 := ⟨p / 3, by omega⟩
    have hα3' : (α : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hα3, Units.val_one]
    rw [hk, pow_succ, pow_mul, hα3', one_pow, one_mul]
  have hαF' : ((α⁻¹ : Kˣ) : K) ∈ F := by
    rw [Units.val_inv_eq_inv_val]
    exact F.inv_mem hαF
  obtain ⟨X₀, hX₀⟩ := exists_mapF_eq F (M := X₀K) (fun i j => by
    fin_cases i <;> fin_cases j
    · exact hαF
    · exact F.zero_mem
    · exact F.zero_mem
    · exact hαF')
  have hκf : κ X₀ = MulAut.conj (projRestrict SU₄ A) := by
    rw [hκa]
    congr 2
    apply Subtype.ext
    apply (coordZ Z').injective
    change coordZ Z' (psiU X₀) = _
    rw [hpsi, hX₀, hAZ]
  have hκker : ∀ B, κ B = 1 → B = 1 ∨ B = -1 := by
    intro B hB
    rw [hκ, iotaOf_eq_one_iff _ hZ] at hB
    have hB' : mapF F B ∈ (ProjGenLinGroup.mk.comp blkDiag).ker := by
      have e : (ProjGenLinGroup.mk.comp (psiZ Z')).ker =
          (ProjGenLinGroup.mk.comp blkDiag).ker := by
        rw [psiZ, ker_mk_reindexV₄, ker_mk_conj]
      rw [← e]
      exact hB
    rcases eq_one_or_neg_one_of_mk_blkDiag hB' with h | h
    · left
      exact mapF_injective F (by rw [h, map_one])
    · right
      exact mapF_injective F (by rw [h, mapF_neg_one])
  have hcommZ : ∀ (B : SL(2, F)) (X : GL (Fin 4) K) (hX : X ∈ SU₄),
      ((coordZ Z' X : GL V₄ K) : Matrix V₄ V₄ K) * blkDiag (mapF F B) =
        blkDiag (mapF F B) * (coordZ Z' X : GL V₄ K) →
      κ B * MulAut.conj (projRestrict SU₄ ⟨X, hX⟩) =
        MulAut.conj (projRestrict SU₄ ⟨X, hX⟩) * κ B := by
    intro B X hX h
    rw [hκa, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    apply (coordZ Z').injective
    apply Units.ext
    change ((coordZ Z' (psiU B * X) : GL V₄ K) : Matrix V₄ V₄ K) =
      ((coordZ Z' (X * psiU B) : GL V₄ K) : Matrix V₄ V₄ K)
    rw [map_mul, map_mul, hpsi, Units.val_mul, Units.val_mul, h]
  have hκU : ∀ B, κ B * u = u * κ B := by
    intro B
    rw [← hUu]
    refine hcommZ B _ (hφ.1 U) ?_
    rw [hUZ, coe_blkDiag]
    exact (quatBlockU_commute _ _ _).symm
  have hκV : ∀ B, κ B * t₂ = t₂ * κ B := by
    intro B
    rw [← hVt]
    refine hcommZ B _ (hφ.1 V) ?_
    rw [hVZ, coe_blkDiag]
    exact (quatBlockV_commute _).symm
  have hκT : ∀ B, κ B ∈ Subgroup.centralizer (T : Set (MulAut PSU₄)) := by
    intro B
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rcases four_group_cases hTe hT4 hu ht₂T hu1 ht₂1 ht₂u t ht with h | h | h | h
    · rw [h, one_mul, mul_one]
    · rw [h, hκU]
    · rw [h, hκV]
    · rw [h]
      calc u * t₂ * κ B = u * (t₂ * κ B) := mul_assoc _ _ _
        _ = u * (κ B * t₂) := by rw [hκV]
        _ = (u * κ B) * t₂ := (mul_assoc _ _ _).symm
        _ = (κ B * u) * t₂ := by rw [hκU]
        _ = κ B * (u * t₂) := mul_assoc _ _ _
  have hqH : q ∈ threeGen ((MulAut.conj : PSU₄ →* MulAut PSU₄).range ⊓
        Subgroup.centralizer ({u} : Set (MulAut PSU₄))) ⊓
          Subgroup.centralizer (T : Set (MulAut PSU₄)) := Subgroup.map_subtype_le _ hq
  have hΔInn : threeGen ((MulAut.conj : PSU₄ →* MulAut PSU₄).range ⊓
      Subgroup.centralizer ({u} : Set (MulAut PSU₄))) ≤
        (MulAut.conj : PSU₄ →* MulAut PSU₄).range :=
    (Subgroup.closure_le _).mpr fun x hx => (Subgroup.mem_inf.mp hx.1).1
  obtain ⟨y, rfl⟩ := hΔInn (Subgroup.mem_inf.mp hqH).1
  obtain ⟨X, rfl⟩ := projRestrict_surjective SU₄ y
  have hqT := (Subgroup.mem_inf.mp hqH).2
  have hXW : ∀ W : SL(2, K), W * W = -1 → ι4 W ∈ T →
      ((coordZ Z' (X : GL (Fin 4) K) : GL V₄ K) : Matrix V₄ V₄ K) * (coordZ Z' (φ W)) =
          (coordZ Z' (φ W) : GL V₄ K) * (coordZ Z' (X : GL (Fin 4) K) : GL V₄ K) ∨
        ((coordZ Z' (X : GL (Fin 4) K) : GL V₄ K) : Matrix V₄ V₄ K) * (coordZ Z' (φ W)) =
          -(((coordZ Z' (φ W) : GL V₄ K) : Matrix V₄ V₄ K) *
            (coordZ Z' (X : GL (Fin 4) K) : GL V₄ K)) := by
    intro W hW hWT
    have hc : projRestrict SU₄ X * projRestrict SU₄ ⟨φ W, hφ.1 W⟩ =
        projRestrict SU₄ ⟨φ W, hφ.1 W⟩ * projRestrict SU₄ X := hinj (by
      rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp hqT _ hWT).symm)
    have hφneg : φ (-1) = -1 := by
      change R⁻¹ * iotaSo (unitaryInvolution K p 1) (-1) * R⁻¹⁻¹ = -1
      rw [iotaSo_neg_one, mul_neg_one, neg_mul, mul_inv_cancel]
    have hh : ((φ W : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (φ W : GL (Fin 4) K) = -1 := by
      rw [← Units.val_mul, ← map_mul, hW, hφneg, Units.val_neg, Units.val_one]
    exact coordZ_rel Z' (X := (X : GL (Fin 4) K)) (Y := φ W)
      (commute_or_anticommute_of_mk SU₄ hc hh)
  have hUU : U * U = -1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, hUm, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one])
  have hVV : V * V = -1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, hVm, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one])
  have hgU := hXW U hUU (by rw [hUu]; exact hu)
  have hgV := hXW V hVV (by rw [hVt]; exact ht₂T)
  rw [hUZ] at hgU
  rw [hVZ] at hgV
  obtain ⟨x, Y, hx, hXY⟩ := quat_centralizer_decomp h2 hac _ hgU hgV
  have hUform := ((htrans _).mp (hφ.1 U)).2
  have hVform := ((htrans _).mp (hφ.1 V)).2
  rw [hUZ] at hUform
  rw [hVZ] at hVform
  have hxform : cstar (unitaryInvolution K p 1) x * formQ * x = formQ := by
    rcases hx with rfl | rfl | rfl | rfl
    · rw [cstar_one, Matrix.one_mul, Matrix.mul_one]
    · exact hUform
    · exact hVform
    · rw [cstar_mul]
      calc cstar (unitaryInvolution K p 1) quatBlockV *
          cstar (unitaryInvolution K p 1) (quatBlockU (a₀ : K) c₀) * formQ *
            (quatBlockU (a₀ : K) c₀ * quatBlockV) =
          cstar (unitaryInvolution K p 1) quatBlockV *
            (cstar (unitaryInvolution K p 1) (quatBlockU (a₀ : K) c₀) * formQ *
              quatBlockU (a₀ : K) c₀) * quatBlockV := by simp only [Matrix.mul_assoc]
        _ = formQ := by rw [hUform, hVform]
  have hXform := ((htrans _).mp X.2).2
  rw [hXY] at hXform
  have hY := cstar_jMat_of_formQ hxform hXform
  obtain ⟨β, hβF⟩ := exists_beta hF Y hY
  have hβ : ∀ B, κ (β B) =
      MulAut.conj (projRestrict SU₄ X) * κ B * (MulAut.conj (projRestrict SU₄ X))⁻¹ := by
    intro B
    have hmat : ((coordZ Z' (X : GL (Fin 4) K) : GL V₄ K) : Matrix V₄ V₄ K) *
        (blkDiag (mapF F B) : GL V₄ K) =
          (blkDiag (CFSG.GH74.Generic.S3.glConj Y (mapF F B)) : GL V₄ K) *
            (coordZ Z' (X : GL (Fin 4) K) : GL V₄ K) := by
      rw [hXY, coe_blkDiag, coe_blkDiag, CFSG.GH74.Generic.S3.coe_glConj]
      exact quat_blk_conj hx (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) _
    have hGL : coordZ Z' (X : GL (Fin 4) K) * blkDiag (mapF F B) *
        (coordZ Z' (X : GL (Fin 4) K))⁻¹ =
          blkDiag (CFSG.GH74.Generic.S3.glConj Y (mapF F B)) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Units.ext hmat
    have e : MulAut.conj (projRestrict SU₄ X) * κ B * (MulAut.conj (projRestrict SU₄ X))⁻¹ =
        MulAut.conj (projRestrict SU₄ (X * ⟨psiU B, hpsiMem B⟩ * X⁻¹)) := by
      rw [hκa]
      simp only [map_mul, map_inv]
    rw [e, hκa]
    congr 2
    apply Subtype.ext
    apply (coordZ Z').injective
    change coordZ Z' (psiU (β B)) =
      coordZ Z' ((X : GL (Fin 4) K) * psiU B * (X : GL (Fin 4) K)⁻¹)
    rw [map_mul, map_mul, map_inv, hpsi, hpsi, hβF, hGL]
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcardF]
    omega
  have h2F : (2 : F) ≠ 0 := fun h => h2 (by rw [← map_ofNat F.subtype 2, h, map_zero])
  have hX₀e : ∀ i j, (((X₀ : Matrix (Fin 2) (Fin 2) F) i j : F) : K) =
      (X₀K : Matrix (Fin 2) (Fin 2) K) i j := fun i j => by
    have := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) i j) hX₀
    simpa [coe_mapF] using this
  have hX₀ns : ¬ Item211Lie3Proof.IsScalar2 (X₀ : Matrix (Fin 2) (Fin 2) F) := by
    rintro ⟨-, -, h00⟩
    have e : (((X₀ : Matrix (Fin 2) (Fin 2) F) 0 0 : F) : K) =
        (((X₀ : Matrix (Fin 2) (Fin 2) F) 1 1 : F) : K) := congrArg Subtype.val h00
    rw [hX₀e, hX₀e] at e
    exact ne_inv_of_cube hα3 hα1 (by simpa [X₀K] using e)
  have hX₀3 : X₀ ^ 3 = 1 := by
    apply mapF_injective F
    rw [map_pow, hX₀, map_one]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    have hα3' : (α : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hα3, Units.val_one]
    change (!![(α : K), 0; 0, ((α⁻¹ : Kˣ) : K)]) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, hα3']
    ring_nf
    simp [hα3']
  have hf3 : MulAut.conj (projRestrict SU₄ A) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hA3, map_one, map_one]
  exact commute_of_kappa hF4 h2F hu hfT hf3 ⟨_, rfl⟩ κ (fun B => ⟨_, rfl⟩) hκT hκker hX₀ns
    hX₀3 hκf hq β hβ

theorem two_ne_zero_of_card {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p) : (2 : F) ≠ 0 := by
  intro h
  have h1 : addOrderOf (1 : F) ∣ 2 :=
    addOrderOf_dvd_of_nsmul_eq_zero (by rw [two_nsmul, one_add_one_eq_two, h])
  have h2 := addOrderOf_dvd_natCard (1 : F)
  rw [hF] at h2
  have h3 : addOrderOf (1 : F) ∣ Nat.gcd 2 p := Nat.dvd_gcd h1 h2
  rw [(Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2), Nat.dvd_one,
    AddMonoid.addOrderOf_eq_one_iff] at h3
  exact one_ne_zero h3

theorem excMinusFor_U4 {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp3 : 3 < p) (hp1 : p % 3 = 1) (hK : Nat.card K = (p ^ 1) ^ 2)
    (hZ : Subgroup.center PSU₄ = ⊥) : Item211Lie2Proof.ExcMinusFor PSU₄ := by
  classical
  have hZ4 : ∀ s : Kˣ, GeneralLinearGroup.scalar (Fin 4) s ∈ SU₄ → s ^ 4 = 1 :=
    fun s hs => pow_four_eq_one_of_det_scalar (mem_SUid.1 hs).1
  have hinj := Item211Lie2Proof.conj_injective' hZ
  intro D T hDi hTi hDe _ hTe hT4 _ hTD u hu hu1 f hf
  obtain ⟨hfD, hfT⟩ := Subgroup.mem_inf.mp hf
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  by_cases hf1 : f = 1
  · rw [hf1, mul_one, one_mul]
  obtain ⟨y, rfl⟩ := hDi hfD
  have hy3 : y ^ 3 = 1 := hinj (by rw [map_pow, hDe.2 _ hfD, map_one])
  have hy1 : y ≠ 1 := fun h => hf1 (by rw [h, map_one])
  obtain ⟨A, rfl, hA3, hA1⟩ := exists_lift_cube SU₄ hZ4 y (orderOf_eq_prime hy3 hy1)
  obtain ⟨R, α, hQ, hα3, hα1, hD | hD⟩ := exists_normal_form_U4 hp1 hK A hA3 hA1
  ·
    exfalso
    obtain ⟨F, _, _, p', hp', hp5, hcF, φ, hφ, hker, hdec⟩ :=
      sl2Datum_U4_long hp3 hK hQ hα3 hα1 hD
    obtain ⟨-, hcomm, -⟩ := bridge _ hZ hZ4 hA3 φ hφ hdec hDi hDe hfD
    have hTC : T ≤ (MulAut.conj : PSU₄ →* MulAut PSU₄).range ⊓
        Subgroup.centralizer ({MulAut.conj (projRestrict SU₄ A)} : Set (MulAut PSU₄)) :=
      fun t ht => Subgroup.mem_inf.mpr ⟨hTi ht, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hfT t ht)⟩
    have hTr := le_range_of_commutator_eq hTC (le_inf_centralizer hDe hfD hDi) hTD hcomm
    have hιinj : Function.Injective (iotaOf _ φ hφ.1) := by
      rw [injective_iff_map_eq_one]
      intro s hs
      rw [iotaOf_eq_one_iff _ hZ, hker] at hs
      exact Subgroup.mem_bot.mp hs
    have := card_le_two_of_le_range_sl2 (two_ne_zero_of_card hp' (by omega) hcF) hιinj hTe hTr
    omega
  · exact excMinus_U4_short hp3 hp1 hK hZ hDi hTi hDe hTe hT4 hTD hA3 hQ hα3 hα1 hD hfD hfT hu
      hu1 hq

end Item211Res4Proof

open Item211Res4Proof

theorem ks211ExcMinusU4_holds : KS211ExcMinusU4 := by
  intro p _ hp3 hp1
  have hK : Nat.card (GaloisField p (2 * 1)) = (p ^ 1) ^ 2 := by
    rw [GaloisField.card p (2 * 1) (by norm_num)]
    ring
  have hproj : projSU 4 p 1 =
      projImage (SUid (unitaryInvolution (GaloisField p (2 * 1)) p 1) 4) := by
    rw [SUid_eq_statedSU hK 4, CFSG.RankThree.PartTwo.Census.projImage_statedSU]
  refine Item211Lie2Proof.excMinusFor_of_mulEquiv (MulEquiv.subgroupCongr hproj) ?_
  exact excMinusFor_U4 hp3 hp1 hK center_projImage_SUid_eq_bot

end CFSG.RankThree.PartTwo.Sec21
