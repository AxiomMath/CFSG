module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartF
public import CFSG.Quasithin.Vol2.Ch11SecDFacts6
public import CFSG.Quasithin.Vol2.Ch11SecO1A
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA SecS SecS.C11P9A
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem exists_adapted_sl3 [IsMulCommutative ↥(fsuV T I)] (hS : SecD.NatSetting11 G T L I n)
    (hk : KindSL3 L (fsuV T I) n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ (π : ↥(Assembly.LowTwoRank.StatedSL 3 K) →* ↥(autOn L (fsuV T I)))
        (f : ↥(fsuV T I) → (Fin 3 → K)),
        IsCoord (linModelNat (Assembly.LowTwoRank.StatedSL 3 K)) (autOn L (fsuV T I)) ⊥ π f ∧
        ∃ g : SpecialLinearGroup (Fin 3) K,
          (∀ v : ↥(fsuV T I), (v : G) ∈ V₁ ↔ f v ∈ gmap g (flagSpace 3 K 1)) ∧
          autOn (LOf L V₁) (fsuV T I) = (stabE0 K).map (psiW π g) := by
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, hK, π, f, -, hf⟩ := exists_coord_sl3 hS hk
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf (isSylowTwoOf_P hS)
  have hU₁ := isFlagW_of_isVi hS hV₁
  rw [← hK] at hU₁
  have hV := eq_U1_of_isFlagW (sq_eq_one hS) hf hg hU₁
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, π, f, hf, g, fun v => ?_, ?_⟩
  · rw [← Subgroup.mem_subgroupOf, hV]
    rfl
  · rw [SecS.autOn_lOf hS.le_normalizer (SecA.IsVi.le_fsuV hV₁), hV, gammaW_one_eq hSL hf g]

section Transvection

variable {K : Type} [Field K]

@[expose] def trvSL (i j : Fin 3) (hij : i ≠ j) (c : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩

theorem trvSL_mulVec (i j : Fin 3) (hij : i ≠ j) (c : K) (s : Fin 3 → K) :
    ((trvSL i j hij c : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ s =
      s + Pi.single i (c * s j) := by
  change Matrix.transvection i j c *ᵥ s = _
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

theorem transvection_mem_stabE0 (i j : Fin 3) (hij : i ≠ j) (hj : j ≠ 0) (c : K) :
    trvSL i j hij c ∈ stabE0 K := by
  rw [mem_stabE0, trvSL_mulVec]
  have h0 : (![1, 0, 0] : Fin 3 → K) j = 0 := by
    fin_cases j
    · exact absurd rfl hj
    · rfl
    · rfl
  rw [h0, mul_zero, Pi.single_zero, add_zero]

theorem exists_ne_zero_ne (i : Fin 3) : ∃ j : Fin 3, j ≠ 0 ∧ i ≠ j := by
  fin_cases i
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩

end Transvection

theorem _root_.CFSG.Quasithin.Vol2.Ch11.SecD.commLOneSL3Fact_holds : SecD.CommLOneSL3Fact := by
  intro G _ _ T L I n V₁ hS hk hV₁
  have := isMulCommutative hS
  obtain ⟨K, _, _, _, hK, π, f, hf, g, -, hL₁⟩ := exists_adapted_sl3 hS hk hV₁
  have hLV : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    ((perfectCore_le _).trans inf_le_left).trans hS.le_normalizer
  set C := ⁅fsuV T I, LOf L V₁⁆ with hCdef
  have hCV : C ≤ fsuV T I := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def, show v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) by group]
    exact (fsuV T I).mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp
      ((fsuV T I).inv_mem hv))
  refine le_antisymm hCV fun v₀ hv₀ => ?_
  have hkey : ∀ (i : Fin 3) (c : K), ∃ w : ↥(fsuV T I), (w : G) ∈ C ∧
      f w = ((g : Matrix (Fin 3) (Fin 3) K)) *ᵥ Pi.single i c := by
    intro i c
    obtain ⟨j, hj0, hij⟩ := exists_ne_zero_ne i
    have hB := transvection_mem_stabE0 (K := K) i j hij hj0 1
    have hmem : psiW π g (trvSL i j hij 1) ∈ autOn (LOf L V₁) (fsuV T I) := by
      rw [hL₁]
      exact ⟨_, hB, rfl⟩
    obtain ⟨l, hl, hlV, hle⟩ := SecA.mem_autOn_iff.mp hmem
    obtain ⟨v, hv⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single j (-c))
    have hw : ⁅(v : G), l⁆ ∈ fsuV T I := hCV (Subgroup.commutator_mem_commutator v.2 hl)
    refine ⟨⟨_, hw⟩, Subgroup.commutator_mem_commutator v.2 hl, ?_⟩
    have he : (⟨⁅(v : G), l⁆, hw⟩ : ↥(fsuV T I)) = v * (conjV (fsuV T I) l hlV v)⁻¹ := by
      apply Subtype.ext
      change ⁅(v : G), l⁆ = _
      rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, conjV_apply_coe]
      group
    rw [he, hf.map_mul_inv, ← hle, psiW_apply, hf.act3, hv, Matrix.mulVec_mulVec,
      ← Matrix.SpecialLinearGroup.coe_mul, show g * trvSL i j hij 1 * g⁻¹ * g = g * trvSL i j hij 1
        by group, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, trvSL_mulVec,
      ← Matrix.mulVec_sub, Pi.single_eq_same, one_mul, sub_add_cancel_left, ← Pi.single_neg,
      neg_neg]
  have hsum : ∀ y : Fin 3 → K, ∃ w : ↥(fsuV T I), (w : G) ∈ C ∧
      f w = ((g : Matrix (Fin 3) (Fin 3) K)) *ᵥ y := by
    intro y
    obtain ⟨w₀, h₀, e₀⟩ := hkey 0 (y 0)
    obtain ⟨w₁, h₁, e₁⟩ := hkey 1 (y 1)
    obtain ⟨w₂, h₂, e₂⟩ := hkey 2 (y 2)
    refine ⟨w₀ * w₁ * w₂, C.mul_mem (C.mul_mem h₀ h₁) h₂, ?_⟩
    rw [hf.map_mul, hf.map_mul, e₀, e₁, e₂, ← Matrix.mulVec_add, ← Matrix.mulVec_add]
    congr 1
    funext k
    fin_cases k <;> simp
  obtain ⟨w, hwC, hwf⟩ := hsum (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
    f ⟨v₀, hv₀⟩)
  rw [g_ginv_mulVec] at hwf
  rw [← show (w : G) = v₀ from congrArg Subtype.val (IsCoord.injective_of_bot hf hwf)]
  exact hwC

end CFSG.Quasithin.Vol2.Ch11.SecO1
