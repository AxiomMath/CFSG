module

import CFSG.LieType.Chevalley.E6ToralGraphInvolution
import CFSG.LieType.Chevalley.OddRootPairSL2
public import CFSG.RankThree.PartOne.SRC.CentralizerKer
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Prime

public section

namespace CFSG.RankThree.PartOne.SLBG2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartTwo.Census.Carrier TauCeti
  CFSG.RankThree.PartOne.SRC
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)


theorem exists_two_SL2_G2 {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) :
    ∃ (t : adjointGroup Tag.G2 K) (ι₁ ι₂ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup Tag.G2 K),
      (t : ModGL Tag.G2 K) = rootDiagUnit .G2 (signA K) ∧ orderOf t = 2 ∧
      Function.Injective ι₁ ∧ Function.Injective ι₂ ∧ (∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a) ∧
      (∀ a, ι₁ a * t = t * ι₁ a) ∧ (∀ b, ι₂ b * t = t * ι₂ b) := by
  obtain ⟨B, hB, -⟩ :=
    (CFSG.LieType.Chevalley.G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).1
  obtain ⟨-, -, hdC, -⟩ :=
    (CFSG.LieType.Chevalley.G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).2 B hB
      (signA K)
  have hneg : (-1 : Kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK2 (congrArg Units.val h)
  have hd1 : rootDiagUnit .G2 (signA K) ≠ 1 := by
    intro h
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_one] at h
    have h0 := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) ⟨0, by decide⟩
    exact hneg h0
  have hd2 : rootDiagUnit .G2 (signA K) * rootDiagUnit .G2 (signA K) = 1 := by
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_one]
    congr 1
    funext i
    fin_cases i
    · change (-1 : Kˣ) * (-1) = 1
      rw [neg_mul_neg, one_mul]
    · change (1 : Kˣ) * 1 = 1
      rw [one_mul]
  have hα : IsRoot Tag.G2 rootA := CFSG.Quasithin.G2U.isRoot_iff_mem_rootList.mpr (by decide)
  have hβ : IsRoot Tag.G2 rootB := CFSG.Quasithin.G2U.isRoot_iff_mem_rootList.mpr (by decide)
  obtain ⟨hQleα, ⟨eα⟩, -⟩ :=
    CFSG.LieType.Chevalley.odd_arbitrary_root_pair_SL2_p_components .G2 K hK2 hα
  obtain ⟨hQleβ, ⟨eβ⟩, -⟩ :=
    CFSG.LieType.Chevalley.odd_arbitrary_root_pair_SL2_p_components .G2 K hK2 hβ
  let t : adjointGroup Tag.G2 K := ⟨rootDiagUnit .G2 (signA K), hdC⟩
  let ι₁ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup Tag.G2 K :=
    (Subgroup.inclusion hQleα).comp eα.toMonoidHom
  let ι₂ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup Tag.G2 K :=
    (Subgroup.inclusion hQleβ).comp eβ.toMonoidHom
  have hι₁ : Function.Injective ι₁ :=
    (Subgroup.inclusion_injective hQleα).comp eα.injective
  have hι₂ : Function.Injective ι₂ :=
    (Subgroup.inclusion_injective hQleβ).comp eβ.injective
  have ht : orderOf t = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [pow_two] using hd2)
    · intro h
      exact hd1 (congrArg Subtype.val h)
  have hcomm : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a := by
    intro a b
    have h1 := Subgroup.mem_centralizer_iff.mp
      (rootPair_le_centralizer (K := K) (eβ b).2) (eα a : ModGL Tag.G2 K) (eα a).2
    exact Subtype.ext h1
  have hc₁ : ∀ a, ι₁ a * t = t * ι₁ a := by
    intro a
    have hmem : (eα a : ModGL Tag.G2 K) ∈
        CFSG.LieType.Chevalley.toralCentralizer Tag.G2 K (signA K) := by
      apply rootSpan_le_toralCentralizer (signA K)
      rw [rootSpan_signA hK2]
      exact Subgroup.mem_sup_left (eα a).2
    have h1 := Subgroup.mem_centralizer_iff.mp hmem.2 (rootDiagUnit .G2 (signA K))
      (Set.mem_singleton _)
    exact Subtype.ext h1.symm
  have hc₂ : ∀ b, ι₂ b * t = t * ι₂ b := by
    intro b
    have hmem : (eβ b : ModGL Tag.G2 K) ∈
        CFSG.LieType.Chevalley.toralCentralizer Tag.G2 K (signA K) := by
      apply rootSpan_le_toralCentralizer (signA K)
      rw [rootSpan_signA hK2]
      exact Subgroup.mem_sup_right (eβ b).2
    have h1 := Subgroup.mem_centralizer_iff.mp hmem.2 (rootDiagUnit .G2 (signA K))
      (Set.mem_singleton _)
    exact Subtype.ext h1.symm
  exact ⟨t, ι₁, ι₂, rfl, ht, hι₁, hι₂, hcomm, hc₁, hc₂⟩

@[expose] def signB (K : Type) [Field K] : Fin Tag.G2.rank → Kˣ := ![-1, -1]

@[expose] def signC (K : Type) [Field K] : Fin Tag.G2.rank → Kˣ := ![1, -1]

theorem weylElt0_conj {K : Type} [Field K] :
    weylElt Tag.G2 K ⟨0, by decide⟩ 1 * rootDiagUnit .G2 (signA K) *
        (weylElt Tag.G2 K ⟨0, by decide⟩ 1)⁻¹ = rootDiagUnit .G2 (signB K) := by
  rw [CFSG.LieType.Chevalley.weylElt_conj_rootDiagUnit]
  congr 1
  funext j
  fin_cases j
  · change (-1 : Kˣ) * (-1 : Kˣ) ^ (-(2:ℤ)) = -1
    simp [zpow_neg]
  · change (1 : Kˣ) * (-1 : Kˣ) ^ (-(-1:ℤ)) = -1
    simp

theorem weylElt1_conj {K : Type} [Field K] :
    weylElt Tag.G2 K ⟨1, by decide⟩ 1 * rootDiagUnit .G2 (signB K) *
        (weylElt Tag.G2 K ⟨1, by decide⟩ 1)⁻¹ = rootDiagUnit .G2 (signC K) := by
  rw [CFSG.LieType.Chevalley.weylElt_conj_rootDiagUnit]
  congr 1
  funext j
  fin_cases j
  · change (-1 : Kˣ) * (-1 : Kˣ) ^ (-(-3:ℤ)) = 1
    have : (-1 : Kˣ) ^ (3:ℤ) = -1 := by
      rw [show (3:ℤ) = ((3:ℕ):ℤ) by norm_num, zpow_natCast]; norm_num
    simp [this]
  · change (-1 : Kˣ) * (-1 : Kˣ) ^ (-(2:ℤ)) = -1
    simp [zpow_neg]

theorem signA_mul_signB_mul_signC {K : Type} [Field K] : signA K * signB K * signC K = 1 := by
  funext j
  fin_cases j
  · change (-1 : Kˣ) * (-1) * 1 = 1
    simp
  · change (1 : Kˣ) * (-1) * (-1) = 1
    simp

theorem g2Nine_model {K : Type} [Field K] [Finite K] [CharP K 3] (_hK : Nat.card K = 9) :
    ∃ (b : Fin 3 → adjointGroup Tag.G2 K)
      (ι : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
        adjointGroup Tag.G2 K),
      (∀ i, orderOf (b i) = 2) ∧ b 0 * b 1 * b 2 = 1 ∧
      (∀ i A, ι i A = 1 → A ^ 2 = 1) ∧ (∀ i g, ι i g * b i = b i * ι i g) := by
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  obtain ⟨t, ι₁, ι₂, htv, ht, hι₁, hι₂, hcomm, hc₁, hc₂⟩ := exists_two_SL2_G2 hK2
  let ι0 : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      adjointGroup Tag.G2 K := ι₁.noncommCoprod ι₂ fun a b => hcomm a b
  have hker : ∀ A, ι0 A = 1 → A ^ 2 = 1 := by
    rintro ⟨a, b⟩ h
    have h' : ι₁ a * ι₂ b = 1 := h
    have hmul : ι₁ a = (ι₂ b)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have hmul' : ι₂ b = (ι₁ a)⁻¹ := eq_inv_of_mul_eq_one_right h'
    have ha : a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hι₁
      rw [map_mul, map_mul, hmul]
      exact ((show Commute (ι₁ g) (ι₂ b) from hcomm g b).inv_right).eq
    have hb : b ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hι₂
      rw [map_mul, map_mul, hmul']
      exact ((show Commute (ι₂ g) (ι₁ a) from (hcomm a g).symm).inv_right).eq
    exact Prod.ext (sq_eq_one_of_mem_center_SL2 ha) (sq_eq_one_of_mem_center_SL2 hb)
  have hc0 : ∀ x, ι0 x * t = t * ι0 x := by
    rintro ⟨a, b⟩
    show ι₁ a * ι₂ b * t = t * (ι₁ a * ι₂ b)
    calc ι₁ a * ι₂ b * t = ι₁ a * (ι₂ b * t) := by rw [mul_assoc]
      _ = ι₁ a * (t * ι₂ b) := by rw [hc₂]
      _ = (ι₁ a * t) * ι₂ b := by rw [mul_assoc]
      _ = (t * ι₁ a) * ι₂ b := by rw [hc₁]
      _ = t * (ι₁ a * ι₂ b) := by rw [mul_assoc]
  let n0 : adjointGroup Tag.G2 K :=
    ⟨weylElt Tag.G2 K ⟨0, by decide⟩ 1, weylElt_mem_adjointGroup _ 1⟩
  let n1 : adjointGroup Tag.G2 K :=
    ⟨weylElt Tag.G2 K ⟨1, by decide⟩ 1, weylElt_mem_adjointGroup _ 1⟩
  let g : Fin 3 → adjointGroup Tag.G2 K := ![1, n0, n1 * n0]
  have hb0 : (((g 0 * t * (g 0)⁻¹ : adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      rootDiagUnit .G2 (signA K) := by
    show ((1 * t * (1 : adjointGroup Tag.G2 K)⁻¹ : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) = _
    rw [inv_one, mul_one, one_mul]
    exact htv
  have hb1 : (((g 1 * t * (g 1)⁻¹ : adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      rootDiagUnit .G2 (signB K) := by
    show ((n0 * t * n0⁻¹ : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, htv]
    exact weylElt0_conj
  have hb2 : (((g 2 * t * (g 2)⁻¹ : adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      rootDiagUnit .G2 (signC K) := by
    have e : g 2 * t * (g 2)⁻¹ = n1 * (n0 * t * n0⁻¹) * n1⁻¹ := by
      show n1 * n0 * t * (n1 * n0)⁻¹ = n1 * (n0 * t * n0⁻¹) * n1⁻¹
      group
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, htv]
    have h1 : (n0 : ModGL Tag.G2 K) * rootDiagUnit .G2 (signA K) * (n0 : ModGL Tag.G2 K)⁻¹ =
        rootDiagUnit .G2 (signB K) := weylElt0_conj
    rw [h1]
    exact weylElt1_conj
  refine ⟨fun i => g i * t * (g i)⁻¹,
    fun i => (MulAut.conj (g i)).toMonoidHom.comp ι0, ?_, ?_, ?_, ?_⟩
  · intro i
    show orderOf ((MulAut.conj (g i)) t) = 2
    rw [MulEquiv.orderOf_eq]
    exact ht
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hb0, hb1, hb2, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
      ← CFSG.LieType.Chevalley.rootDiagUnit_mul, signA_mul_signB_mul_signC,
      CFSG.LieType.Chevalley.rootDiagUnit_one]
    rfl
  · intro i A h
    have h' : (MulAut.conj (g i)) (ι0 A) = 1 := h
    exact hker A ((map_eq_one_iff _ (MulAut.conj (g i)).injective).1 h')
  · intro i x
    show (g i * ι0 x * (g i)⁻¹) * (g i * t * (g i)⁻¹) = (g i * t * (g i)⁻¹) * (g i * ι0 x * (g i)⁻¹)
    calc (g i * ι0 x * (g i)⁻¹) * (g i * t * (g i)⁻¹) = g i * (ι0 x * t) * (g i)⁻¹ := by group
      _ = g i * (t * ι0 x) * (g i)⁻¹ := by rw [hc0 x]
      _ = (g i * t * (g i)⁻¹) * (g i * ι0 x * (g i)⁻¹) := by group

end CFSG.RankThree.PartOne.SLBG2
