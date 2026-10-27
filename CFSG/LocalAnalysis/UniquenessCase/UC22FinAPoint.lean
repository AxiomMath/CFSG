module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab
import CFSG.RankThree.GF2n.Smith81.TiD2Alg
public import Mathlib.Data.Fin.Tuple.Sort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.AGLEmbedding.LinearThreeKit CFSG.RankThree.GF2n.Smith81.D2 Matrix Subgroup
open scoped commutatorElement MatrixGroups

section

variable {K : Type} [Field K]

local notation "M₃" => Matrix (Fin 3) (Fin 3) K

local notation "PS" => stabilizer (flagSpace 3 K 1)

variable (K) in
private def fixW : Subgroup SL(3, K) where
  carrier := {g | (g : M₃) *ᵥ Pi.single 0 1 = Pi.single 0 1}
  one_mem' := one_mulVec _
  mul_mem' {a b} ha hb := by
    change (a : M₃) *ᵥ Pi.single 0 1 = Pi.single 0 1 at ha
    change (b : M₃) *ᵥ Pi.single 0 1 = Pi.single 0 1 at hb
    change ((a * b : SL(3, K)) : M₃) *ᵥ Pi.single 0 1 = Pi.single 0 1
    rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hb, ha]
  inv_mem' {a} ha := by
    change (a : M₃) *ᵥ Pi.single 0 1 = Pi.single 0 1 at ha
    change ((a⁻¹ : SL(3, K)) : M₃) *ᵥ Pi.single 0 1 = Pi.single 0 1
    conv_lhs => rw [← ha]
    rw [mulVec_mulVec, coe_inv_mul_coe, one_mulVec]

private theorem mem_fixW {g : SL(3, K)} :
    g ∈ fixW K ↔ (g : M₃) *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
  Iff.rfl

private theorem fixW_entries {g : SL(3, K)} (hg : g ∈ fixW K) :
    (g : M₃) 0 0 = 1 ∧ (g : M₃) 1 0 = 0 ∧ (g : M₃) 2 0 = 0 := by
  have h := fun i => congrFun (mem_fixW.mp hg) i
  exact ⟨by simpa [mulVec_single_one] using h 0, by simpa [mulVec_single_one] using h 1,
    by simpa [mulVec_single_one] using h 2⟩

private theorem fixW_le : fixW K ≤ PS := fun g hg => by
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, flagSpace_one_eq_span] at hv
  rw [flagSpace_one_eq_span]
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
  rw [mulVecLin_apply, mulVec_smul, mem_fixW.mp hg]

private def leviFun (g : fixW K) : SL(2, K) :=
  ⟨!![((g : SL(3, K)) : M₃) 1 1, ((g : SL(3, K)) : M₃) 1 2;
      ((g : SL(3, K)) : M₃) 2 1, ((g : SL(3, K)) : M₃) 2 2], by
    obtain ⟨h0, h1, h2⟩ := fixW_entries g.2
    have h : ((g : SL(3, K)) : M₃).det = 1 := (g : SL(3, K)).2
    rw [det_fin_three, h0, h1, h2] at h
    rw [det_fin_two_of]
    linear_combination h⟩

private theorem leviFun_apply (g : fixW K) (i j : Fin 2) :
    ((leviFun g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) i j =
      ((g : SL(3, K)) : M₃) i.succ j.succ := by
  fin_cases i <;> fin_cases j <;> rfl

private def levi : fixW K →* SL(2, K) where
  toFun := leviFun
  map_one' := by
    ext i j
    rw [leviFun_apply]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    obtain ⟨-, g1, g2⟩ := fixW_entries g.2
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two, leviFun_apply,
      leviFun_apply, leviFun_apply, leviFun_apply, leviFun_apply, Subgroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_three]
    fin_cases i <;> simp [g1, g2]

private theorem levi_apply (g : fixW K) (i j : Fin 2) :
    ((levi g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) i j =
      ((g : SL(3, K)) : M₃) i.succ j.succ :=
  leviFun_apply g i j

private def blk (B : SL(2, K)) : SL(3, K) :=
  ⟨!![1, 0, 0; 0, (B : Matrix (Fin 2) (Fin 2) K) 0 0, (B : Matrix (Fin 2) (Fin 2) K) 0 1;
      0, (B : Matrix (Fin 2) (Fin 2) K) 1 0, (B : Matrix (Fin 2) (Fin 2) K) 1 1], by
    have h : (B : Matrix (Fin 2) (Fin 2) K).det = 1 := B.2
    rw [det_fin_two] at h
    rw [det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    linear_combination h⟩

private theorem blk_mem (B : SL(2, K)) : blk B ∈ fixW K := by
  rw [mem_fixW]
  ext i
  fin_cases i <;> simp [blk]

private theorem levi_surjective : Function.Surjective (levi (K := K)) := fun B => by
  refine ⟨⟨blk B, blk_mem B⟩, ?_⟩
  ext i j
  rw [levi_apply]
  fin_cases i <;> fin_cases j <;> rfl

private def unip (a b : K) : SL(3, K) :=
  ⟨!![1, a, b; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

private theorem coe_unip (a b : K) : (unip a b : M₃) = !![1, a, b; 0, 1, 0; 0, 0, 1] :=
  rfl

private theorem unip_mem (a b : K) : unip a b ∈ fixW K := by
  rw [mem_fixW, coe_unip]
  ext i
  fin_cases i <;> simp

private theorem eq_unip {g : fixW K} (h : levi g = 1) :
    (g : SL(3, K)) = unip (((g : SL(3, K)) : M₃) 0 1) (((g : SL(3, K)) : M₃) 0 2) := by
  obtain ⟨h0, h1, h2⟩ := fixW_entries g.2
  have e : ∀ i j : Fin 2,
      ((g : SL(3, K)) : M₃) i.succ j.succ = (1 : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => by rw [← levi_apply, h, Matrix.SpecialLinearGroup.coe_one]
  have e00 : ((g : SL(3, K)) : M₃) 1 1 = 1 := by simpa using e 0 0
  have e01 : ((g : SL(3, K)) : M₃) 1 2 = 0 := by simpa using e 0 1
  have e10 : ((g : SL(3, K)) : M₃) 2 1 = 0 := by simpa using e 1 0
  have e11 : ((g : SL(3, K)) : M₃) 2 2 = 1 := by simpa using e 1 1
  refine Subtype.ext ?_
  rw [coe_unip]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, e00, e01, e10, e11]

variable [CharP K 2]

private theorem unip_mul_self (a b : K) : unip a b * unip a b = 1 := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_unip, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

private theorem unip_inv (a b : K) : (unip a b)⁻¹ = unip a b :=
  inv_eq_of_mul_eq_one_right (unip_mul_self a b)

private theorem unip_conj {y : SL(3, K)} {a b d : K} (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hy : (y : M₃) = !![1, a, b; 0, d, 0; 0, 0, d⁻¹]) (c₁ c₂ : K) :
    unip (c₁ * d / (1 + d)) (c₂ / (1 + d)) * y * unip (c₁ * d / (1 + d)) (c₂ / (1 + d)) =
      unip c₁ c₂ * y := by
  have h1d : 1 + d ≠ 0 := fun h =>
    hd1 ((add_eq_zero_iff_eq_neg.mp h).trans (CharTwo.neg_eq d)).symm
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, hy, coe_unip, coe_unip]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

end

theorem eq_commutator_of_normal_perfect {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 8 ≤ Nat.card K) (Y : Subgroup (projectiveSL 3 K))
    (hYP : Y ≤ projStabilizer (flagSpace 3 K 1)) (hperf : ⁅Y, Y⁆ = Y)
    (hnorm : projStabilizer (flagSpace 3 K 1) ≤
      Subgroup.normalizer (Y : Set (projectiveSL 3 K)))
    (h2 : ¬ IsPGroup 2 Y) :
    Y = ⁅projStabilizer (flagSpace 3 K 1), projStabilizer (flagSpace 3 K 1)⁆ := by
  have hP : ⁅projStabilizer (flagSpace 3 K 1), projStabilizer (flagSpace 3 K 1)⁆ =
      ⁅stabilizer (flagSpace 3 K 1), stabilizer (flagSpace 3 K 1)⁆.map (proj 3 K) := by
    rw [projStabilizer, map_commutator]
  have hYc : Y ≤ ⁅projStabilizer (flagSpace 3 K 1), projStabilizer (flagSpace 3 K 1)⁆ :=
    hperf.symm.le.trans (commutator_mono hYP hYP)
  refine le_antisymm hYc ?_
  have hconj : ∀ g ∈ stabilizer (flagSpace 3 K 1), ∀ y ∈ Y.comap (proj 3 K),
      g * y * g⁻¹ ∈ Y.comap (proj 3 K) := by
    intro g hg y hy
    have h := (mem_normalizer_iff.mp (hnorm (mem_map_of_mem _ hg)) (proj 3 K y)).mp hy
    rwa [mem_comap, map_mul, map_mul, map_inv]
  have hlift : ∀ b ∈ Y, ∃ w : fixW K, (w : SL(3, K)) ∈ Y.comap (proj 3 K) ∧
      proj 3 K w = b := by
    intro b hb
    have hb' := hYc hb
    rw [hP] at hb'
    obtain ⟨w, hw, hwb⟩ := mem_map.mp hb'
    refine ⟨⟨w, mem_fixW.mpr (mulVec_single_zero_of_mem_commutator hw)⟩, ?_, hwb⟩
    rw [mem_comap, hwb]
    exact hb
  set N := ((Y.comap (proj 3 K)).subgroupOf (fixW K)).map levi
  have hNn : N.Normal := by
    refine Subgroup.Normal.map ⟨fun n hn g => ?_⟩ levi levi_surjective
    rw [mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hconj _ (fixW_le g.2) _ hn
  rcases sl2_normal_eq_bot_or_top (by omega) N with hN | hN
  · refine absurd (fun g => ?_) h2
    obtain ⟨b, hb⟩ := g
    obtain ⟨w, hwY, rfl⟩ := hlift b hb
    have hw1 : levi w = 1 := by
      have h : levi w ∈ N := mem_map_of_mem _ hwY
      rwa [hN, mem_bot] at h
    have hww : (w : SL(3, K)) * w = 1 := by rw [eq_unip hw1, unip_mul_self]
    refine ⟨1, Subtype.ext ?_⟩
    change proj 3 K w ^ 2 ^ 1 = 1
    rw [pow_one, sq, ← map_mul, hww, map_one]
  · obtain ⟨d, hd⟩ : ∃ d : Kˣ, d ≠ 1 := by
      have : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
      have := Finite.one_lt_card_iff_nontrivial.mp this
      exact exists_ne 1
    have hd0 : (d : K) ≠ 0 := d.ne_zero
    have hd1 : (d : K) ≠ 1 := fun h => hd (Units.val_eq_one.mp h)
    let D : SL(2, K) := ⟨!![(d : K), 0; 0, (d : K)⁻¹], by simp [det_fin_two_of, hd0]⟩
    have hDN : D ∈ N := hN ▸ mem_top D
    obtain ⟨y, hyY, hyD⟩ := mem_map.mp hDN
    have e : ∀ i j : Fin 2, ((y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) i.succ j.succ =
        (D : Matrix (Fin 2) (Fin 2) K) i j := fun i j => by rw [← levi_apply, hyD]
    obtain ⟨h0, h1, h2⟩ := fixW_entries y.2
    have hyY' : (y : SL(3, K)) ∈ Y.comap (proj 3 K) := hyY
    have e00 : ((y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 1 = d := by simpa [D] using e 0 0
    have e01 : ((y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by simpa [D] using e 0 1
    have e10 : ((y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by simpa [D] using e 1 0
    have e11 : ((y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 = (d : K)⁻¹ := by
      simpa [D] using e 1 1
    have hymat : ((y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
        !![1, ((y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1,
          ((y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2; 0, (d : K), 0; 0, 0, (d : K)⁻¹] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, e00, e01, e10, e11]
    have hu : ∀ c₁ c₂ : K, unip c₁ c₂ ∈ Y.comap (proj 3 K) := by
      intro c₁ c₂
      have h := hconj _ (fixW_le (unip_mem (c₁ * d / (1 + d)) (c₂ / (1 + d)))) _ hyY'
      rw [unip_inv, unip_conj hd0 hd1 hymat c₁ c₂] at h
      simpa using mul_mem h (inv_mem hyY')
    have hfix : fixW K ≤ Y.comap (proj 3 K) := by
      intro g hg
      obtain ⟨y', hy', hy'g⟩ := mem_map.mp (hN ▸ mem_top (levi ⟨g, hg⟩) : levi ⟨g, hg⟩ ∈ N)
      have h1 : levi (y'⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hy'g, inv_mul_cancel]
      have hz : ((y'⁻¹ * ⟨g, hg⟩ : fixW K) : SL(3, K)) ∈ Y.comap (proj 3 K) := by
        rw [eq_unip h1]
        exact hu _ _
      simpa using mul_mem (show (y' : SL(3, K)) ∈ Y.comap (proj 3 K) from hy') hz
    rw [hP, map_le_iff_le_comap]
    exact fun w hw => hfix (mem_fixW.mpr (mulVec_single_zero_of_mem_commutator hw))

end CFSG.LocalAnalysis.UniquenessCase.UC22.FinA
