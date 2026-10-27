module

public import CFSG.RankThree.PartOne.LSTD.Tri
public import CFSG.RankThree.PartOne.LSTD.Hyper
public import CFSG.RankThree.PartOne.LSTD.TorusFacts

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP

variable {f : ℕ} {K : Type} [Field K]

theorem mul_mul_inv_cancel_left' {G : Type*} [CommGroup G] (a b : G) : a * (b * a⁻¹) = b := by
  rw [mul_left_comm, mul_inv_cancel, mul_one]

theorem decomp_torus (v : Fin 5 → Kˣ) (hv : v ∈ torusVec 5 5 K) :
    ∃ (z : Kˣ) (d : Fin 3 → Kˣ) (w : Kˣ), z ^ 5 = 1 ∧ d ∈ torusVec 5 3 K ∧ w ^ 5 = 1 ∧
      (∀ a : Fin 3, d a = v (e3 a) * z⁻¹) ∧
      v = (fun _ => z) * extU d * torusElt 3 4 w := by
  have hv5 : ∀ i, v i ^ 5 = 1 := hv.1
  have hprod : v 0 * v 1 * v 2 * (v 3 * v 4) = 1 := by
    have := hv.2
    rw [Fin.prod_univ_five] at this
    rw [← this]
    simp only [mul_assoc]
  set s : Kˣ := v 3 * v 4 with hs
  have hs5 : s ^ 5 = 1 := by rw [hs, mul_pow, hv5, hv5, one_mul]
  set z : Kˣ := s ^ 3 with hz
  have hz5 : z ^ 5 = 1 := by rw [hz, ← pow_mul, mul_comm, pow_mul, hs5, one_pow]
  have hz2 : z ^ 2 = s := by
    rw [hz, ← pow_mul, show 3 * 2 = 5 + 1 from rfl, pow_succ, hs5, one_mul]
  have hv012 : v 0 * v 1 * v 2 = (z ^ 2)⁻¹ := by
    rw [hz2]
    exact eq_inv_of_mul_eq_one_left hprod
  have e0 : (e3 0 : Fin 5) = 0 := rfl
  have e1 : (e3 1 : Fin 5) = 1 := rfl
  have e2 : (e3 2 : Fin 5) = 2 := rfl
  refine ⟨z, fun a => v (e3 a) * z⁻¹, v 3 * z⁻¹, hz5, ⟨fun a => ?_, ?_⟩, ?_, fun a => rfl, ?_⟩
  · rw [mul_pow, inv_pow, hv5, hz5, inv_one, one_mul]
  · rw [Fin.prod_univ_three, e0, e1, e2]
    have : v 0 * z⁻¹ * (v 1 * z⁻¹) * (v 2 * z⁻¹) = (v 0 * v 1 * v 2) * (z⁻¹ * z⁻¹ * z⁻¹) := by
      ac_rfl
    rw [this, hv012]
    have h5' : (z ^ 2)⁻¹ * (z⁻¹ * z⁻¹ * z⁻¹) = (z ^ 5)⁻¹ := by group
    rw [h5', hz5, inv_one]
  · rw [mul_pow, inv_pow, hv5, hz5, inv_one, one_mul]
  · funext i
    fin_cases i
    · have h1 : extU (fun a => v (e3 a) * z⁻¹) 0 = v 0 * z⁻¹ := by simp [extU, e3, Fin.castLE]
      show v 0 = z * extU (fun a => v (e3 a) * z⁻¹) 0 * torusElt 3 4 (v 3 * z⁻¹) 0
      rw [h1, torusElt_apply_other (by decide) (by decide), mul_one, mul_mul_inv_cancel_left']
    · have h1 : extU (fun a => v (e3 a) * z⁻¹) 1 = v 1 * z⁻¹ := by simp [extU, e3, Fin.castLE]
      show v 1 = z * extU (fun a => v (e3 a) * z⁻¹) 1 * torusElt 3 4 (v 3 * z⁻¹) 1
      rw [h1, torusElt_apply_other (by decide) (by decide), mul_one, mul_mul_inv_cancel_left']
    · have h1 : extU (fun a => v (e3 a) * z⁻¹) 2 = v 2 * z⁻¹ := by simp [extU, e3, Fin.castLE]
      show v 2 = z * extU (fun a => v (e3 a) * z⁻¹) 2 * torusElt 3 4 (v 3 * z⁻¹) 2
      rw [h1, torusElt_apply_other (by decide) (by decide), mul_one, mul_mul_inv_cancel_left']
    · show v 3 = z * extU (fun a => v (e3 a) * z⁻¹) 3 * torusElt 3 4 (v 3 * z⁻¹) 3
      rw [extU_three, torusElt_apply_left (by decide), mul_one, mul_mul_inv_cancel_left']
    · show v 4 = z * extU (fun a => v (e3 a) * z⁻¹) 4 * torusElt 3 4 (v 3 * z⁻¹) 4
      rw [extU_four, torusElt_apply_right (by decide), mul_one]
      have h2 : z * (v 3 * z⁻¹)⁻¹ = z ^ 2 * (v 3)⁻¹ := by
        rw [_root_.mul_inv_rev, inv_inv, ← mul_assoc, ← pow_two]
      rw [h2, hz2, hs, mul_inv_cancel_comm]

theorem three_ne_e3 : ∀ x : Fin 3, (3 : Fin 5) ≠ e3 x := by decide

theorem four_ne_e3 : ∀ x : Fin 3, (4 : Fin 5) ≠ e3 x := by decide

section Hyper

variable (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)

theorem const_mem_scalarsU {z : Kˣ} (hv : (fun _ : Fin 5 => z) ∈ torusVec 5 5 K) :
    tSU hU h5 (fun _ => z) hv ∈ scalarsU K f := by
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 5) z = diagU (fun _ : Fin 5 => z) := by
    apply Units.ext
    rw [diagU_val]
    simp [Matrix.GeneralLinearGroup.scalar]
  exact Subgroup.mem_subgroupOf.mpr ⟨z, h1⟩

include h5 in
theorem hyper_eq_model [Finite K] (hf2 : 2 ≤ f) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5)
    {b : StatedProj (unitarySU 2 f K 5)} (hb : b ∈ torusBar K f ⊓ Jfun hU 3 4) (hb1 : b ≠ 1)
    {x y : Fin 3} (hxy : x ≠ y) :
    torusBar K f ⊓ Subgroup.centralizer (Jfun hU (e3 x) (e3 y) : Set _) =
      (torusBar K f ⊓ (Jfun hU 0 1 ⊔ Jfun hU 1 2) ⊓
        Subgroup.centralizer (Jfun hU (e3 x) (e3 y) : Set _)) ⊔ Subgroup.zpowers b := by
  obtain ⟨ζ, hζ'⟩ := hζ
  have hzp : Subgroup.zpowers b = torusBar K f ⊓ Jfun hU 3 4 := by
    have hb5 : b ^ 5 = 1 := torusBar_pow_five hU h5 hb.1
    have hord : orderOf b = 5 := by
      have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      exact orderOf_eq_prime hb5 hb1
    have hcard : Nat.card ↥(torusBar K f ⊓ Jfun hU 3 4) = 5 :=
      card_torusBar_inf_Jfun hU h5 hζ' (by decide : (3 : Fin 5) ≠ 4)
    have : Finite ↥(torusBar K f ⊓ Jfun hU 3 4) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb)
      (by rw [hcard, Nat.card_zpowers, hord])
  apply le_antisymm
  · intro t ht
    obtain ⟨hT, hC⟩ := ht
    obtain ⟨v, hv, rfl⟩ := (mem_torusBar_iff hU h5).mp hT
    have hvxy : v (e3 x) = v (e3 y) := (mem_centralizer_Jfun_iff hU h5 (e3_ne hxy) hv).mp hC
    obtain ⟨z, d, w, hz5, hd, hw5, hdv, hveq⟩ := decomp_torus v hv
    have hdm : extU d ∈ torusVec 5 5 K := extU_mem hd
    have hwm : torusElt 3 4 w ∈ torusVec 5 5 K := torusElt_mem (by decide) hw5
    have hzm : (fun _ : Fin 5 => z) ∈ torusVec 5 5 K :=
      ⟨fun _ => hz5, by simp [Finset.prod_const, hz5]⟩
    have hsplit : projU K f (tSU hU h5 v hv) =
        projU K f (tSU hU h5 (extU d) hdm) *
          projU K f (tSU hU h5 (torusElt 3 4 w) hwm) := by
      rw [← map_mul]
      apply projU_eq_iff.mpr
      refine ⟨tSU hU h5 (fun _ => z) hzm, const_mem_scalarsU hU h5 hzm, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tSU, coe_tSU, coe_tSU, coe_tSU, diagU_mul,
        diagU_mul]
      congr 1
      rw [hveq, mul_assoc, mul_comm]
    have hfirst : projU K f (tSU hU h5 (extU d) hdm) ∈
        torusBar K f ⊓ (Jfun hU 0 1 ⊔ Jfun hU 1 2) ⊓
          Subgroup.centralizer (Jfun hU (e3 x) (e3 y) : Set _) := by
      refine ⟨⟨(mem_torusBar_iff hU h5).mpr ⟨_, hdm, rfl⟩, ?_⟩, ?_⟩
      · rw [Kbar_eq_range hU hf2]
        refine ⟨⟨diagU d, torusSU_le_unitarySU hU h5
          (mem_torusSU_iff.mpr ⟨d, hd.1, hd.2, rfl⟩)⟩, ?_⟩
        rw [theta3_apply]
        congr 1
        apply Subtype.ext
        rw [coe_emb3, coe_tSU]
        exact blockGL_diagU d
      · exact (mem_centralizer_Jfun_iff hU h5 (e3_ne hxy) hdm).mpr
          (by rw [extU_e3, extU_e3, hdv x, hdv y, hvxy])
    have hsecond : projU K f (tSU hU h5 (torusElt 3 4 w) hwm) ∈ Subgroup.zpowers b := by
      rw [hzp]
      refine ⟨(mem_torusBar_iff hU h5).mpr ⟨_, hwm, rfl⟩, ?_⟩
      rw [Jfun_of_ne hU (by decide : (3 : Fin 5) ≠ 4)]
      exact ⟨_, lineElt_mem_Bk hU h5 (by decide) hw5, rfl⟩
    rw [hsplit]
    exact Subgroup.mul_mem_sup hfirst hsecond
  · refine sup_le (inf_le_inf_right _ inf_le_left) (Subgroup.zpowers_le.mpr ⟨hb.1, ?_⟩)
    exact Jfun_le_centralizer_of_disjoint hU (by decide : (3 : Fin 5) ≠ 4) (e3_ne hxy)
      (three_ne_e3 x) (three_ne_e3 y) (four_ne_e3 x) (four_ne_e3 y) hb.2

end Hyper

end CFSG.RankThree.PartOne.LSTD
