module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S4V0
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3J3
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

open Subgroup CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.RankThree.PartTwo.KFacts.K426
open scoped commutatorElement

variable {Rg : ℕ → Gp}

@[expose] def VJ (Rg : ℕ → Gp) (g : Gp) : Subgroup ↥j3P := (cj g (V0 Rg)).subgroupOf j3P

theorem cjV0_le (hR : Reg Rg) {g : Gp} (hg : g ∈ j3P) : cj g (V0 Rg) ≤ j3P :=
  cj_le_of_mem hg (V0_le hR)

theorem cjM0_le (hR : Reg Rg) {g : Gp} (hg : g ∈ j3P) : cj g (M0 Rg) ≤ j3P :=
  cj_le_of_mem hg (M0_le_P hR)

theorem cjH0_le_cjM0 (hR : Reg Rg) (g : Gp) : cj g (H0 Rg) ≤ cj g (M0 Rg) :=
  cj_mono g (H0_le_M0 hR)

theorem cjH0_le (hR : Reg Rg) {g : Gp} (hg : g ∈ j3P) : cj g (H0 Rg) ≤ j3P :=
  (cjH0_le_cjM0 hR g).trans (cjM0_le hR hg)

theorem VJ_elem (hR : Reg Rg) {g : Gp} (hg : g ∈ j3P) :
    CFSG.Open.IsElemAbelian 2 (VJ Rg g) ∧ Nat.card (VJ Rg g) = 16 :=
  ⟨isElemAbelian_subgroupOf (cjV0_le hR hg) (isElemAbelian_cj (V0_elem hR) g),
    by rw [VJ, card_subgroupOf_of_le (cjV0_le hR hg), card_cj, hR.card_V]⟩

theorem VJ_normalizer
    (hR : Reg Rg) {g : Gp} (hg : g ∈ j3P) :
    normalizer (VJ Rg g : Set ↥j3P) = (cj g (M0 Rg)).subgroupOf j3P := by
  rw [VJ, normalizer_subgroupOf (cjV0_le hR hg), ← inf_subgroupOf_right,
    normalizer_cj_inf hg (normalizer_V0 hR)]

theorem VJ_residual
    (hR : Reg Rg) {g : Gp} (hg : g ∈ j3P) :
    inSubgroup perfectResidual (normalizer (VJ Rg g : Set ↥j3P)) =
      (cj g (H0 Rg)).subgroupOf j3P := by
  rw [VJ_normalizer hR hg]
  exact inSubgroup_perfectResidual_subgroupOf (cjM0_le hR hg)
    (inSubgroup_perfectResidual_cj g (M0_residual hR))

theorem x0_eq (hR : Reg Rg) : Rg r_x0 = j3Gen 1 := by
  have := hR.x0_a1
  simp only [prodG_cons, prodG_nil, mul_one] at this
  rw [this, hR.init_a1]

theorem x0_mem (hR : Reg Rg) : Rg r_x0 ∈ j3P := by
  rw [x0_eq hR]
  exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem uu_mem (hR : Reg Rg) : Rg r_uu ∈ j3P := by simpa using hR.uu_P

theorem vv_mem (hR : Reg Rg) : Rg r_vv ∈ j3P := by simpa using hR.vv_P

abbrev B0 (Rg : ℕ → Gp) : Subgroup Gp := Ksub Rg gens_B0

theorem B0_le (hR : Reg Rg) : B0 Rg ≤ j3P := by
  refine Ksub_le fun r hr => ?_
  simp only [gens_B0, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [x0_mem hR, uu_mem hR, vv_mem hR]

theorem B0_elem (hR : Reg Rg) : CFSG.Open.IsElemAbelian 3 (B0 Rg) := by
  have hcomm : ∀ i ∈ gens_B0, ∀ j ∈ gens_B0, Commute (Rg i) (Rg j) := by
    intro i hi j hj
    simp only [gens_B0, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      first
      | exact Commute.refl _
      | exact commute_of_prod hR.comm_x0_uu
      | exact (commute_of_prod hR.comm_x0_uu).symm
      | exact commute_of_prod hR.comm_x0_vv
      | exact (commute_of_prod hR.comm_x0_vv).symm
      | exact commute_of_prod hR.comm_uu_vv
      | exact (commute_of_prod hR.comm_uu_vv).symm
  refine isElemAbelian_closure (S := Rg '' {r | r ∈ gens_B0}) ?_ ?_
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ _
    exact hcomm i hi j hj
  · rintro _ ⟨i, hi, rfl⟩
    simp only [gens_B0, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    exacts [pow_of_ord hR.ord_x0, pow_of_ord hR.ord_uu, pow_of_ord hR.ord_vv]

theorem B0_comm (hR : Reg Rg) {a b : Gp} (ha : a ∈ B0 Rg) (hb : b ∈ B0 Rg) : a * b = b * a := by
  haveI := (B0_elem hR).1
  exact Subtype.ext_iff.1 (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : B0 Rg) ⟨b, hb⟩)

theorem x0_B0 : Rg r_x0 ∈ B0 Rg := Ksub_mem (by simp [gens_B0])

theorem uu_B0 : Rg r_uu ∈ B0 Rg := Ksub_mem (by simp [gens_B0])

theorem CA_eq
    (hR : Reg Rg) :
    Ksub Rg gens_CA = j3P ⊓ centralizer {Rg r_x0} := by
  have h := j3t_caseA.1
  have hsz : j3tCAGens.size = 4 := by simp [j3tCAGens]
  have hset : Rg '' {r | r ∈ gens_CA} = CFSG.RankThree.Native.permsA 6156 j3tCAGens := by
    ext z
    simp only [CFSG.RankThree.Native.permsA, Set.mem_image, Set.mem_setOf_eq, hsz, gens_CA,
      List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨r, hr, rfl⟩
      rcases hr with rfl | rfl | rfl | rfl
      exacts [⟨0, by norm_num, hR.init_ca0.symm⟩, ⟨1, by norm_num, hR.init_ca1.symm⟩,
        ⟨2, by norm_num, hR.init_ca2.symm⟩, ⟨3, by norm_num, hR.init_ca3.symm⟩]
    · rintro ⟨k, hk, rfl⟩
      interval_cases k
      exacts [⟨r_ca0, Or.inl rfl, hR.init_ca0⟩, ⟨r_ca1, Or.inr (Or.inl rfl), hR.init_ca1⟩,
        ⟨r_ca2, Or.inr (Or.inr (Or.inl rfl)), hR.init_ca2⟩,
        ⟨r_ca3, Or.inr (Or.inr (Or.inr rfl)), hR.init_ca3⟩]
  rw [Ksub, hset, h, hR.init_x0, inf_comm]

theorem centralizer_Eh
    (hR : Reg Rg) :
    centralizer ((closure ({(⟨Rg r_x0, x0_mem hR⟩ : ↥j3P), ⟨Rg r_uu, uu_mem hR⟩} : Set ↥j3P) :
      Subgroup ↥j3P) : Set ↥j3P) = (B0 Rg).subgroupOf j3P := by
  rw [centralizer_closure]
  ext x
  rw [mem_centralizer_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    mem_subgroupOf]
  constructor
  · rintro ⟨h1, h2⟩
    have c1 : Rg r_x0 * (x : Gp) = (x : Gp) * Rg r_x0 := congrArg Subtype.val h1
    have c2 : Rg r_uu * (x : Gp) = (x : Gp) * Rg r_uu := congrArg Subtype.val h2
    have hx : (x : Gp) ∈ Ksub Rg gens_CA := by
      rw [CA_eq hR]
      exact ⟨x.2, mem_centralizer_singleton_iff.2 c1.symm⟩
    exact hR.loop_B0 x hx c2.symm
  · intro hx
    exact ⟨Subtype.ext (B0_comm hR x0_B0 hx), Subtype.ext (B0_comm hR uu_B0 hx)⟩

theorem B0_part
    (hR : Reg Rg) :
    CFSG.Open.IsElemAbelian 3 (centralizer ((closure ({(⟨Rg r_x0, x0_mem hR⟩ : ↥j3P),
      ⟨Rg r_uu, uu_mem hR⟩} : Set ↥j3P) : Subgroup ↥j3P) : Set ↥j3P)) ∧
    Nat.card (centralizer ((closure ({(⟨Rg r_x0, x0_mem hR⟩ : ↥j3P),
      ⟨Rg r_uu, uu_mem hR⟩} : Set ↥j3P) : Subgroup ↥j3P) : Set ↥j3P)) = 27 := by
  rw [centralizer_Eh hR]
  exact ⟨isElemAbelian_subgroupOf (B0_le hR) (B0_elem hR),
    by rw [card_subgroupOf_of_le (B0_le hR), hR.card_B0]⟩

theorem mem_normalizer_B0 {f fi : ℕ} (hfi : Rg fi = (Rg f)⁻¹)
    (hx0 : prodG Rg [f, r_x0, fi] ∈ B0 Rg) (huu : prodG Rg [f, r_uu, fi] ∈ B0 Rg)
    (hvv : prodG Rg [f, r_vv, fi] ∈ B0 Rg) : Rg f ∈ normalizer (B0 Rg : Set Gp) := by
  refine mem_normalizer_of_conj_gens (S := Rg '' {r | r ∈ gens_B0}) rfl ?_
  rintro _ ⟨k, hk, rfl⟩
  have e : ∀ b, Rg f * Rg b * (Rg f)⁻¹ = prodG Rg [f, b, fi] := by
    intro b
    simp [prodG, hfi, mul_assoc]
  rw [e]
  simp only [gens_B0, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  exacts [hx0, huu, hvv]

theorem fuse_part
    (hR : Reg Rg) :
    ∀ m : ℕ, (m = 1 ∨ m = 2) → ∃ g ∈ normalizer ((centralizer ((closure
      ({(⟨Rg r_x0, x0_mem hR⟩ : ↥j3P), ⟨Rg r_uu, uu_mem hR⟩} : Set ↥j3P) : Subgroup ↥j3P) :
        Set ↥j3P) : Subgroup ↥j3P) : Set ↥j3P),
      g * (⟨Rg r_x0, x0_mem hR⟩ : ↥j3P) * g⁻¹ =
        ⟨Rg r_x0, x0_mem hR⟩ * ⟨Rg r_uu, uu_mem hR⟩ ^ m := by
  intro m hm
  rw [centralizer_Eh hR, normalizer_subgroupOf (B0_le hR)]
  rcases hm with rfl | rfl
  · refine ⟨⟨Rg r_f1, by simpa using hR.f1_P⟩, ?_, Subtype.ext ?_⟩
    · exact mem_normalizer_B0 (inv_of_prod hR.f1_inv) hR.f1_B0_x0 hR.f1_B0_uu hR.f1_B0_vv
    · have e := hR.f1_conj.trans hR.y1_def
      simp only [prodG_cons, prodG_nil, mul_one, inv_of_prod hR.f1_inv] at e
      simpa [mul_assoc] using e
  · refine ⟨⟨Rg r_f2, by simpa using hR.f2_P⟩, ?_, Subtype.ext ?_⟩
    · exact mem_normalizer_B0 (inv_of_prod hR.f2_inv) hR.f2_B0_x0 hR.f2_B0_uu hR.f2_B0_vv
    · have e := hR.f2_conj.trans hR.y2_def
      simp only [prodG_cons, prodG_nil, mul_one, inv_of_prod hR.f2_inv] at e
      simpa [mul_assoc, pow_two] using e

theorem mem_cj_of_prod {K : Subgroup Gp} {g gi x : ℕ} (hgi : Rg gi = (Rg g)⁻¹)
    (h : prodG Rg [gi, x, g] ∈ K) : Rg x ∈ cj (Rg g) K :=
  mem_cj.2 (by simpa [prodG, hgi, mul_assoc] using h)

theorem gA_mem (hR : Reg Rg) : Rg r_gA ∈ j3P := by simpa using hR.gA_P

theorem gB_mem (hR : Reg Rg) : Rg r_gB ∈ j3P := by simpa using hR.gB_P

theorem gAi_eq (hR : Reg Rg) : Rg r_gAi = (Rg r_gA)⁻¹ := inv_of_prod hR.gA_inv

theorem gBi_eq (hR : Reg Rg) : Rg r_gBi = (Rg r_gB)⁻¹ := inv_of_prod hR.gB_inv

theorem V0_le_H0 (hR : Reg Rg) : V0 Rg ≤ H0 Rg := by
  refine Ksub_le fun r hr => ?_
  simp only [gens_V, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using hR.v1_H
  · simpa using hR.v2_H
  · simpa using hR.v3_H
  · simpa using hR.v4_H

theorem VA_eq (hR : Reg Rg) : Ksub Rg gens_VA = cj (Rg r_gA) (V0 Rg) := by
  have e : ∀ {a v : ℕ}, prodG Rg [a] = prodG Rg [r_gA, v, r_gAi] →
      Rg a = Rg r_gA * Rg v * (Rg r_gA)⁻¹ := by
    intro a v h
    simpa [prodG, gAi_eq hR, mul_assoc] using h
  exact Ksub_conj4 (e hR.vA1_def) (e hR.vA2_def) (e hR.vA3_def) (e hR.vA4_def)

theorem VB_eq (hR : Reg Rg) : Ksub Rg gens_VB = cj (Rg r_gB) (V0 Rg) := by
  have e : ∀ {a v : ℕ}, prodG Rg [a] = prodG Rg [r_gB, v, r_gBi] →
      Rg a = Rg r_gB * Rg v * (Rg r_gB)⁻¹ := by
    intro a v h
    simpa [prodG, gBi_eq hR, mul_assoc] using h
  exact Ksub_conj4 (e hR.vB1_def) (e hR.vB2_def) (e hR.vB3_def) (e hR.vB4_def)

theorem P64_eq (hR : Reg Rg) :
    Ksub Rg gens_P64 = cj (Rg r_gA) (V0 Rg) ⊔ cj (Rg r_gB) (V0 Rg) := by
  rw [gens_P64, Ksub_append, VA_eq hR, VB_eq hR]

theorem P64_le (hR : Reg Rg) : Ksub Rg gens_P64 ≤ j3P := by
  rw [P64_eq hR]
  exact sup_le (cjV0_le hR (gA_mem hR)) (cjV0_le hR (gB_mem hR))

theorem x0_cjM0_A (hR : Reg Rg) : Rg r_x0 ∈ cj (Rg r_gA) (M0 Rg) :=
  mem_cj_of_prod (gAi_eq hR) hR.x0_NA

theorem x0_cjM0_B (hR : Reg Rg) : Rg r_x0 ∈ cj (Rg r_gB) (M0 Rg) :=
  mem_cj_of_prod (gBi_eq hR) hR.x0_NB

theorem uu_cjH0_A (hR : Reg Rg) : Rg r_uu ∈ cj (Rg r_gA) (H0 Rg) :=
  mem_cj_of_prod (gAi_eq hR) hR.uu_HA

theorem uu_cjH0_B (hR : Reg Rg) : Rg r_uu ∈ cj (Rg r_gB) (H0 Rg) :=
  mem_cj_of_prod (gBi_eq hR) hR.uu_HB

theorem VB_le_cjH0_A (hR : Reg Rg) : cj (Rg r_gB) (V0 Rg) ≤ cj (Rg r_gA) (H0 Rg) := by
  rw [← VB_eq hR]
  refine Ksub_le fun r hr => ?_
  simp only [gens_VB, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [mem_cj_of_prod (gAi_eq hR) hR.vB1_HA, mem_cj_of_prod (gAi_eq hR) hR.vB2_HA,
    mem_cj_of_prod (gAi_eq hR) hR.vB3_HA, mem_cj_of_prod (gAi_eq hR) hR.vB4_HA]

theorem VA_le_cjH0_B (hR : Reg Rg) : cj (Rg r_gA) (V0 Rg) ≤ cj (Rg r_gB) (H0 Rg) := by
  rw [← VA_eq hR]
  refine Ksub_le fun r hr => ?_
  simp only [gens_VA, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [mem_cj_of_prod (gBi_eq hR) hR.vA1_HB, mem_cj_of_prod (gBi_eq hR) hR.vA2_HB,
    mem_cj_of_prod (gBi_eq hR) hR.vA3_HB, mem_cj_of_prod (gBi_eq hR) hR.vA4_HB]

theorem normal_closure_frame (hR : Reg Rg) {g gi x1 x2 xi1 xi2 c1 c2 : ℕ} {gensCL : List ℕ}
    (hgens : gensCL = [c1, c2]) (hgi : Rg gi = (Rg g)⁻¹)
    (hcard : Nat.card (Ksub Rg gensCL) = 960) (hu : Rg r_uu ∈ cj (Rg g) (H0 Rg))
    (hx1 : prodG Rg [gi, x1, g] ∈ H0 Rg) (hx2 : prodG Rg [gi, x2, g] ∈ H0 Rg)
    (hxi1 : prodG Rg [x1, xi1] = prodG Rg []) (hxi2 : prodG Rg [x2, xi2] = prodG Rg [])
    (hc1 : prodG Rg [c1] = prodG Rg [x1, r_uu, xi1])
    (hc2 : prodG Rg [c2] = prodG Rg [x2, r_uu, xi2]) :
    closure {z : Gp | ∃ x ∈ cj (Rg g) (H0 Rg), z = x * Rg r_uu * x⁻¹} = cj (Rg g) (H0 Rg) := by
  have hx1' : Rg x1 ∈ cj (Rg g) (H0 Rg) := mem_cj_of_prod hgi hx1
  have hx2' : Rg x2 ∈ cj (Rg g) (H0 Rg) := mem_cj_of_prod hgi hx2
  have hc1' : Rg c1 = Rg x1 * Rg r_uu * (Rg x1)⁻¹ := by
    simpa [prodG, inv_of_prod hxi1, mul_assoc] using hc1
  have hc2' : Rg c2 = Rg x2 * Rg r_uu * (Rg x2)⁻¹ := by
    simpa [prodG, inv_of_prod hxi2, mul_assoc] using hc2
  subst hgens
  refine normal_closure_eq (K' := Ksub Rg [c1, c2]) (S := Rg '' {r | r ∈ [c1, c2]}) hu rfl ?_ ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨Rg x1, hx1', hc1'⟩, ⟨Rg x2, hx2', hc2'⟩]
  · refine Ksub_le fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hc1']
      exact (cj (Rg g) (H0 Rg)).mul_mem ((cj (Rg g) (H0 Rg)).mul_mem hx1' hu)
        ((cj (Rg g) (H0 Rg)).inv_mem hx1')
    · rw [hc2']
      exact (cj (Rg g) (H0 Rg)).mul_mem ((cj (Rg g) (H0 Rg)).mul_mem hx2' hu)
        ((cj (Rg g) (H0 Rg)).inv_mem hx2')
  · rw [hcard, card_cj, hR.card_H]

theorem normal_closure_A (hR : Reg Rg) :
    closure {z : Gp | ∃ x ∈ cj (Rg r_gA) (H0 Rg), z = x * Rg r_uu * x⁻¹} =
      cj (Rg r_gA) (H0 Rg) :=
  normal_closure_frame hR rfl (gAi_eq hR) hR.card_CLA (uu_cjH0_A hR) hR.xA1_H hR.xA2_H
    hR.xA1_inv hR.xA2_inv hR.cA1_def hR.cA2_def

theorem normal_closure_B (hR : Reg Rg) :
    closure {z : Gp | ∃ x ∈ cj (Rg r_gB) (H0 Rg), z = x * Rg r_uu * x⁻¹} =
      cj (Rg r_gB) (H0 Rg) :=
  normal_closure_frame hR rfl (gBi_eq hR) hR.card_CLB (uu_cjH0_B hR) hR.xB1_H hR.xB2_H
    hR.xB1_inv hR.xB2_inv hR.cB1_def hR.cB2_def

theorem prodG_mem_of_subset {K : Subgroup Gp} {l m : List ℕ} (hsub : ∀ i ∈ l, i ∈ m)
    (hm : ∀ i ∈ m, Rg i ∈ K) : prodG Rg l ∈ K :=
  prodG_mem fun i hi => hm i (hsub i hi)

theorem conj_reg_mem {K : Subgroup Gp} {a g gi x : ℕ} (hgi : Rg gi = (Rg g)⁻¹)
    (h : prodG Rg [a] = prodG Rg [g, x, gi]) (hx : Rg x ∈ K) : Rg a ∈ cj (Rg g) K := by
  have : Rg a = Rg g * Rg x * (Rg g)⁻¹ := by simpa [prodG, hgi, mul_assoc] using h
  rw [this]
  exact conj_mem_cj hx

theorem hk_mem (hR : Reg Rg) : ∀ k ∈ gens_H, Rg k ∈ H0 Rg := fun _ hk => Ksub_mem hk

theorem hik_mem (hR : Reg Rg) {h hi : ℕ} (hh : h ∈ gens_H) (hinv : prodG Rg [h, hi] = prodG Rg []) :
    Rg hi ∈ H0 Rg := by
  rw [inv_of_prod hinv]
  exact (H0 Rg).inv_mem (Ksub_mem hh)

theorem P_le_sup (hR : Reg Rg) : j3P ≤ cj (Rg r_gA) (H0 Rg) ⊔ cj (Rg r_gB) (H0 Rg) := by
  set K := cj (Rg r_gA) (H0 Rg) ⊔ cj (Rg r_gB) (H0 Rg) with hK
  have hletter : ∀ i ∈ [r_hA1, r_hA2, r_hA3, r_hA4, r_hAi1, r_hAi2, r_hAi3, r_hAi4,
      r_hB1, r_hB2, r_hB3, r_hB4, r_hBi1, r_hBi2, r_hBi3, r_hBi4], Rg i ∈ K := by
    have hA : ∀ {a x : ℕ}, prodG Rg [a] = prodG Rg [r_gA, x, r_gAi] → Rg x ∈ H0 Rg →
        Rg a ∈ K := fun h hx => Subgroup.mem_sup_left (conj_reg_mem (gAi_eq hR) h hx)
    have hB : ∀ {a x : ℕ}, prodG Rg [a] = prodG Rg [r_gB, x, r_gBi] → Rg x ∈ H0 Rg →
        Rg a ∈ K := fun h hx => Subgroup.mem_sup_right (conj_reg_mem (gBi_eq hR) h hx)
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact hA hR.hA1_def (hk_mem hR _ (by simp [gens_H]))
    · exact hA hR.hA2_def (hk_mem hR _ (by simp [gens_H]))
    · exact hA hR.hA3_def (hk_mem hR _ (by simp [gens_H]))
    · exact hA hR.hA4_def (hk_mem hR _ (by simp [gens_H]))
    · exact hA hR.hAi1_def (hik_mem hR (by simp [gens_H]) hR.h1_inv)
    · exact hA hR.hAi2_def (hik_mem hR (by simp [gens_H]) hR.h2_inv)
    · exact hA hR.hAi3_def (hik_mem hR (by simp [gens_H]) hR.h3_inv)
    · exact hA hR.hAi4_def (hik_mem hR (by simp [gens_H]) hR.h4_inv)
    · exact hB hR.hB1_def (hk_mem hR _ (by simp [gens_H]))
    · exact hB hR.hB2_def (hk_mem hR _ (by simp [gens_H]))
    · exact hB hR.hB3_def (hk_mem hR _ (by simp [gens_H]))
    · exact hB hR.hB4_def (hk_mem hR _ (by simp [gens_H]))
    · exact hB hR.hBi1_def (hik_mem hR (by simp [gens_H]) hR.h1_inv)
    · exact hB hR.hBi2_def (hik_mem hR (by simp [gens_H]) hR.h2_inv)
    · exact hB hR.hBi3_def (hik_mem hR (by simp [gens_H]) hR.h3_inv)
    · exact hB hR.hBi4_def (hik_mem hR (by simp [gens_H]) hR.h4_inv)
  have ha0 : Rg r_a0 ∈ K := by
    rw [show Rg r_a0 = prodG Rg [r_a0] by simp, hR.a0_word]
    exact prodG_mem_of_subset (by decide) hletter
  have ha1 : Rg r_a1 ∈ K := by
    rw [show Rg r_a1 = prodG Rg [r_a1] by simp, hR.a1_word]
    exact prodG_mem_of_subset (by decide) hletter
  refine (closure_le K).2 ?_
  rintro _ (rfl | rfl)
  · rw [← hR.init_a0]; exact ha0
  · rw [← hR.init_a1]; exact ha1

theorem aut_frame
    (hR : Reg Rg) {g : Gp} (hg : g ∈ j3P) :
    ∀ σ : MulAut ↥j3P, (∀ v ∈ VJ Rg g, σ v = v) → ∃ v ∈ VJ Rg g, σ = MulAut.conj v := by
  obtain ⟨e, he, -⟩ := ctuc_j3_full_automorphism_permutation_model
  obtain ⟨-, -, -, -, -, hRmem, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  intro σ hσ
  set r : ↥j3R := e.symm σ with hr
  have hσr : σ = e r := by simp [hr]
  have hcentr : ∀ v ∈ cj g (V0 Rg), (r : Gp) * v * (r : Gp)⁻¹ = v := by
    intro v hv
    have h1 := hσ ⟨v, cjV0_le hR hg hv⟩ (mem_subgroupOf.2 hv)
    rw [hσr] at h1
    have h2 := congrArg (fun z : ↥j3P => (z : Gp)) h1
    simp only [he] at h2
    exact h2
  set r' : Gp := g⁻¹ * (r : Gp) * g with hr'
  have hgR : g ∈ j3R := (le_sup_left : j3P ≤ j3P ⊔ Subgroup.zpowers j3u) hg
  have hr'R : r' ∈ j3R := j3R.mul_mem (j3R.mul_mem (j3R.inv_mem hgR) r.2) hgR
  have hcomm : ∀ v ∈ V0 Rg, r' * v = v * r' := by
    intro v hv
    have h := hcentr (g * v * g⁻¹) (conj_mem_cj hv)
    calc r' * v = g⁻¹ * ((r : Gp) * (g * v * g⁻¹) * (r : Gp)⁻¹) * (r : Gp) * g := by
          rw [hr']; group
      _ = v * r' := by rw [h, hr']; group
  have hv_mem : ∀ k ∈ gens_V, Rg k ∈ V0 Rg := fun _ hk => Ksub_mem hk
  have hcommv : r' * Rg r_v1 = Rg r_v1 * r' ∧ r' * Rg r_v2 = Rg r_v2 * r' ∧
      r' * Rg r_v3 = Rg r_v3 * r' ∧ r' * Rg r_v4 = Rg r_v4 * r' :=
    ⟨hcomm _ (hv_mem _ (by simp [gens_V])), hcomm _ (hv_mem _ (by simp [gens_V])),
      hcomm _ (hv_mem _ (by simp [gens_V])), hcomm _ (hv_mem _ (by simp [gens_V]))⟩
  have hrV : r' ∈ V0 Rg := by
    have ht : r' * Rg r_t1 = Rg r_t1 * r' := hcomm _ (t1_mem hR)
    rcases (hRmem r').1 hr'R with hP | hu
    · have hC : r' ∈ Ksub Rg gens_C := by
        rw [C_eq hR]
        exact ⟨hP, mem_centralizer_singleton_iff.2 ht⟩
      exact hR.loop_J5a r' hC hcommv
    · exfalso
      have hwu : Rg r_w * j3u ∈ j3P := by
        have := hR.w_u
        simpa [prodG, hR.init_u] using this
      have hwt : Rg r_w * Rg r_t1 = Rg r_t1 * Rg r_w := by
        have := hR.w_t1
        simpa [prodG] using this
      set c : Gp := r' * (Rg r_w)⁻¹ with hc
      have hcP : c ∈ j3P := by
        have : c = (r' * j3u) * (Rg r_w * j3u)⁻¹ := by rw [hc]; group
        rw [this]
        exact j3P.mul_mem hu (j3P.inv_mem hwu)
      have hct : c * Rg r_t1 = Rg r_t1 * c := by
        have hw' : (Rg r_w)⁻¹ * Rg r_t1 = Rg r_t1 * (Rg r_w)⁻¹ := by
          calc (Rg r_w)⁻¹ * Rg r_t1 = (Rg r_w)⁻¹ * (Rg r_t1 * Rg r_w) * (Rg r_w)⁻¹ := by group
            _ = (Rg r_w)⁻¹ * (Rg r_w * Rg r_t1) * (Rg r_w)⁻¹ := by rw [hwt]
            _ = Rg r_t1 * (Rg r_w)⁻¹ := by group
        calc c * Rg r_t1 = r' * ((Rg r_w)⁻¹ * Rg r_t1) := by rw [hc]; group
          _ = r' * (Rg r_t1 * (Rg r_w)⁻¹) := by rw [hw']
          _ = (r' * Rg r_t1) * (Rg r_w)⁻¹ := by group
          _ = Rg r_t1 * c := by rw [ht, hc]; group
      have hC : c ∈ Ksub Rg gens_C := by
        rw [C_eq hR]
        exact ⟨hcP, mem_centralizer_singleton_iff.2 hct⟩
      have hcw : c * Rg r_w = r' := by rw [hc]; group
      refine hR.loop_J5b c hC ?_
      rw [hcw]
      exact ⟨hcommv.1, hcommv.2.1, hcommv.2.2.1, hcommv.2.2.2⟩
  have hrr : (r : Gp) = g * r' * g⁻¹ := by rw [hr']; group
  have hrcj : (r : Gp) ∈ cj g (V0 Rg) := by rw [hrr]; exact conj_mem_cj hrV
  have hrP : (r : Gp) ∈ j3P := cjV0_le hR hg hrcj
  refine ⟨⟨r, hrP⟩, mem_subgroupOf.2 hrcj, MulEquiv.ext fun p => ?_⟩
  rw [hσr]
  apply Subtype.ext
  rw [he]
  simp

theorem four_frame (hR : Reg Rg) {y : ℕ} (hy : Rg y ∈ j3P)
    (hcount : Set.ncard {x | x ∈ Ksub Rg gens_P64 ∧ x * Rg y = Rg y * x} = 4)
    (hex : ∃ x ∈ Ksub Rg gens_P64, (x * Rg y = Rg y * x ∧ ¬(x * Rg r_uu = Rg r_uu * x))) :
    Nat.card ↥(centralizer ({(⟨Rg y, hy⟩ : ↥j3P)} : Set ↥j3P) ⊓
        (Ksub Rg gens_P64).subgroupOf j3P) = 4 ∧
      ∃ w ∈ centralizer ({(⟨Rg y, hy⟩ : ↥j3P)} : Set ↥j3P) ⊓
          (Ksub Rg gens_P64).subgroupOf j3P,
        (⟨Rg r_uu, uu_mem hR⟩ : ↥j3P) * w * (⟨Rg r_uu, uu_mem hR⟩ : ↥j3P)⁻¹ ≠ w := by
  rw [centralizer_inf_subgroupOf]
  refine ⟨?_, ?_⟩
  · rw [card_subgroupOf_of_le (inf_le_right.trans (P64_le hR))]
    have hset : ((centralizer ({Rg y} : Set Gp) ⊓ Ksub Rg gens_P64 : Subgroup Gp) : Set Gp) =
        {x | x ∈ Ksub Rg gens_P64 ∧ x * Rg y = Rg y * x} := by
      ext x
      simp only [SetLike.mem_coe, mem_inf, mem_centralizer_singleton_iff, Set.mem_setOf_eq]
      tauto
    rw [← hcount, ← hset]
    exact Nat.card_coe_set_eq _
  · obtain ⟨x, hx, hxy, hxu⟩ := hex
    have hxP : x ∈ j3P := P64_le hR hx
    refine ⟨⟨x, hxP⟩, mem_subgroupOf.2 ⟨mem_centralizer_singleton_iff.2 hxy, hx⟩, fun h => hxu ?_⟩
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
    calc x * Rg r_uu = (Rg r_uu * x * (Rg r_uu)⁻¹) * Rg r_uu := by rw [h']
      _ = Rg r_uu * x := by group

theorem four_part (hR : Reg Rg) :
    ∀ m : ℕ, m < 3 →
      Nat.card ↥(centralizer ({(⟨Rg r_x0, x0_mem hR⟩ : ↥j3P) *
          (⟨Rg r_uu, uu_mem hR⟩ : ↥j3P) ^ m} : Set ↥j3P) ⊓
          (VJ Rg (Rg r_gA) ⊔ VJ Rg (Rg r_gB) : Subgroup ↥j3P)) = 4 ∧
        ∃ w ∈ centralizer ({(⟨Rg r_x0, x0_mem hR⟩ : ↥j3P) *
            (⟨Rg r_uu, uu_mem hR⟩ : ↥j3P) ^ m} : Set ↥j3P) ⊓
            (VJ Rg (Rg r_gA) ⊔ VJ Rg (Rg r_gB) : Subgroup ↥j3P),
          (⟨Rg r_uu, uu_mem hR⟩ : ↥j3P) * w * (⟨Rg r_uu, uu_mem hR⟩ : ↥j3P)⁻¹ ≠ w := by
  have hsup : (VJ Rg (Rg r_gA) ⊔ VJ Rg (Rg r_gB) : Subgroup ↥j3P) =
      (Ksub Rg gens_P64).subgroupOf j3P := by
    rw [VJ, VJ, ← subgroupOf_sup (cjV0_le hR (gA_mem hR)) (cjV0_le hR (gB_mem hR)), P64_eq hR]
  have hy1 : Rg r_y1 ∈ j3P := by
    have := hR.y1_def
    simp only [prodG_cons, prodG_nil, mul_one] at this
    rw [this]
    exact j3P.mul_mem (x0_mem hR) (uu_mem hR)
  have hy2 : Rg r_y2 ∈ j3P := by
    have := hR.y2_def
    simp only [prodG_cons, prodG_nil, mul_one] at this
    rw [this]
    exact j3P.mul_mem (x0_mem hR) (j3P.mul_mem (uu_mem hR) (uu_mem hR))
  intro m hm
  rw [hsup]
  interval_cases m
  · have e : (⟨Rg r_x0, x0_mem hR⟩ : ↥j3P) * (⟨Rg r_uu, uu_mem hR⟩ : ↥j3P) ^ 0 =
        ⟨Rg r_x0, x0_mem hR⟩ := by simp
    rw [e]
    exact four_frame hR (x0_mem hR) hR.loop_four0 hR.loop_nonab0
  · have e : (⟨Rg r_x0, x0_mem hR⟩ : ↥j3P) * (⟨Rg r_uu, uu_mem hR⟩ : ↥j3P) ^ 1 =
        ⟨Rg r_y1, hy1⟩ := by
      apply Subtype.ext
      have := hR.y1_def
      simp only [prodG_cons, prodG_nil, mul_one] at this
      simp [this]
    rw [e]
    exact four_frame hR hy1 hR.loop_four1 hR.loop_nonab1
  · have e : (⟨Rg r_x0, x0_mem hR⟩ : ↥j3P) * (⟨Rg r_uu, uu_mem hR⟩ : ↥j3P) ^ 2 =
        ⟨Rg r_y2, hy2⟩ := by
      apply Subtype.ext
      have := hR.y2_def
      simp only [prodG_cons, prodG_nil, mul_one] at this
      simp [this, pow_two, mul_assoc]
    rw [e]
    exact four_frame hR hy2 hR.loop_four2 hR.loop_nonab2

@[expose] def VPair (Rg : ℕ → Gp) : Fin 2 → Subgroup ↥j3P :=
  fun i => if i = 0 then VJ Rg (Rg r_gA) else VJ Rg (Rg r_gB)

@[simp] theorem VPair_zero : VPair Rg 0 = VJ Rg (Rg r_gA) := if_pos rfl

@[simp] theorem VPair_one : VPair Rg 1 = VJ Rg (Rg r_gB) := if_neg (by decide)

theorem vpair_facts
    (hR : Reg Rg) :
    J3VPair ↥j3P ⟨Rg r_x0, x0_mem hR⟩ ⟨Rg r_uu, uu_mem hR⟩ (VPair Rg) := by
  have hgA := gA_mem hR
  have hgB := gB_mem hR
  have hnorm0 : normalizer (VPair Rg 0 : Set ↥j3P) = (cj (Rg r_gA) (M0 Rg)).subgroupOf j3P := by
    rw [VPair_zero]; exact VJ_normalizer hR hgA
  have hnorm1 : normalizer (VPair Rg 1 : Set ↥j3P) = (cj (Rg r_gB) (M0 Rg)).subgroupOf j3P := by
    rw [VPair_one]; exact VJ_normalizer hR hgB
  have hres0 : inSubgroup perfectResidual (normalizer (VPair Rg 0 : Set ↥j3P)) =
      (cj (Rg r_gA) (H0 Rg)).subgroupOf j3P := by
    rw [VPair_zero]; exact VJ_residual hR hgA
  have hres1 : inSubgroup perfectResidual (normalizer (VPair Rg 1 : Set ↥j3P)) =
      (cj (Rg r_gB) (H0 Rg)).subgroupOf j3P := by
    rw [VPair_one]; exact VJ_residual hR hgB
  have hV00 : VPair Rg 0 ≤ (cj (Rg r_gA) (H0 Rg)).subgroupOf j3P := by
    rw [VPair_zero]; exact subgroupOf_le_subgroupOf (cj_mono _ (V0_le_H0 hR))
  have hV11 : VPair Rg 1 ≤ (cj (Rg r_gB) (H0 Rg)).subgroupOf j3P := by
    rw [VPair_one]; exact subgroupOf_le_subgroupOf (cj_mono _ (V0_le_H0 hR))
  have hV10 : VPair Rg 1 ≤ (cj (Rg r_gA) (H0 Rg)).subgroupOf j3P := by
    rw [VPair_one]; exact subgroupOf_le_subgroupOf (VB_le_cjH0_A hR)
  have hV01 : VPair Rg 0 ≤ (cj (Rg r_gB) (H0 Rg)).subgroupOf j3P := by
    rw [VPair_zero]; exact subgroupOf_le_subgroupOf (VA_le_cjH0_B hR)
  have hHM : ∀ g : Gp, cj g (H0 Rg) ≤ cj g (M0 Rg) := fun g => cj_mono g (H0_le_M0 hR)
  have hle : ∀ i j : Fin 2, VPair Rg j ≤ inSubgroup perfectResidual
      (normalizer (VPair Rg i : Set ↥j3P)) := by
    intro i j
    fin_cases i <;> fin_cases j
    · rw [show ((⟨0, by omega⟩ : Fin 2)) = 0 from rfl, hres0]; exact hV00
    · rw [show ((⟨0, by omega⟩ : Fin 2)) = 0 from rfl, hres0]; exact hV10
    · rw [show ((⟨1, by omega⟩ : Fin 2)) = 1 from rfl, hres1]; exact hV01
    · rw [show ((⟨1, by omega⟩ : Fin 2)) = 1 from rfl, hres1]; exact hV11
  refine ⟨?_, ?_, ?_, ?_, hle, ?_, ?_, ?_, ?_, four_part hR⟩
  · intro i
    fin_cases i
    · simpa using VJ_elem hR hgA
    · simpa using VJ_elem hR hgB
  · intro i
    fin_cases i
    · rw [show ((⟨0, by omega⟩ : Fin 2)) = 0 from rfl, hnorm0]
      exact ⟨mem_subgroupOf.2 (x0_cjM0_A hR), mem_subgroupOf.2 (hHM _ (uu_cjH0_A hR))⟩
    · rw [show ((⟨1, by omega⟩ : Fin 2)) = 1 from rfl, hnorm1]
      exact ⟨mem_subgroupOf.2 (x0_cjM0_B hR), mem_subgroupOf.2 (hHM _ (uu_cjH0_B hR))⟩
  · rw [VPair_zero, VPair_one, VJ, VJ,
      ← subgroupOf_sup (cjV0_le hR hgA) (cjV0_le hR hgB), ← P64_eq hR,
      card_subgroupOf_of_le (P64_le hR), hR.card_P64]
  · intro i j
    exact (hle i j).trans (Subgroup.map_subtype_le _)
  · intro i
    fin_cases i
    · rw [show ((⟨0, by omega⟩ : Fin 2)) = 0 from rfl, hres0]
      exact mem_subgroupOf.2 (uu_cjH0_A hR)
    · rw [show ((⟨1, by omega⟩ : Fin 2)) = 1 from rfl, hres1]
      exact mem_subgroupOf.2 (uu_cjH0_B hR)
  · intro i
    fin_cases i
    · rw [show ((⟨0, by omega⟩ : Fin 2)) = 0 from rfl, hres0]
      exact closure_conj_set_subgroupOf (cjH0_le hR hgA) (uu_cjH0_A hR) (normal_closure_A hR)
    · rw [show ((⟨1, by omega⟩ : Fin 2)) = 1 from rfl, hres1]
      exact closure_conj_set_subgroupOf (cjH0_le hR hgB) (uu_cjH0_B hR) (normal_closure_B hR)
  · rw [hres0, hres1, ← subgroupOf_sup (cjH0_le hR hgA) (cjH0_le hR hgB)]
    exact eq_top_iff.2 fun x _ => mem_subgroupOf.2 (P_le_sup hR x.2)
  · intro i
    fin_cases i
    · simpa using aut_frame hR hgA
    · simpa using aut_frame hR hgB

theorem pair_facts
    (hR : Reg Rg) :
    J3TwoLocalFacts ↥j3P ⟨Rg r_x0, x0_mem hR⟩ ⟨Rg r_uu, uu_mem hR⟩ :=
  ⟨B0_part hR, fuse_part hR, VPair Rg, vpair_facts hR⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611.J3T
