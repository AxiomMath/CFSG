module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommParts

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Explicit

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {φ : L ≃* antiSp K}

theorem sixH_s_lift_mul (V W : antiSp K) :
    ((φ.symm (V * W) : L) : G) = ((φ.symm V : L) : G) * ((φ.symm W : L) : G) := by
  rw [map_mul, Subgroup.coe_mul]

theorem sixH_s_lift_inv (V : antiSp K) :
    ((φ.symm V⁻¹ : L) : G) = ((φ.symm V : L) : G)⁻¹ := by
  rw [map_inv, Subgroup.coe_inv]

theorem sixH_s_lift_one : ((φ.symm 1 : L) : G) = 1 := by
  rw [map_one, Subgroup.coe_one]

theorem sixH_s_exists_lift {S : Subgroup (antiSp K)} {g : G} (hg : g ∈ pull φ S) :
    ∃ V ∈ S, g = ((φ.symm V : L) : G) := by
  obtain ⟨h, hS⟩ := mem_pull.mp hg
  exact ⟨φ ⟨g, h⟩, hS, by rw [MulEquiv.symm_apply_apply]⟩

theorem sixH_s_w_conj (k : Axis) (V : antiSp K) :
    w φ k * ((φ.symm V : L) : G) * (w φ k)⁻¹ =
      ((φ.symm (FullCenterWeyl.weylElt K k * V * (FullCenterWeyl.weylElt K k)⁻¹) : L) : G) := by
  simp only [w, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem sixH_s_w_conj' (k : Axis) (V : antiSp K) :
    (w φ k)⁻¹ * ((φ.symm V : L) : G) * w φ k =
      ((φ.symm ((FullCenterWeyl.weylElt K k)⁻¹ * V * FullCenterWeyl.weylElt K k) : L) : G) := by
  simp only [w, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem sixH_s2_w1_comm_u1 (b : K) :
    FullCenterWeyl.weylElt K Axis.one * uElt 0 b 0 0 =
      uElt 0 b 0 0 * FullCenterWeyl.weylElt K Axis.one := by
  apply antiSp_ext
  show FullCenterWeyl.weylMat K Axis.one * uMat 0 b 0 0 =
    uMat 0 b 0 0 * FullCenterWeyl.weylMat K Axis.one
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [uMat, FullCenterWeyl.weylMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem sixH_s2_w2_comm_u2 (c : K) :
    FullCenterWeyl.weylElt K Axis.two * uElt 0 0 c 0 =
      uElt 0 0 c 0 * FullCenterWeyl.weylElt K Axis.two := by
  apply antiSp_ext
  show FullCenterWeyl.weylMat K Axis.two * uMat 0 0 c 0 =
    uMat 0 0 c 0 * FullCenterWeyl.weylMat K Axis.two
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [uMat, FullCenterWeyl.weylMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem sixH_s2_w2_conj_u1 (b : K) :
    FullCenterWeyl.weylElt K Axis.two * uElt 0 b 0 0 * FullCenterWeyl.weylElt K Axis.two =
      uElt b 0 0 0 := by
  apply antiSp_ext
  show FullCenterWeyl.weylMat K Axis.two * uMat 0 b 0 0 * FullCenterWeyl.weylMat K Axis.two =
    uMat b 0 0 0
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [uMat, FullCenterWeyl.weylMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem sixH_s2_w1_conj_u2 (c : K) :
    FullCenterWeyl.weylElt K Axis.one * uElt 0 0 c 0 * FullCenterWeyl.weylElt K Axis.one =
      uElt 0 0 0 c := by
  apply antiSp_ext
  show FullCenterWeyl.weylMat K Axis.one * uMat 0 0 c 0 * FullCenterWeyl.weylMat K Axis.one =
    uMat 0 0 0 c
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [uMat, FullCenterWeyl.weylMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem sixH_uElt_congr {a b c d A B C D : K} (h1 : a = A) (h2 : b = B) (h3 : c = C)
    (h4 : d = D) : uElt a b c d = uElt A B C D := by
  subst h1 h2 h3 h4
  rfl

theorem sixH_s1_inv_one (b c d : K) : (uElt 0 b c d)⁻¹ = uElt 0 b c d := by
  rw [uElt_inv, zero_mul, add_zero]

theorem sixH_s1_inv_two (a b c : K) : (uElt a b c 0)⁻¹ = uElt a b c 0 := by
  rw [uElt_inv, mul_zero, add_zero]

theorem sixH_s1_prod_one (b c d A B C : K) :
    uElt 0 b c d * uElt A B C 0 = uElt A (b + B) (c + C + b * A) d := by
  rw [uElt_mul]
  apply sixH_uElt_congr <;> ring

theorem sixH_s1_prod_two (a b c B C D : K) :
    uElt a b c 0 * uElt 0 B C D = uElt a (b + B + a * D) (c + C + a * B) D := by
  rw [uElt_mul]
  apply sixH_uElt_congr <;> ring

theorem sixH_s1_assoc4 (V W : antiSp K) : V * W * V * W = (V * W) * (V * W) := by
  simp only [mul_assoc]

theorem sixH_s1_formula_one (b c d A B C : K) :
    (uElt 0 b c d)⁻¹ * (uElt A B C 0)⁻¹ * uElt 0 b c d * uElt A B C 0 =
      uElt 0 (A * d) (A ^ 2 * d) 0 := by
  rw [sixH_s1_inv_one, sixH_s1_inv_two, sixH_s1_assoc4, sixH_s1_prod_one, uElt_mul_self]

theorem sixH_s1_formula_two (a b c B C D : K) :
    (uElt a b c 0)⁻¹ * (uElt 0 B C D)⁻¹ * uElt a b c 0 * uElt 0 B C D =
      uElt 0 (a * D) (a ^ 2 * D) 0 := by
  rw [sixH_s1_inv_two, sixH_s1_inv_one, sixH_s1_assoc4, sixH_s1_prod_two, uElt_mul_self]

theorem sixH_s_comm_lift (V W : antiSp K) :
    ((φ.symm V : L) : G)⁻¹ * ((φ.symm W : L) : G)⁻¹ * ((φ.symm V : L) : G) *
      ((φ.symm W : L) : G) = ((φ.symm (V⁻¹ * W⁻¹ * V * W) : L) : G) := by
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem sixH_s_memZ (b c : K) : ((φ.symm (uElt 0 b c 0) : L) : G) ∈ Z₀ φ :=
  symm_mem_pull.mpr ⟨b, c, rfl⟩

theorem sixH_s1_final {α δ : K} (hα : α ≠ 0) (hδ : δ ≠ 0) :
    ((φ.symm (uElt 0 (α * δ) (α ^ 2 * δ) 0) : L) : G) ∈ Z₀ φ ∧
      ((φ.symm (uElt 0 (α * δ) (α ^ 2 * δ) 0) : L) : G) ∉ U φ Axis.one ∧
      ((φ.symm (uElt 0 (α * δ) (α ^ 2 * δ) 0) : L) : G) ∉ U φ Axis.two := by
  refine ⟨sixH_s_memZ _ _, fun h => ?_, fun h => ?_⟩
  · obtain ⟨b', hb⟩ := symm_mem_pull.mp h
    exact mul_ne_zero (pow_ne_zero 2 hα) hδ (uElt_inj hb).2.2.1
  · obtain ⟨c', hc⟩ := symm_mem_pull.mp h
    exact mul_ne_zero hα hδ (uElt_inj hc).2.1

theorem sixH_s1_pairing (k : Axis) {y x : G} (hy : y ∈ A φ k) (hyZ : y ∉ Z₀ φ)
    (hx : x ∈ A φ k.swap) (hxZ : x ∉ Z₀ φ) :
    y⁻¹ * x⁻¹ * y * x ∈ Z₀ φ ∧ y⁻¹ * x⁻¹ * y * x ∉ U φ Axis.one ∧
      y⁻¹ * x⁻¹ * y * x ∉ U φ Axis.two := by
  cases k
  · obtain ⟨V, hV, rfl⟩ := sixH_s_exists_lift hy
    obtain ⟨W, hW, rfl⟩ := sixH_s_exists_lift hx
    obtain ⟨b, c, d, rfl⟩ := hV
    obtain ⟨a, B, C, rfl⟩ := hW
    have hd : d ≠ 0 := by
      rintro rfl
      exact hyZ (sixH_s_memZ b c)
    have ha : a ≠ 0 := by
      rintro rfl
      exact hxZ (sixH_s_memZ B C)
    rw [sixH_s_comm_lift, sixH_s1_formula_one]
    exact sixH_s1_final ha hd
  · obtain ⟨V, hV, rfl⟩ := sixH_s_exists_lift hy
    obtain ⟨W, hW, rfl⟩ := sixH_s_exists_lift hx
    obtain ⟨a, b, c, rfl⟩ := hV
    obtain ⟨B, C, D, rfl⟩ := hW
    have ha : a ≠ 0 := by
      rintro rfl
      exact hyZ (sixH_s_memZ b c)
    have hD : D ≠ 0 := by
      rintro rfl
      exact hxZ (sixH_s_memZ B C)
    rw [sixH_s_comm_lift, sixH_s1_formula_two]
    exact sixH_s1_final ha hD

theorem sixH_s2_weyl (i : Axis) :
    (∀ u ∈ U φ i, w φ i * u = u * w φ i) ∧
      (∀ u ∈ U φ i.swap, u ≠ 1 →
        (w φ i)⁻¹ * u * w φ i ∈ A φ i ∧ (w φ i)⁻¹ * u * w φ i ∉ Z₀ φ) := by
  refine ⟨fun u hu => ?_, fun u hu hu1 => ?_⟩
  · obtain ⟨V, hV, rfl⟩ := sixH_s_exists_lift hu
    have hc : FullCenterWeyl.weylElt K i * V = V * FullCenterWeyl.weylElt K i := by
      cases i
      · obtain ⟨b, rfl⟩ := hV
        exact sixH_s2_w1_comm_u1 b
      · obtain ⟨c, rfl⟩ := hV
        exact sixH_s2_w2_comm_u2 c
    show ((φ.symm (FullCenterWeyl.weylElt K i) : L) : G) * ((φ.symm V : L) : G) =
      ((φ.symm V : L) : G) * ((φ.symm (FullCenterWeyl.weylElt K i) : L) : G)
    rw [← sixH_s_lift_mul, ← sixH_s_lift_mul, hc]
  · obtain ⟨V, hV, rfl⟩ := sixH_s_exists_lift hu
    rw [sixH_s_w_conj']
    cases i
    · obtain ⟨c, rfl⟩ := hV
      rw [FullCenterWeyl.weylElt_inv, sixH_s2_w1_conj_u2]
      have hc0 : c ≠ 0 := by
        rintro rfl
        apply hu1
        rw [uElt_zero_eq_one, sixH_s_lift_one]
      refine ⟨symm_mem_pull.mpr ⟨0, 0, c, rfl⟩, fun h => ?_⟩
      obtain ⟨b', c', hb⟩ := symm_mem_pull.mp h
      exact hc0 (uElt_inj hb).2.2.2
    · obtain ⟨b, rfl⟩ := hV
      rw [FullCenterWeyl.weylElt_inv, sixH_s2_w2_conj_u1]
      have hb0 : b ≠ 0 := by
        rintro rfl
        apply hu1
        rw [uElt_zero_eq_one, sixH_s_lift_one]
      refine ⟨symm_mem_pull.mpr ⟨b, 0, 0, rfl⟩, fun h => ?_⟩
      obtain ⟨b', c', hb⟩ := symm_mem_pull.mp h
      exact hb0 (uElt_inj hb).1

theorem sixH_s3_inv_a (a : K) : (uElt a 0 0 0)⁻¹ = uElt a 0 0 0 := by
  rw [uElt_inv, mul_zero, add_zero]

theorem sixH_s3_conj_one (a c : K) :
    uElt a 0 0 0 * uElt 0 0 0 c * (uElt a 0 0 0)⁻¹ = uElt 0 (a * c) (a ^ 2 * c) c := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [sixH_s3_inv_a, uElt_mul, uElt_mul]
  apply sixH_uElt_congr
  · linear_combination a * h2
  · ring
  · ring
  · ring

theorem sixH_s3_conj_two (β c : K) :
    uElt 0 0 0 c * uElt β 0 0 0 * (uElt 0 0 0 c)⁻¹ = uElt β (β * c) 0 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [sixH_s1_inv_one, uElt_mul, uElt_mul]
  apply sixH_uElt_congr
  · ring
  · ring
  · ring
  · linear_combination c * h2

theorem sixH_s3_split_c2 (c : K) :
    uElt 0 0 c 0 = uElt 1 0 0 0 * uElt 0 c 0 0 * uElt 1 c 0 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_mul, uElt_mul]
  apply sixH_uElt_congr
  · linear_combination (-1 : K) * h2
  · linear_combination (-c) * h2
  · linear_combination (-c) * h2
  · ring

theorem sixH_s3_split_A2 (a b c : K) :
    uElt a b c 0 = uElt a 0 0 0 * uElt 0 b 0 0 * uElt 0 0 (c - a * b) 0 := by
  rw [uElt_mul, uElt_mul]
  apply sixH_uElt_congr <;> ring

theorem sixH_s3_split_A1 (b c d : K) :
    uElt 0 b c d = uElt 0 b (b ^ 2) 1 * uElt 0 0 (c - b ^ 2) 0 * uElt 0 0 0 (d - 1) := by
  rw [uElt_mul, uElt_mul]
  apply sixH_uElt_congr <;> ring

theorem sixH_s3_w1_conj (c : K) :
    w φ Axis.one * ((φ.symm (uElt 0 0 c 0) : L) : G) * (w φ Axis.one)⁻¹ =
      ((φ.symm (uElt 0 0 0 c) : L) : G) := by
  rw [sixH_s_w_conj, FullCenterWeyl.weylElt_inv, sixH_s2_w1_conj_u2]

theorem sixH_s3_w2_conj (β : K) :
    w φ Axis.two * ((φ.symm (uElt 0 β 0 0) : L) : G) * (w φ Axis.two)⁻¹ =
      ((φ.symm (uElt β 0 0 0) : L) : G) := by
  rw [sixH_s_w_conj, FullCenterWeyl.weylElt_inv, sixH_s2_w2_conj_u1]

theorem sixH_s3_conj_one_G (a c : K) :
    ((φ.symm (uElt a 0 0 0) : L) : G) * ((φ.symm (uElt 0 0 0 c) : L) : G) *
        ((φ.symm (uElt a 0 0 0) : L) : G)⁻¹ =
      ((φ.symm (uElt 0 (a * c) (a ^ 2 * c) c) : L) : G) := by
  rw [← sixH_s_lift_inv, ← sixH_s_lift_mul, ← sixH_s_lift_mul, sixH_s3_conj_one]

theorem sixH_s3_conj_two_G (β c : K) :
    ((φ.symm (uElt 0 0 0 c) : L) : G) * ((φ.symm (uElt β 0 0 0) : L) : G) *
        ((φ.symm (uElt 0 0 0 c) : L) : G)⁻¹ =
      ((φ.symm (uElt β (β * c) 0 0) : L) : G) := by
  rw [← sixH_s_lift_inv, ← sixH_s_lift_mul, ← sixH_s_lift_mul, sixH_s3_conj_two]

theorem sixH_s3_memU_one (b : K) : ((φ.symm (uElt 0 b 0 0) : L) : G) ∈ U φ Axis.one :=
  symm_mem_pull.mpr ⟨b, rfl⟩

theorem sixH_s3_memU_two (c : K) : ((φ.symm (uElt 0 0 c 0) : L) : G) ∈ U φ Axis.two :=
  symm_mem_pull.mpr ⟨c, rfl⟩

theorem sixH_s3_memP_a (a : K) : ((φ.symm (uElt a 0 0 0) : L) : G) ∈ P φ :=
  symm_mem_pull.mpr ⟨a, 0, 0, 0, rfl⟩

theorem sixH_s3_memP_c (c : K) : ((φ.symm (uElt 0 0 0 c) : L) : G) ∈ P φ :=
  symm_mem_pull.mpr ⟨0, 0, 0, c, rfl⟩

theorem sixH_s3_of_one {X : Subgroup G} (hXA : X ≤ A φ Axis.two)
    (hP : ∀ p ∈ P φ, ∀ x ∈ X, p * x * p⁻¹ ∈ X)
    (hw : ∀ x ∈ X, w φ Axis.two * x * (w φ Axis.two)⁻¹ ∈ X)
    (hU : U φ Axis.one ≤ X) : X = A φ Axis.two := by
  refine le_antisymm hXA ?_
  have hT : ∀ β : K, ((φ.symm (uElt β 0 0 0) : L) : G) ∈ X := by
    intro β
    have h := hw _ (hU (sixH_s3_memU_one β))
    rwa [sixH_s3_w2_conj β] at h
  have hV : ∀ c : K, ((φ.symm (uElt 0 0 c 0) : L) : G) ∈ X := by
    intro c
    have h3 : ((φ.symm (uElt 1 c 0 0) : L) : G) ∈ X := by
      have h := hP _ (sixH_s3_memP_c c) _ (hT 1)
      rwa [sixH_s3_conj_two_G, one_mul] at h
    rw [sixH_s3_split_c2 c, sixH_s_lift_mul, sixH_s_lift_mul]
    exact mul_mem (mul_mem (hT 1) (hU (sixH_s3_memU_one c))) h3
  intro g hg
  obtain ⟨V, hVg, rfl⟩ := sixH_s_exists_lift hg
  obtain ⟨a, b, c, rfl⟩ := hVg
  rw [sixH_s3_split_A2 a b c, sixH_s_lift_mul, sixH_s_lift_mul]
  exact mul_mem (mul_mem (hT a) (hU (sixH_s3_memU_one b))) (hV (c - a * b))

theorem sixH_s3_of_two {X : Subgroup G} (hXA : X ≤ A φ Axis.one)
    (hP : ∀ p ∈ P φ, ∀ x ∈ X, p * x * p⁻¹ ∈ X)
    (hw : ∀ x ∈ X, w φ Axis.one * x * (w φ Axis.one)⁻¹ ∈ X)
    (hU : U φ Axis.two ≤ X) : X = A φ Axis.one := by
  refine le_antisymm hXA ?_
  have hT : ∀ c : K, ((φ.symm (uElt 0 0 0 c) : L) : G) ∈ X := by
    intro c
    have h := hw _ (hU (sixH_s3_memU_two c))
    rwa [sixH_s3_w1_conj c] at h
  have hF : ∀ a c : K, ((φ.symm (uElt 0 (a * c) (a ^ 2 * c) c) : L) : G) ∈ X := by
    intro a c
    have h := hP _ (sixH_s3_memP_a a) _ (hT c)
    rwa [sixH_s3_conj_one_G] at h
  intro g hg
  obtain ⟨V, hVg, rfl⟩ := sixH_s_exists_lift hg
  obtain ⟨b, c, d, rfl⟩ := hVg
  have h1 : ((φ.symm (uElt 0 b (b ^ 2) 1) : L) : G) ∈ X := by
    have h := hF b 1
    simpa only [mul_one] using h
  rw [sixH_s3_split_A1 b c d, sixH_s_lift_mul, sixH_s_lift_mul]
  exact mul_mem (mul_mem h1 (hU (sixH_s3_memU_two (c - b ^ 2)))) (hT (d - 1))

theorem sixH_s3_invariant_A (i : Axis) {X : Subgroup G} (hXA : X ≤ A φ i.swap)
    (hP : ∀ p ∈ P φ, ∀ x ∈ X, p * x * p⁻¹ ∈ X)
    (hw : ∀ x ∈ X, w φ i.swap * x * (w φ i.swap)⁻¹ ∈ X) (hU : U φ i ≤ X) :
    X = A φ i.swap := by
  cases i
  · exact sixH_s3_of_one hXA hP hw hU
  · exact sixH_s3_of_two hXA hP hw hU

end Explicit

section Bridge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem scsetting_sq_M_mem_U
    (hSel : CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootSelector fun D _ => CFSG.Blueprint.Catalog D)
    (h : SCSetting L K n φ t i) : ∀ x ∈ Mc φ t i, x * x ∈ U φ i :=
  LocalSixE.sq_M_mem_U hSel h.fc i h.ne_bot h.eq_bot h.kproper h.nonabelian

end Bridge

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
