module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.RankThree.PartTwo.Sec3.MinimalCommutatorTwoGroup
public import Certificates.Certificate152301
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.SectionRank.OpsSpec

open CFSG.Blueprint CFSG.SectionRank.Native LocalWitness

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem conjSeven_spec {A T : M} (hA : Sp.WF A) (hT : Sp.WF T) (i : ℕ) :
    Sp.WF (O.conjSeven A T i) ∧
      Sp.toMat (O.conjSeven A T i) = Sp.toMat T ^ i * Sp.toMat A * Sp.toMat T ^ (7 - i) := by
  obtain ⟨w1, e1⟩ := Sp.pow_spec hT i
  obtain ⟨w2, e2⟩ := Sp.pow_spec hT (7 - i)
  refine ⟨Sp.mul_wf (Sp.mul_wf w1 hA) w2, ?_⟩
  rw [Ops.conjSeven, Sp.toMat_mul (Sp.mul_wf w1 hA) w2, Sp.toMat_mul w1 hA, e1, e2]

theorem frob_of_check [Inhabited M] (D : FrobData) (h : O.frobCheck D = true) :
    ∃ a t : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      a ^ 2 = 1 ∧ a ≠ 1 ∧ t ^ 7 = 1 ∧ a * (t * a * t⁻¹) = t * a * t⁻¹ * a ∧
      a * (t ^ 2 * a * (t ^ 2)⁻¹) = t ^ 2 * a * (t ^ 2)⁻¹ * a ∧
      t ^ 3 * a * (t ^ 3)⁻¹ = t * a * t⁻¹ * a := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  unfold Ops.frobCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hprog, hra⟩, hrt⟩, hA2⟩, hT7⟩, hc1⟩, hc2⟩, hc3⟩, hne⟩ := h
  set R := O.regsOf D.seedA D.seedB D.nregs D.prog with hR
  have hreg : ∀ r < D.nregs, Sp.WF R[r]! ∧ Sp.toMat R[r]! ∈ S := fun r hr =>
    Sp.regsOf_ok hprog hr
  obtain ⟨wA, mA⟩ := hreg _ hra
  obtain ⟨wT, mT⟩ := hreg _ hrt
  set A := R[D.ra]! with hAdef
  set T := R[D.rt]! with hTdef
  have hA2M : Sp.toMat A ^ 2 = 1 := by
    have := Sp.toMat_eq (Sp.mul_wf wA wA) Sp.one_wf hA2
    rwa [Sp.toMat_mul wA wA, Sp.toMat_one, ← pow_two] at this
  have hT7M : Sp.toMat T ^ 7 = 1 := Sp.pow_eq_one_of_check wT hT7
  let a : Sˣ := unitOf S mA (by norm_num : (2 : ℕ) ≠ 0) hA2M
  let t : Sˣ := unitOf S mT (by norm_num : (7 : ℕ) ≠ 0) hT7M
  have fa : valHom S a = Sp.toMat A := valHom_unitOf S mA _ hA2M
  have ft : valHom S t = Sp.toMat T := valHom_unitOf S mT _ hT7M
  have ht7 : t ^ 7 = 1 := unitOf_pow S mT _ hT7M
  have hinv : ∀ i ≤ 7, (t ^ i)⁻¹ = t ^ (7 - i) := fun i hi =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_add, Nat.add_sub_cancel' hi, ht7])
  have fc : ∀ i ≤ 7, valHom S (t ^ i * a * (t ^ i)⁻¹) = Sp.toMat (O.conjSeven A T i) := by
    intro i hi
    rw [hinv i hi, map_mul, map_mul, map_pow, map_pow, fa, ft, (Sp.conjSeven_spec wA wT i).2]
  have hcomm : ∀ {X Y : M}, Sp.WF X → Sp.WF Y → O.commOK X Y = true →
      Sp.toMat X * Sp.toMat Y = Sp.toMat Y * Sp.toMat X := by
    intro X Y hX hY hXY
    have := Sp.toMat_eq (Sp.mul_wf hX hY) (Sp.mul_wf hY hX) hXY
    rwa [Sp.toMat_mul hX hY, Sp.toMat_mul hY hX] at this
  obtain ⟨w1, -⟩ := Sp.conjSeven_spec wA wT 1
  obtain ⟨w2, -⟩ := Sp.conjSeven_spec wA wT 2
  obtain ⟨w3, -⟩ := Sp.conjSeven_spec wA wT 3
  have e1 : t * a * t⁻¹ = t ^ 1 * a * (t ^ 1)⁻¹ := by rw [pow_one]
  refine ⟨a, t, unitOf_pow S mA _ hA2M, fun h1 => ?_, ht7, ?_, ?_, ?_⟩
  · have hM : Sp.toMat A = 1 := by rw [← fa, h1, map_one]
    apply Sp.toVec_ne hne
    rw [Sp.toVec_vmul (Sp.unit_wf _) wA, hM, Matrix.vecMul_one]
  · apply valHom_injective S
    rw [e1, map_mul (valHom S) a, map_mul (valHom S) _ a, fc 1 (by norm_num), fa]
    exact hcomm wA w1 hc1
  · apply valHom_injective S
    rw [map_mul (valHom S) a, map_mul (valHom S) _ a, fc 2 (by norm_num), fa]
    exact hcomm wA w2 hc2
  · apply valHom_injective S
    rw [e1, map_mul (valHom S) _ a, fc 3 (by norm_num), fc 1 (by norm_num), fa]
    have := Sp.toMat_eq w3 (Sp.mul_wf w1 wA) hc3
    rwa [Sp.toMat_mul w1 wA] at this

end CFSG.SectionRank.OpsSpec

namespace CFSG.RankThree.PartTwo.Sec15.Sylow1523Theta

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint

theorem frobPair_of_rels {S : Type*} [Group S] [Finite S] {a t : S} (ha2 : a ^ 2 = 1)
    (ha1 : a ≠ 1) (h1 : a * (t * a * t⁻¹) = t * a * t⁻¹ * a)
    (h2 : a * (t ^ 2 * a * (t ^ 2)⁻¹) = t ^ 2 * a * (t ^ 2)⁻¹ * a)
    (h3 : t ^ 3 * a * (t ^ 3)⁻¹ = t * a * t⁻¹ * a) :
    ∃ Z : Subgroup S, IsPGroup 2 Z ∧ (∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) ∧ Z ≠ ⊥ ∧
      t ∈ Subgroup.normalizer (Z : Set S) ∧ ∀ z ∈ Z, t * z * t⁻¹ = z → z = 1 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → S, ∀ i, c i = t ^ i * a * (t ^ i)⁻¹ := ⟨_, fun _ => rfl⟩
  have hc0 : c 0 = a := by rw [hc]; group
  have hκ : ∀ i, t * c i * t⁻¹ = c (i + 1) := fun i => by rw [hc, hc]; group
  have hκ3 : ∀ i, t ^ 3 * c i * (t ^ 3)⁻¹ = c (i + 3) := fun i => by rw [hc, hc]; group
  have hκmul : ∀ x y : S, t * (x * y) * t⁻¹ = t * x * t⁻¹ * (t * y * t⁻¹) := fun x y => by
    group
  have hsq : ∀ i, c i ^ 2 = 1 := fun i => by
    rw [hc, conj_pow, ha2, mul_one, mul_inv_cancel]
  have hshift : ∀ i j k, c i * c j = c j * c i → c (i + k) * c (j + k) = c (j + k) * c (i + k) := by
    intro i j k hij
    induction k with
    | zero => simpa using hij
    | succ k ih =>
      have e : t * (c (i + k) * c (j + k)) * t⁻¹ = t * (c (j + k) * c (i + k)) * t⁻¹ := by
        rw [ih]
      rw [hκmul, hκmul, hκ, hκ] at e
      rw [← Nat.add_assoc, ← Nat.add_assoc]
      exact e
  have h01 : c 0 * c 1 = c 1 * c 0 := by
    rw [hc0, hc 1, pow_one]
    exact h1
  have h02 : c 0 * c 2 = c 2 * c 0 := by
    rw [hc0, hc 2]
    exact h2
  have h12 : c 1 * c 2 = c 2 * c 1 := by simpa using hshift 0 1 1 h01
  have hthree : ∀ i, c (i + 3) = c (i + 1) * c i := by
    intro i
    induction i with
    | zero =>
      rw [hc0, hc (0 + 3), hc (0 + 1), zero_add, zero_add, pow_one]
      exact h3
    | succ i ih =>
      have e : t * c (i + 3) * t⁻¹ = t * (c (i + 1) * c i) * t⁻¹ := by rw [ih]
      rw [hκmul, hκ, hκ, hκ] at e
      rw [show i + 1 + 3 = i + 3 + 1 by omega]
      exact e
  set Z : Subgroup S := Subgroup.closure ({c 0, c 1, c 2} : Set S) with hZ
  have hZcomm : IsMulCommutative Z := by
    apply Subgroup.isMulCommutative_closure
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | exact h01 | exact h01.symm | exact h02 | exact h02.symm | exact h12 | exact h12.symm
  have hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hZcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hgen : ∀ i, i ≤ 2 → c i ∈ Z := by
    intro i hi
    apply Subgroup.subset_closure
    interval_cases i <;> simp
  have hconj : ∀ x ∈ Z, t * x * t⁻¹ ∈ Z := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rw [hκ]
        exact hgen 1 (by norm_num)
      · rw [hκ]
        exact hgen 2 (by norm_num)
      · rw [hκ, hthree 0]
        exact Z.mul_mem (hgen 1 (by norm_num)) (hgen 0 (by norm_num))
    | one => simp
    | mul x y _ _ hx hy =>
      rw [hκmul]
      exact Z.mul_mem hx hy
    | inv x _ hx =>
      rw [show t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group]
      exact Z.inv_mem hx
  have hP : ∀ z ∈ Z, t ^ 3 * z * (t ^ 3)⁻¹ = t * z * t⁻¹ * z := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> rw [hκ3, hκ, hthree]
    | one => group
    | mul x y hx hy ihx ihy =>
      rw [show t ^ 3 * (x * y) * (t ^ 3)⁻¹ = t ^ 3 * x * (t ^ 3)⁻¹ * (t ^ 3 * y * (t ^ 3)⁻¹) by
        group, hκmul, ihx, ihy]
      have hxy : x * (t * y * t⁻¹) = t * y * t⁻¹ * x := hZab x hx _ (hconj y hy)
      calc t * x * t⁻¹ * x * (t * y * t⁻¹ * y)
          = t * x * t⁻¹ * (x * (t * y * t⁻¹)) * y := by group
        _ = t * x * t⁻¹ * (t * y * t⁻¹ * x) * y := by rw [hxy]
        _ = t * x * t⁻¹ * (t * y * t⁻¹) * (x * y) := by group
    | inv x hx ih =>
      rw [show t ^ 3 * x⁻¹ * (t ^ 3)⁻¹ = (t ^ 3 * x * (t ^ 3)⁻¹)⁻¹ by group,
        show t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group, ih]
      have hxx : x * (t * x * t⁻¹) = t * x * t⁻¹ * x := hZab x hx _ (hconj x hx)
      rw [← hxx]
      group
  refine ⟨Z, fun g => ⟨1, Subtype.ext ?_⟩, hZab, ?_, ?_, ?_⟩
  ·
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    have : ∀ x ∈ Z, x ^ 2 = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl <;> exact hsq _
      | one => exact one_pow 2
      | mul x y hx hy ihx ihy =>
        have hxy : Commute x y := hZab x hx y hy
        rw [hxy.mul_pow, ihx, ihy, one_mul]
      | inv x _ ih => rw [inv_pow, ih, inv_one]
    exact this _ g.2
  · intro hbot
    have haZ : a ∈ Z := hc0 ▸ hgen 0 (by norm_num)
    rw [hbot, Subgroup.mem_bot] at haZ
    exact ha1 haZ
  · exact CFSG.RankThree.PartTwo.Sec3.mem_normalizer_of_forall_conj_mem hconj
  · intro z hzZ hz
    have h3z : t ^ 3 * z * (t ^ 3)⁻¹ = z := by
      rw [show t ^ 3 * z * (t ^ 3)⁻¹ = t * (t * (t * z * t⁻¹) * t⁻¹) * t⁻¹ by
        simp only [pow_three, mul_inv_rev, mul_assoc], hz, hz, hz]
    have hzz := hP z hzZ
    rw [h3z, hz] at hzz
    exact mul_left_cancel (a := z) (by rw [mul_one]; exact hzz.symm)

theorem on_frobenius_check :
    (ops3 154).frobCheck onFrobData = true :=
  Certificates.certificate152301

theorem ON_frobenius_pair :
    ∃ Z : Subgroup NativeSporadic.ON, IsPGroup 2 Z ∧ (∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) ∧
      Z ≠ ⊥ ∧ ∃ t : NativeSporadic.ON, t ^ 7 = 1 ∧ t ∈ Subgroup.normalizer (Z : Set _) ∧
        ∀ z ∈ Z, t * z * t⁻¹ = z → z = 1 := by
  obtain ⟨a, t, ha2, ha1, ht7, h1, h2, h3⟩ :=
    (spec3 154).frob_of_check onFrobData on_frobenius_check
  obtain ⟨Z, hZ2, hZab, hZ1, htN, htfix⟩ := frobPair_of_rels (S := NativeSporadic.ON) ha2 ha1 h1 h2 h3
  exact ⟨Z, hZ2, hZab, hZ1, t, ht7, htN, htfix⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow1523Theta
