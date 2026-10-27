module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
import CFSG.Fischer.Classification.PartIII.U.SixForms
import CFSG.LocalAnalysis.StandardType.ZS.DThreeRigidLift
import CFSG.LocalAnalysis.StandardType.ZS.DThreeRigidGram
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryGen
import CFSG.LocalAnalysis.StandardType.ZS.DThreeRigidSixLift
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

local instance (priority := high) zx6_zmodThreeAddCommGroup : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [Module.Finite (ZMod 3) U]
  {A : Subgroup (U ≃ₗ[ZMod 3] U)}

private def zx6Vec (n : ℕ) : Fin (n + 1) → Fin (n + 1) → ZMod 3 :=
  Fin.cons (Pi.single 0 1 + Pi.single 1 1 + Pi.single (Fin.last n) 1)
    fun i : Fin n => Pi.single i.castSucc 1

private lemma zx6Vec_zero (n : ℕ) :
    zx6Vec n 0 = Pi.single 0 1 + Pi.single 1 1 + Pi.single (Fin.last n) 1 :=
  Fin.cons_zero _ _

private lemma zx6Vec_succ {n : ℕ} (i : Fin n) : zx6Vec n i.succ = Pi.single i.castSucc 1 :=
  Fin.cons_succ _ _ _

private lemma zx6_fin_ne {n : ℕ} (hn : 2 ≤ n) :
    (0 : Fin (n + 1)) ≠ 1 ∧ (0 : Fin (n + 1)) ≠ Fin.last n ∧ (1 : Fin (n + 1)) ≠ Fin.last n := by
  have hv : (1 : Fin (n + 1)).val = 1 := by
    simp
    omega
  refine ⟨Fin.ne_of_val_ne ?_, Fin.ne_of_val_ne ?_, Fin.ne_of_val_ne ?_⟩ <;>
    simp only [Fin.val_zero, Fin.val_last, hv] <;> omega

private lemma zx6Vec_succ_succ {n : ℕ} (i j : Fin n) :
    diagF3 (n + 1) 2 (zx6Vec n i.succ) (zx6Vec n j.succ) = if i = j then 1 else 0 := by
  rw [zx6Vec_succ, zx6Vec_succ, diagF3_single_castSucc]

private lemma zx6Vec_norm {n : ℕ} (hn : 5 ≤ n) (i : Fin (n + 1)) :
    diagF3 (n + 1) 2 (zx6Vec n i) (zx6Vec n i) = 1 := by
  cases i using Fin.cases with
  | zero =>
    obtain ⟨h01, h0l, h1l⟩ := zx6_fin_ne (n := n) (by omega)
    simp only [zx6Vec_zero, map_add, LinearMap.add_apply, LocalU.diagF3_single, if_neg h01,
      if_neg h01.symm, if_neg h0l, if_neg h0l.symm, if_neg h1l, if_neg h1l.symm, if_pos,
      diagF3Entry_two_of_ne_last h0l, diagF3Entry_two_of_ne_last h1l, diagF3Entry_two_last]
    decide
  | succ j => rw [zx6Vec_succ_succ, if_pos rfl]

private lemma zx6Vec_last {n : ℕ} (hn : 2 ≤ n) (i : Fin (n + 1)) :
    zx6Vec n i (Fin.last n) = if i = 0 then 1 else 0 := by
  obtain ⟨-, h0l, h1l⟩ := zx6_fin_ne hn
  cases i using Fin.cases with
  | zero =>
    rw [zx6Vec_zero, Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne h0l.symm,
      Pi.single_eq_of_ne h1l.symm, Pi.single_eq_same, if_pos rfl, zero_add, zero_add]
  | succ j =>
    rw [zx6Vec_succ, Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne',
      if_neg (Fin.succ_ne_zero j)]

private lemma zx6_ne_of_apply {n : ℕ} {x z : Fin (n + 1) → ZMod 3} {k : Fin (n + 1)}
    (hx : x k ≠ 0) (hz : z k = 0) : (x ≠ z ∧ x ≠ -z) ∧ z ≠ x ∧ z ≠ -x := by
  refine ⟨⟨fun h => hx ?_, fun h => hx ?_⟩, fun h => hx ?_, fun h => hx ?_⟩
  · rw [h, hz]
  · rw [h, Pi.neg_apply, hz, neg_zero]
  · rw [← h, hz]
  · have h' := congrFun h k
    rw [Pi.neg_apply, hz] at h'
    exact neg_eq_zero.1 h'.symm

private lemma zx6Vec_ne {n : ℕ} (hn : 5 ≤ n) (i j : Fin (n + 1)) (hij : i ≠ j) :
    zx6Vec n j ≠ zx6Vec n i ∧ zx6Vec n j ≠ -zx6Vec n i := by
  have hl := zx6Vec_last (n := n) (by omega)
  have h0 : zx6Vec n 0 (Fin.last n) ≠ 0 := by
    rw [hl, if_pos rfl]
    exact one_ne_zero
  cases j using Fin.cases with
  | zero => exact (zx6_ne_of_apply (z := zx6Vec n i) h0 (by rw [hl, if_neg hij])).1
  | succ b =>
    cases i using Fin.cases with
    | zero =>
      exact (zx6_ne_of_apply (z := zx6Vec n b.succ) h0
        (by rw [hl, if_neg (Fin.succ_ne_zero b)])).2
    | succ a =>
      have hab : b.castSucc ≠ a.castSucc := fun h =>
        hij (congrArg Fin.succ (Fin.castSucc_injective n h)).symm
      refine (zx6_ne_of_apply (k := b.castSucc) ?_ ?_).1
      · rw [zx6Vec_succ, Pi.single_eq_same]
        exact one_ne_zero
      · rw [zx6Vec_succ, Pi.single_eq_of_ne hab]

private lemma zx6Vec_forest {n : ℕ} (i i' j : Fin (n + 1)) (hi : i < j) (hi' : i' < j)
    (hij : diagF3 (n + 1) 2 (zx6Vec n i) (zx6Vec n j) ≠ 0)
    (hi'j : diagF3 (n + 1) 2 (zx6Vec n i') (zx6Vec n j) ≠ 0) : i = i' := by
  have key : ∀ k, k < j → diagF3 (n + 1) 2 (zx6Vec n k) (zx6Vec n j) ≠ 0 → k = 0 := by
    intro k hk hkj
    cases j using Fin.cases with
    | zero => exact absurd hk (Fin.not_lt_zero k)
    | succ b =>
      cases k using Fin.cases with
      | zero => rfl
      | succ a =>
        rw [zx6Vec_succ_succ, if_neg (Fin.succ_lt_succ_iff.1 hk).ne] at hkj
        exact absurd rfl hkj
  exact (key i hi hij).trans (key i' hi' hi'j).symm

private lemma zx6Vec_span {n : ℕ} (hn : 5 ≤ n) :
    Submodule.span (ZMod 3) (Set.range (zx6Vec n)) = ⊤ := by
  set S := Submodule.span (ZMod 3) (Set.range (zx6Vec n))
  have hmem : ∀ i, zx6Vec n i ∈ S := fun i => Submodule.subset_span (Set.mem_range_self i)
  have hcast : ∀ i : Fin n, (Pi.single i.castSucc 1 : Fin (n + 1) → ZMod 3) ∈ S := fun i => by
    rw [← zx6Vec_succ]
    exact hmem i.succ
  have h0 := hcast ⟨0, by omega⟩
  have h1 := hcast ⟨1, by omega⟩
  have e0 : Fin.castSucc (⟨0, by omega⟩ : Fin n) = 0 := Fin.ext (by simp)
  have e1 : Fin.castSucc (⟨1, by omega⟩ : Fin n) = 1 :=
    Fin.ext (by simp [Nat.mod_eq_of_lt (by omega : 1 < n + 1)])
  rw [e0] at h0
  rw [e1] at h1
  have hlast : (Pi.single (Fin.last n) 1 : Fin (n + 1) → ZMod 3) ∈ S := by
    have heq : zx6Vec n 0 - Pi.single 0 1 - Pi.single 1 1 =
        (Pi.single (Fin.last n) 1 : Fin (n + 1) → ZMod 3) := by
      rw [zx6Vec_zero]
      abel
    rw [← heq]
    exact S.sub_mem (S.sub_mem (hmem 0) h0) h1
  rw [eq_top_iff, ← (Pi.basisFun (ZMod 3) (Fin (n + 1))).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rw [Pi.basisFun_apply]
  cases k using Fin.lastCases with
  | last => exact hlast
  | cast i => exact hcast i

private lemma zx6_mem_of_last_eq_zero (hn : 3 ≤ Module.finrank (ZMod 3) U)
    (hirr : AbsIrred 3 A) {n : ℕ} (hn5 : 5 ≤ n)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 (n + 1) 2))
    (hφ : ∀ g, g ∈ reflImage 3 A ↔ φ g ∈ D3 (diagF3 (n + 1) 2))
    {B : LinearMap.BilinForm (ZMod 3) U} (hBs : ∀ x y, B x y = B y x)
    (hB : ∀ t ∈ A, IsRefl 3 t → ∃ u, B u u = 1 ∧ ∀ x, t x = x + B x u • u)
    {u : Fin (n + 1) → U}
    (hgram : ∀ i j, B (u i) (u j) = diagF3 (n + 1) 2 (zx6Vec n i) (zx6Vec n j))
    (t : Fin (n + 1) → ↥A)
    (ht : ∀ i, φ (QuotientGroup.mk (t i)) = reflBar (diagF3 (n + 1) 2) (zx6Vec n i))
    (htu : ∀ i x, (t i : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i)
    {w : Fin (n + 1) → ZMod 3} (hw : diagF3 (n + 1) 2 w w = 1) (hwl : w (Fin.last n) = 0)
    {s : ↥A} (hs : IsRefl 3 (s : U ≃ₗ[ZMod 3] U))
    (hsw : φ (QuotientGroup.mk s) = reflBar (diagF3 (n + 1) 2) w) {x : U}
    (hx : x ∈ Submodule.span (ZMod 3) (Set.range u)) :
    (s : U ≃ₗ[ZMod 3] U) x ∈ Submodule.span (ZMod 3) (Set.range u) := by
  obtain ⟨a, ha, hsa⟩ := hB s s.2 hs
  have haX : a ∈ Submodule.span (ZMod 3) (Set.range fun i : Fin n => u i.succ) :=
    mem_span_of_last_eq_zero hn hirr (by omega) φ hφ hBs (u := fun i : Fin n => u i.succ)
      (fun i j => by rw [hgram]; exact zx6Vec_succ_succ i j) (fun i => t i.succ)
      (fun i => by simpa only [zx6Vec_succ] using ht i.succ) (fun i => htu i.succ) hw hwl hs
      hsw ha hsa
  have haX' : a ∈ Submodule.span (ZMod 3) (Set.range u) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, rfl⟩) haX
  rw [hsa x]
  exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ haX')

theorem exists_isometry_of_mulEquiv_R3_diagF3_two (hn : 3 ≤ Module.finrank (ZMod 3) U)
    (hirr : AbsIrred 3 A) {m : ℕ} (hm : 6 ≤ m) (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 m 2))
    (hφ : ∀ g, g ∈ reflImage 3 A ↔ φ g ∈ D3 (diagF3 m 2)) {B : LinearMap.BilinForm (ZMod 3) U}
    (hBs : ∀ x y, B x y = B y x) (hBnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hB : ∀ t ∈ A, IsRefl 3 t → ∃ u, B u u = 1 ∧ ∀ x, t x = x + B x u • u) :
    ∃ L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U, ∀ x y, B (L x) (L y) = diagF3 m 2 x y := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn5 : 5 ≤ n := by omega
  obtain ⟨u, hgram, hlift⟩ := exists_roots_of_forest hn hirr (m := n + 1) (by omega)
    (isF3Form_diagF3 (by decide)) φ hφ hBs hB (zx6Vec n) (zx6Vec_norm hn5) (zx6Vec_ne hn5)
    zx6Vec_forest
  choose t _ hφt htu using hlift
  let X : Submodule (ZMod 3) U := Submodule.span (ZMod 3) (Set.range u)
  have hXne : X ≠ ⊥ := by
    intro hbot
    have hmem : u 0 ∈ X := Submodule.subset_span (Set.mem_range_self 0)
    rw [hbot, Submodule.mem_bot] at hmem
    have h1 := hgram 0 0
    have hzero : B (0 : U) 0 = 0 := by simp
    rw [zx6Vec_norm hn5, hmem, hzero] at h1
    exact zero_ne_one h1
  have hqtop : Subgroup.closure ((QuotientGroup.mk : ↥A → ↥A ⧸ Subgroup.center ↥A) ''
      {s : ↥A | ∀ x ∈ X, (s : U ≃ₗ[ZMod 3] U) x ∈ X}) = ⊤ := by
    refine Subgroup.map_injective (f := φ.toMonoidHom) φ.injective ?_
    rw [Subgroup.map_top_of_surjective _ φ.surjective, eq_top_iff,
      ← closure_reflBar_last_eq_zero_insert_eq_top hn5, Subgroup.closure_le]
    rintro q (rfl | ⟨w, hw, hwl, rfl⟩)
    · refine Subgroup.mem_map.2 ⟨QuotientGroup.mk (t 0),
        Subgroup.subset_closure ⟨t 0, fun x hx => ?_, rfl⟩, ?_⟩
      · rw [htu 0 x]
        exact X.add_mem hx (X.smul_mem _ (Submodule.subset_span (Set.mem_range_self 0)))
      · exact (hφt 0).trans (by rw [zx6Vec_zero])
    · obtain ⟨s, hs, hsq⟩ := (hφ (φ.symm (reflBar (diagF3 (n + 1) 2) w))).2
        (by rw [MulEquiv.apply_symm_apply]; exact reflBar_mem_D3 hw)
      have hsw : φ (QuotientGroup.mk s) = reflBar (diagF3 (n + 1) 2) w := by
        rw [hsq, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_map.2 ⟨QuotientGroup.mk s, Subgroup.subset_closure ⟨s, fun x hx =>
        zx6_mem_of_last_eq_zero hn hirr hn5 φ hφ hBs hB hgram t hφt htu hw hwl hs hsw hx, rfl⟩,
        hsw⟩
  have hX : X = ⊤ := AbsIrred.eq_top_of_closure_mk_image_eq_top hirr hXne (fun s hs => hs) hqtop
  obtain ⟨L, -, hL⟩ := exists_linearEquiv_of_gram_eq (isF3Form_diagF3 (by decide)).nondeg hBnd
    (zx6Vec_span hn5) hX hgram
  exact ⟨L, hL⟩

end CFSG.StandardType.ZS
