module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
import TauCeti.GroupTheory.Coxeter.Matrix
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType.ZS

section Comap

variable {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {E : Set X} {F : Set Y}

private lemma mem_symm (hEF : ∀ x, x ∈ E ↔ φ x ∈ F) {y : Y} (hy : y ∈ F) :
    φ.symm y ∈ E :=
  (hEF _).mpr (by simpa using hy)

private lemma orderOf_symm_mul (x y : Y) :
    orderOf (φ.symm x * φ.symm y) = orderOf (x * y) := by
  rw [← map_mul, MulEquiv.orderOf_eq]

private lemma orderOf_symm_mul4 (a b c d : Y) :
    orderOf (φ.symm a * φ.symm b * φ.symm c * φ.symm d) =
      orderOf (a * b * c * d) := by
  have h : φ.symm (a * b * c * d) =
      φ.symm a * φ.symm b * φ.symm c * φ.symm d := by
    simp only [map_mul]
  rw [← h, MulEquiv.orderOf_eq]

private lemma symm_list_prod {k : ℕ} (d : Fin k → Y) :
    (List.ofFn (φ.symm ∘ d)).prod = φ.symm (List.ofFn d).prod := by
  rw [← List.map_ofFn, List.prod_hom]

theorem mem_iff_of_image_eq (h : φ '' E = F) (x : X) : x ∈ E ↔ φ x ∈ F := by
  rw [← h]
  exact φ.injective.mem_set_image.symm

theorem image_eq_of_forall_mem_iff (h : ∀ x, x ∈ E ↔ φ x ∈ F) : φ '' E = F := by
  ext y
  refine ⟨?_, fun hy => ⟨φ.symm y, mem_symm φ h hy, φ.apply_symm_apply y⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact (h x).mp hx

theorem CoxeterConfig.comap (hEF : ∀ x, x ∈ E ↔ φ x ∈ F) {ι : Type*} {M : CoxeterMatrix ι}
    {d : ι → Y} (h : CoxeterConfig F M d) : CoxeterConfig E M (φ.symm ∘ d) := by
  obtain ⟨hdE, hinj, hord, hcomm⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact mem_symm φ hEF (hdE i)
  · exact φ.symm.injective.comp hinj
  · intro i j hij
    simp only [Function.comp_apply]
    rw [orderOf_symm_mul φ (d i) (d j), hord i j hij]
  · intro i j hij hM
    exact (hcomm i j hij hM).map φ.symm

theorem ScalarFrame.comap (hEF : ∀ x, x ∈ E ↔ φ x ∈ F) {k : ℕ} {d : Fin k → Y} {e : Y}
    (h : ScalarFrame F d e) : ScalarFrame E (φ.symm ∘ d) (φ.symm e) := by
  obtain ⟨hdE, hinj, hcomm, heE, hne, hprod⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact mem_symm φ hEF (hdE i)
  · exact φ.symm.injective.comp hinj
  · exact fun i j hij => (hcomm hij).map φ.symm
  · exact mem_symm φ hEF heE
  · intro i h
    exact hne i (φ.symm.injective h)
  · rw [symm_list_prod φ d]
    exact hprod.map φ.symm

theorem AffineTriangle.comap (hEF : ∀ x, x ∈ E ↔ φ x ∈ F) {a b c : Y}
    (h : AffineTriangle F a b c) : AffineTriangle E (φ.symm a) (φ.symm b) (φ.symm c) := by
  obtain ⟨ha, hb, hc, hab, hac, hbc, hcab⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_symm φ hEF ha
  · exact mem_symm φ hEF hb
  · exact mem_symm φ hEF hc
  · rw [orderOf_symm_mul φ a b, hab]
  · rw [orderOf_symm_mul φ a c, hac]
  · rw [orderOf_symm_mul φ b c, hbc]
  · rw [orderOf_symm_mul4 φ c a c b, hcab]

theorem UnitaryFourConfig.comap (hEF : ∀ x, x ∈ E ↔ φ x ∈ F) {a b c d : Y}
    (h : UnitaryFourConfig F a b c d) :
    UnitaryFourConfig E (φ.symm a) (φ.symm b) (φ.symm c) (φ.symm d) := by
  obtain ⟨ha, hb, hc, hd, hab, hac, had, hbc, hcd, hbd, hcab, hcad, hlast⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_symm φ hEF ha
  · exact mem_symm φ hEF hb
  · exact mem_symm φ hEF hc
  · exact mem_symm φ hEF hd
  · rw [orderOf_symm_mul φ a b, hab]
  · rw [orderOf_symm_mul φ a c, hac]
  · rw [orderOf_symm_mul φ a d, had]
  · rw [orderOf_symm_mul φ b c, hbc]
  · rw [orderOf_symm_mul φ c d, hcd]
  · rw [orderOf_symm_mul φ b d, hbd]
  · rw [orderOf_symm_mul4 φ c a c b, hcab]
  · rw [orderOf_symm_mul4 φ c a c d, hcad]
  · rcases hlast with hlast | heq
    · left
      have hprod : φ.symm (b * a * b * (d * c * d)) =
          φ.symm b * φ.symm a * φ.symm b * (φ.symm d * φ.symm c * φ.symm d) := by
        simp only [map_mul]
      rw [← hprod, MulEquiv.orderOf_eq, hlast]
    · right
      have heq' := congrArg φ.symm heq
      simpa only [map_mul] using heq'

theorem closure_range_symm_comp_eq_top {ι : Type*} {d : ι → Y}
    (h : Subgroup.closure (Set.range d) = ⊤) :
    Subgroup.closure (Set.range (φ.symm ∘ d)) = ⊤ := by
  rw [Set.range_comp, ← MulEquiv.coe_toMonoidHom φ.symm,
    ← MonoidHom.map_closure φ.symm.toMonoidHom, h]
  exact Subgroup.map_top_of_surjective φ.symm.toMonoidHom φ.symm.surjective

end Comap

private lemma swap_isSwap {n : ℕ} (i : Fin n) :
    (Equiv.swap i.castSucc i.succ).IsSwap :=
  Equiv.Perm.swap_isSwap_iff.mpr (Fin.castSucc_lt_succ (i := i)).ne

private lemma isThreeCycle_swap_mul_swap_adj {α : Type*} [Fintype α] [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (Equiv.swap a b * Equiv.swap b c).IsThreeCycle := by
  have h3 : (Equiv.swap b a * Equiv.swap b c).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab.symm hbc hac
  rwa [Equiv.swap_comm b a] at h3

private lemma orderOf_swap_mul_swap_of_val_succ {n : ℕ} {i j : Fin n}
    (h : (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)) :
    orderOf (Equiv.swap i.castSucc i.succ * Equiv.swap j.castSucc j.succ) = 3 := by
  rcases h with h | h
  · have hji : j.succ = i.castSucc := Fin.ext (by simpa using h)
    have h3 := isThreeCycle_swap_mul_swap_adj (a := j.castSucc) (b := j.succ)
      (c := i.succ) (Fin.castSucc_lt_succ (i := j)).ne
      (by rw [hji]; exact (Fin.castSucc_lt_succ (i := i)).ne) (by
        intro hh
        have hv : (j : ℕ) = (i : ℕ) + 1 := by simpa using congrArg Fin.val hh
        omega)
    have hprod : Equiv.swap i.castSucc i.succ * Equiv.swap j.castSucc j.succ =
        (Equiv.swap j.castSucc j.succ * Equiv.swap j.succ i.succ)⁻¹ := by
      rw [hji, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
    rw [hprod, orderOf_inv, h3.orderOf]
  · have hij : i.succ = j.castSucc := Fin.ext (by simpa using h)
    have h3 := isThreeCycle_swap_mul_swap_adj (a := i.castSucc) (b := i.succ)
      (c := j.succ) (Fin.castSucc_lt_succ (i := i)).ne
      (by rw [hij]; exact (Fin.castSucc_lt_succ (i := j)).ne) (by
        intro hh
        have hv : (i : ℕ) = (j : ℕ) + 1 := by simpa using congrArg Fin.val hh
        omega)
    rw [← hij]
    exact h3.orderOf

private lemma commute_swap_of_coxeterA_eq_two {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (hM : (CoxeterMatrix.A n).M i j = 2) :
    Commute (Equiv.swap i.castSucc i.succ) (Equiv.swap j.castSucc j.succ) := by
  have hnot : ¬ ((j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)) := by
    intro hc
    rw [TauCeti.coxeterMatrixA_apply, if_neg hij, if_pos hc] at hM
    exact absurd hM (by norm_num)
  push Not at hnot
  have hval : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hab : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  have hcd : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ (i := j)).ne
  have hac : i.castSucc ≠ j.castSucc := fun h => hij (Fin.castSucc_injective n h)
  have had : i.castSucc ≠ j.succ := by
    intro h
    have hv : (i : ℕ) = (j : ℕ) + 1 := by simpa using congrArg Fin.val h
    exact hnot.1 hv.symm
  have hbc : i.succ ≠ j.castSucc := by
    intro h
    have hv : (i : ℕ) + 1 = (j : ℕ) := by simpa using congrArg Fin.val h
    exact hnot.2 hv
  have hbd : i.succ ≠ j.succ := by
    intro h
    have hv : (i : ℕ) = (j : ℕ) := by simpa using congrArg Fin.val h
    exact hval hv
  exact (Equiv.Perm.disjoint_swap_swap (x := i.castSucc) (y := i.succ)
    (z := j.castSucc) (t := j.succ) (by
      simp [List.nodup_cons, hab, hac, had, hbc, hbd, hcd])).commute

private lemma swap_castSucc_succ_injective (n : ℕ) :
    Function.Injective fun k : Fin n => Equiv.swap k.castSucc k.succ := by
  intro i j hij
  have h := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ i.castSucc) hij
  simp only [Equiv.swap_apply_left] at h
  have hne : Equiv.swap j.castSucc j.succ i.castSucc ≠ i.castSucc := by
    rw [← h]
    exact ((Fin.castSucc_lt_succ (i := i)).ne).symm
  rcases Equiv.eq_or_eq_of_swap_apply_ne_self hne with h1 | h1
  · exact Fin.castSucc_injective n h1
  · exfalso
    have hv1 : (i : ℕ) = (j : ℕ) + 1 := by simpa using congrArg Fin.val h1
    have h2 : i.succ = j.castSucc := by
      rw [h, h1, Equiv.swap_apply_right]
    have hv2 : (i : ℕ) + 1 = (j : ℕ) := by simpa using congrArg Fin.val h2
    omega

theorem coxeterConfig_swap (l : ℕ) :
    CoxeterConfig {σ : Equiv.Perm (Fin (l + 1)) | σ.IsSwap} (CoxeterMatrix.A l)
      (fun k : Fin l => Equiv.swap k.castSucc k.succ) := by
  refine ⟨?_, swap_castSucc_succ_injective l, ?_, ?_⟩
  · intro k
    exact swap_isSwap k
  · intro i j hM
    rw [TauCeti.coxeterMatrixA_apply] at hM
    by_cases hij : i = j
    · rw [if_pos hij] at hM
      exact absurd hM (by norm_num)
    · rw [if_neg hij] at hM
      by_cases hadj : (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)
      · exact orderOf_swap_mul_swap_of_val_succ hadj
      · rw [if_neg hadj] at hM
        exact absurd hM (by norm_num)
  · intro i j hij hM
    exact commute_swap_of_coxeterA_eq_two hij hM

theorem closure_range_swap_eq_top (l : ℕ) :
    Subgroup.closure (Set.range fun k : Fin l => Equiv.swap k.castSucc k.succ) = ⊤ :=
  Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ l)

end CFSG.StandardType.ZS
