module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45K22pDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

def commutatorClosure {Γ : Type} [Group Γ] (H : Subgroup Γ) (d : Γ) : Subgroup Γ :=
  Subgroup.closure (Set.range fun y : ↥H => ⁅(y : Γ), d⁆)

section Helpers

variable {Γ : Type} [Group Γ] (H : Subgroup Γ) [H.Normal] (d : Γ)

lemma subtype_commSub_conjNormal_apply (x : ↥H) :
    ((x⁻¹ * (MulAut.conjNormal d : MulAut ↥H) x : ↥H) : Γ) = ⁅(x : Γ)⁻¹, d⁆ := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, commutatorElement_def]
  group

lemma conjugate_mem_closure_commutator (g : Γ) (hgH : ∀ y : ↥H, g * (y : Γ) * g⁻¹ ∈ H)
    (hgd : g * d * g⁻¹ = d) (c : Γ) (hc : c ∈ commutatorClosure H d) :
    g * c * g⁻¹ ∈ commutatorClosure H d := by
  let C : Subgroup Γ := commutatorClosure H d
  change c ∈ C at hc
  change g * c * g⁻¹ ∈ C
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨y, rfl⟩
      refine Subgroup.subset_closure ⟨⟨g * (y : Γ) * g⁻¹, hgH y⟩, ?_⟩
      simpa [hgd] using (conjugate_commutatorElement (y : Γ) d g).symm
  | one => simpa using C.one_mem
  | mul x y _ _ ihx ihy =>
      have heq : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
      rw [heq]
      exact C.mul_mem ihx ihy
  | inv x _ ih =>
      have heq : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [heq]
      exact C.inv_mem ih

lemma d_mem_normalizer_closure_commutator :
    d ∈ Subgroup.normalizer (commutatorClosure H d : Set Γ) := by
  have hH : H.Normal := inferInstance
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact conjugate_mem_closure_commutator H d d (fun y => hH.conj_mem (y : Γ) y.2 d)
      (by group) c hc
  · intro hc
    have h := conjugate_mem_closure_commutator H d d⁻¹
      (fun y => by simpa using hH.conj_mem' (y : Γ) y.2 d)
      (by group) (d * c * d⁻¹) hc
    convert h using 1
    group

lemma zpow_conj_mem_closure_commutator (c : Γ) (hc : c ∈ commutatorClosure H d) (n : ℤ) :
    d ^ n * c * (d ^ n)⁻¹ ∈ commutatorClosure H d :=
  (Subgroup.mem_normalizer_iff.mp (zpow_mem (d_mem_normalizer_closure_commutator H d) n) c).mp hc

lemma commutator_inv_mem_closure_commutator (y : ↥H) :
    ⁅(y : Γ), d⁻¹⁆ ∈ commutatorClosure H d := by
  have hH : H.Normal := inferInstance
  let C : Subgroup Γ := commutatorClosure H d
  change ⁅(y : Γ), d⁻¹⁆ ∈ C
  have hmem : ⁅(y : Γ), d⁆ ∈ C := Subgroup.subset_closure ⟨y, rfl⟩
  have hconj : d⁻¹ * ⁅(y : Γ), d⁆⁻¹ * d ∈ C := by
    simpa using conjugate_mem_closure_commutator H d d⁻¹
      (fun y => by simpa using hH.conj_mem' (y : Γ) y.2 d) (by group) ⁅(y : Γ), d⁆⁻¹
      (C.inv_mem hmem)
  have heq : ⁅(y : Γ), d⁻¹⁆ = d⁻¹ * ⁅(y : Γ), d⁆⁻¹ * d := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [heq]
  exact hconj

lemma commutator_zpow_mem_closure_commutator (y : ↥H) (n : ℤ) :
    ⁅(y : Γ), d ^ n⁆ ∈ commutatorClosure H d := by
  let C : Subgroup Γ := commutatorClosure H d
  change ⁅(y : Γ), d ^ n⁆ ∈ C
  induction n using Int.induction_on with
  | zero => simpa using C.one_mem
  | succ m ih =>
      rw [zpow_add_one d (m : ℤ), commutatorElement_mul_right_eq_mul_conj]
      have hconj : d ^ (m : ℤ) * ⁅(y : Γ), d⁆ * (d ^ (m : ℤ))⁻¹ ∈ C :=
        zpow_conj_mem_closure_commutator H d ⁅(y : Γ), d⁆
          (Subgroup.subset_closure ⟨y, rfl⟩) (m : ℤ)
      have hassoc : ⁅(y : Γ), d ^ (m : ℤ)⁆ * d ^ (m : ℤ) * ⁅(y : Γ), d⁆ *
            (d ^ (m : ℤ))⁻¹ =
          ⁅(y : Γ), d ^ (m : ℤ)⁆ *
            (d ^ (m : ℤ) * ⁅(y : Γ), d⁆ * (d ^ (m : ℤ))⁻¹) := by group
      rw [hassoc]
      exact C.mul_mem ih hconj
  | pred m ih =>
      rw [zpow_sub_one d (-(m : ℤ)), commutatorElement_mul_right_eq_mul_conj]
      have hinv : ⁅(y : Γ), d⁻¹⁆ ∈ C := commutator_inv_mem_closure_commutator H d y
      have hconj : d ^ (-(m : ℤ)) * ⁅(y : Γ), d⁻¹⁆ * (d ^ (-(m : ℤ)))⁻¹ ∈ C :=
        zpow_conj_mem_closure_commutator H d ⁅(y : Γ), d⁻¹⁆ hinv (-(m : ℤ))
      have hassoc : ⁅(y : Γ), d ^ (-(m : ℤ))⁆ * d ^ (-(m : ℤ)) * ⁅(y : Γ), d⁻¹⁆ *
            (d ^ (-(m : ℤ)))⁻¹ =
          ⁅(y : Γ), d ^ (-(m : ℤ))⁆ *
            (d ^ (-(m : ℤ)) * ⁅(y : Γ), d⁻¹⁆ * (d ^ (-(m : ℤ)))⁻¹) := by group
      rw [hassoc]
      exact C.mul_mem ih hconj

lemma closure_commutator_le_commutator_zpowers :
    commutatorClosure H d ≤ ⁅H, Subgroup.zpowers d⁆ := by
  unfold commutatorClosure
  rw [Subgroup.closure_le]
  rintro x ⟨y, rfl⟩
  exact Subgroup.commutator_mem_commutator y.2 (Subgroup.mem_zpowers d)

lemma commutator_zpowers_le_closure_commutator :
    ⁅H, Subgroup.zpowers d⁆ ≤ commutatorClosure H d := by
  rw [Subgroup.commutator_le]
  rintro x hx w ⟨n, rfl⟩
  exact commutator_zpow_mem_closure_commutator H d ⟨x, hx⟩ n

lemma commutator_zpowers_eq_closure_commutator :
    ⁅H, Subgroup.zpowers d⁆ = commutatorClosure H d :=
  le_antisymm (commutator_zpowers_le_closure_commutator H d)
    (closure_commutator_le_commutator_zpowers H d)

lemma map_commSub_conjNormal :
    (K22p.commSub (MulAut.conjNormal d : MulAut ↥H)).map H.subtype = commutatorClosure H d := by
  unfold commutatorClosure K22p.commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    exact ⟨y⁻¹, (subtype_commSub_conjNormal_apply H d y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(y⁻¹)⁻¹ * (MulAut.conjNormal d : MulAut ↥H) y⁻¹, ⟨y⁻¹, rfl⟩, ?_⟩
    simpa using subtype_commSub_conjNormal_apply H d y⁻¹

end Helpers

theorem commSub_conjNormal_map {Γ : Type} [Group Γ] (H D : Subgroup Γ) [H.Normal] (d : Γ)
    (hd : D = Subgroup.zpowers d) :
    (K22p.commSub (MulAut.conjNormal d : MulAut ↥H)).map H.subtype = ⁅H, D⁆ := by
  rw [hd, map_commSub_conjNormal H d, commutator_zpowers_eq_closure_commutator H d]

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
