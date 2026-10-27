module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuBits
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix

@[expose] def gramJ : Matrix (Fin 6) (Fin 6) (ZMod 2) := toMat gramB

@[expose] def spGrp : Subgroup (GL (Fin 6) (ZMod 2)) := CFSG.Open.StatedAPI.gramIsometry gramJ

abbrev G6 : Type := ↥spGrp

abbrev gM (g : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ((g : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))

theorem mem_spGrp {A : GL (Fin 6) (ZMod 2)} :
    A ∈ spGrp ↔ (A : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * gramJ *
      (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) = gramJ := Iff.rfl

theorem gM_mul (g h : G6) : gM (g * h) = gM g * gM h := rfl

theorem gM_one : gM (1 : G6) = 1 := rfl

theorem gM_injective : Function.Injective gM := fun _ _ h => Subtype.ext (Units.ext h)

theorem gM_symp (g : G6) : (gM g)ᵀ * gramJ * gM g = gramJ := g.2

instance : Finite G6 := inferInstance

theorem symp_toMat {A : BM} (h : bmul (bmul (btrans A) gramB) A = gramB) :
    (toMat A)ᵀ * gramJ * toMat A = gramJ := by
  rw [← toMat_btrans, gramJ, ← toMat_bmul, ← toMat_bmul, h]

@[expose] def invG (A : BM) (h1 : bmul A A = bone)
    (h2 : bmul (bmul (btrans A) gramB) A = gramB) : G6 :=
  ⟨⟨toMat A, toMat A, by rw [← toMat_bmul, h1, toMat_bone], by rw [← toMat_bmul, h1, toMat_bone]⟩,
    symp_toMat h2⟩

@[expose] def xE (s : Fin 3) : G6 := invG (xB s) (bit_invol s).1 (bit_symp s).1

@[expose] def yE (s : Fin 3) : G6 := invG (yB s) (bit_invol s).2.1 (bit_symp s).2.1

@[expose] def sE (s : Fin 3) : G6 := invG (sB s) (bit_invol s).2.2 (bit_symp s).2.2

abbrev xM (s : Fin 3) : Matrix (Fin 6) (Fin 6) (ZMod 2) := gM (xE s)

abbrev yM (s : Fin 3) : Matrix (Fin 6) (Fin 6) (ZMod 2) := gM (yE s)

abbrev sM (s : Fin 3) : Matrix (Fin 6) (Fin 6) (ZMod 2) := gM (sE s)

theorem xM_eq_toMat (s : Fin 3) : xM s = toMat (xB s) := rfl

theorem yM_eq_toMat (s : Fin 3) : yM s = toMat (yB s) := rfl

theorem sM_eq_toMat (s : Fin 3) : sM s = toMat (sB s) := rfl

theorem sE_def (s : Fin 3) : sE s = xE s * yE s * xE s := by
  apply gM_injective
  show toMat (sB s) = toMat (xB s) * toMat (yB s) * toMat (xB s)
  rw [← toMat_bmul, ← toMat_bmul, ← (bit_rel s).1]

@[expose] def IsUpU (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Prop :=
  ∀ a b : Fin 6, (b < a → M a b = 0) ∧ (a = b → M a b = 1)

@[expose] def IsLoU (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Prop :=
  ∀ a b : Fin 6, (a < b → M a b = 0) ∧ (a = b → M a b = 1)

instance (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Decidable (IsUpU M) := by
  unfold IsUpU
  haveI : ∀ a : Fin 6, Decidable (∀ b : Fin 6, (b < a → M a b = 0) ∧ (a = b → M a b = 1)) :=
    fun _ => Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

instance (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Decidable (IsLoU M) := by
  unfold IsLoU
  haveI : ∀ a : Fin 6, Decidable (∀ b : Fin 6, (a < b → M a b = 0) ∧ (a = b → M a b = 1)) :=
    fun _ => Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

theorem upU_one : IsUpU 1 := by decide

theorem loU_one : IsLoU 1 := by decide

theorem upU_mul {M N : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hM : IsUpU M) (hN : IsUpU N) :
    IsUpU (M * N) := by
  intro a b
  refine ⟨fun hba => ?_, fun hab => ?_⟩
  · rw [mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with hca | hac
    · rw [(hM a c).1 hca, zero_mul]
    · rw [(hN c b).1 (lt_of_lt_of_le hba hac), mul_zero]
  · subst hab
    rw [mul_apply, Finset.sum_eq_single a]
    · rw [(hM a a).2 rfl, (hN a a).2 rfl, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [(hM a c).1 h, zero_mul]
      · rw [(hN c a).1 h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h

theorem loU_mul {M N : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hM : IsLoU M) (hN : IsLoU N) :
    IsLoU (M * N) := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge a c with hac | hca
    · rw [(hM a c).1 hac, zero_mul]
    · rw [(hN c b).1 (lt_of_le_of_lt hca hab), mul_zero]
  · subst hab
    rw [mul_apply, Finset.sum_eq_single a]
    · rw [(hM a a).2 rfl, (hN a a).2 rfl, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [(hN c a).1 h, mul_zero]
      · rw [(hM a c).1 h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h

theorem inv_mem_of_mul_closed {G : Type*} [Group G] [Finite G] {P : G → Prop} (h1 : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b)) {g : G} (hg : P g) : P g⁻¹ := by
  have hpow : ∀ k : ℕ, P (g ^ k) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hg
  have hpos : 0 < orderOf g := orderOf_pos g
  have h' : g ^ (orderOf g - 1) * g = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  have e : g⁻¹ = g ^ (orderOf g - 1) := (eq_inv_of_mul_eq_one_left h').symm
  rw [e]
  exact hpow _

@[expose] def Ugrp : Subgroup G6 where
  carrier := {g | IsUpU (gM g)}
  mul_mem' ha hb := upU_mul ha hb
  one_mem' := upU_one
  inv_mem' {g} hg := inv_mem_of_mul_closed (P := fun g : G6 => IsUpU (gM g)) upU_one
    (fun _ _ ha hb => upU_mul ha hb) (show IsUpU (gM g) from hg)

@[expose] def Lgrp : Subgroup G6 where
  carrier := {g | IsLoU (gM g)}
  mul_mem' ha hb := loU_mul ha hb
  one_mem' := loU_one
  inv_mem' {g} hg := inv_mem_of_mul_closed (P := fun g : G6 => IsLoU (gM g)) loU_one
    (fun _ _ ha hb => loU_mul ha hb) (show IsLoU (gM g) from hg)

theorem mem_Ugrp {g : G6} : g ∈ Ugrp ↔ IsUpU (gM g) := Iff.rfl

theorem mem_Lgrp {g : G6} : g ∈ Lgrp ↔ IsLoU (gM g) := Iff.rfl

theorem xE_upU : ∀ s, IsUpU (xM s) := by decide +kernel

theorem yE_loU : ∀ s, IsLoU (yM s) := by decide +kernel

theorem xE_mem (s : Fin 3) : xE s ∈ Ugrp := xE_upU s

theorem yE_mem (s : Fin 3) : yE s ∈ Lgrp := yE_loU s

@[expose] def e6 : Fin 3 ⊕ Fin 3 ≃ Fin 6 where
  toFun := Sum.elim (fun i => ⟨i.val, by omega⟩) (fun i => ⟨5 - i.val, by omega⟩)
  invFun j := if h : j.val < 3 then Sum.inl ⟨j.val, h⟩ else Sum.inr ⟨5 - j.val, by omega⟩
  left_inv := by decide
  right_inv := by decide

@[expose] noncomputable def reindexG :
    GL (Fin 3 ⊕ Fin 3) (ZMod 2) ≃* GL (Fin 6) (ZMod 2) :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e6).toRingEquiv.toMulEquiv

theorem coe_reindexG (g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    ((reindexG g : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      Matrix.reindex e6 e6 (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) := rfl

theorem reindex_gram :
    Matrix.reindex e6 e6
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
        gramJ := by
  decide +kernel

theorem reindex_isometry_iff (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (Matrix.reindex e6 e6 M)ᵀ * gramJ * Matrix.reindex e6 e6 M = gramJ ↔
      Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0 := by
  set E := Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e6
  have hmul : ∀ X Y : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2),
      Matrix.reindex e6 e6 (X * Y) = Matrix.reindex e6 e6 X * Matrix.reindex e6 e6 Y :=
    fun X Y => map_mul E X Y
  have htr : ∀ X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2),
      Matrix.reindex e6 e6 Xᵀ = (Matrix.reindex e6 e6 X)ᵀ :=
    fun X => (Matrix.transpose_reindex _ _ X).symm
  rw [← reindex_gram, ← htr, ← hmul, ← hmul]
  exact E.injective.eq_iff

theorem reindexG_mem_iff (h : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    reindexG h ∈ spGrp ↔ h ∈ CFSG.Open.StatedSp 3 (ZMod 2) := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  show ((reindexG h : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ * gramJ *
      ((reindexG h : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = gramJ ↔ _
  rw [coe_reindexG]
  exact reindex_isometry_iff _

theorem spGrp_eq_map :
    spGrp = (CFSG.Open.StatedSp 3 (ZMod 2)).map reindexG.toMonoidHom := by
  ext g
  obtain ⟨h, rfl⟩ := reindexG.surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  exact reindexG_mem_iff h

theorem nonempty_g6_mulEquiv : Nonempty (G6 ≃* ↥(CFSG.Open.StatedSp 3 (ZMod 2))) :=
  ⟨(MulEquiv.subgroupCongr spGrp_eq_map).trans
    (Subgroup.equivMapOfInjective _ reindexG.toMonoidHom reindexG.injective).symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
