module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS3Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolSec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModelBase

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

variable {n : ℕ}

theorem map_act_eq_self {M : Model n} {U : Subgroup M.W} (hU : IsInvSub M ⊤ U) (σ : Perm (Fin n)) :
    U.map (M.act σ : M.W ≃* M.W).toMonoidHom = U := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hU σ (Subgroup.mem_top σ) u hu
  · intro hx
    exact ⟨M.act σ⁻¹ x, hU σ⁻¹ (Subgroup.mem_top _) x hx, act_act_inv M σ x⟩

@[expose] def quotAct (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) (σ : Perm (Fin n)) :
    MulAut (M.W ⧸ U) :=
  QuotientGroup.congr U U (M.act σ) (map_act_eq_self hU σ)

theorem quotAct_mk (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) (σ : Perm (Fin n))
    (w : M.W) :
    quotAct M U hU σ (QuotientGroup.mk w : M.W ⧸ U) = (QuotientGroup.mk (M.act σ w) : M.W ⧸ U) :=
  QuotientGroup.congr_mk _ _ _ (map_act_eq_self hU σ) w

@[expose] def Model.quot (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) : Model n where
  W := M.W ⧸ U
  grp := QuotientGroup.Quotient.commGroup U
  fin := inferInstance
  act :=
    { toFun := quotAct M U hU
      map_one' := MulEquiv.ext fun x => by
        induction x using QuotientGroup.induction_on with
        | H z => rw [quotAct_mk]; simp
      map_mul' := fun σ τ => MulEquiv.ext fun x => by
        induction x using QuotientGroup.induction_on with
        | H z =>
          rw [MulAut.mul_apply, quotAct_mk, quotAct_mk, quotAct_mk, act_mul_apply] }
  sq := fun w => by
    induction w using QuotientGroup.induction_on with
    | H z => rw [← QuotientGroup.mk_mul, M.sq z]; rfl

@[expose] def Model.projQuot (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) :
    M.W →* (M.quot U hU).W := QuotientGroup.mk' U

theorem Model.projQuot_surjective (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) :
    Function.Surjective (M.projQuot U hU) := QuotientGroup.mk'_surjective U

theorem Model.ker_projQuot (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) :
    (M.projQuot U hU).ker = U := QuotientGroup.ker_mk' U

theorem Model.projQuot_act (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U)
    (σ : Perm (Fin n)) (w : M.W) :
    (M.quot U hU).act σ (M.projQuot U hU w) = M.projQuot U hU (M.act σ w) :=
  quotAct_mk M U hU σ w

theorem Model.projQuot_eq_iff (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) (v w : M.W) :
    M.projQuot U hU v = M.projQuot U hU w ↔ v⁻¹ * w ∈ U :=
  QuotientGroup.eq

theorem Model.projQuot_mem_fixW_iff (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U)
    (B : Subgroup (Perm (Fin n))) (w : M.W) :
    M.projQuot U hU w ∈ fixW (M.quot U hU) B ↔ w ∈ fixQ M B U := by
  rw [mem_fixQ]
  refine forall₂_congr fun b _ => ?_
  rw [Model.projQuot_act, Model.projQuot_eq_iff]
  have h2 : (M.act b w)⁻¹ * w = (M.act b w * w⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv, mul_comm]
  rw [h2, inv_mem_iff]

theorem fixW_quot (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U)
    (B : Subgroup (Perm (Fin n))) :
    fixW (M.quot U hU) B = (fixQ M B U).map (M.projQuot U hU) := by
  ext x
  obtain ⟨w, rfl⟩ := M.projQuot_surjective U hU x
  rw [M.projQuot_mem_fixW_iff]
  constructor
  · intro h
    exact ⟨w, h, rfl⟩
  · rintro ⟨v, hv, hvw⟩
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, w = v * u :=
      ⟨v⁻¹ * w, (M.projQuot_eq_iff U hU v w).mp hvw, by simp⟩
    intro b hb
    have h4 : M.act b (v * u) * (v * u)⁻¹ = (M.act b v * v⁻¹) * (M.act b u * u⁻¹) := by
      rw [map_mul, mul_inv_rev]
      ac_rfl
    show M.act b (v * u) * (v * u)⁻¹ ∈ U
    rw [h4]
    exact U.mul_mem (hv b hb) (U.mul_mem (hU b (Subgroup.mem_top b) u hu) (U.inv_mem hu))

theorem index_fixW_quot (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U)
    (B : Subgroup (Perm (Fin n))) :
    (fixW (M.quot U hU) B).index = (fixQ M B U).index := by
  rw [fixW_quot, Subgroup.index_map_eq _ (M.projQuot_surjective U hU)]
  rw [M.ker_projQuot]
  exact le_fixQ (fun b _ u hu => hU b (Subgroup.mem_top b) u hu)

theorem idx_quot (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) (σ : Perm (Fin n)) :
    idx (M.quot U hU) σ = (fixQ M (Subgroup.zpowers σ) U).index :=
  index_fixW_quot M U hU _

theorem fixW_restrict (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U)
    (B : Subgroup (Perm (Fin n))) :
    fixW (M.restrict U hU) B = (fixW M B).subgroupOf U := by
  ext u
  simp only [mem_fixW]
  refine forall₂_congr fun b hb => ?_
  exact Subtype.ext_iff

@[expose] def Model.restrictMk (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) (u : M.W)
    (hu : u ∈ U) : (M.restrict U hU).W := ⟨u, hu⟩

theorem Model.restrictMk_mem_fixW (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U)
    (B : Subgroup (Perm (Fin n))) (u : M.W) (hu : u ∈ U) :
    M.restrictMk U hU u hu ∈ fixW (M.restrict U hU) B ↔ u ∈ fixW M B := by
  rw [fixW_restrict]
  exact Iff.rfl

theorem idx_restrict (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) (σ : Perm (Fin n)) :
    idx (M.restrict U hU) σ = (fixW M (Subgroup.zpowers σ)).relIndex U := by
  unfold idx
  rw [fixW_restrict]
  rfl

theorem idx_restrict_eq_card_commW (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U)
    (σ : Perm (Fin n)) :
    idx (M.restrict U hU) σ = Nat.card (commW M (Subgroup.zpowers σ) U) := by
  rw [idx_restrict, card_commW_zpowers_eq_relIndex (fun b _ u hu => hU b (Subgroup.mem_top b) u hu)]

theorem idx_restrict_mul_idx_quot_le (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U)
    (σ : Perm (Fin n)) :
    idx (M.restrict U hU) σ * idx (M.quot U hU) σ ≤ idx M σ := by
  rw [idx_restrict, idx_quot]
  exact bf4_index (fun b _ u hu => hU b (Subgroup.mem_top b) u hu)

theorem idx_restrict_le (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) (σ : Perm (Fin n)) :
    idx (M.restrict U hU) σ ≤ idx M σ := by
  have h := idx_restrict_mul_idx_quot_le M U hU σ
  have : 0 < idx (M.quot U hU) σ := Nat.pos_of_ne_zero (by
    rw [idx_quot]; exact Subgroup.FiniteIndex.index_ne_zero)
  calc idx (M.restrict U hU) σ ≤ idx (M.restrict U hU) σ * idx (M.quot U hU) σ :=
        Nat.le_mul_of_pos_right _ this
    _ ≤ _ := h

theorem idx_quot_le (M : Model n) (U : Subgroup M.W) (hU : IsInvSub M ⊤ U) (σ : Perm (Fin n)) :
    idx (M.quot U hU) σ ≤ idx M σ := by
  have h := idx_restrict_mul_idx_quot_le M U hU σ
  have : 0 < idx (M.restrict U hU) σ := Nat.pos_of_ne_zero (by
    rw [idx_restrict]
    exact relIndex_ne_zero_of_finite _ _)
  calc idx (M.quot U hU) σ ≤ idx (M.restrict U hU) σ * idx (M.quot U hU) σ :=
        Nat.le_mul_of_pos_left _ this
    _ ≤ _ := h

theorem Model.Iso.fixW_eq {M N : Model n} (e : M.Iso N) (B : Subgroup (Perm (Fin n))) :
    fixW N B = (fixW M B).map e.toMulEquiv.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := e.toMulEquiv.surjective y
  constructor
  · intro h
    refine ⟨x, fun b hb => ?_, rfl⟩
    apply e.toMulEquiv.injective
    rw [e.map_act]
    exact h b hb
  · rintro ⟨v, hv, hvx⟩ b hb
    have hvx' : e.toMulEquiv v = e.toMulEquiv x := hvx
    have := e.toMulEquiv.injective hvx'
    subst this
    rw [← e.map_act, hv b hb]

theorem Model.Iso.index_fixW_eq {M N : Model n} (e : M.Iso N) (B : Subgroup (Perm (Fin n))) :
    (fixW N B).index = (fixW M B).index := by
  rw [e.fixW_eq B]
  exact Subgroup.index_map_equiv _ e.toMulEquiv

theorem Model.Iso.idx_eq {M N : Model n} (e : M.Iso N) (σ : Perm (Fin n)) : idx N σ = idx M σ :=
  e.index_fixW_eq _

theorem Model.Iso.fixW_eq_top_iff {M N : Model n} (e : M.Iso N) (B : Subgroup (Perm (Fin n))) :
    fixW N B = ⊤ ↔ fixW M B = ⊤ := by
  rw [← Subgroup.index_eq_one, ← Subgroup.index_eq_one, e.index_fixW_eq]

theorem isInvSub_fixW_of_normal (M : Model n) {N : Subgroup (Perm (Fin n))} (hN : N.Normal) :
    IsInvSub M ⊤ (fixW M N) := by
  intro σ _ u hu b hb
  have h1 : σ⁻¹ * b * σ ∈ N := by
    have := hN.conj_mem b hb σ⁻¹
    simpa using this
  have h2 := hu _ h1
  calc M.act b (M.act σ u) = M.act σ (M.act (σ⁻¹ * b * σ) u) := by
        rw [← act_mul_apply, ← act_mul_apply]; congr 1; group
    _ = M.act σ u := by rw [h2]

theorem isInvSub_top_commW_of_normal (M : Model n) {N : Subgroup (Perm (Fin n))} (hN : N.Normal)
    {U : Subgroup M.W} (hU : IsInvSub M ⊤ U) : IsInvSub M ⊤ (commW M N U) := by
  intro g _ w hw
  unfold commW at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, u, hu, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨g * c * g⁻¹, by simpa using hN.conj_mem c hc g, M.act g u,
      hU g (Subgroup.mem_top g) u hu, ?_⟩
    rw [map_mul, map_inv, act_mul_apply, act_mul_apply, act_inv_act]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

theorem isInvSub_top (M : Model n) : IsInvSub M ⊤ (⊤ : Subgroup M.W) :=
  fun _ _ _ _ => Subgroup.mem_top _

theorem alt5_perfect : ⁅alternatingGroup (Fin 5), alternatingGroup (Fin 5)⁆ =
    alternatingGroup (Fin 5) :=
  commutator_alternatingGroup_eq_self (by simp)

theorem alt5_le_closure_odd : alternatingGroup (Fin 5) ≤
    Subgroup.closure {x | x ∈ alternatingGroup (Fin 5) ∧ Odd (orderOf x)} := by
  refine le_trans (le_of_eq (Equiv.Perm.closure_three_cycles_eq_alternating (α := Fin 5)).symm) ?_
  refine Subgroup.closure_mono ?_
  intro x hx
  refine ⟨hx.mem_alternatingGroup, ?_⟩
  rw [hx.orderOf]
  decide

theorem perm5_eq_alt5_mul_syl (g : Perm (Fin 5)) :
    ∃ a ∈ alternatingGroup (Fin 5), ∃ s ∈ S5Syl, g = a * s := by
  have hs : swap (0 : Fin 5) 2 ∈ S5Syl := Subgroup.subset_closure (by simp)
  by_cases hg : Perm.sign g = 1
  · exact ⟨g, Perm.mem_alternatingGroup.mpr hg, 1, Subgroup.one_mem _, by simp⟩
  · refine ⟨g * swap 0 2, ?_, swap 0 2, hs, by rw [mul_assoc, swap_mul_self, mul_one]⟩
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (by decide)]
    have : Perm.sign g = -1 := (Int.units_eq_one_or _).resolve_left hg
    rw [this]
    decide

end CFSG.Quasithin.F53Mod
