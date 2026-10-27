module

public import CFSG.LocalAnalysis.StandardType.GGFFModelDefs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.Defs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.StandardType.GGFF

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt pow_val_add vecElt_single vecElt_single_one)

section Torus

variable {H : Type*} [Group H] {z : Fin 3 → H}

def tor (z : Fin 3 → H) : Subgroup H := Subgroup.closure (Set.range z)

theorem vecElt_zero (z : Fin 3 → H) : vecElt z 0 = 1 := by simp [vecElt]

theorem vecElt_add (hp : ∀ i, z i ^ 3 = 1) (hc : ∀ i j, z i * z j = z j * z i)
    (v w : Fin 3 → ZMod 3) : vecElt z (v + w) = vecElt z v * vecElt z w := by
  simp only [vecElt, Pi.add_apply, pow_val_add (hp _)]
  set p0 := z 0 ^ (v 0).val
  set p1 := z 1 ^ (v 1).val
  set p2 := z 2 ^ (v 2).val
  set q0 := z 0 ^ (w 0).val
  set q1 := z 1 ^ (w 1).val
  set q2 := z 2 ^ (w 2).val
  have h01 : q0 * p1 = p1 * q0 := (Commute.pow_pow (hc 0 1) _ _).eq
  have h02 : q0 * p2 = p2 * q0 := (Commute.pow_pow (hc 0 2) _ _).eq
  have h12 : q1 * p2 = p2 * q1 := (Commute.pow_pow (hc 1 2) _ _).eq
  calc p0 * q0 * (p1 * q1) * (p2 * q2) = p0 * (q0 * p1) * q1 * p2 * q2 := by group
    _ = p0 * p1 * q0 * (q1 * p2) * q2 := by rw [h01]; group
    _ = p0 * p1 * (q0 * p2) * q1 * q2 := by rw [h12]; group
    _ = p0 * p1 * p2 * (q0 * q1 * q2) := by rw [h02]; group

theorem vecElt_neg (hp : ∀ i, z i ^ 3 = 1) (hc : ∀ i j, z i * z j = z j * z i)
    (v : Fin 3 → ZMod 3) : vecElt z (-v) = (vecElt z v)⁻¹ := by
  have h := vecElt_add hp hc (-v) v
  rw [neg_add_cancel, vecElt_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem vecElt_mem_tor (z : Fin 3 → H) (v : Fin 3 → ZMod 3) : vecElt z v ∈ tor z := by
  have hz : ∀ i, z i ∈ tor z := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  exact (tor z).mul_mem ((tor z).mul_mem ((tor z).pow_mem (hz 0) _) ((tor z).pow_mem (hz 1) _))
    ((tor z).pow_mem (hz 2) _)

theorem mem_tor (hp : ∀ i, z i ^ 3 = 1) (hc : ∀ i j, z i * z j = z j * z i) {x : H} :
    x ∈ tor z ↔ ∃ v, x = vecElt z v := by
  refine ⟨fun hx => ?_, fun ⟨v, hv⟩ => hv ▸ vecElt_mem_tor z v⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨Pi.single i 1, (vecElt_single_one i).symm⟩
  | one => exact ⟨0, (vecElt_zero z).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    exact ⟨v + w, (vecElt_add hp hc v w).symm⟩
  | inv x _ hx =>
    obtain ⟨v, rfl⟩ := hx
    exact ⟨-v, (vecElt_neg hp hc v).symm⟩

theorem vecElt_injective (hp : ∀ i, z i ^ 3 = 1) (hc : ∀ i j, z i * z j = z j * z i)
    (hi : ∀ v, vecElt z v = 1 → v = 0) : Function.Injective (vecElt z) := by
  intro v w h
  have : vecElt z (v + -w) = 1 := by
    rw [vecElt_add hp hc, vecElt_neg hp hc, h]
    exact mul_inv_cancel _
  exact add_neg_eq_zero.mp (hi _ this)

theorem card_tor (hp : ∀ i, z i ^ 3 = 1) (hc : ∀ i j, z i * z j = z j * z i)
    (hi : ∀ v, vecElt z v = 1 → v = 0) : Nat.card (tor z) = 27 := by
  have e : (Fin 3 → ZMod 3) ≃ tor z :=
    Equiv.ofBijective (fun v => ⟨vecElt z v, vecElt_mem_tor z v⟩)
      ⟨fun v w h => vecElt_injective hp hc hi (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
        obtain ⟨v, rfl⟩ := (mem_tor hp hc).mp hx
        exact ⟨v, rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem isElemAbelian_tor (hp : ∀ i, z i ^ 3 = 1) (hc : ∀ i j, z i * z j = z j * z i) :
    CFSG.Assembly.IsElemAbelian 3 (tor z) :=
  CFSG.Open.IsElemAbelian.closure_of_commute (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hc i j) (by
    rintro _ ⟨i, rfl⟩
    exact hp i)

end Torus

theorem card_wt (k : ℕ) :
    (Finset.univ.filter fun v : Fin 3 → ZMod 3 => wt v = k).card =
      if k = 0 then 1 else if k = 1 then 6 else if k = 2 then 12 else if k = 3 then 8 else 0 := by
  have hk : k ≤ 3 ∨ 3 < k := le_or_gt k 3
  rcases hk with hk | hk
  · interval_cases k <;> decide
  · have : (Finset.univ.filter fun v : Fin 3 → ZMod 3 => wt v = k) = ∅ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      have : wt v ≤ 3 := by
        unfold wt
        exact (Finset.card_filter_le _ _).trans (by simp)
      omega
    rw [this]
    simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega]

theorem wt_eq_zero_iff (v : Fin 3 → ZMod 3) : wt v = 0 ↔ v = 0 := by
  revert v
  decide

theorem wt_neg (v : Fin 3 → ZMod 3) : wt (-v) = wt v := by
  revert v
  decide

theorem eq_single_of_wt_eq_one (v : Fin 3 → ZMod 3) (h : wt v = 1) :
    ∃ j a, a ≠ 0 ∧ v = Pi.single j a := by
  revert v
  decide

theorem vecElt_map {H H' : Type*} [Group H] [Group H'] {F : Type*} [FunLike F H H']
    [MonoidHomClass F H H'] (f : F) (z : Fin 3 → H) (v : Fin 3 → ZMod 3) :
    vecElt (fun i => f (z i)) v = f (vecElt z v) := by
  simp [vecElt, map_mul, map_pow]

theorem isConj_mulEquiv_iff {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') {a b : H} :
    IsConj (e a) (e b) ↔ IsConj a b := by
  simp only [isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, e.injective ?_⟩
    simpa [map_mul, map_inv] using hc
  · rintro ⟨c, hc⟩
    exact ⟨e c, by rw [← hc]; simp [map_mul, map_inv]⟩

namespace Model

variable {H : Type} [Group H] {z : Fin 3 → H}

theorem mem_tor' (h : Model H z) {x : H} : x ∈ tor z ↔ ∃ v, x = vecElt z v :=
  mem_tor h.pow_z h.comm_z

theorem vecElt_mul (h : Model H z) (v w : Fin 3 → ZMod 3) :
    vecElt z v * vecElt z w = vecElt z (v + w) :=
  (vecElt_add h.pow_z h.comm_z v w).symm

theorem vecElt_inv (h : Model H z) (v : Fin 3 → ZMod 3) : (vecElt z v)⁻¹ = vecElt z (-v) :=
  (vecElt_neg h.pow_z h.comm_z v).symm

theorem vecElt_inj (h : Model H z) : Function.Injective (vecElt z) :=
  vecElt_injective h.pow_z h.comm_z h.inj

theorem card_tor' (h : Model H z) : Nat.card (tor z) = 27 := card_tor h.pow_z h.comm_z h.inj

theorem isElemAbelian_tor' (h : Model H z) : CFSG.Assembly.IsElemAbelian 3 (tor z) :=
  isElemAbelian_tor h.pow_z h.comm_z

theorem z_ne_one (h : Model H z) (i : Fin 3) : z i ≠ 1 := fun h1 => by
  have := h.inj (Pi.single i 1) (by rw [vecElt_single_one, h1])
  have h2 := congrFun this i
  simp at h2

theorem exists_ne_comm (h : Model H z) : ∃ x y : H, x * y ≠ y * x := by
  obtain ⟨g, hg⟩ := h.mono 1 ![2, 1, 1] (by decide)
  refine ⟨g, z 0, fun hc => h.z_ne_one 0 ?_⟩
  have h0 : g * z 0 * g⁻¹ = z 0 ^ (2 : ZMod 3).val := hg 0
  rw [show (2 : ZMod 3).val = 2 from rfl, hc, mul_inv_cancel_right, pow_two] at h0
  exact (mul_eq_left.mp h0.symm)

theorem eq_one_of_forall_comm (h : Model H z) {x : H} (hx : ∀ y, x * y = y * x) : x = 1 := by
  have := h.simple
  have hcen : x ∈ Subgroup.center H := Subgroup.mem_center_iff.mpr fun y => (hx y).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with hb | ht
  · rw [hb] at hcen
    exact hcen
  · exfalso
    obtain ⟨a, c, hac⟩ := h.exists_ne_comm
    have ha : a ∈ Subgroup.center H := ht ▸ Subgroup.mem_top a
    exact hac (Subgroup.mem_center_iff.mp ha c).symm

theorem isConj_inv (h : Model H z) {x : H} (hx : x ^ 3 = 1) : IsConj x x⁻¹ := by
  obtain ⟨g, v, rfl⟩ := h.fus x hx
  by_cases hv : v = 0
  · subst hv
    simp [vecElt_zero]
  · have hc : IsConj (vecElt z v) (vecElt z (-v)) :=
      (h.conj_iff v (-v) hv (neg_ne_zero.mpr hv)).mpr (wt_neg v).symm
    rw [← h.vecElt_inv] at hc
    have e : (g * vecElt z v * g⁻¹)⁻¹ = g * (vecElt z v)⁻¹ * g⁻¹ := by group
    rw [e]
    exact ((isConj_iff.mpr ⟨g, rfl⟩).symm.trans hc).trans (isConj_iff.mpr ⟨g, rfl⟩)

theorem mono_of_aut (h : Model H z) (α : MulAut H) (hα : ∀ v, ∃ w, α (vecElt z v) = vecElt z w)
    (i : Fin 3) : ∃ j, α (z i) = z j ∨ α (z i) = (z j)⁻¹ := by
  choose f hf using hα
  have hfi : Function.Injective f := fun v v' hvv' =>
    h.vecElt_inj (α.injective (by rw [hf, hf, hvv']))
  have hf0 : f 0 = 0 := h.vecElt_inj (by rw [← hf, vecElt_zero, map_one])
  have hfne : ∀ v, v ≠ 0 → f v ≠ 0 := fun v hv h0 => hv (hfi (h0.trans hf0.symm))
  have hconj : ∀ v w, IsConj (vecElt z (f v)) (vecElt z (f w)) ↔
      IsConj (vecElt z v) (vecElt z w) := fun v w => by
    rw [← hf, ← hf]
    exact isConj_mulEquiv_iff α
  set u : Fin 3 → ZMod 3 := Pi.single i 1 with hudef
  have hu : u ≠ 0 := fun h0 => by
    have := congrFun h0 i
    simp [u] at this
  have hwu : wt u = 1 := by fin_cases i <;> decide
  have key : ∀ w, w ≠ 0 → (wt (f w) = wt (f u) ↔ wt w = 1) := fun w hw => by
    rw [← hwu, ← h.conj_iff (f w) (f u) (hfne w hw) (hfne u hu), hconj,
      h.conj_iff w u hw hu]
  have hset : (Finset.univ.filter fun w => wt w = wt (f u)) =
      (Finset.univ.filter fun w => wt w = 1).image f := by
    ext w'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hw'
      obtain ⟨w, rfl⟩ := Finite.surjective_of_injective hfi w'
      have hw : w ≠ 0 := fun h0 => by
        rw [h0, hf0] at hw'
        exact hfne u hu ((wt_eq_zero_iff _).mp (hw'.symm.trans ((wt_eq_zero_iff 0).mpr rfl)))
      exact ⟨w, (key w hw).mp hw', rfl⟩
    · rintro ⟨w, hw1, rfl⟩
      have hw : w ≠ 0 := fun h0 => by
        rw [h0, (wt_eq_zero_iff 0).mpr rfl] at hw1
        exact absurd hw1 (by decide)
      exact (key w hw).mpr hw1
  have hcard := congrArg Finset.card hset
  rw [Finset.card_image_of_injective _ hfi, card_wt, card_wt] at hcard
  have hk : wt (f u) = 1 := by
    have hne : wt (f u) ≠ 0 := fun h0 => hfne u hu ((wt_eq_zero_iff _).mp h0)
    have hle : wt (f u) ≤ 3 := (Finset.card_filter_le _ _).trans (by simp)
    interval_cases hx : wt (f u) <;> simp_all
  obtain ⟨j, a, ha, hja⟩ := eq_single_of_wt_eq_one (f u) hk
  refine ⟨j, ?_⟩
  have hαz : α (z i) = z j ^ a.val := by
    rw [← vecElt_single_one (z := z) i, ← hudef, hf, hja, vecElt_single]
  have ha' : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = 2 := by decide
  rcases ha' a ha with rfl | rfl
  · left
    rw [hαz, ZMod.val_one, pow_one]
  · right
    rw [hαz, show (2 : ZMod 3).val = 2 from rfl, eq_inv_iff_mul_eq_one, ← pow_succ, h.pow_z]

theorem eq_of_z_eq (h : Model H z) {i i' : Fin 3} (hz : z i = z i' ∨ z i = (z i')⁻¹) : i = i' := by
  by_contra hne
  rw [← vecElt_single_one (z := z) i, ← vecElt_single_one (z := z) i', h.vecElt_inv] at hz
  rcases hz with hz | hz
  · have := congrFun (h.vecElt_inj hz) i
    simp [hne] at this
  · have := congrFun (h.vecElt_inj hz) i
    simp [hne] at this

theorem exists_conj_of_aut (h : Model H z) (α : MulAut H)
    (hα : ∀ v, ∃ w, α (vecElt z v) = vecElt z w) : ∃ k : H, ∀ i, α (z i) = k * z i * k⁻¹ := by
  choose j hj using h.mono_of_aut α hα
  have hε : ∀ i, ∃ e : ZMod 3, e ≠ 0 ∧ α (z i) = z (j i) ^ e.val := fun i => by
    rcases hj i with h1 | h1
    · exact ⟨1, by decide, by rw [h1, ZMod.val_one, pow_one]⟩
    · refine ⟨2, by decide, ?_⟩
      rw [h1, show (2 : ZMod 3).val = 2 from rfl, eq_comm, eq_inv_iff_mul_eq_one, ← pow_succ,
        h.pow_z]
  choose ε hε0 hεe using hε
  have hinj : Function.Injective j := fun i i' hii' => by
    refine h.eq_of_z_eq ?_
    rcases hj i with h1 | h1 <;> rcases hj i' with h2 | h2 <;> rw [hii'] at h1
    · exact Or.inl (α.injective (h1.trans h2.symm))
    · exact Or.inr (α.injective (by rw [map_inv, h1, h2, inv_inv]))
    · exact Or.inr (α.injective (by rw [map_inv, h1, h2]))
    · exact Or.inl (α.injective (h1.trans h2.symm))
  obtain ⟨k, hk⟩ := h.mono (Equiv.ofBijective j (Finite.injective_iff_bijective.mp hinj)) ε hε0
  exact ⟨k, fun i => by rw [hεe i, hk i, Equiv.ofBijective_apply]⟩

theorem inner3 (h : Model H z) (α : MulAut H) (hα : α ^ 3 = 1) : ∃ k : H, α = MulAut.conj k :=
  h.inner_odd α 3 (by decide) hα

theorem ofMulEquiv {H' : Type} [Group H'] (e : H ≃* H') (h : Model H z) :
    Model H' (fun i => e (z i)) where
  simple := by
    have := h.simple
    exact e.symm.isSimpleGroup
  pow_z i := by rw [← map_pow, h.pow_z, map_one]
  comm_z i j := by rw [← map_mul, h.comm_z, map_mul]
  inj v hv := h.inj v (e.injective (by rw [← vecElt_map, hv, map_one]))
  inner_odd α m hm hα := by
    set β : MulAut H := (e.trans α).trans e.symm with hβ
    have hpow : ∀ j : ℕ, ∀ x, (β ^ j) x = e.symm ((α ^ j) (e x)) := fun j => by
      induction j with
      | zero => intro x; simp
      | succ j ih =>
        intro x
        rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
        simp [hβ]
    have hβm : β ^ m = 1 := by
      ext x
      rw [hpow, hα]
      simp
    obtain ⟨k, hk⟩ := h.inner_odd β m hm hβm
    refine ⟨e k, ?_⟩
    ext x
    have hx := congrArg (fun γ : MulAut H => γ (e.symm x)) hk
    simp only [hβ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply] at hx
    rw [MulAut.conj_apply]
    have := congrArg e hx
    simpa using this
  rank E hE := by
    have h1 := h.rank (E.map e.symm.toMonoidHom) (hE.map _)
    rwa [Subgroup.card_map_of_injective e.symm.injective] at h1
  torus E hE hc := by
    obtain ⟨g, hg⟩ := h.torus (E.map e.symm.toMonoidHom) (hE.map _)
      (by rw [Subgroup.card_map_of_injective e.symm.injective, hc])
    refine ⟨e g, fun x => ?_⟩
    have hx := hg (e.symm x)
    have hmem : e.symm x ∈ E.map e.symm.toMonoidHom ↔ x ∈ E := by
      rw [Subgroup.mem_map_equiv]
      simp
    rw [hmem] at hx
    rw [hx]
    refine exists_congr fun v => ?_
    rw [vecElt_map, ← map_inv, ← map_mul, ← map_mul, ← e.symm_apply_eq]
  fus x hx := by
    obtain ⟨g, v, hgv⟩ := h.fus (e.symm x) (by rw [← map_pow, hx, map_one])
    refine ⟨e g, v, ?_⟩
    rw [vecElt_map, ← map_inv, ← map_mul, ← map_mul, ← hgv, MulEquiv.apply_symm_apply]
  conj_iff v w hv hw := by
    rw [vecElt_map, vecElt_map, isConj_mulEquiv_iff]
    exact h.conj_iff v w hv hw
  mono σ ε hε := by
    obtain ⟨k, hk⟩ := h.mono σ ε hε
    exact ⟨e k, fun i => by rw [← map_inv, ← map_mul, ← map_mul, hk, map_pow]⟩
  no_five x hx h0 h1 := by
    refine e.symm.injective ?_
    rw [map_one]
    refine h.no_five _ (by rw [← map_pow, hx, map_one]) ?_ ?_
    · rw [← e.symm_apply_apply (z 0), ← map_mul, h0, map_mul]
    · rw [← e.symm_apply_apply (z 1), ← map_mul, h1, map_mul]
  five := by
    obtain ⟨x, hx1, hx5, h0, h12⟩ := h.five
    refine ⟨e x, fun h1 => hx1 (e.injective (by rw [h1, map_one])), by rw [← map_pow, hx5, map_one],
      by rw [← map_mul, h0, map_mul], ?_⟩
    rw [← map_mul, ← map_mul, ← map_mul, h12, map_mul, map_mul]

theorem conj (g : H) (h : Model H z) : Model H (fun i => g * z i * g⁻¹) := by
  have := h.ofMulEquiv (MulAut.conj g)
  simpa only [MulAut.conj_apply] using this

end Model

end CFSG.StandardType.GGFF

end
