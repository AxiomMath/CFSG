module

public import CFSG.Sporadic.Schreier.ONVectorOrder
public import CFSG.Certificates.SchreierTransversalProduct

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.Certificates CFSG.Sporadic.ON

abbrev x0 : Fin N := ⟨0, by norm_num⟩

abbrev threeBase : Set (Fin N) := {⟨0, by norm_num⟩, ⟨227759, by norm_num⟩, ⟨100817, by norm_num⟩}

theorem qon_base_take_three :
    {b | b ∈ QON.base.toList.take 3} = threeBase := by
  have hb : QON.base.toList = baseFin := by simp [QON, RawSchreierDatum.ofWords]
  have h3 : QON.base.toList.take 3 =
      [⟨0, by norm_num⟩, ⟨227759, by norm_num⟩, ⟨100817, by norm_num⟩] := by
    rw [hb, baseFin]
    decide
  ext x
  simp [h3]

theorem level3_eq_bot :
    QON.levelSubgroup 3 = ⊥ := by
  have hc := QON.level_card_eq_orbit_product qon_valid 3 (by rw [qon_baseCount]; omega)
  have e : ((List.finRange QON.baseCount).drop 3).map (fun j => Nat.card (QON.orbitPoints j)) =
      ((List.finRange QON.baseCount).map fun j => Nat.card (QON.orbitPoints j)).drop 3 := by
    rw [List.map_drop]
  rw [e, qon_orbit_sizes] at hc
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hc]; decide)

theorem pv_inf_fixing_three :
    Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) threeBase = ⊥ := by
  have hl := QON.levelSubgroup_eq_pointwise_stabilizer qon_valid 3 (by rw [qon_baseCount]; omega)
  rw [qon_originalSubgroup, qon_base_take_three] at hl
  rw [← hl]
  exact level3_eq_bot

theorem eq_of_three
    {g h : Equiv.Perm (Fin N)} (hg : g ∈ Pv) (hh : h ∈ Pv)
    (h0 : g ⟨0, by norm_num⟩ = h ⟨0, by norm_num⟩)
    (h1 : g ⟨227759, by norm_num⟩ = h ⟨227759, by norm_num⟩)
    (h2 : g ⟨100817, by norm_num⟩ = h ⟨100817, by norm_num⟩) : g = h := by
  have hmem : h⁻¹ * g ∈ Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) threeBase := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hh) hg,
      (mem_fixingSubgroup_iff (Equiv.Perm (Fin N))).2 fun x hx => ?_⟩
    rw [Equiv.Perm.smul_def, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    rcases hx with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  rw [pv_inf_fixing_three, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

namespace PairDecomp

variable {n : ℕ} (Q : RawSchreierDatum n) (hk : 3 ≤ Q.baseCount)

@[expose] def l0 : Fin Q.baseCount := ⟨0, by omega⟩

@[expose] def l1 : Fin Q.baseCount := ⟨1, by omega⟩

@[expose] def l2 : Fin Q.baseCount := ⟨2, by omega⟩

theorem base_mem_orbitPoints (i : Fin Q.baseCount) : Q.base.get i ∈ Q.orbitPoints i := by
  show ((Q.orbitSearch i).transversal? (Q.base.get i)).isSome = true
  rw [show (Q.orbitSearch i).transversal? (Q.base.get i) = Q.transversal? i
    (Q.base.get i) from rfl, Q.transversal_root i]
  rfl

theorem orbitTransversal_base (i : Fin Q.baseCount) (x : Q.orbitPoints i)
    (hx : (x : Fin n) = Q.base.get i) : Q.orbitTransversal i x = 1 := by
  rw [RawSchreierDatum.orbitTransversal, hx, Q.transversal_root i]
  rfl

theorem prod_ofFn_eq (f : Fin Q.baseCount → Equiv.Perm (Fin n))
    (h0 : f (l0 Q hk) = 1) (h3 : ∀ i : Fin Q.baseCount, 3 ≤ i.val → f i = 1) :
    (List.ofFn f).prod = f (l1 Q hk) * f (l2 Q hk) := by
  obtain ⟨m, hm⟩ : ∃ m, Q.baseCount = m + 3 := ⟨Q.baseCount - 3, by omega⟩
  rw [List.ofFn_congr hm f, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
    List.prod_cons, List.prod_cons, List.prod_cons]
  have htail : (List.ofFn fun i : Fin m => f (Fin.cast hm.symm i.succ.succ.succ)).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact h3 _ (by simp)
  rw [htail, mul_one]
  have e0 : Fin.cast hm.symm 0 = l0 Q hk := Fin.ext rfl
  have e1 : Fin.cast hm.symm (0 : Fin (m + 2)).succ = l1 Q hk := Fin.ext rfl
  have e2 : Fin.cast hm.symm ((0 : Fin (m + 1)).succ.succ) = l2 Q hk := Fin.ext rfl
  rw [e0, h0, one_mul, e1, e2]

variable (hQ : ValidSchreier Q)
  (hsing : ∀ i : Fin Q.baseCount, 3 ≤ i.val → Nat.card (Q.orbitPoints i) = 1)
include hQ hsing

omit hQ in
theorem orbitPoints_singleton {i : Fin Q.baseCount} (hi : 3 ≤ i.val) (x : Q.orbitPoints i) :
    (x : Fin n) = Q.base.get i := by
  have := (Nat.card_eq_one_iff_unique.1 (hsing i hi)).1
  exact congrArg Subtype.val (Subsingleton.elim x ⟨_, base_mem_orbitPoints Q i⟩)

theorem exists_unique_pair {g : Equiv.Perm (Fin n)} (hgP : g ∈ Q.originalSubgroup)
    (hg0 : g (Q.base.get (l0 Q hk)) = Q.base.get (l0 Q hk)) :
    ∃! yw : Q.orbitPoints (l1 Q hk) × Q.orbitPoints (l2 Q hk),
      g = Q.orbitTransversal (l1 Q hk) yw.1 * Q.orbitTransversal (l2 Q hk) yw.2 := by
  obtain ⟨-, Φ, hΦ, hbij, -⟩ := Q.schreier_transversal_product_bijection hQ
  obtain ⟨x, hx⟩ := hbij.2 ⟨g, hgP⟩
  have hgx : g = (List.ofFn fun i => Q.orbitTransversal i (x i)).prod := by
    rw [← hΦ, hx]
  have hx0 : (x (l0 Q hk) : Fin n) = Q.base.get (l0 Q hk) := by
    have h1 := Q.transversalSuffix_apply_base x (j := 0) (l0 Q hk).isLt
    have hl : (⟨0, (l0 Q hk).isLt⟩ : Fin Q.baseCount) = l0 Q hk := Fin.ext rfl
    rw [hl, Q.transversalSuffix_zero, ← hgx, hg0] at h1
    exact h1.symm
  have hpair : g = Q.orbitTransversal (l1 Q hk) (x (l1 Q hk)) *
      Q.orbitTransversal (l2 Q hk) (x (l2 Q hk)) := by
    rw [hgx]
    exact prod_ofFn_eq Q hk (fun i => Q.orbitTransversal i (x i))
      (orbitTransversal_base Q _ _ hx0)
      fun i hi => orbitTransversal_base Q _ _ (orbitPoints_singleton Q hsing hi _)
  refine ⟨(x (l1 Q hk), x (l2 Q hk)), hpair, ?_⟩
  rintro ⟨y, w⟩ hyw
  have heq := hyw.symm.trans hpair
  have hfix : ∀ t ∈ Q.levelSubgroup (l2 Q hk).val,
      t (Q.base.get (l1 Q hk)) = Q.base.get (l1 Q hk) :=
    fun t ht => Q.levelSubgroup_fixes_base_index _ t ht (l1 Q hk) (by show 1 < 2; omega)
  have hy : y = x (l1 Q hk) := by
    have e := DFunLike.congr_fun heq (Q.base.get (l1 Q hk))
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      hfix _ (Q.orbitTransversal_spec (l2 Q hk) w).2.1,
      hfix _ (Q.orbitTransversal_spec (l2 Q hk) (x (l2 Q hk))).2.1,
      (Q.orbitTransversal_spec (l1 Q hk) y).2.2,
      (Q.orbitTransversal_spec (l1 Q hk) (x (l1 Q hk))).2.2] at e
    exact Subtype.ext e
  subst hy
  have hw : w = x (l2 Q hk) := by
    have e := DFunLike.congr_fun (mul_left_cancel heq) (Q.base.get (l2 Q hk))
    rw [(Q.orbitTransversal_spec (l2 Q hk) w).2.2,
      (Q.orbitTransversal_spec (l2 Q hk) (x (l2 Q hk))).2.2] at e
    exact Subtype.ext e
  rw [hw]

end PairDecomp


theorem qon_three :
    3 ≤ QON.baseCount := by rw [qon_baseCount]; norm_num

theorem qon_singleton :

    ∀ i : Fin QON.baseCount, 3 ≤ i.val → Nat.card (QON.orbitPoints i) = 1 := by
  intro i hi
  have hi' : i.val < 29 := by have := i.isLt; have := qon_baseCount; omega
  rw [qon_card_orbit, List.getElem_append_right (by simp; omega), List.getElem_replicate]

theorem qon_base_get_l0 :
    QON.base.get (PairDecomp.l0 QON qon_three) = x0 := Fin.ext (by
  rw [cert_on_schreier_action_data.2.2.2.2.2.2.2.2.1]
  rfl)

theorem at_on_three_point_separating_base :
    Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) threeBase = ⊥ ∧
      (∀ H : Subgroup (Equiv.Perm (Fin N)), H ≤ Pv →
        H ⊓ fixingSubgroup (Equiv.Perm (Fin N)) threeBase = ⊥) ∧
      Nat.card (Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0} : Subgroup _) = 1876896 ∧
      Nat.card (QON.orbitPoints (PairDecomp.l1 QON qon_three)) = 52136 ∧
      Nat.card (QON.orbitPoints (PairDecomp.l2 QON qon_three)) = 36 ∧
      ∀ g ∈ Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0},
        ∃! yw : QON.orbitPoints (PairDecomp.l1 QON qon_three) ×
            QON.orbitPoints (PairDecomp.l2 QON qon_three),
          g = QON.orbitTransversal (PairDecomp.l1 QON qon_three) yw.1 *
            QON.orbitTransversal (PairDecomp.l2 QON qon_three) yw.2 := by
  refine ⟨pv_inf_fixing_three, fun H hH => eq_bot_iff.2 fun g hg => ?_, card_Pv_stab_zero,
    by rw [qon_card_orbit]; rfl, by rw [qon_card_orbit]; rfl, fun g hg => ?_⟩
  · rw [← pv_inf_fixing_three]
    exact ⟨hH hg.1, hg.2⟩
  · obtain ⟨hgP, hgfix⟩ := Subgroup.mem_inf.1 hg
    have hg0 : g x0 = x0 := by
      have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin N))).1 hgfix x0 rfl
      rwa [Equiv.Perm.smul_def] at this
    refine PairDecomp.exists_unique_pair QON qon_three qon_valid qon_singleton
      (by rw [qon_originalSubgroup]; exact hgP) ?_
    rw [qon_base_get_l0]
    exact hg0

end CFSG.ONSchreier
