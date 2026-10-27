module

public import CFSG.Sporadic.Fi23.Simple

public section

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem stabilizer_root_eq_centralizer :
    MulAction.stabilizer J root = Subgroup.centralizer ({d} : Set J) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff, smul_eq_iff]
  show g * conjPt 0 * g⁻¹ = conjPt 0 ↔ g * d = d * g
  rw [conjPt_zero]
  constructor
  · intro h
    calc g * d = g * d * g⁻¹ * g := by rw [inv_mul_cancel_right]
      _ = d * g := by rw [h]
  · intro h
    rw [h, mul_inv_cancel_right]

theorem card_centralizer_d :
    Nat.card (Subgroup.centralizer ({d} : Set J)) = 129123503308800 := by
  rw [← stabilizer_root_eq_centralizer, card_stabilizer_root]

theorem commute_of_mem_lvl_one
    {h : J} (hh : h ∈ lvl 1) : h * d * h⁻¹ = d := by
  rw [← stabilizer_root] at hh
  rw [stabilizer_root_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hh
  rw [hh, mul_inv_cancel_right]

theorem productChecks_eq :
    productChecks orb = true := certificate_parts.2.2.2

theorem keys_canon
    {k : ℕ} (hk : k < 31671) : canonW 253 orb.keys[k]! = true :=
  conjFacts.canon k (by rw [orb_size]; exact hk)

theorem rowsWF_keys
    {k : ℕ} (hk : k < 31671) : RowsWF (toVM orb.keys[k]!) :=
  RowsWF.of_canonM (canonM_of_canonW (by norm_num) (by norm_num) (keys_canon hk))

theorem mat_d_mul_conjPt {k : ℕ} (hk : k < 31671) :
    mat (d * conjPt k) = toMatW 253 (mulW 253 matD orb.keys[k]!) := by
  rw [mat_mul, mat_d, conjPt_mat k (by rw [orb_size]; exact hk),
    toMatW_mulW matD_facts.1 matD_facts.2.1 (rowsWF_keys hk)]

theorem canonW_idW : canonW 253 (idW 253) = true := by
  have h := certificate_parts.1
  unfold matrixChecks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hI⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact hI

theorem orderOf_of_product {k e : ℕ} [Fact e.Prime] (hk : k < 31671)
    (hpow : eqW 253 (powW 253 (mulW 253 matD orb.keys[k]!) e) (idW 253) = true)
    (hne : eqW 253 (mulW 253 matD orb.keys[k]!) (idW 253) = false)
    (hc : canonW 253 (mulW 253 matD orb.keys[k]!) = true) : orderOf (d * conjPt k) = e := by
  have hw : RowsWF (toVM (mulW 253 matD orb.keys[k]!)) :=
    RowsWF.mulW matD_facts.2.1 (rowsWF_keys hk)
  have hs : (mulW 253 matD orb.keys[k]!).size = 253 := by rw [mulW_size, matD_facts.1]
  apply orderOf_eq_prime
  · apply mat_injective
    rw [mat_pow, mat_one, mat_d_mul_conjPt hk, ← toMatW_powW hw, toMatW_eq_of_eqW hpow,
      toMatW_idW]
  · intro h
    apply toMatW_ne_of_eqW hs hne hc canonW_idW
    rw [← mat_d_mul_conjPt hk, h, mat_one, toMatW_idW]

theorem orderOf_d_mul_conjPt_one : orderOf (d * conjPt 1) = 2 := by
  have h := productChecks_eq
  unfold productChecks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, -⟩, -⟩ := h
  exact orderOf_of_product (by norm_num) h3 h4 h1

theorem orderOf_d_mul_conjPt_two : orderOf (d * conjPt 2) = 3 := by
  have h := productChecks_eq
  unfold productChecks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, h5⟩, h6⟩ := h
  exact orderOf_of_product (by norm_num) h5 h6 h2

theorem orderOf_conj
    (g x : J) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem orderOf_d_mul_conjPt_smul
    {h : J} (hh : h ∈ lvl 1) (p : Fin 31671) :
    orderOf (d * conjPt (h • p).val) = orderOf (d * conjPt p.val) := by
  rw [conjPt_smul]
  conv_lhs => rw [← commute_of_mem_lvl_one hh]
  rw [show h * d * h⁻¹ * (h * conjPt p.val * h⁻¹) = h * (d * conjPt p.val) * h⁻¹ by group,
    orderOf_conj]

theorem subLab_one_pt : subLab (⟨1, by norm_num⟩ : Fin 31671) = 1 :=
  subLab_eq_one.2 (MulAction.mem_orbit_self _)

theorem subLab_two_pt :
    subLab (⟨subRoot, treeFacts_two.r_lt⟩ : Fin 31671) = 2 := by
  have hpos : 0 < (Finset.univ.filter (fun p : Fin 31671 => subLab p = 2)).card := by
    rw [card_subLab_two]; norm_num
  obtain ⟨q, hq⟩ := Finset.card_pos.1 hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  obtain ⟨⟨h, hh⟩, hhq⟩ := two_mem_orbit hq
  have := subLab_inv h hh ⟨subRoot, treeFacts_two.r_lt⟩
  change subLab (h • _) = _ at this
  rw [show (h • (⟨subRoot, treeFacts_two.r_lt⟩ : Fin 31671)) = q from hhq, hq] at this
  exact this.symm

theorem orderOf_d_mul_conjPt (p : Fin 31671) :
    orderOf (d * conjPt p.val) = if p = root then 1 else if subLab p = 1 then 2 else 3 := by
  by_cases h0 : p = root
  · rw [ite_eq_left h0, h0]
    show orderOf (d * conjPt 0) = 1
    rw [conjPt_zero, d_sq, orderOf_one]
  rw [ite_eq_right h0]
  by_cases h1 : subLab p = 1
  · rw [ite_eq_left h1]
    obtain ⟨h, hh, hp⟩ := subLab_orb _ p (subLab_one_pt.trans h1.symm)
    rw [← hp, orderOf_d_mul_conjPt_smul hh]
    exact orderOf_d_mul_conjPt_one
  · rw [ite_eq_right h1]
    have h2 : subLab p = 2 := by
      have h0' := subLab_eq_zero.not.2 h0
      have hcases : subLab p = 0 ∨ subLab p = 1 ∨ subLab p = 2 := by
        rcases subLab p with ⟨_ | _ | _ | n, hn⟩
        · left; rfl
        · right; left; rfl
        · right; right; rfl
        · omega
      rcases hcases with h | h | h
      · exact absurd h h0'
      · exact absurd h h1
      · exact h
    obtain ⟨h, hh, hp⟩ := subLab_orb _ p (subLab_two_pt.trans h2.symm)
    rw [← hp, orderOf_d_mul_conjPt_smul hh]
    exact orderOf_d_mul_conjPt_two

theorem isConj_d_iff
    (x : J) : IsConj d x ↔ ∃ i : Fin 31671, conjPt i.val = x := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g • root, ?_⟩
    rw [conjPt_smul]
    show g * conjPt 0 * g⁻¹ = g * d * g⁻¹
    rw [conjPt_zero]
  · rintro ⟨i, rfl⟩
    have hi : conjPt i.val ∈ MulAction.orbit (ConjAct J) d := by
      rw [orbit_eq]; exact ⟨i.val, by rw [Set.mem_Iio, orb_size]; exact i.isLt, rfl⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hi
    exact ⟨ConjAct.ofConjAct g, by rw [← hg, ConjAct.smul_def]⟩

theorem orderOf_mul_of_isConj
    {x z : J} (hx : IsConj d x) (hz : IsConj d z) :
    orderOf (x * z) = 1 ∨ orderOf (x * z) = 2 ∨ orderOf (x * z) = 3 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  have hz' : IsConj d (g⁻¹ * z * g⁻¹⁻¹) := hz.trans (isConj_iff.2 ⟨g⁻¹, rfl⟩)
  obtain ⟨i, hi⟩ := (isConj_d_iff _).1 hz'
  have e : g * d * g⁻¹ * z = g * (d * conjPt i.val) * g⁻¹ := by
    rw [hi]; group
  rw [e, orderOf_conj, orderOf_d_mul_conjPt]
  split_ifs <;> simp

theorem closure_conjugates :
    Subgroup.closure {x : J | IsConj d x} = ⊤ := by
  have := isSimpleGroup_J
  have hN : (Subgroup.normalClosure ({d} : Set J)).Normal := Subgroup.normalClosure_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({d} : Set J)) with
    h | h
  · exfalso
    apply d_ne_one
    have := Subgroup.subset_normalClosure (Set.mem_singleton d)
    rw [h] at this
    exact this
  · rw [← h]
    unfold Subgroup.normalClosure
    congr 1
    ext x
    simp [Group.mem_conjugatesOfSet_iff]

theorem card_class_d : Nat.card {x : J // IsConj d x} = 31671 := by
  rw [← Nat.card_fin 31671]
  refine (Nat.card_congr (ptEquiv.trans (Equiv.subtypeEquivRight fun x => ?_))).symm
  rw [isConj_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.ofConjAct g, by rw [ConjAct.smul_def]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.toConjAct g, by rw [toConjAct_smul_eq]⟩

end CFSG.Sporadic.Fi23
