module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43Enum
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43Count

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res6.U43P

open CFSG.LieType.Multipliers.U43

@[expose] def chkInv (w : ℕ) : Bool :=
  (List.range 3).all fun j => act w (act (invP w) (bpt j)) == bpt j

@[expose] def sortedLt : List ℕ → Bool
  | a :: b :: l => decide (a < b) && sortedLt (b :: l)
  | _ => true

theorem sortedLt_injective : ∀ {l : List ℕ}, sortedLt l = true → ∀ {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length), l[i] = l[j] → i = j := by
  intro l hl
  have hpw : l.Pairwise (· < ·) := by
    induction l with
    | nil => exact List.Pairwise.nil
    | cons a l ih =>
      cases l with
      | nil => exact List.pairwise_singleton _ _
      | cons b l =>
        simp only [sortedLt, Bool.and_eq_true, decide_eq_true_eq] at hl
        have ih' := ih hl.2
        refine List.Pairwise.cons ?_ ih'
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hl.1
        · exact hl.1.trans (List.rel_of_pairwise_cons ih' hc)
  intro i j hi hj h
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (ne_of_lt (List.pairwise_iff_getElem.mp hpw i j hi hj hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (List.pairwise_iff_getElem.mp hpw j i hj hi hgt))

@[simp] theorem bptF_val (j : ℕ) : (bptF j : ℕ) = bpt j := rfl

@[expose] noncomputable def bkey (g : X₀) : ℕ :=
  ((g • bptF 0 : Fin 820) : ℕ) * 1048576 + ((g • bptF 1 : Fin 820) : ℕ) * 1024 +
    ((g • bptF 2 : Fin 820) : ℕ)

section Base

theorem ev_invP (w : ℕ) (h : chkInv w = true) : ev (invP w) = (ev w)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right (eq_of_bpt fun j hj => ?_)
  simp only [chkInv, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [mul_smul, act_spec, act_spec, one_smul, bptF_val, h j hj]

end Base

@[expose] def keyConj (r w : ℕ) : ℕ :=
  act w (act r (act (invP w) 0)) * 1048576 + act w (act r (act (invP w) 1)) * 1024 +
    act w (act r (act (invP w) 9))

section Base

theorem keyConj_eq_bkey {r w : ℕ} (hw : chkInv w = true) :
    keyConj r w = bkey (ev w * ev r * (ev w)⁻¹) := by
  rw [← ev_invP w hw]
  simp only [bkey, mul_smul, act_spec, bptF_val, keyConj, bpt, ↓reduceIte, one_ne_zero,
    OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero]

end Base

@[expose] def chkConjList (r : ℕ) (ws : List ℕ) : Bool :=
  ws.all chkInv && sortedLt (ws.map (keyConj r))

section Base

theorem card_centralizer_mul_le_of_conjList {r : ℕ} {ws : List ℕ} (h : chkConjList r ws = true) :
    Nat.card (Subgroup.centralizer ({ev r} : Set X₀)) * ws.length ≤ Nat.card X₀ := by
  simp only [chkConjList, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hinv, hs⟩ := h
  refine card_centralizer_mul_le (ev r) (fun i : Fin ws.length => ev ws[(i : ℕ)])
    fun i j hij => ?_
  have hi := hinv _ (List.getElem_mem i.2)
  have hj := hinv _ (List.getElem_mem j.2)
  have hk : keyConj r ws[(i : ℕ)] = keyConj r ws[(j : ℕ)] := by
    rw [keyConj_eq_bkey hi, keyConj_eq_bkey hj, hij]
  have := sortedLt_injective hs (i := i) (j := j) (by simp) (by simp) (by simpa using hk)
  exact Fin.ext this

end Base

@[expose] def chkFixData (r : ℕ) (FL ωs hs : List ℕ) : Bool :=
  FL.all (· < 820) && (List.range 820).all (fun i => (act r i == i) == FL.contains i) &&
    sortedLt (ωs.map fun w => orFold (FL.map (act w))) &&
    hs.all (fun h => orFold (FL.map (act h)) == orFold FL && chkInv h) &&
    sortedLt (hs.map (keyConj r))

theorem act_lt (w : ℕ) (i : Fin 820) : act w i < 820 := by
  rw [← act_spec]
  exact Fin.isLt _

theorem smul_conj_eq_iff (g r : X₀) (q : Fin 820) :
    (g * r * g⁻¹) • q = q ↔ r • (g⁻¹ • q) = g⁻¹ • q := by
  rw [mul_smul, mul_smul]
  constructor
  · intro h
    have := congrArg (g⁻¹ • ·) h
    simpa using this
  · intro h
    rw [h, smul_inv_smul]

section Base

theorem card_centralizer_mul_le_of_fixData {r : ℕ} {FL ωs hs : List ℕ}
    (h : chkFixData r FL ωs hs = true) :
    Nat.card (Subgroup.centralizer ({ev r} : Set X₀)) * (ωs.length * hs.length) ≤
      Nat.card X₀ := by
  simp only [chkFixData, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hFL, hfix⟩, hω⟩, hh⟩, hhs⟩ := h
  have hfixF : ∀ q : Fin 820, ev r • q = q ↔ (q : ℕ) ∈ FL := by
    intro q
    have h1 := hfix q q.2
    rw [Fin.ext_iff, act_spec]
    constructor
    · intro e
      rw [e, beq_self_eq_true] at h1
      exact List.contains_iff_mem.mp h1.symm
    · intro e
      rw [List.contains_iff_mem.mpr e] at h1
      exact beq_iff_eq.mp h1
  have hstab : ∀ v ∈ hs, ∀ p : Fin 820, (p : ℕ) ∈ FL ↔ ((ev v • p : Fin 820) : ℕ) ∈ FL := by
    intro v hv p
    have hm := mem_iff_of_orFold_eq (hh v hv).1
    constructor
    · intro hp
      rw [act_spec, ← hm]
      exact List.mem_map_of_mem hp
    · intro hp
      rw [act_spec, ← hm] at hp
      obtain ⟨p', hp', e⟩ := List.mem_map.mp hp
      have hp'lt := hFL p' hp'
      have e' : ev v • (⟨p', hp'lt⟩ : Fin 820) = ev v • p := by
        apply Fin.ext
        rw [act_spec, act_spec]
        exact e
      rw [smul_left_cancel_iff] at e'
      rw [← e']
      exact hp'
  have hfixC : ∀ ω, ∀ v ∈ hs, ∀ q : Fin 820,
      ((ev ω * ev v) * ev r * (ev ω * ev v)⁻¹) • q = q ↔ (q : ℕ) ∈ FL.map (act ω) := by
    intro ω v hv q
    rw [smul_conj_eq_iff, hfixF, mul_inv_rev, mul_smul, hstab v hv ((ev v)⁻¹ • (ev ω)⁻¹ • q),
      smul_inv_smul]
    constructor
    · intro hq
      refine List.mem_map.mpr ⟨_, hq, ?_⟩
      rw [← act_spec, smul_inv_smul]
    · intro hq
      obtain ⟨p, hp, e⟩ := List.mem_map.mp hq
      have hplt := hFL p hp
      have e' : (ev ω)⁻¹ • q = ⟨p, hplt⟩ := by
        rw [inv_smul_eq_iff]
        apply Fin.ext
        rw [act_spec]
        exact e.symm
      rw [e']
      exact hp
  let f : Fin (ωs.length * hs.length) → X₀ := fun t =>
    ev ωs[((finProdFinEquiv.symm t).1 : ℕ)] * ev hs[((finProdFinEquiv.symm t).2 : ℕ)]
  refine card_centralizer_mul_le (ev r) f fun t t' htt => ?_
  apply finProdFinEquiv.symm.injective
  set a := finProdFinEquiv.symm t
  set a' := finProdFinEquiv.symm t'
  have htt' : (ev ωs[(a.1 : ℕ)] * ev hs[(a.2 : ℕ)]) * ev r *
      (ev ωs[(a.1 : ℕ)] * ev hs[(a.2 : ℕ)])⁻¹ =
      (ev ωs[(a'.1 : ℕ)] * ev hs[(a'.2 : ℕ)]) * ev r *
        (ev ωs[(a'.1 : ℕ)] * ev hs[(a'.2 : ℕ)])⁻¹ := htt
  have hv : hs[(a.2 : ℕ)] ∈ hs := List.getElem_mem _
  have hv' : hs[(a'.2 : ℕ)] ∈ hs := List.getElem_mem _
  have h1 : a.1 = a'.1 := by
    have hmem : ∀ b, b ∈ FL.map (act ωs[(a.1 : ℕ)]) ↔ b ∈ FL.map (act ωs[(a'.1 : ℕ)]) := by
      intro b
      by_cases hb : b < 820
      · have e1 := hfixC ωs[(a.1 : ℕ)] _ hv ⟨b, hb⟩
        have e2 := hfixC ωs[(a'.1 : ℕ)] _ hv' ⟨b, hb⟩
        rw [htt'] at e1
        exact e1.symm.trans e2
      · constructor <;> intro hm <;> obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm <;>
          exact absurd (act_lt _ ⟨p, hFL p hp⟩) hb
    have hk := orFold_eq_of_mem_iff hmem
    exact Fin.ext (sortedLt_injective hω (by simp) (by simp)
      (by simpa using hk))
  have h2 : a.2 = a'.2 := by
    have hc : ev hs[(a.2 : ℕ)] * ev r * (ev hs[(a.2 : ℕ)])⁻¹ =
        ev hs[(a'.2 : ℕ)] * ev r * (ev hs[(a'.2 : ℕ)])⁻¹ := by
      have e1 : ωs[(a'.1 : ℕ)] = ωs[(a.1 : ℕ)] :=
        congrArg (fun k : Fin ωs.length => ωs[(k : ℕ)]) h1.symm
      rw [e1] at htt'
      have := congrArg (fun y => (ev ωs[(a.1 : ℕ)])⁻¹ * y * ev ωs[(a.1 : ℕ)]) htt'
      simpa [mul_assoc] using this
    have hk : keyConj r hs[(a.2 : ℕ)] = keyConj r hs[(a'.2 : ℕ)] := by
      rw [keyConj_eq_bkey (hh _ hv).2, keyConj_eq_bkey (hh _ hv').2, hc]
    exact Fin.ext (sortedLt_injective hhs (by simp) (by simp)
      (by simpa using hk))
  exact Prod.ext h1 h2

end Base

@[expose] def chkCom (u r : ℕ) : Bool :=
  (List.range 3).all fun j => act u (act r (bpt j)) == act r (act u (bpt j))

@[expose] def chkInvolution (u : ℕ) : Bool :=
  (List.range 3).all (fun j => act u (act u (bpt j)) == bpt j) &&
    (List.range 3).any fun j => act u (bpt j) != bpt j

section Base

theorem mem_centralizer_of_chkCom {u r : ℕ} (h : chkCom u r = true) :
    ev u ∈ Subgroup.centralizer ({ev r} : Set X₀) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply eq_of_bpt
  intro j hj
  simp only [chkCom, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [mul_smul, mul_smul, act_spec, act_spec, act_spec, act_spec, bptF_val]
  exact h j hj

theorem orderOf_ev_of_chkInvolution {u : ℕ} (h : chkInvolution u = true) : orderOf (ev u) = 2 := by
  simp only [chkInvolution, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨h2, j, hj, hne⟩ := h
  have hsq : ev u ^ 2 = 1 := by
    apply eq_of_bpt
    intro j hj
    rw [pow_two, mul_smul, act_spec, act_spec, one_smul, bptF_val]
    exact h2 j hj
  have hne1 : ev u ≠ 1 := by
    intro e
    apply hne
    have h1 := act_spec u (bptF j)
    rw [e, one_smul, bptF_val] at h1
    exact h1.symm
  exact orderOf_eq_prime hsq hne1

end Base

namespace ETab

variable (T : ETab)

@[expose] def chkClass (p cls cw wj : ℕ) (reps : List ℕ) : Bool :=
  (List.range T.n).all fun k => k == 0 ||
    (if lk cls k = 0 then
      decide (lk wj k < 3) && ((T.actE k)^[p - 1] (T.b k (lk wj k)) != bpt (lk wj k))
    else
      decide (lk cls k ≤ reps.length) && chkInv (fld cw 64 k) &&
        (List.range 3).all fun j =>
          act (fld cw 64 k) (T.actE k (act (invP (fld cw 64 k)) (bpt j))) ==
            act (reps.getD (lk cls k - 1) 0) (bpt j))

theorem smul_elem_pow (k m : ℕ) (i : Fin 820) :
    ((T.elem k ^ m • i : Fin 820) : ℕ) = (T.actE k)^[m] i := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_smul, ih, Function.iterate_succ_apply, smul_elem]

section Base

theorem exists_conj_rep {p cls cw wj : ℕ} {reps : List ℕ} (hb : T.chkBase = true)
    (ht : T.chkTree = true) (hc : T.chkClass p cls cw wj reps = true) (hp : 1 ≤ p) {k : ℕ}
    (hk : k < T.n) (hk0 : k ≠ 0) (hpow : T.elem k ^ p = 1) :
    1 ≤ lk cls k ∧ lk cls k ≤ reps.length ∧
      ∃ c : X₀, c * T.elem k * c⁻¹ = ev (reps.getD (lk cls k - 1) 0) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [chkClass, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc k hk with h | h
  · exact absurd h hk0
  · by_cases hcl : lk cls k = 0
    · exfalso
      simp only [hcl, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
        Nat.add_sub_cancel] at h
      obtain ⟨hj, hne⟩ := h
      apply hne
      have e := T.smul_elem_pow k (q + 1) (bptF (lk wj k))
      rw [hpow, one_smul, bptF_val, Function.iterate_succ_apply] at e
      have e2 : T.actE k (bpt (lk wj k)) = T.b k (lk wj k) := by
        rw [← bptF_val, ← smul_elem, T.smul_elem_bpt hb ht hk hj]
      rw [e2] at e
      exact e.symm
    · simp only [hcl, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range, beq_iff_eq] at h
      obtain ⟨⟨hle, hinv⟩, hconj⟩ := h
      refine ⟨Nat.one_le_iff_ne_zero.mpr hcl, hle, ev (fld cw 64 k), ?_⟩
      apply eq_of_bpt
      intro j hj
      rw [← ev_invP _ hinv, mul_smul, mul_smul, act_spec, smul_elem, act_spec, act_spec,
        bptF_val]
      exact hconj j hj

end Base

@[expose] def chkComIdx (r : ℕ) (ks : List ℕ) : Bool :=
  sortedLt ks && ks.all fun k => decide (k < T.n) &&
    (List.range 3).all fun j => T.actE k (act r (bpt j)) == act r (T.b k j)

@[expose] def chkComGens (r : ℕ) : Bool :=
  (List.range T.gens.length).all fun i => chkCom (T.gw i) r

section Base

theorem le_card_inf_centralizer {r : ℕ} {ks : List ℕ} (hb : T.chkBase = true)
    (ht : T.chkTree = true) (hs : T.chkSorted = true) (hc : T.chkComIdx r ks = true) :
    ks.length ≤ Nat.card (T.H ⊓ Subgroup.centralizer ({ev r} : Set X₀) : Subgroup X₀) := by
  simp only [chkComIdx, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    beq_iff_eq] at hc
  obtain ⟨hsort, hks⟩ := hc
  have hmem : ∀ i : Fin ks.length, T.elem ks[(i : ℕ)] ∈
      (T.H ⊓ Subgroup.centralizer ({ev r} : Set X₀) : Subgroup X₀) := by
    intro i
    obtain ⟨hlt, hcom⟩ := hks _ (List.getElem_mem i.2)
    refine Subgroup.mem_inf.mpr ⟨T.elem_mem ht hlt, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply eq_of_bpt
    intro j hj
    rw [mul_smul, mul_smul, smul_elem, act_spec, act_spec, T.smul_elem_bpt hb ht hlt hj,
      bptF_val]
    exact hcom j hj
  have hinj : Function.Injective fun i : Fin ks.length =>
      (⟨T.elem ks[(i : ℕ)], hmem i⟩ : (T.H ⊓ Subgroup.centralizer ({ev r} : Set X₀) :
        Subgroup X₀)) := by
    intro i i' h
    have e := congrArg Subtype.val h
    have hi := (hks _ (List.getElem_mem i.2)).1
    have hi' := (hks _ (List.getElem_mem i'.2)).1
    exact Fin.ext (sortedLt_injective hsort i.2 i'.2 (T.elem_injOn hb ht hs hi hi' e))
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := Fin ks.length), Fintype.card_fin] at this

theorem H_le_centralizer {r : ℕ} (hc : T.chkComGens r = true) :
    T.H ≤ Subgroup.centralizer ({ev r} : Set X₀) := by
  rw [H, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  simp only [chkComGens, List.all_eq_true, List.mem_range] at hc
  exact mem_centralizer_of_chkCom (hc i hi)

end Base

end ETab

end CFSG.RankThree.PartTwo.Sec6.Res611Res6.U43P
