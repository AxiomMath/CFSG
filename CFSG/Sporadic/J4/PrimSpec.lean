module

public import CFSG.Sporadic.J4.StabSpec
public import CFSG.Sporadic.J4.LocalOrder
import Certificates.Data.CFSGNative.J4.Orbit
import Certificates.Data.CFSGNative.J4.Suborbits
import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.Sporadic.J4

open Native CFSG.Sporadic.Th

theorem isPreprimitive_of_labels {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    [DecidableEq X] [MulAction.IsPretransitive G X] (x : X) (H : Subgroup G)
    (hH : ∀ h ∈ H, h • x = x) {k : ℕ} (lab : X → Fin k)
    (horb : ∀ p q : X, lab p = lab q → ∃ h ∈ H, h • p = q)
    (hdiv : ∀ S : Finset (Fin k), lab x ∈ S →
      (∑ i ∈ S, (Finset.univ.filter (fun p => lab p = i)).card) ∣ Fintype.card X →
      S = {lab x} ∨ S = Finset.univ) :
    MulAction.IsPreprimitive G X := by
  classical
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base x fun {B} hxB hB => ?_
  have hclosed : ∀ p q : X, p ∈ B → lab p = lab q → q ∈ B := by
    intro p q hp hpq
    obtain ⟨h, hh, rfl⟩ := horb p q hpq
    have hhx : h • x ∈ B := by
      rw [hH h hh]
      exact hxB
    rw [← hB.smul_eq_of_mem hxB hhx]
    exact Set.smul_mem_smul_set hp
  let S : Finset (Fin k) := (Finset.univ.filter (· ∈ B)).image lab
  have hmemS : ∀ p, lab p ∈ S ↔ p ∈ B := by
    intro p
    constructor
    · intro hp
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
      exact hclosed q p (Finset.mem_filter.mp hq).2 hqp
    · intro hp
      exact Finset.mem_image_of_mem lab (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩)
  have hBS : B = ↑(Finset.univ.filter fun p => lab p ∈ S) := by
    ext p
    rw [Finset.mem_coe, Finset.mem_filter, hmemS]
    exact ⟨fun hp => ⟨Finset.mem_univ p, hp⟩, fun hp => hp.2⟩
  have hdvd : (∑ i ∈ S, (Finset.univ.filter (fun p => lab p = i)).card) ∣ Fintype.card X := by
    rw [Finset.sum_card_fiberwise_eq_card_filter, ← Set.ncard_coe_finset, ← hBS,
      ← Nat.card_eq_fintype_card]
    exact hB.ncard_dvd_card ⟨x, hxB⟩
  rcases hdiv S ((hmemS x).mpr hxB) hdvd with hS | hS
  · left
    have hx : ∀ r ∈ B, r = x := by
      intro r hr
      have hr' : lab r ∈ S := (hmemS r).mpr hr
      rw [hS, Finset.mem_singleton] at hr'
      obtain ⟨h, hh, hhr⟩ := horb x r hr'.symm
      rw [← hhr, hH h hh]
    intro p hp q hq
    rw [hx p hp, hx q hq]
  · right
    ext p
    refine ⟨fun _ => Set.mem_univ p, fun _ => (hmemS p).mp ?_⟩
    rw [hS]
    exact Finset.mem_univ (lab p)

theorem countLab_get (L : Labels) (k : ℕ) :
    ∀ n, (countLab n k L).size = k ∧ ∀ i < k,
      (countLab n k L)[i]! = ((Finset.range n).filter (fun p => L.labelOf p = i)).card := by
  intro n
  induction n with
  | zero =>
    refine ⟨by simp [countLab], fun i hi => ?_⟩
    simp only [countLab, Nat.fold_zero, Finset.range_zero, Finset.filter_empty, Finset.card_empty]
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_replicate]
  | succ n ih =>
    obtain ⟨hs, hg⟩ := ih
    have e : countLab (n + 1) k L = (countLab n k L).modify (L.labelOf n) (· + 1) := by
      simp only [countLab, Nat.fold_succ]
    refine ⟨by rw [e, Array.size_modify, hs], fun i hi => ?_⟩
    rw [e, getElem!_pos _ i (by rw [Array.size_modify, hs]; exact hi), Array.getElem_modify,
      Finset.range_add_one, Finset.filter_insert]
    have hn : n ∉ (Finset.range n).filter (fun p => L.labelOf p = i) := by simp
    by_cases h : L.labelOf n = i
    · rw [ite_eq_left h, ite_eq_left h, Finset.card_insert_of_notMem hn, ← hg i hi,
        getElem!_pos _ i (by rw [hs]; exact hi)]
    · rw [ite_eq_right h, ite_eq_right h, ← hg i hi, getElem!_pos _ i (by rw [hs]; exact hi)]

@[expose] def subSizesF : Fin 7 → ℕ := ![1, 32643072, 82575360, 54405120, 3400320, 15180, 28336]

theorem subSizesF_blocks (S : Finset (Fin 7)) (h0 : (0 : Fin 7) ∈ S)
    (hd : (∑ i ∈ S, subSizesF i) ∣ 173067389) : S = {0} ∨ S = Finset.univ := by
  rw [← Finset.univ_inter S, ← Finset.sum_ite_mem, Fin.sum_univ_seven] at hd
  simp only [subSizesF, h0, ite_true] at hd
  split_ifs at hd with h1 h2 h3 h4 h5 h6
  all_goals first | (exfalso; norm_num at hd; done) | skip
  · right
    exact Finset.eq_univ_of_forall fun i => by fin_cases i <;> assumption
  · left
    exact Finset.eq_singleton_iff_unique_mem.2 ⟨h0, fun i hi => by fin_cases i <;> simp_all⟩

@[expose] noncomputable def lab7 (p : Fin nPts) : Fin 7 := ⟨min (L0.labelOf p.val) 6, by omega⟩

section Facts

variable (hF : J4NativeFacts)
include hF

theorem label_parts : ∀ p < nPts, labelAt nPts (zT 0) (zT 1) (zT 2) L0 p = true :=
  parAllS_eq_true hF.label

theorem reps_eq : L0.reps = subReps := beq_iff_eq.mp hF.reps

theorem labelOf_lt {p : ℕ} (hp : p < nPts) : L0.labelOf p < 7 := by
  have h := label_parts hF p hp
  unfold labelAt at h
  rw [Bool.and_eq_true, decide_eq_true_eq, reps_eq hF] at h
  exact h.1

theorem lab7_val (p : Fin nPts) : (lab7 p).val = L0.labelOf p.val := by
  have := labelOf_lt hF p.isLt
  simp only [lab7]
  omega

omit hF in
theorem letterG_xJ_mem (l : ℕ) : letterG (xJ 0) (xJ 1) (xJ 2) l ∈ Hj := by
  unfold letterG
  split_ifs <;> exact xJ_mem (by norm_num)

theorem reach_rep : ∀ d p, p < nPts → depOf L0.dep p = d →
    ∃ h ∈ Hj, idx nPts h subReps[L0.labelOf p]! = p := by
  have hz := RepT.letter3 (rep_z hF (k := 0) (by norm_num)) (rep_z hF (k := 1) (by norm_num))
    (rep_z hF (k := 2) (by norm_num))
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro p hp hd
    have h := label_parts hF p hp
    unfold labelAt at h
    rw [Bool.and_eq_true] at h
    obtain ⟨-, h⟩ := h
    split_ifs at h with h0
    · rw [beq_iff_eq, reps_eq hF] at h
      exact ⟨1, Hj.one_mem, by rw [idx_one, h]⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨hp0, -⟩, -⟩, hzp⟩, hlab⟩, hdep⟩ := h
      rw [beq_iff_eq] at h0
      obtain ⟨g, hg, hgp⟩ := ih _ (by omega) _ hp0 rfl
      refine ⟨letterG (xJ 0) (xJ 1) (xJ 2) (labOf L0.par p) * g,
        Hj.mul_mem (letterG_xJ_mem _) hg, ?_⟩
      rw [idx_mul, ← hlab, hgp, ← hz _ _ hp0, hzp]

theorem lab7_orb (p q : Fin nPts) (h : lab7 p = lab7 q) : ∃ g ∈ Hj, g • p = q := by
  obtain ⟨gp, hgp, ep⟩ := reach_rep hF _ p.val p.isLt rfl
  obtain ⟨gq', hgq, eq⟩ := reach_rep hF _ q.val q.isLt rfl
  have hl : L0.labelOf p.val = L0.labelOf q.val := by rw [← lab7_val hF, ← lab7_val hF, h]
  refine ⟨gq' * gp⁻¹, Hj.mul_mem hgq (Hj.inv_mem hgp), Fin.ext ?_⟩
  rw [val_smul, idx_mul]
  have e := idx_inv_idx (n := nPts) gp subReps[L0.labelOf p.val]!
  rw [ep] at e
  rw [e, hl, eq]

theorem lab7_root : lab7 (root0 hF) = 0 := by
  obtain ⟨g, hg, eg⟩ := reach_rep hF _ 0 (nPts_pos hF) rfl
  have e := idx_inv_idx (n := nPts) g subReps[L0.labelOf 0]!
  rw [eg, idx_Hj hF (Hj.inv_mem hg)] at e
  apply Fin.ext
  rw [lab7_val hF]
  show L0.labelOf 0 = 0
  have hl := labelOf_lt hF (nPts_pos hF)
  revert e
  interval_cases L0.labelOf 0 <;> intro e <;> first | rfl | exact absurd e (by decide)

theorem card_lab7 (i : Fin 7) :
    (Finset.univ.filter (fun p : Fin nPts => lab7 p = i)).card = subSizesF i := by
  have hc := (countLab_get L0 7 nPts).2 i.val i.isLt
  have hcnt : (countLab nPts 7 L0).toList = subSizes := beq_iff_eq.mp hF.counts
  have hsz := (countLab_get L0 7 nPts).1
  have e1 : (countLab nPts 7 L0)[i.val]! = subSizesF i := by
    have hi : i.val < (countLab nPts 7 L0).toList.length := by
      rw [Array.length_toList, hsz]; exact i.isLt
    rw [getElem!_pos _ _ (by rw [hsz]; exact i.isLt), ← Array.getElem_toList hi,
      List.getElem_of_eq hcnt hi]
    fin_cases i <;> rfl
  rw [← e1, hc]
  apply Finset.card_bij (fun p _ => p.val)
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_range.2 p.isLt, by rw [← lab7_val hF, hp.2]⟩
  · intro p _ q _ h
    exact Fin.ext h
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_range] at hb
    refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Fin.ext (by rw [lab7_val hF]; exact hb.2)⟩

theorem isPretransitive_J : MulAction.IsPretransitive J (Fin nPts) := by
  refine ⟨fun x y => ⟨trans y.val * (trans x.val)⁻¹, Fin.ext ?_⟩⟩
  rw [val_smul, idx_mul]
  have e := idx_inv_idx (n := nPts) (trans x.val) 0
  rw [idx_trans hF x.isLt] at e
  rw [e, idx_trans hF y.isLt]

theorem isPreprimitive_J : MulAction.IsPreprimitive J (Fin nPts) := by
  have := isPretransitive_J hF
  classical
  refine isPreprimitive_of_labels (root0 hF) Hj (fun h hh => Hj_le_stabilizer hF hh) lab7
    (lab7_orb hF) fun S hS hdvd => ?_
  rw [lab7_root hF] at hS ⊢
  have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : Fin nPts => lab7 p = i)).card) =
      ∑ i ∈ S, subSizesF i := Finset.sum_congr rfl fun i _ => card_lab7 hF i
  rw [hsum, Fintype.card_fin] at hdvd
  exact subSizesF_blocks S hS hdvd

theorem faithful_J : FaithfulSMul J (Fin nPts) := by
  refine ⟨fun {g₁ g₂} h => ?_⟩
  have hfix : ∀ p < nPts, idx nPts (g₂⁻¹ * g₁) p = p := by
    intro p hp
    have := h ⟨p, hp⟩
    rw [idx_of_lt _ hp, mul_smul, this, inv_smul_smul]
  have e : g₂⁻¹ * g₁ = 1 :=
    eq_one_of_fix_qIdx0 hF (hfix 0 (nPts_pos hF)) fun t ht => hfix _ (qIdx0_lt hF t ht)
  rw [← mul_left_cancel_iff (a := g₂⁻¹), e, inv_mul_cancel]

end Facts

end CFSG.Sporadic.J4
