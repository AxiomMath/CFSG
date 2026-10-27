module

public import CFSG.Sporadic.Co1Patterson.AmalgamInnerElem

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.InnerNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
  CFSG.Sporadic.Co1Patterson.TwistNative CFSG.Sporadic.Co1Patterson.Native
open CFSG.Blueprint (NativeSporadic.Co1)

local macro "CA" : term => `(centralizer ({aNC} : Set NativeSporadic.Co1))

theorem imp_of_not_or {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  cases a <;> cases b <;> simp_all

theorem of_bne_or {X Y : Native.Rows} {c : Bool} (h : (X != Y || c) = true) (e : X = Y) :
    c = true := by
  subst e
  simpa using h

@[expose] noncomputable def tSubE (b S : ℕ) : CA :=
  (List.range 6).foldl (fun acc j => if S.testBit j then acc * tE (b + j) else acc) 1

theorem rep_tSubE (b S : ℕ) : MRep (tSub b S) (centEmb (tSubE b S)) := by
  rw [tSubE, map_foldl_if, map_one, tSub]
  exact rep_foldl_if _ _ _ _ (fun j _ => rep_tE (b + j)) MRep.one

theorem tSubE_mem {F : Subgroup CA} {b : ℕ} (hT : ∀ j < 6, tE (b + j) ∈ F) (S : ℕ) :
    tSubE b S ∈ F :=
  foldl_if_mem _ _ _ (fun j hj => hT j (List.mem_range.1 hj)) (one_mem _)

theorem rep_of_mem_vRows : ∀ W ∈ vRows, ∃ v ∈ vSub, MRep W (centEmb v) := by
  intro W hW
  simp only [vRows, List.mem_cons, List.not_mem_nil, or_false] at hW
  rcases hW with rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, rep_one'⟩
  · exact ⟨_, mem_vSub.2 (Or.inr (Or.inl rfl)), rep_z'⟩
  · exact ⟨_, mem_vSub.2 (Or.inr (Or.inr (Or.inl rfl))), rep_w'⟩
  · exact ⟨_, mem_vSub.2 (Or.inr (Or.inr (Or.inr rfl))), rep_wz'⟩

theorem innerGenOK_parts :
    (∀ p ∈ aList, ∃ S < 64, ∃ W ∈ vRows, Native.mul (tSub 0 S) W = aRowOf p) ∧
    (∀ i < 6, ∃ S < 64, ∃ p ∈ aList,
      Native.mul (tSub 6 S) (aRowOf p) = twRow (hIdx.getD i 0)) ∧
    ∀ i < 12, ∀ j < 12,
      (vRows.any fun v => Native.mul (tRow i) (tRow j) ==
        Native.mul v (Native.mul (tRow j) (tRow i))) = true := by
  have h := inner_gen_check
  simp only [innerGenOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_map,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun p hp => ?_, fun i hi => ?_, fun i hi j hj => ?_⟩
  · obtain ⟨t, ⟨S, hS, rfl⟩, W, hW, e⟩ := h1 p hp
    exact ⟨S, hS, W, hW, e⟩
  · obtain ⟨t, ⟨S, hS, rfl⟩, p, hp, e⟩ := h2 i hi
    exact ⟨S, hS, p, hp, e⟩
  · obtain ⟨W, hW, e⟩ := h3 _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact List.any_eq_true.2 ⟨W, hW, beq_iff_eq.2 e⟩

theorem rep_hH {i : ℕ} (hi : i < 6) : MRep (twRow (hIdx.getD i 0)) (centEmb (hH i)) := by
  rw [centEmb_hH hi]
  exact rep_twG _

theorem R₀_le_of_tE_mem (F : Subgroup CA) (hV : vSub ≤ F) (hT : ∀ j < 12, tE j ∈ F) :
    R₀ ≤ F := by
  have ha : ∀ p ∈ aList, aElt p ∈ F := by
    intro p hp
    obtain ⟨S, -, W, hW, e⟩ := innerGenOK_parts.1 p hp
    obtain ⟨v, hv, hWv⟩ := rep_of_mem_vRows W hW
    have h1 : MRep (Native.mul (tSub 0 S) W) (centEmb (tSubE 0 S * v)) := by
      rw [map_mul]
      exact (rep_tSubE 0 S).mul hWv
    rw [e] at h1
    rw [show aElt p = tSubE 0 S * v from centEmb_injective ((rep_aElt p).eq h1)]
    exact mul_mem (tSubE_mem (fun j hj => hT _ (by omega)) S) (hV hv)
  have hh : ∀ i < 6, hH i ∈ F := by
    intro i hi
    obtain ⟨S, -, p, hp, e⟩ := innerGenOK_parts.2.1 i hi
    have h1 : MRep (Native.mul (tSub 6 S) (aRowOf p)) (centEmb (tSubE 6 S * aElt p)) := by
      rw [map_mul]
      exact (rep_tSubE 6 S).mul (rep_aElt p)
    rw [e] at h1
    rw [show hH i = tSubE 6 S * aElt p from centEmb_injective ((rep_hH hi).eq h1)]
    exact mul_mem (tSubE_mem (fun j hj => hT _ (by omega)) S) (ha p hp)
  intro r hr
  obtain ⟨c, -, p, hp, rfl⟩ := mem_R₀_iff.1 hr
  exact mul_mem (foldl_if_mem _ _ _ (fun i hi => hh i (List.mem_range.1 hi)) (one_mem _))
    (ha p hp)

theorem innerLoopOK_parts : ∀ c < 64, ∀ p ∈ aList,
    loopAt ((List.range 12).map tRow) (kWordR (stabWords.getD 0 []))
      (kWordR (stabWords.getD 1 [])) (kRow 1) c p (Native.mul (hprodRow c) (aRowOf p)) = true := by
  intro c hc p hp
  have h := inner_loop_check
  rw [innerLoopOK] at h
  have h1 := List.all_eq_true.1 h c (List.mem_range.2 hc)
  exact List.all_eq_true.1 h1 (p, aRowOf p) (List.mem_map.2 ⟨p, hp, rfl⟩)

theorem yprodH_zero : yprodH 0 = 1 := by
  apply centEmb_injective
  rw [centEmb_yprodH, map_one]
  simp [yprodG]

theorem mem_vSub_of_isVPar {c : ℕ} {p : ℕ × ℕ} (hp : p ∈ aList) (h : isVPar c p = true) :
    hcH c * aElt p ∈ vSub := by
  simp only [isVPar, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨rfl, h1⟩ := h
  obtain ⟨-, -, h2⟩ := mem_aList.1 hp
  obtain ⟨c, d⟩ := p
  simp only at h1 h2
  rw [hcH_zero, one_mul]
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · rw [aElt, ite_eq_right (by norm_num), yprodH_zero]
    exact one_mem _
  · rw [aElt, ite_eq_left rfl, yprodH_zero, one_mul]
    exact mem_vSub.2 (Or.inr (Or.inl rfl))
  · rw [aElt, ite_eq_right (by norm_num), ← yH_zero_eq]
    exact mem_vSub.2 (Or.inr (Or.inr (Or.inl rfl)))
  · rw [aElt, ite_eq_left rfl, ← yH_zero_eq]
    exact mem_vSub.2 (Or.inr (Or.inr (Or.inr rfl)))

theorem exists_rows {r : CA} (hr : r ∈ R₀) :
    ∃ c < 64, ∃ p ∈ aList, r = hcH c * aElt p ∧
      MRep (Native.mul (hprodRow c) (aRowOf p)) (centEmb r) ∧
      CFSG.Sporadic.Co1.InvNative.validRows (Native.mul (hprodRow c) (aRowOf p)) = true ∧
      loopAt ((List.range 12).map tRow) (kWordR (stabWords.getD 0 []))
        (kWordR (stabWords.getD 1 [])) (kRow 1) c p
        (Native.mul (hprodRow c) (aRowOf p)) = true := by
  obtain ⟨c, hc, p, hp, rfl⟩ := mem_R₀_iff.1 hr
  refine ⟨c, hc, p, hp, rfl, ?_, valid_mul (valid_hprodRow c) (valid_aRowOf (mem_aList.1 hp).1),
    innerLoopOK_parts c hc p hp⟩
  rw [map_mul]
  exact (rep_hcH c).mul (rep_aElt p)

theorem comm_tE_tE {i j : ℕ} (hi : i < 12) (hj : j < 12) :
    ∃ v ∈ vSub, tE i * tE j = v * (tE j * tE i) := by
  have hij : MRep (Native.mul (tRow i) (tRow j)) (centEmb (tE i * tE j)) := by
    rw [map_mul]; exact (rep_tE i).mul (rep_tE j)
  have hji : MRep (Native.mul (tRow j) (tRow i)) (centEmb (tE j * tE i)) := by
    rw [map_mul]; exact (rep_tE j).mul (rep_tE i)
  exact exists_of_any hij hji (innerGenOK_parts.2.2 i hi j hj)

theorem mem_vSub_of_comm {r : CA} (hr : r ∈ R₀) (h : ∀ j < 12, r * tE j = tE j * r) :
    r ∈ vSub := by
  obtain ⟨c, -, p, hp, rfl, hR, vR, hL⟩ := exists_rows hr
  simp only [loopAt, Bool.and_eq_true] at hL
  refine mem_vSub_of_isVPar hp (imp_of_not_or hL.1.1 ?_)
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
  have hj' := List.mem_range.1 hj
  have hrt : MRep (Native.mul (Native.mul (hprodRow c) (aRowOf p)) (tRow j))
      (centEmb (hcH c * aElt p * tE j)) := by rw [map_mul]; exact hR.mul (rep_tE j)
  have htr : MRep (Native.mul (tRow j) (Native.mul (hprodRow c) (aRowOf p)))
      (centEmb (tE j * (hcH c * aElt p))) := by rw [map_mul]; exact (rep_tE j).mul hR
  exact (rows_beq_iff hrt htr (valid_mul vR (valid_tRow j)) (valid_mul (valid_tRow j) vR)).2
    (congrArg centEmb (h j hj'))

theorem mem_vSub_of_fix {r : CA} (hr : r ∈ R₀) (h : ∃ v ∈ vSub, r * kH 1 = v * (kH 1 * r)) :
    r ∈ vSub := by
  obtain ⟨c, -, p, hp, rfl, hR, vR, hL⟩ := exists_rows hr
  simp only [loopAt, Bool.and_eq_true] at hL
  refine mem_vSub_of_isVPar hp (imp_of_not_or hL.1.2 ?_)
  have hk := rep_kH (j := 1) (by norm_num)
  have vk := (innerElemOK_parts.1 1 (by norm_num)).1
  have hrx : MRep (Native.mul (Native.mul (hprodRow c) (aRowOf p)) (kRow 1))
      (centEmb (hcH c * aElt p * kH 1)) := by rw [map_mul]; exact hR.mul hk
  have hxr : MRep (Native.mul (kRow 1) (Native.mul (hprodRow c) (aRowOf p)))
      (centEmb (kH 1 * (hcH c * aElt p))) := by rw [map_mul]; exact hk.mul hR
  exact any_of_exists hrx hxr (valid_mul vR vk) (valid_mul vk vR) h

theorem stab_uniq {r : CA} (hr : r ∈ R₀)
    (h₁ : ∃ v ∈ vSub, kW (stabWords.getD 0 []) * r = v * (r * kW (stabWords.getD 0 [])))
    (h₂ : ∃ v ∈ vSub, kW (stabWords.getD 1 []) * r = v * (r * kW (stabWords.getD 1 []))) :
    (r * r = typeSystemC.z → ∃ v ∈ vSub, r = v * rx) ∧
      (r * r = yH 0 → ∃ v ∈ vSub, r = v * ry) := by
  obtain ⟨c, -, p, hp, rfl, hR, vR, hL⟩ := exists_rows hr
  simp only [loopAt, Bool.and_eq_true] at hL
  have hw0 : ∀ j ∈ stabWords.getD 0 [], j < 2 := by decide
  have hw1 : ∀ j ∈ stabWords.getD 1 [], j < 2 := by decide
  have hs := imp_of_not_or hL.2 (by
    rw [Bool.and_eq_true]
    exact ⟨stabR_of_stab (rep_kW hw0) hR (valid_kWordR hw0) vR h₁,
      stabR_of_stab (rep_kW hw1) hR (valid_kWordR hw1) vR h₂⟩)
  rw [Bool.and_eq_true] at hs
  have hrr : MRep (Native.mul (Native.mul (hprodRow c) (aRowOf p))
      (Native.mul (hprodRow c) (aRowOf p))) (centEmb ((hcH c * aElt p) * (hcH c * aElt p))) := by
    rw [map_mul]; exact hR.mul hR
  have vrr := valid_mul vR vR
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have e' := (rows_eq_iff hrr rep_z' vrr dagOK_parts.2.1).2 (congrArg centEmb e)
    exact exists_of_any (Y := rxRow) hR rep_rx (of_bne_or hs.1 e')
  · have e' := (rows_eq_iff hrr rep_w' vrr (dagOK_parts.2.2.1 0 (by norm_num))).2
      (congrArg centEmb e)
    exact exists_of_any (Y := ryRow) hR rep_ry (of_bne_or hs.2 e')

end CFSG.Sporadic.Co1Patterson.InnerNative
