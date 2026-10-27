module

public import CFSG.Sporadic.Co1.Module.LeechOddLit
public import CFSG.Sporadic.Co1.Module.LeechOddLitInputs
public import CFSG.Sporadic.Co1.Module.OddNative
public import CFSG.Sporadic.Co1.Module.OddBuildBase1

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix
open CFSG.KD.Co1Odd CFSG.KC.Co1F2 CFSG.KC.M1F2

attribute [local instance] vecAct vecSMul
attribute [local irreducible] rr regsRows

theorem zgens_mem {k : ℕ}
    (hk : k < 3) : ∀ l < (zIdx[k]!).length, reg ((zIdx[k]!)[l]!) ∈ Hst ⊓
      Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({reg (sIdx[k]!)} : Set NativeSporadic.Co1) := by
  have hpk := partnerOK_facts k hk
  have hzk : zIdx[k]! ∈ zIdx := by interval_cases k <;> simp [zIdx]
  intro l hl
  have hzin : (zIdx[k]!)[l]! ∈ zIdx[k]! := by
    rw [getElem!_pos (zIdx[k]!) l hl]
    exact List.getElem_mem hl
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨reg_fix_of_mem ?_,
    reg_mem_centralizer (hpk.1 _ hzin).1⟩, ?_⟩
  · simp only [List.mem_append]
    exact Or.inr (List.mem_flatten.2 ⟨zIdx[k]!, hzk, hzin⟩)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact reg_comm (hpk.1 _ hzin).2

theorem zgens_mat {k : ℕ} {G : List ℕ}
    (h : (zIdx[k]!).map rr = G.map (unpackR 24)) :
    ∀ l < G.length, mat (reg ((zIdx[k]!).getD l 0)) = rowsMatrix 24 (unpackR 24 (G.getD l 0)) := by
  intro l hl
  have hl' : l < (zIdx[k]!).length := by
    have := congrArg List.length h
    simp only [List.length_map] at this
    omega
  have e := congrArg (fun L => L[l]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hl',
    Option.map_some, Option.some.injEq] at e
  rw [mat_reg, List.getD_eq_getElem _ _ hl', List.getD_eq_getElem _ _ hl, e]

theorem disj_facts_lit
    (h : zOneLitOK)
    (hcard : Nat.card ↥(Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep 1} : Set NativeSporadic.Co1)) = 1344) :
    ∀ y ∈ Hst, y ∈ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) →
      y ∈ Subgroup.centralizer ({sRep 1} : Set NativeSporadic.Co1) → ¬ IsConj rho3 y := by
  have := finite_co1
  obtain ⟨hG, hT, hd, hc, hW⟩ := h
  have hGl : Z1G.length = (zIdx[1]!).length := by
    have := congrArg List.length hG
    simpa using this.symm
  intro y hyH hyρ hys
  refine not_conj_of_tree71 hT hd hc hW (fun l => reg ((zIdx[1]!).getD l 0)) (zgens_mat hG)
    (Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep 1} : Set NativeSporadic.Co1)) (fun l hl => ?_) hcard rho3_sq
    fix_rho3 y (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hyH, hyρ⟩, hys⟩)
  have hl' : l < (zIdx[1]!).length := hGl ▸ hl
  have := zgens_mem (k := 1) (by norm_num) l hl'
  rw [List.getD_eq_getElem _ _ hl']
  rw [getElem!_pos (zIdx[1]!) l hl'] at this
  exact this

theorem outer_facts_lit
    (h : zTwoLitOK) (ho : outerLitOK = true)
    (hcard : Nat.card ↥(Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1)) = 96) :
    ∀ y ∈ Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1), IsConj rho3 y →
      ∃ u v : Vec24, rho3 • v = v ∧ sRep 2 • v = v ∧ v ∈ MulAction.orbit Jmat v₄ ∧
        y • u + u = v := by
  have := finite_co1
  obtain ⟨hG, hT, hd, hc⟩ := h
  have hGl : Z2G.length = (zIdx[2]!).length := by
    have := congrArg List.length hG
    simpa using this.symm
  intro y hy hconj
  obtain ⟨i, hiP, hm⟩ := tree71_point hT hd hc (fun l => reg ((zIdx[2]!).getD l 0)) (zgens_mat hG)
    (Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1)) (fun l hl => by
        have hl' : l < (zIdx[2]!).length := hGl ▸ hl
        have := zgens_mem (k := 2) (by norm_num) l hl'
        rw [List.getD_eq_getElem _ _ hl']
        rw [getElem!_pos (zIdx[2]!) l hl'] at this
        exact this) hcard y hy
  obtain ⟨h1, h2, h3⟩ := conj_point_facts (Z2W.getD i []) hconj hm rho3_sq fix_rho3
  unfold outerLitOK at ho
  rw [List.all_eq_true] at ho
  have hoi := ho i (List.mem_range.2 hiP)
  rw [h2, h3] at hoi
  simp only [Bool.not_true, Bool.or_false, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at hoi
  rcases hoi with hid | ⟨hu24, htest⟩
  · exact absurd hid h1
  set u := (Z2W.getD i []).getD 0 0
  set Y := unpackR 24 (Z2P.getD i 0)
  have hlt : vecMulN 24 (transposeRows 24 Y) u < 2 ^ 24 :=
    vecMulN_lt _ (transposeRows_lt _) u
  have hv24 : vecMulN 24 (transposeRows 24 Y) u ^^^ u < 2 ^ 24 := Nat.xor_lt_two_pow hlt hu24
  unfold outerTest at htest
  simp only [Bool.and_eq_true] at htest
  obtain ⟨⟨hf1, hf2⟩, hf3⟩ := htest
  refine ⟨toVecD 24 u, toVecD 24 (vecMulN 24 (transposeRows 24 Y) u ^^^ u), ?_, ?_,
    (type4N_iff _ hv24).1 (by rw [isT4'] at hf3; exact hf3), ?_⟩
  · exact (smul_reg_iff 27 _).2 ((isFixedN_iff (rr 27) hv24).1 hf1)
  · exact (smul_reg_iff _ _).2 ((isFixedN_iff (rr (sIdx[2]!)) hv24).1 hf2)
  · rw [toVecD_xor, smul_eq_co1Act, co1Act_eq_mulVec, hm, rowsMatrix_mulVec]

theorem orbitOK_spec' {Zs : List (Array ℕ)} {L : List ℕ} (h : orbitOK Zs L = true) :
    ∃ u₀ ∈ L, ∀ u ∈ L, ∃ z ∈ Zs, vecMulN 24 (transposeRows 24 z) u₀ = u := by
  unfold orbitOK at h
  rcases L with _ | ⟨u₀, rest⟩
  · simp at h
  · simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
    exact ⟨u₀, List.mem_cons_self, h⟩

theorem mem_vecsTwo_lit (x : ℕ) :
    x ∈ vecsTwo ↔ x < 2 ^ 24 ∧ rho3 • toVecD 24 x = toVecD 24 x ∧
      sRep 2 • toVecD 24 x = toVecD 24 x := by
  unfold vecsTwo Wk
  rw [mem_fixList]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨hx, h1, h2⟩
    exact ⟨hx, (smul_reg_iff 27 _).2 h1, (smul_reg_iff _ _).2 h2⟩
  · rintro ⟨hx, h1, h2⟩
    exact ⟨hx, (smul_reg_iff 27 _).1 h1, (smul_reg_iff _ _).1 h2⟩

theorem orbitY_facts_lit
    (h : zTwoLitOK) (hy : orbitYLitOK = true) : ∃ u₀ : Vec24, rho3 • u₀ = u₀ ∧ sRep 2 • u₀ = u₀ ∧
    u₀ ∈ MulAction.orbit Jmat v₂ ∧ u₀ + omega0 ∈ MulAction.orbit Jmat v₂ ∧
    ∀ u : Vec24, rho3 • u = u → sRep 2 • u = u → u ∈ MulAction.orbit Jmat v₂ →
      u + omega0 ∈ MulAction.orbit Jmat v₂ →
      ∃ z ∈ Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
        Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1), z • u₀ = u := by
  obtain ⟨hG, hT, -, -⟩ := h
  have hGl : Z2G.length = (zIdx[2]!).length := by
    have := congrArg List.length hG
    simpa using this.symm
  obtain ⟨hPn, -, -⟩ := treeOK71_facts hT
  have hel := tree71_elems hT (fun l => reg ((zIdx[2]!).getD l 0)) (zgens_mat hG)
    (Hst ⊓ Subgroup.centralizer ({rho3} : Set NativeSporadic.Co1) ⊓
      Subgroup.centralizer ({sRep 2} : Set NativeSporadic.Co1)) (fun l hl => by
        have hl' : l < (zIdx[2]!).length := hGl ▸ hl
        have := zgens_mem (k := 2) (by norm_num) l hl'
        rw [List.getD_eq_getElem _ _ hl']
        rw [getElem!_pos (zIdx[2]!) l hl'] at this
        exact this)
  have hT2 : ∀ x, x < 2 ^ 24 → (isT2 x = true ↔ toVecD 24 x ∈ MulAction.orbit Jmat v₂) :=
    fun x hx => by rw [isT2]; exact inPts_iff x hx
  have hyl : ∀ x, x ∈ yList ↔ x ∈ vecsTwo ∧ isT2 x = true ∧ isT2 (x ^^^ code4) = true := by
    intro x
    unfold yList w2List
    simp only [List.mem_filter, and_assoc]
  have hxor : ∀ x : ℕ, toVecD 24 x + omega0 = toVecD 24 (x ^^^ code4) := by
    intro x
    rw [toVecD_xor]
    rfl
  have hc4 : code4 < 2 ^ 24 := by norm_num [code4]
  unfold orbitYLitOK at hy
  obtain ⟨u₀, hu₀, hall⟩ := orbitOK_spec' hy
  obtain ⟨hv, ht2, ht3⟩ := (hyl u₀).1 hu₀
  obtain ⟨hu24, hu1, hu2⟩ := (mem_vecsTwo_lit u₀).1 hv
  refine ⟨toVecD 24 u₀, hu1, hu2, (hT2 u₀ hu24).1 ht2, ?_, fun u h1 h2 h3 h4 => ?_⟩
  · rw [hxor]
    exact (hT2 _ (Nat.xor_lt_two_pow hu24 hc4)).1 ht3
  obtain ⟨x, hx, rfl⟩ := exists_toVecD u
  have hxy : x ∈ yList := by
    rw [hyl]
    refine ⟨(mem_vecsTwo_lit x).2 ⟨hx, h1, h2⟩, (hT2 x hx).2 h3, ?_⟩
    rw [hxor] at h4
    exact (hT2 _ (Nat.xor_lt_two_pow hx hc4)).2 h4
  obtain ⟨Y, hYmem, hYeq⟩ := hall x hxy
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hYmem
  obtain ⟨j, hj, hjM⟩ := List.getElem_of_mem hM
  have hj96 : j < 96 := hPn ▸ hj
  obtain ⟨z, hzK, hzm⟩ := hel j hj96
  refine ⟨z, hzK, ?_⟩
  rw [List.getD_eq_getElem _ _ hj, hjM] at hzm
  rw [smul_eq_co1Act, co1Act_eq_mulVec, hzm, rowsMatrix_mulVec, hYeq]

end CFSG.Sporadic.Co1.Module.Odd

end
