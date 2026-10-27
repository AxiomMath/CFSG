module

public import CFSG.Sporadic.Recognition.LyonsLocalMcLInputs
public import CFSG.Sporadic.Recognition.McLASClasses
public import CFSG.Sporadic.Recognition.McLASThreeCount

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.PairNative

theorem fixedPtCount_eq {n : ℕ} {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) :
    fixedPtCount n T = fixedPtNum g := by
  unfold fixedPtCount fixedPtNum
  have h1 : ((List.range n).filter fun i => ap T i == i).length =
      ((Finset.range n).filter fun i => ap T i = i).card := by
    rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    congr 1
    ext i
    simp
  rw [h1]
  refine (Finset.card_bij (fun (i : Fin n) _ => i.val) ?_ ?_ ?_).symm
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨i.isLt, ?_⟩
    rw [hT i.val i.isLt, idx_of_lt g i.isLt]
    exact congrArg Fin.val hi
  · intro i _ j _ h
    exact Fin.ext h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    refine ⟨⟨i, hi.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := hi.2
    rw [hT i hi.1, idx_of_lt g hi.1] at this
    exact Fin.ext this

theorem pairSel_iff {a b : Table} {x g : Equiv.Perm (Fin 275)} (ha : Rep 275 a x)
    (hb : Rep 275 b g) :
    pairSel a b = true ↔ orderOf g = 3 ∧ fixedPtNum g = 5 ∧ g ≠ 1 ∧ g ≠ x ∧ g ≠ x * x := by
  have h1 := ordTest_iff_perm hb (by norm_num : 0 < 3)
  have h2 := fixedPtCount_eq hb
  have h3 := tblEq_idT_iff (by norm_num : 275 < 2 ^ 32) hb
  have h4 := tblEq_iff_eq hb ha
  have h5 := tblEq_iff_eq hb (Rep.compT ha ha)
  simp only [pairSel, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨⟨ho, hf⟩, hi⟩, hx⟩, hxx⟩
    exact ⟨h1.1 ho, by rw [← h2]; exact hf, fun hg => Bool.eq_false_iff.1 hi (h3.2 hg),
      fun hg => Bool.eq_false_iff.1 hx (h4.2 hg), fun hg => Bool.eq_false_iff.1 hxx (h5.2 hg)⟩
  · rintro ⟨ho, hf, hi, hx, hxx⟩
    exact ⟨⟨⟨⟨h1.2 ho, by rw [h2]; exact hf⟩, Bool.eq_false_iff.2 fun h => hi (h3.1 h)⟩,
      Bool.eq_false_iff.2 fun h => hx (h4.1 h)⟩, Bool.eq_false_iff.2 fun h => hxx (h5.1 h)⟩

theorem sel_conj {x g c : Equiv.Perm (Fin 275)} (hc : c * x = x * c)
    (h : orderOf g = 3 ∧ fixedPtNum g = 5 ∧ g ≠ 1 ∧ g ≠ x ∧ g ≠ x * x) :
    orderOf (c * g * c⁻¹) = 3 ∧ fixedPtNum (c * g * c⁻¹) = 5 ∧ c * g * c⁻¹ ≠ 1 ∧ c * g * c⁻¹ ≠ x ∧
      c * g * c⁻¹ ≠ x * x := by
  obtain ⟨ho, hf, h1, hx, hxx⟩ := h
  have hcx : c⁻¹ * x * c = x := by
    calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
      _ = c⁻¹ * (c * x) := by rw [hc]
      _ = x := by group
  have hback : ∀ y, c * g * c⁻¹ = y → g = c⁻¹ * y * c := fun y h => by
    rw [← h]
    group
  refine ⟨?_, by rw [fixedPtNum_conj]; exact hf, fun h => h1 ?_, fun h => hx ?_, fun h => hxx ?_⟩
  · rw [← ho]
    exact (MulAut.conj c).orderOf_eq g
  · rw [hback 1 h]
    group
  · rw [hback x h, hcx]
  · rw [hback (x * x) h]
    calc c⁻¹ * (x * x) * c = (c⁻¹ * x * c) * (c⁻¹ * x * c) := by group
      _ = x * x := by rw [hcx]

theorem mclP_pair_core
    (hrows : ThreeFacts) (hpair : pairCheck = true) :
    fixedPtNum three₁ = 5 ∧
      ∃ b₀ ∈ mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))),
        Nat.card ↥(mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) ⊓
          centralizer ({b₀} : Set (Equiv.Perm (Fin 275)))) = 162 ∧
        ∀ y ∈ mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))), orderOf y = 3 →
          fixedPtNum y = 5 → y ≠ 1 → y ≠ three₁ → y ≠ three₁ * three₁ →
          ∃ c ∈ mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))), y = c * b₀ * c⁻¹ := by
  have hD : GroupData 275 mclP mclPGTbls mclGen mclSift := mcl_groupData
  obtain ⟨hrepA, -, -, hgens, hcent, -⟩ := hrows.row₁
  have hE := hrows.enum₁
  simp only [pairCheck, pairCheckAux, Bool.and_eq_true, beq_iff_eq] at hpair
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hfixA, hpermB⟩, hsiftB⟩, hcommB⟩, hselB⟩, hcg⟩, htree⟩, hdist⟩, hsz⟩, hall⟩ :=
    hpair
  dsimp only [threeRow₁] at hrepA hgens hcent hcg htree hdist hsz hall hE
  set cg : Array Table := #[threeTbl 0, threeTbl 1, threeTbl 2] with hcgdef
  set cgInv : Array Table := cg.map (invT 275) with hcgInvdef
  set C := mulClosureH 275 cg 924000 with hCdef
  set o := conjClosureH 275 cg cgInv pairTbl 200 with hodef
  set K := mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) with hKdef
  have hA3 : fixedPtNum three₁ = 5 := by rw [← fixedPtCount_eq hrepA]; exact hfixA
  obtain ⟨b₀, hB⟩ : ∃ b₀, Rep 275 pairTbl b₀ := ⟨_, rep_tp hpermB⟩
  have hcommK : ∀ c ∈ K, c * three₁ = three₁ * c := fun c hc =>
    mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
  have hb₀K : b₀ ∈ K := mem_inf.2 ⟨(hD.sift _ _ hB).1 hsiftB, by
    rw [mem_centralizer_singleton_iff]
    exact (commTT_iff hB hrepA).1 hcommB⟩
  have hsel₀ := (pairSel_iff hrepA hB).1 hselB
  rw [Array.all_eq_true'] at hcg
  simp only [Bool.and_eq_true] at hcg
  have hgK : ∀ l < cg.size, Rep 275 cg[l]! (tp 275 cg[l]!) ∧
      Rep 275 cgInv[l]! (tp 275 cg[l]!)⁻¹ ∧ tp 275 cg[l]! ∈ K := by
    intro l hl
    have hmem : cg[l]! ∈ cg := getElem!_mem_array hl
    obtain ⟨h1, h2⟩ := hcg _ hmem
    have hc := rep_tp h1
    refine ⟨hc, ?_, ?_⟩
    · rw [getElem!_pos cgInv l (by simpa [cgInv] using hl), Array.getElem_map,
        ← getElem!_pos cg l hl]
      exact rep_invT hc h2
    · rw [← hgens]
      exact subset_closure ⟨_, hmem, rfl⟩
  have hKcov : ∀ y ∈ K, ∃ k < C.1.size, Rep 275 C.1[k]! y := hE
  have horb := conjTreeOK_spec K (gg := fun l => tp 275 cg[l]!) hgK hB htree
  have horep : ∀ k < o.1.size, Rep 275 o.1[k]! (tablePerm 275 o.1[k]!) := by
    intro k hk
    obtain ⟨c, -, hrep⟩ := horb k hk
    rw [tablePerm_eq hrep]
    exact hrep
  have honodup := nodup_of_hkeysDistinct (forall₂_tablePerm horep) hdist
  have hcover : ∀ y ∈ K, orderOf y = 3 → fixedPtNum y = 5 → y ≠ 1 → y ≠ three₁ →
      y ≠ three₁ * three₁ → ∃ j < o.1.size, y = tablePerm 275 o.1[j]! := by
    intro y hy ho hf h1 h2 h3
    obtain ⟨k, hk, hrep⟩ := hKcov y hy
    have hsel : pairSel (threeTbl 0) C.1[k]! = true :=
      (pairSel_iff hrepA hrep).2 ⟨ho, hf, h1, h2, h3⟩
    rw [Array.all_eq_true'] at hall
    have h := hall _ (getElem!_mem_array hk)
    rw [hsel, Bool.not_true, Bool.false_or] at h
    exact memT_spec horep hrep h
  have hconj : ∀ y, y ∈ conjClass K b₀ ↔ y ∈ o.1.toList.map (tablePerm 275) := by
    intro y
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hs := sel_conj (hcommK c hc) hsel₀
      obtain ⟨j, hj, hyj⟩ := hcover _ (K.mul_mem (K.mul_mem hc hb₀K) (K.inv_mem hc)) hs.1 hs.2.1
        hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
      rw [hyj]
      exact List.mem_map.2 ⟨o.1[j]!, Array.mem_toList_iff.2 (getElem!_mem_array hj), rfl⟩
    · intro hy
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm horep hy
      obtain ⟨c, hc, hrep⟩ := horb k hk
      rw [tablePerm_eq hrep]
      exact ⟨c, hc, rfl⟩
  have hncard : (conjClass K b₀).ncard = 180 := by
    classical
    have hset : conjClass K b₀ = ((o.1.toList.map (tablePerm 275)).toFinset :
        Set (Equiv.Perm (Fin 275))) := by
      ext y
      rw [List.coe_toFinset]
      exact hconj y
    rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup honodup, List.length_map,
      Array.length_toList, hsz]
  have hos := ncard_conjClass_mul_card K b₀
  rw [hncard, hcent] at hos
  refine ⟨hA3, b₀, hb₀K, by omega, fun y hy ho hf h1 h2 h3 => ?_⟩
  obtain ⟨j, hj, hyj⟩ := hcover y hy ho hf h1 h2 h3
  obtain ⟨c, hc, hrep⟩ := horb j hj
  exact ⟨c, hc, by rw [hyj, tablePerm_eq hrep]⟩

theorem inf_centralizer_pair {M : Type*} [Group M] (H : Subgroup M) (s t : M) :
    H ⊓ centralizer ({s, t} : Set M) =
      (H ⊓ centralizer ({s} : Set M)) ⊓ centralizer ({t} : Set M) := by
  ext x
  simp only [mem_inf, mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  tauto

theorem card_inf_centralizer_pair_conj {M : Type*} [Group M] (H : Subgroup M) {g : M} (hg : g ∈ H)
    (s t : M) :
    Nat.card ↥(H ⊓ centralizer ({g * s * g⁻¹, g * t * g⁻¹} : Set M)) =
      Nat.card ↥(H ⊓ centralizer ({s, t} : Set M)) := by
  have h := CFSG.Sporadic.SmallOddCore.map_conj_inf_centralizer H hg ({s, t} : Set M)
  rw [Set.image_pair] at h
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [← h]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mclP_pair_card
    (hrows : ThreeFacts) (hpair : pairCheck = true)
    {b : Equiv.Perm (Fin 275)} (hb : b ∈ mclP) (hb3 : orderOf b = 3)
    (hbc : ∃ g ∈ mclP, b = g * three₁ * g⁻¹) (hcomm : b * three₁ = three₁ * b)
    (hnot : b ∉ Subgroup.zpowers three₁) :
    Nat.card ↥(mclP ⊓ Subgroup.centralizer ({three₁, b} : Set (Equiv.Perm (Fin 275)))) = 162 := by
  obtain ⟨hA3, b₀, -, hcard, hcov⟩ := mclP_pair_core hrows hpair
  have hbK : b ∈ mclP ⊓ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) :=
    mem_inf.2 ⟨hb, mem_centralizer_singleton_iff.2 hcomm⟩
  have hbf : fixedPtNum b = 5 := by
    obtain ⟨g, -, rfl⟩ := hbc
    rw [fixedPtNum_conj, hA3]
  obtain ⟨c, hc, hbc'⟩ := hcov b hbK hb3 hbf
    (fun h => hnot (by rw [h]; exact one_mem _)) (fun h => hnot (by rw [h]; exact mem_zpowers _))
    (fun h => hnot (by rw [h]; exact mul_mem (mem_zpowers _) (mem_zpowers _)))
  rw [inf_centralizer_pair, hbc', CFSG.Sporadic.SmallOddCore.inf_centralizer_conj _ hc,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact hcard

theorem card_inf_centralizer_image_of_equiv {n : ℕ} {T : Type*} [Group T]
    {P : Subgroup (Equiv.Perm (Fin n))} (e : T ≃* P) (s : Set T) :
    Nat.card ↥(P ⊓ centralizer ((fun t => ((e t : P) : Equiv.Perm (Fin n))) '' s)) =
      Nat.card ↥(centralizer s) := by
  let ι : T →* Equiv.Perm (Fin n) := P.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hrange : ι.range = P := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  have h := CFSG.Sporadic.SmallOddCore.map_centralizer_eq_inf hι s
  rw [hrange] at h
  rw [← Subgroup.card_map_of_injective hι, h]
  rfl

theorem pair_card_of_equiv
    (hrows : ThreeFacts) (hpair : pairCheck = true) {T : Type*} [Group T] (e : T ≃* mclP) {a b : T}
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (ha : Nat.card ↥(centralizer ({a} : Set T)) = 29160)
    (hb : Nat.card ↥(centralizer ({b} : Set T)) = 29160) (hab : a * b = b * a)
    (hnot : b ∉ zpowers a) : Nat.card ↥(centralizer ({a, b} : Set T)) = 162 := by
  obtain ⟨-, -, -, -, -, hc₂, -, -, -, hall⟩ := mclP_order_three_classes hrows
  have hxP : ((e a : mclP) : Equiv.Perm (Fin 275)) ∈ mclP := (e a).2
  have hyP : ((e b : mclP) : Equiv.Perm (Fin 275)) ∈ mclP := (e b).2
  have hx3 : orderOf ((e a : mclP) : Equiv.Perm (Fin 275)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha3]
  have hy3 : orderOf ((e b : mclP) : Equiv.Perm (Fin 275)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hb3]
  have hcx : Nat.card ↥(mclP ⊓ centralizer ({((e a : mclP) : Equiv.Perm (Fin 275))} :
      Set (Equiv.Perm (Fin 275)))) = 29160 := by
    have := card_inf_centralizer_image_of_equiv e ({a} : Set T)
    rw [Set.image_singleton] at this
    rw [this, ha]
  have hcy : Nat.card ↥(mclP ⊓ centralizer ({((e b : mclP) : Equiv.Perm (Fin 275))} :
      Set (Equiv.Perm (Fin 275)))) = 29160 := by
    have := card_inf_centralizer_image_of_equiv e ({b} : Set T)
    rw [Set.image_singleton] at this
    rw [this, hb]
  have hclass : ∀ z ∈ mclP, orderOf z = 3 →
      Nat.card ↥(mclP ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 275)))) = 29160 →
      ∃ g ∈ mclP, z = g * three₁ * g⁻¹ := by
    intro z hz hz3 hzc
    rcases hall z hz hz3 with h | ⟨g, hg, hgz⟩
    · exact h
    · exfalso
      rw [hgz, card_cent_conj hg, hc₂] at hzc
      omega
  obtain ⟨g₁, hg₁, hgx⟩ := hclass _ hxP hx3 hcx
  obtain ⟨g₂, hg₂, hgy⟩ := hclass _ hyP hy3 hcy
  set x : Equiv.Perm (Fin 275) := ((e a : mclP) : Equiv.Perm (Fin 275)) with hxdef
  set y : Equiv.Perm (Fin 275) := ((e b : mclP) : Equiv.Perm (Fin 275)) with hydef
  have hxy : x * y = y * x := by
    have := congrArg (fun z : T => ((e z : mclP) : Equiv.Perm (Fin 275))) hab
    simpa using this
  have hb'P : g₁⁻¹ * y * g₁ ∈ mclP := mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hg₁) hyP) hg₁
  have hb'3 : orderOf (g₁⁻¹ * y * g₁) = 3 := by
    rw [← hy3]
    have := (MulAut.conj g₁⁻¹).orderOf_eq y
    simpa using this
  have hb'c : ∃ g ∈ mclP, g₁⁻¹ * y * g₁ = g * three₁ * g⁻¹ :=
    ⟨g₁⁻¹ * g₂, mclP.mul_mem (mclP.inv_mem hg₁) hg₂, by rw [hgy]; group⟩
  have hb'comm : (g₁⁻¹ * y * g₁) * three₁ = three₁ * (g₁⁻¹ * y * g₁) := by
    have h3 : three₁ = g₁⁻¹ * x * g₁ := by rw [hgx]; group
    rw [h3]
    calc g₁⁻¹ * y * g₁ * (g₁⁻¹ * x * g₁) = g₁⁻¹ * (y * x) * g₁ := by group
      _ = g₁⁻¹ * (x * y) * g₁ := by rw [hxy]
      _ = g₁⁻¹ * x * g₁ * (g₁⁻¹ * y * g₁) := by group
  have hb'not : g₁⁻¹ * y * g₁ ∉ zpowers three₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    apply hnot
    have hyk : y = x ^ k := by
      have h1 : y = g₁ * (g₁⁻¹ * y * g₁) * g₁⁻¹ := by group
      rw [h1, ← hk, hgx]
      exact (conj_zpow).symm.trans (by rw [conj_zpow])
    refine mem_zpowers_iff.2 ⟨k, e.injective (Subtype.ext ?_)⟩
    rw [map_zpow]
    exact hyk.symm
  have h162 := mclP_pair_card hrows hpair hb'P hb'3 hb'c hb'comm hb'not
  have hconj := card_inf_centralizer_pair_conj mclP hg₁ three₁ (g₁⁻¹ * y * g₁)
  rw [show g₁ * (g₁⁻¹ * y * g₁) * g₁⁻¹ = y by group, ← hgx] at hconj
  have himg := card_inf_centralizer_image_of_equiv e ({a, b} : Set T)
  rw [Set.image_pair] at himg
  rw [← himg, hconj, h162]

theorem mcl_pair_card
    (hrows : ThreeFacts) (hpair : pairCheck = true) {a b : CFSG.Blueprint.NativeSporadic.McL}
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3)
    (ha : Nat.card ↥(Subgroup.centralizer ({a} : Set CFSG.Blueprint.NativeSporadic.McL)) = 29160)
    (hb : Nat.card ↥(Subgroup.centralizer ({b} : Set CFSG.Blueprint.NativeSporadic.McL)) = 29160)
    (hab : a * b = b * a) (hnot : b ∉ Subgroup.zpowers a) :
    Nat.card ↥(Subgroup.centralizer ({a, b} : Set CFSG.Blueprint.NativeSporadic.McL)) = 162 :=
  @pair_card_of_equiv hrows hpair CFSG.Blueprint.NativeSporadic.McL inferInstance
    mclPermEquiv a b ha3 hb3 ha hb hab hnot

end CFSG.Sporadic.Recognition.McLAS
