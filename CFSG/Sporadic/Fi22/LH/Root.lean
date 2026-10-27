module

public import CFSG.Sporadic.Fi22.LH.Transport
public import CFSG.Fischer.TransvectionPoints
public import CFSG.Sporadic.Fi22.LH.Tables

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.F3.Native Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.F4.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem tvPt_eq_tvP (m : Fin 693) : tvPt m = tvP m := by
  have h := rep_tvP m
  rw [tvTabs_get] at h
  exact perm_eq_of_rep (rep_tvPt m) h

theorem tvP_eq_self_iff_perp
    (x y : Fin 693) : tvP x y = y ↔ perp x y := by
  have hxx : tvP x * tvP x = 1 := tvP_mul_self x
  rw [perp_iff, ← tvP_comm_iff]
  constructor
  · intro h
    have e := tvP_conj x y
    rw [h] at e
    calc tvP x * tvP y = tvP x * tvP y * tvP x * tvP x := by
          rw [mul_assoc (tvP x * tvP y), hxx, mul_one]
      _ = tvP y * tvP x := by rw [e]
  · intro h
    apply tvP_injective
    rw [← tvP_conj, h, mul_assoc, hxx, mul_one]

theorem ptE_mul_ptE
    (u v : Fin 693) : (ptE u : J) * ptE v * ptE u = ptE (tvP u v) := by
  have h := rho_ptE u
  rw [tvPt_eq_tvP] at h
  have h2 : rho ⟨ptE u, ptE_mem_Ca u⟩ v = tvP u v := by rw [h]
  rw [rho_apply] at h2
  have h3 : (⟨ptE u, ptE_mem_Ca u⟩ : Ca) • ptE v = ptE (tvP u v) := by
    rw [← h2, Equiv.apply_symm_apply]
  have h4 := congrArg Subtype.val h3
  rw [starAction_val] at h4
  rw [← h4, Pair.inv_eq pair_D (ptE u).2.1]

theorem ptE_commute_iff
    (u v : Fin 693) :
    (ptE u : J) * ptE v = ptE v * ptE u ↔ perp u v := by
  rw [← tvP_eq_self_iff_perp, ← Pair.mul_mul_eq_self_iff pair_D (ptE u).2.1, ptE_mul_ptE]
  constructor
  · intro h
    exact ptE.injective (Subtype.ext h)
  · intro h
    rw [h]

@[expose] noncomputable def ptLocal :
    LocalPoints polarModel D a where
  χ := ptE.symm
  comm f g := by
    rw [← ptE.apply_symm_apply f, ← ptE.apply_symm_apply g, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, ptE_commute_iff]
    rfl
  tau f g h := by
    have e : (⟨(f : J) * g * f, h⟩ : star) = ptE (tvP (ptE.symm f) (ptE.symm g)) := by
      apply Subtype.ext
      rw [← ptE_mul_ptE, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [e, Equiv.symm_apply_apply]
    rfl

theorem ptLocal_χ_symm
    (u : Fin 693) : ptLocal.χ.symm u = ptE u := rfl

theorem mem_ptLocal_pts
    {U : Set J} {u : Fin 693} :
    u ∈ ptLocal.pts U ↔ (ptE u : J) ∈ U := Iff.rfl

theorem f4mul_one {x : ℕ} (hx : x < 4) : f4mul 1 x = x := by
  interval_cases x <;> decide

theorem coord_lt (c i : ℕ) : coord c i < 4 := by
  unfold coord; omega

theorem vecOfCode_code (c : ℕ) (i : Fin 6) : (vecOfCode c i).code.val = coord c i.val := rfl

theorem vecOfCode_ne_zero_iff (c : ℕ) (i : Fin 6) : vecOfCode c i ≠ 0 ↔ coord c i.val ≠ 0 := by
  rw [ne_eq, ne_eq, not_iff_not]
  constructor
  · intro h
    exact congrArg (fun x : F4 => x.code.val) h
  · intro h
    exact code_inj h

theorem ncard_fin_eq_countP (n : ℕ) (p : ℕ → Bool) :
    ({x : Fin n | p x.val = true} : Set (Fin n)).ncard = (List.range n).countP p := by
  have h1 : ({x : Fin n | p x.val = true} : Set (Fin n)).ncard =
      (Fin.val '' {x : Fin n | p x.val = true}).ncard :=
    (Set.ncard_image_of_injective _ Fin.val_injective).symm
  have h2 : Fin.val '' {x : Fin n | p x.val = true} = {i | i ∈ (List.range n).filter p} := by
    ext i
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hi, hp⟩
      exact ⟨⟨i, hi⟩, hp, rfl⟩
  have hnd : ((List.range n).filter p).Nodup := List.Nodup.filter p List.nodup_range
  rw [h1, h2, List.countP_eq_length_filter, ← List.coe_toFinset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

theorem weight_vecOfCode (c : ℕ) : weight (vecOfCode c) = weightC c := by
  have h : ((Finset.univ.filter fun k : Fin 6 => vecOfCode c k ≠ 0 : Finset (Fin 6)) :
      Set (Fin 6)) = {k : Fin 6 | (coord c k.val != 0) = true} := by
    ext k
    simp [vecOfCode_ne_zero_iff]
  unfold weight weightC
  rw [← Set.ncard_coe_finset, h, ← List.countP_eq_length_filter]
  exact ncard_fin_eq_countP 6 (fun i => coord c i != 0)

theorem code_prod_vecOfCode (c : ℕ) : (∏ k, vecOfCode c k).code.val = prodC c := by
  unfold prodC
  rw [Fin.prod_univ_six, show List.range 6 = [0, 1, 2, 3, 4, 5] by decide]
  simp only [code_mul, vecOfCode_code, List.foldl_cons, List.foldl_nil]
  rw [f4mul_one (coord_lt c 0)]
  rfl

theorem code_omega_pow (j : Fin 3) : (F4.ω ^ (j : ℕ)).code.val = j.val + 1 := by
  fin_cases j <;> decide

theorem mem_hypRoot_iff (j : Fin 3) (u : Fin 693) :
    u ∈ hypRoot j ↔ hypC j.val uPts[u.val]! = true := by
  unfold hypRoot hypC
  simp only [Set.mem_ofPred_eq, uVec, weight_vecOfCode, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true]
  have e : ∏ k, vecOfCode uPts[u.val]! k = F4.ω ^ (j : ℕ) ↔ prodC uPts[u.val]! = j.val + 1 := by
    rw [← code_prod_vecOfCode, ← code_omega_pow j]
    exact ⟨fun h => by rw [h], fun h => code_inj h⟩
  rw [e]

theorem lhData_lt
    {i : ℕ} (hi : i < 2) {k : ℕ} (hk : k < 351) : (lhData[i]!)[k]! < 3510 := by
  obtain ⟨-, h⟩ := lhData_parts
  obtain ⟨-, -, hinc, hlast⟩ := h i hi
  have : ∀ m, k + m ≤ 350 → (lhData[i]!)[k]! + m ≤ (lhData[i]!)[k + m]! := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hinc (k + m) (by omega)
      have e : k + (m + 1) = k + m + 1 := by omega
      rw [e]
      omega
  have := this (350 - k) (by omega)
  rw [show k + (350 - k) = 350 by omega] at this
  omega

theorem mem_lhData_iff {i : ℕ} (hi : i < 2) {x : ℕ} :
    x ∈ lhData[i]! ↔ ∃ l < 351, (lhData[i]!)[l]! = x := by
  have hs := (lhData_parts.2 i hi).1
  rw [Array.mem_iff_getElem]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, by omega, by rw [getElem!_pos _ l hl]⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, by omega, by rw [getElem!_pos _ l (by omega)]⟩

theorem lt_of_mem_lhData
    {i : ℕ} (hi : i < 2) {x : ℕ} (hx : x ∈ lhData[i]!) : x < 3510 := by
  obtain ⟨l, hl, rfl⟩ := (mem_lhData_iff hi).1 hx
  exact lhData_lt hi hl

theorem conjPt_mem_lhRoot
    {i : Fin 2} {x : ℕ} (hx : x < 3510) :
    conjPt x ∈ Subtype.val '' lhRoot i ↔ bitAt lhc.B[i.val]! x = true := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← ptD.apply_symm_apply y] at hy hyx
    rw [ptD_mem_lhRoot] at hy
    rw [ptD_val'] at hyx
    have := conjPt_inj (by rw [orb_size]; exact (ptD.symm y).2) (by rw [orb_size]; exact hx) hyx
    rwa [← this]
  · intro h
    exact ⟨ptD ⟨x, hx⟩, ptD_mem_lhRoot.2 h, rfl⟩

theorem mem_val_lhRoot
    {i : Fin 2} {y : J} :
    y ∈ Subtype.val '' lhRoot i ↔ ∃ x < 3510, y = conjPt x ∧ bitAt lhc.B[i.val]! x = true := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(ptD.symm z).val, (ptD.symm z).2, ?_, ?_⟩
    · rw [← ptD_val', Equiv.apply_symm_apply]
    · rw [← ptD_mem_lhRoot, Equiv.apply_symm_apply]; exact hz
  · rintro ⟨x, hx, rfl, h⟩
    exact (conjPt_mem_lhRoot hx).2 h

theorem tabOf_size (c : ℕ) : (tabOf orb c).size = 3510 := by
  unfold tabOf
  rw [cTab.eq_def]
  split_ifs <;> first | (unfold compT; simp) | exact actionChecks_parts.2.1

theorem ap_eq_zero_of_size {T : Table} {x : ℕ} (hx : T.size ≤ x) : ap T x = 0 := by
  unfold ap
  rw [getElem!_neg T x (by omega)]
  rfl

theorem lt_of_ap_tT_eq_self
    {c x : ℕ} (h : ap tT[c]! x = x) (hx : x ≠ 0) : x < 3510 := by
  by_contra hlt
  apply hx
  rw [← h]
  apply ap_eq_zero_of_size
  by_cases hc : c < 3510
  · rw [tT_get hc, tabOf_size]; omega
  · rw [getElem!_neg tT c (by rw [lh_parts.1]; exact hc)]
    show 0 ≤ x
    omega

theorem ptLocal_pts_lhRoot
    (i : Fin 2) :
    ptLocal.pts (Subtype.val '' lhRoot i ∩ star) = hypRoot ⟨2 * i.val, by omega⟩ := by
  ext u
  rw [mem_ptLocal_pts, mem_hypRoot_iff, Fin.val_mk]
  have hi := (lh_parts.2.2.2.2.2.2.2.2.2.1 i.val i.2).2.2.1
  have hu : phiPos[u.val]! < 693 := by rw [← phiEquiv_symm_val]; exact (phiEquiv.symm u).2
  have hk : ea[phiPos[u.val]!]! < 3510 := ea_get_lt hu
  rw [← starOK_spec hi u.2, ptE_apply]
  constructor
  · rintro ⟨h, -⟩
    exact (conjPt_mem_lhRoot hk).1 h
  · intro h
    refine ⟨(conjPt_mem_lhRoot hk).2 h, ?_⟩
    rw [← ptE_apply]
    exact (ptE u).2

theorem lhRoot_closed
    (i : Fin 2) {s t : J} (hs : s ∈ Subtype.val '' lhRoot i)
    (ht : t ∈ Subtype.val '' lhRoot i) : s * t * s ∈ Subtype.val '' lhRoot i := by
  obtain ⟨x, hx, rfl, hxB⟩ := mem_val_lhRoot.1 hs
  obtain ⟨y, hy, rfl, hyB⟩ := mem_val_lhRoot.1 ht
  rw [conjPt_mul_conjPt hx hy]
  exact (conjPt_mem_lhRoot (ap_tT_lt hx hy)).2
    (closedOK_spec (lh_parts.2.2.2.2.2.2.2.2.2.1 i.val i.2).2.1 hx hy hxB hyB)

theorem conj_image_lhRoot
    (i : Fin 2) {s : J} (hs : s ∈ Subtype.val '' lhRoot i) :
    (fun x => s * x * s⁻¹) '' (Subtype.val '' lhRoot i) = Subtype.val '' lhRoot i := by
  have hsE : s ∈ D := by obtain ⟨y, -, rfl⟩ := hs; exact y.2
  rw [Pair.inv_eq pair_D hsE]
  have hinj : Function.Injective fun x => s * x * s := by
    have := conj_injective s
    rwa [Pair.inv_eq pair_D hsE] at this
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨t, ht, rfl⟩
    exact lhRoot_closed i hs ht
  · exact (Set.ncard_image_of_injective _ hinj).ge
  · exact Set.toFinite _

theorem conj_image_lhRoot_of_mem_closure
    (i : Fin 2) {g : J}
    (hg : g ∈ Subgroup.closure (Subtype.val '' lhRoot i)) :
    (fun x => g * x * g⁻¹) '' (Subtype.val '' lhRoot i) = Subtype.val '' lhRoot i := by
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact conj_image_lhRoot i hs
  | one => simp
  | mul x y _ _ hx hy =>
    have e : (fun z => x * y * z * (x * y)⁻¹) =
        (fun z => x * z * x⁻¹) ∘ (fun z => y * z * y⁻¹) := by
      funext z
      simp only [Function.comp, mul_inv_rev]
      group
    rw [e, Set.image_comp, hy, hx]
  | inv x _ hx =>
    have e : (fun z => x⁻¹ * z * x⁻¹⁻¹) '' ((fun z => x * z * x⁻¹) '' (Subtype.val '' lhRoot i)) =
        Subtype.val '' lhRoot i := by
      rw [Set.image_image]
      simp only [inv_inv]
      have : ∀ z, x⁻¹ * (x * z * x⁻¹) * x = z := fun z => by group
      simp only [this, Set.image_id']
    rwa [hx] at e

theorem isLocallyHyperoval_lhRoot
    (hHF : HyperovalFacts) (i : Fin 2) :
    IsLocallyHyperoval D (Subtype.val '' lhRoot i) := by
  have hparts := lh_parts.2.2.2.2.2.2.2.2.2.1 i.val i.2
  have hstar : IsHyperovalIn star (Subtype.val '' lhRoot i ∩ star) := by
    rw [ptLocal.isHyperovalIn_iff hHF.linesByPerp pair_D Set.inter_subset_right,
      ptLocal_pts_lhRoot]
    exact hHF.isClosedHyperoval_of_mem _ _ (hypRoot_mem_hypOrbit _)
  have hne : (Subtype.val '' lhRoot i ∩ star).Nonempty := by
    obtain ⟨-, -, h3, h4, -⟩ := commTreeOK_spec hparts.2.2.2.2.1
    obtain ⟨hp, hb, hc, hn⟩ := h4 1 le_rfl (by norm_num)
    have hp0 : (lhc.cpar[i.val]!)[1]! = 0 := by omega
    rw [hp0, h3] at hc hn
    have hx := lt_of_ap_tT_eq_self hc (Ne.symm hn)
    refine ⟨conjPt (lhc.cord[i.val]!)[1]!, (conjPt_mem_lhRoot hx).2 hb, mem_D_iff.2 ⟨_, hx, rfl⟩,
      fun h => hn ?_, ?_⟩
    · rw [← conjPt_zero] at h
      exact (conjPt_inj (by rw [orb_size]; exact hx) (by rw [orb_size]; norm_num) h).symm
    · rw [← conjPt_zero]
      exact ((conjPt_commute_iff (by norm_num) hx).2 hc).symm
  obtain ⟨-, hlet, htree, hcov⟩ := rootTreeOK_spec hparts.2.2.2.1
  have hrep : ∀ l ∈ Array.range 351,
      Rep 3510 (lhc.letters[i.val]!)[l]! (conjPt (lhData[i.val]!)[l]!) := by
    intro l hl
    rw [Array.mem_range] at hl
    rw [hlet l hl]
    exact rep_tT (lhData_lt i.2 hl)
  have hTF := treeOK_facts (lG := fun l => conjPt (lhData[i.val]!)[l]!) hrep htree
  have hmove : ∀ s ∈ Subtype.val '' lhRoot i,
      ∃ g ∈ Subgroup.closure (Subtype.val '' lhRoot i), g * a * g⁻¹ = s := by
    intro s hs
    obtain ⟨x, hx, rfl, hxB⟩ := mem_val_lhRoot.1 hs
    obtain ⟨hpos, hpts⟩ := hcov x ((bitAt_B_iff i.2 hx).1 hxB)
    refine ⟨treeG lhc.trees[i.val]! (fun l => conjPt (lhData[i.val]!)[l]!)
      (ap lhc.trees[i.val]!.pos x), ?_, ?_⟩
    · refine (Subgroup.closure_le _).2 ?_ (hTF.treeG_mem hpos)
      rintro _ ⟨l, hl, rfl⟩
      rw [Array.mem_range] at hl
      apply Subgroup.subset_closure
      exact (conjPt_mem_lhRoot (lhData_lt i.2 hl)).2
        ((bitAt_B_iff i.2 (lhData_lt i.2 hl)).2 ((mem_lhData_iff i.2).2 ⟨l, hl, rfl⟩))
    · have he := hTF.elt _ hpos
      rw [hpts, idx_of_lt _ (by norm_num : 0 < 3510)] at he
      have he' : (treeG lhc.trees[i.val]! (fun l => conjPt (lhData[i.val]!)[l]!)
          (ap lhc.trees[i.val]!.pos x) • (0 : Fin 3510)).val = x := he
      have := conjPt_smul (treeG lhc.trees[i.val]! (fun l => conjPt (lhData[i.val]!)[l]!)
        (ap lhc.trees[i.val]!.pos x)) 0
      rw [he', show ((0 : Fin 3510) : ℕ) = 0 from rfl, conjPt_zero] at this
      exact this.symm
  have hconj : ∀ g ∈ Subgroup.closure (Subtype.val '' lhRoot i),
      Subtype.val '' lhRoot i ∩ LocalClass D (g * a * g⁻¹) =
        (fun x => g * x * g⁻¹) '' (Subtype.val '' lhRoot i ∩ star) := by
    intro g hg
    rw [image_conj_inter, conj_image_lhRoot_of_mem_closure i hg, Pair.image_conj_localClass pair_D]
  refine ⟨?_, fun s hs t ht => lhRoot_closed i hs ht, fun s hs => ?_, fun s hs => ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · obtain ⟨g, hg, rfl⟩ := hmove s hs
    rw [hconj g hg]
    exact hne.image _
  · obtain ⟨g, hg, rfl⟩ := hmove s hs
    rw [hconj g hg]
    exact hstar.conj pair_D g

theorem val_image_conjPerm (g : J) (T : Set D) :
    Subtype.val '' (⇑(Pair.conjPerm pair_D g) '' T) =
      (fun x => g * x * g⁻¹) '' (Subtype.val '' T) := by
  rw [Set.image_image, Set.image_image]
  simp only [Pair.conjPerm_apply]

theorem isLocallyHyperoval_of_mem_lhOrbit
    (hHF : HyperovalFacts) {i : Fin 2} {T : Set D}
    (hT : T ∈ lhOrbit i) : IsLocallyHyperoval D (Subtype.val '' T) := by
  obtain ⟨g, rfl⟩ := hT
  rw [val_image_conjPerm]
  exact (isLocallyHyperoval_lhRoot hHF i).conj pair_D g

theorem ncard_lhRoot
    (i : Fin 2) : (lhRoot i).ncard = 351 := by
  obtain ⟨-, hinc, -⟩ := (lhData_parts.2 i.val i.2).2
  have hsz := (lhData_parts.2 i.val i.2).1
  set f : Fin 351 → Fin 3510 := fun m => ⟨(lhData[i.val]!)[m.val]!, lhData_lt i.2 m.2⟩ with hf
  have hmono : StrictMono f := by
    rw [Fin.strictMono_iff_lt_succ]
    intro m
    exact hinc m.val m.2
  have hset : {k : Fin 3510 | k.val ∈ lhData[i.val]!} = Set.range f := by
    ext k
    rw [Set.mem_ofPred_eq, mem_lhData_iff i.2]
    constructor
    · rintro ⟨l, hl, hlk⟩
      exact ⟨⟨l, hl⟩, Fin.ext hlk⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m.val, m.2, rfl⟩
  unfold lhRoot
  rw [Set.ncard_image_of_injective _ ptD.injective, hset,
    Set.ncard_range_of_injective hmono.injective, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ncard_of_mem_lhOrbit
    {i : Fin 2} {T : Set D} (hT : T ∈ lhOrbit i) : T.ncard = 351 := by
  obtain ⟨g, rfl⟩ := hT
  rw [Set.ncard_image_of_injective _ (Pair.conjPerm pair_D g).injective, ncard_lhRoot]

end CFSG.Sporadic.Fi22
