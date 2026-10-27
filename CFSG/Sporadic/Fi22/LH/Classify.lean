module

public import CFSG.Sporadic.Fi22.LH.Root
public import CFSG.Sporadic.Fi22.LocalPSU
public import CFSG.Fischer.Uniq.F22

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.F3.Native Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.F4.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem nonempty_localPoints_D
    {s : J} (hs : s ∈ D) : Nonempty (LocalPoints polarModel D s) :=
  F22.nonempty_localPoints f22_J hs

theorem conjPt_lt_mem_D
    {k : ℕ} (hk : k < 3510) : conjPt k ∈ D := mem_D_iff.2 ⟨k, hk, rfl⟩

theorem conjPt_ne
    {k l : ℕ} (hk : k < 3510) (hl : l < 3510) (h : k ≠ l) : conjPt k ≠ conjPt l :=
  fun e => h (conjPt_inj (by rw [orb_size]; exact hk) (by rw [orb_size]; exact hl) e)

theorem conjPt_mem_localClass
    {k l : ℕ} (hk : k < 3510) (hl : l < 3510) :
    conjPt l ∈ LocalClass D (conjPt k) ↔ l ≠ k ∧ ap tT[k]! l = l := by
  rw [mem_localClass]
  constructor
  · rintro ⟨-, hne, hc⟩
    exact ⟨fun h => hne (by rw [h]), (conjPt_commute_iff hk hl).1 hc.symm⟩
  · rintro ⟨hne, hc⟩
    exact ⟨conjPt_lt_mem_D hl, conjPt_ne hl hk hne, ((conjPt_commute_iff hk hl).2 hc).symm⟩

theorem mem_D_lt
    {x : J} (hx : x ∈ D) : ∃ k < 3510, x = conjPt k := mem_D_iff.1 hx

theorem eq_lhRoot_of_star
    (hHF : HyperovalFacts) (i : Fin 2) {T : Set J}
    (hT : IsLocallyHyperoval D T) (haT : a ∈ T)
    (hstar : T ∩ star = Subtype.val '' lhRoot i ∩ star) : T = Subtype.val '' lhRoot i := by
  have hRl := isLocallyHyperoval_lhRoot hHF i
  have hparts := lh_parts.2.2.2.2.2.2.2.2.2.1 i.val i.2
  have hzero : (lhData[i.val]!)[0]! = 0 := (lhData_parts.2 i.val i.2).2.1
  have haR : a ∈ Subtype.val '' lhRoot i := by
    rw [← conjPt_zero, conjPt_mem_lhRoot (by norm_num), bitAt_B_iff i.2 (by norm_num),
      mem_lhData_iff i.2]
    exact ⟨0, by norm_num, hzero⟩
  let good : J → Prop := fun x => x ∈ T ∧ x ∈ Subtype.val '' lhRoot i ∧
    T ∩ LocalClass D x = Subtype.val '' lhRoot i ∩ LocalClass D x
  have hstep : ∀ x y, good x → y ∈ Subtype.val '' lhRoot i → y ∈ LocalClass D x → good y := by
    rintro x y ⟨hxT, hxR, hxe⟩ hyR hyx
    have hyT : y ∈ T := by
      have : y ∈ Subtype.val '' lhRoot i ∩ LocalClass D x := ⟨hyR, hyx⟩
      rw [← hxe] at this
      exact this.1
    have hxy : x ∈ LocalClass D y := ⟨hT.subset hxT, fun h => hyx.2.1 h.symm, hyx.2.2.symm⟩
    obtain ⟨L⟩ := nonempty_localPoints_D (hT.subset hyT)
    refine ⟨hyT, hyR, IsHyperovalIn.eq_of_inter hHF pair_D L (hT.hyperoval y hyT)
      (hRl.hyperoval y hyR) ⟨hxT, hxy⟩ ⟨hxR, hxy⟩ ?_⟩
    rw [Set.inter_right_comm, hxe, Set.inter_right_comm]
  obtain ⟨hosz, -, ho0, hopar, hocov⟩ := commTreeOK_spec hparts.2.2.2.2.1
  have hlt : ∀ k < 351, (lhc.cord[i.val]!)[k]! < 3510 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [ho0]; norm_num
    · obtain ⟨-, -, hc, -⟩ := hopar k hk0 hk
      by_cases h0 : (lhc.cord[i.val]!)[k]! = 0
      · rw [h0]; norm_num
      · exact lt_of_ap_tT_eq_self hc h0
  have hgood : ∀ k < 351, good (conjPt (lhc.cord[i.val]!)[k]!) := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [ho0, conjPt_zero]
        exact ⟨haT, haR, hstar⟩
      · obtain ⟨hp, hb, hc, hn⟩ := hopar k hk0 hk
        have hpk : (lhc.cpar[i.val]!)[k]! < 351 := by omega
        refine hstep _ _ (ih _ hp hpk) ((conjPt_mem_lhRoot (hlt k hk)).2 hb) ?_
        exact (conjPt_mem_localClass (hlt _ hpk) (hlt k hk)).2 ⟨Ne.symm hn, hc⟩
  have hgoodR : ∀ x ∈ Subtype.val '' lhRoot i, good x := by
    intro x hx
    obtain ⟨y, hy, rfl, hyB⟩ := mem_val_lhRoot.1 hx
    have hyS := (bitAt_B_iff i.2 hy).1 hyB
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 (hocov _ hyS)
    have := hgood k (by omega)
    rwa [getElem!_pos _ k hk] at this
  refine Set.Subset.antisymm ?_ fun x hx => (hgoodR x hx).1
  intro f hfT
  by_contra hfR
  obtain ⟨m, hm, rfl⟩ := mem_D_lt (hT.subset hfT)
  have hmB : bitAt lhc.B[i.val]! m = false := by
    cases h : bitAt lhc.B[i.val]! m
    · rfl
    · exact absurd ((conjPt_mem_lhRoot hm).2 h) hfR
  obtain ⟨⟨x, hx, hxB, hxc⟩, -⟩ := domOK_spec hparts.2.2.2.2.2.1 hm hmB
  have hxR := (conjPt_mem_lhRoot hx).2 hxB
  obtain ⟨-, -, hxe⟩ := hgoodR _ hxR
  have hmx : conjPt m ∈ LocalClass D (conjPt x) := by
    refine (conjPt_mem_localClass hx hm).2 ⟨fun h => ?_, ?_⟩
    · rw [h] at hmB; rw [hmB] at hxB; exact absurd hxB (by decide)
    · exact (conjPt_commute_iff hx hm).1 ((conjPt_commute_iff hm hx).2 hxc).symm
  have : conjPt m ∈ T ∩ LocalClass D (conjPt x) := ⟨hfT, hmx⟩
  rw [hxe] at this
  exact hfR this.1

theorem conjPt_mem_star_iff
    {k : ℕ} (hk : k < 3510) : conjPt k ∈ star ↔ k ∈ ea := by
  refine ⟨fun h => ?_, conjPt_mem_star⟩
  obtain ⟨l, hl, hkl⟩ := mem_ea_of_mem_star h
  have := conjPt_inj (by rw [orb_size]; exact hk) (by rw [orb_size]; exact (mem_ea.1 hl).1) hkl
  rwa [this]

theorem ptE_symm_conjPt
    {k : ℕ} (hk : k ∈ ea) :
    (ptE.symm ⟨conjPt k, conjPt_mem_star hk⟩).val = phiData[(ePos ea)[k]!]! := by
  have hk3 := (mem_ea.1 hk).1
  have hp : (ePos ea)[k]! < 693 := (ePos_lt_iff hk3).2 hk
  have e : (⟨conjPt k, conjPt_mem_star hk⟩ : star) = posEquiv ⟨(ePos ea)[k]!, hp⟩ := by
    apply Subtype.ext
    rw [posEquiv_apply]
    simp only
    rw [ea_ePos hk]
  rw [e, ptE_symm_posEquiv, phiEquiv_apply]

theorem not_star_hypRoot_one
    (hHF : HyperovalFacts) {T : Set J} (hT : IsLocallyHyperoval D T)
    (haT : a ∈ T) (hstar : ptLocal.pts (T ∩ star) = hypRoot 1) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := failOK_spec lh_parts.2.2.2.2.2.2.2.2.2.2.2.1
  have h63 : (63 : ℕ) ∈ ea := (ePos_lt_iff (by norm_num)).1 h1
  have hmemT : ∀ k (hk : k ∈ ea), conjPt k ∈ T ↔
      hypC 1 uPts[phiData[(ePos ea)[k]!]!]! = true := by
    intro k hk
    have hu := ptE_symm_conjPt hk
    have := mem_hypRoot_iff 1 (ptE.symm ⟨conjPt k, conjPt_mem_star hk⟩)
    rw [hu, show ((1 : Fin 3) : ℕ) = 1 from rfl] at this
    rw [← this, ← hstar, mem_ptLocal_pts, Equiv.apply_symm_apply]
    exact ⟨fun h => ⟨h, conjPt_mem_star hk⟩, fun h => h.1⟩
  have htT : conjPt 63 ∈ T := (hmemT 63 h63).2 h2
  have htstar : conjPt 63 ∈ star := conjPt_mem_star h63
  have hct : conjPt 2751 ∈ LocalClass D (conjPt 63) :=
    (conjPt_mem_localClass (k := 63) (l := 2751) (by norm_num) (by norm_num)).2 ⟨by norm_num, h3⟩
  have hac : a * conjPt 2751 ≠ conjPt 2751 * a := by
    rw [← conjPt_zero, ne_eq, conjPt_commute_iff (c := 0) (i := 2751) (by norm_num) (by norm_num)]
    exact h4
  have hat : a ∈ LocalClass D (conjPt 63) :=
    ⟨a_mem_D, fun h => htstar.2.1 h.symm, htstar.2.2.symm⟩
  obtain ⟨L⟩ := nonempty_localPoints_D (hT.subset htT)
  apply IsHyperovalIn.not_linear hHF pair_D L (hT.hyperoval _ htT) ⟨haT, hat⟩ hct hac
  intro x hxt hxa
  obtain ⟨k, hk, rfl⟩ := mem_D_lt hxt.1
  have hkea : k ∈ ea := (conjPt_mem_star_iff hk).1 hxa
  have hkt := (conjPt_mem_localClass (k := 63) (l := k) (by norm_num) hk).1 hxt
  have hka := (conjPt_mem_localClass (k := 0) (l := k) (by norm_num) hk).1
    (by rw [conjPt_zero]; exact hxa)
  have hiff := h5 k hk
  have hep : (ePos ea)[k]! < 693 := (ePos_lt_iff hk).2 hkea
  rw [Set.mem_inter_iff, hmemT k hkea, conjPt_commute_iff (c := k) (i := 2751) hk (by norm_num)]
  simp only [hxt, and_true]
  constructor
  · intro hh
    have := hiff.1 ⟨hep, hh, hkt.2, hkt.1⟩
    rw [← conjPt_commute_iff (c := k) (i := 2751) hk (by norm_num)]
    exact ((conjPt_commute_iff (c := 2751) (i := k) (by norm_num) hk).2 this.2.2.2.2.1).symm
  · intro hcomm
    have hck : ap tT[2751]! k = k :=
      (conjPt_commute_iff (c := 2751) (i := k) (by norm_num) hk).1
        ((conjPt_commute_iff (c := k) (i := 2751) hk (by norm_num)).2 hcomm).symm
    have hk2751 : k ≠ 2751 := by
      rintro rfl
      exact h4 hka.2
    exact (hiff.2 ⟨hkt.2, hkt.1, hka.2, hka.1, hck, hk2751⟩).2.1

theorem ptLocal_pts_conj
    {h : Ca} {U : Set J} (hU : U ⊆ star) :
    ptLocal.pts ((fun x => (h : J)⁻¹ * x * ((h : J)⁻¹)⁻¹) '' U) =
      ⇑(rho h)⁻¹ '' ptLocal.pts U := by
  have key : ∀ q : Fin 693, (ptE ((rho h)⁻¹ q) : J) = (h : J)⁻¹ * ptE q * ((h : J)⁻¹)⁻¹ := by
    intro q
    rw [← map_inv, rho_apply, Equiv.apply_symm_apply, starAction_val]
    rfl
  ext p
  rw [mem_ptLocal_pts]
  constructor
  · rintro ⟨x, hx, hxp⟩
    obtain ⟨q, hq⟩ := ptE.surjective ⟨x, hU hx⟩
    have hqx : (ptE q : J) = x := congrArg Subtype.val hq
    refine ⟨q, ?_, ?_⟩
    · rw [mem_ptLocal_pts, hqx]
      exact hx
    · apply ptE.injective
      apply Subtype.ext
      rw [key, hqx]
      exact hxp
  · rintro ⟨q, hq, rfl⟩
    exact ⟨ptE q, hq, (key q).symm⟩

theorem exists_mem_lhOrbit
    (hPF : PolarFacts) (hHF : HyperovalFacts) {T : Set D}
    (hT : IsLocallyHyperoval D (Subtype.val '' T)) (hne : T.Nonempty) : ∃ i, T ∈ lhOrbit i := by
  obtain ⟨t, htT⟩ := hne
  obtain ⟨c, hc⟩ := isConj_iff.1 t.2
  set T₁ := ⇑(Pair.conjPerm pair_D c⁻¹) '' T with hT₁
  have hT₁l : IsLocallyHyperoval D (Subtype.val '' T₁) := by
    rw [hT₁, val_image_conjPerm]; exact hT.conj pair_D c⁻¹
  have haT₁ : a ∈ Subtype.val '' T₁ := by
    refine ⟨Pair.conjPerm pair_D c⁻¹ t, ⟨t, htT, rfl⟩, ?_⟩
    rw [Pair.conjPerm_apply, ← hc]
    group
  set O := ptLocal.pts (Subtype.val '' T₁ ∩ star) with hO
  have hOc : IsClosedHyperoval O :=
    (ptLocal.isHyperovalIn_iff hHF.linesByPerp pair_D Set.inter_subset_right).1
      (hT₁l.hyperoval a haT₁)
  have hOne : O.Nonempty := by
    obtain ⟨y, hy⟩ := hT₁l.nonempty a haT₁
    exact ⟨ptE.symm ⟨y, hy.2⟩, by rw [hO, mem_ptLocal_pts, Equiv.apply_symm_apply]; exact hy⟩
  obtain ⟨j, g, hg, hOg⟩ := hPF.exists_mem_hypOrbit O hOc hOne
  rw [← range_rho] at hg
  obtain ⟨h, rfl⟩ := hg
  set T₂ := ⇑(Pair.conjPerm pair_D (h : J)⁻¹) '' T₁ with hT₂
  have hT₂l : IsLocallyHyperoval D (Subtype.val '' T₂) := by
    rw [hT₂, val_image_conjPerm]; exact hT₁l.conj pair_D _
  have hha : (h : J)⁻¹ * a * ((h : J)⁻¹)⁻¹ = a := by
    have := mem_Ca.1 h.2
    rw [inv_inv, mul_assoc, ← this, ← mul_assoc, inv_mul_cancel, one_mul]
  have haT₂ : a ∈ Subtype.val '' T₂ := by
    rw [hT₂, val_image_conjPerm]
    exact ⟨a, haT₁, hha⟩
  have hstar₂ : Subtype.val '' T₂ ∩ star =
      (fun x => (h : J)⁻¹ * x * ((h : J)⁻¹)⁻¹) '' (Subtype.val '' T₁ ∩ star) := by
    rw [hT₂, val_image_conjPerm, image_conj_inter, Pair.image_conj_localClass pair_D, hha]
  have hpts₂ : ptLocal.pts (Subtype.val '' T₂ ∩ star) = hypRoot j := by
    rw [hstar₂, ptLocal_pts_conj Set.inter_subset_right, ← hO, hOg, ← Set.image_comp,
      ← Equiv.Perm.coe_mul, inv_mul_cancel, Equiv.Perm.coe_one, Set.image_id]
  have hback : ∀ i : Fin 2, Subtype.val '' T₂ = Subtype.val '' lhRoot i → T ∈ lhOrbit i := by
    intro i heq
    have h2 : T₂ = lhRoot i := Set.image_injective.2 Subtype.val_injective heq
    refine ⟨c * h, ?_⟩
    rw [← h2, hT₂, hT₁, ← Set.image_comp, ← Set.image_comp, ← Equiv.Perm.coe_mul,
      ← Equiv.Perm.coe_mul, ← map_mul, ← map_mul,
      show c * (h : J) * (h : J)⁻¹ * c⁻¹ = 1 by group, map_one, Equiv.Perm.coe_one, Set.image_id]
  have hroot : ∀ i : Fin 2, ptLocal.pts (Subtype.val '' T₂ ∩ star) =
      ptLocal.pts (Subtype.val '' lhRoot i ∩ star) → T ∈ lhOrbit i := by
    intro i hp
    apply hback i
    apply eq_lhRoot_of_star hHF i hT₂l haT₂
    exact ptLocal.eq_of_pts_eq Set.inter_subset_right Set.inter_subset_right hp
  fin_cases j
  · exact ⟨0, hroot 0 (by rw [hpts₂, ptLocal_pts_lhRoot]; rfl)⟩
  · exact (not_star_hypRoot_one hHF hT₂l haT₂ hpts₂).elim
  · exact ⟨1, hroot 1 (by rw [hpts₂, ptLocal_pts_lhRoot]; rfl)⟩

end CFSG.Sporadic.Fi22
