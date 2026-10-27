module

public import CFSG.Sporadic.Fi22.LH.Classify

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.F3.Native Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem eq_lhRoot_of_agree
    (hHF : HyperovalFacts) (i : Fin 2) {T : Set J}
    (hT : IsLocallyHyperoval D T) {p : J} (hpT : p ∈ T) (hpR : p ∈ Subtype.val '' lhRoot i)
    (hp : T ∩ LocalClass D p = Subtype.val '' lhRoot i ∩ LocalClass D p) :
    T = Subtype.val '' lhRoot i := by
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
  have hmemR : ∀ k < 351, conjPt (lhc.cord[i.val]!)[k]! ∈ Subtype.val '' lhRoot i := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [ho0, conjPt_zero]; exact haR
    · exact (conjPt_mem_lhRoot (hlt k hk)).2 (hopar k hk0 hk).2.1
  have hedge : ∀ k, 1 ≤ k → k < 351 →
      conjPt (lhc.cord[i.val]!)[k]! ∈
          LocalClass D (conjPt (lhc.cord[i.val]!)[(lhc.cpar[i.val]!)[k]!]!) ∧
        conjPt (lhc.cord[i.val]!)[(lhc.cpar[i.val]!)[k]!]! ∈
          LocalClass D (conjPt (lhc.cord[i.val]!)[k]!) := by
    intro k hk0 hk
    obtain ⟨hp, -, hc, hn⟩ := hopar k hk0 hk
    have hpk : (lhc.cpar[i.val]!)[k]! < 351 := by omega
    have h1 := (conjPt_mem_localClass (hlt _ hpk) (hlt k hk)).2 ⟨Ne.symm hn, hc⟩
    exact ⟨h1, conjPt_lt_mem_D (hlt _ hpk), fun e => h1.2.1 e.symm, h1.2.2.symm⟩
  have hup : ∀ k < 351, good (conjPt (lhc.cord[i.val]!)[k]!) →
      good (conjPt (lhc.cord[i.val]!)[0]!) := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hg
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact hg
      · obtain ⟨hp, -, -, -⟩ := hopar k hk0 hk
        have hpk : (lhc.cpar[i.val]!)[k]! < 351 := by omega
        exact ih _ hp hpk (hstep _ _ hg (hmemR _ hpk) (hedge k hk0 hk).2)
  have hdown : good (conjPt (lhc.cord[i.val]!)[0]!) →
      ∀ k < 351, good (conjPt (lhc.cord[i.val]!)[k]!) := by
    intro h0 k hk
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact h0
      · obtain ⟨hp, -, -, -⟩ := hopar k hk0 hk
        have hpk : (lhc.cpar[i.val]!)[k]! < 351 := by omega
        exact hstep _ _ (ih _ hp hpk) (hmemR k hk) (hedge k hk0 hk).1
  have hpos : ∀ x ∈ Subtype.val '' lhRoot i, ∃ k < 351, x = conjPt (lhc.cord[i.val]!)[k]! := by
    intro x hx
    obtain ⟨y, hy, rfl, hyB⟩ := mem_val_lhRoot.1 hx
    have hyS := (bitAt_B_iff i.2 hy).1 hyB
    obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.1 (hocov _ hyS)
    refine ⟨k, by omega, ?_⟩
    rw [getElem!_pos _ k hk, hke]
  obtain ⟨kp, hkp, rfl⟩ := hpos p hpR
  have hgoodR : ∀ x ∈ Subtype.val '' lhRoot i, good x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hpos x hx
    exact hdown (hup kp hkp ⟨hpT, hpR, hp⟩) k hk
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

end CFSG.Sporadic.Fi22
