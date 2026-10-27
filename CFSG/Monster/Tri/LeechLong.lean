module

public import CFSG.Monster.Tri.LeechCover
public import CFSG.Monster.Tri.LeechLongCheck

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.Visible CFSG.Monster.B.Short
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.KstabMaximal

attribute [local instance] olqLeft

@[expose] def longGraph (w : L2) : SimpleGraph L2 where
  Adj c c' := shortGraph.Adj c c' ∧ c' ≠ c + w
  symm := ⟨fun c c' ⟨h, hne⟩ =>
    ⟨h.symm, fun e => hne (by rw [e, add_assoc, add_self_L2, add_zero])⟩⟩
  loopless := ⟨fun _ h => shortGraph.irrefl h.1⟩

theorem longGraph_adj {w c c' : L2} :
    (longGraph w).Adj c c' ↔ shortGraph.Adj c c' ∧ c' ≠ c + w := Iff.rfl

theorem longGraph_adj_kOp (K : OLq) {w c c' : L2} :
    (longGraph (kOp K w)).Adj (kOp K c) (kOp K c') ↔ (longGraph w).Adj c c' := by
  rw [longGraph_adj, longGraph_adj, shortGraph_adj_kOp, ← map_add, (kOp_injective K).ne_iff]

@[expose] def longHom (K : OLq) {w w' : L2} (h : kOp K w = w') : longGraph w →g longGraph w' where
  toFun c := kOp K c
  map_rel' := fun {c c'} hcc => by
    subst h
    exact (longGraph_adj_kOp K).2 hcc

theorem preconnected_longGraph_induce_of_image_kOp (K : OLq) {w : L2} {s : Set L2}
    (h : ((longGraph (kOp K w)).induce (kOp K '' s)).Preconnected) :
    ((longGraph w).induce s).Preconnected := by
  refine CFSG.Monster.B.GSide.preconnected_induce_of_surjOn (longHom K⁻¹ (kOp_inv_apply K w))
    (fun u hu => ?_) (fun u hu => ?_) h
  · obtain ⟨u', hu', rfl⟩ := hu
    change kOp K⁻¹ (kOp K u') ∈ s
    rwa [kOp_inv_apply]
  · exact ⟨kOp K u, ⟨u, hu, rfl⟩, by change kOp K⁻¹ (kOp K u) = u; rw [kOp_inv_apply]⟩

theorem leechLongCheck_parts :
    treeOK shortKlev leechNbr leechLongPar leechLongLev = true ∧
      treeNeOK leechNbr leechLongPar 12288 = true := by
  have h := leechLongCheck_eq_true
  simp only [leechLongCheck, Bool.and_eq_true] at h
  exact h

theorem treeNeOK_spec {vs par : Array Nat} {w : Nat} (h : treeNeOK vs par w = true) :
    ∀ i, i ≠ 0 → i < vs.size → vs[i]! ^^^ vs[par[i]!]! ≠ w := by
  simp only [treeNeOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  intro i hi0 hi
  rcases h i hi with h1 | h1
  · exact absurd h1 hi0
  · exact h1

theorem preconnected_longGraph_neighborSet_v0 :
    ((longGraph v0).induce (shortGraph.neighborSet v0)).Preconnected := by
  refine preconnected_induce_of_tree (longGraph v0) _ nbrPt 4600 (fun i => leechLongPar[i]!)
    (fun i => leechLongLev[i]!) (fun i hi => nbrPt_adj hi) (fun i hi hi0 => ?_) ?_
  · have hi' : i < leechNbr.size := by rw [leechNbr_size]; exact hi
    obtain ⟨hp, hlev, hs⟩ := treeOK_spec leechLongCheck_parts.1 i hi0 hi'
    have hne := treeNeOK_spec leechLongCheck_parts.2 i hi0 hi'
    rw [leechNbr_size] at hp
    refine ⟨hp, hlev, longGraph_adj.2 ⟨(adj_dec_iff (shortHit_leechNbr hi)
      (shortHit_leechNbr hp)).2 hs, fun h => ?_⟩⟩
    have h1 : dec leechNbr[leechLongPar[i]!]! = dec (leechNbr[i]! ^^^ 12288) := by
      rw [dec_xor, dec_12288]
      exact h
    have h2 : leechNbr[leechLongPar[i]!]! = leechNbr[i]! ^^^ 12288 :=
      dec_inj _ _ (shortHit_iff.1 (shortHit_leechNbr hp)).1
        (Nat.xor_lt_two_pow (shortHit_iff.1 (shortHit_leechNbr hi)).1 (by norm_num)) h1
    refine hne ?_
    rw [h2, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · intro a ha
    rw [neighborSet_v0_eq_range] at ha
    obtain ⟨i, rfl⟩ := ha
    exact ⟨i, i.2, rfl⟩

theorem preconnected_longGraph_neighborSet
    {w : L2} (hw : w ∈ shortSet) :
    ((longGraph w).induce (shortGraph.neighborSet w)).Preconnected := by
  obtain ⟨K, _, hK, -⟩ := exists_kOp_eq_seed hw hw
  refine preconnected_longGraph_induce_of_image_kOp K ?_
  rw [← neighborSet_kOp, hK]
  exact preconnected_longGraph_neighborSet_v0

@[expose] noncomputable def longQGraph (w : L2) : SimpleGraph Q := (longGraph w).comap qCls

theorem longQGraph_adj_iff {w : L2} {s s' : Q} :
    (longQGraph w).Adj s s' ↔ shortGraph.Adj (qCls s) (qCls s') ∧ qCls s' ≠ qCls s + w := Iff.rfl

theorem qCls_eq_add_iff {r s s' : Q} :
    qCls s' = qCls s + qCls r ↔ s' = s * r ∨ s' = s * r * zQ := by
  rw [← qCls_mul]
  exact eq_comm.trans qCls_eq_iff

theorem longQGraph_adj_iff_mul {r s s' : Q} :
    (longQGraph (qCls r)).Adj s s' ↔ shortQGraph.Adj s s' ∧ s' ≠ s * r ∧ s' ≠ s * r * zQ := by
  rw [longQGraph_adj_iff, shortQGraph_adj_iff_adj]
  simp only [ne_eq, qCls_eq_add_iff, not_or]

theorem preconnected_longQGraph
    {r : Q} (hr : IsShortCoord (coordOf r)) :
    ((longQGraph (qCls r)).induce (shortQGraph.neighborSet r)).Preconnected := by
  have hp := preconnected_longGraph_neighborSet (show qCls r ∈ shortSet from hr)
  have hc := (preconnected_neighborSet (show qCls r ∈ shortSet from hr)).2
  rw [neighborSet_shortQGraph]
  exact preconnected_induce_comap qCls qCls_surjective hp
    (exists_adj_mem_of_preconnected hp (by rw [hc]; norm_num))

end CFSG.Monster.Tri.Leech
