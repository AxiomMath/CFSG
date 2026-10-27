module

public import CFSG.Monster.Tri.LeechOrbits
public import Certificates.Certificate16024

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.KstabMaximal

attribute [local instance] olqLeft

theorem neighborSet_v0_eq_orbit :
    shortGraph.neighborSet v0 = MulAction.orbit Sgrp (seed 3) := by
  ext y
  constructor
  · exact mem_orbit_seed_three
  · intro hy
    exact ((orbit_invariants hy).1.2 ((seed_adj 3).2 rfl))

theorem ncard_neighborSet_v0 :
    (shortGraph.neighborSet v0).ncard = 4600 := by
  rw [neighborSet_v0_eq_orbit, ncard_orbit_seed]
  rfl

theorem leechNbr_size :
    leechNbr.size = 4600 := (nbrOK_spec leechCheck_parts.1).1

@[expose] def nbrPt (i : ℕ) : L2 := dec leechNbr[i]!

theorem shortHit_leechNbr
    {i : ℕ} (hi : i < 4600) : shortHit shortKlev leechNbr[i]! = true :=
  ((nbrOK_spec leechCheck_parts.1).2.2 i (by rw [leechNbr_size]; exact hi)).1

theorem nbrPt_adj
    {i : ℕ} (hi : i < 4600) : shortGraph.Adj v0 (nbrPt i) :=
  (adj_v0_dec_iff (shortHit_leechNbr hi)).2
    ((nbrOK_spec leechCheck_parts.1).2.2 i (by rw [leechNbr_size]; exact hi)).2

theorem nbrPt_injOn
    {i j : ℕ} (hi : i < 4600) (hj : j < 4600) (h : nbrPt i = nbrPt j) : i = j := by
  have h1 := dec_inj _ _ (shortHit_iff.1 (shortHit_leechNbr hi)).1
    (shortHit_iff.1 (shortHit_leechNbr hj)).1 h
  have hmono := (nbrOK_spec leechCheck_parts.1).2.1
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd h1 (hmono i j hij (by rw [leechNbr_size]; exact hj)).ne
  · exact hij
  · exact absurd h1.symm (hmono j i hij (by rw [leechNbr_size]; exact hi)).ne

theorem neighborSet_v0_eq_range :
    shortGraph.neighborSet v0 = Set.range fun i : Fin 4600 => nbrPt i := by
  have hsub : (Set.range fun i : Fin 4600 => nbrPt i) ⊆ shortGraph.neighborSet v0 :=
    Set.range_subset_iff.2 fun i => nbrPt_adj i.2
  have hinj : Function.Injective fun i : Fin 4600 => nbrPt i := fun i j h =>
    Fin.ext (nbrPt_injOn i.2 j.2 h)
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  rw [ncard_neighborSet_v0, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem preconnected_neighborSet_v0 :
    (shortGraph.induce (shortGraph.neighborSet v0)).Preconnected := by
  refine preconnected_induce_of_tree shortGraph _ nbrPt 4600 (fun i => leechNbrPar[i]!)
    (fun i => leechNbrLev[i]!) (fun i hi => nbrPt_adj hi) (fun i hi hi0 => ?_) ?_
  · obtain ⟨hp, hlev, hs⟩ := treeOK_spec leechCheck_parts.2.1 i hi0
      (by rw [leechNbr_size]; exact hi)
    rw [leechNbr_size] at hp
    refine ⟨hp, hlev, ?_⟩
    exact (adj_dec_iff (shortHit_leechNbr hi) (shortHit_leechNbr hp)).2 hs
  · intro a ha
    rw [neighborSet_v0_eq_range] at ha
    obtain ⟨i, rfl⟩ := ha
    exact ⟨i, i.2, rfl⟩

@[expose] def decPt (vs : Array Nat) (i : ℕ) : L2 := dec vs[i]!

theorem decPt_injOn
    {vs : Array Nat} (hmono : ∀ i j, i < j → j < vs.size → vs[i]! < vs[j]!)
    (hhit : ∀ i < vs.size, shortHit shortKlev vs[i]! = true) {i j : ℕ} (hi : i < vs.size)
    (hj : j < vs.size) (h : decPt vs i = decPt vs j) : i = j := by
  have h1 := dec_inj _ _ (shortHit_iff.1 (hhit i hi)).1 (shortHit_iff.1 (hhit j hj)).1 h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd h1 (hmono i j hij hj).ne
  · exact hij
  · exact absurd h1.symm (hmono j i hij hi).ne

theorem commonNeighbors_aux
    {b : ℕ} {vs par lev : Array Nat}
    (hb : shortHit shortKlev b = true) (hmu : muOK shortKlev leechNbr b vs = true)
    (htree : treeOK shortKlev vs par lev = true) :
    shortGraph.commonNeighbors v0 (dec b) = Set.range (fun i : Fin vs.size => decPt vs i) ∧
    (shortGraph.induce (shortGraph.commonNeighbors v0 (dec b))).Preconnected ∧
    Function.Injective (fun i : Fin vs.size => decPt vs i) := by
  obtain ⟨hmono, hall, hcov⟩ := muOK_spec hmu
  have hhit : ∀ i < vs.size, shortHit shortKlev vs[i]! = true := fun i hi => (hall i hi).1
  have hmem : ∀ i < vs.size, decPt vs i ∈ shortGraph.commonNeighbors v0 (dec b) := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hall i hi
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨(adj_v0_dec_iff h1).2 h2, (adj_dec_iff hb h1).2 (by rwa [Nat.xor_comm])⟩
  have hcov' : ∀ a ∈ shortGraph.commonNeighbors v0 (dec b), ∃ i < vs.size, decPt vs i = a := by
    intro a ha
    rw [SimpleGraph.mem_commonNeighbors] at ha
    obtain ⟨n, hn, rfl⟩ := exists_shortHit_of_mem_shortSet (mem_shortSet_of_adj_right ha.1)
    have h12 : shortHit shortKlev (n ^^^ 12288) = true := (adj_v0_dec_iff hn).1 ha.1
    have hnb : shortHit shortKlev (n ^^^ b) = true := by
      rw [Nat.xor_comm]
      exact (adj_dec_iff hb hn).1 ha.2
    have ha' : dec n ∈ shortGraph.neighborSet v0 := ha.1
    rw [neighborSet_v0_eq_range] at ha'
    obtain ⟨j, hj⟩ := ha'
    have hnj : leechNbr[(j : ℕ)]! = n :=
      dec_inj _ _ (shortHit_iff.1 (shortHit_leechNbr j.2)).1 (shortHit_iff.1 hn).1 hj
    have hmem' : n ∈ leechNbr.toList := mem_toList_iff.2 ⟨j, by rw [leechNbr_size]; exact j.2, hnj⟩
    obtain ⟨i, hi, hin⟩ := mem_toList_iff.1 (hcov n hmem' hnb)
    exact ⟨i, hi, by rw [decPt, hin]⟩
  have hrange : shortGraph.commonNeighbors v0 (dec b) =
      Set.range (fun i : Fin vs.size => decPt vs i) := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, hi, rfl⟩ := hcov' a ha
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact hmem i i.2
  refine ⟨hrange, ?_, fun i j h => Fin.ext (decPt_injOn hmono hhit i.2 j.2 h)⟩
  refine preconnected_induce_of_tree shortGraph _ (decPt vs) vs.size (fun i => par[i]!)
    (fun i => lev[i]!) hmem (fun i hi hi0 => ?_) hcov'
  obtain ⟨hp, hlev, hs⟩ := treeOK_spec htree i hi0 hi
  exact ⟨hp, hlev, (adj_dec_iff (hhit i hi) (hhit _ hp)).2 hs⟩

theorem shortHit_one : shortHit shortKlev 1 = true :=
  shortHit_iff.2 ⟨by norm_num, dec_one_mem_shortSet⟩

theorem shortHit_sixtyFour : shortHit shortKlev 64 = true :=
  shortHit_iff.2 ⟨by norm_num, dec_sixtyFour_mem_shortSet⟩

theorem leechIdx3_size : leechIdx3.size = 275 :=
  Certificates.certificate16024.1

theorem leechIdx4_size : leechIdx4.size = 88 :=
  Certificates.certificate16024.2

theorem commonNeighbors_v0_dec_one :
    (shortGraph.induce (shortGraph.commonNeighbors v0 (dec 1))).Preconnected ∧
      (shortGraph.commonNeighbors v0 (dec 1)).ncard = 275 := by
  obtain ⟨hr, hp, hi⟩ := commonNeighbors_aux shortHit_one leechCheck_parts.2.2.1
    leechCheck_parts.2.2.2.1
  refine ⟨hp, ?_⟩
  rw [hr, Set.ncard_range_of_injective hi, Nat.card_eq_fintype_card, Fintype.card_fin,
    leechIdx3_size]

theorem commonNeighbors_v0_dec_sixtyFour :
    (shortGraph.induce (shortGraph.commonNeighbors v0 (dec 64))).Preconnected ∧
      (shortGraph.commonNeighbors v0 (dec 64)).ncard = 88 := by
  obtain ⟨hr, hp, hi⟩ := commonNeighbors_aux shortHit_sixtyFour leechCheck_parts.2.2.2.2.1
    leechCheck_parts.2.2.2.2.2.1
  refine ⟨hp, ?_⟩
  rw [hr, Set.ncard_range_of_injective hi, Nat.card_eq_fintype_card, Fintype.card_fin,
    leechIdx4_size]

theorem kOp_injective (K : OLq) : Function.Injective (kOp K) := fun a b h => by
  have := congrArg (kOp K⁻¹) h
  rwa [kOp_inv_apply, kOp_inv_apply] at this

theorem kOp_kOp_inv_apply (K : OLq) (x : L2) : kOp K (kOp K⁻¹ x) = x := by
  simpa using kOp_inv_apply K⁻¹ x

theorem commonNeighbors_kOp (K : OLq) (x y : L2) :
    shortGraph.commonNeighbors (kOp K x) (kOp K y) = kOp K '' shortGraph.commonNeighbors x y := by
  ext w
  simp only [SimpleGraph.mem_commonNeighbors, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨kOp K⁻¹ w, ⟨?_, ?_⟩, kOp_kOp_inv_apply K w⟩
    · have := (shortGraph_adj_kOp K⁻¹).2 h1
      rwa [kOp_inv_apply] at this
    · have := (shortGraph_adj_kOp K⁻¹).2 h2
      rwa [kOp_inv_apply] at this
  · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
    exact ⟨(shortGraph_adj_kOp K).2 h1, (shortGraph_adj_kOp K).2 h2⟩

theorem neighborSet_kOp (K : OLq) (x : L2) :
    shortGraph.neighborSet (kOp K x) = kOp K '' shortGraph.neighborSet x := by
  ext w
  simp only [SimpleGraph.mem_neighborSet, Set.mem_image]
  constructor
  · intro h
    refine ⟨kOp K⁻¹ w, ?_, kOp_kOp_inv_apply K w⟩
    have := (shortGraph_adj_kOp K⁻¹).2 h
    rwa [kOp_inv_apply] at this
  · rintro ⟨u, h, rfl⟩
    exact (shortGraph_adj_kOp K).2 h

theorem ncard_commonNeighbors_kOp (K : OLq) (x y : L2) :
    (shortGraph.commonNeighbors (kOp K x) (kOp K y)).ncard =
      (shortGraph.commonNeighbors x y).ncard := by
  rw [commonNeighbors_kOp, Set.ncard_image_of_injective _ (kOp_injective K)]

theorem ncard_neighborSet_kOp (K : OLq) (x : L2) :
    (shortGraph.neighborSet (kOp K x)).ncard = (shortGraph.neighborSet x).ncard := by
  rw [neighborSet_kOp, Set.ncard_image_of_injective _ (kOp_injective K)]

theorem preconnected_induce_of_image_kOp (K : OLq) {s : Set L2}
    (h : (shortGraph.induce (kOp K '' s)).Preconnected) : (shortGraph.induce s).Preconnected := by
  refine CFSG.Monster.B.GSide.preconnected_induce_of_surjOn (kOpHom K⁻¹) (fun w hw => ?_)
    (fun u hu => ?_) h
  · obtain ⟨u, hu, rfl⟩ := hw
    change kOp K⁻¹ (kOp K u) ∈ s
    rwa [kOp_inv_apply]
  · exact ⟨kOp K u, ⟨u, hu, rfl⟩, by change kOp K⁻¹ (kOp K u) = u; rw [kOp_inv_apply]⟩

theorem preconnected_commonNeighbors_of_kOp (K : OLq) {x y : L2}
    (h : (shortGraph.induce (shortGraph.commonNeighbors (kOp K x) (kOp K y))).Preconnected) :
    (shortGraph.induce (shortGraph.commonNeighbors x y)).Preconnected :=
  preconnected_induce_of_image_kOp K (by rwa [← commonNeighbors_kOp])

theorem preconnected_neighborSet_of_kOp (K : OLq) {x : L2}
    (h : (shortGraph.induce (shortGraph.neighborSet (kOp K x))).Preconnected) :
    (shortGraph.induce (shortGraph.neighborSet x)).Preconnected :=
  preconnected_induce_of_image_kOp K (by rwa [← neighborSet_kOp])

theorem exists_kOp_eq_seed
    {x y : L2} (hx : x ∈ shortSet) (hy : y ∈ shortSet) :
    ∃ (K : OLq) (i : Fin 4), kOp K x = v0 ∧ kOp K y = seed i := by
  obtain ⟨k, i, h1, h2⟩ := exists_smul_eq_seed hx hy
  exact ⟨k⁻¹, i, h1, h2⟩

theorem exists_kOp_eq_pair_three
    {x y : L2} (hx : x ∈ shortSet) (hy : y ∈ shortSet)
    (h : qL (x + y) = 1) : ∃ K : OLq, kOp K x = v0 ∧ kOp K y = dec 1 := by
  obtain ⟨K, i, h1, h2⟩ := exists_kOp_eq_seed hx hy
  have hq : qL (v0 + seed i) = 1 := by
    rw [← h1, ← h2, ← map_add, qL_kOp]
    exact h
  obtain rfl := (seed_qL i).1 hq
  exact ⟨K, h1, h2⟩

theorem exists_kOp_eq_pair_four
    {x y : L2} (hx : x ∈ shortSet) (hy : y ∈ shortSet)
    (h : x + y ∈ frameDelta) : ∃ K : OLq, kOp K x = v0 ∧ kOp K y = dec 64 := by
  obtain ⟨K, i, h1, h2⟩ := exists_kOp_eq_seed hx hy
  have hd : v0 + seed i ∈ frameDelta := by
    rw [← h1, ← h2, ← map_add]
    exact (kOp_mem_frameDelta_iff K).2 h
  obtain rfl := (seed_delta i).1 hd
  exact ⟨K, h1, h2⟩

theorem shortGraph_diam_le_two
    {x y : L2} (hx : x ∈ shortSet) (hy : y ∈ shortSet) :
    x = y ∨ shortGraph.Adj x y ∨ (shortGraph.commonNeighbors x y).Nonempty := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  refine Or.inr ?_
  rcases shortSet_pair_trichotomy hx hy hxy with h | h | h
  · exact Or.inl h
  · refine Or.inr ?_
    obtain ⟨K, h1, h2⟩ := exists_kOp_eq_pair_three hx hy h
    have hn := ncard_commonNeighbors_kOp K x y
    rw [h1, h2, commonNeighbors_v0_dec_one.2] at hn
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  · refine Or.inr ?_
    obtain ⟨K, h1, h2⟩ := exists_kOp_eq_pair_four hx hy h
    have hn := ncard_commonNeighbors_kOp K x y
    rw [h1, h2, commonNeighbors_v0_dec_sixtyFour.2] at hn
    exact Set.nonempty_of_ncard_ne_zero (by omega)

theorem preconnected_mu_three
    {x y : L2} (hx : x ∈ shortSet) (hy : y ∈ shortSet)
    (h : qL (x + y) = 1) :
    (shortGraph.induce (shortGraph.commonNeighbors x y)).Preconnected ∧
      (shortGraph.commonNeighbors x y).ncard = 275 := by
  obtain ⟨K, h1, h2⟩ := exists_kOp_eq_pair_three hx hy h
  refine ⟨preconnected_commonNeighbors_of_kOp K ?_, ?_⟩
  · rw [h1, h2]
    exact commonNeighbors_v0_dec_one.1
  · rw [← ncard_commonNeighbors_kOp K x y, h1, h2]
    exact commonNeighbors_v0_dec_one.2

theorem preconnected_neighborSet
    {x : L2} (hx : x ∈ shortSet) :
    (shortGraph.induce (shortGraph.neighborSet x)).Preconnected ∧
      (shortGraph.neighborSet x).ncard = 4600 := by
  obtain ⟨K, i, h1, -⟩ := exists_kOp_eq_seed hx hx
  refine ⟨preconnected_neighborSet_of_kOp K ?_, ?_⟩
  · rw [h1]
    exact preconnected_neighborSet_v0
  · rw [← ncard_neighborSet_kOp K x, h1]
    exact ncard_neighborSet_v0

end CFSG.Monster.Tri.Leech
