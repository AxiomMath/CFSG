module

public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerLines

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank

variable {ℓ f p r : ℕ} {K : Type} [Field K] {Ahat : Subgroup (StatedSp r K)}

@[expose] def centralizerSpan (Ahat : Subgroup (StatedSp r K)) : Subgroup (StatedSp r K) :=
  Subgroup.closure {g : StatedSp r K | ∃ x ∈ Ahat, x ≠ 1 ∧ g * x = x * g}

theorem mem_centralizerSpan {x g : StatedSp r K} (hxA : x ∈ Ahat) (hx1 : x ≠ 1)
    (hg : g * x = x * g) : g ∈ centralizerSpan Ahat :=
  Subgroup.subset_closure ⟨x, hxA, hx1, hg⟩

theorem transCenter_of_fixed {x : StatedSp r K} (hxA : x ∈ Ahat) (hx1 : x ≠ 1)
    {u : Fin r ⊕ Fin r → K} (hu : spEnd x u = u) : TransCenter (centralizerSpan Ahat) u :=
  fun t => mem_centralizerSpan hxA hx1 (commute_spTransvection hu t)

theorem spPlane_exists_ne_one (S : SpPlaneSetup ℓ f p r K Ahat) :
    ∃ a : ↥Ahat, a ≠ 1 := by
  have := S.finite
  have h1 : Nontrivial ↥Ahat := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [S.card_plane]
    exact Nat.one_lt_pow two_ne_zero S.prime_p.one_lt)
  exact exists_ne (1 : ↥Ahat)

theorem spPlane_exists_ne_one_of_card (S : SpPlaneSetup ℓ f p r K Ahat)
    {M : Subgroup ↥Ahat} (hM : Nat.card M = p) : ∃ t : ↥Ahat, t ∈ M ∧ t ≠ 1 := by
  have := S.finite
  have h1 : Nontrivial ↥M :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hM]; exact S.prime_p.one_lt)
  obtain ⟨t, ht⟩ := exists_ne (1 : ↥M)
  exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩

theorem transCenter_of_mem_summand (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    (i : Option {M : Subgroup ↥Ahat // Nat.card M = p}) {c : Fin r ⊕ Fin r → K}
    (hc : c ∈ spInnerSummand p Ahat i) : TransCenter (centralizerSpan Ahat) c := by
  rcases i with _ | ⟨M, hM⟩
  · obtain ⟨a, ha⟩ := spPlane_exists_ne_one S
    refine transCenter_of_fixed a.2 (fun h => ha (Subtype.ext h)) ?_
    exact mem_fixSub.mp hc a (Subgroup.mem_top a)
  · obtain ⟨t, htM, ht1⟩ := spPlane_exists_ne_one_of_card S hM
    have hker := (D.ker_eq M hM t htM ht1).1
    have hc' : c ∈ spLineFix M := (inf_le_left : spLineSpace M ≤ spLineFix M) hc
    rw [← hker] at hc'
    exact transCenter_of_fixed t.2 (fun h => ht1 (Subtype.ext h)) (mem_ker_sub_one_iff.mp hc')

theorem transCenter_add_of_mem_summands (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    {M : Subgroup ↥Ahat} (hM : Nat.card M = p) {y y' : Fin r ⊕ Fin r → K}
    (hy : y ∈ spPlaneFix Ahat) (hy' : y' ∈ spLineSpace M) :
    TransCenter (centralizerSpan Ahat) (y + y') := by
  obtain ⟨t, htM, ht1⟩ := spPlane_exists_ne_one_of_card S hM
  have hker := D.ker_eq M hM t htM ht1
  have hmem : y + y' ∈ spLineFix M := by
    rw [hker.2]
    exact Submodule.add_mem_sup hy hy'
  rw [← hker.1] at hmem
  exact transCenter_of_fixed t.2 (fun h => ht1 (Subtype.ext h)) (mem_ker_sub_one_iff.mp hmem)

end CFSG.RankThree.PartOne.CTP
