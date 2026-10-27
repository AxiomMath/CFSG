module

public import CFSG.RankThree.PartTwo.Sec4.E27.ReeEightModel

public noncomputable section

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits HuppertReeEight

namespace CFSG.RankThree.PartTwo.Sec4.E27.ReeEight


theorem genCheckAt_spec {d : PlaneDatum} (h : genCheckAt d = true) :
    (∀ w ∈ d.gu ++ d.gv, lettersOK 4 w = true) ∧
      (∀ w ∈ d.gu, commE (aArr d.u) (aArr w) = true) ∧
      (∀ w ∈ d.gv, commE (aArr d.v) (aArr w) = true) ∧
      (∀ c ∈ (d.gu ++ d.gv).map aArr, isInvA 1755 c (invCand 1755 c) = true) ∧
      ∀ i < 4, lettersOK (d.gu ++ d.gv).length (d.prog.getD i []) = true ∧
        eqA 1755 titsGenArrs[i]!
          (wordArr 1755 ((d.gu ++ d.gv).map aArr).toArray (d.prog.getD i [])) = true := by
  simp only [genCheckAt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    List.size_toArray, List.length_map] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h6⟩

theorem eq_top_of_genCheck (hg : genCheck () = true) {d : PlaneDatum} (hd : d ∈ planeData)
    (hlu : lettersOK 4 d.u = true) (hlv : lettersOK 4 d.v = true) {F : Subgroup ↥titsA}
    (hF1 : ∀ k : ↥titsA, k * valA d.u = valA d.u * k → k ∈ F)
    (hF2 : ∀ k : ↥titsA, k * valA d.v = valA d.v * k → k ∈ F) : F = ⊤ := by
  have h := List.all_eq_true.1 hg d hd
  obtain ⟨hlet, hcu, hcv, hinv, hprog⟩ := genCheckAt_spec h
  set gens : List (List ℤ) := d.gu ++ d.gv with hgens
  set m : ℕ := gens.length with hm
  set Cs : Array (Array ℕ) := (gens.map aArr).toArray with hCs
  let gsA : ℕ → ↥titsA := fun t => valA (gens.getD t [])
  have hget : ∀ t (ht : t < gens.length), gens.getD t [] = gens[t] := fun t ht => by
    simp [List.getD_eq_getElem?_getD, ht]
  have hmem : ∀ t < m, gens.getD t [] ∈ gens := fun t ht => by
    rw [hget t ht]
    exact List.getElem_mem ht
  have hCt : ∀ t < m, Cs[t]! = aArr (gens.getD t []) := fun t ht => by
    have ht' : t < gens.length := ht
    rw [hget t ht']
    simp [hCs, getElem!_pos, ht', List.getElem?_eq_getElem ht']
  have hgsF : ∀ t < m, gsA t ∈ F := by
    intro t ht
    have hw := hmem t ht
    have hrw := rep_valA (hlet _ hw)
    rcases List.mem_append.1 hw with hw1 | hw2
    · exact hF1 _ (((commE_iff (rep_valA hlu) hrw).1 (hcu _ hw1)).symm)
    · exact hF2 _ (((commE_iff (rep_valA hlv) hrw).1 (hcv _ hw2)).symm)
  have hA : ∀ t < m, Rep 1755 Cs[t]! (gsA t : Equiv.Perm (Fin 1755)) := fun t ht => by
    rw [hCt t ht]
    exact rep_valA (hlet _ (hmem t ht))
  have hinvA : ∀ t < m, isInvA 1755 Cs[t]! (invCand 1755 Cs[t]!) = true := fun t ht => by
    rw [hCt t ht]
    exact hinv _ (List.mem_map.2 ⟨_, hmem t ht, rfl⟩)
  have hletter : ∀ i : ℕ, ∀ hi : i < 4, (⟨titsGen i, titsGen_mem hi⟩ : ↥titsA) ∈ F := by
    intro i hi
    obtain ⟨hl, he⟩ := hprog i hi
    have hrep := rep_wordArr (k := m) (A := Cs) (gs := fun t => (gsA t : Equiv.Perm (Fin 1755)))
      (by simp [hCs, hm]) hA hinvA hl
    have heq := eq_of_eqA (titsGen_rep hi) hrep he
    have hmemF : wordIn m gsA (d.prog.getD i []) ∈ F := wordIn_mem hgsF _
    have hcoe : ((wordIn m gsA (d.prog.getD i []) : ↥titsA) : Equiv.Perm (Fin 1755)) =
        wordIn m (fun t => (gsA t : Equiv.Perm (Fin 1755))) (d.prog.getD i []) :=
      map_wordIn titsA.subtype m gsA _
    have : (⟨titsGen i, titsGen_mem hi⟩ : ↥titsA) = wordIn m gsA (d.prog.getD i []) :=
      Subtype.ext (heq.trans hcoe.symm)
    rw [this]
    exact hmemF
  rw [eq_top_iff]
  intro g _
  have hle : titsA ≤ F.map titsA.subtype := by
    show Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨titsGen i, titsGen_mem i.2⟩, hletter i i.2, rfl⟩
  obtain ⟨f, hf, hfg⟩ := hle g.2
  have : f = g := Subtype.ext hfg
  rwa [← this]

end CFSG.RankThree.PartTwo.Sec4.E27.ReeEight
