module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiW

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

@[expose] def sc (l : List (Fin 6)) : SC :=
  (fun k => if (⟨k.val, by omega⟩ : Fin 6) ∈ l then 1 else 0,
    fun k => if (⟨k.val + 3, by omega⟩ : Fin 6) ∈ l then 1 else 0)

@[expose] def scOrbL : Fin 10 → List (List (Fin 6)) :=
  ![[[0, 1, 2]],
    [[2], [1], [0]],
    [[5], [4], [3], [2, 5], [1, 4], [0, 3]],
    [[1, 2], [0, 2], [0, 1]],
    [[2, 4], [2, 3], [1, 5], [1, 3], [1, 2, 5], [1, 2, 4], [0, 5], [0, 4], [0, 2, 5], [0, 2, 3],
      [0, 1, 4], [0, 1, 3]],
    [[4, 5], [3, 5], [3, 4], [2, 4, 5], [2, 3, 5], [1, 4, 5], [1, 3, 4], [1, 2, 4, 5], [0, 3, 5],
      [0, 3, 4], [0, 2, 3, 5], [0, 1, 3, 4]],
    [[1, 2, 3], [0, 2, 4], [0, 1, 5], [0, 1, 2, 5], [0, 1, 2, 4], [0, 1, 2, 3]],
    [[2, 3, 4], [1, 3, 5], [1, 2, 3, 5], [1, 2, 3, 4], [0, 4, 5], [0, 2, 4, 5], [0, 2, 3, 4],
      [0, 1, 4, 5], [0, 1, 3, 5], [0, 1, 2, 4, 5], [0, 1, 2, 3, 5], [0, 1, 2, 3, 4]],
    [[2, 3, 4, 5], [1, 3, 4, 5], [0, 3, 4, 5], [0, 1, 2, 3, 4, 5]],
    [[3, 4, 5], [1, 2, 3, 4, 5], [0, 2, 3, 4, 5], [0, 1, 3, 4, 5]]]

@[expose] def scOrb (i : Fin 10) : Finset SC := ((scOrbL i).map sc).toFinset

@[expose] def IsClosedSC (F : Set SC) : Prop :=
  ∀ x ∈ F, actMu x ∈ F ∧ actMu' x ∈ F ∧ actTau x ∈ F ∧ actXi x ∈ F

@[expose] def actOf : Fin 4 → SC → SC := ![actMu, actMu', actTau, actXi]

theorem actOf_mem {F : Set SC} (hF : IsClosedSC F) {x : SC} (hx : x ∈ F) (j : Fin 4) :
    actOf j x ∈ F := by
  obtain ⟨h0, h1, h2, h3⟩ := hF x hx
  fin_cases j
  exacts [h0, h1, h2, h3]

@[expose] def actWord : List (Fin 4) → SC → SC
  | [], x => x
  | j :: w, x => actWord w (actOf j x)

theorem actWord_mem {F : Set SC} (hF : IsClosedSC F) {x : SC} (hx : x ∈ F) :
    ∀ w : List (Fin 4), actWord w x ∈ F
  | [] => hx
  | j :: w => actWord_mem hF (actOf_mem hF hx j) w

@[expose] def scFw : Fin 10 → List (List (Fin 4)) :=
  ![[[]],
    [[], [3, 2], [3]],
    [[], [3, 2], [3], [1], [1, 3, 2], [1, 3]],
    [[], [2], [2, 3]],
    [[], [2], [3, 2], [3, 3], [0, 3, 2], [0], [3], [2, 3], [0, 3], [0, 2], [0, 2, 3], [0, 3, 3]],
    [[], [2], [2, 3], [1], [0, 3], [0], [0, 2, 3], [0, 1], [0, 2], [0, 3, 3], [2, 1], [2, 1, 3]],
    [[], [2], [2, 3], [0, 2, 3], [0, 2], [0]],
    [[], [3, 2], [1, 3, 3], [0, 1], [3], [3, 1], [1], [1, 3], [1, 3, 2], [0, 3], [0, 3, 2], [0]],
    [[], [0, 1], [1], [0]],
    [[], [0, 1], [1], [0]]]

@[expose] def scBw : Fin 10 → List (List (Fin 4)) :=
  ![[[]],
    [[], [3], [2, 3]],
    [[], [3], [2, 3], [1], [0, 3], [0, 2, 3]],
    [[], [2], [3]],
    [[], [2], [3, 2], [3], [1, 3, 2], [0], [3, 3], [2, 3], [1, 3, 3], [0, 2], [0, 2, 3], [0, 3]],
    [[], [2], [3], [1], [2, 1], [0], [3, 1], [0, 1], [0, 2], [1, 3], [1, 2], [0, 3]],
    [[], [2], [3], [1, 3], [0, 2], [0]],
    [[], [3], [3, 1], [0, 1], [2, 3], [1, 2, 3], [1], [0, 2, 3], [0, 3], [2, 1, 3], [1, 3], [0]],
    [[], [3], [1], [0]],
    [[], [0, 1], [1], [0]]]

theorem scFw_spec : ∀ i : Fin 10, ∀ k < (scOrbL i).length,
    actWord ((scFw i).getD k []) (sc ((scOrbL i).getD 0 [])) = sc ((scOrbL i).getD k []) := by
  decide

theorem scBw_spec : ∀ i : Fin 10, ∀ k < (scOrbL i).length,
    actWord ((scBw i).getD k []) (sc ((scOrbL i).getD k [])) = sc ((scOrbL i).getD 0 []) := by
  decide

theorem mem_scOrb {i : Fin 10} {x : SC} :
    x ∈ scOrb i ↔ ∃ k < (scOrbL i).length, x = sc ((scOrbL i).getD k []) := by
  simp only [scOrb, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨k, hk, hkl⟩ := List.getElem_of_mem hl
    exact ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk, hkl]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, List.getElem_mem hk, by rw [List.getD_eq_getElem _ _ hk]⟩

theorem scOrb_subset_of_closed {F : Set SC} (hF : IsClosedSC F) {i : Fin 10} {x : SC}
    (hxi : x ∈ scOrb i) (hxF : x ∈ F) : ↑(scOrb i) ⊆ F := by
  obtain ⟨k, hk, rfl⟩ := mem_scOrb.mp hxi
  have hhead := scBw_spec i k hk ▸ actWord_mem hF hxF ((scBw i).getD k [])
  intro y hy
  obtain ⟨k', hk', rfl⟩ := mem_scOrb.mp (Finset.mem_coe.mp hy)
  rw [← scFw_spec i k' hk']
  exact actWord_mem hF hhead _

theorem scOrb_cover : ∀ x : SC, x ≠ 0 → ∃ i, x ∈ scOrb i := by decide

theorem scOrb_disjoint : ∀ i j : Fin 10, i ≠ j → Disjoint (scOrb i) (scOrb j) := by decide

theorem card_scOrb : ∀ i : Fin 10, (scOrb i).card = ![1, 3, 6, 3, 12, 12, 6, 12, 4, 4] i := by
  decide

theorem eq_biUnion_of_closed {F : Finset SC} (hF : IsClosedSC ↑F) (h0 : (0 : SC) ∉ F) :
    F = (Finset.univ.filter fun i => scOrb i ⊆ F).biUnion scOrb := by
  ext x
  constructor
  · intro hx
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    obtain ⟨i, hi⟩ := scOrb_cover x hx0
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hi⟩
    exact fun y hy => scOrb_subset_of_closed hF hi hx (Finset.mem_coe.mpr hy)
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hi).2 hxi

theorem card_eq_sum_of_closed {F : Finset SC} (hF : IsClosedSC ↑F) (h0 : (0 : SC) ∉ F) :
    F.card = ∑ i ∈ Finset.univ.filter (fun i => scOrb i ⊆ F), (scOrb i).card := by
  conv_lhs => rw [eq_biUnion_of_closed hF h0]
  exact Finset.card_biUnion fun i _ j _ hij => scOrb_disjoint i j hij

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
