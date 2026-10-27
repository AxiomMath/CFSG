module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviCore
public import CFSG.LocalAnalysis.StandardType.GGTBJLeviAssemble
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Curtis.UnitaryLevi
  CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootChar_nsmul_single)

@[expose] def e6LeviDel : Finset (Finset (Fin 6)) :=
  {{0}, {5}, {1}, {0, 5}, {0, 1}, {1, 5}, {0, 2}, {4, 5}, {1, 4, 5}, {0, 1, 5}, {0, 4, 5},
    {0, 2, 5}, {0, 1, 2}}

section

private def e6k_theta : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

private theorem e6k_theta_eq :
    kacE6.θ = e6k_theta := rfl

open scoped CFSG.Decide.Bounded in
private theorem e6k_conn_cases : ∀ c ∈ e6Conn, 3 ≤ c.length → c.length ≤ 6 →
    c = [0, 2, 4] ∨ c = [0, 2, 3, 4] ∨ c = [0, 2, 4, 5] ∨ c = [0, 1, 2, 3, 4] ∨
    c = [0, 2, 3, 4, 5] ∨ c = [0, 2, 4, 5, 6] ∨ c = [0, 1, 2, 3, 4, 5] ∨ c = [0, 2, 3, 4, 5, 6] ∨
    c = [1, 3, 4] ∨ c = [2, 3, 4] ∨ c = [2, 4, 5] ∨ c = [3, 4, 5] ∨ c = [4, 5, 6] ∨
    c = [2, 3, 4, 5] ∨ c = [3, 4, 5, 6] ∨ c = [1, 3, 4, 5] ∨ c = [2, 4, 5, 6] ∨
    c = [1, 2, 3, 4] ∨ c = [2, 3, 4, 5, 6] ∨ c = [1, 2, 3, 4, 5] ∨ c = [1, 3, 4, 5, 6] ∨
    c = [1, 2, 3, 4, 5, 6] := by
  decide +kernel

private def e6k_leviDel' : Finset (Finset (Fin Tag.E6.rank)) :=
  {{0}, {5}, {1}, {0, 5}, {0, 1}, {1, 5}, {0, 2}, {4, 5}, {1, 4, 5}, {0, 1, 5}, {0, 4, 5},
    {0, 2, 5}, {0, 1, 2}}

open scoped CFSG.Decide.Bounded in
private theorem e6k_levi_del_cases : ∀ c ∈ e6Conn, 3 ≤ c.length → c.length ≤ 5 → 0 ∉ c →
    ∃ S ∈ e6k_leviDel', ∀ j : Fin Tag.E6.rank,
      some j ∈ ((c.map (idxNode (r := Tag.E6.rank))).toFinset :
        Finset (Option (Fin Tag.E6.rank))) ↔ j ∉ S := by
  decide +kernel

private def e6k_wordAct :
    List (Fin Tag.E6.rank) → (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)
  | [], v => v
  | i :: l, v => reflect .E6 i (e6k_wordAct l v)

private theorem e6k_wordW_smul_wordAct
    (l : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    wordW .E6 l • v = e6k_wordAct l v := by
  induction l with
  | nil => simp [wordW, e6k_wordAct]
  | cons i l ih =>
    have h1 : wordW .E6 (i :: l) = simple .E6 i * wordW .E6 l := rfl
    rw [h1, mul_smul, ih, simple_smul]
    rfl

private theorem e6k_wordW_reverse
    (l : List (Fin Tag.E6.rank)) :
    wordW .E6 l.reverse = (wordW .E6 l)⁻¹ := by
  induction l with
  | nil => simp [wordW]
  | cons i l ih =>
    have h1 : wordW .E6 (i :: l) = simple .E6 i * wordW .E6 l := rfl
    have h2 : wordW .E6 [i] = simple .E6 i := rfl
    rw [List.reverse_cons, wordW_append, ih, h1, h2, mul_inv_rev, simple_inv]

private theorem e6k_toVec_ofFn {n : ℕ} (f : Fin n → ℤ) : toVec n (List.ofFn f) = f :=
  toVec_vofFn f

private def e6k_word1 : List (Fin Tag.E6.rank) := [2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2]

private def e6k_word2 : List (Fin Tag.E6.rank) := [5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4]

private def e6k_word3 : List (Fin Tag.E6.rank) := [1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2]

private def e6k_word4 : List (Fin Tag.E6.rank) := [1, 3, 4, 2, 3, 0, 2, 1, 3, 4]

private def e6k_word5 : List (Fin Tag.E6.rank) := [0, 2, 3, 4, 1, 3, 2, 0]

private def e6k_word6 : List (Fin Tag.E6.rank) := [1, 3, 4, 5, 2, 3, 4, 1, 3, 2]

private def e6k_N024 : Finset (Option (Fin Tag.E6.rank)) := {none, some 1, some 3}

private def e6k_N0234 : Finset (Option (Fin Tag.E6.rank)) := {none, some 1, some 2, some 3}

private def e6k_N0245 : Finset (Option (Fin Tag.E6.rank)) := {none, some 1, some 3, some 4}

private def e6k_N01234 : Finset (Option (Fin Tag.E6.rank)) :=
  {none, some 0, some 1, some 2, some 3}

private def e6k_N02345 : Finset (Option (Fin Tag.E6.rank)) :=
  {none, some 1, some 2, some 3, some 4}

private def e6k_N02456 : Finset (Option (Fin Tag.E6.rank)) :=
  {none, some 1, some 3, some 4, some 5}

private def e6k_N012345 : Finset (Option (Fin Tag.E6.rank)) :=
  {none, some 0, some 1, some 2, some 3, some 4}

private def e6k_N023456 : Finset (Option (Fin Tag.E6.rank)) :=
  {none, some 1, some 2, some 3, some 4, some 5}

open scoped CFSG.Decide.Bounded in
private theorem e6k_check1M : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N024 (toVec Tag.E6.rank l) ↔
      ∀ j ∈ ({0, 1, 2} : Finset (Fin Tag.E6.rank)),
        (e6k_wordAct e6k_word1 (toVec Tag.E6.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_check1N : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N024 (e6k_wordAct e6k_word1.reverse (toVec Tag.E6.rank l)) ↔
      ∀ j ∈ ({0, 1, 2} : Finset (Fin Tag.E6.rank)), (toVec Tag.E6.rank l) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_check2M : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N0234 (toVec Tag.E6.rank l) ↔
      ∀ j ∈ ({1, 5} : Finset (Fin Tag.E6.rank)),
        (e6k_wordAct e6k_word2 (toVec Tag.E6.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_check2N : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N0234 (e6k_wordAct e6k_word2.reverse (toVec Tag.E6.rank l)) ↔
      ∀ j ∈ ({1, 5} : Finset (Fin Tag.E6.rank)), (toVec Tag.E6.rank l) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_check3M : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N0245 (toVec Tag.E6.rank l) ↔
      ∀ j ∈ ({0, 1} : Finset (Fin Tag.E6.rank)),
        (e6k_wordAct e6k_word3 (toVec Tag.E6.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_check3N : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N0245 (e6k_wordAct e6k_word3.reverse (toVec Tag.E6.rank l)) ↔
      ∀ j ∈ ({0, 1} : Finset (Fin Tag.E6.rank)), (toVec Tag.E6.rank l) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_check4M : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N01234 (toVec Tag.E6.rank l) ↔
      ∀ j ∈ ({1} : Finset (Fin Tag.E6.rank)),
        (e6k_wordAct e6k_word4 (toVec Tag.E6.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_check4N : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N01234 (e6k_wordAct e6k_word4.reverse (toVec Tag.E6.rank l)) ↔
      ∀ j ∈ ({1} : Finset (Fin Tag.E6.rank)), (toVec Tag.E6.rank l) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_check5M : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N02345 (toVec Tag.E6.rank l) ↔
      ∀ j ∈ ({0} : Finset (Fin Tag.E6.rank)),
        (e6k_wordAct e6k_word5 (toVec Tag.E6.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_check5N : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N02345 (e6k_wordAct e6k_word5.reverse (toVec Tag.E6.rank l)) ↔
      ∀ j ∈ ({0} : Finset (Fin Tag.E6.rank)), (toVec Tag.E6.rank l) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_check6M : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N02456 (toVec Tag.E6.rank l) ↔
      ∀ j ∈ ({1} : Finset (Fin Tag.E6.rank)),
        (e6k_wordAct e6k_word6 (toVec Tag.E6.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_check6N : ∀ l ∈ Tag.E6.artifactRoots,
    (kacTest e6k_theta e6k_N02456 (e6k_wordAct e6k_word6.reverse (toVec Tag.E6.rank l)) ↔
      ∀ j ∈ ({1} : Finset (Fin Tag.E6.rank)), (toVec Tag.E6.rank l) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_allPhi1 : ∀ l ∈ Tag.E6.artifactRoots,
    kacTest e6k_theta e6k_N012345 (toVec Tag.E6.rank l) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e6k_allPhi2 : ∀ l ∈ Tag.E6.artifactRoots,
    kacTest e6k_theta e6k_N023456 (toVec Tag.E6.rank l) := by
  decide +kernel

private theorem e6k_checkM_of_list
    {C : Finset (Option (Fin Tag.E6.rank))}
    {S : Finset (Fin Tag.E6.rank)} {l : List (Fin Tag.E6.rank)}
    (h : ∀ l' ∈ Tag.E6.artifactRoots,
      (kacTest e6k_theta C (toVec Tag.E6.rank l') ↔
        ∀ j ∈ S, (e6k_wordAct l (toVec Tag.E6.rank l')) j = 0)) :
    ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      (kacTest kacE6.θ C γ ↔ ∀ j ∈ S, (e6k_wordAct l γ) j = 0) := by
  intro γ hγ
  have hmem : List.ofFn γ ∈ Tag.E6.artifactRoots := (isRoot_iff_mem_artifactRoots (τ := .E6)).1 hγ
  have h' := h (List.ofFn γ) hmem
  rw [e6k_toVec_ofFn] at h'
  rwa [e6k_theta_eq]

private theorem e6k_checkN_of_list
    {C : Finset (Option (Fin Tag.E6.rank))}
    {S : Finset (Fin Tag.E6.rank)} {l : List (Fin Tag.E6.rank)}
    (h : ∀ l' ∈ Tag.E6.artifactRoots,
      (kacTest e6k_theta C (e6k_wordAct l.reverse (toVec Tag.E6.rank l')) ↔
        ∀ j ∈ S, (toVec Tag.E6.rank l') j = 0)) :
    ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      (kacTest kacE6.θ C (e6k_wordAct l.reverse γ) ↔ ∀ j ∈ S, γ j = 0) := by
  intro γ hγ
  have hmem : List.ofFn γ ∈ Tag.E6.artifactRoots := (isRoot_iff_mem_artifactRoots (τ := .E6)).1 hγ
  have h' := h (List.ofFn γ) hmem
  rw [e6k_toVec_ofFn] at h'
  rwa [e6k_theta_eq]

private theorem e6k_rootsOf_eq_image_parabolic
    (l : List (Fin Tag.E6.rank))
    (C : Finset (Option (Fin Tag.E6.rank))) (S : Finset (Fin Tag.E6.rank))
    (hC : ∃ y, y ∉ C)
    (hcheckM : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      (kacTest kacE6.θ C γ ↔ ∀ j ∈ S, (e6k_wordAct l γ) j = 0))
    (hcheckN : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      (kacTest kacE6.θ C (e6k_wordAct l.reverse γ) ↔ ∀ j ∈ S, γ j = 0)) :
    kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) =
      (fun α => wordW .E6 l.reverse • α) '' parabolicRoots .E6 {j : Fin Tag.E6.rank | j ∉ S} := by
  ext γ
  rw [mem_rootsOf_iff kacE6 facts_E6 hC]
  constructor
  · rintro ⟨hγ, htest⟩
    have hvan : ∀ j ∈ S, (e6k_wordAct l γ) j = 0 := (hcheckM γ hγ).1 htest
    refine ⟨e6k_wordAct l γ, ⟨?_, fun j hj => hvan j (by by_contra h; exact hj h)⟩, ?_⟩
    · rw [← e6k_wordW_smul_wordAct]
      exact IsRoot.smul hγ _
    · rw [e6k_wordW_reverse, ← e6k_wordW_smul_wordAct]
      exact inv_smul_smul (wordW .E6 l) γ
  · rintro ⟨δ, ⟨hδroot, hδvan⟩, rfl⟩
    have hvanS : ∀ j ∈ S, δ j = 0 := fun j hj => hδvan j (fun h => h hj)
    change IsRoot .E6 (wordW .E6 l.reverse • δ) ∧
      kacTest kacE6.θ C (wordW .E6 l.reverse • δ)
    refine ⟨IsRoot.smul hδroot _, ?_⟩
    rw [e6k_wordW_smul_wordAct]
    exact (hcheckN δ hδroot).2 hvanS

private theorem e6k_rootsOf_eq_parabolic_of_forall
    {C : Finset (Option (Fin Tag.E6.rank))}
    (hnone : none ∉ C) {S : Finset (Fin Tag.E6.rank)}
    (hJ : ∀ j : Fin Tag.E6.rank, some j ∈ C ↔ j ∉ S) :
    kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) =
      parabolicRoots .E6 {j : Fin Tag.E6.rank | j ∉ S} := by
  rw [KacData.rootsOf_eq_parabolicRoots kacE6 hnone]
  congr 1
  ext j
  exact hJ j

private theorem e6k_a_eq_one_of_rootmem
    {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)}
    {C : Finset (Option (Fin Tag.E6.rank))} {v : WeylGroup .E6}
    (hcl' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))))
    (hmemroot : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      γ ∈ kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank)))) :
    ∀ j : Fin Tag.E6.rank, a j = 1 := by
  intro j
  have hroot : IsRoot .E6 (v⁻¹ • (Pi.single j 1)) := IsRoot.smul (isRoot_single .E6 j) v⁻¹
  have hmem : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ componentRoots (rootCharHom a) i := by
    rw [hcl']
    refine ⟨v⁻¹ • Pi.single j 1, hmemroot _ hroot, ?_⟩
    change v • (v⁻¹ • (Pi.single j 1)) = Pi.single j 1
    exact smul_inv_smul v _
  obtain ⟨hkr, -⟩ := hmem
  have hroot' : rootChar a (Pi.single j 1) = 1 := hkr.2
  have hev : rootChar a (Pi.single j 1) = a j := by simpa using rootChar_nsmul_single a j 1
  rwa [hev] at hroot'

end

theorem e6_class_levi
    {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Lˣ}
    (hζ : IsPrimitiveRoot (ζ : L) p) (a : Fin Tag.E6.rank → Lˣ) (ha : ∀ i, a i ^ p = 1)
    (ha1 : ∃ j, a j ≠ 1) (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (v : WeylGroup .E6) (S : Finset (Fin 6)), S ∈ e6LeviDel ∧
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots .E6 {j | j ∉ S} := by
  classical
  have _hp2 : p ≠ 2 := hp2
  obtain ⟨v, μ, -, hi⟩ :=
    KacData.exists_smul_rootsOf (τ := Tag.E6) kacE6 facts_E6 hp.pos hζ a ha
  obtain ⟨x, hx, hcl⟩ := hi i
  obtain ⟨c, hc, hcomp⟩ :=
    kacE6.exists_comp_eq_of_check e6_tree e6_adj (adm := fun _ => true) e6_check rfl hx
  set C : Finset (Option (Fin Tag.E6.rank)) := (c.map (idxNode (r := Tag.E6.rank))).toFinset
    with hCdef
  have hCset : kacE6.comp p μ x = (C : Set (Option (Fin Tag.E6.rank))) := by
    rw [hcomp, hCdef]
    ext y
    simp only [Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨w, hw, rfl⟩
      rw [nodeIdx_idxNode (e6_lt c hc w hw)]
      exact hw
  have hproper : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacE6 hp.pos μ x
    exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
  have hcl' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) := by
    rw [hcl, hCset]
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hcl', compRank_image, compRank_rootsOf kacE6 facts_E6 hproper, hCdef, e6_card c hc]
  have hlen3 : 3 ≤ c.length := by
    have h := h3
    rwa [hrank] at h
  have hlen6 : c.length ≤ 6 := by
    obtain ⟨y, hy⟩ := hproper
    have h1 := Finset.card_lt_univ_of_notMem hy
    rw [hCdef, e6_card c hc, Fintype.card_option, Fintype.card_fin] at h1
    have hr : Tag.E6.rank = 6 := rfl
    rw [hr] at h1
    omega
  rcases e6k_conn_cases c hc hlen3 hlen6 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have hCeq : C = e6k_N024 := by rw [hCdef]; decide +kernel
    have hS : ({0, 1, 2} : Finset (Fin 6)) ∈ e6LeviDel := by decide +kernel
    have hword : kacE6.rootsOf (e6k_N024 : Set (Option (Fin Tag.E6.rank))) =
        (fun α => wordW .E6 e6k_word1.reverse • α) ''
          parabolicRoots .E6 {j : Fin Tag.E6.rank | j ∉ ({0, 1, 2} : Finset (Fin Tag.E6.rank))} :=
      e6k_rootsOf_eq_image_parabolic e6k_word1 e6k_N024 {0, 1, 2} (by decide +kernel)
        (e6k_checkM_of_list e6k_check1M) (e6k_checkN_of_list e6k_check1N)
    refine ⟨v * wordW .E6 e6k_word1.reverse, {0, 1, 2}, hS, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    have hCeq : C = e6k_N0234 := by rw [hCdef]; decide +kernel
    have hS : ({1, 5} : Finset (Fin 6)) ∈ e6LeviDel := by decide +kernel
    have hword : kacE6.rootsOf (e6k_N0234 : Set (Option (Fin Tag.E6.rank))) =
        (fun α => wordW .E6 e6k_word2.reverse • α) ''
          parabolicRoots .E6 {j : Fin Tag.E6.rank | j ∉ ({1, 5} : Finset (Fin Tag.E6.rank))} :=
      e6k_rootsOf_eq_image_parabolic e6k_word2 e6k_N0234 {1, 5} (by decide +kernel)
        (e6k_checkM_of_list e6k_check2M) (e6k_checkN_of_list e6k_check2N)
    refine ⟨v * wordW .E6 e6k_word2.reverse, {1, 5}, hS, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    have hCeq : C = e6k_N0245 := by rw [hCdef]; decide +kernel
    have hS : ({0, 1} : Finset (Fin 6)) ∈ e6LeviDel := by decide +kernel
    have hword : kacE6.rootsOf (e6k_N0245 : Set (Option (Fin Tag.E6.rank))) =
        (fun α => wordW .E6 e6k_word3.reverse • α) ''
          parabolicRoots .E6 {j : Fin Tag.E6.rank | j ∉ ({0, 1} : Finset (Fin Tag.E6.rank))} :=
      e6k_rootsOf_eq_image_parabolic e6k_word3 e6k_N0245 {0, 1} (by decide +kernel)
        (e6k_checkM_of_list e6k_check3M) (e6k_checkN_of_list e6k_check3N)
    refine ⟨v * wordW .E6 e6k_word3.reverse, {0, 1}, hS, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    have hCeq : C = e6k_N01234 := by rw [hCdef]; decide +kernel
    have hS : ({1} : Finset (Fin 6)) ∈ e6LeviDel := by decide +kernel
    have hword : kacE6.rootsOf (e6k_N01234 : Set (Option (Fin Tag.E6.rank))) =
        (fun α => wordW .E6 e6k_word4.reverse • α) ''
          parabolicRoots .E6 {j : Fin Tag.E6.rank | j ∉ ({1} : Finset (Fin Tag.E6.rank))} :=
      e6k_rootsOf_eq_image_parabolic e6k_word4 e6k_N01234 {1} (by decide +kernel)
        (e6k_checkM_of_list e6k_check4M) (e6k_checkN_of_list e6k_check4N)
    refine ⟨v * wordW .E6 e6k_word4.reverse, {1}, hS, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    have hCeq : C = e6k_N02345 := by rw [hCdef]; decide +kernel
    have hS : ({0} : Finset (Fin 6)) ∈ e6LeviDel := by decide +kernel
    have hword : kacE6.rootsOf (e6k_N02345 : Set (Option (Fin Tag.E6.rank))) =
        (fun α => wordW .E6 e6k_word5.reverse • α) ''
          parabolicRoots .E6 {j : Fin Tag.E6.rank | j ∉ ({0} : Finset (Fin Tag.E6.rank))} :=
      e6k_rootsOf_eq_image_parabolic e6k_word5 e6k_N02345 {0} (by decide +kernel)
        (e6k_checkM_of_list e6k_check5M) (e6k_checkN_of_list e6k_check5N)
    refine ⟨v * wordW .E6 e6k_word5.reverse, {0}, hS, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    have hCeq : C = e6k_N02456 := by rw [hCdef]; decide +kernel
    have hS : ({1} : Finset (Fin 6)) ∈ e6LeviDel := by decide +kernel
    have hword : kacE6.rootsOf (e6k_N02456 : Set (Option (Fin Tag.E6.rank))) =
        (fun α => wordW .E6 e6k_word6.reverse • α) ''
          parabolicRoots .E6 {j : Fin Tag.E6.rank | j ∉ ({1} : Finset (Fin Tag.E6.rank))} :=
      e6k_rootsOf_eq_image_parabolic e6k_word6 e6k_N02456 {1} (by decide +kernel)
        (e6k_checkM_of_list e6k_check6M) (e6k_checkN_of_list e6k_check6N)
    refine ⟨v * wordW .E6 e6k_word6.reverse, {1}, hS, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    have hCeq : C = e6k_N012345 := by rw [hCdef]; decide +kernel
    have htest : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ → kacTest kacE6.θ C γ := by
      intro γ hγ
      rw [hCeq]
      have hmem : List.ofFn γ ∈ Tag.E6.artifactRoots :=
        (isRoot_iff_mem_artifactRoots (τ := .E6)).1 hγ
      have h := e6k_allPhi1 (List.ofFn γ) hmem
      rw [e6k_toVec_ofFn] at h
      rwa [e6k_theta_eq]
    have hmr : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
        γ ∈ kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) := by
      intro γ hγ
      rw [mem_rootsOf_iff kacE6 facts_E6 hproper]
      exact ⟨hγ, htest γ hγ⟩
    exfalso
    obtain ⟨j, hj⟩ := ha1
    exact hj (e6k_a_eq_one_of_rootmem hcl' hmr j)
  ·
    have hCeq : C = e6k_N023456 := by rw [hCdef]; decide +kernel
    have htest : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ → kacTest kacE6.θ C γ := by
      intro γ hγ
      rw [hCeq]
      have hmem : List.ofFn γ ∈ Tag.E6.artifactRoots :=
        (isRoot_iff_mem_artifactRoots (τ := .E6)).1 hγ
      have h := e6k_allPhi2 (List.ofFn γ) hmem
      rw [e6k_toVec_ofFn] at h
      rwa [e6k_theta_eq]
    have hmr : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
        γ ∈ kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) := by
      intro γ hγ
      rw [mem_rootsOf_iff kacE6 facts_E6 hproper]
      exact ⟨hγ, htest γ hγ⟩
    exfalso
    obtain ⟨j, hj⟩ := ha1
    exact hj (e6k_a_eq_one_of_rootmem hcl' hmr j)
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [1, 3, 4] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [2, 3, 4] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [2, 4, 5] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [3, 4, 5] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [4, 5, 6] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [2, 3, 4, 5] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [3, 4, 5, 6] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [1, 3, 4, 5] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [2, 4, 5, 6] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [1, 2, 3, 4] (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [2, 3, 4, 5, 6] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [1, 2, 3, 4, 5] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e6k_levi_del_cases [1, 3, 4, 5, 6] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine ⟨v, S, hS, ?_⟩
    rw [hcl', hCdef, e6k_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    exfalso
    have hnone : none ∉ ((([1, 2, 3, 4, 5, 6].map (idxNode (r := Tag.E6.rank))).toFinset :
        Finset (Option (Fin Tag.E6.rank)))) := by decide +kernel
    have hpar : kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) =
        parabolicRoots .E6 Set.univ := by
      rw [hCdef, KacData.rootsOf_eq_parabolicRoots kacE6 hnone]
      congr 1
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      fin_cases j <;> decide +kernel
    have hmr : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
        γ ∈ kacE6.rootsOf (C : Set (Option (Fin Tag.E6.rank))) := by
      intro γ hγ
      rw [hpar]
      exact ⟨hγ, fun i hi => absurd (Set.mem_univ i) hi⟩
    obtain ⟨j, hj⟩ := ha1
    exact hj (e6k_a_eq_one_of_rootmem hcl' hmr j)

end CFSG.StandardType

end
