module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def e7LeviDel : Finset (Finset (Fin 7)) :=
  {{0}, {1}, {6}, {0, 1}, {0, 2}, {1, 6}, {0, 6}, {5, 6}}

section Kac

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.AlgebraicGroups (rootCharHom)
open CFSG.RankThree.Lattice CFSG.HardMathSupport.Curtis.UnitaryLevi
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootChar_nsmul_single)

private def e7Theta : Fin Tag.E7.rank → ℤ := ![2, 2, 3, 4, 3, 2, 1]

private theorem e7Theta_eq :
    kacE7.θ = e7Theta := rfl

open scoped CFSG.Decide.Bounded in
private theorem e7_conn_cases : ∀ c ∈ e7Conn, 5 ≤ c.length → c.length ≤ 7 →
    c = [0, 1, 2, 3, 4] ∨ c = [0, 1, 3, 4, 5] ∨ c = [1, 2, 3, 4, 5] ∨ c = [1, 3, 4, 5, 6] ∨
    c = [2, 3, 4, 5, 6] ∨ c = [2, 4, 5, 6, 7] ∨ c = [3, 4, 5, 6, 7] ∨ c = [0, 1, 2, 3, 4, 5] ∨
    c = [0, 1, 3, 4, 5, 6] ∨ c = [1, 2, 3, 4, 5, 6] ∨ c = [1, 3, 4, 5, 6, 7] ∨
    c = [2, 3, 4, 5, 6, 7] ∨ c = [0, 1, 2, 3, 4, 5, 6] ∨ c = [0, 1, 3, 4, 5, 6, 7] ∨
    c = [1, 2, 3, 4, 5, 6, 7] := by
  decide +kernel

private def e7LeviDel' : Finset (Finset (Fin Tag.E7.rank)) :=
  {{0}, {1}, {6}, {0, 1}, {0, 2}, {1, 6}, {0, 6}, {5, 6}}

open scoped CFSG.Decide.Bounded in
private theorem e7_levi_del_cases : ∀ c ∈ e7Conn, 5 ≤ c.length → c.length ≤ 6 → 0 ∉ c →
    ∃ S ∈ e7LeviDel', ∀ j : Fin Tag.E7.rank,
      some j ∈ ((c.map (idxNode (r := Tag.E7.rank))).toFinset :
        Finset (Option (Fin Tag.E7.rank))) ↔ j ∉ S := by
  decide +kernel

private def e7WordAct :
    List (Fin Tag.E7.rank) → (Fin Tag.E7.rank → ℤ) → (Fin Tag.E7.rank → ℤ)
  | [], v => v
  | i :: l, v => reflect .E7 i (e7WordAct l v)

private def e7SymWord : List (Fin Tag.E7.rank) :=
  [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6]

private def e7NodesA : Finset (Option (Fin Tag.E7.rank)) :=
  {none, some 0, some 1, some 2, some 3}

private def e7NodesB : Finset (Option (Fin Tag.E7.rank)) :=
  {none, some 0, some 2, some 3, some 4}

private def e7NodesC : Finset (Option (Fin Tag.E7.rank)) :=
  {none, some 0, some 1, some 2, some 3, some 4}

private def e7NodesD : Finset (Option (Fin Tag.E7.rank)) :=
  {none, some 0, some 2, some 3, some 4, some 5}

private def e7DelA : Finset (Fin Tag.E7.rank) := {0, 2}

private def e7DelB : Finset (Fin Tag.E7.rank) := {0, 1}

private def e7DelC : Finset (Fin Tag.E7.rank) := {0}

private def e7DelD : Finset (Fin Tag.E7.rank) := {1}

private theorem e7DelA_mem : e7DelA ∈ e7LeviDel' := by decide +kernel

private theorem e7DelB_mem : e7DelB ∈ e7LeviDel' := by decide +kernel

private theorem e7DelC_mem : e7DelC ∈ e7LeviDel' := by decide +kernel

private theorem e7DelD_mem : e7DelD ∈ e7LeviDel' := by decide +kernel

private theorem e7WordW_smul_wordAct
    (l : List (Fin Tag.E7.rank)) (v : Fin Tag.E7.rank → ℤ) :
    wordW .E7 l • v = e7WordAct l v := by
  induction l with
  | nil => simp [wordW, e7WordAct]
  | cons i l ih =>
    have h1 : wordW .E7 (i :: l) = simple .E7 i * wordW .E7 l := rfl
    rw [h1, mul_smul, ih, simple_smul]
    rfl

private theorem e7WordW_reverse
    (l : List (Fin Tag.E7.rank)) :
    wordW .E7 l.reverse = (wordW .E7 l)⁻¹ := by
  induction l with
  | nil => simp [wordW]
  | cons i l ih =>
    have h1 : wordW .E7 (i :: l) = simple .E7 i * wordW .E7 l := rfl
    have h2 : wordW .E7 [i] = simple .E7 i := rfl
    rw [List.reverse_cons, wordW_append, ih, h1, h2, mul_inv_rev, simple_inv]

open scoped CFSG.Decide.Bounded in
private theorem e7CheckAM : ∀ l ∈ Tag.E7.artifactRoots,
    (kacTest e7Theta e7NodesA (toVec Tag.E7.rank l) ↔
      ∀ j ∈ e7DelA, (e7WordAct e7SymWord (toVec Tag.E7.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e7CheckAN : ∀ l ∈ Tag.E7.artifactRoots,
    (kacTest e7Theta e7NodesA (e7WordAct e7SymWord.reverse (toVec Tag.E7.rank l)) ↔
      ∀ j ∈ e7DelA, (toVec Tag.E7.rank l) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e7CheckBM : ∀ l ∈ Tag.E7.artifactRoots,
    (kacTest e7Theta e7NodesB (toVec Tag.E7.rank l) ↔
      ∀ j ∈ e7DelB, (e7WordAct e7SymWord (toVec Tag.E7.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e7CheckBN : ∀ l ∈ Tag.E7.artifactRoots,
    (kacTest e7Theta e7NodesB (e7WordAct e7SymWord.reverse (toVec Tag.E7.rank l)) ↔
      ∀ j ∈ e7DelB, (toVec Tag.E7.rank l) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e7CheckCM : ∀ l ∈ Tag.E7.artifactRoots,
    (kacTest e7Theta e7NodesC (toVec Tag.E7.rank l) ↔
      ∀ j ∈ e7DelC, (e7WordAct e7SymWord (toVec Tag.E7.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e7CheckCN : ∀ l ∈ Tag.E7.artifactRoots,
    (kacTest e7Theta e7NodesC (e7WordAct e7SymWord.reverse (toVec Tag.E7.rank l)) ↔
      ∀ j ∈ e7DelC, (toVec Tag.E7.rank l) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e7CheckDM : ∀ l ∈ Tag.E7.artifactRoots,
    (kacTest e7Theta e7NodesD (toVec Tag.E7.rank l) ↔
      ∀ j ∈ e7DelD, (e7WordAct e7SymWord (toVec Tag.E7.rank l)) j = 0) := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private theorem e7CheckDN : ∀ l ∈ Tag.E7.artifactRoots,
    (kacTest e7Theta e7NodesD (e7WordAct e7SymWord.reverse (toVec Tag.E7.rank l)) ↔
      ∀ j ∈ e7DelD, (toVec Tag.E7.rank l) j = 0) := by
  decide +kernel

private theorem e7ToVec_ofFn {n : ℕ} (f : Fin n → ℤ) : toVec n (List.ofFn f) = f :=
  toVec_vofFn f

private theorem e7CheckM_of_list
    {C : Finset (Option (Fin Tag.E7.rank))}
    {S : Finset (Fin Tag.E7.rank)} {l : List (Fin Tag.E7.rank)}
    (h : ∀ l' ∈ Tag.E7.artifactRoots,
      (kacTest e7Theta C (toVec Tag.E7.rank l') ↔
        ∀ j ∈ S, (e7WordAct l (toVec Tag.E7.rank l')) j = 0)) :
    ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ →
      (kacTest kacE7.θ C γ ↔ ∀ j ∈ S, (e7WordAct l γ) j = 0) := by
  intro γ hγ
  have hmem : List.ofFn γ ∈ Tag.E7.artifactRoots := (isRoot_iff_mem_artifactRoots (τ := .E7)).1 hγ
  have h' := h (List.ofFn γ) hmem
  rw [e7ToVec_ofFn] at h'
  rwa [e7Theta_eq]

private theorem e7CheckN_of_list
    {C : Finset (Option (Fin Tag.E7.rank))}
    {S : Finset (Fin Tag.E7.rank)} {l : List (Fin Tag.E7.rank)}
    (h : ∀ l' ∈ Tag.E7.artifactRoots,
      (kacTest e7Theta C (e7WordAct l.reverse (toVec Tag.E7.rank l')) ↔
        ∀ j ∈ S, (toVec Tag.E7.rank l') j = 0)) :
    ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ →
      (kacTest kacE7.θ C (e7WordAct l.reverse γ) ↔ ∀ j ∈ S, γ j = 0) := by
  intro γ hγ
  have hmem : List.ofFn γ ∈ Tag.E7.artifactRoots := (isRoot_iff_mem_artifactRoots (τ := .E7)).1 hγ
  have h' := h (List.ofFn γ) hmem
  rw [e7ToVec_ofFn] at h'
  rwa [e7Theta_eq]

private theorem e7_rootsOf_eq_image_parabolic
    (l : List (Fin Tag.E7.rank))
    (C : Finset (Option (Fin Tag.E7.rank))) (S : Finset (Fin Tag.E7.rank))
    (hC : ∃ y, y ∉ C)
    (hcheckM : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ →
      (kacTest kacE7.θ C γ ↔ ∀ j ∈ S, (e7WordAct l γ) j = 0))
    (hcheckN : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ →
      (kacTest kacE7.θ C (e7WordAct l.reverse γ) ↔ ∀ j ∈ S, γ j = 0)) :
    kacE7.rootsOf (C : Set (Option (Fin Tag.E7.rank))) =
      (fun α => wordW .E7 l.reverse • α) ''
        parabolicRoots .E7 {j : Fin Tag.E7.rank | j ∉ S} := by
  ext γ
  rw [mem_rootsOf_iff kacE7 facts_E7 hC]
  constructor
  · rintro ⟨hγ, htest⟩
    have hvan : ∀ j ∈ S, (e7WordAct l γ) j = 0 := (hcheckM γ hγ).1 htest
    refine ⟨e7WordAct l γ, ⟨?_, fun j hj => hvan j (by by_contra h; exact hj h)⟩, ?_⟩
    · rw [← e7WordW_smul_wordAct]
      exact IsRoot.smul hγ _
    · rw [e7WordW_reverse, ← e7WordW_smul_wordAct]
      exact inv_smul_smul (wordW .E7 l) γ
  · rintro ⟨δ, ⟨hδroot, hδvan⟩, rfl⟩
    have hvanS : ∀ j ∈ S, δ j = 0 := fun j hj => hδvan j (fun h => h hj)
    change IsRoot .E7 (wordW .E7 l.reverse • δ) ∧
      kacTest kacE7.θ C (wordW .E7 l.reverse • δ)
    refine ⟨IsRoot.smul hδroot _, ?_⟩
    rw [e7WordW_smul_wordAct]
    exact (hcheckN δ hδroot).2 hvanS

private theorem e7_p_eq_sum_off
    {p : ℕ} {μ : Fin Tag.E7.rank → ℤ}
    {x : Option (Fin Tag.E7.rank)} {c : List ℕ}
    (hcomp : kacE7.comp p μ x = {y | nodeIdx y ∈ c}) (h0 : 0 ∈ c) :
    (p : ℤ) = ∑ j ∈ Finset.univ.filter (fun j : Fin Tag.E7.rank => (j : ℕ) + 1 ∉ c),
      kacE7.θ j * μ j := by
  have hθ : kacE7.θ ⬝ᵥ μ = (p : ℤ) := by
    have hmem : none ∈ kacE7.comp p μ x := by
      rw [hcomp]
      exact h0
    exact hmem.1
  rw [← hθ, dotProduct]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_).symm
  have hj' : (j : ℕ) + 1 ∈ c := by
    by_contra h
    exact hj (Finset.mem_filter.2 ⟨Finset.mem_univ j, h⟩)
  have hzj : μ j = 0 := by
    have hmem : some j ∈ kacE7.comp p μ x := by
      rw [hcomp]
      exact hj'
    exact hmem.1
  rw [hzj, mul_zero]

private theorem e7_rootsOf_eq_parabolic_of_forall
    {C : Finset (Option (Fin Tag.E7.rank))}
    (hnone : none ∉ C) {S : Finset (Fin Tag.E7.rank)}
    (hJ : ∀ j : Fin Tag.E7.rank, some j ∈ C ↔ j ∉ S) :
    kacE7.rootsOf (C : Set (Option (Fin Tag.E7.rank))) =
      parabolicRoots .E7 {j : Fin Tag.E7.rank | j ∉ S} := by
  rw [KacData.rootsOf_eq_parabolicRoots kacE7 hnone]
  congr 1
  ext j
  exact hJ j

private theorem e7_false_of_two_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : 2 ∣ p) : False := by
  obtain h1 | h1 := Nat.Prime.eq_one_or_self_of_dvd (p := p) hp 2 h
  · norm_num at h1
  · exact hp2 h1.symm

end Kac

open CFSG.LieType.AlgebraicGroups (rootCharHom)
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Curtis.UnitaryLevi
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootChar_nsmul_single)

theorem e7_class_levi
    {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Lˣ}
    (hζ : IsPrimitiveRoot (ζ : L) p) (a : Fin Tag.E7.rank → Lˣ) (ha : ∀ i, a i ^ p = 1)
    (ha1 : ∃ j, a j ≠ 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (v : WeylGroup .E7) (S : Finset (Fin 7)), S ∈ e7LeviDel ∧
      componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots .E7 {j | j ∉ S} := by
  classical
  obtain ⟨w, μ, hμ, hw⟩ := kacE7.exists_weyl_normal hp.pos hζ a ha
  have hζu : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.1 hζ
  set a' : Fin Tag.E7.rank → Lˣ := fun i => ζ ^ μ i with ha'
  have hconj : IsCharConj (rootCharHom a) (rootCharHom a') w := by
    intro v
    change rootChar a' v = rootChar a (w⁻¹ • v)
    rw [hw, smul_inv_smul, ha', KacData.rootChar_eq_zpow]
  have hχ : ∀ γ, IsRoot Tag.E7 γ →
      ((rootCharHom a') (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ) := by
    intro γ _
    change rootChar a' γ = 1 ↔ _
    rw [ha', KacData.rootChar_eq_zpow]
    exact hζu.zpow_eq_one_iff_dvd _
  obtain ⟨i', hi'⟩ := KacData.componentRoots_smul_of_isCharConj hconj i
  obtain ⟨x, hx, hxi⟩ := KacData.componentRoots_eq_rootsOf kacE7 facts_E7 hp.pos hμ hχ i'
  have hcl : componentRoots (rootCharHom a) i =
      (fun α => w⁻¹ • α) '' kacE7.rootsOf (kacE7.comp p μ x) := by
    rw [hi', hxi]
  obtain ⟨c, hc, hcomp⟩ :=
    kacE7.exists_comp_eq_of_check e7_tree e7_adj (adm := fun _ => true) e7_check rfl hx
  set C : Finset (Option (Fin Tag.E7.rank)) := (c.map (idxNode (r := Tag.E7.rank))).toFinset
    with hCdef
  have hCset : kacE7.comp p μ x = (C : Set (Option (Fin Tag.E7.rank))) := by
    rw [hcomp, hCdef]
    ext y
    simp only [Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨u, hu, rfl⟩
      rw [nodeIdx_idxNode (e7_lt c hc u hu)]
      exact hu
  have hproper : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacE7 hp.pos μ x
    exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
  have hcl' : componentRoots (rootCharHom a) i =
      (fun α => w⁻¹ • α) '' kacE7.rootsOf (C : Set (Option (Fin Tag.E7.rank))) := by
    rw [hcl, hCset]
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hcl', compRank_image, compRank_rootsOf kacE7 facts_E7 hproper, hCdef, e7_card c hc]
  have hlen5 : 5 ≤ c.length := by
    have h := h5
    rwa [hrank] at h
  have hlen7 : c.length ≤ 7 := by
    obtain ⟨y, hy⟩ := hproper
    have h1 := Finset.card_lt_univ_of_notMem hy
    rw [hCdef, e7_card c hc, Fintype.card_option, Fintype.card_fin] at h1
    have h7 : Tag.E7.rank = 7 := rfl
    rw [h7] at h1
    omega
  rcases e7_conn_cases c hc hlen5 hlen7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have hCeq : C = e7NodesA := by rw [hCdef]; decide +kernel
    have hword : kacE7.rootsOf (e7NodesA : Set (Option (Fin Tag.E7.rank))) =
        (fun α => wordW .E7 e7SymWord.reverse • α) ''
          parabolicRoots .E7 {j : Fin Tag.E7.rank | j ∉ e7DelA} :=
      e7_rootsOf_eq_image_parabolic e7SymWord e7NodesA e7DelA (by decide +kernel)
        (e7CheckM_of_list e7CheckAM) (e7CheckN_of_list e7CheckAN)
    refine ⟨w⁻¹ * wordW .E7 e7SymWord.reverse, e7DelA, e7DelA_mem, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    have hCeq : C = e7NodesB := by rw [hCdef]; decide +kernel
    have hword : kacE7.rootsOf (e7NodesB : Set (Option (Fin Tag.E7.rank))) =
        (fun α => wordW .E7 e7SymWord.reverse • α) ''
          parabolicRoots .E7 {j : Fin Tag.E7.rank | j ∉ e7DelB} :=
      e7_rootsOf_eq_image_parabolic e7SymWord e7NodesB e7DelB (by decide +kernel)
        (e7CheckM_of_list e7CheckBM) (e7CheckN_of_list e7CheckBN)
    refine ⟨w⁻¹ * wordW .E7 e7SymWord.reverse, e7DelB, e7DelB_mem, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e7_levi_del_cases [1, 2, 3, 4, 5] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine ⟨w⁻¹, S, hS, ?_⟩
    rw [hcl', hCdef, e7_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e7_levi_del_cases [1, 3, 4, 5, 6] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine ⟨w⁻¹, S, hS, ?_⟩
    rw [hcl', hCdef, e7_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e7_levi_del_cases [2, 3, 4, 5, 6] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine ⟨w⁻¹, S, hS, ?_⟩
    rw [hcl', hCdef, e7_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e7_levi_del_cases [2, 4, 5, 6, 7] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine ⟨w⁻¹, S, hS, ?_⟩
    rw [hcl', hCdef, e7_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e7_levi_del_cases [3, 4, 5, 6, 7] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine ⟨w⁻¹, S, hS, ?_⟩
    rw [hcl', hCdef, e7_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    have hCeq : C = e7NodesC := by rw [hCdef]; decide +kernel
    have hword : kacE7.rootsOf (e7NodesC : Set (Option (Fin Tag.E7.rank))) =
        (fun α => wordW .E7 e7SymWord.reverse • α) ''
          parabolicRoots .E7 {j : Fin Tag.E7.rank | j ∉ e7DelC} :=
      e7_rootsOf_eq_image_parabolic e7SymWord e7NodesC e7DelC (by decide +kernel)
        (e7CheckM_of_list e7CheckCM) (e7CheckN_of_list e7CheckCN)
    refine ⟨w⁻¹ * wordW .E7 e7SymWord.reverse, e7DelC, e7DelC_mem, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    have hCeq : C = e7NodesD := by rw [hCdef]; decide +kernel
    have hword : kacE7.rootsOf (e7NodesD : Set (Option (Fin Tag.E7.rank))) =
        (fun α => wordW .E7 e7SymWord.reverse • α) ''
          parabolicRoots .E7 {j : Fin Tag.E7.rank | j ∉ e7DelD} :=
      e7_rootsOf_eq_image_parabolic e7SymWord e7NodesD e7DelD (by decide +kernel)
        (e7CheckM_of_list e7CheckDM) (e7CheckN_of_list e7CheckDN)
    refine ⟨w⁻¹ * wordW .E7 e7SymWord.reverse, e7DelD, e7DelD_mem, ?_⟩
    rw [hcl', hCeq, hword, Set.image_image]
    simp only [mul_smul]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e7_levi_del_cases [1, 2, 3, 4, 5, 6] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine ⟨w⁻¹, S, hS, ?_⟩
    rw [hcl', hCdef, e7_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e7_levi_del_cases [1, 3, 4, 5, 6, 7] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine ⟨w⁻¹, S, hS, ?_⟩
    rw [hcl', hCdef, e7_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    obtain ⟨S, hS, hJ⟩ := e7_levi_del_cases [2, 3, 4, 5, 6, 7] (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refine ⟨w⁻¹, S, hS, ?_⟩
    rw [hcl', hCdef, e7_rootsOf_eq_parabolic_of_forall (by decide +kernel) hJ]
    rfl
  ·
    exfalso
    have hp_eq := e7_p_eq_sum_off (c := [0, 1, 2, 3, 4, 5, 6]) hcomp (by decide +kernel)
    have hfilt : (Finset.univ.filter
        (fun j : Fin Tag.E7.rank => (j : ℕ) + 1 ∉ [0, 1, 2, 3, 4, 5, 6])) =
        ({6} : Finset (Fin Tag.E7.rank)) := by decide +kernel
    rw [hfilt, Finset.sum_singleton] at hp_eq
    have h6 : kacE7.θ 6 = 1 := by rw [e7Theta_eq]; decide +kernel
    rw [h6, one_mul] at hp_eq
    have hμ0 : ∀ k : Fin Tag.E7.rank, k ≠ 6 → μ k = 0 := by
      intro k hk
      have hc' : (k : ℕ) + 1 ∈ [0, 1, 2, 3, 4, 5, 6] := by
        revert hk
        fin_cases k <;> decide
      have hz : kacE7.IsZ p μ (some k) := by
        have hmem : some k ∈ kacE7.comp p μ x := by
          rw [hcomp]
          exact hc'
        exact hmem.1
      exact hz
    have hall : ∀ j : Fin Tag.E7.rank, a j = 1 := by
      intro j
      have hdot : (w • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) ⬝ᵥ μ =
          (w • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) 6 * μ 6 := by
        rw [dotProduct, Finset.sum_eq_single 6 (fun b _ hb => by rw [hμ0 b hb, mul_zero])
          (fun h => absurd (Finset.mem_univ 6) h)]
      have hone : rootChar a (Pi.single j 1) = 1 := by
        rw [hw, hdot, ← hp_eq]
        exact (hζu.zpow_eq_one_iff_dvd _).2 (dvd_mul_left _ _)
      have hev : rootChar a (Pi.single j 1 : Fin Tag.E7.rank → ℤ) = a j := by
        simpa using rootChar_nsmul_single a j 1
      rw [hev] at hone
      exact hone
    obtain ⟨j, hj⟩ := ha1
    exact hj (hall j)
  ·
    exfalso
    have hp_eq := e7_p_eq_sum_off (c := [0, 1, 3, 4, 5, 6, 7]) hcomp (by decide +kernel)
    have hfilt : (Finset.univ.filter
        (fun j : Fin Tag.E7.rank => (j : ℕ) + 1 ∉ [0, 1, 3, 4, 5, 6, 7])) =
        ({1} : Finset (Fin Tag.E7.rank)) := by decide +kernel
    rw [hfilt, Finset.sum_singleton] at hp_eq
    have h1 : kacE7.θ 1 = 2 := by rw [e7Theta_eq]; decide +kernel
    rw [h1] at hp_eq
    have hdvd : (2 : ℤ) ∣ (p : ℤ) := ⟨μ 1, by rw [hp_eq]⟩
    exact e7_false_of_two_dvd hp hp2 (by exact_mod_cast hdvd)
  ·
    exfalso
    have hnone : none ∉ (([1, 2, 3, 4, 5, 6, 7].map (idxNode (r := Tag.E7.rank))).toFinset :
        Finset (Option (Fin Tag.E7.rank))) := by decide +kernel
    have hpar : kacE7.rootsOf (C : Set (Option (Fin Tag.E7.rank))) =
        parabolicRoots .E7 Set.univ := by
      rw [hCdef, KacData.rootsOf_eq_parabolicRoots kacE7 hnone]
      congr 1
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      fin_cases j <;> decide +kernel
    have hall : ∀ j : Fin Tag.E7.rank, a j = 1 := by
      intro j
      have hmem : (Pi.single j 1 : Fin Tag.E7.rank → ℤ) ∈
          componentRoots (rootCharHom a) i := by
        rw [hcl', hpar]
        refine ⟨w • (Pi.single j 1), ⟨IsRoot.smul (IsRoot.basis j) w, ?_⟩, ?_⟩
        · exact fun k hk => absurd (Set.mem_univ k) hk
        · change w⁻¹ • (w • (Pi.single j 1)) = Pi.single j 1
          exact inv_smul_smul w _
      obtain ⟨hkr, -⟩ := hmem
      have hroot : rootChar a (Pi.single j 1) = 1 := hkr.2
      have hev : rootChar a (Pi.single j 1) = a j := by
        simpa using rootChar_nsmul_single a j 1
      rwa [hev] at hroot
    obtain ⟨j, hj⟩ := ha1
    exact hj (hall j)

section Datum

open CFSG CFSG.Assembly CFSG.Monster.B.Geometry

private def e7Reach (S : Finset (Fin 7)) (s : Finset {i : Fin 7 // i ∉ S}) :
    Finset {i : Fin 7 // i ∉ S} :=
  s ∪ s.biUnion fun a => Finset.univ.filter fun b =>
    b ≠ a ∧ CoxeterMatrix.E₇.M b a ≠ 2

private def e7ReachN (S : Finset (Fin 7)) : ℕ → Finset {i : Fin 7 // i ∉ S} →
    Finset {i : Fin 7 // i ∉ S}
  | 0, s => s
  | k + 1, s => e7Reach S (e7ReachN S k s)

private theorem e7ReachN_mem_rtg {S : Finset (Fin 7)} {a : {i : Fin 7 // i ∉ S}} (k : ℕ) :
    ∀ {b : {i : Fin 7 // i ∉ S}}, b ∈ e7ReachN S k {a} →
      Relation.ReflTransGen
        (fun u v : {i : Fin 7 // i ∉ S} => u ≠ v ∧ CoxeterMatrix.E₇.M u v ≠ 2) a b := by
  induction k with
  | zero =>
    intro b hb
    simp only [e7ReachN, Finset.mem_singleton] at hb
    subst hb
    exact .refl
  | succ k ih =>
    intro b hb
    simp only [e7ReachN, e7Reach, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at hb
    rcases hb with hb | ⟨a', ha', hb'⟩
    · exact ih hb
    · exact (ih ha').trans (.single ⟨hb'.1.symm, by
        rw [← CoxeterMatrix.E₇.isSymm.apply a' b]; exact hb'.2⟩)

private theorem e7DeletedConnectedS {S : Finset (Fin 7)}
    (h : ∀ i j : {i : Fin 7 // i ∉ S}, j ∈ e7ReachN S 7 {i}) :
    GGDeletedConnectedS CoxeterMatrix.E₇ S := by
  intro i j
  exact e7ReachN_mem_rtg 7 (a := i) (h i j)

private theorem e7Parabolic_weyl {S : Finset (Fin 7)} (hne : Nonempty {i : Fin 7 // i ∉ S})
    (hdel : GGDeletedConnectedS CoxeterMatrix.E₇ S) :
    GGIsWeylMatrix (parMatrix CoxeterMatrix.E₇ {i | i ∉ S}) :=
  l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected S CoxeterMatrix.E₇ (CartanMatrix.E 7)
    (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 7), by ext i j; rfl⟩)))
    ggIntCartan_E₇ hdel hne

private theorem ggIntCartan_parMatrix {ι : Type} (M : CoxeterMatrix ι) (C : Matrix ι ι ℤ)
    (T : Set ι) (h : GGIntCartan M C) :
    GGIntCartan (parMatrix M T) (C.submatrix Subtype.val Subtype.val) := by
  constructor
  · intro i
    exact h.1 i.val
  · intro i j hij
    exact h.2 i.val j.val (fun hh => hij (Subtype.ext hh))

private theorem ggIsReflection_conj {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {φ : MulAut ↥Bs} (h : GGIsReflection p φ) (ψ : MulAut ↥Bs) :
    GGIsReflection p (ψ * φ * ψ⁻¹) := by
  refine ⟨by rw [conj_pow, h.1, mul_one, mul_inv_cancel], ?_⟩
  rw [← h.2]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv (ψ⁻¹ : MulAut ↥Bs).toEquiv fun b => ?_)
  show ψ (φ (ψ⁻¹ b)) = b ↔ φ (ψ⁻¹ b) = ψ⁻¹ b
  constructor
  · intro hb
    have h1 := congrArg (ψ⁻¹ : MulAut ↥Bs) hb
    rwa [MulAut.inv_apply_self] at h1
  · intro hb
    rw [hb, MulAut.apply_inv_self]

private theorem ggLin_conj {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V) (u φ : MulAut E)
    {g : Module.Dual (ZMod p) V} {z : V}
    (hφ : ∀ v, ggLin (p := p) ι φ v = v - g v • z) (v : V) :
    ggLin (p := p) ι (u * φ * u⁻¹) v =
      v - g ((ggLin (p := p) ι u).symm v) • ggLin (p := p) ι u z := by
  rw [map_mul, map_mul, map_inv]
  show ggLin (p := p) ι u (ggLin (p := p) ι φ ((ggLin (p := p) ι u).symm v)) = _
  rw [hφ, map_sub, map_smul, LinearEquiv.apply_symm_apply]

private theorem subgroup_map_conj {E : Type*} [Group E] (S : Subgroup E) (u : E) (hu : u ∈ S) :
    Subgroup.map (MulAut.conj u).toMonoidHom S = S := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hy) (Subgroup.inv_mem _ hu)
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨u⁻¹ * x * u, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hx) hu
    · show u * (u⁻¹ * x * u) * u⁻¹ = x
      group

private theorem range_subtype_eq {β : Type*} (f : Fin 7 → β) {S : Finset (Fin 7)} {b : Fin 7}
    (hSb : S = {b}) :
    Set.range (fun j : {j : Fin 7 // j ≠ b} => f j) =
      Set.range (fun j : {j : Fin 7 // j ∉ S} => f j) := by
  subst hSb
  let e : {j : Fin 7 // j ≠ b} ≃ {j : Fin 7 // j ∉ ({b} : Finset (Fin 7))} :=
    Equiv.subtypeEquivRight (fun j => by simp)
  have h : (fun j : {j : Fin 7 // j ≠ b} => f j) =
      (fun j : {j : Fin 7 // j ∉ ({b} : Finset (Fin 7))} => f j) ∘ e := rfl
  rw [h, Set.range_comp, e.surjective.range_eq, Set.image_univ]

private theorem e7Side_weyl {b : Fin 7}
    (h : GGIsWeylMatrix (parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ∉ ({b} : Finset (Fin 7))})) :
    GGIsWeylMatrix (parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ≠ b}) := by
  have hmat : parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ≠ b} =
      (parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ∉ ({b} : Finset (Fin 7))}).reindex
        (Equiv.subtypeEquivRight (fun j => by simp)) := by
    ext i j
    rfl
  rw [hmat]
  exact l05nBL_weyl_reindex h _

private theorem e7SideDatum {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {M : CoxeterMatrix (Fin 7)} (hWM : GGIsWeylMatrix M)
    {C : Matrix (Fin 7) (Fin 7) ℤ} (hMC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {ψ : Fin 7 → MulAut ↥Bs} {h : Fin 7 → V} {α : Fin 7 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (ψ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = ψ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range ψ))
    (b : Fin 7) (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 7 // j ≠ b} => ψ j))
    (hWMJ : GGIsWeylMatrix (parMatrix M {j : Fin 7 | j ≠ b}))
    (h3 : 3 ≤ Fintype.card {j : Fin 7 // j ≠ b}) :
    GGResSideDatum p Bs X J := by
  have hWMJ' : GGIsWeylMatrixFixed (parMatrix M {j : Fin 7 | j ≠ b}) := hWMJ
  have hCJ : GGIntCartan (parMatrix M {j : Fin 7 | j ≠ b})
      (C.submatrix Subtype.val Subtype.val) := ggIntCartan_parMatrix M C _ hMC
  have hpairJ : ∀ i j : {j : Fin 7 // j ≠ b}, α (i : Fin 7) (h (j : Fin 7)) =
      ((C.submatrix Subtype.val Subtype.val) i j : ZMod p) := fun i j => hpair i.val j.val
  have hconjJ : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Fin 7 // j ≠ b} => ψ j) :=
    ggReflConjSimple_of_weylMatrix hp hWMJ' h3 hCJ ι
      (fun j : {j : Fin 7 // j ≠ b} => ψ j) (fun j : {j : Fin 7 // j ≠ b} => h j)
      (fun j : {j : Fin 7 // j ≠ b} => α j) hpairJ (fun i w => hlin i w) hJ
  let fJ : (parMatrix M {j : Fin 7 | j ≠ b}).Group ≃* ↥(ggAutomizer J Bs) :=
    ggParabolic_equiv_of_generator_equiv M {j : Fin 7 | j ≠ b} ψ f hf hJ
  have hfJ : ∀ j, (fJ ((parMatrix M {j : Fin 7 | j ≠ b}).simple j) : MulAut ↥Bs) = ψ j :=
    fun i => ggParabolic_equiv_of_generator_equiv_simple M f ψ hf _ hJ i
  exact ⟨Fin 7, inferInstance, inferInstance, b, M, C, parMatrix M {j : Fin 7 | j ≠ b}, V,
    inferInstance, inferInstance, ι, ψ, h, α, hWM, hMC, hWMJ, fun _ _ => rfl, hlin, hrefl, hpair,
    ⟨f, hf⟩, hclos, ⟨fJ, hfJ⟩, hJ, hconjJ⟩

private theorem e7LeviSideDatum {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {Bs X J : Subgroup G} {M : CoxeterMatrix (Fin 7)} (hWM : GGIsWeylMatrix M)
    {C : Matrix (Fin 7) (Fin 7) ℤ} (hMC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {ψ : Fin 7 → MulAut ↥Bs} {h : Fin 7 → V} {α : Fin 7 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (ψ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = ψ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range ψ))
    (S : Finset (Fin 7)) (hS1 : 2 ≤ S.card) (hS2 : S.card ≤ 3)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 7 // j ∉ S} => ψ j))
    (hWMJ : GGIsWeylMatrix (parMatrix M {j : Fin 7 | j ∉ S}))
    (h3 : 3 ≤ Fintype.card {j : Fin 7 // j ∉ S}) :
    GGResLeviSideDatumLE3 p Bs X J := by
  have hWMJ' : GGIsWeylMatrixFixed (parMatrix M {j : Fin 7 | j ∉ S}) := hWMJ
  have hCJ : GGIntCartan (parMatrix M {j : Fin 7 | j ∉ S})
      (C.submatrix Subtype.val Subtype.val) := ggIntCartan_parMatrix M C _ hMC
  have hpairJ : ∀ i j : {j : Fin 7 // j ∉ S}, α (i : Fin 7) (h (j : Fin 7)) =
      ((C.submatrix Subtype.val Subtype.val) i j : ZMod p) := fun i j => hpair i.val j.val
  have hconjJ : GGReflConjSimple p (ggAutomizer J Bs)
      (fun j : {j : Fin 7 // j ∉ S} => ψ j) :=
    ggReflConjSimple_of_weylMatrix hp hWMJ' h3 hCJ ι
      (fun j : {j : Fin 7 // j ∉ S} => ψ j) (fun j : {j : Fin 7 // j ∉ S} => h j)
      (fun j : {j : Fin 7 // j ∉ S} => α j) hpairJ (fun i w => hlin i w) hJ
  let fJ : (parMatrix M {j : Fin 7 | j ∉ S}).Group ≃* ↥(ggAutomizer J Bs) :=
    ggParabolic_equiv_of_generator_equiv M {j : Fin 7 | j ∉ S} ψ f hf hJ
  have hfJ : ∀ j, (fJ ((parMatrix M {j : Fin 7 | j ∉ S}).simple j) : MulAut ↥Bs) = ψ j :=
    fun i => ggParabolic_equiv_of_generator_equiv_simple M f ψ hf _ hJ i
  exact ⟨Fin 7, inferInstance, inferInstance, S, M, C, parMatrix M {j : Fin 7 | j ∉ S}, V,
    inferInstance, inferInstance, ι, ψ, h, α, hS1, hS2, hWM, hMC, hWMJ, fun _ _ => rfl, hlin,
    hrefl, hpair, ⟨f, hf⟩, hclos, ⟨fJ, hfJ⟩, hJ, hconjJ⟩

theorem ggE7LeviDatum_of_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {Bs X J : Subgroup G} {M : CoxeterMatrix (Fin 7)} (hM : M = CoxeterMatrix.E₇)
    {C : Matrix (Fin 7) (Fin 7) ℤ} (hMC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Fin 7 → MulAut ↥Bs} {h : Fin 7 → V} {α : Fin 7 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (u : M.Group) {S : Finset (Fin 7)} (hS : S ∈ e7LeviDel)
    (hJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Fin 7 // j ∉ S} =>
      (f u : MulAut ↥Bs) * φ j * (f u : MulAut ↥Bs)⁻¹)) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  obtain rfl : M = CoxeterMatrix.E₇ := hM
  have hWM : GGIsWeylMatrix (CoxeterMatrix.E₇ : CoxeterMatrix (Fin 7)) :=
    Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 7), by ext i j; rfl⟩))
  let g : MulAut ↥Bs := (f u : MulAut ↥Bs)
  let W : V ≃ₗ[ZMod p] V := ggLin (p := p) ι g
  let ψ : Fin 7 → MulAut ↥Bs := fun i => (f u : MulAut ↥Bs) * φ i * (f u : MulAut ↥Bs)⁻¹
  let h' : Fin 7 → V := fun i => W (h i)
  let α' : Fin 7 → Module.Dual (ZMod p) V :=
    fun i => (α i).comp (W.symm : V ≃ₗ[ZMod p] V).toLinearMap
  have hlin' : ∀ i w, ggLin (p := p) ι (ψ i) w = w - α' i w • h' i := by
    intro i v
    have h := ggLin_conj (p := p) ι g (φ i) (hlin i) v
    simpa only [ψ, α', h', W, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using h
  have hrefl' : ∀ i, GGIsReflection p (ψ i) := fun i => ggIsReflection_conj (hrefl i) g
  have hpair' : ∀ i j, α' i (h' j) = (C i j : ZMod p) := by
    intro i j
    simpa only [α', h', W, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply] using hpair i j
  let f' : (CoxeterMatrix.E₇).Group ≃* ↥(ggAutomizer X Bs) := (MulAut.conj u).trans f
  have hf' : ∀ i, (f' ((CoxeterMatrix.E₇).simple i) : MulAut ↥Bs) = ψ i := by
    intro i
    show ((f (u * (CoxeterMatrix.E₇).simple i * u⁻¹) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = _
    rw [map_mul, map_mul, map_inv]
    simp only [ψ, Subgroup.coe_mul, Subgroup.coe_inv, hf i]
  have hgA : g ∈ ggAutomizer X Bs := (f u).2
  have hclos' : ggAutomizer X Bs = Subgroup.closure (Set.range ψ) := by
    have hrange : Set.range ψ = (MulAut.conj g).toMonoidHom '' Set.range φ := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨φ i, ⟨i, rfl⟩, (MulAut.conj_apply g (φ i)).symm⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, MulAut.conj_apply g (φ i)⟩
    rw [hclos, hrange, ← MonoidHom.map_closure]
    exact (subgroup_map_conj _ g (hclos ▸ hgA)).symm
  have hS' : S = {0} ∨ S = {1} ∨ S = {6} ∨ S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 6} ∨
      S = {0, 6} ∨ S = {5, 6} := by
    simpa [e7LeviDel] using hS
  rcases hS' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have hJ' : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Fin 7 // j ≠ 0} => ψ j) := by
      rw [hJ, ← range_subtype_eq ψ (S := ({0} : Finset (Fin 7))) rfl]
    have hWMJ : GGIsWeylMatrix (parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ≠ 0}) :=
      e7Side_weyl (e7Parabolic_weyl (S := {0}) ⟨⟨1, by decide⟩⟩
        (e7DeletedConnectedS (by decide +kernel)))
    exact Or.inl (e7SideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos' 0 hJ' hWMJ
      (by decide +kernel))
  ·
    have hJ' : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Fin 7 // j ≠ 1} => ψ j) := by
      rw [hJ, ← range_subtype_eq ψ (S := ({1} : Finset (Fin 7))) rfl]
    have hWMJ : GGIsWeylMatrix (parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ≠ 1}) :=
      e7Side_weyl (e7Parabolic_weyl (S := {1}) ⟨⟨0, by decide⟩⟩
        (e7DeletedConnectedS (by decide +kernel)))
    exact Or.inl (e7SideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos' 1 hJ' hWMJ
      (by decide +kernel))
  ·
    have hJ' : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Fin 7 // j ≠ 6} => ψ j) := by
      rw [hJ, ← range_subtype_eq ψ (S := ({6} : Finset (Fin 7))) rfl]
    have hWMJ : GGIsWeylMatrix (parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ≠ 6}) :=
      e7Side_weyl (e7Parabolic_weyl (S := {6}) ⟨⟨0, by decide⟩⟩
        (e7DeletedConnectedS (by decide +kernel)))
    exact Or.inl (e7SideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos' 6 hJ' hWMJ
      (by decide +kernel))
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ∉ ({0, 1} : Finset (Fin 7))}) :=
      e7Parabolic_weyl (S := {0, 1}) ⟨⟨2, by decide⟩⟩ (e7DeletedConnectedS (by decide +kernel))
    exact Or.inr (e7LeviSideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 1} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) hJ hWMJ
      (by decide +kernel))
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ∉ ({0, 2} : Finset (Fin 7))}) :=
      e7Parabolic_weyl (S := {0, 2}) ⟨⟨1, by decide⟩⟩ (e7DeletedConnectedS (by decide +kernel))
    exact Or.inr (e7LeviSideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 2} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) hJ hWMJ
      (by decide +kernel))
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ∉ ({1, 6} : Finset (Fin 7))}) :=
      e7Parabolic_weyl (S := {1, 6}) ⟨⟨0, by decide⟩⟩ (e7DeletedConnectedS (by decide +kernel))
    exact Or.inr (e7LeviSideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({1, 6} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) hJ hWMJ
      (by decide +kernel))
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ∉ ({0, 6} : Finset (Fin 7))}) :=
      e7Parabolic_weyl (S := {0, 6}) ⟨⟨1, by decide⟩⟩ (e7DeletedConnectedS (by decide +kernel))
    exact Or.inr (e7LeviSideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({0, 6} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) hJ hWMJ
      (by decide +kernel))
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.E₇ {j : Fin 7 | j ∉ ({5, 6} : Finset (Fin 7))}) :=
      e7Parabolic_weyl (S := {5, 6}) ⟨⟨0, by decide⟩⟩ (e7DeletedConnectedS (by decide +kernel))
    exact Or.inr (e7LeviSideDatum hp hWM hMC hlin' hrefl' hpair' hf' hclos'
      ({5, 6} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) hJ hWMJ
      (by decide +kernel))

end Datum

end CFSG.StandardType

end
