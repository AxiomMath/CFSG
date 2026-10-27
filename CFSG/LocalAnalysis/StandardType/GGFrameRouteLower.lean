module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGSpJoinWeylRank
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylow

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.Open
  CFSG.Assembly

@[expose] noncomputable def wordW (τ : Tag) (l : List (Fin τ.rank)) : WeylGroup τ :=
  (l.map (simple τ)).prod

theorem wordW_smul {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    wordW τ l • v = TableBExc.wordAct τ l v := by
  induction l with
  | nil => simp [wordW, TableBExc.wordAct]
  | cons i l ih =>
    simp only [wordW, List.map_cons, List.prod_cons, mul_smul] at ih ⊢
    rw [ih, simple_smul]
    rfl

theorem exists_elemAbelian_two_of_lines {τ : Tag} (β : Fin τ.rank → Fin τ.rank → ℤ)
    (hβ : ∀ j, β j ≠ 0) (d : ℤ) (hd : d ≠ 0) (N : Fin τ.rank → Fin τ.rank → ℤ)
    (hN : ∀ i, d • (Pi.single i 1 : Fin τ.rank → ℤ) = ∑ j, N i j • β j)
    (g : Fin τ.rank → WeylGroup τ) (hg : ∀ k j, g k • β j = if j = k then -β j else β j) :
    ∃ S : Subgroup (WeylGroup τ), IsElemAbelian 2 S ∧
      ∃ f : Finset (Fin τ.rank) → S, Function.Injective f := by
  classical
  have hext : ∀ u v : WeylGroup τ, (∀ j, u • β j = v • β j) → u = v := by
    intro u v huv
    refine ext_single fun i => ?_
    have key : ∀ w : WeylGroup τ, d • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) =
        ∑ j, N i j • (w • β j) := by
      intro w
      rw [smul_comm, hN i, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    have h := (key u).trans ((Finset.sum_congr rfl fun j _ => by rw [huv j]).trans (key v).symm)
    exact smul_right_injective _ hd h
  let S : Subgroup (WeylGroup τ) :=
    { carrier := {w | ∀ j, w • β j = β j ∨ w • β j = -β j}
      mul_mem' := by
        intro a b ha hb j
        simp only [Set.mem_setOf_eq, mul_smul] at ha hb ⊢
        rcases hb j with h | h <;> rw [h]
        · exact ha j
        · rw [smul_neg]
          rcases ha j with h' | h' <;> rw [h'] <;> simp
      one_mem' := by intro j; simp
      inv_mem' := by
        intro a ha j
        simp only [Set.mem_setOf_eq] at ha ⊢
        rcases ha j with h | h
        · exact Or.inl (inv_smul_eq_iff.mpr h.symm)
        · refine Or.inr (inv_smul_eq_iff.mpr ?_)
          rw [smul_neg, h, neg_neg] }
  have hsign : ∀ (a b : WeylGroup τ), a ∈ S → b ∈ S → ∀ j, (a * b) • β j = (b * a) • β j := by
    intro a b ha hb j
    rw [mul_smul, mul_smul]
    rcases ha j with h | h <;> rcases hb j with h' | h' <;> simp [h, h', smul_neg]
  refine ⟨S, ⟨⟨⟨fun a b => Subtype.ext (hext _ _ (hsign a b a.2 b.2))⟩⟩, fun a ha => ?_⟩, ?_⟩
  · rw [pow_two]
    refine hext _ _ fun j => ?_
    rw [mul_smul, one_smul]
    rcases ha j with h | h <;> simp [h, smul_neg]
  · have hgS : ∀ k, g k ∈ S := by
      intro k j
      rw [hg k j]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    have hex : ∀ T : Finset (Fin τ.rank), ∃ w ∈ S,
        ∀ j, w • β j = if j ∈ T then -β j else β j := by
      intro T
      induction T using Finset.induction_on with
      | empty => exact ⟨1, S.one_mem, fun j => by simp⟩
      | insert k T hk ih =>
        obtain ⟨w, hw, hwT⟩ := ih
        refine ⟨g k * w, S.mul_mem (hgS k) hw, fun j => ?_⟩
        rw [mul_smul, hwT j]
        simp only [Finset.mem_insert]
        by_cases hjk : j = k
        · subst hjk
          simp [hk, hg]
        · by_cases hjT : j ∈ T
          · simp [hjT, smul_neg, hg, hjk]
          · simp [hjT, hg, hjk]
    choose w hwS hwT using hex
    refine ⟨fun T => ⟨w T, hwS T⟩, fun T T' hTT' => ?_⟩
    have hw : w T = w T' := congrArg Subtype.val hTT'
    ext j
    have h1 := hwT T j
    have h2 := hwT T' j
    rw [hw] at h1
    have hne : β j ≠ -β j := fun h => hβ j (by
      have : (2 : ℤ) • β j = 0 := by rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
      exact (smul_eq_zero.mp this).resolve_left (by norm_num))
    constructor
    · intro hj
      by_contra hj'
      rw [if_pos hj] at h1
      rw [if_neg hj'] at h2
      exact hne (h2.symm.trans h1)
    · intro hj'
      by_contra hj
      rw [if_neg hj] at h1
      rw [if_pos hj'] at h2
      exact hne (h1.symm.trans h2)

@[expose] def betaE7 : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1], ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 2, 2, 1],
    ![1, 2, 2, 4, 3, 2, 1]]

@[expose] def wordsE7Raw : Fin 7 → List (Fin 7) :=
  ![[0], [1], [4], [6], [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2],
    [5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 5],
    [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3]]

@[expose] def wordsE7 : Fin Tag.E7.rank → List (Fin Tag.E7.rank) := wordsE7Raw

@[expose] def coeffE7 : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![![2, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 1, 1, -1],
    ![0, -1, -1, 0, 0, -1, 1], ![0, 0, 2, 0, 0, 0, 0], ![0, 0, -1, -1, -1, 1, 0],
    ![0, 0, 0, 2, 0, 0, 0]]

theorem wordsE7_act : ∀ k j : Fin Tag.E7.rank, TableBExc.wordAct .E7 (wordsE7 k) (betaE7 j) =
    if j = k then -betaE7 j else betaE7 j := by
  decide +kernel

theorem coeffE7_spec : ∀ i : Fin Tag.E7.rank, (2 : ℤ) • (Pi.single i 1 : Fin Tag.E7.rank → ℤ) =
    ∑ j, coeffE7 i j • betaE7 j := by
  decide +kernel

theorem betaE7_ne : ∀ j : Fin Tag.E7.rank, betaE7 j ≠ 0 := by decide +kernel

theorem exists_elemAbelian_two_coxeterE7 :
    ∃ S : Subgroup (CoxeterMatrix.E₇).Group, IsElemAbelian 2 S ∧
      ∃ f : Finset (Fin Tag.E7.rank) → S, Function.Injective f := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E7 = CartanMatrix.E 7 := cartanE_eq 7
  have hmat : CoxeterMatrix.E₇ = coxeterMatrix (isFiniteType_cartan .E7) :=
    (coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E7)
      (M := CoxeterMatrix.E₇) (isFiniteType_cartan .E7) (hc.symm ▸ ggIntCartan_E₇)).symm
  rw [hmat]
  exact exists_elemAbelian_two_of_lines (τ := .E7) betaE7 betaE7_ne 2 (by norm_num) coeffE7
    coeffE7_spec (fun k => wordW .E7 (wordsE7 k)) fun k j => by
      rw [wordW_smul]; exact wordsE7_act k j

@[expose] def betaE8 : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0], ![1, 1, 2, 2, 1, 0, 0, 0], ![1, 1, 2, 2, 2, 2, 1, 0],
    ![1, 2, 2, 4, 3, 2, 1, 0], ![2, 3, 4, 6, 5, 4, 3, 2]]

@[expose] def wordsE8Raw : Fin 8 → List (Fin 8) :=
  ![[0], [1], [4], [6], [2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2],
    [5, 6, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 6, 5],
    [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3],
    [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2,
      3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7]]

@[expose] def wordsE8 : Fin Tag.E8.rank → List (Fin Tag.E8.rank) := wordsE8Raw

@[expose] def coeffE8 : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ :=
  ![![2, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 1, 1, -1, 0],
    ![0, -1, -1, 0, 0, -1, 1, 0], ![0, 0, 2, 0, 0, 0, 0, 0], ![0, 0, -1, -1, -1, 1, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, -1, 0, -1, -1, 1]]

theorem wordsE8_act : ∀ k j : Fin Tag.E8.rank, TableBExc.wordAct .E8 (wordsE8 k) (betaE8 j) =
    if j = k then -betaE8 j else betaE8 j := by
  decide +kernel

theorem coeffE8_spec : ∀ i : Fin Tag.E8.rank, (2 : ℤ) • (Pi.single i 1 : Fin Tag.E8.rank → ℤ) =
    ∑ j, coeffE8 i j • betaE8 j := by
  decide +kernel

theorem betaE8_ne : ∀ j : Fin Tag.E8.rank, betaE8 j ≠ 0 := by decide +kernel

theorem exists_elemAbelian_two_coxeterE8 :
    ∃ S : Subgroup (CoxeterMatrix.E₈).Group, IsElemAbelian 2 S ∧
      ∃ f : Finset (Fin Tag.E8.rank) → S, Function.Injective f := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E8 = CartanMatrix.E 8 := cartanE_eq 8
  have hmat : CoxeterMatrix.E₈ = coxeterMatrix (isFiniteType_cartan .E8) :=
    (coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E8)
      (M := CoxeterMatrix.E₈) (isFiniteType_cartan .E8) (hc.symm ▸ ggIntCartan_E₈)).symm
  rw [hmat]
  exact exists_elemAbelian_two_of_lines (τ := .E8) betaE8 betaE8_ne 2 (by norm_num) coeffE8
    coeffE8_spec (fun k => wordW .E8 (wordsE8 k)) fun k j => by
      rw [wordW_smul]; exact wordsE8_act k j

theorem pow_le_card_of_weylOfType_of_two {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) {ι : Type} {M : CoxeterMatrix ι}
    {A : Subgroup (MulAut ↥Bs)} (hA : GGWeylOfType p M A) {n : ℕ}
    (hS : ∃ S : Subgroup M.Group, IsElemAbelian 2 S ∧
      ∃ f : Finset (Fin n) → S, Function.Injective f) : p ^ n ≤ Nat.card Bs := by
  obtain ⟨e, -⟩ := hA
  obtain ⟨S₀, hS₀, f, hf⟩ := hS
  let F : M.Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom
  have hF : Function.Injective F := Subtype.val_injective.comp e.injective
  have hS : IsElemAbelian 2 (S₀.map F) := hS₀.map F
  have hcard : 2 ^ n ≤ Nat.card (S₀.map F) := by
    have h1 : Nat.card (Finset (Fin n)) = 2 ^ n := by
      rw [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]
    rw [← h1, Subgroup.card_map_of_injective hF]
    have : Finite S₀ := Finite.of_injective (fun s : S₀ => F s) (hF.comp Subtype.val_injective)
    exact Nat.card_le_card_of_injective f hf
  exact pow_le_card_of_elemAbelian_two hp hp2 hBs hS hcard

theorem ggFrameBstarLowerInput_E7 : GGFrameBstarLowerInput CoxeterMatrix.E₇ 7 := by
  intro G _ _ B Bs x L D J hR _ hAt _
  obtain ⟨y, K, -, hM⟩ := hAt
  exact pow_le_card_of_weylOfType_of_two Nat.prime_three (by norm_num) hR.1.2.1.2.1 hM
    exists_elemAbelian_two_coxeterE7

theorem ggFrameBstarLowerInput_E8 : GGFrameBstarLowerInput CoxeterMatrix.E₈ 8 := by
  intro G _ _ B Bs x L D J hR _ hAt _
  obtain ⟨y, K, -, hM⟩ := hAt
  exact pow_le_card_of_weylOfType_of_two Nat.prime_three (by norm_num) hR.1.2.1.2.1 hM
    exists_elemAbelian_two_coxeterE8

end CFSG.StandardType.FrameRoute

end
