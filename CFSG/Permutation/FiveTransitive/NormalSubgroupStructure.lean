module

public import CFSG.Permutation.FiveTransitive.AbelianNormalObstruction

public section

namespace CFSG

namespace FiveTransitive.NormalSubgroupStructure

open scoped commutatorElement

theorem isPretransitive_of_nontrivial_normal
    (G X : Type*) [Group G] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsQuasiPreprimitive G X]
    (N : Subgroup G) [N.Normal] [Nontrivial N] :
    MulAction.IsPretransitive N X := by
  apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
  intro hfixed
  apply not_subsingleton N
  constructor
  intro a b
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  have hx : x ∈ MulAction.fixedPoints N X := by
    rw [hfixed]
    exact Set.mem_univ x
  exact ((MulAction.mem_fixedPoints.mp hx) a).trans
    ((MulAction.mem_fixedPoints.mp hx) b).symm

theorem centralizer_eq_bot_of_nontrivial_normal
    (G X : Type*) [Group G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i)
    (N : Subgroup G) [N.Normal] [Nontrivial N] :
    Subgroup.centralizer (N : Set G) = ⊥ := by
  classical
  have h5G : MulAction.IsMultiplyPretransitive G X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    exact ⟨g, Function.Embedding.ext hg⟩
  let _ : MulAction.IsMultiplyPretransitive G X 5 := h5G
  have h2 : MulAction.IsMultiplyPretransitive G X 2 :=
    MulAction.isMultiplyPretransitive_of_le
      (G := G) (α := X) (m := 2) (n := 5) (by omega)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let _ : MulAction.IsPreprimitive G X :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  let _ : MulAction.IsPretransitive N X :=
    isPretransitive_of_nontrivial_normal G X N
  by_contra hC
  let C : Subgroup G := Subgroup.centralizer (N : Set G)
  let _ : Nontrivial C := C.nontrivial_iff_ne_bot.mpr hC
  have hCtrans : MulAction.IsPretransitive C X :=
    isPretransitive_of_nontrivial_normal G X C
  have hfree : ∀ (a : N) (x : X), a • x = x → a = 1 := by
    intro a x hax
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro y
    obtain ⟨c, rfl⟩ := hCtrans.exists_smul_eq x y
    change (a : G) • ((c : G) • x) = (1 : G) • ((c : G) • x)
    have hcomm : (a : G) * (c : G) = (c : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp c.property (a : G) a.property
    rw [← mul_smul, hcomm, mul_smul]
    simp only [Subgroup.smul_def] at hax
    rw [hax]
    simp
  let _ : IsCancelSMul N X := isCancelSMul_iff_eq_one_of_smul_eq.mpr hfree
  exact AbelianNormalObstruction.false_of_regular_normal_of_five_transitive
    G X hcard h5 N

private theorem inf_ne_bot_of_nontrivial_normal
    (G X : Type*) [Group G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i)
    (N M : Subgroup G) [N.Normal] [M.Normal] [Nontrivial N] [Nontrivial M] :
    N ⊓ M ≠ ⊥ := by
  intro hbot
  have hcomm : ⁅N, M⁆ = ⊥ :=
    le_antisymm ((Subgroup.commutator_le_inf N M).trans hbot.le) bot_le
  have hle : N ≤ Subgroup.centralizer (M : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  rw [centralizer_eq_bot_of_nontrivial_normal G X hcard h5 M] at hle
  exact N.nontrivial_iff_ne_bot.mp inferInstance (le_antisymm hle bot_le)

private theorem exists_minimal_nontrivial_normal
    (G : Type*) [Group G] [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧
      ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N := by
  classical
  have hex : ∃ n : ℕ, ∃ N : Subgroup G,
      N.Normal ∧ N ≠ ⊥ ∧ Nat.card N = n := by
    refine ⟨Nat.card (⊤ : Subgroup G), ⊤, inferInstance, ?_, rfl⟩
    exact top_ne_bot
  obtain ⟨N, hNnormal, hNne, hNcard⟩ := Nat.find_spec hex
  refine ⟨N, hNnormal, hNne, ?_⟩
  intro K hKnormal hKN
  by_cases hKbot : K = ⊥
  · exact Or.inl hKbot
  · right
    apply Subgroup.eq_of_le_of_card_ge hKN
    have hminimal := Nat.find_min' hex ⟨K, hKnormal, hKbot, rfl⟩
    rw [hNcard]
    exact hminimal

theorem existsUnique_minimal_nontrivial_normal
    (G X : Type*) [Group G] [Finite G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    ∃! N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧
      ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N := by
  classical
  have h5G : MulAction.IsMultiplyPretransitive G X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    exact ⟨g, Function.Embedding.ext hg⟩
  let _ : MulAction.IsMultiplyPretransitive G X 5 := h5G
  have h2 : MulAction.IsMultiplyPretransitive G X 2 :=
    MulAction.isMultiplyPretransitive_of_le
      (G := G) (α := X) (m := 2) (n := 5) (by omega)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let _ : MulAction.IsMultiplyPretransitive G X 2 := h2
  let _ : MulAction.IsPretransitive G X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let _ : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : Nontrivial G := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    refine ⟨⟨g, 1, ?_⟩⟩
    intro hg1
    apply hxy
    simpa only [hg1, one_smul] using hg
  obtain ⟨N, hNnormal, hNne, hNmin⟩ := exists_minimal_nontrivial_normal G
  refine ⟨N, ⟨hNnormal, hNne, hNmin⟩, ?_⟩
  intro M hM
  obtain ⟨hMnormal, hMne, hMmin⟩ := hM
  let _ : N.Normal := hNnormal
  let _ : M.Normal := hMnormal
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hNne
  let _ : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hMne
  have hinf := inf_ne_bot_of_nontrivial_normal G X hcard h5 N M
  have hinfN : N ⊓ M = N :=
    (hNmin (N ⊓ M) inferInstance inf_le_left).resolve_left hinf
  have hinfM : N ⊓ M = M :=
    (hMmin (N ⊓ M) inferInstance inf_le_right).resolve_left hinf
  exact hinfM.symm.trans hinfN

end FiveTransitive.NormalSubgroupStructure

end CFSG
