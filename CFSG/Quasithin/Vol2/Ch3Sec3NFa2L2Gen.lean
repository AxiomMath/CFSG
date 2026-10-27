module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Defs
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2PslDefs
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LinAlg
public import CFSG.Models.PGLSimple

public section

namespace CFSG.Quasithin.H13.NFa2

open scoped MatrixGroups
open CFSG.Open CFSG.Assembly.LowTwoRank

theorem nonempty_mulEquiv_psl_zmod {Kb : Type} [Group Kb] {q : ℕ} (hq : q.Prime)
    (h : StatedClassicalModel Kb .PSL 2 q 1) : Nonempty (Kb ≃* PSL(2, ZMod q)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod q) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  let φ : K ≃+* ZMod q := FiniteField.ringEquivOfCardEq hcard
  exact ⟨e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2)))⟩

theorem isSimpleGroup_of_psl_two_model {Kb : Type} [Group Kb] {q : ℕ} (hq5 : 5 ≤ q)
    (h : StatedClassicalModel Kb .PSL 2 q 1) : IsSimpleGroup Kb := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = q := by rw [hK, pow_one]
  haveI : IsSimpleGroup (StatedProj (StatedSL 2 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K le_rfl
      (Or.inr (by rw [hK']; omega)) (Or.inr (by rw [hK']; omega))
  exact e.isSimpleGroup

theorem card_psl_two_zmod {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    Nat.card PSL(2, ZMod q) = q * (q ^ 2 - 1) / 2 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (ZMod q)) := by
    rw [Nat.card_zmod]
    exact ⟨q, 1, hq, hq.odd_of_ne_two hq2, le_rfl, (pow_one q).symm⟩
  rw [CFSG.GorensteinWalter.psl2_card_formula (ZMod q) hodd, Nat.card_zmod]

theorem card_psl_two_zmod_ne_two {q : ℕ} (hq : q.Prime) (hq11 : 11 ≤ q) :
    Nat.card PSL(2, ZMod q) ≠ 2 := by
  rw [card_psl_two_zmod hq (by omega)]
  have h1 : 121 ≤ q ^ 2 := by nlinarith
  have h2 : 120 ≤ q ^ 2 - 1 := by omega
  have h3 : 11 * 120 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq11 h2
  generalize q * (q ^ 2 - 1) = m at h3 ⊢
  omega

theorem subgroup_eq_top_of_mem {G : Type} [Group G] [IsSimpleGroup G] {a b c : G} (hab : a ≠ b)
    (habc : Subgroup.closure ({a, b, c} : Set G) = ⊤) (N : Subgroup (G × G))
    (ha : (a, a) ∈ N) (hb : (b, b) ∈ N) (hc : (c, c) ∈ N) (hab' : (a, b) ∈ N) : N = ⊤ := by
  have hdiag : ∀ x ∈ ({a, b, c} : Set G), (x, x) ∈ N := by
    intro x hx
    rcases hx with h | h | h
    · rw [h]; exact ha
    · rw [h]; exact hb
    · rw [h]; exact hc
  have hfst_top : N.map (MonoidHom.fst G G) = ⊤ := by
    rw [eq_top_iff, ← habc, Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_map.mpr ⟨(x, x), hdiag x hx, rfl⟩
  have hsnd_top : N.map (MonoidHom.snd G G) = ⊤ := by
    rw [eq_top_iff, ← habc, Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_map.mpr ⟨(x, x), hdiag x hx, rfl⟩
  have hfst : ∀ x : G, ∃ y : G, (x, y) ∈ N := by
    intro x
    have hx : x ∈ N.map (MonoidHom.fst G G) := by
      rw [hfst_top]; exact Subgroup.mem_top x
    obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hx
    exact ⟨p.2, by rw [← hpx]; exact hp⟩
  have hsnd : ∀ y : G, ∃ x : G, (x, y) ∈ N := by
    intro y
    have hy : y ∈ N.map (MonoidHom.snd G G) := by
      rw [hsnd_top]; exact Subgroup.mem_top y
    obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.mp hy
    exact ⟨p.1, by rw [← hpy]; exact hp⟩
  let N₂ : Subgroup G := N.comap (MonoidHom.inr G G)
  haveI : N₂.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨h, hh⟩ := hsnd g
    have hn' : (1, n) ∈ N := hn
    have h1 : (h, g) * (1, n) * (h, g)⁻¹ ∈ N := N.mul_mem (N.mul_mem hh hn') (N.inv_mem hh)
    have h2 : (h, g) * (1, n) * (h, g)⁻¹ = (1, g * n * g⁻¹) := by
      ext <;> simp [mul_assoc]
    rw [h2] at h1
    exact h1
  rcases Subgroup.Normal.eq_bot_or_eq_top N₂ with h₂ | h₂
  ·
    exfalso
    apply hab
    have h1 : (a, a)⁻¹ * (a, b) = (1, a⁻¹ * b) := by ext <;> simp
    have h2 : a⁻¹ * b ∈ N₂ := by
      show (1, a⁻¹ * b) ∈ N
      rw [← h1]
      exact N.mul_mem (N.inv_mem ha) hab'
    rw [h₂, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact h2
  ·
    rw [eq_top_iff]
    rintro ⟨x, y⟩ -
    obtain ⟨y', hy'⟩ := hfst x
    have h3 : (1, y * y'⁻¹) ∈ N := by
      have : y * y'⁻¹ ∈ N₂ := by rw [h₂]; exact Subgroup.mem_top _
      exact this
    have h4 : (x, y) = (1, y * y'⁻¹) * (x, y') := by ext <;> simp
    rw [h4]
    exact N.mul_mem h3 hy'

theorem isConj_pair_of {G : Type} [Group G] {i a b : G} (ha : IsConj i a) (hb : IsConj i b) :
    IsConj (i, i) (a, b) := by
  obtain ⟨g₁, hg₁⟩ := isConj_iff.mp ha
  obtain ⟨g₂, hg₂⟩ := isConj_iff.mp hb
  exact isConj_iff.mpr ⟨(g₁, g₂), by ext <;> simp [hg₁, hg₂]⟩

theorem exists_involution_triple (hA : PslConjStmt) (hB : PslGenStmt) {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) {Kb : Type} [Group Kb] (e : Kb ≃* PSL(2, ZMod q)) (i : Kb)
    (hi : orderOf i = 2) :
    ∃ j₁ j₂ j₃ : Kb, orderOf j₁ = 2 ∧ orderOf j₂ = 2 ∧ orderOf j₃ = 2 ∧
      IsConj i j₁ ∧ IsConj i j₂ ∧ IsConj i j₃ ∧
      Subgroup.closure ({j₁, j₂, j₃} : Set Kb) = ⊤ := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨i₁, i₂, i₃, h₁, h₂, h₃, hgen⟩ := hB q hq5
  have hi' : orderOf (e i) = 2 := by rw [MulEquiv.orderOf_eq]; exact hi
  have c₁ : IsConj (e i) i₁ := hA q (by omega) _ _ hi' h₁
  have c₂ : IsConj (e i) i₂ := hA q (by omega) _ _ hi' h₂
  have c₃ : IsConj (e i) i₃ := hA q (by omega) _ _ hi' h₃
  have back : ∀ x : PSL(2, ZMod q), IsConj (e i) x → IsConj i (e.symm x) := by
    intro x hx
    have := MonoidHom.map_isConj e.symm.toMonoidHom hx
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this
  refine ⟨e.symm i₁, e.symm i₂, e.symm i₃, ?_, ?_, ?_, back i₁ c₁, back i₂ c₂, back i₃ c₃, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact h₁
  · rw [MulEquiv.orderOf_eq]; exact h₂
  · rw [MulEquiv.orderOf_eq]; exact h₃
  · have h := congrArg (Subgroup.map e.symm.toMonoidHom) hgen
    have htop : Subgroup.map e.symm.toMonoidHom (⊤ : Subgroup PSL(2, ZMod q)) = ⊤ :=
      Subgroup.map_top_of_surjective _ e.symm.surjective
    rw [MonoidHom.map_closure, htop] at h
    simpa [Set.image_insert_eq, Set.image_singleton] using h


theorem leaf_G2_of (hA : PslConjStmt) (hB : PslGenStmt) : Leaf_G2 := by
  intro q hq hq11 Kb _ hKb X _ _ _ ρ hfix i hi
  have hq5 : 5 ≤ q := by omega
  obtain ⟨e⟩ := nonempty_mulEquiv_psl_zmod hq hKb
  obtain ⟨j₁, j₂, j₃, -, -, -, hc₁, hc₂, hc₃, hgen⟩ :=
    exists_involution_triple hA hB hq hq5 e i hi
  classical
  let S : Finset Kb := {j₁, j₂, j₃}
  have hScard : S.card ≤ 3 := Finset.card_le_three
  have hS : Subgroup.closure (S : Set Kb) = ⊤ := by
    have hSset : (S : Set Kb) = {j₁, j₂, j₃} := by simp [S]
    rw [hSset]; exact hgen
  have hconj : ∀ s ∈ S, IsConj i s := by
    intro s hs
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hc₁
    · exact hc₂
    · exact hc₃
  exact (finrank_le_card_mul_of_closure_eq_top ρ hfix S hS i hconj).trans
    (Nat.mul_le_mul_right _ hScard)

theorem leaf_G3_of (hA : PslConjStmt) (hB : PslGenStmt) : Leaf_G3 := by
  intro q hq hq11 Kb _ hKb X _ _ _ ρ hfix i hi
  have hq5 : 5 ≤ q := by omega
  have hsimple : IsSimpleGroup Kb := isSimpleGroup_of_psl_two_model hq5 hKb
  obtain ⟨e⟩ := nonempty_mulEquiv_psl_zmod hq hKb
  have hne2 : Nat.card Kb ≠ 2 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_psl_two_zmod_ne_two hq (by omega)
  obtain ⟨j₁, j₂, j₃, hj₁, -, -, hc₁, hc₂, hc₃, hgen⟩ :=
    exists_involution_triple hA hB hq hq5 e i hi
  obtain ⟨a, b, c, hab, ha, hb, hc, habc⟩ :
      ∃ a b c : Kb, a ≠ b ∧ IsConj i a ∧ IsConj i b ∧ IsConj i c ∧
        Subgroup.closure ({a, b, c} : Set Kb) = ⊤ := by
    by_cases h12 : j₁ = j₂
    · by_cases h13 : j₁ = j₃
      ·
        exfalso
        rw [← h12, ← h13] at hgen
        have hsing : ({j₁, j₁, j₁} : Set Kb) = {j₁} := by simp
        rw [hsing, ← Subgroup.zpowers_eq_closure] at hgen
        have hcard : Nat.card Kb = orderOf j₁ := by
          rw [← Nat.card_zpowers, hgen, Subgroup.card_top]
        exact hne2 (hcard.trans hj₁)
      · refine ⟨j₁, j₃, j₂, h13, hc₁, hc₃, hc₂, ?_⟩
        have hset : ({j₁, j₃, j₂} : Set Kb) = {j₁, j₂, j₃} := by
          ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rw [hset]; exact hgen
    · exact ⟨j₁, j₂, j₃, h12, hc₁, hc₂, hc₃, hgen⟩
  classical
  have hS' : Subgroup.closure ({(a, a), (b, b), (c, c), (a, b)} : Set (Kb × Kb)) = ⊤ :=
    subgroup_eq_top_of_mem hab habc _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  let S : Finset (Kb × Kb) := {(a, a), (b, b), (c, c), (a, b)}
  have hScard : S.card ≤ 4 := Finset.card_le_four
  have hSset : (S : Set (Kb × Kb)) = {(a, a), (b, b), (c, c), (a, b)} := by simp [S]
  have hS : Subgroup.closure (S : Set (Kb × Kb)) = ⊤ := by rw [hSset]; exact hS'
  have hconj : ∀ s ∈ S, IsConj (i, i) s := by
    intro s hs
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact isConj_pair_of ha ha
    · exact isConj_pair_of hb hb
    · exact isConj_pair_of hc hc
    · exact isConj_pair_of ha hb
  exact (finrank_le_card_mul_of_closure_eq_top ρ hfix S hS (i, i) hconj).trans
    (Nat.mul_le_mul_right _ hScard)

end CFSG.Quasithin.H13.NFa2
