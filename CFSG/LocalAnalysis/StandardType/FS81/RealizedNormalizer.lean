module

public import CFSG.LocalAnalysis.StandardType.FS81.AutMat
public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth
public import CFSG.GroupTheory.MulAutCongr

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Basis3

variable {G : Type} [Group G] {k : ℕ}

private theorem mulVec_single_zero (M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3)) :
    M *ᵥ Pi.single (0 : Fin (k + 1)) 1 = fun i => M i 0 :=
  Matrix.mulVec_single_one M 0

private theorem vec_neg_single (B : Basis3 G (k + 1)) :
    B.vec (-Pi.single (0 : Fin (k + 1)) 1) = (B.b 0)⁻¹ := by
  have h := B.vec_add (Pi.single (0 : Fin (k + 1)) 1) (-Pi.single (0 : Fin (k + 1)) 1)
  rw [add_neg_cancel, B.vec_zero, B.vec_single] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem acts_col_zero (B : Basis3 G (k + 1)) {b₀ g : G}
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3)}
    (hM : B.Acts g M) (hb : B.b 0 = b₀) :
    g * b₀ * g⁻¹ = B.vec (fun i => M i 0) := by
  simpa [hb] using hM 0





private theorem realized_inv_mem [Finite G] (B : Basis3 G k) (H : Subgroup G)
    {M : Matrix (Fin k) (Fin k) (ZMod 3)} (hM : M ∈ B.realized H) :
    ∃ M' ∈ B.realized H, M * M' = 1 ∧ M' * M = 1 := by
  rw [B.mem_realized_iff] at hM
  obtain ⟨φ, hφ, rfl⟩ := hM
  have hmemA : φ ∈ ggAutomizer H B.span := by
    rw [ggAutomizer_eq]; exact hφ
  have hinv : φ⁻¹ ∈ ggInduced H B.span := by
    have h : φ⁻¹ ∈ ggAutomizer H B.span := (ggAutomizer H B.span).inv_mem hmemA
    rwa [ggAutomizer_eq] at h
  refine ⟨B.matOf φ⁻¹, ?_, ?_, ?_⟩
  · rw [B.mem_realized_iff]; exact ⟨φ⁻¹, hinv, rfl⟩
  · rw [← B.matOf_mul]; simp [B.matOf_one]
  · rw [← B.matOf_mul]; simp [B.matOf_one]


theorem realized_inf_normalizer_zpowers [Finite G] (B : Basis3 G k) (H : Subgroup G)
    (i : Fin k) :
    B.realized (H ⊓ Subgroup.normalizer (Subgroup.zpowers (B.b i) : Set G)) =
      {M | M ∈ B.realized H ∧
        (M *ᵥ Pi.single i 1 = Pi.single i 1 ∨ M *ᵥ Pi.single i 1 = -Pi.single i 1)} := by
  have hb3 : B.b i ^ 3 = 1 := by rw [← B.ord i]; exact pow_orderOf_eq_one _
  have hb1 : B.b i ≠ 1 := by
    intro h
    have h1 : orderOf (B.b i) = 1 := by rw [h, orderOf_one]
    rw [B.ord i] at h1
    omega
  have hneg : B.vec (-Pi.single i 1) = (B.vec (Pi.single i 1))⁻¹ := B.vec_neg _
  ext M
  constructor
  · rintro ⟨g, ⟨hgH, hgN⟩, hActs⟩
    have hmem : g * B.b i * g⁻¹ ∈ Subgroup.zpowers (B.b i) :=
      (Subgroup.mem_normalizer_iff.mp hgN (B.b i)).mp (Subgroup.mem_zpowers (B.b i))
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hv : B.vec (M *ᵥ Pi.single i 1) = g * B.b i * g⁻¹ := by
      rw [← B.acts_vec hActs (Pi.single i 1), B.vec_single]
    have hmod : (B.b i) ^ (z % 3) = (B.b i) ^ z := (zpow_eq_zpow_emod' z hb3).symm
    have hlt : z % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have hge : 0 ≤ z % 3 := Int.emod_nonneg _ (by norm_num)
    have hz3 : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
    refine ⟨⟨g, hgH, hActs⟩, ?_⟩
    rcases hz3 with h | h | h
    · exfalso
      have h0 : B.vec (M *ᵥ Pi.single i 1) = 1 := by
        rw [hv, ← hz, ← hmod, h, zpow_zero]
      have h1 : g * B.b i * g⁻¹ = 1 := by rw [← hv, h0]
      apply hb1
      calc B.b i = g⁻¹ * (g * B.b i * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · left
      apply B.vec_injective
      rw [hv, ← hz, ← hmod, h, zpow_one, B.vec_single]
    · right
      apply B.vec_injective
      rw [hv, ← hz, ← hmod, h, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
        hneg, B.vec_single, eq_inv_iff_mul_eq_one, ← pow_succ,
        show (2 + 1 : ℕ) = 3 from by norm_num, hb3]
  · rintro ⟨⟨g, hgH, hActs⟩, hcol⟩
    have hv : g * B.b i * g⁻¹ = B.vec (M *ᵥ Pi.single i 1) := by
      rw [← B.acts_vec hActs (Pi.single i 1), B.vec_single]
    have hmem : g * B.b i * g⁻¹ ∈ Subgroup.zpowers (B.b i) := by
      rw [hv]
      rcases hcol with h | h
      · rw [h, B.vec_single]; exact Subgroup.mem_zpowers _
      · rw [h, hneg, B.vec_single]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    exact ⟨g, ⟨hgH, Basis3.mem_normalizer_zpowers_of_conj hmem⟩, hActs⟩

end Basis3

theorem realized_normalizer_eq_or_card_eq_two {G : Type} [Group G] [Finite G] {k : ℕ}
    (B : Basis3 G (k + 1)) (b₀ : G) (hb₀ : orderOf b₀ = 3) (hb : B.b 0 = b₀) :
    B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) =
        B.realized (Subgroup.centralizer ({b₀} : Set G)) ∨
      Nat.card ↥(B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))) =
        2 * Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) := by
  classical
  set N := Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) with hN
  set Cc := Subgroup.centralizer ({b₀} : Set G) with hC
  have hb3 : b₀ ^ 3 = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have hb1 : b₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb₀
    omega
  have hvec0 : B.vec (Pi.single (0 : Fin (k + 1)) 1) = b₀ := by
    rw [B.vec_single, hb]
  have hCN : Cc ≤ N := by
    intro g hg
    have hcomm : b₀ * g = g * b₀ :=
      Subgroup.mem_centralizer_iff.mp hg b₀ (Set.mem_singleton b₀)
    have hconj : g * b₀ * g⁻¹ = b₀ := by rw [← hcomm]; group
    have hinv : g⁻¹ * b₀ * g = b₀ := by
      calc g⁻¹ * b₀ * g = g⁻¹ * (b₀ * g) := by group
        _ = g⁻¹ * (g * b₀) := by rw [hcomm]
        _ = b₀ := by group
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨z, by rw [(conj_zpow (a := g) (b := b₀) (i := z)).symm, hconj]⟩
    · intro hx
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨z, ?_⟩
      have h1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      have hxeq : x = b₀ ^ z := by
        have hcz : g⁻¹ * b₀ ^ z * g = (g⁻¹ * b₀ * g) ^ z := by
          simpa using (conj_zpow (a := g⁻¹) (b := b₀) (i := z)).symm
        rw [← h1, ← hz, hcz, hinv]
      exact hxeq.symm
  have hcol : ∀ M ∈ B.realized N,
      M *ᵥ Pi.single 0 1 = Pi.single 0 1 ∨ M *ᵥ Pi.single 0 1 = -Pi.single 0 1 := by
    rintro M ⟨g, hgN, hActs⟩
    have hmem : g * b₀ * g⁻¹ ∈ Subgroup.zpowers b₀ :=
      (Subgroup.mem_normalizer_iff.mp hgN b₀).mp (Subgroup.mem_zpowers b₀)
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hconj3 : (g * b₀ * g⁻¹) ^ (3 : ℤ) = 1 := by
      rw [conj_zpow (a := g) (b := b₀) (i := (3 : ℤ)),
        show b₀ ^ (3 : ℤ) = 1 from by
          rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hb3],
        mul_one, mul_inv_cancel]
    have hne : g * b₀ * g⁻¹ ≠ 1 := by
      intro h1
      apply hb1
      have h2 : b₀ = g⁻¹ * (g * b₀ * g⁻¹) * g := by group
      rw [h1] at h2
      simpa using h2
    have hcases : g * b₀ * g⁻¹ = b₀ ∨ g * b₀ * g⁻¹ = b₀⁻¹ := by
      have hmod : b₀ ^ (z % 3) = b₀ ^ z := (zpow_eq_zpow_emod' z hb3).symm
      have hlt : z % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
      have hge : 0 ≤ z % 3 := Int.emod_nonneg _ (by norm_num)
      have hr : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
      rcases hr with h | h | h
      · exfalso
        apply hne
        rw [← hz, ← hmod, h]
        simp
      · left
        rw [← hz, ← hmod, h]
        norm_num
      · right
        rw [← hz, ← hmod, h, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, show (2 + 1 : ℕ) = 3 from rfl, hb3]
    have hcol0 : (fun i => M i 0) = Pi.single (0 : Fin (k + 1)) 1 ∨
        (fun i => M i 0) = -Pi.single (0 : Fin (k + 1)) 1 := by
      have hvv : B.vec (fun i => M i 0) = g * b₀ * g⁻¹ :=
        (B.acts_col_zero hActs hb).symm
      rcases hcases with h | h
      · left
        apply B.vec_injective
        rw [hvv, h, B.vec_single, hb]
      · right
        apply B.vec_injective
        rw [hvv, h, B.vec_neg_single, hb]
    rcases hcol0 with h | h
    · left; rw [Basis3.mulVec_single_zero, h]
    · right; rw [Basis3.mulVec_single_zero, h]
  set P : Set (Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3)) :=
    {M | M ∈ B.realized N ∧ M *ᵥ Pi.single 0 1 = Pi.single 0 1} with hPdef
  set Q : Set (Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3)) :=
    {M | M ∈ B.realized N ∧ M *ᵥ Pi.single 0 1 = -Pi.single 0 1} with hQdef
  have hcol0ne : (Pi.single (0 : Fin (k + 1)) 1 : Fin (k + 1) → ZMod 3) ≠
      -Pi.single 0 1 := by
    intro h
    have h0 := congrFun h 0
    simp only [Pi.single_eq_same, Pi.neg_apply] at h0
    exact absurd h0 (by decide)
  have hP_eq : B.realized Cc = P := by
    ext M
    constructor
    · intro hM
      refine ⟨realized_mono B hCN hM, ?_⟩
      obtain ⟨g, hg, hActs⟩ := hM
      have hcomm : b₀ * g = g * b₀ :=
        Subgroup.mem_centralizer_iff.mp hg b₀ (Set.mem_singleton b₀)
      have hgb : g * b₀ * g⁻¹ = b₀ := by rw [← hcomm]; group
      have hv : B.vec (fun i => M i 0) = B.vec (Pi.single 0 1) := by
        rw [← B.acts_col_zero hActs hb, hgb, B.vec_single, hb]
      rw [Basis3.mulVec_single_zero, B.vec_injective hv]
    · rintro ⟨hM, hcolM⟩
      obtain ⟨g, hgN, hActs⟩ := hM
      have hv : B.vec (fun i => M i 0) = B.vec (Pi.single 0 1) := by
        rw [← Basis3.mulVec_single_zero M, hcolM]
      have hgb : g * b₀ * g⁻¹ = b₀ := by
        rw [B.acts_col_zero hActs hb, hv, B.vec_single, hb]
      have hgC : g ∈ Cc := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyb : y = b₀ := Set.mem_singleton_iff.mp hy
        rw [hyb]
        conv_lhs => rw [← hgb]
        group
      exact ⟨g, hgC, hActs⟩
  have hcover : B.realized N ⊆ P ∪ Q := by
    intro M hM
    rcases hcol M hM with h | h
    · exact Or.inl ⟨hM, h⟩
    · exact Or.inr ⟨hM, h⟩
  have hdisj : Disjoint P Q := by
    rw [Set.disjoint_left]
    rintro M ⟨-, h1⟩ ⟨-, h2⟩
    exact hcol0ne (h1.symm.trans h2)
  by_cases hsub : B.realized N ⊆ B.realized Cc
  · exact Or.inl (le_antisymm hsub (realized_mono B hCN))
  · right
    obtain ⟨M₀, hM₀N, hM₀C⟩ := Set.not_subset.mp hsub
    have hM₀Q : M₀ ∈ Q := by
      rcases hcover hM₀N with h | h
      · rw [← hP_eq] at h
        exact absurd h hM₀C
      · exact h
    obtain ⟨M₀', hM₀'N, hM₀'_r, hM₀'_l⟩ := B.realized_inv_mem N hM₀N
    have hM₀'col : M₀' *ᵥ Pi.single 0 1 = -Pi.single 0 1 := by
      have h1 : (M₀' * M₀) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
        rw [hM₀'_l, Matrix.one_mulVec]
      rw [← Matrix.mulVec_mulVec, hM₀Q.2, Matrix.mulVec_neg] at h1
      exact neg_eq_iff_eq_neg.mp h1
    have hcardPQ : Nat.card ↥P = Nat.card ↥Q := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun M => ⟨M.1 * M₀, realized_mul B M.2.1 hM₀N, ?_⟩
          invFun := fun M => ⟨M.1 * M₀', realized_mul B M.2.1 hM₀'N, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · rw [← Matrix.mulVec_mulVec, hM₀Q.2, Matrix.mulVec_neg, M.2.2]
      · rw [← Matrix.mulVec_mulVec, hM₀'col, Matrix.mulVec_neg, M.2.2, neg_neg]
      · intro M
        apply Subtype.ext
        show (M.1 * M₀) * M₀' = M.1
        rw [Matrix.mul_assoc, hM₀'_r, Matrix.mul_one]
      · intro M
        apply Subtype.ext
        show (M.1 * M₀') * M₀ = M.1
        rw [Matrix.mul_assoc, hM₀'_l, Matrix.mul_one]
    have hcard_split : Nat.card ↥(B.realized N) = Nat.card ↥P + Nat.card ↥Q := by
      classical
      let p : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3) → Prop :=
        fun M => M *ᵥ Pi.single 0 1 = Pi.single 0 1
      let s : Finset (Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3)) :=
        Finset.univ.filter (fun M => M ∈ B.realized N)
      have hcoe : ∀ t : Finset (Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3)),
          Nat.card ↥t = t.card := by
        intro t
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      have hs : (s : Set (Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3))) = B.realized N := by
        ext M
        simp [s]
      have hsP : (s.filter p : Set (Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3))) = P := by
        ext M
        constructor
        · intro h
          obtain ⟨hM, hp⟩ := Finset.mem_filter.mp h
          rw [hPdef]
          exact ⟨(Finset.mem_filter.mp hM).2, hp⟩
        · intro h
          rw [hPdef] at h
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩, h.2⟩
      have hsQ : (s.filter (fun M => ¬ p M) : Set
          (Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3))) = Q := by
        ext M
        constructor
        · intro h
          obtain ⟨hM, hp⟩ := Finset.mem_filter.mp h
          have hMS := (Finset.mem_filter.mp hM).2
          rw [hQdef]
          exact ⟨hMS, by
            rcases hcol M hMS with hh | hh
            · exact absurd hh hp
            · exact hh⟩
        · intro h
          rw [hQdef] at h
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩,
              fun hp => hcol0ne (by rw [← h.2, hp])⟩
      have hs_card : Nat.card ↥(B.realized N) = s.card := by
        rw [← hs]
        exact hcoe s
      have hPc : Nat.card ↥P = (s.filter p).card := by
        rw [← hsP]
        exact hcoe _
      have hQc : Nat.card ↥Q = (s.filter fun M => ¬ p M).card := by
        rw [← hsQ]
        exact hcoe _
      calc Nat.card ↥(B.realized N) = s.card := hs_card
        _ = (s.filter p).card + (s.filter fun M => ¬ p M).card :=
            (Finset.card_filter_add_card_filter_not (s := s) (p := p)).symm
        _ = Nat.card ↥P + Nat.card ↥Q := by rw [← hPc, ← hQc]
    rw [hcard_split, hP_eq, hcardPQ]
    ring

end CFSG.StandardType.FrameRoute.FS81

end
