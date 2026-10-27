module

public import CFSG.Quasithin.Background.FLc6Grp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open
open scoped Pointwise commutatorElement

theorem transvection_mulVec' {F : Type} [Field F] (i j : Fin 3) (c : F) (x : Fin 3 → F) :
    (Matrix.transvection i j c).mulVec x = x + Pi.single i (c * x j) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  ext r
  simp [Pi.single_apply]

theorem eq_univ_of_transvection_invariant {F : Type} [Field F] (X : Set (Fin 3 → F))
    (hadd : ∀ x ∈ X, ∀ y ∈ X, x + y ∈ X) (hneg : ∀ x ∈ X, -x ∈ X)
    (hT : ∀ (i j : Fin 3) (_ : i ≠ j) (c : F), ∀ x ∈ X, (Matrix.transvection i j c).mulVec x ∈ X)
    {x₀ : Fin 3 → F} (hx₀ : x₀ ∈ X) (hne : x₀ ≠ 0) : ∀ v : Fin 3 → F, v ∈ X := by
  obtain ⟨j, hj⟩ : ∃ j, x₀ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hzero : (0 : Fin 3 → F) ∈ X := by
    have := hadd _ hx₀ _ (hneg _ hx₀)
    simpa using this
  have hsingle : ∀ i, i ≠ j → ∀ c : F, (Pi.single i c : Fin 3 → F) ∈ X := by
    intro i hij c
    have h1 := hT i j hij (c * (x₀ j)⁻¹) x₀ hx₀
    have h2 : (Matrix.transvection i j (c * (x₀ j)⁻¹)).mulVec x₀ = x₀ + Pi.single i c := by
      rw [transvection_mulVec', mul_assoc, inv_mul_cancel₀ hj, mul_one]
    rw [h2] at h1
    have := hadd _ h1 _ (hneg _ hx₀)
    simpa using this
  have hsingle' : ∀ k : Fin 3, ∀ c : F, (Pi.single k c : Fin 3 → F) ∈ X := by
    intro k c
    by_cases hk : k = j
    · subst hk
      obtain ⟨i, hi⟩ : ∃ i : Fin 3, i ≠ k := by
        by_cases h0 : k = 0
        · exact ⟨1, by rw [h0]; decide⟩
        · exact ⟨0, fun h => h0 h.symm⟩
      have h1 := hT k i hi.symm c (Pi.single i 1) (hsingle i hi 1)
      have h2 : (Matrix.transvection k i c).mulVec (Pi.single i 1) =
          Pi.single i 1 + Pi.single k c := by
        rw [transvection_mulVec']
        simp
      rw [h2] at h1
      have := hadd _ h1 _ (hneg _ (hsingle i hi 1))
      simpa using this
    · exact hsingle k hk c
  intro v
  have hv : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) + Pi.single 2 (v 2) := by
    ext r
    fin_cases r <;> simp
  rw [hv]
  exact hadd _ (hadd _ (hsingle' 0 _) _ (hsingle' 1 _)) _ (hsingle' 2 _)

variable {G : Type} [Group G]

theorem natural_section_eq_mul {K Q Z N₁ : Subgroup G} {F : Type} [Field F]
    (hsec : IsNaturalSection K Q Z (CFSG.pCore 2 ↥K) (CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hN₁Q : N₁ ≤ Q) (hN₁K : ∀ k ∈ K, ∀ x ∈ N₁, k * x * k⁻¹ ∈ N₁)
    (hnz : ∃ x ∈ N₁, x ∉ Z) : ∀ q ∈ Q, ∃ x ∈ N₁, ∃ z ∈ Z, q = x * z := by
  obtain ⟨hKQ, α, hαs, hαk, β, hβs, hβk, hrel⟩ := hsec
  let X : Set (Fin 3 → F) := {v | ∃ x : ↥Q, (x : G) ∈ N₁ ∧ Multiplicative.toAdd (β x) = v}
  have hXadd : ∀ v ∈ X, ∀ w ∈ X, v + w ∈ X := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine ⟨x * y, N₁.mul_mem hx hy, ?_⟩
    simp [map_mul, toAdd_mul]
  have hXneg : ∀ v ∈ X, -v ∈ X := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x⁻¹, N₁.inv_mem hx, ?_⟩
    simp [map_inv, toAdd_inv]
  have hXT : ∀ (i j : Fin 3) (_ : i ≠ j) (c : F), ∀ v ∈ X,
      (Matrix.transvection i j c).mulVec v ∈ X := by
    intro i j hij c v hv
    obtain ⟨x, hx, rfl⟩ := hv
    have hmem : Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c) ∈
        CFSG.Assembly.LowTwoRank.StatedSL 3 F := by
      apply Subgroup.subset_closure
      show (((Matrix.SpecialLinearGroup.transvection hij c : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F)).det = 1
      exact (Matrix.SpecialLinearGroup.transvection hij c).det_coe
    obtain ⟨a, ha⟩ := hαs ⟨_, hmem⟩
    have hy : (a : G) * x * (a : G)⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hKQ a.2) x).1 x.2
    refine ⟨⟨_, hy⟩, hN₁K a a.2 x hx, ?_⟩
    rw [hrel a x ⟨_, hy⟩ rfl, ha]
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection]
  obtain ⟨x₀, hx₀N, hx₀Z⟩ := hnz
  have hx₀Q : x₀ ∈ Q := hN₁Q hx₀N
  have hβx₀ : β ⟨x₀, hx₀Q⟩ ≠ 1 := by
    intro h
    apply hx₀Z
    have : (⟨x₀, hx₀Q⟩ : ↥Q) ∈ β.ker := h
    rw [hβk, Subgroup.mem_subgroupOf] at this
    exact this
  have hall := eq_univ_of_transvection_invariant X hXadd hXneg hXT
    (x₀ := Multiplicative.toAdd (β ⟨x₀, hx₀Q⟩)) ⟨⟨x₀, hx₀Q⟩, hx₀N, rfl⟩
    (fun h => hβx₀ (by simpa using congrArg Multiplicative.ofAdd h))
  intro q hq
  obtain ⟨x, hxN, hx⟩ := hall (Multiplicative.toAdd (β ⟨q, hq⟩))
  have hxq : β x = β ⟨q, hq⟩ := Multiplicative.toAdd.injective hx
  refine ⟨(x : G), hxN, ((x⁻¹ * ⟨q, hq⟩ : ↥Q) : G), ?_, by simp⟩
  have : x⁻¹ * ⟨q, hq⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxq, inv_mul_cancel]
  rw [hβk, Subgroup.mem_subgroupOf] at this
  exact this

@[expose] def E13 (n : ℕ) (h4 : 3 < n) : SLt n :=
  tv (ix 1 (by omega)) (ix 3 h4) (by simp [ix, Fin.lt_def])

theorem E13_sq {n : ℕ} (hn : n = 4 ∨ n = 5) (h4 : 3 < n) : E13 n h4 * E13 n h4 = 1 := by
  rcases hn with rfl | rfl <;> decide +revert

@[expose] def X1c (n : ℕ) (h3 : 3 ≤ n) (h4 : 3 < n) : SLt n :=
  T1 n h3 * E13 n h4 * (T1 n h3 * T1 n h3) * E13 n h4

@[expose] def X2c (n : ℕ) (h3 : 3 ≤ n) (h4 : 3 < n) : SLt n :=
  (T1 n h3 * T1 n h3) * E13 n h4 * T1 n h3 * E13 n h4

@[expose] def commXA {n : ℕ} (X A : SLt n) : SLt n := X * A * X * (A * A)

theorem comm_values {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) (h4 : 3 < n) :
    X1c n h3 h4 * X1c n h3 h4 = 1 ∧ blk3 h3 (X1c n h3 h4) = 1 ∧
      X2c n h3 h4 * X2c n h3 h4 = 1 ∧ blk3 h3 (X2c n h3 h4) = 1 := by
  rcases hn with rfl | rfl <;> decide +revert

theorem comm_noncentral {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) (h4 : 3 < n) :
    commXA (X1c n h3 h4) (T1 n h3) * T1 n h3 ≠ T1 n h3 * commXA (X1c n h3 h4) (T1 n h3) ∧
    commXA (X1c n h3 h4) (T1 n h3 * T1 n h3) * (T1 n h3 * T1 n h3) ≠
      (T1 n h3 * T1 n h3) * commXA (X1c n h3 h4) (T1 n h3 * T1 n h3) ∧
    commXA (X2c n h3 h4) (T1 n h3) * T1 n h3 ≠ T1 n h3 * commXA (X2c n h3 h4) (T1 n h3) ∧
    commXA (X2c n h3 h4) (T1 n h3 * T1 n h3) * (T1 n h3 * T1 n h3) ≠
      (T1 n h3 * T1 n h3) * commXA (X2c n h3 h4) (T1 n h3 * T1 n h3) := by
  rcases hn with rfl | rfl <;> decide +revert

theorem e0_moved {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) :
    mat (T1 n h3 * T1 n h3) *ᵥ (Pi.single (ix 0 (by omega) : Fin n) (1 : ZMod 2) : Vt n) ≠
        (Pi.single (ix 0 (by omega) : Fin n) (1 : ZMod 2) : Vt n) ∧
    mat ((T1 n h3 * T1 n h3) * (T1 n h3 * T1 n h3)) *ᵥ
        (Pi.single (ix 0 (by omega) : Fin n) (1 : ZMod 2) : Vt n) ≠
        (Pi.single (ix 0 (by omega) : Fin n) (1 : ZMod 2) : Vt n) := by
  rcases hn with rfl | rfl <;> decide +revert


namespace P0Setup

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

include D

theorem centralizes_of_blk3_eq_one (h3n : 3 < n) {l : ↥L}
    (hst : D.α l ∈ stabilizer (flagSpace n (ZMod 2) 3)) (hb : blk3 h3n.le (D.α l) = 1) :
    (l : G) ∈ Subgroup.centralizer (W 3 : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨hwU, hwF⟩ := (D.W_mem (by norm_num) h3n w).1 hw
  have hlu : (l : G) * w * (l : G)⁻¹ ∈ UL := (Subgroup.mem_normalizer_iff.1 (D.L_le l.2) w).1 hwU
  have h1 := D.rel l ⟨w, hwU⟩ ⟨_, hlu⟩ rfl
  have h2 : mat (D.α l) *ᵥ Multiplicative.toAdd (D.β ⟨w, hwU⟩) =
      Multiplicative.toAdd (D.β ⟨w, hwU⟩) := fixes_of_blk3_eq_one h3n.le hst hb hwF
  have h3 : D.β ⟨_, hlu⟩ = D.β ⟨w, hwU⟩ := Multiplicative.toAdd.injective (by rw [h1, h2])
  have h4 : (⟨_, hlu⟩ : ↥UL) = ⟨w, hwU⟩ := D.β.injective h3
  have h5 : (l : G) * w * (l : G)⁻¹ = w := congrArg Subtype.val h4
  calc w * (l : G) = ((l : G) * w * (l : G)⁻¹) * (l : G) := by rw [h5]
    _ = (l : G) * w := by group

theorem exists_lift_T1 [Finite G] (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) :
    ∃ l : ↥L, (l : G) ∈ kNode L S n W ∧ (D.α l = T1 n h3 ∨ D.α l = T1 n h3 * T1 n h3) := by
  obtain ⟨hT1, -, -⟩ := node_compute hn h3
  obtain ⟨l, hodd, hl⟩ := D.exists_odd_lift hT1
  have hαl : D.α l ∈ Qn n 1 := by
    rcases hl with h | h
    · rw [h]; exact T1_mem_Qn h3
    · rw [h]; exact (Qn n 1).mul_mem (T1_mem_Qn h3) (T1_mem_Qn h3)
  have hlP : (l : G) ∈ parab (L ⊔ S) n W 1 := D.mem_parab_of_alpha l hαl
  exact ⟨l, Subgroup.mem_sup_left (show (l : G) ∈ yNode L S n W 1 from
    mem_oTwoUpper_of_odd hlP hodd), hl⟩

theorem exists_witnesses [Finite G] (hn : n = 4 ∨ n = 5) :
    ∃ (l₁ q₀ : ↥L) (n₀ : G),
      (l₁ : G) ∈ kNode L S n W ∧ (q₀ : G) ∈ ⁅pCoreOf 2 (gNode L S n W), kNode L S n W⁆ ∧
      n₀ ∈ ⁅UL, kNode L S n W⁆ ∧ D.α q₀ * D.α l₁ ≠ D.α l₁ * D.α q₀ ∧
      (l₁ : G) * n₀ * (l₁ : G)⁻¹ ≠ n₀ := by
  have h3 : 3 ≤ n := by omega
  have h4 : 3 < n := by omega
  obtain ⟨hT1, -, -⟩ := node_compute hn h3
  obtain ⟨l₁, hl₁K, hl₁⟩ := D.exists_lift_T1 hn h3
  have hAcube : D.α l₁ * D.α l₁ * D.α l₁ = 1 := by
    rcases hl₁ with h | h
    · rw [h]; exact hT1
    · rw [h]
      calc T1 n h3 * T1 n h3 * (T1 n h3 * T1 n h3) * (T1 n h3 * T1 n h3) =
          (T1 n h3 * T1 n h3 * T1 n h3) * (T1 n h3 * T1 n h3 * T1 n h3) := by group
        _ = 1 := by rw [hT1, one_mul]
  obtain ⟨a, haY, ha⟩ := D.exists_comm_lift (j := 1) hT1 (E13_sq hn h4) (T1_mem_Qn h3)
    (tv_mem_Ut _ : E13 n h4 ∈ Ut n)
  have haK : (a : G) ∈ kNode L S n W := Subgroup.mem_sup_left haY
  obtain ⟨hv1, hv2, hv3, hv4⟩ := comm_values hn h3 h4
  have hXa : D.α a * D.α a = 1 ∧ blk3 h3 (D.α a) = 1 := by
    rcases ha with h | h
    · rw [h]; exact ⟨hv1, hv2⟩
    · rw [h]; exact ⟨hv3, hv4⟩
  have hst : D.α a ∈ stabilizer (flagSpace n (ZMod 2) 3) :=
    (D.mem_normalizer_W (by norm_num) h4 a).1 (kNode_le_normalizer_W 3 le_rfl h4 haK)
  have haC : (a : G) ∈ Subgroup.centralizer (W 3 : Set G) :=
    D.centralizes_of_blk3_eq_one h4 hst hXa.2
  have haO : (a : G) ∈ pCoreOf 2 (gNode L S n W) :=
    inf_centralizer_le_pCoreOf_of_kernel D.qNode_le_normalizer_kNode
      (D.gNode_le_normalizer_W 3 le_rfl h4) (D.inf_centralizer_isPGroup hn) qNode_isPGroup
      ⟨kNode_le_gNode haK, haC⟩
  set q₀ : ↥L := a * l₁ * a⁻¹ * l₁⁻¹ with hq₀
  have hq₀G : (q₀ : G) = ⁅(a : G), (l₁ : G)⁆ := by
    simp [hq₀, commutatorElement_def]
  have hq₀Q : (q₀ : G) ∈ ⁅pCoreOf 2 (gNode L S n W), kNode L S n W⁆ := by
    rw [hq₀G]
    exact Subgroup.commutator_mem_commutator haO hl₁K
  have hαq : D.α q₀ = commXA (D.α a) (D.α l₁) := by
    simp only [hq₀, map_mul, map_inv, commXA]
    have e1 : (D.α a)⁻¹ = D.α a := inv_eq_of_mul_eq_one_right hXa.1
    have e2 : (D.α l₁)⁻¹ = D.α l₁ * D.α l₁ := inv_eq_of_mul_eq_one_right (by
      rw [← mul_assoc]; exact hAcube)
    rw [e1, e2]
  have hnc : D.α q₀ * D.α l₁ ≠ D.α l₁ * D.α q₀ := by
    rw [hαq]
    obtain ⟨c1, c2, c3, c4⟩ := comm_noncentral hn h3 h4
    rcases ha with h | h <;> rcases hl₁ with h' | h' <;> rw [h, h']
    · exact c1
    · exact c2
    · exact c3
    · exact c4
  obtain ⟨u₀, hβu₀⟩ : ∃ u₀ : ↥UL,
      Multiplicative.toAdd (D.β u₀) = (Pi.single (ix 0 (by omega)) 1 : Vt n) :=
    ⟨D.β.symm (Multiplicative.ofAdd (Pi.single (ix 0 (by omega)) 1)), by simp⟩
  have hl₁N : (l₁ : G) ∈ Subgroup.normalizer (UL : Set G) := D.L_le l₁.2
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : ↥UL, (u₁ : G) = (l₁ : G) * (u₀ : G) * (l₁ : G)⁻¹ :=
    ⟨⟨_, (Subgroup.mem_normalizer_iff.1 hl₁N u₀).1 u₀.2⟩, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : ↥UL, (u₂ : G) = (l₁ : G) * (u₁ : G) * (l₁ : G)⁻¹ :=
    ⟨⟨_, (Subgroup.mem_normalizer_iff.1 hl₁N u₁).1 u₁.2⟩, rfl⟩
  have hβ₁ : Multiplicative.toAdd (D.β u₁) =
      mat (D.α l₁) *ᵥ (Pi.single (ix 0 (by omega)) 1 : Vt n) := by
    rw [D.rel l₁ u₀ u₁ hu₁, hβu₀]
  have hβ₂ : Multiplicative.toAdd (D.β u₂) =
      mat (D.α l₁) *ᵥ (mat (D.α l₁) *ᵥ (Pi.single (ix 0 (by omega)) 1 : Vt n)) := by
    rw [D.rel l₁ u₁ u₂ hu₂, hβ₁]
  refine ⟨l₁, q₀, (u₀ : G) * l₁ * (u₀ : G)⁻¹ * (l₁ : G)⁻¹, hl₁K, hq₀Q,
    Subgroup.commutator_mem_commutator u₀.2 hl₁K, hnc, ?_⟩
  intro heq
  have h1 : u₁ * u₂⁻¹ = u₀ * u₁⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu₁, hu₂]
    calc _ = (l₁ : G) * ((u₀ : G) * l₁ * (u₀ : G)⁻¹ * (l₁ : G)⁻¹) * (l₁ : G)⁻¹ := by group
      _ = (u₀ : G) * l₁ * (u₀ : G)⁻¹ * (l₁ : G)⁻¹ := heq
      _ = _ := by group
  have h2 := congrArg (fun x => Multiplicative.toAdd (D.β x)) h1
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, hβ₁, hβ₂, hβu₀] at h2
  have key : ∀ x y z : Vt n, x + -y = z + -x → y = z := by
    intro x y z h
    ext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.neg_apply] at this
    generalize x i = a' at this ⊢
    generalize y i = b' at this ⊢
    generalize z i = c' at this ⊢
    revert a' b' c'
    decide
  have h3' := key _ _ _ h2
  rw [Matrix.mulVec_mulVec, ← mat_mul] at h3'
  obtain ⟨m1, m2⟩ := e0_moved hn h3
  rcases hl₁ with h | h
  · rw [h] at h3'
    exact m1 h3'
  · rw [h] at h3'
    exact m2 h3'

theorem not_isNaturalSection [Finite G] (hn : n = 4 ∨ n = 5) (hUL : UL ≤ L ⊔ S) (hULL : UL ≤ L)
    {F : Type} [Field F] {Z : Subgroup G}
    (hZ : ∀ z ∈ Z, ∀ k ∈ kNode L S n W, k * z = z * k)
    (hsec : IsNaturalSection (kNode L S n W) ⁅pCoreOf 2 (gNode L S n W), kNode L S n W⁆ Z
      (CFSG.pCore 2 ↥(kNode L S n W)) (CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : False := by
  obtain ⟨l₁, q₀, n₀, hl₁K, hq₀Q, hn₀N, hnc, hn₀mov⟩ := D.exists_witnesses hn
  have hULq := D.UL_le_qNode hUL
  have hULG : UL ≤ gNode L S n W := hULq.trans le_sup_right
  have hGUL : gNode L S n W ≤ Subgroup.normalizer (UL : Set G) :=
    sup_le (D.kNode_le_L.trans D.L_le) (D.qNode_le_S.trans D.S_le)
  have hULO : UL ≤ pCoreOf 2 (gNode L S n W) :=
    le_pCoreOf_of_le_normalizer 2 hULG hGUL D.UL_isPGroup
  have hN₁Q : ⁅UL, kNode L S n W⁆ ≤ ⁅pCoreOf 2 (gNode L S n W), kNode L S n W⁆ :=
    Subgroup.commutator_mono hULO le_rfl
  have hN₁K : ∀ k ∈ kNode L S n W, ∀ x ∈ ⁅UL, kNode L S n W⁆,
      k * x * k⁻¹ ∈ ⁅UL, kNode L S n W⁆ := by
    intro k hk x hx
    have hkU : k ∈ Subgroup.normalizer (UL : Set G) := D.L_le (D.kNode_le_L hk)
    have hkK : k ∈ Subgroup.normalizer ((kNode L S n W : Subgroup G) : Set G) :=
      Subgroup.le_normalizer hk
    exact (Subgroup.mem_normalizer_iff.1 (A4.mem_normalizer_commutator hkU hkK) x).1 hx
  have hN₁UL : ∀ x ∈ ⁅UL, kNode L S n W⁆, x ∈ UL := by
    intro x hx
    have : ⁅UL, kNode L S n W⁆ ≤ UL := by
      refine Subgroup.commutator_le.2 fun u hu k hk => ?_
      have hkU : k ∈ Subgroup.normalizer (UL : Set G) := D.L_le (D.kNode_le_L hk)
      have h1 : k * u⁻¹ * k⁻¹ ∈ UL := (Subgroup.mem_normalizer_iff.1 hkU u⁻¹).1 (UL.inv_mem hu)
      have e : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact UL.mul_mem hu h1
    exact this hx
  have hn₀Z : n₀ ∉ Z := by
    intro hz
    apply hn₀mov
    have h1 := hZ n₀ hz l₁ hl₁K
    calc (l₁ : G) * n₀ * (l₁ : G)⁻¹ = (n₀ * l₁) * (l₁ : G)⁻¹ := by rw [h1]
      _ = n₀ := by group
  obtain ⟨x, hxN, z, hzZ, hxz⟩ :=
    natural_section_eq_mul hsec hN₁Q hN₁K ⟨n₀, hn₀N, hn₀Z⟩ q₀ hq₀Q
  have hxUL : x ∈ UL := hN₁UL x hxN
  have hxL : x ∈ L := hULL hxUL
  have hzL : z ∈ L := by
    have : z = x⁻¹ * (q₀ : G) := by rw [hxz]; group
    rw [this]
    exact L.mul_mem (L.inv_mem hxL) q₀.2
  have hαx : D.α ⟨x, hxL⟩ = 1 :=
    D.alpha_eq_one_of_mem_centralizer (a := ⟨x, hxL⟩)
      (Subgroup.mem_centralizer_iff.2 fun u hu => D.UL_comm hu hxUL)
  have hq₀eq : q₀ = ⟨x, hxL⟩ * ⟨z, hzL⟩ := Subtype.ext hxz
  have hl₁z : l₁ * ⟨z, hzL⟩ = ⟨z, hzL⟩ * l₁ := Subtype.ext (hZ z hzZ l₁ hl₁K)
  apply hnc
  rw [hq₀eq, map_mul, hαx, one_mul, ← map_mul, ← map_mul, hl₁z]

theorem not_isC134Case1 [Finite G] (hn : n = 4 ∨ n = 5) (hUL : UL ≤ L ⊔ S) (hULL : UL ≤ L) :
    ¬ IsC134Case1 (gNode L S n W) (qNode L S n W) (kNode L S n W) := by
  rintro ⟨-, m, F, hF, hFin, hcard, hsec⟩
  exact D.not_isNaturalSection hn hUL hULL (Z := ⊥)
    (fun z hz k _ => by rw [Subgroup.mem_bot.1 hz]; simp) hsec

theorem not_isC134Case5 [Finite G] (hn : n = 4 ∨ n = 5) (hUL : UL ≤ L ⊔ S) (hULL : UL ≤ L) :
    ¬ IsC134Case5 (gNode L S n W) (qNode L S n W) (kNode L S n W) := by
  rintro ⟨⟨α, hα, -, hvia⟩, -⟩
  have hsec : IsNaturalSection (kNode L S n W) (c134Q (gNode L S n W) (kNode L S n W))
      (c134CQ (gNode L S n W) (kNode L S n W)) (CFSG.pCore 2 ↥(kNode L S n W))
      (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ hvia.2.1).2 ⟨α, hα.1, hα.2, hvia⟩
  exact D.not_isNaturalSection hn hUL hULL (Z := c134CQ (gNode L S n W) (kNode L S n W))
    (fun z hz k hk => Subgroup.mem_centralizer_iff.1 hz.2 k hk) hsec

end P0Setup

end CFSG.Quasithin.FLc
