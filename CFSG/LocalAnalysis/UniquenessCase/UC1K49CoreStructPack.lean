module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

variable {G : Type} [Group G] [Finite G]

open scoped commutatorElement IsMulCommutative
open CFSG.ABGLocalTools

theorem chief_struct49_sup_eq_Lc_ne {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) :
    Lc L x i ≠ Lc L x j := by
  have hxX : x ∈ X := hx ▸ Subgroup.mem_zpowers x
  have hord : orderOf x = 3 := by
    rw [← Nat.card_zpowers, ← hx]
    exact h.card_X
  obtain ⟨h01, h02, h12⟩ := conjugates_distinct h hxX hx hord
  interval_cases i <;> interval_cases j <;>
    first | exact absurd rfl hij | assumption | exact Ne.symm ‹_›

theorem chief_struct49_sup_eq_Lc_normalizes {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hx : X = Subgroup.zpowers x) {N M : Subgroup G} (hch : HChief H N M)
    {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    Lc L x i ≤ Subgroup.normalizer (⁅N, Lc L x j⁆ ⊔ M : Subgroup G) := by
  have hxX : x ∈ X := hx ▸ Subgroup.mem_zpowers x
  have hLiH : Lc L x i ≤ H :=
    (conjugate_le_I h (X.pow_mem hxX i)).trans (I_le_H h)
  have hLj : Lc L x i ≤ Subgroup.normalizer (Lc L x j : Set G) := by
    by_cases hij : i = j
    · subst hij
      exact Subgroup.le_normalizer
    · exact conjugate_normalize_of_ne h (X.pow_mem hxX i) (X.pow_mem hxX j)
        (chief_struct49_sup_eq_Lc_ne h hx hi hj hij)
  have hcomm : Lc L x i ≤ Subgroup.normalizer (⁅N, Lc L x j⁆ : Subgroup G) :=
    le_normalizer_commutator49 (hLiH.trans hch.2.1) hLj
  have hM : Lc L x i ≤ Subgroup.normalizer (M : Set G) := hLiH.trans hch.2.2.1
  exact (le_inf hcomm hM).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)

theorem chief_struct49_sup_eq_Lc_normalizes_E {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hx : X = Subgroup.zpowers x) {N M : Subgroup G} (hch : HChief H N M)
    (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) {i : ℕ} (hi : i < 3) :
    Lc L x i ≤ Subgroup.normalizer (V 0 ⊔ V 1 ⊔ V 2 : Subgroup G) := by
  have h0 : Lc L x i ≤ Subgroup.normalizer (V 0 : Set G) := by
    rw [hV 0]
    exact chief_struct49_sup_eq_Lc_normalizes h hx hch hi (by norm_num)
  have h1 : Lc L x i ≤ Subgroup.normalizer (V 1 : Set G) := by
    rw [hV 1]
    exact chief_struct49_sup_eq_Lc_normalizes h hx hch hi (by norm_num)
  have h2 : Lc L x i ≤ Subgroup.normalizer (V 2 : Set G) := by
    rw [hV 2]
    exact chief_struct49_sup_eq_Lc_normalizes h hx hch hi (by norm_num)
  have h01 : Lc L x i ≤ Subgroup.normalizer (V 0 ⊔ V 1 : Subgroup G) :=
    (le_inf h0 h1).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  exact (le_inf h01 h2).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)

theorem chief_struct49_sup_eq_commutator_le {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hx : X = Subgroup.zpowers x) {N M : Subgroup G} (hch : HChief H N M)
    (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) :
    ⁅N, I⁆ ≤ V 0 ⊔ V 1 ⊔ V 2 := by
  have hxX : x ∈ X := hx ▸ Subgroup.mem_zpowers x
  have hIeq : I = Lc L x 0 ⊔ Lc L x 1 ⊔ Lc L x 2 := by
    simpa only [Lc, pow_zero, pow_one, conjugate_one] using I_eq_sup_conjugates49 h hxX hx
  have hVle : ∀ i, ⁅N, Lc L x i⁆ ≤ V i := by
    intro i
    rw [hV i]
    exact le_sup_left
  have hV0E : V 0 ≤ V 0 ⊔ V 1 ⊔ V 2 := le_sup_of_le_left (le_sup_of_le_left le_rfl)
  have hV1E : V 1 ≤ V 0 ⊔ V 1 ⊔ V 2 := le_sup_of_le_left (le_sup_of_le_right le_rfl)
  have hV2E : V 2 ≤ V 0 ⊔ V 1 ⊔ V 2 := le_sup_of_le_right le_rfl
  rw [hIeq]
  have h01 : ⁅N, Lc L x 0 ⊔ Lc L x 1⁆ ≤ V 0 ⊔ V 1 ⊔ V 2 := by
    refine commutator_sup_le_of_normal49 ?_ ?_ ?_ ?_ ?_
    · exact conjugate_normalize_of_ne h (X.pow_mem hxX 0) (X.pow_mem hxX 1)
        (chief_struct49_sup_eq_Lc_ne h hx (by norm_num) (by norm_num) (by norm_num))
    · exact chief_struct49_sup_eq_Lc_normalizes_E h hx hch V hV (by norm_num)
    · exact chief_struct49_sup_eq_Lc_normalizes_E h hx hch V hV (by norm_num)
    · exact (hVle 0).trans hV0E
    · exact (hVle 1).trans hV1E
  refine commutator_sup_le_of_normal49 ?_ ?_ ?_ h01 ?_
  · exact sup_le
      (conjugate_normalize_of_ne h (X.pow_mem hxX 0) (X.pow_mem hxX 2)
        (chief_struct49_sup_eq_Lc_ne h hx (by norm_num) (by norm_num) (by norm_num)))
      (conjugate_normalize_of_ne h (X.pow_mem hxX 1) (X.pow_mem hxX 2)
        (chief_struct49_sup_eq_Lc_ne h hx (by norm_num) (by norm_num) (by norm_num)))
  · exact sup_le (chief_struct49_sup_eq_Lc_normalizes_E h hx hch V hV (by norm_num))
      (chief_struct49_sup_eq_Lc_normalizes_E h hx hch V hV (by norm_num))
  · exact chief_struct49_sup_eq_Lc_normalizes_E h hx hch V hV (by norm_num)
  · exact (hVle 2).trans hV2E

theorem chief_struct49_sup_eq_le_sup {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hx : X = Subgroup.zpowers x) {N M : Subgroup G} (V : ℕ → Subgroup G)
    (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) :
    V 0 ⊔ V 1 ⊔ V 2 ≤ ⁅N, I⁆ ⊔ M := by
  have hxX : x ∈ X := hx ▸ Subgroup.mem_zpowers x
  have h0 : V 0 ≤ ⁅N, I⁆ ⊔ M := by
    rw [hV 0]
    exact sup_le ((Subgroup.commutator_mono_right (conjugate_le_I h (X.pow_mem hxX 0))).trans
      le_sup_left) le_sup_right
  have h1 : V 1 ≤ ⁅N, I⁆ ⊔ M := by
    rw [hV 1]
    exact sup_le ((Subgroup.commutator_mono_right (conjugate_le_I h (X.pow_mem hxX 1))).trans
      le_sup_left) le_sup_right
  have h2 : V 2 ≤ ⁅N, I⁆ ⊔ M := by
    rw [hV 2]
    exact sup_le ((Subgroup.commutator_mono_right (conjugate_le_I h (X.pow_mem hxX 2))).trans
      le_sup_left) le_sup_right
  exact sup_le (sup_le h0 h1) h2

theorem chief_struct49_sup_eq {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) {A : Subgroup G} {a n : G} (hd : XAData X L I x A a n)
    {N M : Subgroup G} (hch : HChief H N M) (hI : ¬ ⁅N, I⁆ ≤ M) :
    ∀ V : ℕ → Subgroup G, (∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) → N = V 0 ⊔ V 1 ⊔ V 2 := by
  intro V hV
  have hxX : x ∈ X := hx ▸ Subgroup.mem_zpowers x
  have hI_le : ⁅N, I⁆ ≤ V 0 ⊔ V 1 ⊔ V 2 :=
    chief_struct49_sup_eq_commutator_le h hx hch V hV
  have h_le : V 0 ⊔ V 1 ⊔ V 2 ≤ ⁅N, I⁆ ⊔ M :=
    chief_struct49_sup_eq_le_sup h hx V hV
  have hM0 : M ≤ V 0 := by
    rw [hV 0]
    exact le_sup_right
  have hME : M ≤ V 0 ⊔ V 1 ⊔ V 2 :=
    hM0.trans (le_sup_of_le_left (le_sup_of_le_left le_rfl))
  have hV0N : ⁅N, Lc L x 0⁆ ≤ N :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (((conjugate_le_I h (X.pow_mem hxX 0)).trans (I_le_H h)).trans hch.2.1)
  have hV1N : ⁅N, Lc L x 1⁆ ≤ N :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (((conjugate_le_I h (X.pow_mem hxX 1)).trans (I_le_H h)).trans hch.2.1)
  have hV2N : ⁅N, Lc L x 2⁆ ≤ N :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (((conjugate_le_I h (X.pow_mem hxX 2)).trans (I_le_H h)).trans hch.2.1)
  have hEN : V 0 ⊔ V 1 ⊔ V 2 ≤ N := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [hV 0]; exact sup_le hV0N hch.1.le
    · rw [hV 1]; exact sup_le hV1N hch.1.le
    · rw [hV 2]; exact sup_le hV2N hch.1.le
  have hE_eq : (V 0 ⊔ V 1 ⊔ V 2 : Subgroup G) = ⁅N, I⁆ ⊔ M :=
    le_antisymm h_le (sup_le hI_le hME)
  have hHn : H ≤ Subgroup.normalizer (⁅N, I⁆ ⊔ M : Subgroup G) :=
    (le_inf (le_normalizer_commutator49 hch.2.1 (le_normalizer_I h)) hch.2.2.1).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hHn' : H ≤ Subgroup.normalizer (V 0 ⊔ V 1 ⊔ V 2 : Subgroup G) := by
    rw [hE_eq]
    exact hHn
  rcases hch.2.2.2.2.2.2 (V 0 ⊔ V 1 ⊔ V 2) hME hEN hHn' with hEM | hEN'
  · exact absurd (hEM ▸ hI_le) hI
  · exact hEN'.symm

section Context

variable {H X L Q I : Subgroup G} {x : G} {A : Subgroup G} {a n : G} {N M : Subgroup G}

namespace Ctx49

variable (c : Ctx49 H X L Q I x A a n N M)

theorem direct_V_le_N (c : Ctx49 H X L Q I x A a n N M) (V : ℕ → Subgroup G)
    (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) (j : ℕ) : V j ≤ N := by
  have hLjN : Lc L x j ≤ Subgroup.normalizer (N : Set G) := (c.Lc_H j).trans c.chief.2.1
  rw [hV j]
  refine sup_le ?_ c.chief.1.le
  rw [Subgroup.commutator_le]
  intro n hn l hl
  have hmem : l * n * l⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hLjN hl) n).mp hn
  have hthis : ⁅n, l⁆ = ⁅l, n⁆⁻¹ := by simp only [commutatorElement_def]; group
  rw [hthis]
  exact N.inv_mem (N.mul_mem hmem (N.inv_mem hn))

theorem direct_comm_mem_sup {Vj Vk : Subgroup G} {d : G}
    (hVjk : Vj ≤ Subgroup.normalizer (Vk : Set G)) (hVjN : Vj ≤ N) (hVkN : Vk ≤ N)
    (hNM : N ≤ Subgroup.normalizer (M : Set G))
    (hj : ∀ n ∈ Vj, ⁅n, d⁆ ∈ M) (hk : ∀ n ∈ Vk, ⁅n, d⁆ ∈ M) :
    ∀ n ∈ Vj ⊔ Vk, ⁅n, d⁆ ∈ M := by
  intro n hn
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_le_normalizer hVjk).mp hn
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hb' : a * ⁅b, d⁆ * a⁻¹ ∈ M :=
    (Subgroup.mem_normalizer_iff.mp (hNM (hVjN ha)) ⁅b, d⁆).mp (hk b hb)
  exact M.mul_mem hb' (hj a ha)

theorem direct_le_normalizer (c : Ctx49 H X L Q I x A a n N M) {Vj Vk : Subgroup G}
    (hVjN : Vj ≤ N) (hVkN : Vk ≤ N) (hMVk : M ≤ Vk) :
    Vj ≤ Subgroup.normalizer (Vk : Set G) := by
  refine Subgroup.le_normalizer_iff_commutator_le_right.mpr ?_
  exact (Subgroup.commutator_le.mpr fun a ha b hb =>
    c.chief.2.2.2.2.1 a (hVjN ha) b (hVkN hb)).trans hMVk

theorem direct_op_fix (c : Ctx49 H X L Q I x A a n N M)
    [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]
    {y : G} (hy : y ∈ N) {g : ↥H} (hcomm : ⁅y, (g : G)⁆ ∈ M) :
    op49 c.chief g (Additive.ofMul ((⟨y, hy⟩ : ↥N) : N ⧸ M.subgroupOf N)) =
      Additive.ofMul ((⟨y, hy⟩ : ↥N) : N ⧸ M.subgroupOf N) := by
  have hNM : N ≤ Subgroup.normalizer (M : Set G) :=
    (c.NQ.trans (Q_le_H49 c.setup)).trans c.chief.2.2.1
  have hq : ((chiefConj c.chief.2.1 g ⟨y, hy⟩ : ↥N) : N ⧸ M.subgroupOf N) =
      ((⟨y, hy⟩ : ↥N) : N ⧸ M.subgroupOf N) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hcoe : (((chiefConj c.chief.2.1 g ⟨y, hy⟩)⁻¹ * ⟨y, hy⟩ : ↥N) : G) =
        y⁻¹ * ⁅y, (g : G)⁆ * y := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, chiefConj_apply_coe, commutatorElement_def]
      group
    rw [hcoe]
    exact (Subgroup.mem_normalizer_iff''.mp (hNM hy) ⁅y, (g : G)⁆).mp hcomm
  calc op49 c.chief g (Additive.ofMul ((⟨y, hy⟩ : ↥N) : N ⧸ M.subgroupOf N))
      = Additive.ofMul ((chiefConj c.chief.2.1 g ⟨y, hy⟩ : ↥N) : N ⧸ M.subgroupOf N) :=
        chiefRep_apply_mk (p := 2) c.chief.2.1 c.chief.2.2.1 g ⟨y, hy⟩
    _ = Additive.ofMul ((⟨y, hy⟩ : ↥N) : N ⧸ M.subgroupOf N) := by rw [hq]

theorem direct_inf_sup_eq (c : Ctx49 H X L Q I x A a n N M)
    [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]
    (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (h3 : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅V i, Lc L x j⁆ ≤ M)
    {i j k : ℕ} (hi : i < 3) (hj : j < 3) (hk : k < 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    V i ⊓ (V j ⊔ V k) = M := by
  have hVN : ∀ t, V t ≤ N := direct_V_le_N c V hV
  have hMV : ∀ t, M ≤ V t := fun t => by rw [hV t]; exact le_sup_right
  have hNM : N ≤ Subgroup.normalizer (M : Set G) :=
    (c.NQ.trans (Q_le_H49 c.setup)).trans c.chief.2.2.1
  refine le_antisymm ?_ (le_inf (hMV i) (le_sup_of_le_left (hMV j)))
  intro y hy
  have hyVi : y ∈ V i := hy.1
  have hyjk : y ∈ V j ⊔ V k := hy.2
  have hyN : y ∈ N := hVN i hyVi
  let v : Additive (N ⧸ M.subgroupOf N) :=
    Additive.ofMul ((⟨y, hyN⟩ : ↥N) : N ⧸ M.subgroupOf N)
  have hfix : ∀ m : ℕ, m < 3 → ∀ g : ↥H, (g : G) ∈ Lc L x m →
      op49 c.chief g v = v := by
    intro m hm g hg
    have hcomm : ⁅y, (g : G)⁆ ∈ M := by
      have hcov : m = i ∨ m = j ∨ m = k := by omega
      rcases hcov with hm_i | hm_j | hm_k
      · rw [hm_i] at hg
        have hVjk : V j ≤ Subgroup.normalizer (V k : Set G) :=
          direct_le_normalizer c (hVN j) (hVN k) (hMV k)
        exact direct_comm_mem_sup (Vj := V j) (Vk := V k) hVjk (hVN j) (hVN k) hNM
          (fun n hn => (Subgroup.commutator_le.mp (h3 j i hj hi (Ne.symm hij))) n hn g hg)
          (fun n hn => (Subgroup.commutator_le.mp (h3 k i hk hi (Ne.symm hik))) n hn g hg)
          y hyjk
      · rw [hm_j] at hg
        exact (Subgroup.commutator_le.mp (h3 i j hi hj hij)) y hyVi g hg
      · rw [hm_k] at hg
        exact (Subgroup.commutator_le.mp (h3 i k hi hk hik)) y hyVi g hg
    exact direct_op_fix c hyN hcomm
  have hzero : v = 0 :=
    c.eq_zero_of_fixed (hfix 0 (by norm_num)) (hfix 1 (by norm_num)) (hfix 2 (by norm_num))
  have hone : ((⟨y, hyN⟩ : ↥N) : N ⧸ M.subgroupOf N) = 1 := by
    have h0 := hzero
    change Additive.ofMul ((⟨y, hyN⟩ : ↥N) : N ⧸ M.subgroupOf N) = 0 at h0
    exact Additive.ofMul.injective h0
  exact Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff (N := M.subgroupOf N) (⟨y, hyN⟩ : ↥N)).mp hone)

include c in
theorem direct (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (h3 : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅V i, Lc L x j⁆ ≤ M) :
    V 0 ⊓ (V 1 ⊔ V 2) = M ∧ V 1 ⊓ (V 0 ⊔ V 2) = M ∧ V 2 ⊓ (V 0 ⊔ V 1) = M := by
  haveI hNorm : (M.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.chief.1.le).mpr
      ((c.NQ.trans (Q_le_H49 c.setup)).trans c.chief.2.2.1)
  haveI hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N) := c.chief.isElementaryAbelian
  refine ⟨direct_inf_sup_eq c V hV h3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num),
    direct_inf_sup_eq c V hV h3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num),
    direct_inf_sup_eq c V hV h3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)⟩

theorem irred_conjugate_sup (A B : Subgroup G) (g : G) :
    CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g := by
  simp only [CFSG.conjugate, Subgroup.map_sup]

theorem irred_conjugate_comm (A B : Subgroup G) (g : G) :
    CFSG.conjugate ⁅A, B⁆ g = ⁅CFSG.conjugate A g, CFSG.conjugate B g⁆ := by
  simp only [CFSG.conjugate, Subgroup.map_commutator]

theorem irred_conj_Lc (i j : ℕ) :
    CFSG.conjugate (Lc L x i) (x ^ j) = Lc L x (i + j) := by
  simp only [Lc]
  rw [conjugate_conjugate, ← pow_add]

theorem irred_conj_Lc_inv (i : ℕ) :
    CFSG.conjugate (Lc L x i) ((x ^ i)⁻¹) = Lc L x 0 := by
  simp only [Lc, conjugate_conjugate, mul_inv_cancel, conjugate_one, pow_zero]

theorem irred_conj_of_mem_normalizer {W : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) : CFSG.conjugate W g = W := by
  rw [CFSG.conjugate]
  exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := W) (g := g⁻¹)).mp
    ((Subgroup.normalizer (W : Set G)).inv_mem hg)

theorem irred_conjugate_mono {A B : Subgroup G} (g : G) (h : A ≤ B) :
    CFSG.conjugate A g ≤ CFSG.conjugate B g := by
  simp only [CFSG.conjugate]
  exact Subgroup.map_mono h

include c in
theorem irred_conj_N (g : G) (hg : g ∈ H) : CFSG.conjugate N g = N :=
  irred_conj_of_mem_normalizer (c.chief.2.1 hg)

include c in
theorem irred_conj_M (g : G) (hg : g ∈ H) : CFSG.conjugate M g = M :=
  irred_conj_of_mem_normalizer (c.chief.2.2.1 hg)

include c in
theorem irred_conj_Q (g : G) (hg : g ∈ H) : CFSG.conjugate Q g = Q :=
  irred_conj_of_mem_normalizer (H_le_normalizer_Q c.setup hg)

include c in
theorem irred_conj_V (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (i j : ℕ) : CFSG.conjugate (V i) (x ^ j) = V (i + j) := by
  have hN := c.irred_conj_N (x ^ j) (c.setup.X_le (c.pow_mem j))
  have hM := c.irred_conj_M (x ^ j) (c.setup.X_le (c.pow_mem j))
  rw [hV i, hV (i + j), irred_conjugate_sup, irred_conjugate_comm, hN, hM,
    irred_conj_Lc i j]

include c in
theorem irred_conj_V_inv (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (i : ℕ) : CFSG.conjugate (V i) ((x ^ i)⁻¹) = V 0 := by
  have hg : (x ^ i)⁻¹ ∈ H := c.setup.X_le (X.inv_mem (c.pow_mem i))
  have hN := c.irred_conj_N ((x ^ i)⁻¹) hg
  have hM := c.irred_conj_M ((x ^ i)⁻¹) hg
  rw [hV i, hV 0, irred_conjugate_sup, irred_conjugate_comm, hN, hM,
    irred_conj_Lc_inv i]

include c in
theorem irred_conj_V_one (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (i : ℕ) : CFSG.conjugate (V i) x = V (i + 1) := by
  simpa using c.irred_conj_V V hV i 1

theorem irred_conjugate_normalizer (Y : Subgroup G) (g : G) :
    CFSG.conjugate (Subgroup.normalizer (Y : Set G)) g =
      Subgroup.normalizer (CFSG.conjugate Y g : Set G) := by
  simp only [CFSG.conjugate]
  exact Subgroup.map_equiv_normalizer_eq Y (MulAut.conj g⁻¹)

theorem irred_mem_normalizer_of_conj_eq {W : Subgroup G} {g : G}
    (h : CFSG.conjugate W g = W) : g ∈ Subgroup.normalizer (W : Set G) := by
  have h' : g⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := W) (g := g⁻¹)).mpr h
  simpa using (Subgroup.normalizer (W : Set G)).inv_mem h'

include c in
theorem irred_V_le_N (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (j : ℕ) : V j ≤ N := by
  have hcomm : ⁅N, Lc L x j⁆ ≤ N := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp ((c.Lc_H j).trans c.chief.2.1)
  rw [hV j]
  exact sup_le hcomm c.chief.1.le

include c in
theorem irred_Q_le_normalizer {W : Subgroup G} (hMW : M ≤ W) (hWN : W ≤ N) :
    Q ≤ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.le_normalizer_iff_commutator_le_left]
  exact (Subgroup.commutator_mono hWN le_rfl).trans
    ((chief_q_trivial49 c.setup c.chief c.NQ).trans hMW)

include c in
theorem irred_normalizer_sup (V : ℕ → Subgroup G)
    (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) (i : ℕ) :
    Lc L x i ⊔ Q ≤ Subgroup.normalizer (V i : Set G) := by
  refine sup_le ?_ ?_
  · rw [hV i]
    have hLN : Lc L x i ≤ Subgroup.normalizer (N : Set G) := (c.Lc_H i).trans c.chief.2.1
    have hLM : Lc L x i ≤ Subgroup.normalizer (M : Set G) := (c.Lc_H i).trans c.chief.2.2.1
    have hLc : Lc L x i ≤ Subgroup.normalizer (⁅N, Lc L x i⁆ : Subgroup G) :=
      le_normalizer_commutator49 hLN Subgroup.le_normalizer
    exact (le_inf hLc hLM).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  · exact c.irred_Q_le_normalizer (by rw [hV i]; exact le_sup_right)
      (c.irred_V_le_N V hV i)

include c in
theorem irred_normalizer_M (i : ℕ) :
    Lc L x i ⊔ Q ≤ Subgroup.normalizer (M : Set G) :=
  sup_le ((c.Lc_H i).trans c.chief.2.2.1) ((Q_le_H49 c.setup).trans c.chief.2.2.1)

include c in
theorem irred_lt (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (h1 : N = V 0 ⊔ V 1 ⊔ V 2) (i : ℕ) (hi : i < 3) : M < V i := by
  refine lt_of_le_of_ne ?_ (fun hEq => ?_)
  · rw [hV i]; exact le_sup_right
  · have hstep : ∀ k : ℕ, V k = M → V (k + 1) = M := by
      intro k hk
      have h := c.irred_conj_V_one V hV k
      rw [hk, c.irred_conj_M x (c.setup.X_le c.xX)] at h
      exact h.symm
    have hadd3 : ∀ k : ℕ, V (k + 3) = V k := by
      intro k
      have h := c.irred_conj_V V hV k 3
      rw [c.x3, conjugate_one] at h
      exact h.symm
    have hVi : V i = M := hEq.symm
    interval_cases i
    · have h1M : V 1 = M := hstep 0 hVi
      have h2M : V 2 = M := hstep 1 h1M
      have hNM : N = M := by rw [h1, hVi, h1M, h2M]; simp
      exact absurd hNM (ne_of_gt c.chief.1)
    · have h2M : V 2 = M := hstep 1 hVi
      have h3M : V 3 = M := hstep 2 h2M
      have h0M : V 0 = M := by rwa [hadd3 0] at h3M
      have hNM : N = M := by rw [h1, h0M, hVi, h2M]; simp
      exact absurd hNM (ne_of_gt c.chief.1)
    · have h3M : V 3 = M := hstep 2 hVi
      have h4M : V 4 = M := hstep 3 h3M
      have h0M : V 0 = M := by rwa [hadd3 0] at h3M
      have h1M : V 1 = M := by rwa [hadd3 1] at h4M
      have hNM : N = M := by rw [h1, h0M, h1M, hVi]; simp
      exact absurd hNM (ne_of_gt c.chief.1)

include c in
theorem irred_inf_sup_le (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (h2 : V 0 ⊓ (V 1 ⊔ V 2) = M ∧ V 1 ⊓ (V 0 ⊔ V 2) = M ∧ V 2 ⊓ (V 0 ⊔ V 1) = M)
    {Y Y1 Y2 : Subgroup G} (hMY : M ≤ Y) (hYV : Y ≤ V 0)
    (hY1V : Y1 ≤ V 1) (hY2V : Y2 ≤ V 2) (hMY1 : M ≤ Y1) :
    V 0 ⊓ (Y ⊔ (Y1 ⊔ Y2)) ≤ Y := by
  have hV0N : V 0 ≤ N := c.irred_V_le_N V hV 0
  have hV1N : V 1 ≤ N := c.irred_V_le_N V hV 1
  have hV2N : V 2 ≤ N := c.irred_V_le_N V hV 2
  have hY12V : Y1 ⊔ Y2 ≤ V 1 ⊔ V 2 :=
    sup_le (hY1V.trans le_sup_left) (hY2V.trans le_sup_right)
  have hY12M : V 0 ⊓ (Y1 ⊔ Y2) ≤ M := by
    have h := inf_le_inf (le_rfl : V 0 ≤ V 0) hY12V
    rwa [h2.1] at h
  have hY12N : Y1 ⊔ Y2 ≤ N := hY12V.trans (sup_le hV1N hV2N)
  have hcomm : ⁅Y, Y1 ⊔ Y2⁆ ≤ Y1 ⊔ Y2 :=
    (Subgroup.commutator_mono (hYV.trans hV0N) hY12N).trans
      ((Subgroup.commutator_le.mpr fun a ha b hb => c.chief.2.2.2.2.1 a ha b hb).trans
        (hMY1.trans le_sup_left))
  have hYnorm : Y ≤ Subgroup.normalizer (Y1 ⊔ Y2 : Subgroup G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr hcomm
  rintro u ⟨huV0, huZ⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := (mem_sup_of_le_normalizer hYnorm).mp huZ
  have hwV0 : w ∈ V 0 := by
    have hmem : y⁻¹ * (y * w) ∈ V 0 := (V 0).mul_mem ((V 0).inv_mem (hYV hy)) huV0
    rwa [inv_mul_cancel_left] at hmem
  exact Y.mul_mem hy (hMY (hY12M ⟨hwV0, hw⟩))

include c in
theorem irred_Z_normalizer (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (h3 : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅V i, Lc L x j⁆ ≤ M)
    {Y Y1 Y2 Z : Subgroup G} (hZ : Z = Y ⊔ (Y1 ⊔ Y2))
    (hY1V : Y1 ≤ V 1) (hY2V : Y2 ≤ V 2) (hMY1 : M ≤ Y1) (hMY2 : M ≤ Y2)
    (hNorm : Lc L x 0 ⊔ Q ≤ Subgroup.normalizer (Y : Set G)) :
    Q ≤ Subgroup.normalizer (Z : Set G) ∧ Lc L x 0 ≤ Subgroup.normalizer (Z : Set G) := by
  have hV1N : V 1 ≤ N := c.irred_V_le_N V hV 1
  have hV2N : V 2 ≤ N := c.irred_V_le_N V hV 2
  have hQY : Q ≤ Subgroup.normalizer (Y : Set G) := le_sup_right.trans hNorm
  have hQY1 : Q ≤ Subgroup.normalizer (Y1 : Set G) :=
    c.irred_Q_le_normalizer hMY1 (hY1V.trans hV1N)
  have hQY2 : Q ≤ Subgroup.normalizer (Y2 : Set G) :=
    c.irred_Q_le_normalizer hMY2 (hY2V.trans hV2N)
  have hQZ : Q ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZ]
    exact (le_inf hQY ((le_inf hQY1 hQY2).trans
      (Subgroup.inf_normalizer_le_normalizer_sup Y1 Y2))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup Y (Y1 ⊔ Y2))
  have hLY : Lc L x 0 ≤ Subgroup.normalizer (Y : Set G) := le_sup_left.trans hNorm
  have hLY1 : Lc L x 0 ≤ Subgroup.normalizer (Y1 : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact (Subgroup.commutator_mono hY1V le_rfl).trans
      ((h3 1 0 (by norm_num) (by norm_num) (by norm_num)).trans hMY1)
  have hLY2 : Lc L x 0 ≤ Subgroup.normalizer (Y2 : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact (Subgroup.commutator_mono hY2V le_rfl).trans
      ((h3 2 0 (by norm_num) (by norm_num) (by norm_num)).trans hMY2)
  have hLZ : Lc L x 0 ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZ]
    exact (le_inf hLY ((le_inf hLY1 hLY2).trans
      (Subgroup.inf_normalizer_le_normalizer_sup Y1 Y2))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup Y (Y1 ⊔ Y2))
  exact ⟨hQZ, hLZ⟩

include c in
theorem irred_Z_invariant (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (h3 : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅V i, Lc L x j⁆ ≤ M)
    {Y Z : Subgroup G} (hZ : Z = Y ⊔ (CFSG.conjugate Y x ⊔ CFSG.conjugate Y (x ^ 2)))
    (hMY : M ≤ Y) (hYV : Y ≤ V 0)
    (hNorm : Lc L x 0 ⊔ Q ≤ Subgroup.normalizer (Y : Set G)) :
    H ≤ Subgroup.normalizer (Z : Set G) ∧ M ≤ Z ∧ Z ≤ N := by
  rw [hZ]
  set Y1 := CFSG.conjugate Y x with hY1def
  set Y2 := CFSG.conjugate Y (x ^ 2) with hY2def
  set Z' := Y ⊔ (Y1 ⊔ Y2) with hZ'def
  have hV0N : V 0 ≤ N := c.irred_V_le_N V hV 0
  have hV1N : V 1 ≤ N := c.irred_V_le_N V hV 1
  have hV2N : V 2 ≤ N := c.irred_V_le_N V hV 2
  have hY1V : Y1 ≤ V 1 := by
    rw [hY1def, ← c.irred_conj_V_one V hV 0]; exact irred_conjugate_mono x hYV
  have hY2V : Y2 ≤ V 2 := by
    rw [hY2def, ← c.irred_conj_V V hV 0 2]; exact irred_conjugate_mono (x ^ 2) hYV
  have hMY1 : M ≤ Y1 := by
    rw [hY1def]
    have h := irred_conjugate_mono x hMY
    rwa [c.irred_conj_M x (c.setup.X_le c.xX)] at h
  have hMY2 : M ≤ Y2 := by
    rw [hY2def]
    have h := irred_conjugate_mono (x ^ 2) hMY
    rwa [c.irred_conj_M (x ^ 2) (c.setup.X_le (c.pow_mem 2))] at h
  obtain ⟨hQZ, hLZ⟩ := c.irred_Z_normalizer V hV h3 hZ'def hY1V hY2V hMY1 hMY2 hNorm
  have hx1 : x * x = x ^ 2 := (pow_two x).symm
  have hx2 : x ^ 2 * x = 1 := by
    rw [(pow_succ x 2).symm, show (2 : ℕ) + 1 = 3 from by norm_num, c.x3]
  have hconjY1 : CFSG.conjugate Y1 x = Y2 := by
    rw [hY1def, hY2def, conjugate_conjugate, hx1]
  have hconjY2 : CFSG.conjugate Y2 x = Y := by
    rw [hY2def, conjugate_conjugate, hx2, conjugate_one]
  have hconjZ : CFSG.conjugate Z' x = Z' := by
    rw [hZ'def, irred_conjugate_sup, irred_conjugate_sup, ← hY1def, hconjY1, hconjY2]
    ac_rfl
  have hxZ : x ∈ Subgroup.normalizer (Z' : Set G) := irred_mem_normalizer_of_conj_eq hconjZ
  have hXZ : X ≤ Subgroup.normalizer (Z' : Set G) := by
    rw [c.hx]; exact Subgroup.zpowers_le.mpr hxZ
  have hL0 : L = Lc L x 0 := by rw [Lc, pow_zero, conjugate_one]
  have hHZ : H ≤ Subgroup.normalizer (Z' : Set G) := by
    rw [c.setup.H_eq]
    exact sup_le (sup_le hXZ (hL0.symm ▸ hLZ)) hQZ
  have hMZ : M ≤ Z' := by rw [hZ'def]; exact hMY.trans le_sup_left
  have hZNle : Z' ≤ N := by
    rw [hZ'def]
    exact sup_le (hYV.trans hV0N) (sup_le (hY1V.trans hV1N) (hY2V.trans hV2N))
  exact ⟨hHZ, hMZ, hZNle⟩

include c in
theorem irred_min (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (h1 : N = V 0 ⊔ V 1 ⊔ V 2)
    (h2 : V 0 ⊓ (V 1 ⊔ V 2) = M ∧ V 1 ⊓ (V 0 ⊔ V 2) = M ∧ V 2 ⊓ (V 0 ⊔ V 1) = M)
    (h3 : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅V i, Lc L x j⁆ ≤ M) :
    ∀ Y : Subgroup G, M ≤ Y → Y ≤ V 0 →
      Lc L x 0 ⊔ Q ≤ Subgroup.normalizer (Y : Set G) → Y = M ∨ Y = V 0 := by
  intro Y hMY hYV hNorm
  set Y1 := CFSG.conjugate Y x with hY1def
  set Y2 := CFSG.conjugate Y (x ^ 2) with hY2def
  set Z := Y ⊔ (Y1 ⊔ Y2) with hZdef
  have hZ' : Z = Y ⊔ (CFSG.conjugate Y x ⊔ CFSG.conjugate Y (x ^ 2)) := by
    rw [hZdef, hY1def, hY2def]
  obtain ⟨hHZ, hMZ, hZNle⟩ := c.irred_Z_invariant V hV h3 hZ' hMY hYV hNorm
  have hY1V : Y1 ≤ V 1 := by
    rw [hY1def, ← c.irred_conj_V_one V hV 0]; exact irred_conjugate_mono x hYV
  have hY2V : Y2 ≤ V 2 := by
    rw [hY2def, ← c.irred_conj_V V hV 0 2]; exact irred_conjugate_mono (x ^ 2) hYV
  have hMY1 : M ≤ Y1 := by
    rw [hY1def]
    have h := irred_conjugate_mono x hMY
    rwa [c.irred_conj_M x (c.setup.X_le c.xX)] at h
  rcases c.chief.2.2.2.2.2.2 Z hMZ hZNle hHZ with hZM | hZeqN
  · left
    have hYZ : Y ≤ Z := by rw [hZdef]; exact le_sup_left
    exact le_antisymm (hYZ.trans (le_of_eq hZM)) hMY
  · right
    have hV0Z : V 0 ≤ Z := (c.irred_V_le_N V hV 0).trans (le_of_eq hZeqN.symm)
    have hV0Y : V 0 ≤ Y := by
      have h := c.irred_inf_sup_le V hV h2 hMY hYV hY1V hY2V hMY1
      rw [← hZdef, inf_eq_left.mpr hV0Z] at h
      exact h
    exact le_antisymm hYV hV0Y

include c in
theorem irred_min_rotate (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M) (i : ℕ)
    (hmin0 : ∀ Y : Subgroup G, M ≤ Y → Y ≤ V 0 →
      Lc L x 0 ⊔ Q ≤ Subgroup.normalizer (Y : Set G) → Y = M ∨ Y = V 0) :
    ∀ Y : Subgroup G, M ≤ Y → Y ≤ V i →
      Lc L x i ⊔ Q ≤ Subgroup.normalizer (Y : Set G) → Y = M ∨ Y = V i := by
  intro Y hMY hYV hNorm
  have hgH : (x ^ i)⁻¹ ∈ H := c.setup.X_le (X.inv_mem (c.pow_mem i))
  have hM' : M ≤ CFSG.conjugate Y ((x ^ i)⁻¹) := by
    have h := irred_conjugate_mono ((x ^ i)⁻¹) hMY
    rwa [c.irred_conj_M ((x ^ i)⁻¹) hgH] at h
  have hY'V : CFSG.conjugate Y ((x ^ i)⁻¹) ≤ V 0 := by
    have h := irred_conjugate_mono ((x ^ i)⁻¹) hYV
    rwa [c.irred_conj_V_inv V hV i] at h
  have hNorm' : Lc L x 0 ⊔ Q ≤
      Subgroup.normalizer (CFSG.conjugate Y ((x ^ i)⁻¹) : Set G) := by
    have h := irred_conjugate_mono ((x ^ i)⁻¹) hNorm
    rw [irred_conjugate_sup, irred_conj_Lc_inv, c.irred_conj_Q ((x ^ i)⁻¹) hgH,
      irred_conjugate_normalizer] at h
    exact h
  have hYinv : CFSG.conjugate (CFSG.conjugate Y ((x ^ i)⁻¹)) (x ^ i) = Y := by
    rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]
  rcases hmin0 (CFSG.conjugate Y ((x ^ i)⁻¹)) hM' hY'V hNorm' with h | h
  · left
    rw [← hYinv, h, c.irred_conj_M (x ^ i) (c.setup.X_le (c.pow_mem i))]
  · right
    rw [← hYinv, h, c.irred_conj_V V hV 0 i, Nat.zero_add]

include c in
theorem irred (V : ℕ → Subgroup G) (hV : ∀ i, V i = ⁅N, Lc L x i⁆ ⊔ M)
    (h1 : N = V 0 ⊔ V 1 ⊔ V 2)
    (h2 : V 0 ⊓ (V 1 ⊔ V 2) = M ∧ V 1 ⊓ (V 0 ⊔ V 2) = M ∧ V 2 ⊓ (V 0 ⊔ V 1) = M)
    (h3 : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅V i, Lc L x j⁆ ≤ M) :
    ∀ i : ℕ, i < 3 → HChief (Lc L x i ⊔ Q) (V i) M := by
  intro i hi
  refine ⟨c.irred_lt V hV h1 i hi, c.irred_normalizer_sup V hV i, c.irred_normalizer_M i,
    ?_, ?_, ?_, ?_⟩
  · intro u hu v hv
    exact c.chief.2.2.2.1 u (c.irred_V_le_N V hV i hu) v hv
  · intro u hu v hv
    exact c.chief.2.2.2.2.1 u (c.irred_V_le_N V hV i hu) v (c.irred_V_le_N V hV i hv)
  · intro u hu
    exact c.chief.2.2.2.2.2.1 u (c.irred_V_le_N V hV i hu)
  · exact c.irred_min_rotate V hV i (c.irred_min V hV h1 h2 h3)

end Ctx49

end Context

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
