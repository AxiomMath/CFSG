module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBML
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin CFSG.Open

set_option maxRecDepth 100000

@[expose] def dGenC : List (List ℕ) := [[2, 5, 4, 1, 7, 6, 3, 0, 8, 9, 10, 11, 12, 13, 14, 15], [1, 0, 3, 2, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15], [0, 1, 2, 3, 4, 5, 6, 7, 10, 13, 12, 9, 15, 14, 11, 8], [0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 14, 15, 12, 13]]

@[expose] def dTree : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 2), (2, 3), (3, 2), (3, 3), (4, 2), (5, 0), (5, 1), (5, 2), (5, 3), (6, 2), (6, 3), (7, 2), (7, 3), (8, 2), (9, 2), (9, 3), (10, 2), (10, 3), (11, 2), (12, 2), (12, 3), (15, 2), (15, 3), (16, 2), (16, 3), (17, 2), (17, 3), (18, 2), (19, 2), (19, 3), (20, 2), (21, 2), (21, 3), (24, 2), (24, 3), (25, 2), (26, 2), (26, 3), (31, 2), (31, 3), (32, 2), (33, 2), (33, 3), (34, 2), (35, 2), (35, 3), (38, 2), (38, 3), (43, 2), (43, 3), (48, 2), (48, 3), (51, 2), (51, 3)]

@[expose] def dTbl : List (List ℕ) := [[1, 2, 3, 4], [5, 6, 7, 8], [9, 0, 10, 11], [7, 10, 12, 13], [8, 11, 14, 0], [15, 16, 17, 18], [2, 1, 19, 20], [17, 19, 21, 22], [18, 20, 23, 1], [16, 15, 24, 25], [24, 3, 26, 27], [25, 4, 28, 2], [21, 26, 29, 30], [22, 27, 4, 3], [23, 28, 30, 29], [0, 9, 31, 32], [6, 5, 33, 34], [31, 33, 35, 36], [32, 34, 37, 5], [10, 7, 38, 39], [11, 8, 40, 6], [35, 38, 41, 42], [36, 39, 8, 7], [37, 40, 42, 41], [33, 31, 43, 44], [34, 32, 45, 9], [43, 12, 46, 47], [44, 13, 11, 10], [45, 14, 47, 46], [41, 46, 0, 14], [42, 47, 13, 12], [3, 24, 48, 49], [4, 25, 50, 15], [19, 17, 51, 52], [20, 18, 53, 16], [48, 51, 54, 55], [49, 52, 18, 17], [50, 53, 55, 54], [26, 21, 56, 57], [27, 22, 20, 19], [28, 23, 57, 56], [54, 56, 1, 23], [55, 57, 22, 21], [51, 48, 58, 59], [52, 49, 25, 24], [53, 50, 59, 58], [58, 29, 2, 28], [59, 30, 27, 26], [12, 43, 60, 61], [13, 44, 32, 31], [14, 45, 61, 60], [38, 35, 62, 63], [39, 36, 34, 33], [40, 37, 63, 62], [60, 62, 5, 37], [61, 63, 36, 35], [46, 41, 6, 40], [47, 42, 39, 38], [62, 60, 9, 45], [63, 61, 44, 43], [29, 58, 15, 50], [30, 59, 49, 48], [56, 54, 16, 53], [57, 55, 52, 51]]

@[expose] def dLit : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [2, 5, 4, 1, 7, 6, 3, 0, 8, 9, 10, 11, 12, 13, 14, 15], [1, 0, 3, 2, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15], [0, 1, 2, 3, 4, 5, 6, 7, 10, 13, 12, 9, 15, 14, 11, 8], [0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 14, 15, 12, 13], [4, 6, 7, 5, 0, 3, 1, 2, 8, 9, 10, 11, 12, 13, 14, 15], [5, 2, 1, 4, 3, 0, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15], [2, 5, 4, 1, 7, 6, 3, 0, 10, 13, 12, 9, 15, 14, 11, 8], [2, 5, 4, 1, 7, 6, 3, 0, 9, 8, 11, 10, 14, 15, 12, 13], [3, 7, 6, 0, 5, 4, 2, 1, 8, 9, 10, 11, 12, 13, 14, 15], [1, 0, 3, 2, 6, 7, 4, 5, 10, 13, 12, 9, 15, 14, 11, 8], [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10, 14, 15, 12, 13], [0, 1, 2, 3, 4, 5, 6, 7, 12, 14, 15, 13, 8, 11, 9, 10], [0, 1, 2, 3, 4, 5, 6, 7, 13, 10, 9, 12, 11, 8, 15, 14], [0, 1, 2, 3, 4, 5, 6, 7, 11, 15, 14, 8, 13, 12, 10, 9], [7, 3, 0, 6, 2, 1, 5, 4, 8, 9, 10, 11, 12, 13, 14, 15], [6, 4, 5, 7, 1, 2, 0, 3, 8, 9, 10, 11, 12, 13, 14, 15], [4, 6, 7, 5, 0, 3, 1, 2, 10, 13, 12, 9, 15, 14, 11, 8], [4, 6, 7, 5, 0, 3, 1, 2, 9, 8, 11, 10, 14, 15, 12, 13], [5, 2, 1, 4, 3, 0, 7, 6, 10, 13, 12, 9, 15, 14, 11, 8], [5, 2, 1, 4, 3, 0, 7, 6, 9, 8, 11, 10, 14, 15, 12, 13], [2, 5, 4, 1, 7, 6, 3, 0, 12, 14, 15, 13, 8, 11, 9, 10], [2, 5, 4, 1, 7, 6, 3, 0, 13, 10, 9, 12, 11, 8, 15, 14], [2, 5, 4, 1, 7, 6, 3, 0, 11, 15, 14, 8, 13, 12, 10, 9], [3, 7, 6, 0, 5, 4, 2, 1, 10, 13, 12, 9, 15, 14, 11, 8], [3, 7, 6, 0, 5, 4, 2, 1, 9, 8, 11, 10, 14, 15, 12, 13], [1, 0, 3, 2, 6, 7, 4, 5, 12, 14, 15, 13, 8, 11, 9, 10], [1, 0, 3, 2, 6, 7, 4, 5, 13, 10, 9, 12, 11, 8, 15, 14], [1, 0, 3, 2, 6, 7, 4, 5, 11, 15, 14, 8, 13, 12, 10, 9], [0, 1, 2, 3, 4, 5, 6, 7, 15, 11, 8, 14, 10, 9, 13, 12], [0, 1, 2, 3, 4, 5, 6, 7, 14, 12, 13, 15, 9, 10, 8, 11], [7, 3, 0, 6, 2, 1, 5, 4, 10, 13, 12, 9, 15, 14, 11, 8], [7, 3, 0, 6, 2, 1, 5, 4, 9, 8, 11, 10, 14, 15, 12, 13], [6, 4, 5, 7, 1, 2, 0, 3, 10, 13, 12, 9, 15, 14, 11, 8], [6, 4, 5, 7, 1, 2, 0, 3, 9, 8, 11, 10, 14, 15, 12, 13], [4, 6, 7, 5, 0, 3, 1, 2, 12, 14, 15, 13, 8, 11, 9, 10], [4, 6, 7, 5, 0, 3, 1, 2, 13, 10, 9, 12, 11, 8, 15, 14], [4, 6, 7, 5, 0, 3, 1, 2, 11, 15, 14, 8, 13, 12, 10, 9], [5, 2, 1, 4, 3, 0, 7, 6, 12, 14, 15, 13, 8, 11, 9, 10], [5, 2, 1, 4, 3, 0, 7, 6, 13, 10, 9, 12, 11, 8, 15, 14], [5, 2, 1, 4, 3, 0, 7, 6, 11, 15, 14, 8, 13, 12, 10, 9], [2, 5, 4, 1, 7, 6, 3, 0, 15, 11, 8, 14, 10, 9, 13, 12], [2, 5, 4, 1, 7, 6, 3, 0, 14, 12, 13, 15, 9, 10, 8, 11], [3, 7, 6, 0, 5, 4, 2, 1, 12, 14, 15, 13, 8, 11, 9, 10], [3, 7, 6, 0, 5, 4, 2, 1, 13, 10, 9, 12, 11, 8, 15, 14], [3, 7, 6, 0, 5, 4, 2, 1, 11, 15, 14, 8, 13, 12, 10, 9], [1, 0, 3, 2, 6, 7, 4, 5, 15, 11, 8, 14, 10, 9, 13, 12], [1, 0, 3, 2, 6, 7, 4, 5, 14, 12, 13, 15, 9, 10, 8, 11], [7, 3, 0, 6, 2, 1, 5, 4, 12, 14, 15, 13, 8, 11, 9, 10], [7, 3, 0, 6, 2, 1, 5, 4, 13, 10, 9, 12, 11, 8, 15, 14], [7, 3, 0, 6, 2, 1, 5, 4, 11, 15, 14, 8, 13, 12, 10, 9], [6, 4, 5, 7, 1, 2, 0, 3, 12, 14, 15, 13, 8, 11, 9, 10], [6, 4, 5, 7, 1, 2, 0, 3, 13, 10, 9, 12, 11, 8, 15, 14], [6, 4, 5, 7, 1, 2, 0, 3, 11, 15, 14, 8, 13, 12, 10, 9], [4, 6, 7, 5, 0, 3, 1, 2, 15, 11, 8, 14, 10, 9, 13, 12], [4, 6, 7, 5, 0, 3, 1, 2, 14, 12, 13, 15, 9, 10, 8, 11], [5, 2, 1, 4, 3, 0, 7, 6, 15, 11, 8, 14, 10, 9, 13, 12], [5, 2, 1, 4, 3, 0, 7, 6, 14, 12, 13, 15, 9, 10, 8, 11], [3, 7, 6, 0, 5, 4, 2, 1, 15, 11, 8, 14, 10, 9, 13, 12], [3, 7, 6, 0, 5, 4, 2, 1, 14, 12, 13, 15, 9, 10, 8, 11], [7, 3, 0, 6, 2, 1, 5, 4, 15, 11, 8, 14, 10, 9, 13, 12], [7, 3, 0, 6, 2, 1, 5, 4, 14, 12, 13, 15, 9, 10, 8, 11], [6, 4, 5, 7, 1, 2, 0, 3, 15, 11, 8, 14, 10, 9, 13, 12], [6, 4, 5, 7, 1, 2, 0, 3, 14, 12, 13, 15, 9, 10, 8, 11]]

@[expose] def D88 : Subgroup P16 := closure {g | g ∈ [u1, v1, u2, v2]}

theorem d_gens : [u1, v1, u2, v2].map code = dGenC := by decide

theorem d_build : dLit = Core.buildCodes cid dGenC dTree := by decide +kernel

theorem d_tbl : Core.tblCheckC cid dGenC dLit dTbl = true := by decide +kernel

theorem d_nodup : dLit.Nodup := by decide +kernel

theorem d_length : dLit.length = 64 := by decide +kernel

theorem d_desc : LDesc D88 dLit := ldesc_of_closure d_gens d_build d_tbl

theorem card_D88 : Nat.card D88 = 64 := by rw [d_desc.card d_nodup, d_length]

theorem u1_mem : u1 ∈ L01 := (l1_desc.mem u1).2 (by decide +kernel)

theorem v1_mem : v1 ∈ L01 := (l1_desc.mem v1).2 (by decide +kernel)

theorem u2_mem : u2 ∈ L02 := (l2_desc.mem u2).2 (by decide +kernel)

theorem v2_mem : v2 ∈ L02 := (l2_desc.mem v2).2 (by decide +kernel)

theorem D88_le_L : D88 ≤ L01 ⊔ L02 := by
  rw [D88, closure_le]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact mem_sup_left u1_mem
  · exact mem_sup_left v1_mem
  · exact mem_sup_right u2_mem
  · exact mem_sup_right v2_mem

variable (i : Fin 4)

theorem mem_GB_of_mem {g : P16} (hg : g ∈ [a1, b1, a2, b2] ++ bGens i) : g ∈ GB i :=
  subset_closure hg

theorem L01_le_GB : L01 ≤ GB i := by
  rw [L01, closure_le]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
  rcases hg with rfl | rfl <;> exact mem_GB_of_mem i (by simp)

theorem L02_le_GB : L02 ≤ GB i := by
  rw [L02, closure_le]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
  rcases hg with rfl | rfl <;> exact mem_GB_of_mem i (by simp)

theorem TB_le_GB : TB i ≤ GB i := by
  rw [TB, closure_le]
  intro g hg
  simp only [List.mem_append, Set.mem_setOf_eq] at hg
  rcases hg with hg | hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact L01_le_GB i u1_mem
    · exact L01_le_GB i v1_mem
    · exact L02_le_GB i u2_mem
    · exact L02_le_GB i v2_mem
  · exact mem_GB_of_mem i (List.mem_append_right _ hg)

theorem D88_le_TB : D88 ≤ TB i := by
  rw [D88, closure_le]
  intro g hg
  exact subset_closure (List.mem_append_left _ hg)

theorem GB_le_sup : GB i ≤ (L01 ⊔ L02) ⊔ TB i := by
  rw [GB, closure_le]
  intro g hg
  simp only [List.mem_append, Set.mem_setOf_eq] at hg
  rcases hg with hg | hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_left (subset_closure (by simp)))
    · exact mem_sup_left (mem_sup_left (subset_closure (by simp)))
    · exact mem_sup_left (mem_sup_right (subset_closure (by simp)))
    · exact mem_sup_left (mem_sup_right (subset_closure (by simp)))
  · exact mem_sup_right (subset_closure (List.mem_append_right _ hg))

theorem mem_normalizer_of_map_le {H : Subgroup P16} {g : P16}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set P16) := by
  have hc : Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
    card_map_of_injective (MulAut.conj g).injective
  have heq : H.map (MulAut.conj g).toMonoidHom = H := eq_of_le_of_card_ge h hc.ge
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by simpa using hyx
    rwa [← this]

theorem L_eq_closure : L01 ⊔ L02 = closure {g | g ∈ [a1, b1, a2, b2]} := by
  rw [L01, L02, ← Subgroup.closure_union]
  congr 1
  ext g
  simp [or_assoc]

@[expose] def GNormChk (gc : List (List ℕ)) : Bool :=
  gc.all fun g => [code a1, code b1, code a2, code b2].all fun x =>
    l1Lit.contains (cconj g x) || l2Lit.contains (cconj g x)

theorem GB_le_normalizer (h : GNormChk (([a1, b1, a2, b2] ++ bGens i).map code) = true) :
    GB i ≤ normalizer ((L01 ⊔ L02 : Subgroup P16) : Set P16) := by
  rw [GB, closure_le]
  intro g hg
  apply mem_normalizer_of_map_le
  rw [L_eq_closure, MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, hx, rfl⟩
  simp only [GNormChk, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Bool.or_eq_true, List.contains_iff_mem] at h
  have h1 := h g hg
  have hx' : code x ∈ [code a1, code b1, code a2, code b2] := by
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp
  rcases h1 (code x) hx' with h2 | h2
  · rw [← code_conj] at h2
    rw [← L_eq_closure]
    exact mem_sup_left ((l1_desc.mem _).2 h2)
  · rw [← code_conj] at h2
    rw [← L_eq_closure]
    exact mem_sup_right ((l2_desc.mem _).2 h2)

abbrev L1b : Subgroup ↥(GB i) := L01.subgroupOf (GB i)

abbrev L2b : Subgroup ↥(GB i) := L02.subgroupOf (GB i)

abbrev Tb : Subgroup ↥(GB i) := (TB i).subgroupOf (GB i)

theorem normal_L (h : GNormChk (([a1, b1, a2, b2] ++ bGens i).map code) = true) :
    (L1b i ⊔ L2b i).Normal := by
  rw [L1b, L2b, ← subgroupOf_sup (L01_le_GB i) (L02_le_GB i)]
  constructor
  intro n hn g
  rw [mem_subgroupOf] at hn ⊢
  exact (mem_normalizer_iff.1 (GB_le_normalizer i h g.2) n).1 hn

theorem cent_L : centralizer ((L1b i ⊔ L2b i : Subgroup ↥(GB i)) : Set ↥(GB i)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  apply Subtype.ext
  apply eq_one_of_commute
  · intro x hx
    have := mem_centralizer_iff.1 hz ⟨x, L01_le_GB i hx⟩
      (mem_sup_left (show (⟨x, L01_le_GB i hx⟩ : ↥(GB i)) ∈ L1b i from hx))
    exact (congrArg Subtype.val this).symm
  · intro x hx
    have := mem_centralizer_iff.1 hz ⟨x, L02_le_GB i hx⟩
      (mem_sup_right (show (⟨x, L02_le_GB i hx⟩ : ↥(GB i)) ∈ L2b i from hx))
    exact (congrArg Subtype.val this).symm

theorem three_L : ∃ y ∈ L1b i, orderOf y = 3 := by
  obtain ⟨y, hy, hy3⟩ := exists_three_L01
  exact ⟨⟨y, L01_le_GB i hy⟩, hy, by rw [Subgroup.orderOf_mk, hy3]⟩

theorem isSimpleGroup_L1b : IsSimpleGroup ↥(L1b i) := by
  have := isSimpleGroup_L01
  exact (subgroupOfEquivOfLe (L01_le_GB i)).isSimpleGroup

theorem isSimpleGroup_L2b : IsSimpleGroup ↥(L2b i) := by
  have := isSimpleGroup_L02
  exact (subgroupOfEquivOfLe (L02_le_GB i)).isSimpleGroup

theorem map_conj_subgroupOf {H K : Subgroup P16} {g : P16} (hg : g ∈ K) :
    (H.subgroupOf K).map (MulAut.conj (⟨g, hg⟩ : ↥K)).toMonoidHom =
      (H.map (MulAut.conj g).toMonoidHom).subgroupOf K := by
  ext x
  simp only [mem_map, mem_subgroupOf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨y, ?_⟩, hy, Subtype.ext hyx⟩
    have : y = g⁻¹ * x * g := by rw [← hyx]; group
    rw [this]
    exact K.mul_mem (K.mul_mem (K.inv_mem hg) x.2) hg

theorem commute_L1b_L2b {x y : ↥(GB i)} (hx : x ∈ L1b i) (hy : y ∈ L2b i) : x * y = y * x :=
  Subtype.ext (commute_L01_L02 hx hy)

theorem le_normalizer_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ k ∈ K, ∀ x ∈ H, k * x = x * k) : K ≤ normalizer (H : Set G) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : k * x * k⁻¹ = x := by rw [h k hk x hx, mul_inv_cancel_right]
    rw [this]
    exact hx
  · intro hx
    have h2 := h k⁻¹ (inv_mem hk) _ hx
    have e : x = k⁻¹ * (k * x * k⁻¹) * k := by group
    have e2 : k⁻¹ * (k * x * k⁻¹) * k = k * x * k⁻¹ := by rw [h2]; group
    rw [e, e2]
    exact hx

theorem commutator_le_inf_of_le_normalizer {G : Type*} [Group G] {M H : Subgroup G} [M.Normal]
    (h : M ≤ normalizer (H : Set G)) : ⁅M, H⁆ ≤ M ⊓ H := by
  refine le_inf (commutator_le_left M H) ?_
  rw [commutator_le]
  intro m hm x hx
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.1 (h hm) x).1 hx) (inv_mem hx)

theorem le_of_simple {G : Type*} [Group G] {M H : Subgroup G} [hM : M.Normal]
    (hs : IsSimpleGroup ↥H) (hne : M ⊓ H ≠ ⊥) : H ≤ M := by
  have := hM.subgroupOf H
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf H) with h | h
  · exfalso
    apply hne
    rw [subgroupOf_eq_bot] at h
    exact disjoint_iff.1 h
  · rwa [subgroupOf_eq_top] at h

theorem map_conj_le_of_normal {G : Type*} [Group G] {K H : Subgroup G} (hK : K.Normal)
    (hHK : H ≤ K) (g : G) : H.map (MulAut.conj g).toMonoidHom ≤ K := by
  rintro _ ⟨y, hy, rfl⟩
  exact hK.conj_mem y (hHK hy) g

theorem map_conj_inv_map_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [map_map]
  have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [this, map_id]

theorem le_of_normal_L (h : GNormChk (([a1, b1, a2, b2] ++ bGens i).map code) = true)
    {w : P16} (hw : w ∈ GB i) (hwL : L02 = L01.map (MulAut.conj w).toMonoidHom) :
    ∀ K : Subgroup ↥(GB i), K.Normal → (∃ x ∈ K, orderOf x = 2) → L1b i ⊔ L2b i ≤ K := by
  intro K hK ⟨x, hxK, hx2⟩
  have hLn := normal_L i h
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx2
  set wX : ↥(GB i) := ⟨w, hw⟩
  have h12 : L2b i = (L1b i).map (MulAut.conj wX).toMonoidHom := by
    rw [map_conj_subgroupOf, ← hwL]
  have h21 : L1b i = (L2b i).map (MulAut.conj wX⁻¹).toMonoidHom := by
    rw [h12, map_conj_inv_map_conj]
  set M := K ⊓ (L1b i ⊔ L2b i) with hMdef
  have hMn : M.Normal := inferInstance
  have hMK : M ≤ K := inf_le_left
  have hML : M ≤ L1b i ⊔ L2b i := inf_le_right
  have hMne : M ≠ ⊥ := by
    intro hbot
    have h1 : ⁅K, L1b i ⊔ L2b i⁆ = ⊥ := eq_bot_iff.2 (hbot ▸ commutator_le_inf K _)
    rw [commutator_eq_bot_iff_le_centralizer, cent_L] at h1
    exact hx1 ((mem_bot).1 (h1 hxK))
  have hN1 : L1b i ⊔ L2b i ≤ normalizer (L1b i : Set ↥(GB i)) :=
    sup_le le_normalizer (le_normalizer_of_commute fun k hk y hy => (commute_L1b_L2b i hy hk).symm)
  have hN2 : L1b i ⊔ L2b i ≤ normalizer (L2b i : Set ↥(GB i)) :=
    sup_le (le_normalizer_of_commute fun k hk y hy => commute_L1b_L2b i hk hy) le_normalizer
  have hs1 := isSimpleGroup_L1b i
  have hs2 := isSimpleGroup_L2b i
  by_cases h1 : M ⊓ L1b i = ⊥
  · by_cases h2 : M ⊓ L2b i = ⊥
    · exfalso
      have c1 : ⁅M, L1b i⁆ = ⊥ :=
        eq_bot_iff.2 (h1 ▸ commutator_le_inf_of_le_normalizer (hML.trans hN1))
      have c2 : ⁅M, L2b i⁆ = ⊥ :=
        eq_bot_iff.2 (h2 ▸ commutator_le_inf_of_le_normalizer (hML.trans hN2))
      rw [commutator_eq_bot_iff_le_centralizer] at c1 c2
      have hc : M ≤ centralizer ((L1b i ⊔ L2b i : Subgroup ↥(GB i)) : Set ↥(GB i)) := by
        rw [le_centralizer_iff]
        exact sup_le (le_centralizer_iff.1 c1) (le_centralizer_iff.1 c2)
      rw [cent_L] at hc
      exact hMne (eq_bot_iff.2 hc)
    · have hL2 : L2b i ≤ K := (le_of_simple hs2 h2).trans hMK
      have hL1 : L1b i ≤ K := h21 ▸ map_conj_le_of_normal hK hL2 _
      exact sup_le hL1 hL2
  · have hL1 : L1b i ≤ K := (le_of_simple hs1 h1).trans hMK
    have hL2 : L2b i ≤ K := h12 ▸ map_conj_le_of_normal hK hL1 _
    exact sup_le hL1 hL2

theorem card_L : Nat.card (L01 ⊔ L02 : Subgroup P16) = 28224 := by
  set Y := L01 ⊔ L02
  set N := L02.subgroupOf Y
  set H := L01.subgroupOf Y
  have hNn : N.Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    have hg : (g : P16) ∈ normalizer (L02 : Set P16) :=
      sup_le (le_normalizer_of_commute fun k hk y hy => commute_L01_L02 hk hy) le_normalizer g.2
    exact (mem_normalizer_iff.1 hg n).1 hn
  have htop : H ⊔ N = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hinf : N ⊓ H = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx2, hx1⟩
    rw [mem_bot]
    apply Subtype.ext
    have : (x : P16) ∈ L01 ⊓ L02 := ⟨hx1, hx2⟩
    rw [L01_inf_L02, mem_bot] at this
    exact this
  have h1 : N.index = Nat.card H := by
    rw [← relIndex_top_right, ← htop, relIndex_sup_right]
    have := relIndex_mul_card N H
    rw [hinf, card_bot, mul_one] at this
    exact this
  have h2 := N.index_mul_card
  rw [h1, show Nat.card H = 168 by
      rw [Nat.card_congr (subgroupOfEquivOfLe (le_sup_left : L01 ≤ Y)).toEquiv, card_L01],
    show Nat.card N = 168 by
      rw [Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : L02 ≤ Y)).toEquiv,
        l2_desc.card l2_nodup, l2_length]] at h2
  rw [← h2]


theorem card_subgroupOf {H : Subgroup P16} (h : H ≤ GB i) : Nat.card (H.subgroupOf (GB i)) = Nat.card H :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

theorem L1b_sup_L2b : L1b i ⊔ L2b i = (L01 ⊔ L02).subgroupOf (GB i) :=
  (subgroupOf_sup (L01_le_GB i) (L02_le_GB i)).symm

theorem sylow_T (h : GNormChk (([a1, b1, a2, b2] ++ bGens i).map code) = true) {n : ℕ}
    (hT : Nat.card (TB i) = 2 ^ n) : IsSylowIn 2 (Tb i) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lx := L1b i ⊔ L2b i with hLx
  have hLn : Lx.Normal := normal_L i h
  have hTcard : Nat.card (Tb i) = 2 ^ n := by rw [Tb, card_subgroupOf i (TB_le_GB i), hT]
  have hLcard : Nat.card Lx = 28224 := by
    rw [hLx, L1b_sup_L2b, card_subgroupOf i (sup_le (L01_le_GB i) (L02_le_GB i)), card_L]
  have htop : Tb i ⊔ Lx = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ ((L01 ⊔ L02) ⊔ TB i).subgroupOf (GB i) := GB_le_sup i x.2
    rwa [subgroupOf_sup (sup_le (L01_le_GB i) (L02_le_GB i)) (TB_le_GB i), ← L1b_sup_L2b,
      sup_comm] at hx
  have hp : IsPGroup 2 (Tb i) := IsPGroup.of_card hTcard
  have hD : Nat.card (Lx ⊓ Tb i : Subgroup ↥(GB i)) = 64 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hp.to_inf_right (H := Lx))
    have hdvd : Nat.card (Lx ⊓ Tb i : Subgroup ↥(GB i)) ∣ 28224 := hLcard ▸ card_dvd_of_le inf_le_left
    have hDle : D88.subgroupOf (GB i) ≤ Lx ⊓ Tb i := by
      intro x hx
      refine ⟨?_, D88_le_TB i hx⟩
      rw [hLx, L1b_sup_L2b]
      exact D88_le_L hx
    have hle : 64 ≤ Nat.card (Lx ⊓ Tb i : Subgroup ↥(GB i)) := by
      have := card_le_of_le hDle
      rwa [card_subgroupOf i ((D88_le_TB i).trans (TB_le_GB i)), card_D88] at this
    rw [hk] at hdvd hle ⊢
    have hcop : Nat.Coprime (2 ^ k) 441 := Nat.Coprime.pow_left k (by norm_num)
    have h64 : 2 ^ k ∣ 64 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h64) hle
  have hidx : (Tb i).index = 441 := by
    have e1 := (Tb i).index_mul_card
    have e2 := Lx.index_mul_card
    have e3 : Lx.index = Lx.relIndex (Tb i) := by
      rw [← relIndex_top_right, ← htop, relIndex_sup_right]
    have e4 := relIndex_mul_card Lx (Tb i)
    rw [hD, hTcard] at e4
    rw [e3, hLcard] at e2
    rw [hTcard, ← e2, ← e4] at e1
    have hpos : 0 < Lx.relIndex (Tb i) * 64 := by
      rw [e4]
      positivity
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [e1]; ring)
  refine ⟨le_top, hp, ?_⟩
  rw [relIndex_top_right, hidx]
  decide

theorem mem_Tb_iff {tLit : List (List ℕ)} (hT : LDesc (TB i) tLit) (x : ↥(GB i)) :
    x ∈ Tb i ↔ code x.1 ∈ tLit := by
  rw [Tb, mem_subgroupOf]
  exact hT.mem x.1

theorem exists_Tb {tLit : List (List ℕ)} (hT : LDesc (TB i) tLit) {c : List ℕ} (hc : c ∈ tLit) :
    ∃ x : ↥(GB i), x ∈ Tb i ∧ code x.1 = c := by
  obtain ⟨σ, hσ, rfl⟩ := hT.surj c hc
  exact ⟨⟨σ, TB_le_GB i hσ⟩, hσ, rfl⟩

theorem exists_L1b {c : List ℕ} (hc : c ∈ l1Lit) : ∃ x : ↥(GB i), x ∈ L1b i ∧ code x.1 = c := by
  obtain ⟨σ, hσ, rfl⟩ := l1_desc.surj c hc
  exact ⟨⟨σ, L01_le_GB i hσ⟩, hσ, rfl⟩

theorem exists_L2b {c : List ℕ} (hc : c ∈ l2Lit) : ∃ x : ↥(GB i), x ∈ L2b i ∧ code x.1 = c := by
  obtain ⟨σ, hσ, rfl⟩ := l2_desc.surj c hc
  exact ⟨⟨σ, L02_le_GB i hσ⟩, hσ, rfl⟩

theorem exists_GB {tLit : List (List ℕ)} (hT : LDesc (TB i) tLit) {c1 c2 c3 : List ℕ}
    (h1 : c1 ∈ l1Lit) (h2 : c2 ∈ l2Lit) (h3 : c3 ∈ tLit) :
    ∃ x : ↥(GB i), code x.1 = Core.cmul (Core.cmul c1 c2) c3 := by
  obtain ⟨x1, -, e1⟩ := exists_L1b i h1
  obtain ⟨x2, -, e2⟩ := exists_L2b i h2
  obtain ⟨x3, -, e3⟩ := exists_Tb i hT h3
  exact ⟨x1 * x2 * x3, by rw [Subgroup.coe_mul, Subgroup.coe_mul, code_mul, code_mul, e1, e2, e3]⟩

@[expose] def PairChk (tLit : List (List ℕ))
    (ws : List ((List ℕ × List ℕ × List ℕ) × (List ℕ × List ℕ × List ℕ))) : Bool :=
  tLit.length == ws.length &&
  (tLit.zip ws).all fun p => !(cinvol p.1) ||
    (l1Lit.contains p.2.1.1 && l2Lit.contains p.2.1.2.1 && tLit.contains p.2.1.2.2 &&
      l1Lit.contains p.2.2.1 && l2Lit.contains p.2.2.2.1 && tLit.contains p.2.2.2.2 &&
      tLit.contains (cconj (Core.cmul (Core.cmul p.2.1.1 p.2.1.2.1) p.2.1.2.2) p.1) &&
      tLit.contains (cconj (Core.cmul (Core.cmul p.2.2.1 p.2.2.2.1) p.2.2.2.2)
        (cconj (Core.cmul (Core.cmul p.2.1.1 p.2.1.2.1) p.2.1.2.2) p.1)) &&
      !(ccomm (cconj (Core.cmul (Core.cmul p.2.1.1 p.2.1.2.1) p.2.1.2.2) p.1)
        (cconj (Core.cmul (Core.cmul p.2.2.1 p.2.2.2.1) p.2.2.2.2)
          (cconj (Core.cmul (Core.cmul p.2.1.1 p.2.1.2.1) p.2.1.2.2) p.1))))

theorem pair_of_chk {tLit : List (List ℕ)} (hT : LDesc (TB i) tLit)
    (hsyl : IsSylowIn 2 (Tb i) ⊤)
    {ws : List ((List ℕ × List ℕ × List ℕ) × (List ℕ × List ℕ × List ℕ))}
    (hw : PairChk tLit ws = true) :
    ∀ x : ↥(GB i), orderOf x = 2 → ∃ n : ↥(GB i),
      IsPGroup 2 (closure {x, n * x * n⁻¹}) ∧ x * (n * x * n⁻¹) ≠ (n * x * n⁻¹) * x := by
  intro x hx
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxp : IsPGroup 2 (zpowers x) := by
    intro y
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp y.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, ← hx, pow_orderOf_eq_one, one_zpow, Subgroup.coe_one]
  obtain ⟨g, hg⟩ := NFA6.exists_conj_mem hsyl hxp
  set x' := g⁻¹ * x * g with hx'
  have hx'1 : x' ≠ 1 := by
    intro h1
    have : x = 1 := by
      have e : x = g * x' * g⁻¹ := by rw [hx']; group
      rw [e, h1]; group
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hx'2 : x' * x' = 1 := by
    rw [hx']
    have e : g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x ^ 2) * g := by rw [pow_two]; group
    rw [e, hx2]
    group
  have hinv : cinvol (code x'.1) = true := by
    rw [cinvol_iff]
    refine ⟨fun h1 => hx'1 (Subtype.ext h1), ?_⟩
    rw [← Subgroup.coe_mul, hx'2]
    rfl
  simp only [PairChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hw
  obtain ⟨hlen, hall⟩ := hw
  have hmem : code x'.1 ∈ tLit := (mem_Tb_iff i hT x').1 hg
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hmem
  have hk' : k < ws.length := hlen ▸ hk
  have hz : (code x'.1, ws[k]) ∈ tLit.zip ws := by
    rw [← hkx]
    exact List.mem_iff_getElem.2 ⟨k, by simp [hk, hk'], by simp⟩
  have h := hall _ hz
  simp only [hinv, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h4'⟩, h4''⟩, h5⟩, h6⟩, h7⟩ := h
  obtain ⟨hh, hhc⟩ := exists_GB i hT h1 h2 h3
  obtain ⟨m, hmc⟩ := exists_GB i hT h4 h4' h4''
  set c' := hh * x' * hh⁻¹ with hc'
  set d := m * c' * m⁻¹ with hd
  have hc'c : code c'.1 = cconj (Core.cmul (Core.cmul (ws[k]).1.1 (ws[k]).1.2.1) (ws[k]).1.2.2)
      (code x'.1) := by
    rw [hc', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, code_conj, hhc]
  have hdc : code d.1 = cconj (Core.cmul (Core.cmul (ws[k]).2.1 (ws[k]).2.2.1) (ws[k]).2.2.2)
      (code c'.1) := by
    rw [hd, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, code_conj, hmc]
  have hc'T : c' ∈ Tb i := (mem_Tb_iff i hT c').2 (hc'c ▸ h5)
  have hdT : d ∈ Tb i := (mem_Tb_iff i hT d).2 (by rw [hdc, hc'c]; exact h6)
  have hne : c' * d ≠ d * c' := by
    intro he
    have h8 : ccomm (code c'.1) (code d.1) = true := by
      rw [ccomm_iff, ← Subgroup.coe_mul, ← Subgroup.coe_mul, he]
    rw [hdc, hc'c] at h8
    rw [h8] at h7
    exact Bool.noConfusion h7
  set y := g * hh⁻¹ with hy
  have hxe : x = y * c' * y⁻¹ := by rw [hy, hc', hx']; group
  refine ⟨y * m * y⁻¹, ?_, ?_⟩
  · have hye : y * m * y⁻¹ * x * (y * m * y⁻¹)⁻¹ = y * d * y⁻¹ := by rw [hxe, hd]; group
    have hle : closure {x, y * m * y⁻¹ * x * (y * m * y⁻¹)⁻¹} ≤
        (Tb i).map (MulAut.conj y).toMonoidHom := by
      rw [closure_le]
      intro z hz
      rcases hz with rfl | hz
      · rw [hxe]
        exact ⟨c', hc'T, by simp [MulAut.conj_apply]⟩
      · rw [Set.mem_singleton_iff] at hz
        rw [hz, hye]
        exact ⟨d, hdT, by simp [MulAut.conj_apply]⟩
    exact (hsyl.isPGroup.map _).to_le hle
  · intro he
    apply hne
    have hye : y * m * y⁻¹ * x * (y * m * y⁻¹)⁻¹ = y * d * y⁻¹ := by rw [hxe, hd]; group
    rw [hye, hxe] at he
    have := congrArg (fun z => y⁻¹ * z * y) he
    simpa [mul_assoc] using this

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF
