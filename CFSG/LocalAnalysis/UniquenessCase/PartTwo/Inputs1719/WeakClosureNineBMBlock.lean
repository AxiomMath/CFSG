module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMCode
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNPGL27Abs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNPGL27Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF

open CFSG.QuasithinUnique.A6Facts Subgroup

set_option maxRecDepth 100000

@[expose] def cfixLo (c : List ℕ) : Bool := (List.range 8).all fun k => c.getD k 0 == k

@[expose] def cfixHi (c : List ℕ) : Bool := (List.range' 8 8).all fun k => c.getD k 0 == k

@[expose] def cpresLo (c : List ℕ) : Bool := (List.range 8).all fun k => decide (c.getD k 0 < 8)

theorem all_getD_iff {P : ℕ → ℕ → Bool} {σ : P16} {l : List ℕ} (hl : ∀ k ∈ l, k < 16) :
    (l.all fun k => P k ((code σ).getD k 0)) = true ↔
      ∀ k : Fin 16, k.val ∈ l → P k (σ k) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h k hk
    have := h k hk
    rwa [show (k : ℕ) = ((k : Fin 16) : ℕ) from rfl, codeN_getD] at this
  · intro h k hk
    have := h ⟨k, hl k hk⟩ hk
    rwa [show k = ((⟨k, hl k hk⟩ : Fin 16) : ℕ) from rfl, codeN_getD]

theorem cfixLo_iff {σ : P16} : cfixLo (code σ) = true ↔ ∀ k : Fin 16, k.val < 8 → σ k = k := by
  rw [cfixLo, all_getD_iff (P := fun k v => v == k) (fun k hk => by
    rw [List.mem_range] at hk; omega)]
  simp only [List.mem_range, beq_iff_eq]
  exact forall_congr' fun k => imp_congr_right fun _ => Fin.val_inj

theorem cfixHi_iff {σ : P16} : cfixHi (code σ) = true ↔ ∀ k : Fin 16, 8 ≤ k.val → σ k = k := by
  rw [cfixHi, all_getD_iff (P := fun k v => v == k) (fun k hk => by
    rw [List.mem_range'] at hk; omega)]
  simp only [List.mem_range', beq_iff_eq]
  refine forall_congr' fun k => ⟨fun h hk => Fin.val_inj.1 (h ⟨k.val - 8, by omega, by omega⟩),
    fun h ⟨m, hm, hk⟩ => Fin.val_inj.2 (h (by omega))⟩

theorem cpresLo_iff {σ : P16} : cpresLo (code σ) = true ↔ ∀ k : Fin 16, k.val < 8 → (σ k).val < 8 := by
  rw [cpresLo, all_getD_iff (P := fun k v => decide (v < 8)) (fun k hk => by
    rw [List.mem_range] at hk; omega)]
  simp only [List.mem_range, decide_eq_true_eq]

@[expose] def fixLoP : Subgroup P16 where
  carrier := {σ | ∀ k : Fin 16, k.val < 8 → σ k = k}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb k hk => by
    change a (b k) = k
    rw [hb k hk, ha k hk]
  inv_mem' := fun {a} ha k hk => by
    change a⁻¹ k = k
    rw [Equiv.Perm.inv_eq_iff_eq, ha k hk]

@[expose] def fixHiP : Subgroup P16 where
  carrier := {σ | ∀ k : Fin 16, 8 ≤ k.val → σ k = k}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb k hk => by
    change a (b k) = k
    rw [hb k hk, ha k hk]
  inv_mem' := fun {a} ha k hk => by
    change a⁻¹ k = k
    rw [Equiv.Perm.inv_eq_iff_eq, ha k hk]

theorem lt_of_mem_fixHiP {σ : P16} (h : σ ∈ fixHiP) {k : Fin 16} (hk : k.val < 8) :
    (σ k).val < 8 := by
  by_contra hc
  have h1 := h (σ k) (by omega)
  have h2 : σ k = k := σ.injective h1
  rw [h2] at hc
  exact hc hk

theorem commute_of_fixHiP_fixLoP {σ τ : P16} (hσ : σ ∈ fixHiP) (hτ : τ ∈ fixLoP) :
    σ * τ = τ * σ := by
  ext k
  change (σ (τ k) : ℕ) = τ (σ k)
  by_cases hk : k.val < 8
  · rw [hτ k hk, hτ _ (lt_of_mem_fixHiP hσ hk)]
  · have h1 : 8 ≤ (τ k).val := by
      by_contra hc
      have h2 := hτ (τ k) (by omega)
      have h3 : τ k = k := τ.injective h2
      rw [h3] at hc
      exact hc (by omega)
    rw [hσ k (by omega), hσ _ h1]

@[expose] def blk1 : Fin 8 ≃ {k : Fin 16 // k.val < 8} where
  toFun a := ⟨⟨a.val, by omega⟩, a.2⟩
  invFun k := ⟨k.1.val, k.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def iota1 : Equiv.Perm (Fin 8) →* P16 := Equiv.Perm.extendDomainHom blk1

theorem iota1_injective : Function.Injective iota1 := Equiv.Perm.extendDomainHom_injective blk1

theorem code_iota1 (σ : Equiv.Perm (Fin 8)) :
    code (iota1 σ) = (List.range 16).map fun k => if h : k < 8 then (σ ⟨k, h⟩ : ℕ) else k := by
  apply List.ext_getElem
  · simp [code_length]
  · intro j h1 h2
    have hj : j < 16 := by simpa [code_length] using h1
    rw [code_getElem]
    simp only [List.getElem_map, List.getElem_range]
    split_ifs with h
    · change ((Equiv.Perm.extendDomain σ blk1 ⟨j, hj⟩ : Fin 16) : ℕ) = _
      rw [Equiv.Perm.extendDomain_apply_subtype σ blk1 (show (⟨j, hj⟩ : Fin 16).val < 8 from h)]
      rfl
    · change ((Equiv.Perm.extendDomain σ blk1 ⟨j, hj⟩ : Fin 16) : ℕ) = _
      rw [Equiv.Perm.extendDomain_apply_not_subtype σ blk1
        (show ¬ (⟨j, hj⟩ : Fin 16).val < 8 from h)]

@[expose] def cIota1 (c : List ℕ) : List ℕ :=
  (List.range 16).map fun k => if k < 8 then c.getD k 0 else k

theorem code_iota1' (σ : Equiv.Perm (Fin 8)) : code (iota1 σ) = cIota1 (codeN 8 σ) := by
  rw [code_iota1, cIota1]
  apply List.map_congr_left
  intro k _
  split_ifs with h
  · exact (codeN_getD σ ⟨k, h⟩).symm
  · rfl

@[expose] def l8GenC : List (List ℕ) := [[1, 2, 3, 4, 5, 6, 0, 7], [7, 6, 3, 2, 5, 4, 1, 0]]

@[expose] def l8Tree : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0), (3, 1), (4, 0), (5, 0), (5, 1), (6, 0), (6, 1), (7, 0), (8, 0), (8, 1), (9, 0), (9, 1), (10, 0), (11, 0), (11, 1), (12, 0), (13, 0), (13, 1), (14, 0), (14, 1), (16, 0), (16, 1), (17, 0), (18, 0), (18, 1), (19, 1), (20, 0), (21, 0), (21, 1), (22, 0), (22, 1), (24, 0), (24, 1), (25, 0), (26, 0), (26, 1), (27, 0), (28, 0), (28, 1), (29, 0), (29, 1), (31, 0), (32, 0), (32, 1), (33, 0), (33, 1), (35, 0), (35, 1), (36, 0), (37, 0), (37, 1), (38, 0), (39, 0), (41, 0), (42, 0), (42, 1), (43, 0), (43, 1), (45, 0), (45, 1), (47, 0), (47, 1), (48, 0), (48, 1), (50, 0), (50, 1), (51, 0), (52, 0), (52, 1), (53, 0), (54, 0), (56, 0), (57, 0), (57, 1), (58, 0), (58, 1), (59, 0), (59, 1), (60, 0), (60, 1), (62, 0), (62, 1), (63, 0), (64, 0), (64, 1), (65, 0), (66, 0), (66, 1), (68, 0), (68, 1), (69, 0), (70, 0), (70, 1), (71, 0), (72, 0), (74, 0), (75, 1), (76, 0), (76, 1), (77, 0), (77, 1), (78, 0), (78, 1), (80, 0), (80, 1), (82, 0), (82, 1), (84, 0), (85, 0), (86, 0), (86, 1), (88, 0), (90, 0), (91, 1), (92, 0), (92, 1), (93, 0), (94, 0), (95, 0), (96, 0), (98, 0), (99, 1), (100, 0), (100, 1), (101, 0), (101, 1), (103, 0), (103, 1), (105, 0), (105, 1), (107, 0), (108, 0), (109, 0), (109, 1), (112, 0), (113, 0), (114, 0), (116, 0), (117, 0), (117, 1), (118, 0), (118, 1), (121, 0), (124, 1), (125, 0), (126, 0), (128, 0), (128, 1), (130, 0), (130, 1), (135, 0), (136, 0), (137, 0), (139, 0), (142, 1), (143, 0), (144, 1), (148, 1), (150, 0), (150, 1), (151, 1), (158, 1)]

@[expose] def l8Tbl : List (List ℕ) := [[1, 2], [3, 4], [5, 0], [6, 7], [8, 1], [9, 10], [11, 12], [13, 3], [14, 15], [16, 17], [18, 5], [19, 20], [21, 6], [22, 23], [24, 25], [2, 8], [26, 27], [28, 9], [29, 30], [30, 31], [32, 11], [33, 34], [35, 36], [4, 13], [37, 38], [39, 14], [40, 41], [42, 16], [43, 44], [45, 46], [0, 18], [47, 19], [48, 49], [50, 51], [7, 21], [52, 53], [54, 22], [55, 56], [57, 24], [58, 40], [15, 39], [59, 26], [60, 61], [62, 63], [10, 28], [64, 65], [31, 29], [66, 67], [68, 69], [12, 32], [70, 71], [72, 33], [73, 74], [75, 35], [76, 55], [23, 54], [77, 37], [78, 79], [80, 81], [82, 83], [84, 85], [17, 42], [86, 87], [88, 43], [89, 90], [91, 45], [92, 93], [20, 47], [94, 95], [96, 48], [97, 98], [99, 50], [100, 73], [34, 72], [101, 52], [63, 102], [103, 104], [105, 106], [107, 108], [25, 57], [109, 110], [41, 58], [111, 112], [27, 59], [113, 94], [114, 60], [115, 116], [102, 62], [117, 89], [44, 88], [118, 64], [108, 119], [120, 121], [122, 66], [123, 84], [124, 68], [125, 97], [49, 96], [126, 70], [81, 127], [128, 129], [130, 131], [36, 75], [132, 133], [56, 76], [134, 135], [38, 77], [136, 120], [137, 78], [138, 139], [127, 80], [71, 126], [140, 82], [141, 134], [142, 115], [61, 114], [143, 86], [144, 145], [146, 147], [46, 91], [119, 107], [148, 92], [85, 123], [67, 122], [104, 149], [150, 146], [151, 111], [51, 99], [152, 153], [74, 100], [154, 155], [53, 101], [87, 143], [149, 103], [95, 113], [156, 105], [157, 154], [158, 138], [79, 137], [159, 109], [135, 141], [83, 140], [153, 160], [161, 132], [131, 162], [90, 117], [98, 125], [65, 118], [129, 163], [69, 124], [164, 165], [145, 166], [110, 159], [163, 128], [121, 136], [162, 130], [155, 157], [106, 156], [165, 167], [160, 152], [116, 142], [167, 164], [166, 144], [93, 148], [133, 161], [147, 150], [112, 151], [139, 158]]

@[expose] def b8 : Equiv.Perm (Fin 8) where
  toFun := ![7, 6, 3, 2, 5, 4, 1, 0]
  invFun := ![7, 6, 3, 2, 5, 4, 1, 0]
  left_inv := by decide
  right_inv := by decide

@[expose] def L8 : Subgroup (Equiv.Perm (Fin 8)) := closure {g | g ∈ [NFF7.g1, b8]}

theorem l8_gens : [NFF7.g1, b8].map (codeN 8) = l8GenC := by decide

theorem l8_tbl : Core.tblCheckC (List.range 8) l8GenC (Core.buildCodes (List.range 8) l8GenC l8Tree)
    l8Tbl = true := by decide +kernel

theorem l8_nodup : (Core.buildCodes (List.range 8) l8GenC l8Tree).Nodup := by decide +kernel

theorem l8_length : (Core.buildCodes (List.range 8) l8GenC l8Tree).length = 168 := by decide +kernel

theorem l8_sub_g0 : ∀ c ∈ Core.buildCodes (List.range 8) l8GenC l8Tree, c ∈ NFF7.gLit := by
  decide +kernel

theorem card_L8 : Nat.card L8 = 168 := by
  rw [L8, card_closure_eq_of_tblN l8_gens l8_tbl l8_nodup, l8_length]

theorem mem_L8_iff (σ : Equiv.Perm (Fin 8)) :
    σ ∈ L8 ↔ codeN 8 σ ∈ Core.buildCodes (List.range 8) l8GenC l8Tree :=
  (mem_closure_iff_of_tblN l8_gens l8_tbl).1 σ

theorem L8_le_G0 : L8 ≤ NFF7.G0 := fun σ hσ =>
  (NFF7.mem_G0_iff σ).2 (l8_sub_g0 _ ((mem_L8_iff σ).1 hσ))

theorem codeN8_inv (σ : Equiv.Perm (Fin 8)) :
    codeN 8 σ⁻¹ = (List.range 8).map fun j => (codeN 8 σ).idxOf j := by
  apply List.ext_getElem
  · simp [codeN_length]
  · intro j h1 h2
    have hj : j < 8 := by simpa [codeN_length] using h1
    simp only [List.getElem_map, List.getElem_range]
    have hc : ∀ (τ : Equiv.Perm (Fin 8)) (m : ℕ) (hm : m < (codeN 8 τ).length),
        (codeN 8 τ)[m] = (τ ⟨m, by simpa [codeN_length] using hm⟩ : ℕ) := by
      intro τ m hm
      simp only [codeN, List.getElem_ofFn]
    rw [hc]
    set m := σ⁻¹ ⟨j, hj⟩ with hm
    have hnd : (codeN 8 σ).Nodup := by
      unfold codeN
      rw [List.nodup_ofFn]
      intro a b h
      exact σ.injective (Fin.ext h)
    have hlt : (m : ℕ) < (codeN 8 σ).length := by rw [codeN_length]; exact m.2
    have hget : (codeN 8 σ)[(m : ℕ)] = j := by
      rw [hc]
      simp [hm]
    have := List.get_idxOf hnd ⟨m, hlt⟩
    simp only [List.get_eq_getElem] at this
    rw [hget] at this
    exact this.symm

theorem L8_le_commutator : L8 ≤ ⁅L8, L8⁆ := by
  rw [L8, closure_le]
  intro g hg
  have key : ∀ (cx cy : List ℕ) (g' : Equiv.Perm (Fin 8)),
      cx ∈ Core.buildCodes (List.range 8) l8GenC l8Tree →
      cy ∈ Core.buildCodes (List.range 8) l8GenC l8Tree →
      Core.cmul (Core.cmul (Core.cmul cx cy) ((List.range 8).map fun j => cx.idxOf j))
        ((List.range 8).map fun j => cy.idxOf j) = codeN 8 g' → g' ∈ ⁅closure {g | g ∈ [NFF7.g1, b8]},
          closure {g | g ∈ [NFF7.g1, b8]}⁆ := by
    intro cx cy g' hx hy he
    obtain ⟨x, hxL, rfl⟩ := (mem_closure_iff_of_tblN l8_gens l8_tbl).2 cx hx
    obtain ⟨y, hyL, rfl⟩ := (mem_closure_iff_of_tblN l8_gens l8_tbl).2 cy hy
    rw [← codeN8_inv, ← codeN8_inv, ← codeN_mul, ← codeN_mul, ← codeN_mul] at he
    rw [← codeN_injective he]
    exact commutator_mem_commutator hxL hyL
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
  rcases hg with rfl | rfl
  · refine key [2, 3, 4, 5, 6, 0, 1, 7] [5, 2, 6, 3, 0, 4, 1, 7] _ ?_ ?_ ?_ <;> decide +kernel
  · refine key [0, 6, 2, 1, 5, 7, 3, 4] [4, 3, 1, 2, 7, 5, 6, 0] _ ?_ ?_ ?_ <;> decide +kernel

noncomputable def g0Equiv : ↥NFF7.G0 ≃* CFSG.GorensteinWalter.PGL2 (ZMod 7) :=
  ((MonoidHom.ofInjective NFF7.rho_injective).trans (MulEquiv.subgroupCongr NFF7.rho_range)).symm

theorem isSimpleGroup_L8 : IsSimpleGroup ↥L8 := by
  set Lb := L8.subgroupOf NFF7.G0 with hLb
  have hidx : Lb.index = 2 := by
    have h1 := Lb.index_mul_card
    rw [show Nat.card Lb = 168 by
      rw [hLb, Nat.card_congr (subgroupOfEquivOfLe L8_le_G0).toEquiv, card_L8],
      show Nat.card ↥NFF7.G0 = 336 from NFF7.card_G0] at h1
    omega
  have hn : Lb.Normal := normal_of_index_eq_two hidx
  have hne : Lb ≠ ⊥ := by
    intro h
    have : Lb.index = Nat.card ↥NFF7.G0 := by rw [h, index_bot]
    rw [hidx, NFF7.card_G0] at this
    norm_num at this
  have hperf : ⁅Lb, Lb⁆ = Lb := by
    apply map_injective NFF7.G0.subtype_injective
    rw [map_commutator, hLb, subgroupOf_map_subtype, inf_eq_left.2 L8_le_G0]
    exact le_antisymm (commutator_le_self _) L8_le_commutator
  obtain ⟨-, hs, -⟩ := NFF7.lb_facts g0Equiv hn hne hperf
  have := hs
  exact (subgroupOfEquivOfLe L8_le_G0).symm.isSimpleGroup

theorem L01_eq_map : L01 = L8.map iota1 := by
  rw [L8, MonoidHom.map_closure, L01]
  congr 1
  ext σ
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq, Set.mem_image]
  have h1 : iota1 NFF7.g1 = a1 := code_injective (by rw [code_iota1']; decide)
  have h2 : iota1 b8 = b1 := code_injective (by rw [code_iota1']; decide)
  constructor
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, h1⟩
    · exact ⟨_, Or.inr rfl, h2⟩
  · rintro ⟨τ, (rfl | rfl), rfl⟩
    · exact Or.inl h1
    · exact Or.inr h2

theorem isSimpleGroup_L01 : IsSimpleGroup ↥L01 := by
  have := isSimpleGroup_L8
  rw [L01_eq_map]
  exact (L8.equivMapOfInjective iota1 iota1_injective).symm.isSimpleGroup

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF
