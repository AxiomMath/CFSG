module

public import CFSG.Quasithin.Background.HZL34B
public import CFSG.Quasithin.Background.HZCoc24C

public section

namespace CFSG.Quasithin.H.L34Z

open CFSG.Open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.L3W9
  CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H.ZTrans

@[expose] def irrVData : List (ℕ × List (ℕ × ℕ)) := [
    (2, [(0, 0), (1, 0), (1, 6)]), (4, [(0, 0), (1, 0), (1, 6)]), (6, [(1, 0), (1, 6), (1, 7)]),
    (128, [(1, 0), (0, 6), (1, 6)]), (130, [(0, 0), (1, 0), (1, 6)]),
    (132, [(0, 0), (1, 0), (1, 6)]), (134, [(1, 0), (0, 6), (1, 6)]),
    (256, [(0, 0), (1, 0), (1, 6)]), (258, [(0, 0), (1, 0), (1, 6)]),
    (260, [(0, 0), (1, 0), (1, 6)]), (262, [(0, 0), (1, 0), (1, 6)]),
    (384, [(0, 0), (1, 0), (1, 6)]), (386, [(0, 0), (1, 0), (1, 6)]),
    (388, [(0, 0), (1, 0), (1, 6)]), (390, [(0, 0), (1, 0), (1, 6)])]

theorem irrV_ok : ∀ e ∈ irrVData, e.1 < 2 ^ 9 ∧
    nodupB (combos (derivB lAct (e.1 :: w0Basis) e.2)) 0 = true ∧
    (derivB lAct (e.1 :: w0Basis) e.2).length = 9 := by
  decide +kernel

theorem irrV_cover : ∀ m < 2 ^ 9, m ∉ combos w0Basis →
    ∃ e ∈ irrVData, m ^^^ e.1 ∈ combos w0Basis := by
  decide +kernel

theorem w0Basis_mem_combos : ∀ a ∈ w0Basis, a ∈ combos w0Basis := by
  decide +kernel

theorem eq_top_of_W0_lt {Y : Subgroup W9} (h1 : W0 < Y) (h3 : L34 ≤ stabSub Y) : Y = ⊤ := by
  obtain ⟨y, hyY, hyW⟩ := IsConcreteLE.exists_of_lt h1
  obtain ⟨m, hm, rfl⟩ := toW_surj 9 y
  have hmW : m ∉ combos w0Basis := fun h => hyW (toW_mem_maskSub h)
  obtain ⟨e, he, hme⟩ := irrV_cover m hm hmW
  obtain ⟨he9, hnd, hlen⟩ := irrV_ok e he
  let P : ℕ → Prop := fun k => k < 2 ^ 9 ∧ toW 9 k ∈ Y
  have Pact : ∀ g k, P k → P (lAct g k) := by
    rintro g k ⟨hk9, hk⟩
    have hk' : k < 512 := lt_of_lt_of_eq hk9 (by norm_num)
    refine ⟨lt_of_lt_of_eq (lAct_lt g k hk') (by norm_num), ?_⟩
    obtain ⟨x, hx, hxe⟩ := rho_lAct g hk'
    rw [← hxe]
    exact ((h3 hx) _).2 hk
  have P0 : P 0 := ⟨by norm_num, by rw [toW_zero]; exact Y.one_mem⟩
  have hstart : ∀ k ∈ e.1 :: w0Basis, P k := by
    intro k hk
    rcases List.mem_cons.1 hk with rfl | hk
    · refine ⟨he9, ?_⟩
      have e1 : toW 9 e.1 = toW 9 m * toW 9 (m ^^^ e.1) := by
        rw [← toW_xor, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [e1]
      exact Y.mul_mem hyY (h1.le (toW_mem_maskSub hme))
    · exact ⟨w0_lt k hk, h1.le (toW_mem_maskSub (w0Basis_mem_combos k hk))⟩
  have hall := mem_of_derivB lAct P Pact P0 e.2 _ hstart
  have hcard := (MaskCoords.std 9).pow_le_card Y (derivB lAct (e.1 :: w0Basis) e.2)
    (nodup_of_nodupB _ _ hnd).1 (fun a ha => (hall a ha).1) (fun a ha => (hall a ha).2)
  rw [hlen] at hcard
  refine Subgroup.eq_top_of_le_card _ ?_
  rw [Nat.card_eq_fintype_card, card_Wn]
  exact hcard

theorem irrV_of_binaryNine {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} (h : BinaryNineTensor H ⊤ ⊥ 1) {z : V} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2)
    (hzS : z ∈ fixV S) : ∀ Y : Subgroup V, vZ H z < Y → parZ H z ≤ stabSub Y → Y = ⊤ := by
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 h hz1 hSH hS hzS
  intro Y h1 h3
  have keyW : ∀ (A : Subgroup (MulAut W9)) (w : W9), A = img9 → w = z0 → vZ A w = W0 := by
    rintro A w rfl rfl
    exact vZ_std
  have hW : (vZ H z).map e.toMonoidHom = W0 := (vZ_map e H z).trans (keyW _ _ he hez)
  have keyP : ∀ (A : Subgroup (MulAut W9)) (w : W9), A = img9 → w = z0 → parZ A w = L34 := by
    rintro A w rfl rfl
    exact parZ_std
  have hP : (parZ H z).map (congrHom e) = L34 := (parZ_map e H z).trans (keyP _ _ he hez)
  have h1' : W0 < Y.map e.toMonoidHom := by
    rw [← hW]
    exact (Subgroup.map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr h1
  have h3' : L34 ≤ stabSub (Y.map e.toMonoidHom) := by
    intro p hp
    rw [← hP] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    exact (stabSub_map_congrHom e Y).ge ⟨p₀, h3 hp₀, rfl⟩
  have htop := eq_top_of_W0_lt h1' h3'
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [htop, Subgroup.map_top_of_surjective _ e.surjective]

end CFSG.Quasithin.H.L34Z


namespace CFSG.Quasithin.H.Coc24

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans

@[expose] def irrVData : List (ℕ × List (ℕ × ℕ)) := [
    (1, [(0, 0), (1, 0), (0, 8)]), (2, [(0, 0), (0, 8), (1, 9)]), (3, [(0, 0), (1, 0), (0, 8)]),
    (4, [(0, 0), (1, 0), (1, 8)]), (5, [(0, 0), (1, 0), (0, 8)]), (6, [(0, 0), (1, 0), (1, 8)]),
    (7, [(0, 0), (1, 0), (0, 8)]), (8, [(0, 0), (0, 8), (0, 9)]), (9, [(1, 0), (0, 8), (0, 9)]),
    (10, [(0, 0), (0, 8), (0, 9)]), (11, [(0, 0), (1, 0), (0, 8)]),
    (12, [(0, 0), (1, 0), (0, 8)]), (13, [(0, 0), (1, 0), (0, 8)]),
    (14, [(0, 0), (1, 0), (0, 8)]), (15, [(0, 0), (1, 0), (1, 8)])]

theorem irrV_ok : ∀ e ∈ irrVData, e.1 < 2 ^ 11 ∧
    nodupB (combos (derivB lzAct (e.1 :: w0Basis) e.2)) 0 = true ∧
    (derivB lzAct (e.1 :: w0Basis) e.2).length = 11 := by
  decide +kernel

@[expose] def projCols : List ℕ := [1, 2, 4, 8, 15, 0, 0, 0, 0, 0, 0]

theorem xorLin_proj : XorLin fun m => m ^^^ actM projCols m := fun x y => by
  show x ^^^ y ^^^ actM projCols (x ^^^ y) = x ^^^ actM projCols x ^^^ (y ^^^ actM projCols y)
  rw [actM_xor projCols x y]
  ac_rfl

theorem xor_proj_mem : ∀ m < 2 ^ 11, m ^^^ actM projCols m ∈ combos w0Basis :=
  mem_combos_of_xorLin xorLin_proj (by decide +kernel)

theorem proj_lt (m : ℕ) : actM projCols m < 2 ^ 4 := actM_lt (by decide) m

theorem proj_cover : ∀ c < 2 ^ 4, c ≠ 0 → c ∈ irrVData.map Prod.fst := by
  decide +kernel

theorem irrV_cover : ∀ m < 2 ^ 11, m ∉ combos w0Basis →
    ∃ e ∈ irrVData, m ^^^ e.1 ∈ combos w0Basis := by
  intro m hm hmW
  have hne : actM projCols m ≠ 0 := by
    intro h0
    apply hmW
    have := xor_proj_mem m hm
    rwa [h0, Nat.xor_zero] at this
  obtain ⟨e, he, he1⟩ := List.mem_map.1 (proj_cover _ (proj_lt m) hne)
  exact ⟨e, he, he1 ▸ xor_proj_mem m hm⟩

theorem w0Basis_mem_combos : ∀ a ∈ w0Basis, a ∈ combos w0Basis := by
  decide +kernel

theorem eq_top_of_W0_lt {Y : Subgroup W11} (h1 : W0 < Y) (h3 : img11 Lz ≤ stabSub Y) :
    Y = ⊤ := by
  obtain ⟨y, hyY, hyW⟩ := IsConcreteLE.exists_of_lt h1
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 y
  have hmW : m ∉ combos w0Basis := fun h => hyW (toW_mem_maskSub h)
  obtain ⟨e, he, hme⟩ := irrV_cover m hm hmW
  obtain ⟨he11, hnd, hlen⟩ := irrV_ok e he
  let P : ℕ → Prop := fun k => k < 2 ^ 11 ∧ toW 11 k ∈ Y
  have Pact : ∀ g k, P k → P (lzAct g k) := by
    rintro g k ⟨-, hk⟩
    refine ⟨by unfold lzAct; exact act11_lt _ _, ?_⟩
    obtain ⟨x, hx, hxe⟩ := rho_lzAct g k
    rw [← hxe]
    exact ((h3 hx) _).2 hk
  have P0 : P 0 := ⟨by norm_num, by rw [toW_zero]; exact Y.one_mem⟩
  have hstart : ∀ k ∈ e.1 :: w0Basis, P k := by
    intro k hk
    rcases List.mem_cons.1 hk with rfl | hk
    · refine ⟨he11, ?_⟩
      have e1 : toW 11 e.1 = toW 11 m * toW 11 (m ^^^ e.1) := by
        rw [← toW_xor, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [e1]
      exact Y.mul_mem hyY (h1.le (toW_mem_maskSub hme))
    · exact ⟨w0_lt k hk, h1.le (toW_mem_maskSub (w0Basis_mem_combos k hk))⟩
  have hall := mem_of_derivB lzAct P Pact P0 e.2 _ hstart
  have hcard := (MaskCoords.std 11).pow_le_card Y (derivB lzAct (e.1 :: w0Basis) e.2)
    (nodup_of_nodupB _ _ hnd).1 (fun a ha => (hall a ha).1) (fun a ha => (hall a ha).2)
  rw [hlen] at hcard
  refine Subgroup.eq_top_of_le_card _ ?_
  rw [Nat.card_eq_fintype_card, card_Wn]
  exact hcard

theorem irrV_of_cocode24
    {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} (h : MathieuCocode24 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2)
    (hzS : z ∈ fixV S) : ∀ Y : Subgroup V, vZ H z < Y → parZ H z ≤ stabSub Y → Y = ⊤ := by
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 h hz1 hSH hS hzS
  intro Y h1 h3
  have keyW : ∀ (A : Subgroup (MulAut W11)) (w : W11),
      A = img11 AutPerm → w = z0 → vZ A w = W0 := by
    rintro A w rfl rfl
    exact vZ_std
  have hW : (vZ H z).map e.toMonoidHom = W0 := (vZ_map e H z).trans (keyW _ _ he hez)
  have keyP : ∀ (A : Subgroup (MulAut W11)) (w : W11),
      A = img11 AutPerm → w = z0 → parZ A w = img11 Lz := by
    rintro A w rfl rfl
    exact parZ_std
  have hP : (parZ H z).map (congrHom e) = img11 Lz := (parZ_map e H z).trans (keyP _ _ he hez)
  have h1' : W0 < Y.map e.toMonoidHom := by
    rw [← hW]
    exact (Subgroup.map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr h1
  have h3' : img11 Lz ≤ stabSub (Y.map e.toMonoidHom) := by
    intro p hp
    rw [← hP] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    exact (stabSub_map_congrHom e Y).ge ⟨p₀, h3 hp₀, rfl⟩
  have htop := eq_top_of_W0_lt h1' h3'
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [htop, Subgroup.map_top_of_surjective _ e.surjective]

end CFSG.Quasithin.H.Coc24
